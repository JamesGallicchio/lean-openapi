/-  Copyright (C) 2023 The Http library contributors.

    This program is free software: you can redistribute it and/or modify
    it under the terms of the GNU General Public License as published by
    the Free Software Foundation, either version 3 of the License, or
    (at your option) any later version.

    This program is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
    GNU General Public License for more details.

    You should have received a copy of the GNU General Public License
    along with this program.  If not, see <https://www.gnu.org/licenses/>.
-/

import Lean.Data.Json
import LeanOpenAPI.Std

/-! This file implements a strengthened-up version of JsonSchema. -/

namespace LeanOpenAPI

structure JsonSchema (α) extends Lean.FromJson α, Lean.ToJson α where

structure JsonValue (s : JsonSchema α) where
  val : α
deriving Inhabited

instance : Repr (JsonValue s) := ⟨(s.toJson ·.val |> reprPrec)⟩
instance : Lean.FromJson (JsonValue s) := ⟨fun j => s.fromJson? j |>.map (⟨·⟩)⟩
instance : Lean.ToJson (JsonValue s) := ⟨fun x => s.toJson x.val⟩

instance : CoeSort (JsonSchema α) Type := ⟨JsonValue⟩

namespace JsonSchema

def map (f : α → β) (finv : β → α) (s : JsonSchema α) : JsonSchema β where
  toJson := s.toJson ∘ finv
  fromJson? := (f <$> s.fromJson? ·)

def any : JsonSchema Lean.Json where
  toJson := id
  fromJson? := pure

def ofLeanJson [T : Lean.ToJson α] [F : Lean.FromJson α] : JsonSchema α where

def addFailingJson (s : JsonSchema α) : JsonSchema α where
  toJson := s.toJson
  fromJson? := fun j =>
    s.fromJson? j |>.mapError (s!"{·}\n{j.pretty}")

/-! Primitive data types -/

def integer : JsonSchema Int where

def number : JsonSchema Lean.JsonNumber where

def string : JsonSchema String where

def boolean : JsonSchema Bool where

/-! Arrays -/

def array (s : JsonSchema α) : JsonSchema (Array (JsonValue s)) where
  toJson x := .arr (x.map (s.toJson ·.val))
  fromJson? x :=
    match x with
    | .arr a => a.mapM (s.fromJson? · |>.map (⟨·⟩))
    | _ => .error "expected array"

/-! Objects -/

/-- For a given key, if that key exists, specify the schema
    that applies to that key -/
def objectMap (f : (s : String) → JsonSchema (α s)) : JsonSchema (Lean.RBNode String α) where
  toJson x := .obj (x.map (f · |>.toJson))
  fromJson? j :=
    match j with
    | .obj m => m.mapM (f · |>.fromJson? ·)
    | _ => .error "expected object"

/-! Subtypes (arbitrary properties on top of a given schema) -/

def withProperty (s : JsonSchema α) (errString : String) (p : α → Bool)
  : JsonSchema { a : α // p a } where
  toJson x := s.toJson x
  fromJson? j := do
    let a ← s.fromJson? j
    if h : p a then
      return ⟨a,h⟩
    else .error errString

/-! Pairs -/

def guard {β : α → Type} (f : Except String α) (g : (a : α) → JsonSchema (β a)) : JsonSchema (Σ a, β a) where
  toJson | ⟨a,b⟩ => (g a).toJson b
  fromJson? j := do
    let a ← f
    let b ← (g a).fromJson? j
    return ⟨a,b⟩

/-! Either -/

def orElse (s1 : JsonSchema α) (s2 : JsonSchema β) : JsonSchema (α ⊕ β) where
  toJson | .inl a => s1.toJson a | .inr b => s2.toJson b
  fromJson? j :=
    (s1.fromJson? j |>.map .inl) |>.orElseLazy fun () => (s2.fromJson? j |>.map .inr)

/-! References -/

inductive Reference
| pointer (tokens : List String)

def reference : JsonSchema Reference where
  toJson
  | .pointer toks => .str <| toks.foldl (· ++ "/" ++ tokenEncode ·) "#"
  fromJson? j :=
    match j with
    | .str s => do
      unless s.startsWith "#" do
        throw "expected fragment, starting with #"
      let segs := s.drop 1 |>.splitOn (sep := "/") |>.drop 1 |>.map tokenDecode
      return .pointer segs
    | _ => throw "expected reference: got not-a-string"
where
  tokenEncode (s : String) :=
    s.replace (pattern := "~") (replacement := "~0")
    |>.replace (pattern := "/") (replacement := "~1")
  tokenDecode (s : String) :=
    s.replace (pattern := "~1") (replacement := "/")
    |>.replace (pattern := "~0") (replacement := "~")

structure RefObj where
  «$ref» : reference
deriving Lean.ToJson, Lean.FromJson

def refObj : JsonSchema RefObj := JsonSchema.ofLeanJson

private def resolvePointer (j : Lean.Json) (p : List String) : Except String Lean.Json := do
  match p with
  | [] => return j
  | t::p =>
  match j with
  | .obj m =>
    let some j' := m.find compare t | throw s!"object does not contain key {t}"
    resolvePointer j' p
  | .arr a =>
    let some i := t.toNat? | throw s!"referencing array element, but reference token {t} is not a number"
    let some j' := a[i]? | throw s!"reference token {t} out of range of array"
    resolvePointer j' p
  | _ => throw "referencing a value that is not an object or array"

def resolveRef (j : Lean.Json) (expectedSchema : JsonSchema α) (r : Reference)
      : Except String (JsonValue expectedSchema) :=
  match r with
  | .pointer p => resolvePointer j p |>.bind Lean.FromJson.fromJson?

def resolveRefOr (j : Lean.Json) (v : JsonValue (refObj.orElse s)) : Except String (JsonValue s) :=
  match v.val with
  | .inl r => resolveRef j s r.«$ref».val
  | .inr v => pure ⟨v⟩

/-! JsonSchema for JsonSchema -/

namespace CoreSchema

inductive «Type»
| integer | number | string | object
deriving Lean.ToJson, Lean.FromJson

def Type.toType : «Type» → Type
| .integer => Int
| .number => Lean.JsonNumber
| .string => String
| .object => Lean.RBNode String (fun _ => Lean.Json)

def Type.toJsonSchema (c : «Type») : JsonSchema c.toType :=
  match c with
  | .integer => JsonSchema.integer
  | .number  => JsonSchema.number
  | .string  => JsonSchema.string
  | .object  => JsonSchema.objectMap fun _ => any

end CoreSchema

inductive CoreSchema
| mk
  (type : Option CoreSchema.«Type»)
  (oneOf : Option (Array CoreSchema))

def CoreSchema.toJson : CoreSchema → Lean.Json
| .mk type oneOf => Id.run do
  let mut res := Lean.RBNode.leaf
  for _h : ty in type do
    res := res.insert compare "type" (Lean.ToJson.toJson ty)
  for _h : ss in oneOf do
    res := res.insert compare "oneOf"
      (Lean.ToJson.toJson
        (← (ss.pmap
          (fun (s : CoreSchema) (h : ∃ i, ss[i] = s) =>
            have : sizeOf s < 1 + sizeOf type + sizeOf oneOf := sorry
            toJson s
      ))))
  return .obj res
termination_by _ s => sizeOf s

def coreSchema : JsonSchema (CoreSchema) where
  toJson cs :=
    match cs with
    | .mk type oneOf => sorry
  fromJson? j :=
    sorry
