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

namespace JsonSchema


end JsonSchema

structure JsonSchema (α) extends Lean.FromJson α, Lean.ToJson α where

def JsonValue (_s : JsonSchema α) := α
def JsonValue.val {s : JsonSchema α} (v : JsonValue s) : α := v

instance : Repr (JsonValue s) := ⟨(s.toJson · |> reprPrec)⟩
instance : Lean.FromJson (JsonValue s) := ⟨s.fromJson?⟩
instance : Lean.ToJson (JsonValue s) := ⟨s.toJson⟩

instance : CoeSort (JsonSchema α) Type := ⟨JsonValue⟩

namespace JsonSchema

def map (f : α → β) (finv : β → α) (s : JsonSchema α) : JsonSchema β where
  toJson := s.toJson ∘ finv
  fromJson? := (f <$> s.fromJson? ·)

def any : JsonSchema Lean.Json where
  toJson := id
  fromJson? := pure

def ofLeanJson [T : Lean.ToJson α] [F : Lean.FromJson α] : JsonSchema α where
  toJson := T.toJson
  fromJson? := F.fromJson?

def addFailingJson (s : JsonSchema α) : JsonSchema α where
  toJson := s.toJson
  fromJson? := fun j =>
    s.fromJson? j |>.mapError (s!"{·}\n{j.pretty}")

/-! Primitive data types -/

def integer : JsonSchema Int := ofLeanJson

def number : JsonSchema Lean.JsonNumber := ofLeanJson

def string : JsonSchema String := ofLeanJson

def boolean : JsonSchema Bool := ofLeanJson

/-! Arrays -/

def array (s : JsonSchema α) : JsonSchema (Array (JsonValue s)) where
  toJson x := .arr (x.map (s.toJson ·))
  fromJson? x :=
    match x with
    | .arr a => a.mapM (s.fromJson? · |>.map (·))
    | _ => .error "expected array"

/-! Objects -/

structure ObjSchema (α : String → Type) where
  schemas : (s : String) → JsonSchema (α s)
  required : List String

def ObjSchema.toType (os : ObjSchema α) :=
  { m : Lean.RBNode String (os.schemas ·) //
    ∀ key ∈ os.required, ∃ j, m.findCore compare key = some ⟨key,j⟩ }

instance : CoeSort (ObjSchema α) Type where
  coe := ObjSchema.toType

def ObjSchema.toType.get {os : ObjSchema α} (v : os) (s : String) (h : s ∈ os.required := by decide)
  : α s :=
  match h' : v.val.findCore compare s with
  | some ⟨s',x⟩ =>
    have : s = s' := by
      have := v.val.keys_eq_of_findCore_some h'
      simp [compare, compareOfLessAndEq] at this
      split at this <;>
        first | contradiction
              | split at this <;> first | contradiction | assumption
    this ▸ x.val
  | none => False.elim <| by
    have ⟨sv,h⟩ := v.property _ h
    rw [h'] at h
    contradiction

def ObjSchema.toType.get? {os : ObjSchema α} (v : os) (s : String)
  : Option (α s) :=
  v.val.findCore compare s |>.pmap (fun ⟨s',x⟩ h' =>
    have : s = s' := by
      have := v.val.keys_eq_of_findCore_some h'
      simp [compare, compareOfLessAndEq] at this
      split at this <;>
        first | contradiction
              | split at this <;> first | contradiction | assumption
    this ▸ x.val
  ) (fun _ => id)

def objSchema (os : ObjSchema α) : JsonSchema os where
  toJson v := .obj <| v.val.map (fun s x => os.schemas s |>.toJson x)
  fromJson? j :=
    match j with
    | .obj m => do
      let m ← m.mapM (os.schemas · |>.fromJson?)
      match h : os.required.find? (m.findCore compare · |>.isNone) with
      | some s => throw s!"object expected to have key \"{s}\": {j}"
      | none => return ⟨m, by
        intro key hk
        simp [List.find?_eq_none] at h
        have := h key hk
        simp [Option.isNone] at this; split at this <;> try contradiction
        rename_i v h'
        rcases v with ⟨a,b⟩
        have := Lean.RBNode.keys_eq_of_findCore_some _ h'
        simp [compare, compareOfLessAndEq] at this
        split at this <;> first | contradiction | split at this <;> try contradiction
        subst_vars
        exact ⟨_, h'⟩
        ⟩
    | _ => .error s!"expected object, got: {j}"

open Lean Macro Elab Term in
scoped macro "{" pairs:( str ":" term ),* "}" : term => do
  let ss' := pairs.getElems.map (fun s =>
    let key := s.raw[0].isStrLit?.get!
    let val : Syntax := s.raw[2]
    (key, (.mk val : TSyntax `term)))
  let eα ← `(fun (s : String) => $(
    ← ss'.foldrM
      (fun (k,_v) e => `(if s = $(Syntax.mkStrLit k) then _ else $e))
      (← `(Lean.Json))
    ))
  let eschemas ← `(fun (s : String) =>
    show JsonSchema ($eα s) from $(
    ← ss'.foldrM
      (fun (k,v) e => `(
        iteInduction (c := s = $(Syntax.mkStrLit k)) (motive := id) (fun _ => $v) (fun _ => $e)))
      (← `(any))
  ))
  return eschemas

/-- For a given key, if that key exists, specify the schema
    that applies to that key -/
def objectMap {α : String → Type} (f : (s : String) → JsonSchema (α s))
  := objSchema ⟨f, []⟩

/-! Subtypes (arbitrary properties on top of a given schema) -/

def withProperty (s : JsonSchema α) (errString : String) (p : α → Bool)
  : JsonSchema { a : JsonValue s // p a } where
  toJson x := s.toJson x.val
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

def orElse (s1 : JsonSchema α) (s2 : JsonSchema β) : JsonSchema (JsonValue s1 ⊕ JsonValue s2) where
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
  match v with
  | .inl r => resolveRef j s r.«$ref»
  | .inr v => pure v

/-! JsonSchema for JsonSchema -/

namespace CoreSchema

inductive «Type»
| integer | number | boolean | string | array | object
deriving DecidableEq, Lean.ToJson, Lean.FromJson

def Type.toType : «Type» → Type
| .integer => Int
| .number => Lean.JsonNumber
| .boolean => Bool
| .string => String
| .array => Array Lean.Json
| .object => ObjSchema.toType ⟨fun _ => any, []⟩

def Type.toJsonSchema (c : «Type») : JsonSchema c.toType :=
  match c with
  | .integer => JsonSchema.integer
  | .number  => JsonSchema.number
  | .boolean => JsonSchema.boolean
  | .string  => JsonSchema.string
  | .array   => JsonSchema.array any
  | .object  => JsonSchema.objectMap fun _ => any

def type : JsonSchema «Type» :=
  JsonSchema.ofLeanJson |>.addFailingJson

/- TODO: this should all be specified via structures, but
Lean structures currently don't have good enough support
for nested inductives for this to not be hugely painful. -/

structure Res where
  name : Lean.Ident
  type : Lean.Expr
  default : Option Lean.Expr

def fromJson? (j : Lean.Json) : Except String Res := do
  let oneOf   := Except.toOption <| j.getObjVal? "oneOf"
  let nullable:= Except.toOption <| j.getObjVal? "nullable"
  let type    := Except.toOption <| j.getObjVal? "type"
  let format  := Except.toOption <| j.getObjVal? "format"
  let properties := Except.toOption <| j.getObjVal? "properties"
  let default := Except.toOption <| j.getObjVal? "default"
  let enum    := Except.toOption <| j.getObjVal? "enum"
  let minimum := Except.toOption <| j.getObjVal? "minimum"
  let maximum := Except.toOption <| j.getObjVal? "maximum"
  return sorry

end CoreSchema
