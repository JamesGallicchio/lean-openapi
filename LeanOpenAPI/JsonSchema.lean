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

/-! This file implements a version of parsing JsonSchema. -/

namespace LeanOpenAPI

namespace JsonSchema

/-! References -/

inductive Reference
| pointer (tokens : List String)

namespace Reference

def toString : Reference → String
| pointer toks =>
  toks.foldl (· ++ "/" ++ tokenEncode ·) "#"
where
  tokenEncode (s : String) :=
    s.replace (pattern := "~") (replacement := "~0")
    |>.replace (pattern := "/") (replacement := "~1")
instance : ToString Reference := ⟨Reference.toString⟩

def fromString (s : String) : Except String Reference := do
  unless s.startsWith "#" do
    throw "expected fragment, starting with #"
  let segs := s.drop 1 |>.splitOn (sep := "/") |>.drop 1 |>.map tokenDecode
  return .pointer segs
where
  tokenDecode (s : String) :=
    s.replace (pattern := "~1") (replacement := "/")
    |>.replace (pattern := "~0") (replacement := "~")

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

def thenIdx (i : Nat) : Reference → Reference
| pointer toks => pointer (toks.concat (ToString.toString i))
def thenKey (k : String) : Reference → Reference
| pointer toks => pointer (toks.concat k)

end Reference

def SchemaM := ExceptT String <| ReaderT Lean.Json <| ReaderT Reference <| ReaderT Lean.Json Id

namespace SchemaM

def run (m : SchemaM α) (j : Lean.Json) : Except String α := m j ⟨[]⟩ j

@[inline] def topJson : SchemaM Lean.Json :=
  fun top _ _ => Except.ok top
@[inline] def curJson : SchemaM Lean.Json :=
  fun _ _ cur => Except.ok cur
@[inline] def curRef : SchemaM Reference :=
  fun _ ref _ => Except.ok ref
@[inline] def throw (e : String) : SchemaM α :=
  fun _ ref _ => .error s!"{ref}: {e}"
@[inline] def withState (r : Reference) (j : Lean.Json) (s : SchemaM α) : SchemaM α :=
  fun top _ _ => s top r j

instance : Monad SchemaM := inferInstanceAs (Monad (ExceptT _ _))
instance : MonadLift (Except String) SchemaM where
  monadLift e := show ExceptT _ _ _ from liftM e

end SchemaM

def any : SchemaM Lean.Json := SchemaM.curJson

def ofLeanJson [Lean.FromJson α] : SchemaM α := do
  match Lean.FromJson.fromJson? (← SchemaM.curJson) with
  | .ok a => return a
  | .error e => SchemaM.throw s!
"FromJson error:
{e}

Input JSON:
{(←SchemaM.curJson).pretty}"

/-! Primitive data types -/

def integer : SchemaM Int := ofLeanJson

def number : SchemaM Lean.JsonNumber := ofLeanJson

def string : SchemaM String := ofLeanJson

def boolean : SchemaM Bool := ofLeanJson

/-! Arrays -/

def array (s : SchemaM α) : SchemaM (Array α) := do
  let j ← SchemaM.curJson
  match j with
  | .arr a =>
    let r ← SchemaM.curRef
    a.mapIdxM (fun i j' => SchemaM.withState (r.thenIdx i) j' s)
  | _ => SchemaM.throw s!"expected array, got:\n{j}"

/-! Objects -/

structure ObjSchema (α : String → Type) where
  schemas : (s : String) → SchemaM (α s)
  required : List String

def ObjSchema.toType (os : ObjSchema α) :=
  { m : Lean.RBNode String α //
    ∀ key ∈ os.required, ∃ j, m.findCore compare key = some ⟨key,j⟩ }


def ObjSchema.toType.get {os : ObjSchema α} (v : os.toType) (s : String) (h : s ∈ os.required := by decide)
  : α s :=
  match h' : v.val.findCore compare s with
  | some ⟨s',x⟩ =>
    have : s = s' := by
      have := v.val.keys_eq_of_findCore_some h'
      simp [compare, compareOfLessAndEq] at this
      split at this <;>
        first | contradiction
              | split at this <;> first | contradiction | assumption
    this ▸ x
  | none => False.elim <| by
    have ⟨sv,h⟩ := v.property _ h
    rw [h'] at h
    contradiction

def ObjSchema.toType.get? {os : ObjSchema α} (v : os.toType) (s : String)
  : Option (α s) :=
  v.val.findCore compare s |>.pmap (fun ⟨s',x⟩ h' =>
    have : s = s' := by
      have := v.val.keys_eq_of_findCore_some h'
      simp [compare, compareOfLessAndEq] at this
      split at this <;>
        first | contradiction
              | split at this <;> first | contradiction | assumption
    this ▸ x
  ) (fun _ => id)

def objSchema (os : ObjSchema α) : SchemaM os.toType := do
  let j ← SchemaM.curJson
  match j with
  | .obj m =>
    let r ← SchemaM.curRef
    let m ← m.mapM (fun key val => SchemaM.withState (r.thenKey key) val (os.schemas key))
    match h : os.required.find? (m.findCore compare · |>.isNone) with
    | some s => SchemaM.throw s!"object expected to have key \"{s}\": {j}"
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
  | _ => SchemaM.throw s!"expected object, got: {j}"

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
    show SchemaM ($eα s) from $(
    ← ss'.foldrM
      (fun (k,v) e => `(
        iteInduction (c := s = $(Syntax.mkStrLit k)) (motive := id) (fun _ => $v) (fun _ => $e)))
      (← `(any))
  ))
  return eschemas

/-- For a given key, if that key exists, specify the schema
    that applies to that key -/
def objectMap {α : String → Type} (f : (s : String) → SchemaM (α s))
  := objSchema ⟨f, []⟩

/-! Subtypes (arbitrary properties on top of a given schema) -/

def withProperty (s : SchemaM α) (errString : α → String) (p : α → Bool)
      : SchemaM { a : α // p a } := do
  let a ← s
  if h : p a then
    return ⟨a,h⟩
  else SchemaM.throw (errString a)

/-! Pairs -/

def guard {β : α → Type} (f : SchemaM α) (g : (a : α) → SchemaM (β a))
      : SchemaM (Σ a, β a) := do
  let a ← f
  let b ← (g a)
  return ⟨a,b⟩

/-! Either -/

def orElse (s1 : SchemaM α) (s2 : SchemaM β) : SchemaM (α ⊕ β) :=
  fun top r j =>
    match s1 top r j with
    | .ok a => .ok (.inl a)
    | .error e1 =>
      match s2 top r j with
      | .ok b => .ok (.inr b)
      | .error e2 =>
        .error s!"multiple failures:\n{e1}\n\n{e2}"

/-! SchemaM for core schemas -/

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

def Type.toJsonSchema (c : «Type») : SchemaM c.toType :=
  match c with
  | .integer => JsonSchema.integer
  | .number  => JsonSchema.number
  | .boolean => JsonSchema.boolean
  | .string  => JsonSchema.string
  | .array   => JsonSchema.array any
  | .object  => JsonSchema.objectMap fun _ => any

def type : SchemaM «Type» := JsonSchema.ofLeanJson

/- TODO: schema schemas should be specified via structures,
but Lean structures currently don't have good enough support
for nested inductives for this to not be hugely painful. -/

structure Res where
  name : Lean.Ident
  descr : Option String
  type : Lean.Expr
  schema : Lean.Expr
  toJson : Lean.Expr
  default : Option Lean.Expr

def fromJson? (j : Lean.Json) : Except String Res := do
  let title       := Except.toOption <| j.getObjVal? "title"
  let description := Except.toOption <| j.getObjVal? "description"
  let nullable    := Except.toOption <| j.getObjVal? "nullable"
  let default     := Except.toOption <| j.getObjVal? "default"
  -- types
  let type        := Except.toOption <| j.getObjValAs? «Type» "type"
  let format      := Except.toOption <| j.getObjVal? "format"
  let enum        := Except.toOption <| j.getObjVal? "enum"
  -- int
  let minimum     := Except.toOption <| j.getObjVal? "minimum"
  let maximum     := Except.toOption <| j.getObjVal? "maximum"
  -- object
  let properties  := Except.toOption <| j.getObjVal? "properties"
  let required    := Except.toOption <| j.getObjVal? "required"
  -- array
  let items       := Except.toOption <| j.getObjVal? "items"
  -- combinators
  let allOf       := Except.toOption <| j.getObjVal? "allOf"
  let oneOf       := Except.toOption <| j.getObjVal? "oneOf"

  
  return sorry

end CoreSchema
