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

structure JsonSchema where
  validate : Lean.Json → Bool

namespace JsonSchema

def validates (s : JsonSchema) (j : Lean.Json) : Prop := s.validate j = true

end JsonSchema

structure ValidJson (s : JsonSchema) where
  json : Lean.Json
  isValid : s.validates json

/-! Primitive data types -/

def JsonSchema.integer : JsonSchema := ⟨(match · with | .num n => n.exponent = 0 | _ => false)⟩
def ValidJson.integer (j : ValidJson .integer) : Int :=
  match j with
  | ⟨.num n, _h⟩ => n.mantissa

def JsonSchema.number : JsonSchema := ⟨(match · with | .num _n => true | _ => false)⟩
def ValidJson.number (j : ValidJson .number) : Lean.JsonNumber :=
  match j with
  | ⟨.num n, _h⟩ => n

def JsonSchema.string : JsonSchema := ⟨(match · with | .str _n => true | _ => false)⟩
def ValidJson.string (j : ValidJson .string) : String :=
  match j with
  | ⟨.str s, _h⟩ => s

def JsonSchema.boolean : JsonSchema := ⟨(match · with | .bool _n => true | _ => false)⟩
def ValidJson.boolean (j : ValidJson .boolean) : Bool :=
  match j with
  | ⟨.bool b, _h⟩ => b

/-! Arrays -/

def JsonSchema.array (s : JsonSchema) : JsonSchema := ⟨(match · with | .arr a => a.all s.validate | _ => false)⟩
def ValidJson.array (j : ValidJson (.array s)) : Array (ValidJson s) :=
  match j with
  | ⟨.arr a, h⟩ => a.pmap (fun j' h' => ⟨j', by
    rcases h' with ⟨i,h'⟩
    simp [JsonSchema.validates, JsonSchema.array] at h
    have := Array.forall_of_all _ h i
    rw [h'] at this; exact this
    ⟩)

/-! Objects -/

structure JsonSchema.ObjectField where
  name : String
  isOpt : Bool
  schema : JsonSchema

/-- Validates a value if it is an object.
  
  For each `{name,isOpt,schema} ∈ fields`, if `isOpt = true` then `name`
  MUST be a field of the object. Furthermore, if `name : value` in the object,
  then `schema` validates `value`. -/
def JsonSchema.object (fields : List JsonSchema.ObjectField) : JsonSchema where
  validate j :=
    match j with
    | .obj m => fields.all (fun {name, isOpt, schema} =>
      match m.find compare name with
      | some j => schema.validate j
      | none => isOpt)
    | _ => false
def ValidJson.objectHead (j : ValidJson (.object ({name,isOpt:=false,schema}::fs)))
  : ValidJson schema :=
  match j with
  | ⟨.obj m,h⟩ =>
    have h := by simp [JsonSchema.object, JsonSchema.validates] at h; exact h.1
    match h' : m.find compare name with
    | some j => ⟨j, by simp [h'] at h; exact h⟩
    | none   => by simp [h'] at h
def ValidJson.objectHeadOpt (j : ValidJson (.object ({name,isOpt:=true,schema}::fs)))
  : Option (ValidJson schema) :=
  match j with
  | ⟨.obj m,h⟩ =>
    have h := by simp [JsonSchema.object, JsonSchema.validates] at h; exact h.1
    match h' : m.find compare name with
    | some j => some ⟨j, by simp [h'] at h; exact h⟩
    | none   => none

theorem JsonSchema.objectTail (h : JsonSchema.object (f::fs) |>.validates j)
  : JsonSchema.object fs |>.validates j := by
  cases j <;>
    simp [validates, object] at h ⊢
  exact h.2

-- TODO: a macro to get object values by name alone

/-! Subtypes (arbitrary properties on top of a given schema) -/

def JsonSchema.withProperty (s : JsonSchema) (p : ValidJson s → Bool) : JsonSchema where
  validate j :=
    if h : s.validate j then
      p ⟨j, h⟩
    else false
def ValidJson.val (j : ValidJson (.withProperty s p)) : ValidJson s :=
  match j with
  | ⟨json, h⟩ => ⟨json, by
    simp [JsonSchema.validates, JsonSchema.withProperty] at h
    split at h
    · assumption
    · contradiction⟩
def ValidJson.property (j : ValidJson (.withProperty s p)) : p j.val := by
  rcases j with ⟨json,h⟩
  simp [JsonSchema.validates, JsonSchema.withProperty] at h
  split at h <;> try contradiction
  simp [val, h]

/-! Either -/

def JsonSchema.orElse (s1 s2 : JsonSchema) : JsonSchema where
  validate j := s1.validate j || s2.validate j
def ValidJson.orElse (j : ValidJson (.orElse s1 s2)) : (ValidJson s1) ⊕ (ValidJson s2) :=
  match j with
  | ⟨j, h⟩ =>
  if h' : s1.validate j then
    .inl ⟨j, h'⟩
  else
    .inr ⟨j, by simp [JsonSchema.validates, JsonSchema.orElse, h'] at h; exact h⟩

/-! -/
