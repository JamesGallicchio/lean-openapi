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

/-! Primitive data types -/

def integer : JsonSchema Int where

def number : JsonSchema Lean.JsonNumber where

def string : JsonSchema String where

def boolean : JsonSchema Bool where

/-! Arrays -/

def array (s : JsonSchema α) : JsonSchema (Array α) where
  toJson x := .arr (x.map s.toJson)
  fromJson? x :=
    match x with
    | .arr a => a.mapM s.fromJson?
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
