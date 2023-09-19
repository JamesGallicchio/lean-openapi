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

import Http
import LeanOpenAPI.Std
import LeanOpenAPI.JsonSchema

namespace LeanOpenAPI

open Lean JsonSchema

namespace OpenAPI

structure PathTemplate where
  params : List String
  subst : (∀ s, s ∈ params → String) → String

def pathTemplate (s : String) : Except String PathTemplate := do
  if !s.startsWith "/" then
    throw "Expected path template to start with /"
  
  let params ← findVars 0 []
  return {
    params
    subst := fun f => params.attach.foldl (fun s ⟨v,h⟩ =>
        s.replace (pattern := s!"\{{v}}") (replacement := f v h)
      ) s
  }
where findVars (start : String.Pos) (acc : List String) : Except String (List String) := do
  if _hs : start < s.endPos then
    let leftBracIdx := String.posOfAux s '{' s.endPos start
    if s.atEnd leftBracIdx then
      return acc

    let rightBracIdx := String.posOfAux s '}' s.endPos (s.next leftBracIdx)
    if s.atEnd rightBracIdx then
      throw "mismatched { in path template"
      
    let var := { str := s, startPos := s.next leftBracIdx,
                  stopPos := rightBracIdx : Substring }
        |>.toString
    
    if var.any (· ∈ ['{', '}', '/', '?', '#']) then
      throw s!"path parameter name contains special characters: `{var}`"

    if _h : start < s.next rightBracIdx then
      findVars (s.next rightBracIdx) (var :: acc)
    else panic! "posOfAux indices messed up"
  else return acc
termination_by findVars start _ => s.endPos - start
decreasing_by
  simp_wf; simp [sizeOf, String.Pos._sizeOf_1]
  apply Nat.add_lt_add_left; apply Nat.sub_lt_sub_left
  repeat assumption

structure Reference where
  «$ref» : String
deriving ToJson, FromJson, Repr

def reference : JsonSchema Reference where

section Info

structure Contact where
  name  : Option string
  url   : Option string
  email : Option string
deriving ToJson, FromJson

def contact : JsonSchema Contact where

structure License where
  name : string
  url : Option string
deriving ToJson, FromJson

def license : JsonSchema License where

structure Info where
  title : string
  description : Option string
  termsOfService : Option string
  contact : Option contact
  license : Option license
  version : string
deriving ToJson, FromJson

def info : JsonSchema Info where

end Info

section Server

structure ServerVariable where
  enum : Option (array string)
  default : string
  description : Option string
deriving ToJson, FromJson

def serverVariable : JsonSchema ServerVariable where

structure Server where
  url : string
  description : Option string
  variables : Option (objectMap (fun _ => serverVariable))
deriving ToJson, FromJson

def server : JsonSchema Server where

end Server

structure ExternalDocs where
  description : Option string
  url : string
deriving ToJson, FromJson

def externalDocs : JsonSchema ExternalDocs where

section Parameter

inductive Parameter.In
| query | header | path | cookie
deriving ToJson, FromJson, DecidableEq

def parameter.in : JsonSchema Parameter.In where

structure Parameter where
  «in» : parameter.in
  name : string.withProperty "parameter name conditions" (fun s =>
      match «in».val with
      | .path => True
      | _ => True
  )
  description : Option string
  required : Option boolean
  deprecated : Option boolean
  allowEmptyValue : Option boolean
deriving ToJson, FromJson

def parameter : JsonSchema Parameter where

end Parameter

section Paths

structure RequestBody where
  --
deriving ToJson, FromJson

def requestBody : JsonSchema RequestBody where

structure Operation where
  tags : Option (array string)
  (summary description : Option string)
  externalDocs : Option externalDocs
  operationId : Option string
  parameters : Option (array (reference.orElse parameter))
  requestBody : Option (reference.orElse requestBody)
  --responses : Responses
  --callbacks : Lean.RBMap String (MaybeRef Callback)
  deprecated : Option boolean
  --security : Option (Array SecurityRequirement)
  servers : Option (array server)
deriving ToJson, FromJson

def operation : JsonSchema Operation where

structure PathItem (pt : PathTemplate) where
  summary : Option string
  description : Option string
  (get put post delete options head patch trace : Option operation)
  servers : Option (array server)
  parameters : Option (array (reference.orElse parameter)) 
deriving Inhabited, Repr, ToJson, FromJson

def pathItem (pt) : JsonSchema (PathItem pt) where

def paths : JsonSchema (RBNode String fun _ =>
    (pt : PathTemplate) × (Reference ⊕ PathItem pt)
  ) := objectMap (fun path =>
  guard (pathTemplate path) fun pt => reference.orElse (pathItem pt))

end Paths

structure Components where
  --schemas : Lean.RBMap String (MaybeRef Schema) compare
  --responses : Lean.RBMap String (MaybeRef Response) compare
  parameters : objectMap (fun _ => reference.orElse parameter)
  --examples : Lean.RBMap String (MaybeRef Example) compare
  --requestBodies : Lean.RBMap String (MaybeRef RequestBody) compare
  --headers : Lean.RBMap String (MaybeRef Header) compare
  --securitySchemes : Lean.RBMap String (MaybeRef SecurityScheme) compare
  --links : Lean.RBMap String (MaybeRef Link) compare
  --callbacks : Lean.RBMap String (MaybeRef Callback) compare
deriving ToJson, FromJson

structure OpenAPI where
  openapi : string
  info    : info
  servers     : Option <| array server
  paths       : paths
  components  : Option Components
  --security    : Option <| Array SecurityRequirement
  --tags        : Option <| Array Tag
  externalDocs : Option externalDocs
deriving ToJson, FromJson

#eval do
  let str ← IO.FS.readFile "examples/api.github.com.json"
  let json ← IO.ofExcept <| Lean.Json.parse str
  let spec : OpenAPI ← IO.ofExcept <| Lean.FromJson.fromJson? json
  let ⟨a,b,c⟩ ← IO.ofExcept <| Option.getDM (m := Except String) (spec.paths.val.lowerBound compare "/rz" none) (throw "hi")
  return a
