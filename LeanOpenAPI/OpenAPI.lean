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
deriving ToJson, FromJson, Repr, Inhabited

def parameter.in : JsonSchema Parameter.In :=
  JsonSchema.ofLeanJson.addFailingJson

structure Parameter where
  «in» : parameter.in
  name : string
  description : Option string
  required : Option boolean
  deprecated : Option boolean
  allowEmptyValue : Option boolean
  style : Option string
  explode : Option boolean
  allowReserved : Option boolean
  schema : Option coreSchema
  «example» : Option any
  examples : Option (objectMap fun _ => any)
deriving ToJson, FromJson

def parameter : JsonSchema Parameter :=
  JsonSchema.ofLeanJson.addFailingJson

end Parameter

section RequestBody

structure MediaType where
  schema : Option Lean.Json
  «example» : Option Lean.Json
  examples : Option Lean.Json
  encoding : Option Lean.Json
deriving ToJson, FromJson

def mediaType : JsonSchema MediaType := .ofLeanJson

structure RequestBody where
  description : Option string
  content : objectMap (fun _ => mediaType)
  required : Option boolean
deriving ToJson, FromJson

def requestBody : JsonSchema RequestBody where

end RequestBody

section Responses

structure Header where
  description : Option string
  required : Option boolean
  deprecated : Option boolean
  allowEmptyValue : Option boolean
  style : Option string
  explode : Option boolean
  allowReserved : Option boolean
  schema : Option any
  «example» : Option any
  examples : Option (objectMap fun _ => any)
deriving ToJson, FromJson

def header : JsonSchema Header := JsonSchema.ofLeanJson

structure Response where
  description : string
  headers : Option (objectMap fun _ => refObj.orElse header)
  content : Option (objectMap fun _ => mediaType)
  links : Option (objectMap fun _ => refObj.orElse any)
deriving ToJson, FromJson

def response : JsonSchema Response := .ofLeanJson

structure Responses where
  map : Lean.RBNode String (fun _ => RefObj ⊕ Response)

def Responses.get (r : Responses) (code : Http.StatusCode) : Option (RefObj ⊕ Response) :=
  let code := toString code.val
  r.map.find compare code
  |>.orElse fun () =>
  r.map.find compare s!"{code.get 0}XX"
  |>.orElse fun () =>
  r.map.find compare "default"

def responses : JsonSchema Responses :=
  JsonSchema.objectMap (fun _ => refObj.orElse response)
  |>.map (⟨·⟩) (·.map)

end Responses

section Paths

structure Operation where
  tags : Option (array string)
  (summary description : Option string)
  externalDocs : Option externalDocs
  operationId : Option string
  parameters : Option (array (refObj.orElse parameter))
  requestBody : Option (refObj.orElse requestBody)
  responses : Option responses
  --callbacks : Lean.RBMap String (MaybeRef Callback)
  deprecated : Option boolean
  --security : Option (Array SecurityRequirement)
  servers : Option (array server)
deriving ToJson, FromJson, Inhabited

def operation : JsonSchema Operation where

structure PathItem (pt : PathTemplate) where
  «$ref» : Option reference
  summary : Option string
  description : Option string
  (get put post delete options head patch trace : Option operation)
  servers : Option (array server)
  parameters : Option (array (refObj.orElse parameter))
deriving Inhabited, Repr, ToJson, FromJson

def PathItem.ops (i : PathItem pt) : List (Http.Method × operation) :=
  [ i.get     |>.map (⟨.GET, ·⟩)
  , i.put     |>.map (⟨.PUT, ·⟩)
  , i.post    |>.map (⟨.POST, ·⟩)
  , i.delete  |>.map (⟨.DELETE, ·⟩)
  , i.options |>.map (⟨.OPTIONS, ·⟩)
  , i.head    |>.map (⟨.HEAD, ·⟩)
  , i.patch   |>.map (⟨.PATCH, ·⟩)
  , i.trace   |>.map (⟨.TRACE, ·⟩)
  ].filterMap id

def pathItem (pt) : JsonSchema (PathItem pt) where

def paths : JsonSchema (RBNode String fun _ =>
    (pt : PathTemplate) × PathItem pt
  ) := objectMap (fun path => guard (pathTemplate path) pathItem)

end Paths

structure Components where
  --schemas         : Option <| objectMap (fun _ => reference.orElse schema)
  responses       : Option <| objectMap (fun _ => reference.orElse response)
  parameters      : Option <| objectMap (fun _ => reference.orElse parameter)
  --examples        : Option <| objectMap (fun _ => reference.orElse example)
  requestBodies   : Option <| objectMap (fun _ => reference.orElse requestBody)
  --headers         : Option <| objectMap (fun _ => reference.orElse header)
  --securitySchemes : Option <| objectMap (fun _ => reference.orElse securityScheme)
  --links           : Option <| objectMap (fun _ => reference.orElse link)
  --callbacks       : Option <| objectMap (fun _ => reference.orElse callback)
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
