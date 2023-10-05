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
deriving Inhabited

genStructSchema contact for Contact

structure License where
  name : string
  url  : Option string

genStructSchema license for License

structure Info where
  title : string
  version : string
  description     : Option string
  termsOfService  : Option string
  contact         : Option contact
  license         : Option license

genStructSchema info for Info

end Info

section Server

structure ServerVariable where
  default : string
  enum        : Option <| array string
  description : Option <| string

genStructSchema serverVariable for ServerVariable

structure Server where
  url : string
  description : Option string
  variables : Option <| objectMap (fun _ => serverVariable)

genStructSchema server for Server

end Server

structure ExternalDocs where
  description : Option string
  url : string

genStructSchema externalDocs for ExternalDocs

section Parameter

inductive Parameter.In
| query | header | path | cookie
deriving ToJson, FromJson, Repr, Inhabited

def parameter.in : SchemaM Parameter.In := JsonSchema.ofLeanJson

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
  schema : Option any
  «example» : Option any
  examples : Option (objectMap fun _ => any)

genStructSchema parameter for Parameter

end Parameter

section RequestBody

structure MediaType where
  schema : Option any
  «example» : Option any
  examples : Option any
  encoding : Option any

genStructSchema mediaType for MediaType

structure RequestBody where
  description : Option string
  content : objectMap (fun _ => mediaType)
  required : Option boolean

genStructSchema requestBody for RequestBody

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

genStructSchema header for Header

structure Response where
  description : string
  headers : Option (objectMap fun _ => maybeRefObj header)
  content : Option (objectMap fun _ => mediaType)
  links : Option (objectMap fun _ => maybeRefObj any)

genStructSchema response for Response

def Responses := RBNode String fun _ => Response

def responses : SchemaM Responses :=
  JsonSchema.objectMap fun _ => maybeRefObj response

def Responses.get (r : Responses) (code : Http.StatusCode) : Option Response :=
  let code := toString code.val
  r.find compare code
  |>.orElse fun () =>
  r.find compare s!"{code.get 0}XX"
  |>.orElse fun () =>
  r.find compare "default"

end Responses

section Paths

structure Operation where
  tags        : Option <| array string
  summary     : Option <| string
  description : Option <| string
  externalDocs: Option <| externalDocs
  operationId : Option <| string
  parameters  : Option <| array (maybeRefObj parameter)
  requestBody : Option <| maybeRefObj requestBody
  responses   : Option <| responses
  --callbacks   : Option <| objectMap (fun _ => maybeRefObj callback)
  deprecated  : Option <| boolean
  --security    : Option <| Array securityRequirement
  servers     : Option <| array server

genStructSchema operation for Operation

structure PathItem where
  «$ref» : Option reference
  summary : Option string
  description : Option string
  get : Option operation
  put : Option operation
  post : Option operation
  delete : Option operation
  options : Option operation
  head : Option operation
  patch : Option operation
  trace : Option operation
  servers : Option (array server)
  parameters : Option (array (maybeRefObj parameter))

genStructSchema pathItem for PathItem

def PathItem.ops (i : PathItem) : List (Http.Method × operation) :=
  [ i.get     |>.map (⟨.GET, ·⟩)
  , i.put     |>.map (⟨.PUT, ·⟩)
  , i.post    |>.map (⟨.POST, ·⟩)
  , i.delete  |>.map (⟨.DELETE, ·⟩)
  , i.options |>.map (⟨.OPTIONS, ·⟩)
  , i.head    |>.map (⟨.HEAD, ·⟩)
  , i.patch   |>.map (⟨.PATCH, ·⟩)
  , i.trace   |>.map (⟨.TRACE, ·⟩)
  ].filterMap id


def Paths := RBNode String fun path => guard (pathTemplate path) (fun _ => pathItem)
def paths : SchemaM Paths := objectMap fun path => guard (pathTemplate path) (fun _ => pathItem)

end Paths

structure Components where
  --schemas         : Option <| objectMap (fun _ => reference.orElse schema)
  responses       : Option <| objectMap (fun _ => maybeRefObj response)
  parameters      : Option <| objectMap (fun _ => maybeRefObj parameter)
  --examples        : Option <| objectMap (fun _ => reference.orElse example)
  requestBodies   : Option <| objectMap (fun _ => maybeRefObj requestBody)
  --headers         : Option <| objectMap (fun _ => reference.orElse header)
  --securitySchemes : Option <| objectMap (fun _ => reference.orElse securityScheme)
  --links           : Option <| objectMap (fun _ => reference.orElse link)
  --callbacks       : Option <| objectMap (fun _ => reference.orElse callback)

genStructSchema components for Components

structure OpenAPI where
  openapi : string
  info    : info
  servers     : Option <| array server
  paths       : paths
  components  : Option components
  --security    : Option <| Array SecurityRequirement
  --tags        : Option <| Array Tag
  externalDocs : Option externalDocs

genStructSchema openAPI for OpenAPI
