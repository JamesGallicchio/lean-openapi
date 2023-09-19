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

#eval do return license.toJson <| ← license.fromJson? (← Json.parse "{\"name\":\"hi\", \"url\":\"bye\"}")

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
  parameters : Option (array (parameter.orElse reference))
  requestBody : Option (requestBody.orElse reference)
  --responses : Responses
  --callbacks : Lean.RBMap String (MaybeRef Callback)
  deprecated : Option boolean
  --security : Option (Array SecurityRequirement)
  servers : Option (array server)
deriving ToJson, FromJson

def operation : JsonSchema Operation where

structure PathItem where
  summary : Option string
  description : Option string
  (get put post delete options head patch trace : Option operation)
  servers : Option (array server)
  parameters : Option (array (parameter.orElse reference)) 
deriving Inhabited, Repr, ToJson, FromJson

def pathItem : JsonSchema PathItem where

def paths := objectMap (fun s => reference.orElse pathItem)

end Paths

structure Components where
  --schemas : Lean.RBMap String (MaybeRef Schema) compare
  --responses : Lean.RBMap String (MaybeRef Response) compare
  --parameters : Lean.RBMap String (MaybeRef Parameter) compare
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
  return spec.paths.val.any (fun _ => Sum.isLeft)
