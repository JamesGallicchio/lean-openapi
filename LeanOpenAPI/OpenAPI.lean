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

inductive MaybeRef (T : Type u)
| notRef (t : T)
| ref (path : String)
deriving Repr

namespace MaybeRef

instance [Lean.FromJson T] : Lean.FromJson (MaybeRef T) where
  fromJson? json :=
    let tryRef : Except _ _ := do
      let map ← json.getObj?
      guard <| map.size = 1
      let some (.str r) := map.find compare "$ref" | default
      return r
    (.ref <$> tryRef).orElseLazy (fun () => .notRef <$> Lean.FromJson.fromJson? json)

end MaybeRef

section Info

structure Contact where
  name  : Option String
  url   : Option String
  email : Option String
deriving Repr, Lean.FromJson, Inhabited

structure License where
  name : String
  url : Option String
deriving Repr, Lean.FromJson, Inhabited

structure Info where
  title : String
  description : Option String
  termsOfService : Option String
  contact : Option Contact
  license : Option License
  version : String
deriving Repr, Lean.FromJson, Inhabited

end Info

section Server

structure ServerVariable where
  enum : Option (Array String)
  default : String
  description : Option String
deriving Repr, Lean.FromJson, Inhabited

structure Server where
  url : String
  description : Option String
  variables : Option <| Lean.RBMap String ServerVariable compare
deriving Repr, Lean.FromJson, Inhabited

end Server

structure ExternalDocs where
  description : Option String
  url : String
deriving Repr, Lean.FromJson, Inhabited

section Parameter

inductive Parameter.In
| query | header | path | cookie
deriving Repr, Lean.FromJson, Inhabited

structure Parameter where
  name : String
  «in» : Parameter.In
  description : Option String
  required : Option Bool
  deprecated : Option Bool
  allowEmptyValue : Option Bool
deriving Repr, Lean.FromJson, Inhabited  

end Parameter

section Paths

structure Operation where
  tags : Option (Array String)
  (summary description : Option String)
  externalDocs : Option ExternalDocs
  operationId : Option String
  parameters : Option (Array (MaybeRef Parameter))
  --requestBody : Option (MaybeRef RequestBody)
  --responses : Responses
  --callbacks : Lean.RBMap String (MaybeRef Callback)
  deprecated : Option Bool
  --security : Option (Array SecurityRequirement)
  servers : Option (Array Server)
deriving Repr, Lean.FromJson, Inhabited

structure PathItem where
  summary : Option String
  description : Option String
  (get put post delete options head patch trace : Option Operation)
  servers : Option (Array Server)
  parameters : Option (Array (MaybeRef Parameter)) 
deriving Repr, Lean.FromJson, Inhabited

def Paths := Lean.RBMap String PathItem compare
deriving Repr, Lean.FromJson, Inhabited

end Paths

structure Components where
  --schemas : Lean.RBMap String (MaybeRef Schema) compare
  --responses : Lean.RBMap String (MaybeRef Response) compare
  parameters : Lean.RBMap String (MaybeRef Parameter) compare
  --examples : Lean.RBMap String (MaybeRef Example) compare
  --requestBodies : Lean.RBMap String (MaybeRef RequestBody) compare
  --headers : Lean.RBMap String (MaybeRef Header) compare
  --securitySchemes : Lean.RBMap String (MaybeRef SecurityScheme) compare
  --links : Lean.RBMap String (MaybeRef Link) compare
  --callbacks : Lean.RBMap String (MaybeRef Callback) compare
deriving Repr, Lean.FromJson, Inhabited

structure OpenAPI where
  openapi : String
  info    : Info
  servers     : Option <| Array Server
  paths       : Paths
  components  : Option Components
  --security    : Option <| Array SecurityRequirement
  --tags        : Option <| Array Tag
  externalDocs : Option ExternalDocs
deriving Repr, Lean.FromJson, Inhabited

#eval do
  let str ← IO.FS.readFile "examples/api.github.com.json"
  let json ← IO.ofExcept <| Lean.Json.parse str
  let spec : OpenAPI ← IO.ofExcept <| Lean.FromJson.fromJson? json
  return spec.paths.lowerBound "/h"
