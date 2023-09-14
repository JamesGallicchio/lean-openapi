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

namespace LeanOpenAPI

structure Contact where
  name  : Option String
  url   : Option String
  email : Option String
deriving Repr, Lean.FromJson

structure License where
deriving Repr, Lean.FromJson

structure Info where
  title : String
  description : Option String
  termsOfService : Option String
  contact : Option Contact
  license : Option License
  version : String
deriving Repr, Lean.FromJson

structure ServerVariable where
  enum : Option (Array String)
  default : String
  description : Option String
deriving Repr, Lean.FromJson

structure Paths where
deriving Repr, Lean.FromJson

structure Server where
  url : String
  description : Option String
  variables : Option <| Lean.RBMap String ServerVariable compare
deriving Repr, Lean.FromJson

structure OpenAPI where
  openapi : String
  info    : Info
  servers     : Option <| Array Server
  paths       : Paths
  components  : Option Components
  security    : Option <| Array SecurityRequirement
  tags        : Option <| Array Tag
  externalDocs : Option ExternalDocs
deriving Repr, Lean.FromJson

#eval do
  let str ← IO.FS.readFile "examples/api.github.com.json"
  let json ← IO.ofExcept <| Lean.Json.parse str
  let spec : OpenAPI ← IO.ofExcept <| Lean.FromJson.fromJson? json
  return spec
