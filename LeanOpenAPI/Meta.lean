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

import LeanOpenAPI.OpenAPI

namespace LeanOpenAPI.Meta

open OpenAPI

open Lean Elab Meta Command

scoped elab "genOpenAPI!" s:str : command => do
  let ctx ← read
  let f : System.FilePath := s.getString

  let fileContents ← IO.FS.readFile f
  let json : Lean.Json ←
    match Lean.Json.parse fileContents with
    | .ok j => pure j
    | .error e =>
      throwError s!"error parsing json from file: {e}"
 
  let api ←
    match fromJson? json with
    | .ok (j : OpenAPI) => pure j
    | .error e =>
      throwError s!"failed to validate json against OAI schema: {e}"

  let server ← do
    let servers := api.servers.map (·.val) |>.getD #[] |>.map (·.val)
    match servers[0]? with
    | none => throwError s!"API does not list a top-level server!"
    | some s =>
    if servers.size > 1 then
      logWarning s!"API lists multiple top-level servers..."
    pure s

  for ⟨path, pt, item⟩ in api.paths.val.toArray do
    if item.«$ref».isSome then
      logWarning s!"Path {path} has a $ref item. This is not currently supported."; continue
    
    if item.servers.isSome then
      logWarning s!"Path {path} lists more servers (not supported)"; continue

    match
      item.parameters.map (·.val)
        |>.getD #[]
        |>.mapM (fun p => show Except String _ from do
          let p ← JsonSchema.resolveRefOr json p
          return p.val)
    with
    | .error e =>
      logWarning s!"Path {path} parameter resolution failed:\n{e}"
      continue
    | .ok itemParams =>

    for (method, ⟨op⟩) in item.ops do
      let some id := op.operationId.map (mkIdent ·.val)
        | logWarning s!"{method} on {path} does not have operation id"; continue
      
      -- Construct the docstring from a bunch of potential doc elements
      let docstring :=
        [ item.summary.map ("### " ++·.val)
        , op.summary.map ("#### " ++ ·.val)
        , item.description.map (·.val)
        , op.description.map (·.val)
        , op.externalDocs.map (fun ed =>
          s!"{ed.val.description.map (·.val) |>.getD "Documentation"
            }: {ed.val.url.val}")
        ].filterMap _root_.id
        |> String.intercalate "\n\n"
      
      let deprecated := op.deprecated.map (·.val) |>.getD false

      match
        op.parameters.map (·.val)
        |>.getD #[]
        |>.mapM (fun p => show Except String _ from do
          let p ← JsonSchema.resolveRefOr json p
          return p.val)
      with
      | .error e => logWarning s!"Error processing parameters for {method} on {path}:\n{e}"
      | .ok params =>

      elabCommand (← `(
        $(Lean.mkDocComment docstring):docComment
        def $id := $(quote <| (toJson (op)).pretty)
      ))
      
      if deprecated then
        elabCommand (← `(
          attribute [deprecated] $id
        ))

namespace Examples.GitHub
genOpenAPI! "examples/api.github.com.json"
end GitHub

#eval IO.println GitHub.«users/unblock»
