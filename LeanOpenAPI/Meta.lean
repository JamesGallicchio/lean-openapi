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
def explicitBinderF := Parser.Term.explicitBinder false

section Endpoint
variable (serverUrlId : Ident) (path : PathTemplate) (item : PathItem)
          (method : Http.Method) (op : Operation)

/-- Construct the docstring from a bunch of potential doc elements -/
def genDocstring (params : Array (Parameter × JsonSchema.CoreSchema.Res)) : String :=
  [ item.summary.map ("### " ++ ·)
  , op.summary.map ("#### " ++ ·)
  , item.description
  , op.description
  , op.externalDocs.map (fun ed =>
    s!"{ed.description |>.getD "Documentation" |>.val}: {ed.url.val}")
  , some (
      params.foldl (init := "#### Parameters") (fun s (param, schema) =>
      s ++ "\n\n" ++ String.intercalate "\n" ([
        some s!"##### {param.name.val}",
        param.description,
        schema.docs.map (s!"```yaml{·}\n```")
        ].filterMap _root_.id)
    ))
  ].filterMap _root_.id
  |> String.intercalate "\n\n"

/-- Handle path parameters -/
def genPathHandler (params : Array Parameter) (urlId : Ident) : TermElabM (TSyntax `doElem) := do
  let pathParams   := params.filter (·.in.val = .path)
  let pathParamStrLits  : Array StrLit := pathParams.map (Syntax.mkStrLit ·.name.val)
  let pathParamNames    : Array Ident := pathParams.map (mkIdent ·.name.val)
  `(doElem|
    let $urlId := ($urlId).appendPath <|
        PathTemplate.subst $(quote path) (fun s _h =>
          match s with
          $[| $pathParamStrLits:term => $pathParamNames:term]*
          | _ => default)
  )

/-- Handle query parameters -/
def genQueryHandler (params : Array Parameter) (urlId : Ident) : TermElabM (TSyntax `doElem) := do
  let queryParams  := params.filter (·.in.val = .query)
  let queryParamStrLits : Array StrLit := queryParams.map (Syntax.mkStrLit ·.name.val)
  let queryParamNames   : Array Ident := queryParams.map (mkIdent ·.name.val)
  `(doElem|
    let $urlId := ($urlId).withQuery <| String.intercalate "&" [
        $[$queryParamStrLits ++ "=" ++ $queryParamNames],*
    ]
  )

/-- Handle header parameters -/
def genHeaderHandler (params : Array Parameter) (headerId : Ident) : TermElabM (TSyntaxArray `doElem) := do
  let headerParams := params.filter (·.in.val = .header)
  let headerParamStrLits : Array StrLit := headerParams.map (Syntax.mkStrLit ·.name.val)
  let headerParamNames   : Array Ident := headerParams.map (mkIdent ·.name.val)
  return ← (headerParamStrLits.zip headerParamNames).mapM (fun (strLit, name) =>
    `(doElem| let $headerId := ($headerId).add $strLit $name)
  )

/-- Handle cookie parameters -/
def genCookieHandler (params : Array Parameter) (headerId : Ident) : TermElabM (TSyntaxArray `doElem) := do
  let cookieParams := params.filter (·.in.val = .cookie)
  let cookieParamStrLits : Array StrLit := cookieParams.map (Syntax.mkStrLit ·.name.val)
  let cookieParamNames   : Array Ident := cookieParams.map (mkIdent ·.name.val)
  return ← (cookieParamStrLits.zip cookieParamNames).mapM (fun (strLit, name) =>
    `(doElem| let $headerId := ($headerId).add $strLit $name)
  )

/-- generate endpoint for the given arguments, returning the command to be elaborated -/
def genEndpoint : TermElabM (TSyntax `command) := do
  let some id := op.operationId.map (mkIdent ∘ Name.mkSimple)
    | throwError s!"{method} on {path.raw} does not have operation id"
    
  let deprecated := op.deprecated |>.getD false

  let params := Array.flatten #[op.parameters.getD #[], item.parameters.getD #[]]

  let paramSchemas ←
    params.mapM (fun p => do
      match p.schema, p.content with
      | none, none     => throwError "{method} on {path.raw} has parameter {p.name.val} with no schema or content"
      | some _, some _ => throwError "{method} on {path.raw} has parameter {p.name.val} with both schema and content"
      | none, some _   => throwError "{method} on {path.raw} parameter {p.name.val} has content type (not yet supported)"
      | some s, none => return (p, ← s.val))

  let docstring := genDocstring item op paramSchemas

  let paramNames := paramSchemas.map (mkIdent ·.1.name.val)
  let paramToStrings := paramSchemas.map (·.2.toString)
  let paramTypes := paramSchemas.map (·.2.type)
  
  let urlId := mkIdent `url
  let pathHandler ← genPathHandler path params urlId
  let queryHandler ← genQueryHandler params urlId

  let headerId := mkIdent `header
  let headerHandler ← genHeaderHandler params headerId
  let cookieHandler ← genCookieHandler params headerId

  let mainCmd ← `(
    $(Lean.mkDocComment docstring):docComment
    def $id:ident $[ ($paramNames:ident : $paramTypes:term) ]* : Http.Request Unit :=
      Id.run do
      -- serialize all parameters as strings
      $[let $paramNames:ident := $paramToStrings:term $(_root_.id paramNames):ident]*
      -- put parameters into the url
      let $urlId := $serverUrlId
      $pathHandler:doElem
      $queryHandler:doElem
      -- put parameters into the header
      let $headerId := Http.Headers.empty
      $[$headerHandler:doElem]*
      $[$cookieHandler:doElem]*
      return Http.Request.mk
        (method := $(quote method))
        (url := $urlId)
        (version := .HTTP_1_1)
        (headers := $headerId)
        (body := ())
  )
  if deprecated.val then
    return ← `($mainCmd:command attribute [deprecated] $id)
  else return mainCmd

end Endpoint

scoped elab "genOpenAPI!" s:str : command => do
  let f : System.FilePath := s.getString

  let fileContents ← IO.FS.readFile f
  let json : Lean.Json ←
    match Lean.Json.parse fileContents with
    | .ok j => pure j
    | .error e =>
      throwError s!"error parsing json from file: {e}"
 
  let api ←
    match openAPI.run json with
    | .ok (j : OpenAPI) => pure j
    | .error e =>
      throwError s!"failed to validate json against OAI schema: {e}"

  let server ← do
    let servers : Array _ := api.servers |>.getD #[]
    match servers[0]? with
    | none => throwError s!"API does not list a top-level server!"
    | some s =>
    if servers.size > 1 then
      logWarning s!"API lists multiple top-level servers..."
    pure s
  
  if server.variables.isSome then
    throwError s!"server {server.url.val} contains server variables (not yet supported)"

  let serverUrlId := mkIdent `serverUrl
  elabCommand <| ← `(
    def $serverUrlId : Http.URI :=
      (Http.URI.fromString? $(Syntax.mkStrLit server.url)).get!
  )

  for ⟨path, pt, item⟩ in api.paths.toArray do
    if item.«$ref».isSome then
      logWarning s!"Path {path} has a $ref item. This is not currently supported."; continue
    
    if item.servers.isSome then
      logWarning s!"Path {path} lists more servers (not supported)"; continue

    for (method, op) in item.ops do
      try
        let cmds ← liftTermElabM <| genEndpoint serverUrlId pt item method op
        elabCommand cmds
      catch e =>
        logWarning s!"{method} {path}: skipping due to error:\n{← e.toMessageData.toString}"
