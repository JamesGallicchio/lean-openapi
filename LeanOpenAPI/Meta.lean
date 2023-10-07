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

/-- Construct the docstring from a bunch of potential doc elements -/
def genDocstring (item : PathItem) (op : Operation)
      (params : Array (Parameter × JsonSchema.CoreSchema.Res))
      (bodyDocs : Option String)
  : String :=
  [ item.summary.map ("### " ++ ·)
  , op.summary.map ("#### " ++ ·)
  , item.description
  , op.description
  , op.externalDocs.map (fun ed =>
    s!"{ed.description |>.getD "Documentation" |>.val}: {ed.url.val}")
  , bodyDocs.map (s!"#### Body\n{·}")
  , some (
      params.foldl (init := "#### Parameters") (fun s (param, schema) =>
      s ++ "\n\n" ++ String.intercalate "\n" ([
        some s!"##### {param.name.val}{
          if (param.required.isEqSome (α := Bool) true)
          then ""
          else " (optional)"}",
        param.description,
        schema.docs.map (s!"```yaml{·}\n```")
        ].filterMap _root_.id)
    ))
  ].filterMap _root_.id
  |> String.intercalate "\n\n"

/-- Handle path parameters -/
def genPathHandler (path : PathTemplate) (paramSchemas : Array (Parameter × JsonSchema.CoreSchema.Res)) (urlId : Ident)
    : TermElabM (TSyntax `doElem) := do
  let pathParams   := paramSchemas.filter (·.1.in.val = .path)
  for (p,_) in pathParams do
    if !(p.required.isEqSome (α := Bool) true) then
      throwError "Parameter {p.name.val} is path parameter, but is not required"
  
  let pathParamStrLits : Array StrLit := pathParams.map (Syntax.mkStrLit ·.1.name.val)
  let pathParamNames   : Array Ident := pathParams.map (mkIdent ·.1.name.val)
  let pathParamToString: Array Term := pathParams.map (·.2.toString)
  `(doElem|
    let $urlId := ($urlId).appendPath <|
      LeanOpenAPI.OpenAPI.PathTemplate.subst ($(quote path)) (fun s _h =>
          match s with
          $[| $pathParamStrLits:term => $pathParamToString:term $pathParamNames:term]*
          | _ => default)
  )

/-- Handle query parameters -/
def genQueryHandler (paramSchemas : Array (Parameter × JsonSchema.CoreSchema.Res)) (urlId : Ident)
    : TermElabM (TSyntax `doElem) := do
  let queryStrOpts ← paramSchemas.filter (·.1.in.val = .query)
    |>.mapM (fun (p,s) =>
      let strLit := Syntax.mkStrLit p.name.val
      let ident := mkIdent p.name.val
      if p.required.isEqSome (α := Bool) true then
        `(some <| $strLit ++ "=" ++ $s.toString $ident)
      else
        `(($ident).map ($strLit ++ "=" ++ $s.toString ·))
      )
  if queryStrOpts.isEmpty then
    `(doElem| let $urlId := $urlId )
  else
    `(doElem|
      let $urlId := ($urlId).withQuery <| String.intercalate "&" (
        List.filterMap id [
          $[$queryStrOpts],*
        ])
  )

/-- Handle header parameters -/
def genHeaderHandler (paramSchemas : Array (Parameter × JsonSchema.CoreSchema.Res)) (headerId : Ident)
    : TermElabM (TSyntaxArray `doElem) := do
  let headerParams := paramSchemas.filter (·.1.in.val = .header)
  return ← headerParams.mapM (fun (p,r) => do
    let strLit := Syntax.mkStrLit p.name.val
    let ident := mkIdent p.name.val
    let toString :=
      if p.required.isEqSome (α := Bool) true
      then r.toString
      else ← `(Option.map $r.toString)
    `(doElem| let $headerId := ($headerId).add (Http.HeaderName.ofHeaderString $strLit) ($toString $ident))
  )

/-- Handle cookie parameters -/
def genCookieHandler (paramSchemas : Array (Parameter × JsonSchema.CoreSchema.Res)) (headerId : Ident)
    : TermElabM (TSyntaxArray `doElem) := do
  let cookieParams := paramSchemas.filter (·.1.in.val = .cookie)
  return ← cookieParams.mapM (fun (p,r) => do
    let strLit := Syntax.mkStrLit p.name.val
    let ident := mkIdent p.name.val
    let toString :=
      if p.required.isEqSome (α := Bool) true
      then r.toString
      else ← `(Option.map $r.toString)
    `(doElem| let $headerId := ($headerId).add (Http.HeaderName.ofHeaderString $strLit) ($toString $ident))
  )

/-- from a request body, get a docstring, content-type string,
  binder, request body type, and request body value -/
def genRequestBody (rb : RequestBody) : TermElabM <|
    String × String × TSyntax `Lean.Parser.Term.bracketedBinderF × Term × Term
  := do
  if !(rb.required.isEqSome true (α := Bool)) then
    logWarning s!"request body not required; currently unsupported"

  let ⟨ct, mt⟩ ← do
    let arr := rb.content.toArray
    if h : arr.size > 0 then
      let res := arr[0]
      if arr.size > 1 then
        logWarning s!"request body has multiple content types. using {res.1}.\n{repr arr}"
      pure res
    else
      throwError "request body has no content types listed"
  match mt.schema, mt.encoding with
  | _, some enc =>
    throwError s!"request body supports content type {ct} with an encoding:\n{
      enc.val.pretty}"
  | none, none =>
    throwError s!"request body supports content type {ct} but does not provide a schema for it"
  | some schema, none =>
  let res ← schema.toRes
  let body : Ident := mkIdent `body
  let binder ← `(Lean.Parser.Term.bracketedBinderF| ($body : $res.type))
  let type ← `(String)
  let val ← `($res.toString $body)
  let docs := [
      rb.description
    , res.docs.map (s!"```{·}\n```")
    ].filterMap id |> String.intercalate "\n"
  return (docs, ct, binder, type, val)

/-- generate endpoint for the given arguments, returning the command to be elaborated -/
def genEndpoint (serverUrlId : Ident) (path : PathTemplate) (item : PathItem)
                (method : Http.Method) (op : Operation)
    : TermElabM (TSyntax `command) := do
  let some id := op.operationId.map (mkIdent ∘ Name.mkSimple)
    | throwError s!"no operation id"
    
  if op.security.isSome then
    let secs := op.security.get!.val
    throwError s!"security not yet supported
{secs.map (fun sec =>
s!"{sec.toArray}"
)}
"

  let deprecated := op.deprecated |>.getD false

  let params := Array.flatten #[op.parameters.getD #[], item.parameters.getD #[]]

  let paramSchemas : Array (Parameter × JsonSchema.CoreSchema.Res) ←
    params.mapM (fun p => do
      match p.schema, p.content with
      | none, none     => throwError "parameter {p.name.val} has no schema or content"
      | some _, some _ => throwError "parameter {p.name.val} has both schema and content"
      | none, some _   => throwError "parameter {p.name.val} has content type (not yet supported)"
      | some s, none =>
      let s ← s.val.toRes
      return (p, s)
    )

  let paramBinders : Array (TSyntax `Lean.Parser.Term.bracketedBinderF) ←
    paramSchemas.mapM (fun (p,s) =>
      if p.required.isEqSome true (α := Bool) then
        `(Lean.Parser.Term.bracketedBinderF| ($(mkIdent p.name.val):ident : $(s.type):term) )
      else
        `(Lean.Parser.Term.bracketedBinderF| ($(mkIdent p.name.val):ident : Option $(s.type):term := none) )
    )
  
  let urlId := mkIdent `url
  let pathHandler ← genPathHandler path paramSchemas urlId
  let queryHandler ← genQueryHandler paramSchemas urlId

  let headerId := mkIdent `header
  let headerHandler ← genHeaderHandler paramSchemas headerId
  let cookieHandler ← genCookieHandler paramSchemas headerId

  let (reqDocs, reqCtHeader, reqBodyParam, reqBodyType, reqBodyVal) ← do
    match op.requestBody with
    | none =>
      pure (none, none, none, ← `(String), ← `(""))
    | some rb =>
      let (docs, ct, param, type, val) ← genRequestBody rb
      let ctHeader ← `(doElem|
        let $headerId := ($headerId).add (Http.HeaderName.standard .CONTENT_TYPE) $(Syntax.mkStrLit ct)
      )
      pure (some docs, some ctHeader, some param, type, val)
  
  let docstring := genDocstring item op paramSchemas reqDocs

  let mainCmd ← `(
    $(Lean.mkDocComment docstring):docComment
    def $id:ident $[ $(paramBinders ++ reqBodyParam.toArray):bracketedBinder ]*
      : Http.Request $reqBodyType
      :=
      Id.run do
      -- put parameters into the url
      let $urlId := $serverUrlId
      $pathHandler:doElem
      $queryHandler:doElem
      -- put parameters into the header
      let $headerId := Http.Headers.empty
      $[$headerHandler:doElem]*
      $[$cookieHandler:doElem]*
      -- if there is a content-type header, insert that
      $[$(reqCtHeader |>.toArray):doElem]*
      -- construct request
      return Http.Request.mk
        (method := $(quote method))
        (url := $urlId)
        (version := .HTTP_1_1)
        (headers := $headerId)
        (body := $reqBodyVal)
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
  
  if api.security.isSome then
    throwError "API security schemes not yet supported"

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
