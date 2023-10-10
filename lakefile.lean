import Lake
open Lake DSL

package «lean-openapi»

@[default_target]
lean_lib LeanOpenAPI {
  precompileModules := true
}

lean_lib GitHub

require std from git "https://github.com/leanprover/std4" @ "main"
require Http from git "https://github.com/JamesGallicchio/http" @ "main"
