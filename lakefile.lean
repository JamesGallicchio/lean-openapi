import Lake
open Lake DSL

package «lean-openapi» {
  -- add package configuration options here
}

@[default_target]
lean_lib LeanOpenAPI {
  -- add library configuration options here
}

@[default_target]
lean_exe «examples» {
  root := `Examples
} 

require std from git "https://github.com/leanprover/std4" @ "main"
require Http from git "https://github.com/JamesGallicchio/http" @ "main"
