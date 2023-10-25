import LeanOpenAPI

open LeanOpenAPI.Meta

namespace GitHub
genOpenAPI! do
  let me : System.FilePath := file%
  let file := me.parent.get! / "examples/api.github.com.json"
  return (← IO.FS.readFile file)
end GitHub
