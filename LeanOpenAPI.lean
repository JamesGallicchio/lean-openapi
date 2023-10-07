import LeanOpenAPI.JsonSchema
import LeanOpenAPI.OpenAPI
import LeanOpenAPI.Std
import LeanOpenAPI.Meta

namespace LeanOpenAPI
open Meta

namespace GitHub
genOpenAPI! "examples/api.github.com.json"
end GitHub

#eval IO.println <| Http.Request.toRequestString <|
  GitHub.«actions/add-custom-labels-to-self-hosted-runner-for-org»
    (org := "myorg")
    (runner_id := 12345)
    (body := .obj <| Lean.RBNode.leaf.ins compare "labels" (.arr #["bug"]))

-- POST https://api.github.com/orgs/myorg/actions/runners/12345/labels? HTTP/1.1
-- content-type: application/json
-- 
-- {"labels": ["bug"]}
