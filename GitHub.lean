import LeanOpenAPI

open LeanOpenAPI.Meta

namespace GitHub
genOpenAPI! "examples/api.github.com.json"
end GitHub

example :
  (GitHub.«actions/add-custom-labels-to-self-hosted-runner-for-org»
    (org := "myorg")
    (runner_id := 12345)
    (body := .obj <| Lean.RBNode.leaf.ins compare "labels" (.arr #["bug"]))
  |>.toRequestString)
=
"POST https://api.github.com/orgs/myorg/actions/runners/12345/labels HTTP/1.1\x0d
content-type: application/json\x0d
\x0d
{\"labels\": [\"bug\"]}"
:= by native_decide
