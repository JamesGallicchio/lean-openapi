import LeanOpenAPI

open LeanOpenAPI Meta

namespace Examples.GitHub
genOpenAPI! "examples/api.github.com.json"
end GitHub

#check GitHub.«actions/get-actions-cache-list»
