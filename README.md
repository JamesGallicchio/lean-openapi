# OpenAPI definitions and code generation for Lean 

**Input:** OpenAPI spec  
**Output:** Lean bindings for each endpoint

The generated bindings are functions that construct HTTP requests
as defined by the [`http` package](https://github.com/JamesGallicchio/).
These requests can then be sent over the wire with
e.g. [`Socket.lean`](https://github.com/hargoniX/socket.lean).

### Usage

Add the following to your `lakefile.lean`:
```
require «lean-openapi» from git "http://github.com/JamesGallicchio/lean-openapi" @ "main"
```

Then, in a file:
```
import LeanOpenAPI
...

-- The declarations are generated in the namespace where the macro is invoked
namespace MyLib
-- The `genOpenAPI!` macro is scoped, so we need to open this namespace:
open LeanOpenAPI.Meta
-- now we can generate the API. the argument must have type `IO String`
-- and should be the json string for the OpenAPI spec
genOpenAPI! (IO.FS.readFile "examples/api.github.com.json")
```

### Limitations

A list of features of OpenAPI not (yet!) supported. PRs welcome :-)

- Some restrictions on parameter objects are not enforced.
- Parameter object's `allowEmptyValue` field is always ignored.
- Meta-schemas are mostly unsupported;
  the current behavior puts the meta-schema in the docstring,
  and provides an over-approximation of the argument type,
  expecting users to adhere to the docstring's meta-schema.
- Security requirements are not supported
- Examples are recognized but unused
