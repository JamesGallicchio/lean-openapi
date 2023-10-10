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
require LeanOpenAPI from git "https://github.com/JamesGallicchio/LeanOpenAPI" @ "main"
```

Then, in a file:
```
import LeanOpenAPI
...

-- The declarations are generated in the namespace where the macro is invoked
namespace MyLib
-- The `genOpenAPI!` macro is scoped, so we need to open this namespace:
open LeanOpenAPI.Meta
-- now we can generate the API. the argument is a path to a file.
-- (I need to make this more robust to Lake package stuff...)
genOpenAPI! "examples/api.github.com.json"
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
