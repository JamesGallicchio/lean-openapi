# OpenAPI definitions and code generation for Lean 

Goal: given an OpenAPI spec, generate Lean bindings for each endpoint.

Each endpoint generates HTTP requests as defined by the
[`http` package](https://github.com/JamesGallicchio/).
This implements a subset of OpenAPI. See `Limitations`.

### Limitations

A list of features of OpenAPI not (yet!) supported. PRs welcome :-)

- Some restrictions on parameter objects are not enforced.
- Parameter object's `allowEmptyValue` field is always ignored.
