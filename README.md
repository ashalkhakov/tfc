# Continuation-Passing ATS

This library provides very lightweight user-space cooperative threads in ATS.
I
The implementation is inspired by "Continuation-Passing C".

# Features

* since all continuations are guaranteed to be "one-shot" by the type system,
  memory management is greatly simplified (also correctness is improved, one
  can't just discard a continuation, that's a type error!)
* extremely simple and bare-bones

# Examples

Please see the [tests](tests) directory.

# License

[BSD v3](LICENSE)

# Authors

Artyom Shalkhakov, artyom DOT shalkhakov AT gmail DOT com
