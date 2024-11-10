# AFactor
A programming language for Wasm GC while allowing stack storage and references for performance and WASI-P1 compatability.

## Features
NOT YET COMPLETED AND MIGHT NEVER BE
* Parser
* IR:
  * Hindley–Milner like type resolution (currently tested with number types)
  * No function calls, blocks and a bunch of other stuff
* Wasm encoding:
  * Types (Heap, local & stack), function definitions, imports, names
  * No code section and correct locals
