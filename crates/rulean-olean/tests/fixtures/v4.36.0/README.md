# Fixture: Init.Control.Do of Lean v4.36.0

The three files in `Init/Control` are the `.olean`, `.olean.server` and `.olean.private` files of the module `Init.Control.Do`. They come without change from the release v4.36.0 of Lean 4, in the directory `lib/lean` of the toolchain. Lean 4 is licensed under Apache-2.0, see https://github.com/leanprover/lean4/blob/v4.36.0/LICENSE.

| File | SHA-256 |
|---|---|
| Do.olean | 7eed1af4c6a7cbaa27045ac932c280d5c9423792bd880b5dbe70a373047a2310 |
| Do.olean.server | 1c60837902f95fb94eeb3b02d09b09708de7f0665b4f814738ddbdd46e51260d |
| Do.olean.private | ba533120c9961c631e7c7ed922d6f3e71d41d88f3184266cde154439158f1398 |

The test `tests/fixture.rs` decodes the module, and then decodes damaged copies of the files. A damaged copy must give an error or a result, and never a panic.
