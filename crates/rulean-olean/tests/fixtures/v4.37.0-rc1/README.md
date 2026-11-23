# Fixture: Init.Control.Do of Lean v4.37.0-rc1

The three files in `Init/Control` are the `.olean`, `.olean.server` and `.olean.private` files of the module `Init.Control.Do`. They come without change from the release v4.37.0-rc1 of Lean 4, in the directory `lib/lean` of the toolchain for `darwin_aarch64`. Lean 4 is licensed under Apache-2.0, see https://github.com/leanprover/lean4/blob/v4.37.0-rc1/LICENSE.

The files have the olean format version 4. The header is followed by `data_size`, the data, an empty closure section and an empty library table. The module data has the constant trie of spec 07.3.5.

| File | SHA-256 |
|---|---|
| Do.olean | 3229cbec7c94a911f5669ca2be946be9aa22bccb08da071e2a231cf4ab129680 |
| Do.olean.server | 81d8f94e047f877b1310f07c2ab007b4092867dc81d4dc8adb7d418f053fdd43 |
| Do.olean.private | 58c9fb52d17a6b42f7de2d0946adc7741b7aa43772b751a00dd63af324e8f6c4 |

The test `tests/fixture.rs` decodes the module, and then decodes damaged copies of the files. A damaged copy must give an error or a result, and never a panic.
