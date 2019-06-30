# cop-printf

Implementation of `sprintf` and `sscanf` for Coq

## Format specifiers

The syntax of format specifiers is given by this regular expression:

```
%(-|+| |#|0)^* (\d+)   (N?)   (s|c|b|o|d|x|X|Zd)
```

which corresponds to this structure:

```
%[flags]       [width] [type] specifier
```

## Flags

| Flags | Description                                                                 |
|-------|-----------------------------------------------------------------------------|
| `-`   | Left justify                                                                |
| `+`   | Precede nonnegative numbers with a plus sign (only for `nat`, `N`, `Z`)     |
| *(space)* | Space if no sign precedes                                               |
| `#`   | With specifier `o`, `x`, `X`, precede with `0`, `0x`, `0X` respectively for values different than zero |
| `0`   | Pad with 0's instead of space                                               |

These flags are ignored by `sscanf`.

## Width

The width modifier `(\d+)` gives:

- for `sprintf`, the minimum number of characters to be printed (this enables padding);
- for `sscanf`, the maximum number of characters to be read for this specifier.

## Type

The type modifier `(N?)` affects the specifiers `b`, `o`, `d`, `x`, `X` to use the
type `N` instead of the default `nat`.

## Specifiers

| Specifier | Description            | Types      |
|-----------|------------------------|------------|
| `s`       | string                 | `string`   |
| `c`       | character              | `ascii`    |
| `b`       | binary                 | `nat`, `N` |
| `o`       | octal                  | `nat`, `N` |
| `d`       | decimal                | `nat`, `N` |
| `x`       | hexadecimal lower case | `nat`, `N` |
| `X`       | hexadecimal upper case | `nat`, `N` |
| `Zd`      | signed decimal         | `Z`        |

The special sequence `%%` encodes a literal `%`.

## Example

```Coq
Require Import Coq.Strings.String.
Require Import Printf.Printf.

Eval compute in (sprintf "%b" 1234).
```

## Resources

Reference : http://www.cplusplus.com/reference/cstdio/printf
