# cop-printf

Implementation of `sprintf` for Coq

## Format specifiers

The syntax of format specifiers is given by this regexp:

```
%(-|+| |#|0)^* (\d+) (s|b|o|d|x|X|c)
```

which corresponds to this structure:

```
%[flags]       [width]  specifier
```

## Flags

| Flags | Description                                                                 |
|-------|-----------------------------------------------------------------------------|
| `-`   | Left justify                                                                |
| `+`   | Precede with a plus sign (only applies to `nat`)                            |
| *(space)* | Space if no sign precedes                                               |
| `#`   | With specifier `o`, `x`, `X`, precede with `0`, `0x`, `0X` respectively for values different than zero |
| `0`   | Pad with 0's instead of space                                               |

## Specifiers

| Specifier | Description            |
|-----------|------------------------|
| `s`       | string                 |
| `b`       | binary                 |
| `o`       | octal                  |
| `d`       | decimal                |
| `x`       | hexadecimal lower case |
| `X`       | hexadecimal upper case |
| `c`       | character              |


## Example

```Coq
Require Import Coq.Strings.String.
Require Import Printf.Printf.

Eval compute in (sprintf "%b" 1234).
```

## Resources

Reference : http://www.cplusplus.com/reference/cstdio/printf
