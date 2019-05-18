# cop-printf

Implementation of sprintf for Coq

## format specifiers

Regexp

%(-|+| |#|0)^* (\d+) (s|b|o|d|x|X|c)

Structure

%[flags]       [width]  specifier

## flags

| flags | description                                                                 |
|-------|-----------------------------------------------------------------------------|
| '-'   | left justify                                                                |
| '+'   | precede with a plus sign (only applys to nat)                               |
| ' '   | space if no sign precedes                                                   |
| '#'   | with specfier o x X precede with 0 0x 0X for for values different than zero |


'0' pad with 0's instead of space

## specifier

| specifier | description            |
|-----------|------------------------|
| 's'       | string                 |
| 'b'       | binary                 |
| 'o'       | octal                  |
| 'd'       | decimal                |
| 'x'       | hexidecimal lower case |
| 'X'       | hexidecimal upper case |
| 'c'       | character              |


## example

```Coq
Require Import Coq.Strings.String.
Require Import Printf.Printf.

Eval compute in (sprintf "%b" 1234).
```

## resources

reference : http://www.cplusplus.com/reference/cstdio/printf
