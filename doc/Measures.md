# Liquid Haskell Built-in measures

I don't know where these are documented; you might just have to read
the include files in [liquidhaskell/include](https://github.com/ucsd-progsys/liquidhaskell/tree/develop/include) like I did.

## Lists

`len` -- length of a list

## Tuples

`fst`, `snd` -- extract the appropriate element of a tuple

## Maybe

`isJust` -- true when the argument is a Just

`fromJust` -- extract the value from a Just

## Either

`isLeft` -- true when the argument is a Left

## Strings

`stringlen` -- length of a string, doesn't seem very useful because it is only used in the `fromString` specification

The `String.hs` module encapsulates SMT strings, but it looks like these
only work with `Data.ByteString`, not normal Haskell strings.

`stringEmp` -- empty string

`stringLen` -- length of a string

`subString` -- take a substring

`concatString` -- string concatenation

`fromString` -- Data.String to SMTString

`takeString` -- take first N bytes

`dropString` -- drop first N bytes

## Sets

I'm not clear why `member` can be used, it seems to alias to `Set_mem`

`Set_cup` -- union

`Set_cap` -- intersection

`Set_dif` -- set difference

`Set_sng` -- singleton set creator

`Set_emp` -- true if set is empty

`Set_empty` -- the empty set

`Set_mem` -- membership test

`Set_sub` -- subset set


