# Error messages from Liquid Haskell

## Not expanding cases

```
WARNING: (2022/day2/Main.hs:(141,1)-(146,34)) Not expanding DEFAULT with 2 cases at depth 3
Enable expansion with --max-case-expand=4
```

*This means*:  We're not gonna consider all the cases of your pattern match,
which might lead to either (a) a type error if you give a bogus value for
the default case that should never happen, or (b) a type error like this
if you error out:

```
/home/mark/aoc-lh/2022/day2/Main.hs:146:19: error:
    Liquid Type Mismatch
    .
    The inferred type
      VV : {v : [GHC.Types.Char] | v ~~ "Inconceivable!"
                                   && len v == strLen "Inconceivable!"
                                   && len v >= 0
                                   && v == "Inconceivable!"}
    .
    is not a subtype of the required type
      VV : {VV : [GHC.Types.Char] | false}
    .
    |
146 | ourMove _ _ = die "Inconceivable!"
    |
```

Solution: `{-@ LIQUID "--max-case-expand=4" @-}` at the top of the file

## Five is less than four

Error:

```
/home/mark/aoc-lh/2022/day2/Main.hs:47:1: error:
    Liquid Type Mismatch
    .
    The inferred type
      VV : {v : GHC.Prim.Addr# | v == "2022/day2/Main.hs:(47,1)-(52,24)|function parseMove"}
    .
    is not a subtype of the required type
      VV : {VV : GHC.Prim.Addr# | 5 < 4}
    .
   |
47 | parseMove "A" = Rock
   | ^^^^^^^^
```

*This means*:  You didn't include a default case, or cover all the
possibilities.

Solution: add a default case (but see above, it might be redundant.)
