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

## Can't inline functions that deconstruct pairs?

Error:

```
/home/mark/aoc-lh/2022/day4/Main.hs:16:1: error:
    • Illegal type specification for `Main.contains`
    Main.contains :: x##1:(GHC.Types.Int, GHC.Types.Int) -> x##2:(GHC.Types.Int, GHC.Types.Int) -> {VV : GHC.Types.Bool | VV <=> lqdc##$select##GHC.Tuple.(,)##1 x##1 <= lqdc##$select##GHC.Tuple.(,)##1 x##2
                                                                                                                                 && lqdc##$select##GHC.Tuple.(,)##2 x##2 <= lqdc##$select##GHC.Tuple.(,)##2 x##1}
    Sort Error in Refinement: {VV : bool | (VV <=> lqdc##$select##GHC.Tuple.(,)##1 x##1 <= lqdc##$select##GHC.Tuple.(,)##1 x##2
                                                   && lqdc##$select##GHC.Tuple.(,)##2 x##2 <= lqdc##$select##GHC.Tuple.(,)##2 x##1)}
    Unbound symbol lqdc##$select##GHC.Tuple.(,)##1 --- perhaps you meant: GHC.Tuple.(,) ?
    • 
   |
16 | contains (s1,e1) (s2,e2) = s1 <= s2 && e2 <= e1
   | ^^^^^^^^
```

*This means*: you tried to inline a function that deconstructs a pair in its definition?  (Unconfirmed.)

Solution: switch to measures that extract the first and second elements


## Dependent pair has too few colons

Error:

```
12 | list4ToRanges (a:b:c:d:[]) = ((a,b),(c,d))
   | ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

/home/mark/aoc-lh/2022/day4/Main.hs:10:22: error:
    • Illegal type specification for `Main.list4ToRanges`
    Main.list4ToRanges :: x:{x : [GHC.Types.Int] | len x == 4} -> ((GHC.Types.Int, {y : GHC.Types.Int | x <= y}), (GHC.Types.Int, {y : GHC.Types.Int | x <= y}))
    Sort Error in Refinement: {y : int | x <= y}
    The sort [int] is not numeric
  because
The sort [int] is not numeric
```

Possibly a clearer example:
```
   • Illegal type specification for `Example.buildRange`
    Example.buildRange :: lq_tmp$db##0:GHC.Types.Int -> lq_tmp$db##1:GHC.Types.Int -> (GHC.Maybe.Maybe (GHC.Types.Int, {y : GHC.Types.Int | x <= y}))
    Sort Error in Refinement: {y : int | x <= y}
    Unbound symbol x --- perhaps you meant: y ?
    • 
  |
7 | {-@ buildRange :: Int -> Int -> Maybe ValidRange @-}
  |                   ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
```


*This means*: you tried to inline a function that deconstructs a pair in its definition?  (Unconfirmed.)

Broken
```:
{-@ type ValidRange = (x:Int,{y:Int | x <= y}) @-}
```

OK:
```
{-@ type ValidRange = (x::Int,{y:Int | x <= y}) @-}
```

Solution: use two colons, I guess.

## Tuple isn't numeric

Problem: I applied an invariant to (Int,Int) but it seems to be being applied to all pairs?!?  (Uncofirmed.)

```
**** LIQUID: ERROR :1:1-1:1: Error
  elaborate solver elabBE 562 "VV##F##164" {VV##F##164 : bool | [(VV##F##164 <=> && [((Main.start lq_rnm$xInv##200) <= (Main.end lq_rnm$xInv##200))])]} failed on:
      VV##F##164 <=> Main.start lq_rnm$xInv##200 <= Main.end lq_rnm$xInv##200
  with error
      The sort (Tuple int int) is not numeric
  because
Cannot unify int with (Tuple int int) in expression: Main.start lq_rnm$xInv##200 
  in environment
      Main.end := func(0 , [(Tuple int int); int])

      Main.start := func(0 , [(Tuple int int); int])

      VV##F##164 := bool

      lq_rnm$xInv##200 := (Tuple (Tuple int int) (Tuple int int)) 
```

Solution: use a data type for the pair for which you want to specify the invariant, not a tuple

