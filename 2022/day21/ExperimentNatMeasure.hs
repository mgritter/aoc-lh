module ExperimentNatMeasure where

{-@ measure numVars :: ExprTree -> Nat @-}

{-@ data ExprTree where
  ConstantE :: Int -> {e:ExprTree | numVars e = 0 }  |
  DivE :: left:ExprTree -> {right:ExprTree | numVars right = 0} -> {e:ExprTree | numVars e = numVars left} |
  VarE :: name:String -> {e:ExprTree | numVars e = 1}
@-}
data ExprTree =
  ConstantE Int |
  DivE ExprTree ExprTree |
  VarE String

{-@ simplify :: e:ExprTree -> {se:ExprTree | numVars se <= numVars e } @-}
simplify :: ExprTree -> ExprTree
simplify (DivE a b) = ConstantE 0
simplify (VarE s) = ConstantE 0
simplify (ConstantE e) = ConstantE e

