module ExperimentCase where
{-@ LIQUID "--max-case-expand=10" @-}

{-@ measure depth :: ExprTree -> Nat @-}
{-@ data ExprTree where
  ConstantE :: Int -> {e:ExprTree | depth e == 0}  |
  VariableE :: constantTerm:Int -> {e:ExprTree | depth e == 0}  |
  AddE :: left:ExprTree -> right:ExprTree -> {e:ExprTree | depth e > depth left && depth e > depth right} |
  ErrorV :: message:String -> {e:ExprTree | depth e == 0}
@-}

data ExprTree =
  ConstantE Int |
  AddE ExprTree ExprTree |
  VariableE Int |
  ErrorV String  
  deriving (Show)

isSimple :: ExprTree -> Bool
isSimple (ConstantE _ ) = True
isSimple (VariableE _ ) = True
isSimple (ErrorV _ ) = True
isSimple _ = False
{-@ measure isSimple @-}

{-@ simplify :: e:ExprTree -> {se:ExprTree | isSimple se } / [ depth e ] @-}
simplify :: ExprTree -> ExprTree
simplify (ConstantE v) = ConstantE v
simplify (VariableE c) = VariableE c
simplify (ErrorV v) = ErrorV v
simplify (AddE a b) =
  case (simplify a, simplify b) of
    (ErrorV e, _) -> ErrorV e
    (_, ErrorV e) -> ErrorV e
    (ConstantE va, ConstantE vb) -> ConstantE (va + vb)
    (VariableE c, ConstantE vb) -> VariableE (c + vb)
    (ConstantE va, VariableE c) -> VariableE (va + c)
    (VariableE _, VariableE _) -> ErrorV "too many variables"
    _ -> ErrorV "unhandled case"
    
