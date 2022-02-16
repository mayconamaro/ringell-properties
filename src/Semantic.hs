module Semantic where

-- Translating the AST into 1st Intermediate Representation 
-- No invalid names for function decl+def, peano notation
-- brackets info removed, no duplicate names
data ExpS 
    = VarS String
    | ZeroS  
    | SucS ExpS
    | AbsS String TypeS ExpS
    | AppS ExpS ExpS
    | MatchS ExpS ExpS (String, ExpS)
    deriving (Eq, Show)

data TypeS 
    = NatS
    | ArrowS TypeS TypeS
    deriving (Eq, Show)

data FunS 
    = FunS String TypeS ExpS
    deriving (Eq, Show)

data ProgS 
    = DeclS FunS ProgS 
    | MainS TypeS ExpS      
    deriving (Eq, Show)

-- Typechecking

type Context = [(String, TypeS)]

lookupV :: Context -> String -> TypeS
lookupV c s = lookupV' c s

lookupV' :: Context -> String -> TypeS
lookupV' []             s = error $ "Variable " ++ s ++ " not in scope"
lookupV' ((v, t) : env) s
  | s == v    = t
  | otherwise = lookupV' env s 

-- -- Typecheck
infertypeE :: ExpS -> Context -> TypeS
infertypeE (VarS v)              env = lookupV env v            
infertypeE (ZeroS)                 env = NatS
infertypeE (SucS e)                env 
 | infertypeE e env == NatS = NatS
 | otherwise = error "type error: numbers must be nat" 
infertypeE (AbsS v t e)            env = ArrowS t (infertypeE e ((v, t) : env)) 
infertypeE (AppS e1 e2)            env =
    case infertypeE e1 env of
        ArrowS t1 t2 -> if infertypeE e2 env == t1 
                          then t2
                          else error "type error: function argument does not match the given value"
        _            -> error "type error: numbers cannot be functions"
infertypeE (MatchS e1 e2 (v, e3))  env =
    case infertypeE e1 env of
        NatS -> case infertypeE e2 env of
                  t1 -> if infertypeE e3 ((v , NatS) : env) == t1 
                          then t1
                          else error "type error: pattern match cases must have the same type"
        _    -> error "type error: matching can only occurs with numbers"  

data Status = Ok | Fail String
   deriving (Eq, Show)

typecheck :: ProgS -> Context -> Status
typecheck (MainS t e) env
  | t' == t        = Ok
  | otherwise      = Fail "main type does not match"
    where t' = infertypeE e env
typecheck (DeclS (FunS s t e) p) env
  | t' == t        = typecheck p ((s, t) : env)
  | otherwise      = Fail $ "function type for " ++ s ++ " does not match" 
    where t' = infertypeE e ((s, t) : env)

{- Alternate Pretty Printing for ExpS 
showExpS :: ExpS -> Int -> String
showExpS (VarS s)               n = "Var " ++ s ++ "\n"
showExpS (ZeroS)                n = "Zero\n"
showExpS (SucS e)               n = "Suc\n" ++ replicate (2*n + 2) ' ' ++ showExpS e (n+1)
showExpS (AbsS v t e)           n = "Abs " ++ v ++ " " ++ show t ++ "\n" 
                                      ++ replicate (2*n + 2) ' ' ++ showExpS e (n+1)
showExpS (AppS e1 e2)           n = "App\n" 
                                      ++ replicate (2*n + 2) ' ' ++ showExpS e1 (n+1)
                                      ++ replicate (2*n + 2) ' ' ++ showExpS e2 (n+1)
showExpS (MatchS e1 e2 (v, e3)) n = "Match\n" 
                                      ++ replicate (2*n + 2) ' ' ++ showExpS e1 (n+1) 
                                      ++ replicate (2*n + 2) ' ' ++ showExpS e2 (n+1)
                                      ++ replicate (2*n + 2) ' ' ++ "(" ++ v ++ ", " ++ showExpS e3 (n+1) 
                                      ++ replicate (2*n + 2) ' ' ++ ")\n"

instance Show ExpS where
  show e = showExpS e 0
  -}