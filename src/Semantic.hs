module Semantic where

data ExpS 
    = VarS String
    | ZeroS  
    | SucS ExpS
    | AbsS String TypeS ExpS
    | AppS ExpS ExpS
    | MatchS ExpS ExpS (String, ExpS)
    deriving (Show)

data TypeS 
    = NatS
    | ArrowS TypeS TypeS
    deriving (Eq, Show)

data FunS 
    = FunS String TypeS ExpS
    deriving (Show)

data ProgS 
    = DeclS FunS ProgS 
    | MainS TypeS ExpS
    deriving (Show)

-- Typechecking

type Context = [(String, TypeS)]

lookupV :: Context -> String -> TypeS
lookupV c s = lookupV' c s

lookupV' :: Context -> String -> TypeS
lookupV' ((v, t) : env) s
  | s == v    = t
  | otherwise = lookupV' env s 

partialIf :: Bool -> a -> a
partialIf True = id

-- -- Typecheck
infertypeE :: ExpS -> Context -> TypeS
infertypeE (VarS v)              env = lookupV env v            
infertypeE (ZeroS)                 env = NatS
infertypeE (SucS e)                env 
 | infertypeE e env == NatS = NatS
infertypeE (AbsS v t e)            env = ArrowS t (infertypeE e ((v, t) : env)) 
infertypeE (AppS e1 e2)            env =
    case infertypeE e1 env of
        ArrowS t1 t2 -> partialIf (infertypeE e2 env == t1) t2
infertypeE (MatchS e1 e2 (v, e3))  env =
    case infertypeE e1 env of
        NatS -> case infertypeE e2 env of
                  t1 -> partialIf (infertypeE e3 ((v , NatS) : env) == t1) t1

data Status = Ok | Fail String
   deriving (Eq)

typecheck :: ProgS -> Context -> Status
typecheck (MainS t e) env
  | t' == t        = Ok
    where t' = infertypeE e env
typecheck (DeclS (FunS s t e) p) env
  | t' == t        = typecheck p ((s, t) : env)
    where t' = infertypeE e ((s, t) : env)
