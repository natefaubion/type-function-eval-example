module Types where

import Prelude

import Data.Foldable (elem, intercalate)
import Data.List (List)
import Data.List as List
import Data.Maybe (Maybe(..))
import Data.Tuple (Tuple(..))
import Partial.Unsafe (unsafeCrashWith)

type Name = String

data Ty
  = Ty
  | TySko Name
  | TyVar Name
  | TyApp Ty Ty
  | TyLam Name Ty
  | TyCase Ty (List (Tuple Pat Ty))
  | TyForall Name Knd Ty
  | TyArrow Ty Ty
  | TyConstr (Constr Ty) Ty

type Knd = Ty

data Constr a =
  ConstrEval a

data Pat
  = PatApp Pat Pat
  | PatVar Name
  | PatCtr Name

data Env = Env Name SemTy Env | Nil

data Closure = Closure Env Ty

data SemTy
  = SemTy
  | SemSko Name
  | SemVar Name
  | SemApp SemTy SemTy
  | SemLam Name Closure
  | SemForall Name SemTy Closure
  | SemArrow SemTy SemTy
  | SemConstr (Constr SemTy) SemTy
  | SemCase SemTy (List (Tuple Pat Closure))

lookup :: Name -> Env -> Maybe SemTy
lookup m = go
  where
  go = case _ of
    Env n c _ | m == n ->
      Just c
    Env _ _ x ->
      go x
    Nil ->
      Nothing

data Mode = Strict | Lax

eval :: Env -> Ty -> SemTy
eval env ty = case ty of
  Ty ->
    SemTy
  TySko n ->
    SemSko n
  TyVar n ->
    case lookup n env of
      Just sem ->
        sem
      _ ->
        SemVar n
  TyApp l r ->
    evalApp env l r
  TyCase hd ps ->
    evalCase env hd ps
  TyLam v a ->
    SemLam v (Closure env a)
  TyForall v kd a ->
    SemForall v (eval env kd) (Closure env a)
  TyArrow a b ->
    SemArrow (eval env a) (eval env b)
  TyConstr a b ->
    SemConstr (evalConstr env a) (eval env b)

evalApp :: Env -> Ty -> Ty -> SemTy
evalApp env l r = case eval env l of
  SemLam v (Closure env' a) ->
    eval (Env v (eval env r) env') a
  x ->
    SemApp x (eval env r)

evalConstr :: Env -> Constr Ty -> Constr SemTy
evalConstr env = case _ of
  ConstrEval ty -> ConstrEval (eval env ty)

evalCase :: Env -> Ty -> List (Tuple Pat Ty) -> SemTy
evalCase env hd pats = go (eval env hd) pats
  where
  go ty = case _ of
    List.Cons (Tuple pat bod) ps ->
      case matchCase pat ty of
        Apart ->
          SemCase ty $ (map (Closure env)) <$> pats
        Fail ->
          go ty ps
        Match k ->
          eval (k env) bod
    List.Nil ->
      unsafeCrashWith "Fail case"

data Match = Fail | Apart | Match (Env -> Env)

instance Semigroup Match where
  append = case _, _ of
    Apart, _ -> Apart
    _, Apart -> Apart
    Fail, _ -> Fail
    _, Fail -> Fail
    Match a, Match b -> Match (b <<< a)

matchCase :: Pat -> SemTy -> Match
matchCase = case _, _ of
  PatVar v, sem ->
    Match (Env v sem)
  PatCtr v, SemVar v'
    | v == v' ->
        Match identity
    | otherwise ->
        Fail
  PatApp p1 p2, SemApp a b -> do
    matchCase p1 a <> matchCase p2 b
  _, SemSko _ ->
    Apart
  _, _ ->
    Fail

fresh :: List Name -> Name -> Tuple Name (List Name)
fresh names v = go 1
  where
  go n = do
    let
      name
        | n == 1 = v
        | otherwise = v <> show n
    if name `elem` names then
      go (n + 1)
    else
      Tuple name (List.Cons name names)

quote :: Mode -> List Name -> SemTy -> Ty
quote mode names = case _ of
  SemTy ->
    Ty
  SemSko n ->
    TySko n
  SemVar n ->
    TyVar n
  SemApp l r ->
    TyApp (quote mode names l) (quote mode names r)
  SemForall v kd (Closure env a) -> do
    let Tuple v' names' = fresh names v
    TyForall v' (quote mode names kd) (quote mode names' (eval (Env v' (SemSko v') env) a))
  SemArrow a b ->
    TyArrow (quote mode names a) (quote mode names b)
  SemConstr a b ->
    TyConstr (quoteConstr mode names a) (quote mode names b)
  SemLam v c -> do
    let ty = quoteLam names v c
    case mode of
      Strict ->
        unsafeCrashWith $ "Stuck type lambda: " <> printTy ty
      Lax ->
        ty
  SemCase a pats -> do
    let ty = quoteCase names a pats
    case mode of
      Strict ->
        unsafeCrashWith $ "Stuck type case: " <> printTy ty
      Lax ->
        ty

quoteConstr :: Mode -> List Name -> Constr SemTy -> Constr Ty
quoteConstr _ names = case _ of
  ConstrEval sem ->
    ConstrEval (quote Lax names sem)

quoteLam :: List Name -> Name -> Closure -> Ty
quoteLam names v (Closure env sem) = do
  let Tuple v' names' = fresh names v
  TyLam v' (quote Lax names' (eval (Env v' (SemSko v') env) sem))

quoteCase :: List Name -> SemTy -> List (Tuple Pat Closure) -> Ty
quoteCase names a pats = TyCase (quote Lax names a) (quotePat' <$> pats)
  where
  quotePat' (Tuple p (Closure env sem)) = do
    let Tuple p' (Tuple k names') = quotePat names p
    Tuple p' (quote Lax names' (eval (k env) sem))

quotePat ::  List Name -> Pat -> Tuple Pat (Tuple (Env -> Env) (List Name))
quotePat = go identity
  where
  go k names = case _ of
    PatCtr v ->
      Tuple (PatCtr v) (Tuple k names)
    PatVar v -> do
      let Tuple v' names' = fresh names v
      Tuple (PatVar v') (Tuple (Env v (SemVar v') <<< k) names')
    PatApp a b -> do
      let Tuple a' (Tuple k' names') = go k names a
      let Tuple b' (Tuple k'' names'') = go k' names' b
      Tuple (PatApp a' b') (Tuple k'' names'')

printTy :: Ty -> String
printTy = case _ of
  TyApp a@(TyApp _ _) b ->
    printTy a <> " " <> printTy1 b
  TyApp a b ->
    printTy1 a <> " " <> printTy1 b
  TyLam v a ->
    "\\" <> v <> " -> " <> printTy a
  TyCase ty ps ->
    "case " <> printTy ty <> " of { " <> intercalate "; " (printPat' <$> ps) <> " }"
    where
    printPat' (Tuple p t) = printPat p <> " -> " <> printTy t
  TyForall v kd ty ->
    "forall (" <> v <> " :: " <> printTy kd <> "). " <> printTy ty
  TyArrow a b ->
    printTy1 a <> " -> " <> printTy b
  TyConstr a b ->
    printConstr a <> " => " <> printTy b
  a ->
    printTy1 a

printTy1 :: Ty -> String
printTy1 = case _ of
  Ty ->
    "*"
  TySko n ->
    n
  TyVar v ->
    v
  a ->
    "(" <> printTy a <> ")"

printConstr :: Constr Ty -> String
printConstr = case _ of
  ConstrEval ty ->
    "Eval " <> printTy1 ty

printPat :: Pat -> String
printPat = case _ of
  PatApp a@(PatApp _ _) b ->
    printPat a <> " " <> printPat1 b
  PatApp a b ->
    printPat1 a <> " " <> printPat1 b
  p ->
    printPat1 p

printPat1 :: Pat -> String
printPat1 = case _ of
  PatCtr n ->
    n
  PatVar v ->
    v
  p ->
    "(" <> printPat p <> ")"
