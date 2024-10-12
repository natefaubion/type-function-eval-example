module Main where

import Prelude

import Data.List as List
import Data.Tuple (Tuple(..))
import Effect (Effect)
import Effect.Console (log)
import Types (Constr(..), Env(..), Mode(..), Pat(..), Ty(..), eval, printTy, quote)

infixl 2 TyApp as :$
infixr 0 TyLam as :\->
infixr 1 TyArrow as :->
infixr 1 TyConstr as :=>

case_ :: Ty -> Array (Tuple Pat Ty) -> Ty
case_ a = TyCase a <<< List.fromFoldable

expand :: Mode -> Ty -> Ty
expand m = quote m List.Nil <<< eval Nil

main :: Effect Unit
main = do
  let
    print m t = do
      log $ printTy t
      log $ printTy $ expand m t
      log ""

  print Lax do
    ("f" :\-> "g" :\-> TyVar "f" :$ TyVar "Int") :$ TyVar "Foo"

  print Strict do
    case_ (TyVar "Foo" :$ TyVar "Bar")
      [ Tuple (PatApp (PatCtr "Foo") (PatVar "b"))
          (TyVar "b")
      ]

  print Strict do
    TyForall "f" Ty $ TyVar "f" :-> TyVar "f"

  print Strict do
    TyForall "f" Ty $ case_ (TyVar "Foo" :$ TyVar "f")
      [ Tuple (PatApp (PatCtr "Foo") (PatVar "x")) (TyVar "x")
      ]


  print Strict do
    TyForall "f" Ty $ TyForall "r" Ty $ TyConstr
      (ConstrEval (case_ (TyVar "f")
        [ Tuple (PatCtr "Foo") (TyVar "Int")
        ])
        (TyVar "r"))
      (TyVar "r")

  print Strict do
    TyForall "f" Ty $ case_ (TyVar "f")
      [ Tuple (PatCtr "Foo") (TyVar "Int")
      ]
