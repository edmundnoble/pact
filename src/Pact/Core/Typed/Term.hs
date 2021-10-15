module Pact.Core.Typed.Term where

import Pact.Core.Type

-- | Untyped pact core terms
data Term name tyname
  = Var name
  | Lam name (Type tyname) (Term name tyname)
  | If (Term name tyname) (Term name tyname) (Term name tyname)
  | App (Term name tyname) (Term name tyname)
  | TyApp (Term name tyname) (Type name)
