module Pact.Core.Type where

data PrimType =
  TyInt |
  TyDecimal |
  TyTime |
  TyBool |
  TyString |
  TyUnit
  deriving (Eq,Ord,Show)

data TyRow n =
  Row (n, Type n) | Empty
  deriving (Eq,Ord,Show)

-- | Our internal core type language
--   Tables, rows and and interfaces are quite similar,
--    t ::= B
--      |   v
--      |   t -> t
--      |   row
--      |   list<t>
--      |   interface name row
--
--    row  ::= {name:t, row*}
--    row* ::= name:t | ϵ
data Type n
  = TyVar n
  | TyPrim PrimType
  | TyFun (Type n) (Type n)
  | TyRow [TyRow n]
  -- ^ Row objects
  | TyList (Type n)
  -- ^ List aka [a]
  | TyTable (Maybe n) [TyRow n]
  -- ^ Tables, which may be inlined or optionally named
  -- | TyGuard n
  -- -- ^ Guards
  | TyCap n (Type n) [TyRow n]
  -- ^ Capabilities (do we want the dependent caps as part of the type?)
  | TyInterface n [TyRow n]
  deriving (Eq, Ord, Show)

data TypeScheme 
