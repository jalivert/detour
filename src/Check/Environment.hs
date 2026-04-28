module Check.Environment where


import Data.Map.Strict qualified as Map

import Syntax.Theorem ( Theorem )
import Syntax.Term ( Rigid )
import Syntax.Type ( Type )

import {-# SOURCE #-} Check.Assertion ( Assertion )


data Environment = Env{ lem                 :: Bool
                      , theorems            :: Map.Map String Theorem
                      , depth               :: Int
                      , assert'scope        :: Map.Map String Assertion
                      , current'theorem     :: Maybe String
                      , rigid'vars          :: [Rigid]
                      , proof'context       :: [String]
                      , context'prefix      :: String }
  deriving (Show, Eq)


init'env :: Bool -> Environment
init'env lem = Env{ lem             = lem
                  , theorems        = Map.empty
                  , assert'scope    = Map.empty
                  , depth           = 0
                  , current'theorem = Nothing
                  , rigid'vars      = []
                  , proof'context   = []
                  , context'prefix  = "" }
