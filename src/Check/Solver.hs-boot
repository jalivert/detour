module Check.Solver where

import {-# SOURCE #-} Check.Check ( Check )
import Check.Substitution ( Substitution )


get'subst :: Monad m => Check m Substitution
