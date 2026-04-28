module Syntax.Judgment where


-- import Syntax.Assumption ( Assumption )
import Syntax.Claim ( Claim )
import Syntax.Formula ( Formula(..) )
-- import {-# SOURCE #-} Syntax.Justification ( Justification )
import {-# SOURCE #-} Syntax.Proof ( Proof )


data Judgment = Sub'Proof Proof
              | Claim Claim
              | Alias String Formula
              | Prove (Maybe String) Formula
  deriving (Eq)


instance Show Judgment where
  show (Sub'Proof proof) = show proof
  show (Claim claim) = show claim
  show (Alias name formula) = name ++ " := " ++ show formula
  show (Prove (Just n) fm) = n ++ " : prove " ++ show fm
  show (Prove Nothing fm) = "prove " ++ show fm
