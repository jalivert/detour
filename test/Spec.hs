import Test.Hspec

import CheckerSpec qualified
import ParserSpec qualified


main :: IO ()
main = hspec $ do
  ParserSpec.spec
  CheckerSpec.spec
