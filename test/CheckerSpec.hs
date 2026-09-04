module CheckerSpec (spec) where


import Data.Either (isLeft)
import Data.Maybe (isNothing)
import Test.Hspec

import Check.Environment (Environment (lem), init'env)
import Helper (checkFile, replace, runCheck)


spec :: Spec
spec = do
  implSrc <- runIO (readFile "exs/impl.dt")

  describe "Checker.check'module" $ do

    it "checks the ==>-intro/==>-elim proof in exs/impl.dt" $ do
      checkFile False "exs/impl.dt" `shouldReturn` Right [("foo", Nothing)]


    it "checks the Top-intro proof in examples/simplest.dt" $ do
      res <- checkFile False "examples/simplest.dt"
      res `shouldSatisfy` either (const False) (all (isNothing . snd))


    it "checks the Exists-intro proof in ex-talk/ex.dt" $ do
      res <- checkFile False "ex-talk/ex.dt"
      res `shouldSatisfy` either (const False) (all (isNothing . snd))


    it "checks axioms with Forall-elim in exs/a.dt" $ do
      res <- checkFile False "exs/a.dt"
      res `shouldSatisfy` either (const False) (all (isNothing . snd))


    it "rejects the faulty Exists-intro step in exs/wrong-ex.dt" $ do
      res <- checkFile False "exs/wrong-ex.dt"
      case res of
        Right [("wrong", Just err)] ->
          show err `shouldContain` "∃-intro"
        other ->
          expectationFailure ("expected single failing theorem `wrong', got: " ++ show other)


    it "rejects references to unknown assumptions" $ do
      let bad = replace "on p, p1" "on p, nosuch" implSrc
      case runCheck False bad of
        Right [("foo", Just err)] ->
          show err `shouldContain` "Unknown identifier"
        other ->
          expectationFailure ("expected `foo' to fail on an unknown identifier, got: " ++ show other)


    it "rejects references to unknown theorems" $ do
      let bad = replace "by rule ==>-elim on p, p1" "by theorem nosuchthm on p, p1" implSrc
      case runCheck False bad of
        Right [("foo", Just err)] ->
          show err `shouldContain` "Unknown theorem"
        other ->
          expectationFailure ("expected `foo' to fail on an unknown theorem, got: " ++ show other)


    it "succeeds vacuously on a module with no theorems" $ do
      checkFile False "exs/rejected.dt" `shouldReturn` Right []


    it "surfaces parse errors as Left without checking anything" $ do
      runCheck False "this is not valid detour @@@ ###" `shouldSatisfy` isLeft


  describe "Check.Environment.init'env" $ do

    it "records the LEM flag from the --lem/--no-lem CLI switch" $ do
      lem (init'env True) `shouldBe` True
      lem (init'env False) `shouldBe` False


  describe "proof by contradiction" $ do

    -- Double-negation elimination needs the classical rule, so the
    -- --lem/--no-lem switch must decide whether it checks.
    let dne = unlines
          [ "module dnetest"
          , ""
          , "theorem dne : ¬(¬(A)) ⊢ A"
          , "| nn : ¬(¬(A))"
          , "|----------------------------"
          , "|"
          , "| c : | n : ¬(A)"
          , "|     |--------------------------------"
          , "|     |"
          , "|     | f : ⊥ by rule ¬-elim on nn, n"
          , "| A by rule proof-by-contradiction on c"
          ]

    it "rejects proof by contradiction without the LEM flag" $ do
      case runCheck False dne of
        Right [("dne", Just err)] ->
          show err `shouldContain` "disallowed"
        other ->
          expectationFailure ("expected `dne' to be disallowed, got: " ++ show other)


    it "accepts proof by contradiction with the LEM flag" $ do
      runCheck True dne `shouldBe` Right [("dne", Nothing)]
