module ParserSpec (spec) where


import Data.Either (isLeft)
import Test.Hspec

import Helper (parseOrFail)
import Parser.Parser (parse'module)
import Syntax.Module qualified as M
import Syntax.Theorem qualified as T


spec :: Spec
spec = describe "Parser.parse'module" $ do

  it "parses an empty module and keeps its name" $ do
    modul <- parseOrFail "module impl\n"
    M.name modul `shouldBe` "impl"
    M.theorems modul `shouldBe` []


  it "parses axiom declarations with their names" $ do
    modul <- parseOrFail "module m\n\naxiom ax1 : A ==> B\n"
    map fst (M.axioms modul) `shouldBe` ["ax1"]
    M.theorems modul `shouldBe` []


  it "parses a theorem statement with premises and conclusion" $ do
    simplest <- readFile "examples/simplest.dt"
    modul <- parseOrFail simplest
    M.name modul `shouldBe` "Simplest"
    map T.name (M.theorems modul) `shouldBe` ["simplest"]


  it "parses the syntax/judgment/rule-schema declarations of e/N-n+0.dt" $ do
    src <- readFile "e/N-n+0.dt"
    modul <- parseOrFail src
    M.name modul `shouldBe` "ℕ"
    M.syntax modul `shouldSatisfy` (not . null)
    M.judgments modul `shouldSatisfy` (not . null)


  it "rejects garbage input" $ do
    parse'module "this is not valid detour @@@ ###" `shouldSatisfy` isLeft


  it "rejects the legacy `theorem name:` header still found in old sketches" $ do
    -- examples/quantifiers.dt starts with `theorem foo: ...`; the current
    -- grammar no longer accepts that header, so it must fail loudly.
    parse'module "theorem foo: A ==> B .\n" `shouldSatisfy` isLeft
