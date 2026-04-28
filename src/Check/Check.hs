module Check.Check where


-- import Control.Monad.Reader ( ReaderT, asks )
-- import Control.Monad.State ( MonadState(get, put), gets, StateT )
-- import Control.Monad.Except ( Except, throwError, withError )
import Control.Monad.InteractT

import Data.List ( intercalate )
import Data.List.Extra ( trim )
import Data.Map.Strict qualified as Map

import Syntax.Term ( Term(..), Var(..), Rigid(..), Constant(..), Bound(..), Free(..) )
import Syntax.Theorem ( Theorem )
import Syntax.Formula ( Formula(..) )
import Syntax.Relation ( Relation(..), Prop'Var(..) )
import Syntax.Type ( Type(..), Type'Scheme(..) )
import Syntax.Judgment ( Judgment )

import Check.Error ( Error(..) )
import Check.Environment ( Environment(..) )
import Check.State ( State(..), Level(..) )
import Check.Constraint ( Constraint(..) )
import {-# SOURCE #-} Check.Types ( instantiate'scheme )
import {-# SOURCE #-} Check.Assertion ( Assertion )


-- type Check a
--   = ReaderT
--       Environment
--       (StateT
--         State
--         (Except Error))
--       a


type Check m a = InteractT Environment State Error m a


data Context = Context  { theorem'name :: String
                        , local'assertions :: [(String, Assertion)]
                        , known'theorems :: [(String, Theorem)]
                        , proof'ctxt :: [String] }
  deriving (Show)


data Q a where
  What'Next :: Context -> Formula -> Q Command
  Inform :: Context -> String -> Q ()


instance Show (Q a) where
  show (What'Next ctx goal) = "What'Next? " ++ show goal ++ " happening within " ++ show ctx
  show (Inform ctx msg) = "Inform about: " ++ show msg ++ " happening within " ++ show ctx


data Command  = IDK
              | Assert String
  deriving (Show)

newtype Number = Number Int
  deriving (Show)


instance Interact Q IO where
  request :: Q r -> IO r

  request (What'Next c@Context{ theorem'name, local'assertions, known'theorems, proof'ctxt } goal) = do
    putStrLn ""
    putStrLn $! "I am solving a theorem `" ++ theorem'name ++ "'"
    putStrLn $! intercalate "\n" (reverse proof'ctxt)
    putStrLn $! "My current goal is: `" ++ show goal ++ "'"
    source <- get'source
    case trim source of
      "list theorems" -> do
        putStrLn "Proven theorems:"
        putStrLn $! intercalate "\n" (map show known'theorems)
        request (What'Next c goal)

      "list locals" -> do
        putStrLn "Local assertions:"
        putStrLn $! intercalate "\n" (map show local'assertions)
        request (What'Next c goal)

      "" -> do
        return IDK

      _ -> do
        return (Assert source)

    where get'source :: IO String
          get'source = do
            line <- getLine
            case line of
              "" -> return ""
              _ -> do
                rest <- get'source
                return $! line ++ "\n" ++ rest

  request (Inform Context{ theorem'name } about) = do
    putStrLn ""
    putStrLn $! "I am solving a theorem `" ++ theorem'name ++ "'"
    putStrLn about
    return ()


inform'about :: Interact Q m => String -> Check m ()
inform'about msg = do
  context <- get'context
  inter (Inform context msg)


ask'for'next :: Interact Q m => Formula -> Check m Command
ask'for'next fm = do
  context <- get'context
  inter (What'Next context fm)


get'context :: Interact Q m => Check m Context
get'context = do
  th'name <- get'theorem'name

  thrms <- asks theorems
  let ths = Map.assocs thrms

  assertions <- asks assert'scope
  let asserts = Map.assocs assertions

  p'c <- asks proof'context

  return $! Context{ theorem'name = th'name, local'assertions = asserts, known'theorems = ths, proof'ctxt = p'c }



get'theorem'name :: Interact Q m => Check m String
get'theorem'name = do
  th'name <- asks current'theorem
  case th'name of
    Nothing -> throwError $! Err "internal error: theorem name is not present even though I am checking some theorem"
    Just n -> return n




withError' m e = withError (const e) m


because :: Monad m => String -> Check m a -> Check m a
because msg m = withError (\ (Err msg') -> (Err (msg ++ "\nand " ++ msg'))) m


fresh'name :: Monad m => Check m String
fresh'name = do
  s@State{ counter } <- get
  put s{ counter = counter + 1 }
  return $! "_" ++ show counter


fresh'proposition :: Monad m => Check m Formula
fresh'proposition = do
  name <- fresh'name
  return $! Atom (Meta'Rel (Prop'Var name))


fresh'free :: Monad m => Check m Free
fresh'free = do
  n <- fresh'name

  d <- asks depth

  s <- get
  free'depths <- gets free'depth'context
  put s{ free'depth'context = Map.insert (F n) d free'depths }

  return (F n)


fresh'constant :: Monad m => Level -> Check m Constant
fresh'constant l = do
  name <- fresh'name

  return (C name)


free'level :: Monad m => Free -> Check m Int
free'level f = do
  free'depths <- gets free'depth'context
  case Map.lookup f free'depths of
    Nothing -> do
      throwError (Err ("Internal Error. The free variable `" ++ show f ++ "' is not recorded in the context."))

    Just l -> return l


rigid'level :: Monad m => Rigid -> Check m Int
rigid'level r = do
  rigid'depths <- gets rigid'depth'context
  case Map.lookup r rigid'depths of
    Nothing -> do
      throwError (Err ("Internal Error. The rigid variable `" ++ show r ++ "' is not recorded in the context."))

    Just l -> return l


fresh'bound :: Monad m => Check m Bound
fresh'bound = do
  n <- fresh'name

  return (B n)


fresh'type :: Monad m => Check m Type
fresh'type = do
  n <- fresh'name

  return (Type'Var n)


fresh'type'const :: Monad m => Check m Type
fresh'type'const = do
  n <- fresh'name

  return (Type'Const n)


class Collect a where
  collect :: Monad m => Constraint a -> Check m ()


instance Collect Term where
  collect :: Monad m => Constraint Term -> Check m ()
  collect constraint = do
    s@State{ term'constraints } <- get
    put s{ term'constraints = constraint : term'constraints}


instance Collect Formula where
  collect :: Monad m => Constraint Formula -> Check m ()
  collect constraint = do
    s@State{ formula'constraints } <- get
    put s{ formula'constraints = constraint : formula'constraints}


instance Collect Type where
  collect :: Monad m => Constraint Type -> Check m ()
  collect constraint = do
    s@State{ type'constraints } <- get
    put s{ type'constraints = constraint : type'constraints }


look'up'theorem :: Monad m => String -> Check m Theorem
look'up'theorem name = do
  thms <- asks theorems

  case Map.lookup name thms of
    Nothing -> do
      throwError $! Err ("Unknown theorem `" ++ name ++ "'.")

    Just thm -> do
      return thm


look'up'type :: Monad m => String -> Check m Type
look'up'type name = do
  t'ctx <- gets typing'ctx

  case Map.lookup name t'ctx of
    Nothing -> throwError $! Err ("Type Error. I don't know a variable or a constant named `" ++ name ++ "'.")

    Just ts -> do
      t <- instantiate'scheme ts
      return t


type'of :: Monad m => Term -> Check m Type
type'of (Var v) = do
  t'ctx <- gets typing'ctx
  let s = case v of
            Free (F s) -> s
            Rigid (R s) -> s

  case Map.lookup s t'ctx of
    Nothing -> do
      throwError $! Err ("I can not get a type of a variable `" ++ s ++ "' because I don't know it.")

    Just ts -> do
      t <- instantiate'scheme ts
      return t

-- type'of (App (C s) []) = do
--   t'ctx <- asks typing'ctx

--   case Map.lookup s t'ctx of
--     Nothing -> do
--       throwError $! Err ("I can not get a type of a constant `" ++ s ++ "' because I don't know it.")

--     Just t -> return t

type'of (App (C s) args) = do
  --  get the type of the function/constant
  --  it should be a function type
  --  infer all the types of the arguments and unify them with the types of parameters in the function type

  t'ctx <- gets typing'ctx

  case Map.lookup s t'ctx of
    Nothing -> do
      throwError $! Err ("I can not get a type of a constant `" ++ s ++ "' because I don't know it.")

    Just ts -> do
      t <- instantiate'scheme ts
      unify'args args t

  where unify'args :: Monad m => [Term] -> Type -> Check m Type
        unify'args [] t = return t
        unify'args (t : ts) ty = do
          t't <- type'of t

          par <- fresh'type
          res <- fresh'type
          let fn't = Type'Fn par res

          collect (fn't :≡: ty)
          collect (t't :≡: par)

          unify'args ts res


type'of term = undefined  --  TODO: what about Bound?
--  TODO: TYPE-CHECK
--  How do I know what type terms are?
--  Free-vars need to be in the typing environment.
--  Bound-vars are not there yet, but I think I can get them there using local.
--    What I am thinking about is this—when I am unifying two quantified formulae
--    I rename two bound variables to a same name and then unify those formulae.
--    Bounds unify only with bounds, so if I run the unification of the bodies within a local
--    that should be enough. Because Bounds can't even unify with free-vars.
--    This should mean that they should never end up in a substitution, right?
--    What if I want to unify a free-var with an application featuring a bound-var?
--    Like this: x :≡: ƒ(α, b)    where α is a bound-var
--    This produces a substitution containing the uniqly created bound-var `α`.
--    And I thought it could never end up in the substitution.
--    This could mean that later, when I try to unify something else with `α` I will need its type
--    and I can't have it.
--    On the other hand, the only thing that can unify with `α` is precisely `α`. And then their types don't matter.

--    So, bound-vars don't need to go in the typing environment.
--    But then, how do I know that ƒ is applied to a correctly typed α?
--    It would help to track them in the environment.

--  How do I even check that a function is applied to a correctly typed arguments?
--  When do I check that?
--

--  Checking applications should go like this—I must know the function.
--  It is either a constructor or it has been mentioned in a formula when asserting something about that function.
--  Like:  ∀ (m : ℕ) (n : ℕ) : ℕ(m + n)
--  I need to collect these "declaratitions" and record that + : ℕ -> ℕ -> ℕ
--  then I can type-check any term.


--  It might also be worth considering to exclude quantified formulae from unification somehow.
--  Instead of checking that two formulae are the same using unification on quantified formulae,
--  I would use a special function that would not "misuse" unification for checking that those binders
--  are corresponding to one another.
--  There would still be unification happening on types and terms but not on bounds.
--  Can I do that?