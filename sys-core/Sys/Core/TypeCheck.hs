{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- | Provides functions that can take a 'Lang' and check our typing
-- rules

module Sys.Core.TypeCheck where

import           Sys.Core.Util
import           Sys.Core.Lang

import           Control.Applicative
import           Control.Comonad
import           Control.Monad (join)
import           Control.Monad.Fix
import           Control.Monad.Free.Church
import           Control.Monad.Tardis

import           Data.Distributive
import           Data.Foldable (foldl', foldlM)
import           Data.HashMap.Strict (HashMap)
import qualified Data.HashMap.Strict as HM
import qualified Data.HashSet as HS
import           Data.Hashable
import           Data.Maybe (fromMaybe)
import           Data.Text (Text)

newtype ErrorPatching var f
  = ErrorPatching (HashMap SourceDescription [Error var (TyCheckResult var f)])

data SysMessageLevel
  = SysMessageCritical
  | SysMessageError
  | SysMessageWarning
  | SysMessageInfo
  | SysMessageDebug
  deriving (Show, Eq, Ord, Enum, Bounded)

data SysF a
  = SysMessage
  { level     :: SysMessageLevel
  , subsystem :: Text
  , message   :: Text
  , sysNext   :: a }
  deriving Functor

newtype Sys a = Sys (F SysF a)
  deriving stock Functor
  deriving newtype (Applicative, Monad, MonadFix)

newHole = undefined
newEmptyHole = undefined

data JudgementContext var f
  = JudgementContext
  { judgedType :: Lang var Id (TyCheckResult var f)
  , judgedSources :: SourceLocation
  , judgedLink :: Maybe (HoleId var Id)
  }

data Judgements var f
  = Judgements
  { judged :: HashMap (HoleId var Id)
                      (JudgementContext var f)
  , lastHole :: !Integer
  , forwardErrors :: ErrorPatching var f}

findRepresentative :: (MonadFix m, Hashable var, Eq var)
                   => HoleId var Id
                   -> TardisT bw (Judgements var f) m (HoleId var Id, Maybe (Lang var Id (TyCheckResult var f), SourceLocation))
findRepresentative hole = do
  judgements <- HM.lookup hole . judged <$> getPast
  case judgements of
    Just (JudgementContext ty sources (Just hole')) -> pure (hole', Just (ty, sources))
    _ -> pure (hole, Nothing)

judge :: (MonadFix m,  Hashable var, Eq var)
      => HoleId var Id -> SourceLocation -> Lang var Id (TyCheckResult var f) -> TardisT bw (Judgements var f) m ()
judge hole loc ty = do
  judgements <- getPast
  (hole', _) <- findRepresentative hole

  let oldSources = maybe mempty judgedSources (HM.lookup hole' (judged judgements))

  sendFuture (judgements { judged = HM.insert hole' (JudgementContext ty (loc <> oldSources) Nothing) (judged judgements) })

allocHole :: MonadFix m => TardisT bw (Judgements var f) m Integer
allocHole = do
  prevHole <- lastHole <$> getPast

  let nextHole = prevHole + 1
  modifyForwards (\j -> j { lastHole = nextHole })
  return nextHole

unifyPerhaps :: (Eq var, MonadFix m) => SourceLocation -> Perhaps var -> Perhaps var
             -> TardisT (ErrorPatching var f) (Judgements var f) m  var
unifyPerhaps _ Placeholder (Explicit a) = pure a
unifyPerhaps _ (Explicit b) Placeholder = pure b
unifyPerhaps _ Placeholder Placeholder = fail "Expected at least one explicit"
unifyPerhaps locs (Explicit a) (Explicit b)
  | a == b    = pure a
  | otherwise = do
      sendErrorThroughSpaceTime locs (VariableNameMismatch a b RightHere)
      pure a

sendErrorThroughSpaceTime :: MonadFix m
                          => SourceLocation -> Error var (TyCheckResult var f)
                          -> TardisT (ErrorPatching var f) (Judgements var f) m ()
sendErrorThroughSpaceTime locs err = do
  let addErrors (ErrorPatching errs) =
        ErrorPatching $
        foldl' (\errs' loc -> HM.insert loc (err : fromMaybe [] (HM.lookup loc errs')) errs') errs locs
  modifyBackwards addErrors
  modifyForwards (\j -> j { forwardErrors = addErrors (forwardErrors j) })

collectErrors :: MonadFix m
              => SourceDescription -> TardisT (ErrorPatching var f) (Judgements var f) m [Error var (TyCheckResult var f)]
collectErrors loc = do
  let removeErrors (ErrorPatching err) = ErrorPatching (HM.delete loc err)

  modifyBackwards removeErrors
  ErrorPatching future <- getFuture
  ErrorPatching past <- forwardErrors <$> getPast

  modifyForwards (\j -> j { forwardErrors = removeErrors (forwardErrors j) })

  return (fromMaybe [] (HM.lookup loc future) ++
          fromMaybe [] (HM.lookup loc past))

collectAllErrors :: MonadFix m
                 => SourceLocation -> TardisT (ErrorPatching var f) (Judgements var f) m [ Error var (TyCheckResult var f) ]
collectAllErrors from =
  foldlM (\errs' from' -> fmap (errs' ++) (collectErrors from')) [] from

newInternalHole :: (MonadFix m, Applicative f, Comonad f, Traversable f, SysLocated f, Hashable var, Eq var)
                => SourceLocation -> Lang var Id (TyCheckResult var f)
                -> TardisT (ErrorPatching var f) (Judgements var f) m (TyCheckResult var f (Lang var Id (TyCheckResult var f)))
newInternalHole source firstTy = do
  hole <- UnnamedHole . Id <$> allocHole

  unifyJudgement hole source firstTy

  errs <- collectAllErrors (WhileInferringTheTypeOf `HS.map` source)

  typeHole <- UnnamedHole . Id <$> allocHole

  return (TyCheckResult (Hole typeHole) errs (pure (Hole hole)))


unifyJudgement :: ( MonadFix m, Hashable var, Eq var, Comonad f, Traversable f, SysLocated f )
               => HoleId var Id
               -> SourceLocation
               -> Lang var Id (TyCheckResult var f)
               -> TardisT (ErrorPatching var f) (Judgements var f) m ()
unifyJudgement hole src term =
  do (hole', oldType) <- findRepresentative hole

     newType <- case oldType of
                  Nothing -> pure term
                  Just (oldType', locs) ->
                    unify (src <> locs) (rewriteConstant really term) (rewriteConstant really oldType')

     judge hole' src newType

unify :: (SysLocated f, Comonad f, Eq var, MonadFix m)
      => SourceLocation
      -> Lang var Perhaps (TyCheckResult var f)
      -> Lang var Perhaps (TyCheckResult var f)
      -> TardisT (ErrorPatching var f) (Judgements var f) m
                 (Lang var Id (TyCheckResult var f))
unify locs a@(Ap fn1 nm1 arg1) b@(Ap fn2 nm2 arg2) =
  do fnTy' <- unify (WhileInferringTheTypeOf `HS.map` (tyLocation fn1 <> tyLocation fn2)) (tyCheckTy fn1) (tyCheckTy fn2)
     fn' <- unify (tyLocation fn1 <> tyLocation fn2) (extract (tyCheckAnn fn1)) (extract (tyCheckAnn fn2))

     nm' <- case (nm1, nm2) of
       (Nothing, Nothing) -> pure Nothing
       (Just nm1', Just nm2') ->
         Just <$> unifyPerhaps (TheNameOfTheArgument `HS.map` locs) nm1' nm2'
       _ -> do
         sendErrorThroughSpaceTime locs -- Haskel has superpowers
           (CantUnify a b
             (Namely (ThePlicityOfTheArguments nm1 nm2)))
         pure (join (fromPerhaps <$> nm1) <|> join (fromPerhaps <$> nm2))

     argTy' <- unify (WhileInferringTheTypeOf `HS.map` (tyLocation arg1 <> tyLocation arg2)) (tyCheckTy arg1) (tyCheckTy arg2)
     arg' <- unify (tyLocation arg1 <> tyLocation arg2) (extract (tyCheckAnn arg1)) (extract (tyCheckAnn arg2))

     return (Ap (TyCheckResult fnTy' (tyCheckErrors fn1 ++ tyCheckErrors fn2) (sourcedFrom (tyCheckAnn fn1) (tyCheckAnn fn2) fn'))
                (Id <$> nm')
                (TyCheckResult argTy' (tyCheckErrors arg1 ++ tyCheckErrors arg2) (sourcedFrom (tyCheckAnn arg1) (tyCheckAnn arg2) arg')))

resolve :: (Comonad f, Traversable f, Hashable var, Eq var)
        => Lang var Id (TyCheckResult var f)
        -> TardisT
             (ErrorPatching var f)
             (Judgements var f)
             Sys
             (Lang var Id (TyCheckResult var f))
resolve (Ap f Nothing arg) = Ap <$> traverse resolve f <*> pure Nothing <*> traverse resolve arg
resolve (Hole hole) =
  do holes <- judged <$> getPast
     case HM.lookup hole holes of
       Nothing -> fail ""
       Just hl -> fail ""

typeCheck :: forall var f
           . ( Comonad f, Applicative f, Traversable f, SysLocated f
             , Eq var, Hashable var )
          => f (Lang var Id f)
          -> TardisT (ErrorPatching var f)
                     -- We want to return a tree annotated with errors, but we never know when a
                     -- tree may create errors in a future unification. By sending a list of error
                     -- patches backwards through time, we can construct the tree as it ought to
                     -- have appeared
                     (Judgements var f)
                     -- This is a mapping of holes to resolved types
                     Sys
                     -- The sys monad provides common functionality for logging, staging, etc
                     (TyCheckResult var f (Lang var Id (TyCheckResult var f)))
                     -- Returns a new tree annotated with type errors encountered (or that may be
                     -- encountered in the future)

typeCheck expr =
  case extract expr of

    -- Typing rule:
    --
    -- fun : [ forall { i_n : T_n } -> ... ] forall (v : T) -> U
    -- a : T
    -- =======
    -- fun a : U
    --
    -- given i_n can be resolved in context
    Ap fun Nothing arg -> do
      funRes <- typeCheck fun
      argRes <- typeCheck arg

      -- Mental map
      --   expArgTy === T
      --   expBodyTy === U
      expArgTy <- newInternalHole (WhileInferringTheTypeOf `HS.map` location arg) (tyCheckTy argRes)
      expBodyTy <- newEmptyHole (WhileTypingTheTargetOfAnApplication `HS.map` location expr)

      -- Collect all errors reported at this exact location, from the future, potentially
      errs <- collectAllErrors (location expr)

      -- Unify the result of the function with the expected type, adding placeholders where
      -- necessary
      newHole <- allocHole
      unify (WhileInferringTheTypeOf `HS.map` location expr)
            (Pi False Placeholder (rewriteConstant really <$> expArgTy) (TyCheckResult (Hole (UnnamedHole (Explicit newHole))) [] (pure (rewriteConstant really expBodyTy))))
            (rewriteConstant really (tyCheckTy funRes))

      return (TyCheckResult expBodyTy errs (Ap funRes Nothing argRes <$ expr) ::
                 TyCheckResult var f (Lang var Id (TyCheckResult var f)))
