module Agda.TypeChecking.Primitive.Cubical.UIP (
  -- prim_sqPFill', prim_uip',
  prim_sqFill'
  ) where

import Agda.TypeChecking.Monad
-- import Agda.TypeChecking.Primitive.Cubical
import Agda.TypeChecking.Names
import Agda.TypeChecking.Reduce
import Agda.TypeChecking.Primitive.Cubical.Base

import Agda.Syntax.Internal
import Agda.Syntax.Common
import Agda.TypeChecking.Primitive.Base
import Agda.TypeChecking.Substitute

import Agda.Utils.Impossible
import Agda.TypeChecking.Level (LevelKit(lvlZero))
import Agda.TypeChecking.SizedTypes.Utils (debug)
import Agda.Syntax.Common.Pretty (Pretty(pretty))
import Agda.TypeChecking.Pretty
import Agda.TypeChecking.Warnings (warning)
import Agda.TypeChecking.Free (freeIn)
import Agda.Utils.Maybe (isJust, fromJust)

isNonDep :: Term -> Maybe Term
isNonDep (Lam _ b) = isNoAbs b
isNonDep _         = Nothing

sqFillProduct :: (HasBuiltins m) => (Arg Term) -> (Arg Term) -> m Term
sqFillProduct bA bB = do
  tmSqFill    <- getTerm "for SqFillProduct" builtin_sqFill -- recursive!
  sqFillProduct <- getTerm "for SqFillProduct" builtinSqFillProduct
  let
    sqFillA = apply tmSqFill [bA]
    sqFillB = apply tmSqFill [bB]
  return $ apply sqFillProduct [bA, defaultArg sqFillA, bB, defaultArg sqFillB]

sqFillSigma :: (HasBuiltins m) => (Arg Term) -> (Arg Term) -> m Term
sqFillSigma bA bB = do
  let sqFillA :: Term = apply tmSqFill [bA]
  sqFillSigma <- getTerm "for SqFillSigma" builtinSqFillSigma
  sqFillB <- runNamesT [] $ ( do
    bB' <- open bB
    sf <- open tmSqFill
    lam "a" $ \a -> sf <@> (bB' <@> a))
  return $ apply sqFillSigma [bA, defaultArg sqFillA, defaultArg bB, defaultArg sqFillB]

prim_sqFill' :: TCM PrimitiveImpl
prim_sqFill' = do
  requireCubical CUip
  t <- runNamesT [] $
       nPi' "A" tset $ \ bA ->
       el $ primSqFill <@> bA

  return $ PrimImpl t $
    -- primfunargoccur is for positivity when my primitive is applied to an inductive type.
    -- YJ: try when applying to an inductive type.
    PrimFun __IMPOSSIBLE__ 1 [] $ \ts nelims -> do
      case ts of
        bC:rest -> do
          sbC <- reduceB' bC
          let tbC = unArg $ ignoreBlocking sbC
          mSigma      <- getBuiltinName' builtinSigma
          mUnit       <- getBuiltinName' builtinUnit
          mBool       <- getBuiltinName' builtinBool
          mNat       <- getBuiltinName' builtinNat
          mList       <- getBuiltinName' builtinList
          mMaybe       <- getBuiltinName' builtinMaybe
          mProduct    <- getBuiltinName' builtinProduct
          mCoproduct  <- getBuiltinName' builtinCoproduct
          mpath  <- getBuiltinName' builtinPath
          mpathp <- getBuiltinName' builtinPathP
          let tLam = Lam defaultArgInfo
              todo = nored bC -- TODO: empty records

          case tbC of

            Pi aDom bAbs -> do
              tmSqFill <- getTerm "for SqFillPi" builtin_sqFill -- recursive!
              sqFillPi <- getTerm "for SqFillPi" builtinSqFillPi
              let
                bA = pure $ unEl (unDom aDom)
                bB = pure . tLam $ unEl <$> bAbs -- λ a. B a
                sqFillB = pure . tLam $ apply1 tmSqFill <$> unEl <$> bAbs -- λ a . primSqFill (B a)
              ret <- pure sqFillPi <@> bA <@> bB <@> sqFillB
              let ret' = ret `apply` rest
              redReturn ret'

            Def q [Apply _la, Apply _lb, Apply bA, Apply bB]
              | Just q == mSigma -> do
                -- reportSDoc "cubical.prim.uip" 40 $ "Sigma levels:" <+> pshow (unArg la) <+> pshow (unArg lb)
                -- reportSDoc "cubical.prim.uip" 40 $ "Sigma A B is" <+> prettyTCM tbC
                -- reportSDoc "cubical.prim.uip" 60 $ "in Sigma A B, A is" <+> pshow (unArg bA)
                -- reportSDoc "cubical.prim.uip" 40 $ "in Sigma A B, A is" <+> prettyTCM (unArg bA)
                -- reportSDoc "cubical.prim.uip" 60 $ "in Sigma A B, B is" <+> pshow (unArg bB)
                -- reportSDoc "cubical.prim.uip" 40 $ "in Sigma A B, B is" <+> prettyTCM (unArg bB)
                -- ctx <- getContextTelescope
                -- reportSDoc "cubical.prim.uip" 40 $ "context is" <+> pshow ctx
                -- reportSDoc "cubical.prim.uip" 40 $ "context is" <+> prettyTCM ctx
                tmSqFill    <- getTerm "for SqFillSigma" builtin_sqFill -- recursive!
                bB <- unArg <$> reduce bB
                ret <- case isNonDep bB of
                      Nothing -> do
                        let sqFillA :: Term = apply tmSqFill [bA]
                        sqFillSigma <- getTerm "for SqFillSigma" builtinSqFillSigma
                        sqFillB <- runNamesT [] $ ( do
                          bB' <- open bB
                          sf <- open tmSqFill
                          lam "a" $ \a -> sf <@> (bB' <@> a))
                        return $ apply sqFillSigma [bA, defaultArg sqFillA, defaultArg bB, defaultArg sqFillB]

                      Just bB -> sqFillProduct bA (defaultArg bB)
                redReturn $ ret `apply` rest

              | Just q == mProduct -> do
                ret <- sqFillProduct bA bB
                redReturn $ ret `apply` rest

              | Just q == mCoproduct -> do
                tmSqFill    <- getTerm "for SqFillCoproduct" builtin_sqFill -- recursive!
                sqFillCoproduct <- getTerm "for SqFillCoproduct" builtinSqFillCoproduct
                let
                  sqFillA = apply tmSqFill [bA]
                  sqFillB = apply tmSqFill [bB]
                  ret = apply sqFillCoproduct [bA, defaultArg sqFillA, bB, defaultArg sqFillB]
                redReturn $ ret `apply` rest

            Def q []
              | Just q == mUnit -> do
                reportSDoc "cubical.prim.uip" 40 $ "we are getting Unit type" <+> prettyTCM tbC
                sqFillUnit <- getTerm "for SqFillUnit" builtinSqFillUnit
                redReturn $ sqFillUnit `apply` rest

              | Just q == mBool -> do
                reportSDoc "cubical.prim.uip" 40 $ "we are getting Bool type" <+> prettyTCM tbC
                sqFillBool <- getTerm "for SqFillBool" builtinSqFillBool
                redReturn $ sqFillBool `apply` rest

              | Just q == mNat -> do
                reportSDoc "cubical.prim.uip" 40 $ "we are getting Nat type" <+> prettyTCM tbC
                sqFillNat <- getTerm "for SqFillNat" builtinSqFillNat
                redReturn $ sqFillNat `apply` rest

            Def q [Apply _la, Apply bA]
              | Just q == mList -> do
                reportSDoc "cubical.prim.uip" 40 $ "we are getting List type" <+> prettyTCM tbC
                tmSqFill    <- getTerm "for SqFillList" builtin_sqFill -- recursive!
                sqFillList <- getTerm "for SqFillList" builtinSqFillList
                let sqFillA :: Term = apply tmSqFill [bA]
                redReturn $ apply sqFillList ([bA, defaultArg sqFillA] ++ rest)

              | Just q == mMaybe -> do
                reportSDoc "cubical.prim.uip" 40 $ "we are getting Maybe type" <+> prettyTCM tbC
                tmSqFill    <- getTerm "for SqFillList" builtin_sqFill -- recursive!
                sqFillMaybe <- getTerm "for SqFillMaybe" builtinSqFillMaybe
                let sqFillA :: Term = apply tmSqFill [bA]
                redReturn $ apply sqFillMaybe ([bA, defaultArg sqFillA] ++ rest)

            -- Level _la is ignored; prim^sqFill only applies at level 0 (A : Type).
            -- Note: reducing bC always unfolds _≡_ to PathP, so the Just path' == mpath
            -- guard is never fired in practice; the isNonDep check handles non-dep paths.
            Def path' [Apply _la, Apply bP, Apply x, Apply y]
              | Just path' == mpath || isJust (isNonDep (unArg bP)) -> do
                reportSDoc "cubical.prim.uip" 40 $ "we are getting path type" <+> prettyTCM tbC
                tmSqFill    <- getTerm "for SqFillPath" builtin_sqFill -- recursive!
                sqFillPath <- getTerm "for SqFillPath" builtinSqFillPath
                iZero <- getTerm "for SqFillPathP" builtinIZero
                let
                  bA = (unArg bP) `apply` [defaultArg iZero]
                  sqFillA :: Term = apply tmSqFill [defaultArg bA]
                redReturn $ sqFillPath `apply` [defaultArg bA, x, y, defaultArg sqFillA]

              | Just path' == mpathp -> do
                reportSDoc "cubical.prim.uip" 40 $ "we are getting pathp type" <+> prettyTCM tbC
                tmSqFill    <- getTerm "for SqFillPathP" builtin_sqFill -- recursive!
                sqFillPathP <- getTerm "for SqFillPathP" builtinSqFillPathP
                iOne <- getTerm "for SqFillPathP" builtinIOne
                iZero <- getTerm "for SqFillPathP" builtinIZero
                let
                  bA = (unArg bP) `apply` [defaultArg iZero]
                  bB = (unArg bP) `apply` [defaultArg iOne]
                  sqFillA :: Term = apply tmSqFill [defaultArg bA]
                redReturn $ sqFillPathP `apply` [defaultArg bA, defaultArg bB, x, y, bP, defaultArg sqFillA]

            -- record types
            Def qname elims -> do
              constInfo <- getConstInfo qname
              let
                lam_i = Lam defaultArgInfo . Abs "i"

                -- When should Kan operations on a record value reduce?
                doR r@Record{recEtaEquality' = eta} = case theEtaEquality eta of
                  -- If it's a no-eta, pattern-matching record, then the
                  -- Kan operations behave as they do for data types; Only
                  -- reduce when the base is a constructor
                  -- YJ: u0 is not reduced. Can/should we reduce it first?
                  NoEta PatternMatching -> case unArg u0 of
                    Con{} -> True
                    _ -> False
                  -- For every other case, we can reduce into a value
                  -- defined by copatterns; However, this would expose the
                  -- internal name of transp/hcomp when printed, so hold
                  -- off until there are projections.
                  -- YJ: what about eta, pattern-matching?
                  _ -> nelims > 6
                doR _ = False

              -- Record and data types have their own implementations of
              -- the Kan operations, which get generated as part of their
              -- definition.
              case theDef info of
                  -- Records know how to hcomp themselves:
                  | doR r, Just as <- allApplyElims es, Just hCompR <- nameOfHComp kit ->
                    redReturn $ Def hCompR [] `apply` (as ++ [ignoreBlocking sphi, fromMaybe __IMPOSSIBLE__ u,u0])

                  -- If this is a record with no fields, then compData
                  -- will know what to do with it:
                  | Just as <- allApplyElims es, [] <- recFields r ->
                    compData Nothing False (recPars r) cmd l (as <$ t) sbA sphi u u0

                -- For data types, if this data type is indexed and/or a
                -- higher inductive type, then hcomp is normal; But
                -- compData knows what to do for the general cases.
                Datatype{dataPars = pars, dataIxs = ixs, dataPathCons = pcons, dataTransp = mtrD}
                  | and [null pcons && ixs == 0 | DoHComp  <- [cmd]], Just as <- allApplyElims es ->
                    compData mtrD (not (null pcons) || ixs > 0) (pars + ixs) cmd l (as <$ t) sbA sphi u u0

                _          -> fallback

            Def q _ -> do
              reportSDoc "cubical.prim.uip" 40 $ "we are getting unmatched def type" <+> prettyTCM tbC
              reportSDoc "cubical.prim.uip" 40 $ "the qname is" <+> prettyTCM q
              reportSDoc "cubical.prim.uip" 40 $ "the list qname is" <+> prettyTCM mList
              reportSDoc "cubical.prim.uip" 60 $ "the givn qname is" <+> pshow q
              reportSDoc "cubical.prim.uip" 60 $ "the list qname is" <+> pshow (fromJust mList)
              nored bC

            t -> do
              reportSDoc "cubical.prim.uip" 40 $ "we are getting type" <+> prettyTCM tbC
              reportSDoc "cubical.prim.uip" 60 $ "internal representation:" <+> pshow tbC
              nored bC

        [] -> __IMPOSSIBLE__ -- not enough arguments
      where
        nored t = return $ NoReduction [notReduced t]


-- -- Only for Type.
-- prim_sqPFill' :: TCM PrimitiveImpl
-- prim_sqPFill' = do
--   requireCubical CUip
--   t <-  runNamesT [] $
--         nPi' "A" (primIntervalType --> primIntervalType --> tset) $ \ bA ->
--         let tySqPFill = getTerm "for SqPFill" builtinSqPFill in
--         el $ tySqPFill <@> bA

--   return $ PrimImpl t $
--     PrimFun __IMPOSSIBLE__ 9 [] $ \ts _nelims -> do
--       case ts of
--         bC:rest -> do
--           reportSDoc "cubical.prim.uip" 30 $ (text "reducing type") <+> prettyTCM bC
--           sbC <- reduceB' bC
--           reportSDoc "cubical.prim.uip" 30 $ (text "reduced type") <+> prettyTCM sbC
--           case unArg $ ignoreBlocking sbC of
--             Pi aDom bAbs -> do
--               reportSDoc "cubical.prim.uip" 20 "we are in SqPFillPi"
--               tySqPFill <- getTerm "for SqPFillPi" builtinSqPFill
--               sqPFillPi <- getTerm "for SqPFillPi" builtinSqPFillPi
--               -- A -> B -> SqPFill B -> SqPFill (A -> B), but dependent
--               let bA = pure $ unEl (unDom aDom)
--               let bB = pure $ unEl (unAbs bAbs)
--               let sqPFillB = pure tySqPFill <@> bB
--               -- ret <- pure sqPFillPi <@> bA <@> bB <@> sqPFillB
--               ret <- foldl (<@>) (pure sqPFillPi) ([bA, bB, sqPFillB] ++ map (pure . unArg) rest)
--               redReturn ret
--             -- Lam arginfo (NoAbs {unAbs = (Lam arginfo' (NoAbs {unAbs = t}))}) -> do
--             t@(Lam _ _) -> do
--               reportSDoc "cubical.prim.uip" 20 $ text (show t)
--               nored
--             _ -> nored
--         [] -> nored
--       where
--         nored = return $ NoReduction []

-- prim_uip' :: TCM PrimitiveImpl
-- prim_uip' = do
--   requireCubical CUip
--   t <-  runNamesT [] $
--         hPi' "a" (els (pure LevelUniv) (cl primLevel)) $ \ la ->
--         hPi' "A" (sort . tmSort <$> la) $ \ bA ->
--         nPi' "x" (el' la bA) $ \ x ->
--         nPi' "y" (el' la bA) $ \ y ->
--         let pathxy = cl primPath <#> la <#> bA <@> x <@> y in
--         nPi' "p" (el' la $ pathxy) $ \ p ->
--         nPi' "q" (el' la $ pathxy) $ \ q ->
--         el' la $ cl primPath <#> la <#> pathxy <@> p <@> q
--   return $ PrimImpl t $
--     PrimFun __IMPOSSIBLE__ 6 [] $ \ts _nelims ->
--       return $ NoReduction []

-- ifThenElse :: HasBuiltins m => m Term
-- ifThenElse = runNamesT [] $ do
--   lam "i" $ \ i ->
--     lam "j" $ \ j ->
--     lam "k" $ \ k -> (imax (imin k (imax (ineg i) j)) (imin j (imax i k)))

-- transport :: HasBuiltins m => m Term -> m Term -> m Term -> m Term
-- transport l p a = do
--   tTrans <- getTerm "transp for UIP" builtinTrans
--   iz     <- getTerm "izero for UIP" builtinIZero
--   return tTrans <#> l <@> p <@> return iz <@> a

-- -- spread : (i j : I) → (a : A i j) → (i' j' : I) → A i' j'
-- -- This is done by "transport"-ing a,
-- -- since we could not state the transp cofibration when (i = i' ∧ j = j').
-- spread :: HasBuiltins m => m Term
-- spread = runNamesT [] $ do
--   lam "lA"   $ \ lA ->
--     lam "bA" $ \ bA ->
--     lam "i"  $ \ i ->
--     lam "j"  $ \ j ->
--     lam "a"  $ \ a ->
--     lam "i'" $ \ i' ->
--     lam "j'" $ \ j' -> do
--       let
--         iCoe k = ifThenElse <@> k <@> i <@> i'
--         jCoe k = ifThenElse <@> k <@> j <@> j'
--       transport lA (lam "k" \k -> bA <@> iCoe k <@> jCoe k) a

-- -- transportFiller : {l A B} (p : A ≡ B) → (a : A) → a ≡ transport p a
-- -- transportFiller p a i = transp (λ j → p (i ∧ j)) (~ i) a
-- transportFiller :: HasBuiltins m => m Term
-- transportFiller = runNamesT [] $ do
--   lam "lA" $ \lA ->
--     lam "bA" $ \bA ->
--     lam "bB" $ \bB ->
--     lam "p"  $ \p ->
--     lam "a"  $ \a ->
--     lam "i"  $ \i -> do
--       tTrans <- getTerm "transp for UIP" builtinTrans
--       return tTrans <#> lA <@> (lam "j" \j -> p <@> (imin i j)) <@> ineg i <@> a

-- -- ≡spread : (i j : I) (a : A i j) → a ≡ spread i j a i j
-- -- ≡spread i j a = transport-filler (λ k → A (if k then i else i end) (if k then j else j end)) a
-- spreadFill :: HasBuiltins m => m Term
-- spreadFill = runNamesT [] $ do
--   lam "lA" $ \lA ->
--     lam "bA" $ \bA ->
--     lam "i" $ \i ->
--     lam "j" $ \j ->
--     lam "a" $ \a ->
--     lam "i'" $ \i' ->
--     lam "j'" $ \j' -> do
--       let
--         iCoe k = ifThenElse <@> k <@> i <@> i'
--         jCoe k = ifThenElse <@> k <@> j <@> j'
--       transportFiller <#> lA <@> (lam "k" \k -> bA <@> iCoe k <@> jCoe k) <@> a
--   lam "lA" $ \lA ->
--     lam "bA" $ \bA ->
--     lam "i" $ \i ->
--     lam "j" $ \j ->
--     lam "a" $ \a ->
--     lam "i'" $ \i' ->
--     lam "j'" $ \j' -> do
--       let
--         iCoe k = ifThenElse <@> k <@> i <@> i'
--         jCoe k = ifThenElse <@> k <@> j <@> j'
--       transportFiller <#> lA <@> (lam "k" \k -> bA <@> iCoe k <@> jCoe k) <@> a
