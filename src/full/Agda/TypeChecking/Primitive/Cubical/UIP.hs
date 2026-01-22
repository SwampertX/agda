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

-- Only for Type.
prim_sqFill' :: TCM PrimitiveImpl
prim_sqFill' = do
  requireCubical CUip
  t <- runNamesT [] $
       nPi' "A" tset $ \ bA ->
      --  let tySqFill = getTerm "for SqFill" builtinSqFill in
       el $ primSqFill <@> bA

  return $ PrimImpl t $
    -- primfunargoccur is for positivity when my primitive is applied to an inductive type.
    -- try when applying to an inductive type.
    PrimFun __IMPOSSIBLE__ 1 [] $ \ts _nelims -> do
      case ts of
        bC:rest -> do
          sbC <- reduceB' bC
          case unArg $ ignoreBlocking sbC of
            Pi aDom bAbs -> do
              tmSqFill <- getTerm "for SqFillPi" builtin_sqFill -- recursive!
              sqFillPi <- getTerm "for SqFillPi" builtinSqFillPi
              let 
                bA = pure $ unEl (unDom aDom)
                tLam = Lam defaultArgInfo
                bB = pure . tLam $ unEl <$> bAbs -- λ a. B a 
                sqFillB = pure . tLam $ apply1 tmSqFill <$> unEl <$> bAbs -- λ a . primSqFill (B a)
              ret <- pure sqFillPi <@> bA <@> bB <@> sqFillB
              let ret' = ret `apply` rest

              redReturn ret'
            -- Def qname elims -> do
            --   nored
            t -> do
              reportSDoc "cubical.prim.uip" 40 $ "we are getting type" <+> prettyTCM t
              reportSDoc "cubical.prim.uip" 40 $ "internal representation:" <+> pshow t
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
--       -- YJ TODO: just "alias" to sqPFill.
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
