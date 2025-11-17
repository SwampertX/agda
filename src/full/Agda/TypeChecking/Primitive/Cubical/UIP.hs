module Agda.TypeChecking.Primitive.Cubical.UIP (primSqFill') where

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

ifThenElse :: HasBuiltins m => m Term
ifThenElse = runNamesT [] $ do
  lam "i" $ \ i ->
    lam "j" $ \ j ->
    lam "k" $ \ k -> (imax (imin k (imax (ineg i) j)) (imin j (imax i k)))

transport :: HasBuiltins m => m Term -> m Term -> m Term
transport p a = do
  tTrans <- getTerm "transp for UIP" builtinTrans
  iz     <- getTerm "izero for UIP" builtinIZero
  return tTrans <@> p <@> return iz <@> a

-- spread : (i j : I) → (a : A i j) → (i' j' : I) → A i' j'
-- This is done by "transport"-ing a,
-- since we could not state the transp cofibration when (i = i' ∧ j = j').
spread :: HasBuiltins m => m Term
spread = runNamesT [] $ do
  lam "bA" $ \bA ->
    lam "i" $ \i ->
    lam "j" $ \j ->
    lam "a" $ \a ->
    lam "i'" $ \i' ->
    lam "j'" $ \j' -> do
      let
        iCoe k = ifThenElse <@> k <@> i <@> i'
        jCoe k = ifThenElse <@> k <@> j <@> j'
      transport (lam "k" \k -> bA <@> iCoe k <@> jCoe k) a

-- transportFiller : {l A B} (p : A ≡ B) → (a : A) → a ≡ transport p a
-- transportFiller p a i = transp (λ j → p (i ∧ j)) (~ i) a
transportFiller :: HasBuiltins m => m Term
transportFiller = runNamesT [] $ do
  lam "lA" $ \lA ->
    lam "bA" $ \bA ->
    lam "bB" $ \bB ->
    lam "p"  $ \p ->
    lam "a"  $ \a ->
    lam "i"  $ \i -> do
      tTrans <- getTerm "transp for UIP" builtinTrans
      return tTrans
        <@> (lam "j" \j -> p <@> (imin i j))
        <@> ineg i
        <@> a

-- ≡spread : (i j : I) (a : A i j) → a ≡ spread i j a i j
-- ≡spread i j a = transport-filler (λ k → A (if k then i else i end) (if k then j else j end)) a
spreadFill :: HasBuiltins m => m Term
spreadFill = runNamesT [] $ do
  lam "bA" $ \bA ->
    lam "i" $ \i ->
    lam "j" $ \j ->
    lam "a" $ \a ->
    lam "i'" $ \i' ->
    lam "j'" $ \j' -> do
      let
        iCoe k = ifThenElse <@> k <@> i <@> i'
        jCoe k = ifThenElse <@> k <@> j <@> j'
      transportFiller <@> (lam "k" \k -> bA <@> iCoe k <@> jCoe k) <@> a

primSqFill' :: TCM PrimitiveImpl
primSqFill' = do
  requireCubical CUip
  t <-  runNamesT [] $
        hPi' "a" (els (pure LevelUniv) (cl primLevel)) $ \ la ->
        nPi' "A" (nPi' "i" primIntervalType $ \ i ->
                  nPi' "j" primIntervalType $ \ j ->
                    (sort . tmSort <$> la)) $ \ bA ->

        let (i0, i1) = (primIZero, primIOne) in
        let bAij i j = bA <@> i <@> j in
        let pathP l f p q = cl primPathP <#> l <@> f <@> p <@> q in

        hPi' "a00" (el' la $ bAij i0 i0) $ \ a00 ->
        hPi' "a01" (el' la $ bAij i0 i1) $ \ a01 ->
        nPi' "a0_" (el' la $ pathP la (lam "j" $ \j -> bAij i0 j) a00 a01) $ \ a0_ ->

        hPi' "a10" (el' la $ bAij i1 i0) $ \ a10 ->
        hPi' "a11" (el' la $ bAij i1 i1) $ \ a11 ->
        nPi' "a1_" (el' la $ pathP la (lam "j" $ \j -> bAij i1 j) a10 a11) $ \ a1_ ->

        nPi' "a_0" (el' la $ pathP la (lam "j" $ \j -> bAij j i0) a00 a10) $ \ a_0 ->
        nPi' "a_1" (el' la $ pathP la (lam "j" $ \j -> bAij j i1) a01 a11) $ \ a_1 ->

        el' la $ pathP la
          (lam "i" $ \i -> pathP la (lam "j" $ \j -> bAij i j) (a_0 <@> i) (a_1 <@> i))
          a0_ a1_

  return $ PrimImpl t $
    PrimFun __IMPOSSIBLE__ 10 [] $ \ts _nelims ->
      case ts of
        [a, bA, ul, dl, l, ur, dr, r, u, d] -> do
          sbA <- reduceB' bA
          case unArg $ ignoreBlocking sbA of
            -- SqPFillPiAB {ul} {dl} l {ur} {dr} r u d i j a =
            --   comp (λ k → B i j (≡spread i j a (~ k))) {φ = i ∨ ~ i ∨ j ∨ ~ j}
            --   (λ where
            --       k (i = i0) → l j (≡spread i j a (~ k))
            --       k (i = i1) → r j (≡spread i j a (~ k))
            --       k (j = i0) → u i (≡spread i j a (~ k))
            --       k (j = i1) → d i (≡spread i j a (~ k))) (b i j)
            t@(Pi bDom bCodom) -> runNamesT [] $ do
              tComp <- getTerm "comp for UIP" builtinComp
              -- the term is a huge comp.
              let
                tbB     = unEl . unAbs $ bCodom
                sqFillB = primSqFill <@> pure tbB
              lam "i" $ \i ->
                lam "j" $ \j ->
                  let
                    compType =
                      lam "k" \k -> pure tbB <@> i <@> j <@> spreadFill <@> i <@> j <@> a <@> ineg k
                    phi = foldl imax primIZero [i, ineg i, j, ineg j]
                    faces = _
                    -- ^ FIXME: there is a comp example in TypeChecking.Primitive.Cubical.transpSysTel'
                    -- .. but how does one even write case lambdas?
                    sqa = spread <@> i <@> j
                    lb = lam "j" $ \j' -> l <@> j' <@> (sqa <@> primIZero <@> j')
                    rb = lam "j" $ \j' -> r <@> j' <@> (sqa <@> primIOne  <@> j')
                    ub = lam "i" $ \i' -> u <@> i' <@> (sqa <@> i' <@> primIZero)
                    db = lam "i" $ \i' -> d <@> i' <@> (sqa <@> i' <@> primIOne )
                    b = sqFillB <@> sqa <@> lb <@> rb <@> ub <@> db
                  in
                  pure tComp <@> compType <#> phi <@> faces <@> (b <@> i <@> j)
            _ -> nored
        _ -> nored
      where
        nored = return $ NoReduction []

-- primSqFillPi :: Dom Type -> Abs Type -> TCM Term
-- primSqFillPi bA bB = do
--   -- tSqFill <- getTerm "SqFill" builtinSqFill
--   -- tComp <- getTerm "SqFill" builtinComp
--   let tbB = unEl . unAbs $ bB
--   let sqFillB = primSqFill <@> pure tbB
--   primComp <@> (lam "k" \k -> pure tbB <@> i <@> j <@>)



primUIP' :: TCM PrimitiveImpl
primUIP' = do
  requireCubical CUip
  t <-  runNamesT [] $
        hPi' "a" (els (pure LevelUniv) (cl primLevel)) $ \ la ->
        hPi' "A" (sort . tmSort <$> la) $ \ bA ->
        nPi' "x" (el' la bA) $ \ x ->
        nPi' "y" (el' la bA) $ \ y ->
        let pathxy = cl primPath <#> la <#> bA <@> x <@> y in
        nPi' "p" (el' la $ pathxy) $ \ p ->
        nPi' "q" (el' la $ pathxy) $ \ q ->
        el' la $ cl primPath <#> la <#> pathxy <@> p <@> q
  return $ PrimImpl t $
    PrimFun __IMPOSSIBLE__ 6 [] $ \ts _nelims ->
      return $ NoReduction []
