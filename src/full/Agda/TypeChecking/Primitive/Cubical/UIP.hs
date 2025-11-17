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

ifThenElse :: ReduceM Term
ifThenElse = runNamesT [] $ do
  lam "i" $ \ i ->
    lam "j" $ \ j ->
    lam "k" $ \ k -> (imax (imin k (imax (ineg i) j)) (imin j (imax i k)))

transport :: ReduceM Term -> ReduceM Term -> ReduceM Term
transport p a = do
  tTrans <- getTerm "transp for UIP" builtinTrans
  iz     <- getTerm "izero for UIP" builtinIZero
  pure tTrans <@> p <@> pure iz <@> a

spread :: ReduceM Term
spread = runNamesT [] $ do
  lam "i" $ \i ->
    lam "j" $ \j ->
    lam "a" $ \a -> 
    lam "i'" $ \i' ->
    lam "j'" $ \j' -> do
      p <- lam "k" \k -> A coe
      return $ transport 

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
        [a, bA] -> do
          sbA <- reduceB' bA
          case unArg $ ignoreBlocking sbA of
            t@(Pi bDom bCodom) -> redReturn t
            _ -> nored
        _ -> nored
      where
        nored = return $ NoReduction []