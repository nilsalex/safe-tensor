{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE NoStarIsType #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE StandaloneDeriving #-}

module Tensor where

import Safe
import TH

import Data.Kind (Type)

import Data.Singletons
import Data.Singletons.Prelude
import Data.Singletons.Decide
import Data.Singletons.TypeLits

import Control.Monad.Except

data T :: Type -> Type where
  T :: SingI l => Tensor l v -> T v

deriving instance Show v => Show (T v)

instance Functor T where
  fmap f (T t) = T $ fmap f t

(.*) :: (Num v, MonadError String m) => T v -> T v -> m (T v)
(.*) o1 o2 =
  case o1 of
    T (t1 :: Tensor l1 v) ->
      case o2 of
        T (t2 :: Tensor l2 v) ->
          let sl1 = sing :: Sing l1
              sl2 = sing :: Sing l2
          in case sMergeILs sl1 sl2 of
               SNothing  -> throwError "Tensors have overlapping indices. Cannot multiply."
               SJust sl' ->
                 withSingI sl' $
                 case sSane sl' %~ STrue of
                   Proved Refl -> return $ T (t1 &* t2)
infixl 7 .*

(.+) :: (Eq v, Num v, MonadError String m) => T v -> T v -> m (T v)
(.+) o1 o2 =
  case o1 of
    T (t1 :: Tensor l1 v) ->
      case o2 of
        T (t2 :: Tensor l2 v) ->
          let sl1 = sing :: Sing l1
              sl2 = sing :: Sing l2
          in case sl1 %~ sl2 of
               Proved Refl -> case sSane sl1 %~ STrue of
                                Proved Refl -> return $ T (t1 &+ t2)
               Disproved _ -> throwError "Generalized tensor ranks do not match. Cannot add."
infixl 6 .+

(.-) :: (Eq v, Num v, MonadError String m) => T v -> T v -> m (T v)
(.-) o1 o2 =
  case o1 of
    T (t1 :: Tensor l1 v) ->
      case o2 of
        T (t2 :: Tensor l2 v) ->
          let sl1 = sing :: Sing l1
              sl2 = sing :: Sing l2
          in case sl1 %~ sl2 of
               Proved Refl -> case sSane sl1 %~ STrue of
                                Proved Refl -> return $ T (t1 &- t2)
               Disproved _ -> throwError "Generalized tensor ranks do not match. Cannot add."

contractT :: (Num v, Eq v) => T v -> T v
contractT o =
  case o of
    T (t :: Tensor l v) ->
      let sl = sing :: Sing l
          sl' = sContractL sl
      in withSingI sl' $
         T $ contract t

transposeT :: MonadError String m =>
              Demote (VSpace Symbol Nat) -> Demote (Ix Symbol) -> Demote (Ix Symbol) ->
              T v -> m (T v)
transposeT v ia ib o = 
  case o of
    T (t :: Tensor l v) ->
      let sl = sing :: Sing l
      in withSingI sl $
         withSomeSing v $ \sv ->
         withSomeSing ia $ \sia ->
         withSomeSing ib $ \sib ->
         case sCanTranspose sv sia sib sl of
           STrue  -> return $ T $ transpose sv sia sib t
           SFalse -> throwError $ "Cannot transpose indices " ++ show v ++ " " ++ show ia ++ " " ++ show ib ++ "!"

rankT :: T v -> Demote ILists
rankT o =
  case o of
    T (t :: Tensor l v) ->
      let sl = sing :: Sing l
      in fromSing sl

someDelta :: Num v =>
             Demote Symbol -> Demote Nat -> Demote Symbol -> Demote Symbol ->
             T v
someDelta vid vdim a b =
  withSomeSing vid $ \svid ->
  withSomeSing vdim $ \svdim ->
  withSomeSing a $ \sa ->
  withSomeSing b $ \sb ->
  withKnownNat svdim $
  withKnownSymbol svid $
  withKnownSymbol sa $
  withKnownSymbol sb $
  let sl = sDeltaILists svid svdim sa sb
  in  case sTail' (sTail' sl) of
        SNil -> case sSane (sTail' sl) %~ STrue of
                  Proved Refl -> T $ delta' svid svdim sa sb

someEtaInv :: (Num v, MonadError String m) =>
           Demote Symbol -> Demote Nat -> Demote Symbol -> Demote Symbol ->
           m (T v)
someEtaInv vid vdim a b =
  withSomeSing vid $ \svid ->
  withSomeSing vdim $ \svdim ->
  withSomeSing a $ \sa ->
  withSomeSing b $ \sb ->
  withKnownNat svdim $
  withKnownSymbol svid $
  withKnownSymbol sa $
  withKnownSymbol sb $
  case sCompare sa sb of
    SLT -> return $ T $ etaInv' svid svdim sa sb
    _   -> throwError $ "cannot construct eta with indices " ++ show vid ++ " " ++ show vdim ++ " " ++ show a ++ " " ++ show b
