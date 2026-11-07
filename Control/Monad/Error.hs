{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableInstances #-}
module Control.Monad.Error (
    Error(..),
    MonadError(..),
    ErrorT(..),
    runErrorT,
    mapErrorT,
    withErrorT,
    module Control.Monad
) where

import Control.Monad
import Control.Monad.Except (MonadError(..), ExceptT(..), runExceptT, mapExceptT, withExceptT)

class Error a where
    noMsg  :: a
    strMsg :: String -> a
    noMsg    = strMsg ""
    strMsg _ = noMsg

instance Error String where
    noMsg    = ""
    strMsg s = s

type ErrorT = ExceptT

runErrorT :: ExceptT e m a -> m (Either e a)
runErrorT = runExceptT

mapErrorT :: (m (Either e a) -> n (Either e' b)) -> ExceptT e m a -> ExceptT e' n b
mapErrorT = mapExceptT

withErrorT :: Functor m => (e -> e') -> ExceptT e m a -> ExceptT e' m a
withErrorT = withExceptT
