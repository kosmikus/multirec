{-# LANGUAGE EmptyDataDecls #-}

module Void where

data Void

refute :: Void -> a
refute void = void `seq` undefined