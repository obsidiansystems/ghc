{-# OPTIONS_GHC -XDeriveDataTypeable -XStandaloneDeriving #-}

-- Test #2394

module Foo where

import Data.Data(Data)

deriving instance (Data a,Data b) => Data (a->b)
