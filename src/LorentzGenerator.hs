module LorentzGenerator where

import qualified Data.Map.Strict as Map

data Eta = Eta {-# UNPACK #-} !Int {-# UNPACK #-} !Int
            deriving (Eq, Ord, Show)

data Epsilon = Epsilon {-# UNPACK #-} !Int {-# UNPACK #-} !Int
                       {-# UNPACK #-} !Int {-# UNPACK #-} !Int
                 deriving (Eq, Ord, Show)

data Var = Var {-# UNPACK #-} !Int {-# UNPACK #-} !Int
             deriving (Eq, Ord, Show)

data AnsatzEta = Forest (Map.Map Eta AnsatzEta) |
                 Leaf !Var
                   deriving (Eq, Ord, Show)

type AnsatzEpsilon = Map.Map Epsilon AnsatzEta
