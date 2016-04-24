{-# language DeriveDataTypeable, PatternSynonyms, TemplateHaskell #-}
module Language.Common.Label where

import Data.Function (on)
import Data.List (sortBy)

import Names
import Unbound.Generics.LocallyNameless.TH (makeClosedAlpha)

newtype Label = Label String
              deriving (Show, Eq, Ord, Generic)

-- pattern ValueLabel :: Label
pattern ValueLabel :: Label
pattern ValueLabel = Label "$val"

-- pattern TypeLabel :: Label
pattern TypeLabel :: Label
pattern TypeLabel = Label "$type"

-- pattern SignatureLabel :: Label
pattern SignatureLabel :: Label
pattern SignatureLabel = Label "$sig"

makeClosedAlpha ''Label

instance Subst a Label where
  subst _ _ = id
  substs _ = id


------------------------------------------------------------------------------
-- utilities

canonicalizeLabelOrder :: [(Label, a)] -> [(Label, a)]
canonicalizeLabelOrder = sortBy (compare `on` fst)

