-- | Just re-export Unbound and Data.Typeable.Typeable, and GHC.Generics.Generic
module Names (module Unbound.Generics.LocallyNameless,
              GHC.Generics.Generic,
              Data.Typeable.Typeable
             ) where


import Unbound.Generics.LocallyNameless
import GHC.Generics (Generic)
import Data.Typeable (Typeable)
