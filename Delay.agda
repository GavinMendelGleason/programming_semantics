{-# OPTIONS --copatterns --sized-types #-}

{- This is almost verbatim from J. M. Chapman

https://github.com/jmchapman/Relative-Monads/blob/master/Delay.agda
-}

module Delay where

open import Size
open import Category.Monad
open import Level renaming (zero to lzero; suc to lsuc)
open import Relation.Binary public
import Relation.Binary.PreorderReasoning
module Pre = Relation.Binary.PreorderReasoning
open import Data.Product

mutual

  data Delay (A : Set) (i : Size) : Set where
    now   : A → Delay A i
    later : ∞Delay A i → Delay A i

  record ∞Delay (A : Set) (i : Size) : Set where
    coinductive
    constructor delay
    field
      force : {j : Size< i} → Delay A j

open ∞Delay public

-- Smart constructor.

later! : ∀ {A i} → Delay A i → Delay A (↑ i)
later! x = later (delay x)

module Bind where
  mutual
    _>>=_ : ∀ {i A B} → Delay A i → (A → Delay B i) → Delay B i
    now   x >>= f = f x
    later x >>= f = later (x ∞>>= f)

    _∞>>=_ :  ∀ {i A B} → ∞Delay A i → (A → Delay B i) → ∞Delay B i
    force (x ∞>>= f) = force x >>= f

delayMonad : ∀ {i} → RawMonad {f = lzero} (λ A → Delay A i)
delayMonad {i} = record
  { return = now
  ; _>>=_  = _>>=_ {i}
  } where open Bind

module _ {i : Size} where
  open module DelayMonad = RawMonad (delayMonad {i = i}) 
                           public renaming (_⊛_ to _<*>_)
open Bind public using (_∞>>=_)

_∞<$>_ : ∀ {i A B} (f : A → B) (∞a : ∞Delay A i) → ∞Delay B i
f ∞<$> ∞a = ∞a ∞>>= λ a → return (f a)

