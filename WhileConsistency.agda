
open import Relation.Binary -- .PropositionalEquality
open import Relation.Binary.PropositionalEquality 
open import Relation.Nullary
open import Data.Sum
open import Data.Empty
open import Function
open import Data.Product
open import Data.Nat

module WhileConsistency (Atom : Set) (_≟_atom : Decidable (_≡_ {A = Atom})) where

import While
module WhileAtom = While Atom _≟_atom
open WhileAtom 

{-

Proof that:

⟨ C, s ⟩⟶⋆⟨ skip ,s' ⟩ → ⟨ C , s ⟩ ⇓ s'

-}
⟨C,s⟩⟶⟨C',s'⟩⇒⟨C',s'⟩⇓s''⇒⟨C,s⟩⇓s'' : ∀ {C C' s s' s''} → ⟨ C , s ⟩⟶⟨ C' , s' ⟩ → ⟨ C' , s' ⟩⇓ s'' com → ⟨ C , s ⟩⇓ s'' com
⟨C,s⟩⟶⟨C',s'⟩⇒⟨C',s'⟩⇓s''⇒⟨C,s⟩⇓s'' (While.S-assign x) While.B-skip = B-assign x
⟨C,s⟩⟶⟨C',s'⟩⇒⟨C',s'⟩⇓s''⇒⟨C,s⟩⇓s'' (While.S-cond-true x) (While.B-assign x₁) = B-if-true x (B-assign x₁)
⟨C,s⟩⟶⟨C',s'⟩⇒⟨C',s'⟩⇓s''⇒⟨C,s⟩⇓s'' (While.S-cond-true x) (While.B-seq Q Q₁) = B-if-true x (B-seq Q Q₁)
⟨C,s⟩⟶⟨C',s'⟩⇒⟨C',s'⟩⇓s''⇒⟨C,s⟩⇓s'' (While.S-cond-true x) (While.B-if-true x₁ Q) = B-if-true x (B-if-true x₁ Q)
⟨C,s⟩⟶⟨C',s'⟩⇒⟨C',s'⟩⇓s''⇒⟨C,s⟩⇓s'' (While.S-cond-true x) (While.B-if-false x₁ Q) = B-if-true x (B-if-false x₁ Q)
⟨C,s⟩⟶⟨C',s'⟩⇒⟨C',s'⟩⇓s''⇒⟨C,s⟩⇓s'' (While.S-cond-true x) (While.B-while-false x₁) = B-if-true x (B-while-false x₁)
⟨C,s⟩⟶⟨C',s'⟩⇒⟨C',s'⟩⇓s''⇒⟨C,s⟩⇓s'' (While.S-cond-true x) (While.B-while-true x₁ Q Q₁) = B-if-true x (B-while-true x₁ Q Q₁)
⟨C,s⟩⟶⟨C',s'⟩⇒⟨C',s'⟩⇓s''⇒⟨C,s⟩⇓s'' (While.S-cond-true x) While.B-skip = B-if-true x B-skip
⟨C,s⟩⟶⟨C',s'⟩⇒⟨C',s'⟩⇓s''⇒⟨C,s⟩⇓s'' (While.S-cond-false x) (While.B-assign x₁) = B-if-false x (B-assign x₁)
⟨C,s⟩⟶⟨C',s'⟩⇒⟨C',s'⟩⇓s''⇒⟨C,s⟩⇓s'' (While.S-cond-false x) (While.B-seq Q Q₁) = B-if-false x (B-seq Q Q₁)
⟨C,s⟩⟶⟨C',s'⟩⇒⟨C',s'⟩⇓s''⇒⟨C,s⟩⇓s'' (While.S-cond-false x) (While.B-if-true x₁ Q) = B-if-false x (B-if-true x₁ Q)
⟨C,s⟩⟶⟨C',s'⟩⇒⟨C',s'⟩⇓s''⇒⟨C,s⟩⇓s'' (While.S-cond-false x) (While.B-if-false x₁ Q) = B-if-false x (B-if-false x₁ Q)
⟨C,s⟩⟶⟨C',s'⟩⇒⟨C',s'⟩⇓s''⇒⟨C,s⟩⇓s'' (While.S-cond-false x) (While.B-while-false x₁) = B-if-false x (B-while-false x₁)
⟨C,s⟩⟶⟨C',s'⟩⇒⟨C',s'⟩⇓s''⇒⟨C,s⟩⇓s'' (While.S-cond-false x) (While.B-while-true x₁ Q Q₁) = B-if-false x (B-while-true x₁ Q Q₁)
⟨C,s⟩⟶⟨C',s'⟩⇒⟨C',s'⟩⇓s''⇒⟨C,s⟩⇓s'' (While.S-cond-false x) While.B-skip = B-if-false x B-skip
⟨C,s⟩⟶⟨C',s'⟩⇒⟨C',s'⟩⇓s''⇒⟨C,s⟩⇓s'' (While.S-seq-left P) (While.B-seq Q Q₁) = B-seq (⟨C,s⟩⟶⟨C',s'⟩⇒⟨C',s'⟩⇓s''⇒⟨C,s⟩⇓s'' P Q) Q₁
⟨C,s⟩⟶⟨C',s'⟩⇒⟨C',s'⟩⇓s''⇒⟨C,s⟩⇓s'' While.S-seq-right (While.B-assign x) = B-seq B-skip (B-assign x)
⟨C,s⟩⟶⟨C',s'⟩⇒⟨C',s'⟩⇓s''⇒⟨C,s⟩⇓s'' While.S-seq-right (While.B-seq Q Q₁) = B-seq B-skip (B-seq Q Q₁)
⟨C,s⟩⟶⟨C',s'⟩⇒⟨C',s'⟩⇓s''⇒⟨C,s⟩⇓s'' While.S-seq-right (While.B-if-true x Q) = B-seq B-skip (B-if-true x Q)
⟨C,s⟩⟶⟨C',s'⟩⇒⟨C',s'⟩⇓s''⇒⟨C,s⟩⇓s'' While.S-seq-right (While.B-if-false x Q) = B-seq B-skip (B-if-false x Q)
⟨C,s⟩⟶⟨C',s'⟩⇒⟨C',s'⟩⇓s''⇒⟨C,s⟩⇓s'' While.S-seq-right (While.B-while-false x) = B-seq B-skip (B-while-false x)
⟨C,s⟩⟶⟨C',s'⟩⇒⟨C',s'⟩⇓s''⇒⟨C,s⟩⇓s'' While.S-seq-right (While.B-while-true x Q Q₁) = B-seq B-skip (B-while-true x Q Q₁)
⟨C,s⟩⟶⟨C',s'⟩⇒⟨C',s'⟩⇓s''⇒⟨C,s⟩⇓s'' While.S-seq-right While.B-skip = B-seq B-skip B-skip
⟨C,s⟩⟶⟨C',s'⟩⇒⟨C',s'⟩⇓s''⇒⟨C,s⟩⇓s'' (While.S-whilte-true x) (While.B-seq Q Q₁) = B-while-true x Q Q₁
⟨C,s⟩⟶⟨C',s'⟩⇒⟨C',s'⟩⇓s''⇒⟨C,s⟩⇓s'' (While.S-whilte-false x) While.B-skip = B-while-false x

⟨C,s⟩⟶⟨k⟩⟨skip,s'⟩⇒⟨C,s⟩⇓s' : ∀ {C s s' k} → ⟨ C , s ⟩⟶⟨ k ⟩⟨ skip , s' ⟩ → ⟨ C , s ⟩⇓ s' com
⟨C,s⟩⟶⟨k⟩⟨skip,s'⟩⇒⟨C,s⟩⇓s' While.⟨⟩⟶⟨⟩z = B-skip
⟨C,s⟩⟶⟨k⟩⟨skip,s'⟩⇒⟨C,s⟩⇓s' (While.⟨⟩⟶⟨⟩s x P) with ⟨C,s⟩⟶⟨k⟩⟨skip,s'⟩⇒⟨C,s⟩⇓s' P
⟨C,s⟩⟶⟨k⟩⟨skip,s'⟩⇒⟨C,s⟩⇓s' (While.⟨⟩⟶⟨⟩s x P) | O = ⟨C,s⟩⟶⟨C',s'⟩⇒⟨C',s'⟩⇓s''⇒⟨C,s⟩⇓s'' x O 

⟨C,s⟩⟶⋆⟨skip,s'⟩⇒⟨C,s⟩⇓s' : ∀ {C s s'} → ⟨ C , s ⟩⟶⋆⟨ skip , s' ⟩ → ⟨ C , s ⟩⇓ s' com
⟨C,s⟩⟶⋆⟨skip,s'⟩⇒⟨C,s⟩⇓s' (While.⟨⟩⟶⋆⟨⟩ (_ , P)) = ⟨C,s⟩⟶⟨k⟩⟨skip,s'⟩⇒⟨C,s⟩⇓s' P

{-

Proof that:

⟨ C , s ⟩ ⇓ s' → ⟨ C, s ⟩⟶⋆⟨ skip ,s' ⟩

-}

-- Ugh, this is going to require several context lemmata
--⟨C₁,s⟩⟶⋆⟨skip,s₂⟩


⟨C,s⟩⇓s'⇒⟨C,s⟩⟶⋆⟨skip,s'⟩ : ∀ {C s s'} → ⟨ C , s ⟩⇓ s' com → ⟨ C , s ⟩⟶⋆⟨ skip , s' ⟩
⟨C,s⟩⇓s'⇒⟨C,s⟩⟶⋆⟨skip,s'⟩ (While.B-assign x) = ⟨⟩⟶⋆⟨⟩ (1 , ⟨⟩⟶⟨⟩s (S-assign x) ⟨⟩⟶⟨⟩z)
⟨C,s⟩⇓s'⇒⟨C,s⟩⟶⋆⟨skip,s'⟩ (While.B-seq P P₁) with ⟨C,s⟩⇓s'⇒⟨C,s⟩⟶⋆⟨skip,s'⟩ P
⟨C,s⟩⇓s'⇒⟨C,s⟩⟶⋆⟨skip,s'⟩ (While.B-seq P P₁) | res = {!!}
⟨C,s⟩⇓s'⇒⟨C,s⟩⟶⋆⟨skip,s'⟩ (While.B-if-true x P) = {!!}
⟨C,s⟩⇓s'⇒⟨C,s⟩⟶⋆⟨skip,s'⟩ (While.B-if-false x P) = {!!}
⟨C,s⟩⇓s'⇒⟨C,s⟩⟶⋆⟨skip,s'⟩ (While.B-while-false x) = {!!}
⟨C,s⟩⇓s'⇒⟨C,s⟩⟶⋆⟨skip,s'⟩ (While.B-while-true x P P₁) = {!!}
⟨C,s⟩⇓s'⇒⟨C,s⟩⟶⋆⟨skip,s'⟩ While.B-skip = ⟨⟩⟶⋆⟨⟩ (zero , ⟨⟩⟶⟨⟩z) 
