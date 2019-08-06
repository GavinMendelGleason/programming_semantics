
module OperationalSemantics where

open import Data.Nat

data Exp : Set where
  num : ℕ → Exp
  _⊕_ : Exp → Exp → Exp

-- Big step operational semantics

infix 10 _⇓_ 
data _⇓_ : Exp → ℕ → Set where
  n⇓n : ∀ {n} →

      -------------
      num n ⇓ n
      
  E⊕E : ∀ {E₁ E₂ n₁ n₂} →
  
      E₁ ⇓ n₁  →  E₂ ⇓ n₂ →
      ----------------------------
        E₁ ⊕ E₂ ⇓ (n₁ + n₂)
  

-- Need for Σ which gives us specifications / existentials.
open import Data.Product

-- Σ[ n ∈ ℕ ] P
-- We can read this as: There exists an n in ℕ such that P
---
-- It is a type of pairs, which has a witness (of type ℕ in this case) and a proof
-- that P holds of that witness.
--
evalBig : ∀ E → Σ[ n ∈ ℕ ] E ⇓ n
evalBig (num x) = x , n⇓n
evalBig (e ⊕ e₁) with evalBig e | evalBig e₁
evalBig (e ⊕ e₁) | n , proof_n | m , proof_m = n + m , E⊕E proof_n proof_m

example⇓ : num 3 ⊕ (num 2 ⊕ num 1) ⇓ 6
example⇓ = proj₂ (evalBig (num 3 ⊕ (num 2 ⊕ num 1)))

-- Small step operational semantics
infix 8 _⟶_
data _⟶_ : Exp → Exp → Set where
  +⟶ : ∀ {n m} →
  
          -----------------------------
          num n ⊕ num m ⟶ num (n + m)

  ⊕₁⟶ : ∀ {E₁ E₁' E₂} →

          E₁ ⟶ E₁' → 
          ---------------------
          E₁ ⊕ E₂ ⟶ E₁' ⊕ E₂

  ⊕₂⟶ : ∀ {n E₂ E₂'} →

          E₂ ⟶ E₂' →  
          --------------------------
          num n ⊕ E₂ ⟶ num n ⊕ E₂'

example⟶₁ : (num 3 ⊕ num 7) ⊕ (num 8 ⊕ num 1) ⟶ num 10 ⊕ (num 8 ⊕ num 1)
example⟶₁ = ⊕₁⟶ +⟶ 
example⟶₂ : (num 10) ⊕ (num 8 ⊕ num 1) ⟶ num 10 ⊕ num 9
example⟶₂ = ⊕₂⟶ +⟶

infix 8 _⟶ch_
data _⟶ch_ : Exp → Exp → Set where
  +⟶ch : ∀ {n m} →
  
          -------------------------------
          num n ⊕ num m ⟶ch num (n + m)

  ⊕₁⟶ch : ∀ {E₁ E₁' E₂} →

          E₁ ⟶ch E₁' → 
          ----------------------
          E₁ ⊕ E₂ ⟶ch E₁' ⊕ E₂

  ⊕₂⟶ch : ∀ {E₁ E₂ E₂'} →

          E₂ ⟶ch E₂' →  
          ----------------------
          E₁ ⊕ E₂ ⟶ch E₁ ⊕ E₂'


example⟶ch₁ : (num 3 ⊕ num 7) ⊕ (num 8 ⊕ num 1) ⟶ch num 10 ⊕ (num 8 ⊕ num 1)
example⟶ch₁ = ⊕₁⟶ch +⟶ch
example⟶ch₂ : (num 10) ⊕ (num 8 ⊕ num 1) ⟶ch num 10 ⊕ num 9
example⟶ch₂ = ⊕₂⟶ch +⟶ch

⟶⇒⟶ch : ∀ {E₁ E₂} → (E₁ ⟶ E₂) → (E₁ ⟶ch E₂)
⟶⇒⟶ch +⟶ = +⟶ch
⟶⇒⟶ch (⊕₁⟶ d) = ⊕₁⟶ch (⟶⇒⟶ch d)
⟶⇒⟶ch (⊕₂⟶ d) = ⊕₂⟶ch (⟶⇒⟶ch d)

{- Not a theorem! (proof below)

⟶ch⇒⟶ : ∀ {E₁ E₂} → (E₁ ⟶ch E₂) → (E₁ ⟶ E₂)
⟶ch⇒⟶ +⟶ch = +⟶
⟶ch⇒⟶ (⊕₁⟶ch d) = ⊕₁⟶ (⟶ch⇒⟶ d)
⟶ch⇒⟶ (⊕₂⟶ch d) = {!!} {-  E₂ ⟶ E₂'                  No applicable rule
                                 ———————————————————             
                                 (E₁ ⊕ E₂) ⟶ (E₁ ⊕ E₂')  -}
-}

-- Bring in Agda's notion of negation (a map to a datatype of no constructors)
open import Data.Empty
open import Relation.Nullary

-- We can prove it is not a theorem by exhibiting a counter-example using the case above.
-- i.e. choose to reduce the second antecedent first.
¬⟶ch⇒⟶ : ¬ (∀ E₁ E₂ → (E₁ ⟶ch E₂) → (E₁ ⟶ E₂))
¬⟶ch⇒⟶ f with f ((num 0 ⊕ num 0) ⊕ (num 0 ⊕ num 0)) ((num 0 ⊕ num 0) ⊕ num 0) (⊕₂⟶ch +⟶ch)
¬⟶ch⇒⟶ f | ()

data _⟶_⟨_⟩ : Exp → Exp → ℕ → Set where
  z⟶ : ∀ {E₁} →
  
       --------------
       E₁ ⟶ E₁ ⟨ 0 ⟩
                 
  sn⟶ : ∀ {E₁ E₂ E₃ n} →

        E₁ ⟶ E₂ →  E₂ ⟶ E₃ ⟨ n ⟩ →  
        ----------------------------
             E₁ ⟶ E₃ ⟨ 1 + n ⟩ 


data _⟶⋆_ : Exp → Exp → Set where
  k⟶⋆ : ∀ {E₁ E₂} →

        Σ[ k ∈ ℕ ] E₁ ⟶ E₂ ⟨ k ⟩ →
        --------------------------
               E₁ ⟶⋆ E₂ 

data _⟶ch_⟨_⟩ : Exp → Exp → ℕ → Set where
  z⟶ch : ∀ {E₁} →
  
       --------------
       E₁ ⟶ch E₁ ⟨ 0 ⟩
                 
  sn⟶ch : ∀ {E₁ E₂ E₃ n} →

        E₁ ⟶ch E₂ →  E₂ ⟶ch E₃ ⟨ n ⟩ →  
        ----------------------------
             E₁ ⟶ch E₃ ⟨ 1 + n ⟩ 

data _⟶ch⋆_ : Exp → Exp → Set where
  k⟶ch⋆ : ∀ {E₁ E₂} →

        Σ[ k ∈ ℕ ] E₁ ⟶ch E₂ ⟨ k ⟩ →
        --------------------------
               E₁ ⟶ch⋆ E₂ 


