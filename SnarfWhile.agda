
open import Relation.Binary -- .PropositionalEquality
open import Relation.Binary.PropositionalEquality 
open import Relation.Nullary
open import Data.Sum


module SnarfWhile (Atom : Set) (_≟_atom : Decidable (_≡_ {A = Atom})) where

open import Data.Nat
open import Data.Maybe
open import Data.Bool renaming (_∨_ to _∥_ ; _∧_ to _&&_ ; not to neg ; if_then_else_ to [_⇒_,_] )

Locs : Set
Locs = Atom

data Arith : Set where
  L : Locs → Arith
  N : ℕ → Arith
  _⊕_ : Arith → Arith → Arith
  
data Boolean : Set where
  tt : Boolean
  ff : Boolean
  _==_ : Arith → Arith → Boolean
  _∨_ : Boolean → Boolean → Boolean
  _∧_ : Boolean → Boolean → Boolean
  not : Boolean → Boolean
  
data Com : Set where
  _≔_ : Locs → Arith → Com
  if_then_else_ : Boolean → Com → Com → Com
  _,_ : Com → Com → Com
  skip : Com
  while_do_ : Boolean → Com → Com

State : Set
State = Locs → ℕ

{-

Either we have to add errors and a map to Maybe ℕ or we have to return some value
to avoid getting stuck (in the progress theorem below). 

-}
empty : State
empty _ = 42

_[_↦_] : State → Locs → ℕ → State
(f [ l ↦ n ]) x with l ≟ x atom
(f [ l ↦ n ]) x | yes p = n
(f [ l ↦ n ]) x | no ¬p = f x
  

data ⟨_,_⟩⇓_arith : Arith → State → ℕ → Set where

  B-num : ∀ {n s} → 

        --------------------------
        ⟨ N n , s ⟩⇓ n arith

  B-add : ∀ {E₁ E₂ s n₁ n₂} → 

        ⟨ E₁ , s ⟩⇓ n₁ arith →  ⟨ E₂ , s ⟩⇓ n₂ arith → 
        ------------------------------------------------
            ⟨ E₁ ⊕ E₂ , s ⟩⇓ (n₁ + n₂) arith

  B-loc : ∀ {l s n} → 

             s l ≡ n → 
        -----------------------
        ⟨ (L l) , s ⟩⇓ n arith

data ⟨_,_⟩⇓_bool : Boolean → State → Bool → Set where

  B-tt : ∀ {s} →
  
           -----------------------
           ⟨ tt , s ⟩⇓ true bool


  B-false : ∀ {s} → 
  
           -------------------------
           ⟨ ff , s ⟩⇓ false bool

  {- No shortcut evaluation available - simplifies rules, but slows execution.  We can fix this with more rules. -}
  B-∧ : ∀ {B₁ B₂ b₁ b₂ s} → 

           ⟨ B₁ , s ⟩⇓ b₁ bool → ⟨ B₂ , s ⟩⇓ b₂ bool →   
           --------<------------------------------------
               ⟨ B₁ ∧ B₂ , s ⟩⇓ b₁ && b₂ bool

  B-∨ : ∀ {B₁ B₂ b₁ b₂ s} → 

           ⟨ B₁ , s ⟩⇓ b₁ bool → ⟨ B₂ , s ⟩⇓ b₂ bool → 
           -------------------------------------------
                    ⟨ B₁ ∨ B₂ , s ⟩⇓ b₁ ∥ b₂ bool

  B-== : ∀ {E₁ E₂ s n} →

        ⟨ E₁ , s ⟩⇓ n arith → ⟨ E₂ , s ⟩⇓ n arith → 
        --------------------------------------------------
                 ⟨ E₁ == E₂ , s ⟩⇓ true bool 

  B-not : ∀ {B b s} →

          ⟨ B , s ⟩⇓ b bool → 
        -------------------
        ⟨ not B , s ⟩⇓ neg b bool


data ⟨_,_⟩⇓_com : Com → State → State → Set where

  B-assign : ∀ {E l s n} → 

           ⟨ E , s ⟩⇓ n arith → 
         -----------------------------
         ⟨ l ≔ E , s ⟩⇓ s [ l ↦ n ] com

  B-seq : ∀ {C₁ C₂ s₁ s₂ s₃} →

         ⟨ C₁ , s₁ ⟩⇓ s₂ com → ⟨ C₂ , s₂ ⟩⇓ s₃ com → 
         -----------------------------------------
                ⟨ (C₁ , C₂) , s₁ ⟩⇓ s₃ com
  
  B-if-tt : ∀ {B C₁ C₂ s s'} → 

         ⟨ B , s ⟩⇓ true bool → ⟨ C₁ , s ⟩⇓ s' com → 
         -----------------------------------------
            ⟨ if B then C₁ else C₂ , s ⟩⇓ s' com

  B-if-false : ∀ {B C₁ C₂ s s'} → 

         ⟨ B , s ⟩⇓ false bool → ⟨ C₂ , s ⟩⇓ s' com → 
         -----------------------------------------
            ⟨ if B then C₁ else C₂ , s ⟩⇓ s' com

  B-while-false : ∀ {B C s} → 

            ⟨ B , s ⟩⇓ false bool →
          ---------------------------
          ⟨ while B do C , s ⟩⇓ s com

  B-while-tt : ∀ {B C s₁ s₂ s₃} → 

         ⟨ B , s₁ ⟩⇓ true bool →
         ⟨ C , s₁ ⟩⇓ s₂ com → 
         ⟨ while B do C , s₂ ⟩⇓ s₃ com → 
         -----------------------------
         ⟨ while B do C , s₁ ⟩⇓ s₃ com

  B-skip : ∀ {s} →

         -------------------
         ⟨ skip , s ⟩⇓ s com

⇓-deterministic-arith : ∀ {C s n₁ n₂} → ⟨ C , s ⟩⇓ n₁ arith → ⟨ C , s ⟩⇓ n₂ arith → n₁ ≡ n₂
⇓-deterministic-arith B-num B-num = refl
⇓-deterministic-arith (B-add p p₁) (B-add q q₁) with ⇓-deterministic-arith p q | ⇓-deterministic-arith p₁ q₁
⇓-deterministic-arith (B-add p p₁) (B-add q q₁) | P | Q rewrite P | Q = refl
⇓-deterministic-arith (B-loc x) (B-loc x₁) = aux x x₁
  where aux : ∀ {n m o : ℕ} → o ≡ n → o ≡ m → n ≡ m
        aux refl refl = refl


⇓-deterministic-bool : ∀ {B s b₁ b₂} → ⟨ B , s ⟩⇓ b₁ bool → ⟨ B , s ⟩⇓ b₂ bool → b₁ ≡ b₂
⇓-deterministic-bool = {!!}
{-
⇓-deterministic-bool B-true B-true = refl
⇓-deterministic-bool B-false B-false = refl
⇓-deterministic-bool (B-∧true p p₁) (B-∧true q q₁) = refl
⇓-deterministic-bool (B-∧true p p₁) (B-∧false₁ q) = ⇓-deterministic-bool p q
⇓-deterministic-bool (B-∧true p p₁) (B-∧false₂ q) = ⇓-deterministic-bool p₁ q
⇓-deterministic-bool (B-∧false₁ p) (B-∧true q q₁) = ⇓-deterministic-bool p q
⇓-deterministic-bool (B-∧false₁ p) (B-∧false₁ q) = refl
⇓-deterministic-bool (B-∧false₁ p) (B-∧false₂ q) = refl
⇓-deterministic-bool (B-∧false₂ p) (B-∧true q q₁) = ⇓-deterministic-bool p q₁
⇓-deterministic-bool (B-∧false₂ p) (B-∧false₁ q) = refl
⇓-deterministic-bool (B-∧false₂ p) (B-∧false₂ q) = refl
⇓-deterministic-bool (B-∨true₁ p) (B-∨true₁ q) = refl
⇓-deterministic-bool (B-∨true₁ p) (B-∨true₂ q) = refl
⇓-deterministic-bool (B-∨true₁ p) (B-∨false q q₁) = ⇓-deterministic-bool p q
⇓-deterministic-bool (B-∨true₂ p) (B-∨true₁ q) = refl
⇓-deterministic-bool (B-∨true₂ p) (B-∨true₂ q) = refl
⇓-deterministic-bool (B-∨true₂ p) (B-∨false q q₁) = ⇓-deterministic-bool p q₁
⇓-deterministic-bool (B-∨false p p₁) (B-∨true₁ q) = ⇓-deterministic-bool p q
⇓-deterministic-bool (B-∨false p p₁) (B-∨true₂ q) = ⇓-deterministic-bool p₁ q
⇓-deterministic-bool (B-∨false p p₁) (B-∨false q q₁) = refl
⇓-deterministic-bool (B-== x x₁) (B-== x₂ x₃) = refl
⇓-deterministic-bool (B-not-true p) (B-not-true q) = refl
⇓-deterministic-bool (B-not-false p) (B-not-false q) = refl 
⇓-deterministic-bool (B-not-true p) (B-not-false q) = ⇓-deterministic-bool q p
⇓-deterministic-bool (B-not-false p) (B-not-true q) = ⇓-deterministic-bool q p 
-}

{-
⇓-deterministic : ∀ {C s s₁ s₂} → ⟨ C , s ⟩⇓ s₂ com → ⟨ C , s ⟩⇓ s₁ com → s₁ ≡ s₂
⇓-deterministic (B-assign x) (B-assign x₁) with ⇓-deterministic-arith x x₁
⇓-deterministic (B-assign x) (B-assign x₁) | refl = refl 
⇓-deterministic (B-seq p p₁) (B-seq q q₁) with ⇓-deterministic p q
⇓-deterministic (B-seq p p₁) (B-seq q q₁) | refl with ⇓-deterministic p₁ q₁
⇓-deterministic (B-seq p p₁) (B-seq q q₁) | refl | refl = refl
⇓-deterministic (B-if-true x p) (B-if-true x₁ q) with ⇓-deterministic p q
⇓-deterministic (B-if-true x p) (B-if-true x₁ q) | refl = refl
⇓-deterministic (B-if-true x p) (B-if-false x₁ q) with ⇓-deterministic-bool x x₁
⇓-deterministic (B-if-true x p) (B-if-false x₁ q) | ()
⇓-deterministic (B-if-false x p) (B-if-true x₁ q) with ⇓-deterministic-bool x x₁
⇓-deterministic (B-if-false x p) (B-if-true x₁ q) | () 
⇓-deterministic (B-if-false x p) (B-if-false x₁ q) = ⇓-deterministic p q
⇓-deterministic (B-while-false x) (B-while-false x₁) = refl
⇓-deterministic (B-while-false x) (B-while-true x₁ q q₁) with ⇓-deterministic-bool x x₁
⇓-deterministic (B-while-false x) (B-while-true x₁ q q₁) | ()
⇓-deterministic (B-while-true x p p₁) (B-while-false x₁) with ⇓-deterministic-bool x x₁
⇓-deterministic (B-while-true x p p₁) (B-while-false x₁) | ()
⇓-deterministic (B-while-true x p p₁) (B-while-true x₁ q q₁) with ⇓-deterministic p q
⇓-deterministic (B-while-true x p p₁) (B-while-true x₁ q q₁) | refl = ⇓-deterministic p₁ q₁
⇓-deterministic B-skip B-skip = refl
-}

open import Data.Product

data ⟨_,_⟩⟶⟨_,_⟩ : Com → State → Com → State → Set where 

  S-assign : ∀ {E s n l} → 

                  ⟨ E , s ⟩⇓ n arith → 
           -----------------------------------
           ⟨ l ≔ E , s ⟩⟶⟨ skip , s [ l ↦ n ] ⟩ 

  S-cond-true : ∀ {B C₁ C₂ s} →

           ⟨ B , s ⟩⇓ true bool → 
           ----------------------------------------
           ⟨ if B then C₁ else C₂ , s ⟩⟶⟨ C₁ , s ⟩

  S-cond-false : ∀ {B C₁ C₂ s} →

           ⟨ B , s ⟩⇓ false bool → 
           ----------------------------------------
           ⟨ if B then C₁ else C₂ , s ⟩⟶⟨ C₂ , s ⟩

  S-seq-left : ∀ {C₁ C₁' C₂ s s'} →

                  ⟨ C₁ , s ⟩⟶⟨ C₁' , s' ⟩ → 
           ----------------------------------------
           ⟨ (C₁ , C₂) , s ⟩⟶⟨ (C₁' , C₂) , s' ⟩

  S-seq-right : ∀ {C₂ s} →

           ----------------------------------------
           ⟨ (skip , C₂) , s ⟩⟶⟨  C₂ , s ⟩


  S-whilte-true : ∀ {B C s} →

                     ⟨ B , s ⟩⇓ true bool →
           ----------------------------------------
           ⟨ while B do C , s ⟩⟶⟨ (C , while B do C) , s ⟩

  S-whilte-false : ∀ {B C s} →

                     ⟨ B , s ⟩⇓ false bool →
           ----------------------------------------
           ⟨ while B do C , s ⟩⟶⟨ skip , s ⟩


evalBoolean : ∀ B s → Σ[ b ∈ Bool ] ⟨ B , s ⟩⇓ b bool
evalBoolean tt s = true , B-tt
evalBoolean ff s = false , B-false
evalBoolean (x == x₁) s = {!!}
evalBoolean (B ∨ B₁) s with evalBoolean B s
evalBoolean (B ∨ B₁) s | false , P with evalBoolean B₁ s
evalBoolean (B ∨ B₁) s | false , P | false , Q = false , B-∨ P Q
evalBoolean (B ∨ B₁) s | false , P | true , Q = true , B-∨ P Q
evalBoolean (B ∨ B₁) s | true , proj₂ = true , {!!} 
evalBoolean (B ∧ B₁) s = {!!}
evalBoolean (not B) s = {!!}

data Terminal : Com → Set where
  skip-stop : Terminal skip

progress : ∀ C s → Terminal C ⊎ Σ[ C' ∈ Com ] Σ[ s' ∈ State ] ⟨ C , s ⟩⟶⟨ C' , s' ⟩
progress (x ≔ x₁) s with {!!} 
progress (x ≔ x₁) s | res = inj₂ (skip , ((s [ x ↦ res ]) , (S-assign {!!}))) -- inj₂ ({!!} , {!!})
progress (if x then C else C₁) s = {!!}
progress (C , C₁) s = {!!}
progress skip s = inj₁ skip-stop
progress (while x do C) s = {!!}
