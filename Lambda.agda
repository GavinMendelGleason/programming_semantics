

open import Data.Nat renaming (_<_ to _<_nat)
open import Data.List
open import Data.List.Any.Membership
open import Relation.Binary renaming (Decidable to BinaryDecidable)
open import Relation.Binary.PropositionalEquality hiding (Reveal_·_is_ ; [_])
open import Data.Product
open import Relation.Nullary
open import Relation.Unary using (Decidable) renaming (_⊆_ to _⋐_)

module Lambda (Atom : Set) (_≟_atom : BinaryDecidable (_≡_ {A = Atom})) where

{-

We add some names to constructor arguments so that Agda chooses more
readible names when using 'auto'

-}

data Λ : Set where
  -- Vals
  v : (x : Atom) → Λ
  n : (n : ℕ) → Λ
  tt : Λ
  ff : Λ
  ƛ : (x : Atom) → (t : Λ) → Λ -- Agda wont allow λ
  --  Exps
  _⊕_ : (n : Λ) → (m : Λ) → Λ
  _and_ : (b₁ : Λ) → (b₂ : Λ) → Λ
  _or_ : (b₁ : Λ) → (b₂ : Λ) → Λ
  _==_ : (n : Λ) → (m : Λ) → Λ
  _<_ : (n : Λ) → (m : Λ) → Λ
  if_then_else_ : (b : Λ) → (r : Λ) → (s : Λ) → Λ
  give_≔_to_ : Atom → Λ → Λ → Λ -- let_≔_in_ ! (agda wont allow 'let' or 'in')
  _●_ : Λ → Λ → Λ

{-
open import Relation.Binary
  using (Setoid; module Setoid; Preorder; module Preorder)

AtomSetoid : Setoid _ _
AtomSetoid = record
  { Carrier = Atom
  ; _≈_ = _≡_
  ; isEquivalence = record
    { refl = refl
    ; sym = sym
    ; trans = trans
    }
  }
--
open Membership AtomSetoid
-}
open import Data.List.Any as Any using (Any); open Any.Any
open import Data.List.Any.Properties
open Any.Membership-≡
open import Data.List.All
open import Data.Sum
open import Data.Empty
open import Function
open import Relation.Nullary.Decidable
open import Data.List.Properties

Dec[x≢x₁] : ∀ {x x₁ : Atom} → Dec (x ≢ x₁)
Dec[x≢x₁] {x} {x₁} with x ≟ x₁ atom
Dec[x≢x₁] | yes p = no (λ z → z p)
Dec[x≢x₁] | no ¬p = yes ¬p

infix 4 _≈_
_≈_ : List Atom → List Atom → Set _
xs ≈ ys = xs ⊆ ys × ys ⊆ xs

rightIdentity : ∀ {A : Set} (ys : List A) → ys ++ [] ≡ ys
rightIdentity [] = refl
rightIdentity (x ∷ ys) = cong₂ _∷_ refl (rightIdentity ys)

drop∷ : ∀ (x : Atom) xs ys zs →  (x ∷ xs) ++ ys ⊆ zs → xs ++ ys ⊆ zs
drop∷ x xs ys zs P any = P (there any) 

swap∷ : ∀ (x : Atom) xs ys zs → ys ++ x ∷ xs ⊆ zs → x ∷ ys ++ xs ⊆ zs
swap∷ x xs [] ⊆zs ∈x∷xs = ∈x∷xs
swap∷ x xs (x₁ ∷ ys) ⊆zs with swap∷ x xs ys ⊆zs
swap∷ x xs (x₁ ∷ ys) ⊆zs | swap⊆zs = λ ⊆ x₄ → {!!} -- λ x∷∈r → {!swap⊆zs!} -- swap⊆zs ? {!!} {!!} 

++⊆comm : ∀ {xs ys zs : List Atom} → xs ++ ys ⊆ zs → (ys ++ xs) ⊆ zs
++⊆comm {[]} {ys} p rewrite rightIdentity ys = p
++⊆comm {x ∷ xs} {ys} {zs} p with ++⊆comm {xs} {ys} {zs} (drop∷ x xs ys zs p)
++⊆comm {x ∷ xs} p | res = {!res!}

++≈comm : ∀ {xs ys zs} → xs ++ ys ≈ zs → ys ++ xs ≈ zs
++≈comm (proj₁ , proj₂) = {!proj₁!} 

split : ∀ {p} (xs : List Atom) → (P : Atom → Set p) → Decidable P → Σ[ Pxs ∈ List Atom ] Σ[ ¬Pxs ∈ List Atom ] (All P Pxs) × (All (¬_ ∘ P) ¬Pxs) × (Pxs ++ ¬Pxs ≈ xs)
split [] p decp = [] , [] , [] , [] , id , id
split (x ∷ xs) p decp with split xs p decp
split (x ∷ xs) p₁ decp | res with decp x
split (x ∷ xs) p₁ decp | ys , ¬ys , Pys , ¬Pys , xs⊆ys , ys⊆xs | yes p₂ = x ∷ ys , ¬ys , p₂ ∷ Pys , ¬Pys , (λ { (here p) → here p ; (there p) → there (xs⊆ys p) }) , (λ {(here p) → here p ; (there p) → there (ys⊆xs p)})
split (x ∷ xs) p₁ decp | ys , ¬ys , Pys , ¬Pys , xs⊆ys , ys⊆xs | no ¬p = ys , x ∷ ¬ys , Pys , ¬p ∷ ¬Pys , (λ res → {!!}) , (λ res → {!!} ) 

_-_ : List Atom → Atom → List Atom
[] - x = []
(x ∷ l) - x₁ with x ≟ x₁ atom
(x ∷ l) - x₁ | yes p = l - x₁
(x ∷ l) - x₁ | no ¬p = x ∷ (l - x₁)

{- Some extrinsic proofs of properties -} 
x∉[xs-x] : ∀ {xs ys x} → (xs - x) ≡ ys → x ∉ ys
x∉[xs-x] {[]} refl ()
x∉[xs-x] {x ∷ xs} {ys} {x₁} p q with x ≟ x₁ atom
x∉[xs-x] {x ∷ xs} p₁ q | yes p = ⊥-elim $ x∉[xs-x] {xs} p₁ q
x∉[xs-x] {x ∷ xs} p q | no ¬p with x∉[xs-x] {xs} {!!} q
x∉[xs-x] {x ∷ xs} p q | no ¬p | res = {!!}

{-{x₁} p q with x∉[xs-x] {xs} {ys} {x₁}
x∉[xs-x] {xs} {x ∷ ys} {x₁} p q | res with x ≟ x₁ atom
x∉[xs-x] {xs} {x₁ ∷ ys} p₁ q | res | yes p = {!!}
x∉[xs-x] {xs} {x₁ ∷ ys} p q | res | no ¬p = {!!}
-}

fv : Λ → List Atom
fv (v x) = [ x ] -- 
fv (n x) = []
fv tt = []
fv ff = []
fv (ƛ x x₁) = (fv x₁) - x
fv (x ⊕ x₁) = {!(fv x!}
fv (x and x₁) = {!!}
fv (x or x₁) = {!!}
fv (x == x₁) = {!!}
fv (x < x₁) = {!!}
fv (if x then x₁ else x₂) = {!!}
fv (give x ≔ x₁ to x₂) = {!!}
fv (x ● x₁) = {!!}
