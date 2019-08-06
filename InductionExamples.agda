module InductionExamples where

data ℕ : Set where
  z : ℕ
  s : ℕ → ℕ

_+_ : ℕ → ℕ → ℕ 
z + m = m
(s n) + m = s (n + m)  

_*_ : ℕ → ℕ → ℕ
z * m = z
(s n) * m = m + (n * m)

sum : ℕ → ℕ
sum z = z
sum (s n) = (s n) + sum n

fac : ℕ → ℕ
fac z = s z
fac (s n) = (fac n) * (s n)

ℕInduction : ∀ (P : ℕ → Set) → P z → (∀ n → P n → P (s n)) → (n : ℕ) → P n
ℕInduction P pz pn z = pz
ℕInduction P pz pn (s m) = pn m (ℕInduction P pz pn m)

open import Relation.Binary.PropositionalEquality

{-

A couple of easy examples of nat induction 

(cong)ruence gives us that x ≡ y → f x ≡ f y

Its definition in the standard libarary is:

cong : ∀ {a b} {A : Set a} {B : Set b}
       (f : A → B) {x y} → x ≡ y → f x ≡ f y
cong f refl = refl

-} 

n+0≡n : ∀ n → (n + z) ≡ n 
n+0≡n = ℕInduction (λ n → (n + z) ≡ n) refl (λ n p → cong s p) 

n+1+m≡1+n+m : ∀ n m → n + (s m) ≡ s (n + m)
n+1+m≡1+n+m n m = ℕInduction (λ n → (n + s m) ≡ s (n + m)) refl (λ _ → cong s) n

{-

rewrite is synactic sugar for an induction principle over _≡_.

These proofs get a lot messier with out the sugar.

-}
+-assoc : ∀ n m o → (n + m) + o ≡ n + (m + o)
+-assoc n m o = ℕInduction (λ m → (n + m) + o ≡ n + (m + o)) zP sP m
  where zP : ((n + z) + o) ≡ (n + o)
        zP rewrite (n+0≡n n) = refl
        sP : (n₁ : ℕ) → ((n + n₁) + o) ≡ (n + (n₁ + o)) →
                 ((n + s n₁) + o) ≡ (n + s (n₁ + o))
        sP n₁ p rewrite n+1+m≡1+n+m n n₁ | n+1+m≡1+n+m n (n₁ + o) = cong s p 

+-comm : ∀ n m → n + m ≡ m + n
+-comm n = ℕInduction (λ m' → (n + m') ≡ (m' + n)) (n+0≡n n) sP
  where sP : (n₁ : ℕ) → (n + n₁) ≡ (n₁ + n) → (n + s n₁) ≡ s (n₁ + n)
        sP n₁ p rewrite (n+1+m≡1+n+m n n₁) = cong s p

{-

The following are needed for the example: sum n = n + (n + 1) / 2

We avoid division by writing: 2 * (sum n) = n + (n + 1)

-}
n*1≡n : ∀ n → (n * s z) ≡ n
n*1≡n = ℕInduction (λ n → (n * s z) ≡ n) refl (λ n p → cong s p) 

n*0≡0 : ∀ n → n * z ≡ z 
n*0≡0 = ℕInduction (λ n → (n * z) ≡ z) refl (λ _ p → p)

m*[1+n]≡m+[m*n] : ∀ m n → m * (s n) ≡ m + (m * n)
m*[1+n]≡m+[m*n] m n = ℕInduction (λ m → m * (s n) ≡ m + (m * n)) refl sP m 
  where sP : ∀ n₁ →
             (n₁ * s n) ≡ (n₁ + (n₁ * n)) →
             s (n + (n₁ * s n)) ≡ s (n₁ + (n + (n₁ * n)))
        sP n₁ p rewrite p
                | (sym (+-assoc n n₁ (n₁ * n)))
                | +-comm n n₁
                | +-assoc n₁ n (n₁ * n) = refl

n*sm≡m*[n*m] : ∀ n m → (n * s m) ≡ n + (n * m)
n*sm≡m*[n*m] m = ℕInduction (λ p → (m * s p) ≡ (m + (m * p))) zP sP
  where zP : (m * s z) ≡ (m + (m * z))
        zP rewrite n*0≡0 m | n+0≡n m | n*1≡n m = refl
        sP : ∀ n → (m * s n) ≡ (m + (m * n)) → (m * s (s n)) ≡ (m + (m * s n))
        sP n p rewrite m*[1+n]≡m+[m*n] m (s n) = refl 

{- This would probably be better with begin qed notation -}

2*[sum[n]]≡n*[n+1] : ∀ n → ((s (s z)) * (sum n)) ≡ (n * (n + (s z)))
2*[sum[n]]≡n*[n+1] = ℕInduction ((λ n → ((s (s z)) * (sum n)) ≡ (n * (n + (s z)))))
                                refl
                                sP
  where sP : (n : ℕ) →
             (sum n + (sum n + z)) ≡ (n * (n + s z)) →
             s ((n + sum n) + s ((n + sum n) + z)) ≡ s ((n + s z) + (n * s (n + s z)))
        sP n p rewrite n*sm≡m*[n*m] n (n + s z)
                     | sym p
                     | n+0≡n (sum n)
                     | n+0≡n (n + sum n)
                     | +-comm (n + sum n) (s (n + sum n))
                     | +-comm n (s z)
                     | sym (+-assoc n (sum n) (sum n))
                     | +-comm n (sum n)
                     | sym (+-assoc n (sum n + n) (sum n))
                     | +-assoc n (sum n) n
                     | +-comm n (sum n + n)
                     | +-assoc (sum n + n) n (sum n)
                     | +-comm n (sum n) = refl 

{- BTree example -}

data BTree : Set where
  leaf : BTree
  branch : BTree → BTree → BTree 

BTreeInduction : ∀ (P : BTree → Set) → (P leaf) → (∀ n m → P n → P m → P (branch n m)) → (t : BTree) → P t
BTreeInduction P lh bh leaf = lh
BTreeInduction P lh bh (branch t t₁) = bh t t₁ (BTreeInduction P lh bh t) ((BTreeInduction P lh bh t₁)) 

♯ofLeaves : BTree → ℕ
♯ofLeaves = BTreeInduction (λ _ → ℕ) (s z) (λ _ _ n₁ n₂ →  n₁ + n₂)

♯ofBranches : BTree → ℕ
♯ofBranches = BTreeInduction (λ _ → ℕ) z (λ _ _ n₁ n₂ → (s z) + (n₁ + n₂))

♯ofLeaves≡♯ofBranches+1 : ∀ t → ♯ofLeaves t ≡ s (♯ofBranches t)
♯ofLeaves≡♯ofBranches+1 = BTreeInduction (λ x → ♯ofLeaves x ≡ s (♯ofBranches x)) refl bh
  where bh : (n m : BTree) →
             ♯ofLeaves n ≡ s (♯ofBranches n) →
             ♯ofLeaves m ≡ s (♯ofBranches m) →
             ♯ofLeaves (branch n m) ≡ s (♯ofBranches (branch n m))
        bh n m p q rewrite p | q | n+1+m≡1+n+m (♯ofBranches n) (♯ofBranches m) = refl 


