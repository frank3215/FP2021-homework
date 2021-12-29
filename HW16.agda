module HW16 where

-- How to type those Unicode characters:
-- →   \->
-- ≡   \==
-- ≢   \==n
-- ⟨   \<
-- ⟩   \>
-- ∎   \qed
-- ∘   \o
-- ∷   \::
-- ℕ   \bN
-- ⊕   \oplus
-- ˡ   \^l       (4th candidate, use your right arrow key to select)
-- ʳ   \^r       (4th candidate, use your right arrow key to select)
-- ₁   \_1
-- ×   \x
-- ∀   \all
-- Σ   \Sigma
-- ∃   \ex
-- ⊆   \subseteq
-- ≤   \le
-- ⊔   \sqcu
-- ¬   \neg
-- ⊥   \bot
-- ∈   \in

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; refl; trans; sym; cong; cong-app; subst)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)

open import Function using (_∘_)

module semigroup where
  record IsSemigroup {A : Set} (_⊕_ : A → A → A) : Set where
    field assoc : ∀ x y z → (x ⊕ y) ⊕ z ≡ x ⊕ (y ⊕ z)

  open IsSemigroup public

  open import Data.Nat using (_+_)
  open import Data.Nat.Properties using (+-assoc)
  ℕ-add-is-semigroup : IsSemigroup _+_
  ℕ-add-is-semigroup .assoc = +-assoc

  open import Data.Nat using (_⊔_)
  open import Data.Nat.Properties using (⊔-assoc)
  ℕ-⊔-is-semigroup : IsSemigroup _⊔_
  ℕ-⊔-is-semigroup .assoc = ⊔-assoc

  open import Data.List using (List; _++_; [])
  open import Data.List.Properties using (++-assoc)
  List-++-is-semigroup : ∀ {A : Set} → IsSemigroup {List A} _++_
  List-++-is-semigroup .assoc = ++-assoc

open semigroup

module monoid1 where
  record IsMonoid {A : Set} (e : A) (_⊕_ : A → A → A) : Set where
    field
      is-semigroup : IsSemigroup _⊕_
      identityˡ : ∀ x → e ⊕ x ≡ x
      identityʳ : ∀ x → x ⊕ e ≡ x

  open IsMonoid public

  open import Data.Nat using (_+_)
  open import Data.Nat.Properties using (+-identityˡ; +-identityʳ)
  ℕ-add-is-monoid : IsMonoid 0 _+_
  ℕ-add-is-monoid .is-semigroup = ℕ-add-is-semigroup
  ℕ-add-is-monoid .identityˡ = +-identityˡ
  ℕ-add-is-monoid .identityʳ = +-identityʳ

  open import Data.Nat using (_⊔_)
  open import Data.Nat.Properties using (⊔-identityˡ; ⊔-identityʳ)
  ℕ-⊔-is-monoid : IsMonoid 0 _⊔_
  ℕ-⊔-is-monoid .is-semigroup = ℕ-⊔-is-semigroup
  ℕ-⊔-is-monoid .identityˡ = ⊔-identityˡ
  ℕ-⊔-is-monoid .identityʳ = ⊔-identityʳ

  open import Data.List using (List; _++_; [])
  open import Data.List.Properties using (++-identityˡ; ++-identityʳ)
  List-++-is-monoid : ∀ {A : Set} → IsMonoid {List A} [] _++_
  List-++-is-monoid .is-semigroup = List-++-is-semigroup
  List-++-is-monoid .identityˡ = ++-identityˡ
  List-++-is-monoid .identityʳ = ++-identityʳ

module MSS (
    extensionality : ∀ {A : Set} {B : A → Set}
        {f g : (x : A) → B x}
      → ((x : A) → f x ≡ g x)
        ---------------------
      → f ≡ g
  ) where

  open import Data.List using (List; []; _∷_; [_]; _++_; foldl; foldr; map; scanl; scanr)
  open import Data.Nat using (ℕ; _+_; zero; suc; _⊔_)

  inits : ∀ {A : Set} → List A → List (List A)
  inits = scanl _++_ [] ∘ map [_]

  tails : ∀ {A : Set} → List A → List (List A)
  tails [] = [] ∷ []
  tails (xs @ (x ∷ xs1)) = xs ∷ (tails xs1)

  concat : ∀ {A : Set} → List (List A) → List A
  concat = foldr _++_ []

  segs : ∀ {A : Set} → List A → List (List A)
  segs = concat ∘ map tails ∘ inits

  sum : List ℕ → ℕ
  sum = foldr _+_ 0

  maximum : List ℕ → ℕ
  maximum = foldr _⊔_ 0

  mss : List ℕ → ℕ
  mss = maximum ∘ map sum ∘ segs

  module monoid where
    record IsMonoid {A : Set} (e : A) (_⊕_ : A → A → A) : Set where
      field
        assoc : ∀ x y z → (x ⊕ y) ⊕ z ≡ x ⊕ (y ⊕ z)
        identityˡ : ∀ x → e ⊕ x ≡ x
        identityʳ : ∀ x → x ⊕ e ≡ x

    open IsMonoid public

    open import Data.Nat.Properties using (+-assoc; +-identityˡ; +-identityʳ)
    ℕ-add-is-monoid : IsMonoid 0 _+_
    ℕ-add-is-monoid .assoc = +-assoc
    ℕ-add-is-monoid .identityˡ = +-identityˡ
    ℕ-add-is-monoid .identityʳ = +-identityʳ

    open import Data.Nat.Properties using (⊔-assoc; ⊔-identityˡ; ⊔-identityʳ)
    ℕ-⊔-is-monoid : IsMonoid 0 _⊔_
    ℕ-⊔-is-monoid .assoc = ⊔-assoc
    ℕ-⊔-is-monoid .identityˡ = ⊔-identityˡ
    ℕ-⊔-is-monoid .identityʳ = ⊔-identityʳ

    open import Data.List.Properties using (++-assoc; ++-identityˡ; ++-identityʳ)
    List-++-is-monoid : ∀ {A : Set} → IsMonoid {List A} [] _++_
    List-++-is-monoid .assoc = ++-assoc
    List-++-is-monoid .identityˡ = ++-identityˡ
    List-++-is-monoid .identityʳ = ++-identityʳ

  open monoid

  -- Did you know there are plenty of useful theorems in the standard library?
  open import Data.Nat.Properties using (+-distribˡ-⊔; +-distribʳ-⊔)
  -- +-distribˡ-⊔ : ∀ x y z → x + (y ⊔ z) ≡ (x + y) ⊔ (x + z)
  -- +-distribʳ-⊔ : ∀ x y z → (y ⊔ z) + x ≡ (y + x) ⊔ (z + x)


  -- Lemmas
  open import Data.List.Properties renaming (map-++-commute to map-++-distrib)
  {-
  map-++-distrib : ∀ {A B : Set} -> (xs ys : List A) -> (f : A -> B) -> map f (xs ++ ys) ≡ map f xs ++ map f ys
  map-++-distrib [] ys f = refl
  map-++-distrib (x ∷ xs) ys f =
    begin
      map f ( (x ∷ xs) ++ ys)
    ≡⟨⟩
      f x ∷  map f (xs ++ ys)
    ≡⟨ cong (f x ∷_) (map-++-distrib xs ys f) ⟩
      f x ∷ map f xs ++ map f ys
    ≡⟨⟩
      map f (x ∷ xs) ++ map f ys
    ∎
  -}

  map-promotion : forall {A B : Set} -> (f : A -> B) -> (xss : List (List A)) -> (map f ∘ concat) xss ≡ (concat ∘ map (map f)) xss
  map-promotion {A} f [] = refl
  map-promotion {A} f (xs ∷ xss) =
    begin
      (map f ∘ concat) (xs ∷ xss)
    ≡⟨⟩
      map f (concat (xs ∷ xss))
    ≡⟨⟩
      map f ((xs) ++ (concat xss))
    ≡⟨ map-++-distrib f xs (concat xss) ⟩
      map f xs ++ map f (concat xss)
    ≡⟨ cong (map f xs ++_) (map-promotion {A} f xss) ⟩
      (map f xs) ++ concat (map (map f) xss)
    ≡⟨⟩
      concat ( (map f xs) ∷ (map (map f) xss) )
    ≡⟨⟩
      concat (map (map f) (xs ∷ xss))
    ∎
  
  map-distrib : forall {A B C : Set} -> (f : A -> B) -> (g : B -> C) -> (xs : List A)-> (map g ∘ map f) xs ≡ map (g ∘ f) xs
  map-distrib {A} {B} {C} f g [] = refl
  map-distrib {A} {B} {C} f g (x ∷ xs) =
    begin
      (g (f x) ∷ map g (map f xs))
    ≡⟨ cong (g (f x) ∷_) (map-distrib f g xs) ⟩
      (g (f x) ∷ map (g ∘ f) xs)
    ∎
  
  foldr-++-distrib : {A : Set} -> (xs ys : List A) -> (_⊕_ : A -> A -> A) -> (e : A) -> (IsMonoid e _⊕_) -> foldr _⊕_ e (xs ++ ys) ≡ (foldr _⊕_ e xs) ⊕ (foldr _⊕_ e ys)
  foldr-++-distrib [] ys _⊕_ e m =
    begin
      (foldr _⊕_ e ys)
    ≡⟨ sym (identityˡ m (foldr _⊕_ e ys)) ⟩
      e ⊕ (foldr _⊕_ e ys)
    ∎
  foldr-++-distrib (x ∷ xs) ys _⊕_ e m =
    begin
      x ⊕ foldr _⊕_ e (xs ++ ys)
    ≡⟨ cong (x ⊕_) (foldr-++-distrib xs ys _⊕_ e m) ⟩
      x ⊕ (foldr _⊕_ e xs ⊕ foldr _⊕_ e ys)
    ≡⟨ sym (assoc m x (foldr _⊕_ e xs) (foldr _⊕_ e ys)) ⟩
      (x ⊕ foldr _⊕_ e xs) ⊕ foldr _⊕_ e ys
    ∎

  reduce-promotion : forall {A : Set} -> (xss : List (List A)) -> (_⊕_ : A -> A -> A) -> (e : A) -> (IsMonoid {A} e _⊕_) -> (foldr _⊕_ e ∘ foldr _++_ []) xss ≡ (foldr _⊕_ e ∘ map (foldr _⊕_ e)) xss
  reduce-promotion {A} [] _⊕_ e m = refl
  reduce-promotion {A} (xs ∷ xss) _⊕_ e m =
    begin
      foldr _⊕_ e (xs ++ foldr _++_ [] xss)
    ≡⟨ foldr-++-distrib xs (foldr _++_ [] xss) _⊕_ e m ⟩
      (foldr _⊕_ e xs ⊕ foldr _⊕_ e (foldr _++_ [] xss))
    ≡⟨ cong (foldr _⊕_ e xs ⊕_) (reduce-promotion xss _⊕_ e m) ⟩
      (foldr _⊕_ e xs ⊕ foldr _⊕_ e (map (foldr _⊕_ e) xss))
    ∎
  
  R-Dist : ∀{A : Set} (_⊕_ : A → A → A)(_⊗_ : A → A → A) → Set
  R-Dist {A} _⊕_ _⊗_ = ∀ (a b c : A) → (a ⊕ b) ⊗ c ≡ (a ⊗ c) ⊕ (b ⊗ c)

  horner-rule-lemma2 : ∀{A : Set} (_⊕_ : A → A → A) (e-⊕ : A)
    (_⊗_ : A → A → A) (e-⊗ : A)
    → (p : IsMonoid e-⊕ _⊕_)
    → (q : IsMonoid e-⊗ _⊗_ )
    → (rdist : R-Dist _⊕_ _⊗_)
    → (x : A)
    → (xs : List A)
    -----------------------------
    → ((x ⊗ foldr _⊗_ e-⊗ xs) ⊕ foldl (λ z z₁ → (z ⊗ z₁) ⊕ e-⊗) e-⊗ xs)
    ≡ foldl (λ z z₁ → (z ⊗ z₁) ⊕ e-⊗) (x ⊕ e-⊗) xs
  
  horner-rule-lemma2 {A} _⊕_ e-⊕ _⊗_ e-⊗ p q rdist x [] =
    begin
      ((x ⊗ e-⊗) ⊕ e-⊗)
    ≡⟨ cong (_⊕ e-⊗) (identityʳ q x) ⟩
      (x ⊕ e-⊗)
    ∎
  horner-rule-lemma2 {A} _⊕_ e-⊕ _⊗_ e-⊗ p q rdist x (x₁ ∷ xs) =
    begin
      ((x ⊗ (x₁ ⊗ foldr _⊗_ e-⊗ xs)) ⊕ foldl f ((e-⊗ ⊗ x₁) ⊕ e-⊗) xs)
    ≡⟨ cong (λ y → ((x ⊗ (x₁ ⊗ foldr _⊗_ e-⊗ xs)) ⊕ foldl f ((y) ⊕ e-⊗) xs)) (identityˡ q x₁) ⟩
      ((x ⊗ (x₁ ⊗ foldr _⊗_ e-⊗ xs)) ⊕ foldl f (x₁ ⊕ e-⊗) xs)
    ≡⟨ cong (_⊕ foldl f (x₁ ⊕ e-⊗) xs) (sym (assoc q x x₁ (foldr _⊗_ e-⊗ xs))) ⟩
      (((x ⊗ x₁) ⊗ foldr _⊗_ e-⊗ xs) ⊕ foldl f (x₁ ⊕ e-⊗) xs)
    ≡⟨ cong (λ y → ((x ⊗ x₁) ⊗ foldr _⊗_ e-⊗ xs) ⊕ y) (sym (horner-rule-lemma2 _⊕_ e-⊕ _⊗_ e-⊗ p q rdist x₁ xs))⟩
      (((x ⊗ x₁) ⊗ foldr _⊗_ e-⊗ xs) ⊕ ((x₁ ⊗ foldr _⊗_ e-⊗ xs) ⊕ foldl f e-⊗ xs))
    ≡⟨ sym (assoc p ((x ⊗ x₁) ⊗ foldr _⊗_ e-⊗ xs) (x₁ ⊗ foldr _⊗_ e-⊗ xs) (foldl f e-⊗ xs)) ⟩
      ((((x ⊗ x₁) ⊗ foldr _⊗_ e-⊗ xs) ⊕ (x₁ ⊗ foldr _⊗_ e-⊗ xs)) ⊕ foldl f e-⊗ xs)
    ≡⟨ cong (_⊕ foldl f e-⊗ xs) (sym (rdist (x ⊗ x₁) x₁ (foldr _⊗_ e-⊗ xs)))  ⟩
      ((((x ⊗ x₁) ⊕ x₁) ⊗ foldr _⊗_ e-⊗ xs) ⊕ foldl f e-⊗ xs)
    ≡⟨ horner-rule-lemma2 _⊕_ e-⊕ _⊗_ e-⊗ p q rdist ((x ⊗ x₁) ⊕ x₁) xs ⟩
      foldl f (((x ⊗ x₁) ⊕ x₁) ⊕ e-⊗) xs
    ≡⟨ cong (λ y → foldl f (((x ⊗ x₁) ⊕ y) ⊕ e-⊗) xs) (sym (identityˡ q x₁)) ⟩
      foldl f (((x ⊗ x₁) ⊕ (e-⊗ ⊗ x₁)) ⊕ e-⊗) xs
    ≡⟨ cong (λ y → foldl f (y ⊕ e-⊗) xs) (sym (rdist x e-⊗ x₁)) ⟩
      foldl f (((x ⊕ e-⊗) ⊗ x₁) ⊕ e-⊗) xs
    ∎
    where
      f = (λ z z₁ → (z ⊗ z₁) ⊕ e-⊗)

  horner-rule-lemma : ∀{A : Set} (_⊕_ : A → A → A) (e-⊕ : A)
    (_⊗_ : A → A → A) (e-⊗ : A)
    → (p : IsMonoid e-⊕ _⊕_)
    → (q : IsMonoid e-⊗ _⊗_ )
    → (rdist : R-Dist _⊕_ _⊗_)
    → (xs : List A)
    -----------------------------
    → (foldr _⊕_ e-⊕ ∘ map (foldr _⊗_ e-⊗) ∘ tails) xs
    ≡ (foldl (λ a b → (a ⊗ b) ⊕ e-⊗ ) e-⊗) xs
  
  horner-rule-lemma {A} _⊕_ e-⊕ _⊗_ e-⊗ p q rdist [] =
    begin
      (e-⊗ ⊕ e-⊕)
    ≡⟨ identityʳ p e-⊗ ⟩
      e-⊗
    ∎

  horner-rule-lemma {A} _⊕_ e-⊕ _⊗_ e-⊗ p q rdist (x ∷ xs) =
    begin
      ((x ⊗ foldr _⊗_ e-⊗ xs) ⊕ foldr _⊕_ e-⊕ (map (foldr _⊗_ e-⊗) (tails xs)) )
    ≡⟨ cong (λ y → (x ⊗ foldr _⊗_ e-⊗ xs) ⊕ y) (horner-rule-lemma _⊕_ e-⊕ _⊗_ e-⊗ p q rdist xs) ⟩
      ((x ⊗ foldr _⊗_ e-⊗ xs) ⊕ foldl (λ z z₁ → (z ⊗ z₁) ⊕ e-⊗) e-⊗ xs)
    ≡⟨ horner-rule-lemma2 {A} _⊕_ e-⊕ _⊗_ e-⊗ p q rdist x xs ⟩
      foldl (λ z z₁ → (z ⊗ z₁) ⊕ e-⊗) (x ⊕ e-⊗) xs
    ≡⟨ cong (λ y → foldl (λ z z₁ → (z ⊗ z₁) ⊕ e-⊗) (y ⊕ e-⊗) xs) (sym (identityˡ q x)) ⟩
      foldl (λ z z₁ → (z ⊗ z₁) ⊕ e-⊗) ((e-⊗ ⊗ x) ⊕ e-⊗) xs
    ∎
  {-
    begin
      (foldr _⊕_ e-⊕ ∘ map (foldr _⊗_ e-⊗) ∘ scanr _++_ []) ( [ x ] ∷ map [_] xs)
    ≡⟨⟩
      {!   !}
    ≡⟨ {!   !} ⟩
      {!   !}
    ≡⟨ {!   !} ⟩
      foldl (λ z z₁ → (z ⊗ z₁) ⊕ e-⊗) ((e-⊗ ⊗ x) ⊕ e-⊗) xs
    ∎
  -}

  horner-rule : ∀{A : Set} (_⊕_ : A → A → A) (e-⊕ : A)
    (_⊗_ : A → A → A) (e-⊗ : A)
    → (p : IsMonoid e-⊕ _⊕_)
    → (q : IsMonoid e-⊗ _⊗_ )
    → (rdist : R-Dist _⊕_ _⊗_)
    -----------------------------
    → (foldr _⊕_ e-⊕ ∘ map (foldr _⊗_ e-⊗) ∘ tails)
    ≡ (foldl (λ a b → (a ⊗ b) ⊕ e-⊗ ) e-⊗)
  horner-rule _⊕_ e-⊕ _⊗_ e-⊗ p q rdist = extensionality (horner-rule-lemma _⊕_ e-⊕ _⊗_ e-⊗ p q rdist)
  --

  _⊙_ : ℕ -> ℕ -> ℕ
  _⊙_ a b = (a + b) ⊔ 0

  mss-fast : List ℕ → ℕ
  mss-fast = maximum ∘ scanl _⊙_ 0

  -- note: it is possible to avoid extensionality and instead prove the following
  --
  
  -- +-distribʳ-⊔ : ∀ x y z → (y ⊔ z) + x ≡ (y + x) ⊔ (z + x)
  -- R-Dist {A} _⊕_ _⊗_ = ∀ (a b c : A) → (a ⊕ b) ⊗ c ≡ (a ⊗ c) ⊕ (b ⊕ c)
  -- R-Dist _⊔_ _+_ : 
  -- _*_ DistributesOverʳ _+_ = ∀ x y z → ((y + z) * x) ≈ ((y * x) + (z * x))
  -- _+_ DistributesOverʳ _⊔_ = ∀ x y z → ((y ⊔ z) + x) ≈ ((y + x) ⊔ (z + x))
  -- a-y b-z c-x
  distrib-lemma : (a b c : ℕ) → (a ⊔ b) + c ≡ (a + c) ⊔ (b + c)
  distrib-lemma a b c = +-distribʳ-⊔ c a b

  scanl-lemma1 : {A : Set}
    -> (_⊙_ : A -> A -> A)
    -> (e : A)
    -> IsMonoid e _⊙_
    -> (x : A)
    -> (xs : List A)
    -------------------
    -> scanl _⊙_ x xs ≡ map (x ⊙_) (scanl _⊙_ e xs)
  
  scanl-lemma1 _⊙_ e x x₁ [] =
    begin
      (x₁ ∷ [])
    ≡⟨ sym (cong (_∷ []) (identityʳ x x₁)) ⟩
      ((x₁ ⊙ e) ∷ [])
    ∎
  scanl-lemma1 _⊙_ e m x (x₁ ∷ xs) =
    begin
      (x ∷ scanl _⊙_ (x ⊙ x₁) xs)
    ≡⟨ cong (x ∷_) (scanl-lemma1 _⊙_ e m (x ⊙ x₁) xs) ⟩
      (x ∷ map ((x ⊙ x₁) ⊙_) (scanl _⊙_ e xs))
    ≡⟨ cong (λ y → x ∷ map (y) (scanl _⊙_ e xs)) (extensionality (assoc m x x₁)) ⟩
      (x ∷ map ((x ⊙_) ∘ (x₁ ⊙_)) (scanl _⊙_ e xs))
    ≡⟨ cong (x ∷_) (sym (map-distrib (x₁ ⊙_) (x ⊙_) (scanl _⊙_ e xs))) ⟩
      x ∷ map (x ⊙_) (map (_⊙_ x₁) (scanl _⊙_ e xs))
    ≡⟨ cong (λ y → x ∷ map (x ⊙_) y) (sym (scanl-lemma1 _⊙_ e m x₁ xs)) ⟩
      (x ∷ map (x ⊙_) (scanl _⊙_ x₁ xs))
    ≡⟨ cong (λ y → (x ∷ map (_⊙_ x) (scanl _⊙_ y xs))) (sym (identityˡ m x₁)) ⟩
      (x ∷ map (_⊙_ x) (scanl _⊙_ (e ⊙ x₁) xs))
    ≡⟨ cong (_∷ map (_⊙_ x) (scanl _⊙_ (e ⊙ x₁) xs)) (sym (identityʳ m x)) ⟩
      ((x ⊙ e) ∷ map (_⊙_ x) (scanl _⊙_ (e ⊙ x₁) xs))
    ∎

  scanl-lemma : {A : Set}
    -> (_⊙_ : A -> A -> A)
    -> (e : A)
    -> IsMonoid e _⊙_
    -> (x : A)
    -> (xs : List A)
    -------------------
    -> scanl _⊙_ e (x ∷ xs) ≡ e ∷ map (x ⊙_) (scanl _⊙_ e xs)
  
  scanl-lemma _⊙_ e m x [] =
    begin
      (e ∷ ((e ⊙ x) ∷ []))
    ≡⟨ cong (λ x → e ∷ (x ∷ [])) (identityˡ m x) ⟩
      (e ∷ (x ∷ []))
    ≡⟨ cong (λ x → e ∷ (x ∷ [])) (sym (identityʳ m x)) ⟩ 
      (e ∷ ((x ⊙ e) ∷ []))
    ∎

  scanl-lemma _⊙_ e m x (x₁ ∷ xs) =
    begin
      e ∷ ((e ⊙ x) ∷ scanl _⊙_ ((e ⊙ x) ⊙ x₁) xs)
    ≡⟨ cong (λ y → e ∷ (y ∷ scanl _⊙_ ((e ⊙ x) ⊙ x₁) xs)) (identityˡ m x) ⟩
      (e ∷ (x ∷ scanl _⊙_ ((e ⊙ x) ⊙ x₁) xs))
    ≡⟨ cong (λ y → (e ∷ (x ∷ scanl _⊙_ (y ⊙ x₁) xs))) (identityˡ m x) ⟩
      (e ∷ (x ∷ scanl _⊙_ (x ⊙ x₁) xs))
    ≡⟨ cong (λ y → (e ∷ (x ∷ y))) (scanl-lemma1 _⊙_ e m (x ⊙ x₁) xs) ⟩
      (e ∷ (x ∷ map (_⊙_ (x ⊙ x₁)) (scanl _⊙_ e xs)))
    ≡⟨ cong (λ y → e ∷ (x ∷ map y (scanl _⊙_ e xs))) (extensionality (assoc m x x₁)) ⟩
      (e ∷ (x ∷ map ((x ⊙_) ∘ (x₁ ⊙_)) (scanl _⊙_ e xs)))
    ≡⟨ sym (cong (λ y → (e ∷ (x ∷ y))) ((map-distrib (_⊙_ x₁) (_⊙_ x) (scanl _⊙_ e xs)))) ⟩
      (e ∷ (x ∷ (map (_⊙_ x) ∘ map (_⊙_ x₁)) (scanl _⊙_ e xs)))
    ≡⟨ sym (cong (λ y → (e ∷ (x ∷ map (_⊙_ x) y))) (scanl-lemma1 _⊙_ e m x₁ xs)) ⟩
      (e ∷ (x ∷ map (_⊙_ x) (scanl _⊙_ x₁ xs)))
    ≡⟨ cong (λ y → (e ∷ (x ∷ map (_⊙_ x) (scanl _⊙_ y xs)))) (sym (identityˡ m x₁)) ⟩
      (e ∷ (x ∷ map (_⊙_ x) (scanl _⊙_ (e ⊙ x₁) xs)))
    ≡⟨ cong (λ y → e ∷ (y ∷ map (_⊙_ x) (scanl _⊙_ (e ⊙ x₁) xs))) (sym (identityʳ m x)) ⟩ 
      e ∷ ((x ⊙ e) ∷ map (_⊙_ x) (scanl _⊙_ (e ⊙ x₁) xs))
    ∎

  accum-lemma : {A : Set}
    -> (_⊙_ : A -> A -> A)
    -> (e : A)
    -> (xs : List A)
    ---------------------------
    -> (map (foldl _⊙_ e) ∘ inits) xs ≡ scanl _⊙_ e xs
  
  {-
    inits : ∀ {A : Set} → List A → List (List A)
    inits = scanl _++_ [] ∘ map [_]

    inits : List A → List (List A)
    inits []       = [] ∷ []
    inits (x ∷ xs) = [] ∷ map (x ∷_) (inits xs)

    scanl : (A → B → A) → A → List B → List A
    scanl f e []       = e ∷ []
    scanl f e (x ∷ xs) = e ∷ scanl f (f e x) xs
  -}

  accum-lemma f e [] = refl
  accum-lemma {A} _⊙_ e (x ∷ xs) =
    begin
      (map (foldl _⊙_ e) ∘ scanl _++_ [] ∘ map [_]) (x ∷ xs)
    ≡⟨⟩
      (map (foldl _⊙_ e)) (scanl _++_ [] ([ x ] ∷ map [_] xs))
    ≡⟨ cong (map (foldl _⊙_ e)) (scanl-lemma _++_ [] List-++-is-monoid [ x ] (map [_] xs)) ⟩
      e ∷ ((map (foldl _⊙_ e) ∘ map (x ∷_)) (scanl _++_ [] (map [_] xs)))
    ≡⟨ cong (e ∷_) (map-distrib (x ∷_) (foldl _⊙_ e) (scanl _++_ [] (map [_] xs)))  ⟩
      e ∷ map ((foldl _⊙_ e) ∘ (x ∷_)) (scanl _++_ [] (map [_] xs))
    ≡⟨⟩
      e ∷ map (foldl _⊙_ (e ⊙ x)) (scanl _++_ [] (map [_] xs))
    ≡⟨⟩
      e ∷ map (foldl _⊙_ (e ⊙ x)) (inits xs)
    ≡⟨ cong (e ∷_) (accum-lemma {A} _⊙_ (e ⊙ x) xs) ⟩
      e ∷ scanl _⊙_ (e ⊙ x) xs
    ∎

  derivation-alt : ∀ xs → mss xs ≡ mss-fast xs
  derivation-alt xs =
    begin
      (maximum ∘ map sum ∘ concat ∘ map tails ∘ inits) xs
    ≡⟨ cong (maximum) (map-promotion sum ((map tails ∘ inits) xs)) ⟩
      (maximum ∘ concat ∘ map (map sum) ∘ map tails ∘ inits) xs
    ≡⟨ reduce-promotion ((map (map sum) ∘ map tails ∘ inits) xs) _⊔_ 0 ℕ-⊔-is-monoid ⟩
      (maximum ∘ map maximum ∘ map (map sum) ∘ map tails ∘ inits) xs
    ≡⟨ cong maximum (map-distrib (map sum) maximum ((map tails ∘ inits) xs)) ⟩
      (maximum ∘ map (maximum ∘ (map sum)) ∘ map tails ∘ inits) xs
    ≡⟨ cong maximum (map-distrib tails (maximum ∘ (map sum)) (inits xs)) ⟩
      (maximum ∘ map (foldr _⊔_ 0 ∘ (map (foldr _+_ 0)) ∘ tails) ∘ inits) xs
    ≡⟨ cong (λ f -> (maximum ∘ map f ∘ inits) xs) (horner-rule _⊔_ 0 _+_ 0 ℕ-⊔-is-monoid ℕ-add-is-monoid distrib-lemma) ⟩ -- (λ a b c -> +-distribʳ-⊔ c a b)
      (maximum ∘ map (foldl _⊙_ 0) ∘ inits) xs
    ≡⟨ cong maximum (accum-lemma _⊙_ 0 xs) ⟩
      (maximum ∘ scanl _⊙_ 0) xs
    ∎
  --
  -- in fact, this version should be slightly easier to write, since it (generally)
  -- produces better error messages. If you want to follow this route, go ahead and
  -- prove the above 'derivation-alt', and uncomment the following:
  --
  derivation : mss ≡ mss-fast
  derivation = extensionality derivation-alt

  -- bonus(hard): try to prove the correctness of 'mss' and 'mss-fast'
  --
  -- We have this "segment" relation (you may come up with better definitions):
  --   open import Data.List using (take; drop)
  --   infix 4 _⊆_
  --   data _⊆_ {A : Set} (xs : List A) (ys : List A) : Set where
  --     segment : ∀ m n → take m (drop n ys) ≡ xs → xs ⊆ ys
  -- We also have the "less than" relation:
  --   open import Data.Nat using (_≤_)
  -- which is defined as follows in the standard library:
  --   infix 4 _≤_
  --   data _≤_ : ℕ → ℕ → Set where
  --     z≤n : ∀ {n}                 → zero  ≤ n
  --     s≤s : ∀ {m n} (m≤n : m ≤ n) → suc m ≤ suc n
  -- 'mss' is proven to be correct if we can prove the following two theorems:
  --   open import Data.Product using (_×_; ∃-syntax)
  --   mss-is-max : ∀ {xs ys} → ys ⊆ xs → sum ys ≤ mss xs
  --   mss-is-max = ?
  --   mss-exists : ∀ {xs} → ∃[ ys ] ys ⊆ xs × sum ys ≡ mss xs
  --   mss-exists = ?

module BMF2-1 where

  open monoid1

  open import Data.Product using (_×_; _,_; Σ-syntax; proj₁)
  open import Data.Nat using (ℕ; _+_; zero; suc)
  open import Data.List using (List; []; _∷_; [_]; _++_)
  open import Relation.Nullary using (¬_)

  infixr 5 _∷′_
  data NList (A : Set) : Set where
    [_]′ : (x : A) → NList A
    _∷′_ : (x : A) → (xs : NList A) → NList A

  infixr 5 _++′_
  _++′_ : ∀ {A : Set} → NList A → NList A → NList A
  [ x ]′ ++′ ys = x ∷′ ys
  (x ∷′ xs) ++′ ys = x ∷′ xs ++′ ys

  ++′-assoc : ∀ {A : Set} (xs ys zs : NList A) → (xs ++′ ys) ++′ zs ≡ xs ++′ ys ++′ zs
  ++′-assoc [ x ]′    ys zs = refl
  ++′-assoc (x ∷′ xs) ys zs = cong (x ∷′_) (++′-assoc xs ys zs)

  NList-++′-is-semigroup : ∀ {A : Set} → IsSemigroup {NList A} _++′_
  NList-++′-is-semigroup .assoc = ++′-assoc

  -- this reduce works on non-empty lists
  reduce : ∀ {A : Set} → (_⊕_ : A → A → A) → NList A → A
  reduce {A} _⊕_ [ x ]′ = x
  reduce {A} _⊕_ (x ∷′ xs) = x ⊕ reduce _⊕_ xs

  -- this map works on non-empty lists
  -- and it produces non-empty lists
  map : ∀ {A B : Set} → (f : A → B) → NList A → NList B
  map f [ x ]′ = [ f x ]′
  map f (x ∷′ xs) = f x ∷′ map f xs

  record IsHomomorphism
    {A : Set} {_⊕_ : A → A → A} (m₁ : IsSemigroup _⊕_)
    {B : Set} {_⊗_ : B → B → B} (m₂ : IsSemigroup _⊗_)
    (f : A → B) : Set where
    field
      distrib : (x y : A) → f (x ⊕ y) ≡ f x ⊗ f y

  open IsHomomorphism

  -- 1. prove 'split' is a homomorphism
  split : ∀ {A : Set} → NList A → List A × A
  split = reduce (λ (xs , x) (ys , y) → ((xs ++ [ x ] ++ ys) , y)) ∘ map (λ x → ([] , x))

  -- bonus: you may also want to prove the following theorems:
  --   _⊗_ : ∀ {A : Set} → List A × A → List A × A → List A × A
  --   R-is-semigroup : ∀ {A : Set} → IsSemigroup {List A × A} _⊗_
  --   split-is-homomorphism : ∀ {A : Set} → IsHomomorphism NList-++′-is-semigroup R-is-semigroup (split {A})
  -- Alternatively, you may find it much more desirable (satisfactory) to prove the general case:
  --   reduce-map-is-homomorphism : ∀ {A B : Set}
  --     → (f : A → B)
  --     → (_⊗_ : B → B → B)
  --     → (B-⊗-is-semigroup : IsSemigroup _⊗_)
  --       ---------------------------------------------------------------------------
  --     → IsHomomorphism NList-++′-is-semigroup B-⊗-is-semigroup (reduce _⊗_ ∘ map f)

  -- to verify your 'split' is correct. after defining 'split', proving the following
  -- should be as easy as filling in 'refl'.
  split-is-correct : split (1 ∷′ 2 ∷′ 3 ∷′ [ 4 ]′) ≡ (1 ∷ 2 ∷ 3 ∷ [] , 4)
  split-is-correct =
    begin
      ((1 ∷ (2 ∷ (3 ∷ []))) , 4)
    ∎

  -- bonus: find a proper way to prove your split is indeed correct:
  -- split-is-indeed-correct : ∀ {A} xs
  --   → let (ys , z) = split {A} xs
  --     in xs ≡ ys ++ [ z ]

  -- 2. prove 'init' is not a homomorphism
  init : ∀ {A : Set} → NList A → List A
  init = proj₁ ∘ split

  -- This part might be too hard for you to prove in Agda, so you can choose
  -- to write this part in natural language. If so, comment out (or remove)
  -- the following code, and write your proof in the comments.
  --
  -- Anyway, below are some key points if you want to try to prove in Agda:
  -- (1) inequality 'x ≢ y' is negation of equality: '¬ (x ≡ y)'
  -- (2) negation '¬ x' is implication to falsity: 'x → ⊥'
  -- (3) falsity '⊥' is an empty data type, it has no constructors ...
  -- (4) ... which means we can pattern match with absurd pattern '()'
  
  no-eq : ¬ ([ 1 ] ≡ [ 2 ])
  no-eq ()

{-
  no-homo : ¬ ( (A : Set) → (xs : NList A) → (ys : NList A) → (init xs ≡ init ys) → (xs ≡ ys))
  no-homo proof = no-eq (proof ℕ [ 1 ]′ [ 2 ]′ refl)
-}

  init-is-not-homomorphism : ∀ {_⊗_} (m : IsSemigroup _⊗_)
    → ¬ IsHomomorphism NList-++′-is-semigroup m (init {ℕ})
  init-is-not-homomorphism {_⊗_} m H = no-eq (
    begin
      [ 1 ]
    ≡⟨ distrib H [ 1 ]′ [ 2 ]′ ⟩
      [] ⊗ []
    ≡⟨ sym (distrib H [ 2 ]′ [ 1 ]′) ⟩
      [ 2 ]
    ∎
    )

  -- Hint: you might want to follow this guideline below if you get stuck.
  --
  -- Step 1: interpret the theorem
  --   ¬ IsHomomorphism NList-++′-is-semigroup m (init {ℕ})
  -- is just another way of saying
  --   IsHomomorphism NList-++′-is-semigroup m (init {ℕ}) → ⊥
  -- (proof by contradiction)
  --
  -- Step 2: get your premise
  -- You want to derive contradiction from the premise, so the first thing
  -- to do is get the premise (add it as an argument):
  --   init-is-not-homomorphism {_⊗_} m H = ?
  -- Now we have the following premises:
  --   m : IsSemigroup _⊗_
  --   H : IsHomomorphism NList-++′-is-semigroup m (init {ℕ})
  --
  -- Step 3: derive absurd results
  -- Pass in some example to your premises, and try to get some absurd
  -- results such as 'K : [ 0 ] ≡ [ 42 ]'.
  --
  -- Step 4: show the absurdity by proving the negation
  -- e.g. for 'K : [ 0 ] ≡ [ 42 ]', write the following:
  --   ¬K : [ 0 ] ≢ [ 42 ]
  --   ¬K ()
  --
  -- Step 5: make use of that absurd result
  -- Use the result 'K' from Step 3, apply it to '¬K':
  --   ¬K K
  -- Just use this expression as the return value.