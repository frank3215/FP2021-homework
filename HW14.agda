module HW14 where

module problem-1 where

  open import Data.List using (List; []; _∷_)

  -- we have 'infix 5 _∷_' in 'Data.List'
  -- therefore we make _⊆_ slightly less associative
  infix 4 _⊆_
  data _⊆_ {A : Set} : List A → List A → Set where
    stop : [] ⊆ []
    drop : ∀ {xs y ys} → xs ⊆ ys → xs ⊆ y ∷ ys
    keep : ∀ {x xs ys} → xs ⊆ ys → x ∷ xs ⊆ x ∷ ys

  ⊆-refl : ∀ {A} {xs : List A} → xs ⊆ xs
  ⊆-refl {xs = []} = stop
  ⊆-refl {xs = x ∷ xs} = keep ⊆-refl

  ⊆-trans : ∀ {A} {xs ys zs : List A} → xs ⊆ ys → ys ⊆ zs → xs ⊆ zs
  ⊆-trans stop q = q
  ⊆-trans p (drop q) = drop (⊆-trans p q)
  ⊆-trans (keep p) (keep q) = keep (⊆-trans p q)
  ⊆-trans (drop p) (keep q) = drop (⊆-trans p q)

module problem-2 where

  open import Data.Nat using (ℕ; zero; suc; _+_)

  import Relation.Binary.PropositionalEquality as Eq
  open Eq using (_≡_; refl; trans; sym; cong; cong-app; subst)
  open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)

  +-identity : ∀ (m : ℕ) → m + zero ≡ m
  +-identity zero = refl
  +-identity (suc m) = cong suc (+-identity m)


  +-suc : ∀ (m n : ℕ) → m + suc n ≡ suc (m + n)
  +-suc zero n = refl
  +-suc (suc m) n = cong suc (+-suc m n)
  {-
  +-suc (suc m) n =
    begin
      suc m + suc n
    ≡⟨⟩
      suc (m + suc n)
    ≡⟨ cong suc (+-suc m n) ⟩
      suc (suc (m + n))
    ≡⟨⟩
      suc ((suc m) + n)
    ∎
-}