module HW15 where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; trans; sym; cong; cong-app; subst)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)

open import Data.List using (List; []; _∷_; _++_; foldr)

module problem-1 where

  ++-assoc : ∀ {A : Set}
      (xs ys zs : List A)
      -----------------------------------
    → (xs ++ ys) ++ zs ≡ xs ++ (ys ++ zs)
  ++-assoc {A} [] ys zs = refl
  ++-assoc {A} (x ∷ xs) ys zs =
    begin
      x ∷ (xs ++ ys) ++ zs
    ≡⟨ cong (x ∷_) (++-assoc xs ys zs) ⟩
      x ∷ xs ++ ys ++ zs
    ∎

  -- tips: to input the superscript l (ˡ), type \^l and use your
  --       arrow keys to select it (should be the fourth candidate).
  ++-identityˡ : ∀ {A : Set}
      (xs : List A)
      -------------
    → [] ++ xs ≡ xs
  ++-identityˡ xs = refl

  -- you might have already guessed it: type \^r for superscript r (ʳ)
  -- again, use your arrow keys to select it (the fourth candidate). 
  ++-identityʳ : ∀ {A : Set}
      (xs : List A)
    → xs ++ [] ≡ xs
  ++-identityʳ [] = refl
  ++-identityʳ (x ∷ xs) = 
    begin
      x ∷ xs ++ []
    ≡⟨ cong (x ∷_) (++-identityʳ xs) ⟩
      x ∷ xs
    ∎

module problem-2 where

  -- tips: to input ⊗, type \otimes
  foldr-++ : ∀ {A : Set}
      (_⊗_ : A → A → A)
      (e : A)
      (xs ys : List A)
      -----------------------------
    → foldr _⊗_ e (xs ++ ys)
    ≡ foldr _⊗_ (foldr _⊗_ e ys) xs
  foldr-++ _⊗_ e [] ys = refl
  foldr-++ _⊗_ e (x ∷ xs) ys =
    begin
      (x ⊗ foldr _⊗_ e (xs ++ ys))
    ≡⟨ cong (x ⊗_) (foldr-++ _⊗_ e xs ys) ⟩
      (x ⊗ foldr _⊗_ (foldr _⊗_ e ys) xs)
    ∎

module problem-3 (
    extensionality : ∀ {A : Set} {B : A → Set}
        {f g : (x : A) → B x}
      → ((x : A) → f x ≡ g x)
        ---------------------
      → f ≡ g
  ) where

  open import Function using (id; _∘_)

  reverse : ∀ {A : Set} → List A → List A
  reverse []       = []
  reverse (x ∷ xs) = reverse xs ++ (x ∷ [])

  -- hint: you might want to introduce an extra lemma to prove this.
  
  reverse-tail : forall {A} -> (x : A) -> (xs : List A) -> reverse ( xs ++ x ∷ [] ) ≡ x ∷ (reverse xs)
  reverse-tail x [] = refl
  reverse-tail x (x₁ ∷ xs) = begin
      reverse (xs ++ x ∷ []) ++ x₁ ∷ []
    ≡⟨ cong (_++ x₁ ∷ []) (reverse-tail x xs) ⟩
      x ∷ reverse xs ++ x₁ ∷ []
    ∎

  reverse-involutive-lemma : forall {A} -> (xs : List A) -> reverse (reverse xs) ≡ xs
  reverse-involutive-lemma [] = refl
  reverse-involutive-lemma (x ∷ xs) = begin
      reverse (reverse xs ++ x ∷ [])
    ≡⟨ reverse-tail x (reverse xs) ⟩
      x ∷ reverse (reverse xs)
    ≡⟨ cong (x ∷_) (reverse-involutive-lemma xs) ⟩ 
      x ∷ xs
    ∎

  reverse-involutive : ∀ {A : Set} → reverse {A} ∘ reverse {A} ≡ id
  reverse-involutive = extensionality reverse-involutive-lemma

  -- bonus: fast-reverse-involutive
  -- this is only for practice, not part of the homework this week

  fast-reverse : ∀ {A : Set} → List A → List A
  fast-reverse = helper []
    module FastReverse where
    helper : ∀ {A : Set} → List A → List A → List A
    helper res []       = res
    helper res (x ∷ xs) = helper (x ∷ res) xs


  reverse-helper : ∀ {A : Set} (xs ys : List A) -> FastReverse.helper {A} xs ys ≡ reverse ys ++ xs
  reverse-helper {A} xs [] = refl
  reverse-helper {A} xs (x ∷ ys) = 
    begin
      FastReverse.helper {A} (x ∷ xs) ys
    ≡⟨ reverse-helper (x ∷ xs) ys ⟩
      reverse ys ++ (x ∷ [] ++ xs)
    ≡⟨ sym (problem-1.++-assoc (reverse ys) (x ∷ []) xs) ⟩ 
      (reverse ys ++ x ∷ []) ++ xs
    ∎

  ++-identityʳ : ∀ {A : Set} (xs : List A) → xs ++ [] ≡ xs
  ++-identityʳ [] = refl
  ++-identityʳ (x ∷ xs) =
    begin
      x ∷ (xs ++ [])
    ≡⟨ cong (x ∷_) (++-identityʳ xs) ⟩
      x ∷ xs
    ∎

  reverse-equal : ∀ {A : Set} (xs : List A) -> fast-reverse xs ≡ reverse xs
  reverse-equal {A} xs =
    begin
      FastReverse.helper {A} [] xs
    ≡⟨ reverse-helper [] xs ⟩
      reverse xs ++ []
    ≡⟨ ++-identityʳ (reverse xs) ⟩
      reverse xs
    ∎

  fast-reverse-involutive : ∀ {A : Set}
    → fast-reverse {A} ∘ fast-reverse {A} ≡ id
  fast-reverse-involutive = extensionality λ xs ->
    begin
      fast-reverse (fast-reverse xs)
    ≡⟨ reverse-equal (fast-reverse xs) ⟩
      reverse (fast-reverse xs)
    ≡⟨ cong reverse (reverse-equal xs) ⟩
      reverse (reverse xs)
    ≡⟨ reverse-involutive-lemma xs ⟩
      xs
    ∎