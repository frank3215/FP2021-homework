module HW18 where

-- how to input '≗': type \=o
-- Tips: 'f ≗ g' is the same as '∀ xs → f x ≡ g x'

open import Function using (_∘_)
open import Data.List using ([]; _∷_; foldr; map)
open import Data.List.Properties using (foldr-fusion; map-is-foldr)

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≗_; refl; trans; sym; cong; cong-app; subst)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)

{-
foldr-fusion : ∀ (h : B → C) {f : A → B → B} {g : A → C → C} (e : B) →
               (∀ x y → h (f x y) ≡ g x (h y)) →
               h ∘ foldr f e ≗ foldr g (h e)

map-is-foldr : {f : A → B} → map f ≗ foldr (λ x ys → f x ∷ ys) []
-}

lemma : ∀ {A : Set} {B : Set} {C : Set}
  → (f : A → B)
  → (_⊕_ : B → C → C)
  → (e : C)
  → (∀ x y → foldr _⊕_ e (f x ∷ y) ≡ (f x ⊕ foldr _⊕_ e y))

lemma f _⊕_ e x y = refl

foldr-map-fusion : ∀ {A : Set} {B : Set} {C : Set}
  → (f : A → B)
  → (_⊕_ : B → C → C)
  → (e : C)
  → foldr _⊕_ e ∘ map f ≗ foldr (λ a r → f a ⊕ r) e
foldr-map-fusion {A} {B} {C} f _⊕_ e xs =
  begin
    foldr _⊕_ e (map f xs)
  ≡⟨ cong (foldr _⊕_ e) (map-is-foldr xs) ⟩
    ( foldr _⊕_ e ∘ foldr (λ z → f z ∷_) [] ) xs
  {-
    h ∘ foldr f e ≗ foldr g (h e)
    h = foldr _⊕_ e
    f = (λ z → f z ∷_)
    e = []
    g = (λ z → _⊕_ (f z))
    (∀ x y → h (f x y) ≡ g x (h y))
    (∀ x y → foldr _⊕_ e (f x ∷ y) ≡ f x ⊕ foldr _⊕_ e y)
  -}
  ≡⟨ foldr-fusion (foldr _⊕_ e) {f = (λ z → f z ∷_)} {g = (λ z → _⊕_ (f z))} [] (lemma f _⊕_ e) xs ⟩
    foldr (λ z → _⊕_ (f z)) e xs
  ∎
{-
foldr-map-fusion f _⊕_ e [] = refl
foldr-map-fusion f _⊕_ e (x ∷ xs) =
  begin
    (f x ⊕ foldr _⊕_ e (map f xs))
  ≡⟨ cong (f x ⊕_) (foldr-map-fusion f _⊕_ e xs) ⟩
    (f x ⊕ foldr (λ z → _⊕_ (f z)) e xs)
  ∎
-}


map-composition : ∀ {A : Set} {B : Set} {C : Set}
  → (f : B → C)
  → (g : A → B)
  → map f ∘ map g ≗ map (f ∘ g)
map-composition {A} {B} {C} f g xs =
  begin
    map f (map g xs)
  ≡⟨ map-is-foldr {f = f} (map g xs) ⟩
    foldr (λ z → f z ∷_ ) [] (map g xs)
  ≡⟨ foldr-map-fusion g (λ z → f z ∷_ ) [] xs ⟩
    foldr (λ z → _∷_ (f (g z))) [] xs
  ≡⟨ sym (map-is-foldr {f = f ∘ g} xs) ⟩
    map (f ∘ g) xs
  ∎
{-
map-composition f g [] = refl
map-composition f g (x ∷ xs) =
  begin
    f (g x) ∷ map f (map g xs)
  ≡⟨ cong (f (g x) ∷_) (map-composition f g xs) ⟩
    f (g x) ∷ map (λ z → f (g z)) xs
  ∎
-}