------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of padRight for Vec
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module truncatePropertiesDraft where

open import Data.Fin.Base using (Fin; zero; suc; inject≤)
open import Data.Nat.Base using (ℕ; zero; suc; _+_; _≤_; z≤n; s≤s)
open import Data.Nat.Properties using (≤-refl; ≤-trans; m≤m+n)
open import Data.Vec.Base
open import Data.Vec.Properties using (map-replicate; zipWith-replicate; truncate-trans)
open import Function.Base using (_∘_; _$_)
open import Level using (Level)
open import Relation.Binary.PropositionalEquality.Core
  using (_≡_; refl; cong; sym; trans; subst)
open import Relation.Binary.PropositionalEquality.Properties
  using (module ≡-Reasoning)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl; cong)
open Eq.≡-Reasoning

private
  variable
    a b c : Level
    A : Set a
    B : Set b
    C : Set c
    m n p o : ℕ


------------------------------------------------------------------------
-- Interaction with map
truncate-map : ∀ (f : A → B) (m≤n : m ≤ n) (xs : Vec A n) → 
                map f (truncate m≤n xs) ≡ truncate m≤n (map f xs)
truncate-map f z≤n xs = refl
truncate-map f (s≤s m≤n) (x ∷ xs) = cong (f x ∷_) (truncate-map f m≤n xs)

------------------------------------------------------------------------
-- Interaction with zipWith

-- When both vectors have the same original length
truncate-zipWith : ∀ (f : A → B → C) (m≤n : m ≤ n) (xs : Vec A n) (ys : Vec B n) →
                   zipWith f (truncate m≤n xs) (truncate m≤n ys) ≡
                   truncate m≤n (zipWith f xs ys)
truncate-zipWith f z≤n xs ys = refl
truncate-zipWith f (s≤s m≤n) (x ∷ xs) (y ∷ ys) = cong (f x y ∷_) (truncate-zipWith f m≤n xs ys)

-- When vectors have different original lengths
truncate-zipWith₁ : ∀ (f : A → B → C) (o≤m : o ≤ m) (m≤n : m ≤ n) (xs : Vec A n) (ys : Vec B m) →
  zipWith f (truncate (≤-trans o≤m m≤n) xs) (truncate o≤m ys) ≡
  truncate o≤m (zipWith f (truncate m≤n xs) ys)
truncate-zipWith₁ f o≤m m≤n xs ys = trans (cong (λ zs → zipWith f zs (truncate o≤m ys)) (truncate-trans o≤m m≤n xs))
                                    (truncate-zipWith f o≤m (truncate m≤n xs) ys)

------------------------------------------------------------------------
-- Interaction with updateAt
truncate-updateAt : ∀ (m≤n : m ≤ n) (xs : Vec A n) (f : A → A) (i : Fin m) →
                    updateAt (truncate m≤n xs) i f ≡ truncate m≤n (updateAt xs (inject≤ i m≤n) f)
truncate-updateAt {n = suc _} (s≤s m≤n) (x ∷ xs) f zero = refl
truncate-updateAt {n = suc _} (s≤s m≤n) (x ∷ xs) f (suc i) = cong (x ∷_) (truncate-updateAt m≤n xs f i)

------------------------------------------------------------------------
-- Interaction with drop


