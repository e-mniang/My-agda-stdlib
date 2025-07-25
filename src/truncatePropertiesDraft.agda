------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of padRight for Vec
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module truncatePropertiesDraft where

open import Data.Fin.Base using (Fin; zero; suc; inject≤)
open import Data.Nat.Base using (ℕ; zero; suc; _+_; _≤_; z≤n; s≤s; s≤s⁻¹)
open import Data.Nat.Properties using (≤-refl; ≤-trans; m≤m+n; m≤n⇒m≤1+n)
open import Data.Vec.Base
open import Data.Vec.Properties using (map-replicate; zipWith-replicate; truncate-trans; take++drop≡id; truncate≡take; take≡truncate; take-map; map-cast; take-zipWith)
open import Function.Base using (_∘_; _$_)
open import Level using (Level)
open import Relation.Binary.PropositionalEquality.Core
  using (_≡_; refl; cong; sym; trans; subst)
open import Relation.Binary.PropositionalEquality.Properties
  using (module ≡-Reasoning)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl; cong; cong₂)
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

-- Interaction with map V2 (using take)
truncate-mapV2 : ∀ (f : A → B) (m : ℕ) (m≤n : m ≤ n) (xs : Vec A n) .(eq : n ≡ m + o) → 
                map f (truncate m≤n xs) ≡ truncate m≤n (map f xs)
truncate-mapV2 f m m≤n xs eq = 
  begin
    map f (truncate m≤n xs) ≡⟨ cong (λ l → map f (l)) (truncate≡take m≤n xs eq) ⟩
    map f (take m (cast eq xs)) ≡⟨ sym (take-map f m ((cast eq xs))) ⟩
    take m (map f (cast eq xs)) ≡⟨ cong (λ l → take m l) ((map-cast f eq xs)) ⟩
    take m (cast eq (map f xs)) ≡⟨ (sym (truncate≡take m≤n (map f xs) eq)) ⟩
    truncate m≤n (map f xs) ∎

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
-- Interaction with zipWith V2 (using take)

---
truncate-zipWithV2 : ∀ (f : A → B → C) (m n : ℕ) (xs : Vec A (m + n)) (ys : Vec B (m + n)) → 
                    zipWith f (truncate (m≤m+n m n) xs) (truncate (m≤m+n m n) ys) ≡
                   truncate (m≤m+n m n) (zipWith f xs ys)
truncate-zipWithV2 f m n xs ys = 
  begin
    zipWith f (truncate (m≤m+n m n) xs) (truncate (m≤m+n m n) ys) ≡⟨ cong₂ (λ l → zipWith f (l)) (sym (take≡truncate m xs)) (sym (take≡truncate m ys)) ⟩
    zipWith f (take m xs) (take m ys) ≡⟨ sym (take-zipWith f xs ys) ⟩
    take m (zipWith f xs ys) ≡⟨ take≡truncate m (zipWith f xs ys) ⟩
    truncate (m≤m+n m n) (zipWith f xs ys) ∎  

---
truncate-zipWith₁V2 : ∀ (f : A → B → C) (o m n : ℕ) (xs : Vec A (o + m + n)) (ys : Vec B (o + m)) → 
  zipWith f (truncate (≤-trans (m≤m+n o m) (m≤m+n (o + m) n)) xs) (truncate (m≤m+n o m) ys) ≡ truncate (m≤m+n o m) (zipWith f (truncate (m≤m+n (o + m) n) xs) ys)
truncate-zipWith₁V2 f o m n xs ys = trans (cong (λ zs → zipWith f zs (truncate (m≤m+n o m) ys)) (truncate-trans (m≤m+n o m) (m≤m+n (o + m) n) xs))
                                    (truncate-zipWithV2 f o m (truncate (m≤m+n (o + m) n) xs) ys)


------------------------------------------------------------------------
-- Interaction with updateAt
truncate-updateAt : ∀ (m≤n : m ≤ n) (xs : Vec A n) (f : A → A) (i : Fin m) →
                    updateAt (truncate m≤n xs) i f ≡ truncate m≤n (updateAt xs (inject≤ i m≤n) f)
truncate-updateAt {n = suc _} (s≤s m≤n) (x ∷ xs) f zero = refl
truncate-updateAt {n = suc _} (s≤s m≤n) (x ∷ xs) f (suc i) = cong (x ∷_) (truncate-updateAt m≤n xs f i)

-- Interaction with updateAt v2 
-- updateAt and take : 
take-updateAt : ∀ (m n : ℕ) (xs : Vec A (m + n)) (f : A → A) (i : Fin m) → 
                updateAt (take m xs) i f ≡ take m (updateAt xs (inject≤ i (m≤m+n m n)) f)
take-updateAt .(suc _) n (x ∷ xs) f zero = refl
take-updateAt .(suc _) n (x ∷ xs) f (suc i) = cong (x ∷_) (take-updateAt _ n xs f i)

-- updateAt and truncate
truncate-updateAtV2 : ∀ (m n : ℕ) (xs : Vec A (m + n)) (f : A → A) (i : Fin m) → 
                      updateAt (truncate (m≤m+n m n) xs) i f ≡ truncate (m≤m+n m n) (updateAt xs (inject≤ i (m≤m+n m n)) f)
truncate-updateAtV2 m n xs f i = 
  begin
    updateAt (truncate (m≤m+n m n) xs) i f ≡⟨ cong (λ l → updateAt (l) i f) (sym (take≡truncate m xs)) ⟩
    updateAt (take m xs) i f ≡⟨ take-updateAt m n xs f i ⟩
    take m (updateAt xs (inject≤ i (m≤m+n m n)) f) ≡⟨ take≡truncate m (updateAt xs (inject≤ i (m≤m+n m n)) f) ⟩
    truncate (m≤m+n m n) (updateAt xs (inject≤ i (m≤m+n m n)) f) ∎                 

------------------------------------------------------------------------
-- Interaction with drop V1
truncate++drop≡id : ∀ (m : ℕ) (m≤m+n : m ≤ m + n) (xs : Vec A (m + n)) → truncate m≤m+n xs ++ drop m xs ≡ xs
truncate++drop≡id zero m≤m+n xs = refl
truncate++drop≡id (suc m) (s≤s m≤m+n) (x ∷ xs) = cong (x ∷_) (truncate++drop≡id m m≤m+n xs)

-- Interaction with drop V2
truncate++drop≡idV2 : ∀ (m n : ℕ) (xs : Vec A (m + n)) → truncate (m≤m+n m n) xs ++ drop m xs ≡ xs
truncate++drop≡idV2 m n xs = 
  begin
    truncate (m≤m+n m n) xs ++ drop m xs ≡⟨ cong (_++ drop m xs) (sym (take≡truncate m xs)) ⟩
    take m xs ++ drop m xs ≡⟨ take++drop≡id m xs ⟩
    xs ∎
