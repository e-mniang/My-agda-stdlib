------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of padRight for Vec
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module truncatePropertiesDraftBis where

open import Data.Fin.Base using (Fin; zero; suc; inject≤)
open import Data.Nat.Base using (ℕ; zero; suc; _+_; _≤_; z≤n; s≤s; s≤s⁻¹; _∸_)
open import Data.Nat.Properties using (≤-refl; ≤-trans; m≤m+n; m≤n⇒m≤1+n; m≤n⇒∃[o]m+o≡n)
open import Data.Product.Base using (proj₂)
open import Data.Vec.Base
open import Data.Vec.Properties using (truncate-trans; take++drop≡id; truncate≡take; take≡truncate; take-map; map-cast; take-zipWith)
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
truncate-map : (f : A → B) (m : ℕ) (m≤n : m ≤ n) (xs : Vec A n) →
  map f (truncate m≤n xs) ≡ truncate m≤n (map f xs)
truncate-map {n = n} f m m≤n xs =
  begin
    map f (truncate m≤n xs)     ≡⟨ cong (map f) (truncate≡take m≤n xs eq) ⟩
    map f (take m (cast eq xs)) ≡⟨ take-map f m _ ⟨
    take m (map f (cast eq xs)) ≡⟨ cong (take m) (map-cast f eq xs) ⟩
    take m (cast eq (map f xs)) ≡⟨ truncate≡take m≤n (map f xs) eq ⟨
    truncate m≤n (map f xs) ∎
 where
   .eq : n ≡ m + (n ∸ m)
   eq = sym (proj₂ (m≤n⇒∃[o]m+o≡n m≤n))

------------------------------------------------------------------------
-- Interaction with zipWith

-- When both vectors have the same original length
truncate-zipWith : (f : A → B → C) (m≤n : m ≤ n) (xs : Vec A n) (ys : Vec B n) →
  truncate m≤n (zipWith f xs ys) ≡ zipWith f (truncate m≤n xs) (truncate m≤n ys)
truncate-zipWith f z≤n xs ys = refl
truncate-zipWith f (s≤s m≤n) (x ∷ xs) (y ∷ ys) =
  cong (f x y ∷_) (truncate-zipWith f m≤n xs ys)

-- When vectors have different original lengths
truncate-zipWith-truncate : ∀ (f : A → B → C) (o≤m : o ≤ m) (m≤n : m ≤ n)
  (xs : Vec A n) (ys : Vec B m) →
  let o≤n = ≤-trans o≤m m≤n in
  truncate o≤m (zipWith f (truncate m≤n xs) ys) ≡
  zipWith f (truncate o≤n xs) (truncate o≤m ys)
truncate-zipWith-truncate f o≤m m≤n xs ys =
  let o≤n = ≤-trans o≤m m≤n in
  trans (truncate-zipWith f o≤m (truncate m≤n xs) ys)
  (cong (λ zs → zipWith f zs (truncate o≤m ys)) ((sym (truncate-trans o≤m m≤n xs))))

------------------------------------------------------------------------
-- Interaction with zipWith (using take)
--- When both vectors have the same original length
zipWith-truncate : ∀ (f : A → B → C) {p q : ℕ} (xs : Vec A (p + q)) (ys : Vec B (p + q)) →
  let p≤p+q = m≤m+n p q in
  zipWith f (truncate p≤p+q xs) (truncate p≤p+q ys) ≡ truncate p≤p+q (zipWith f xs ys)
zipWith-truncate f {p} {q} xs ys =
  let p≤p+q = m≤m+n p q in
  begin
    zipWith f (truncate p≤p+q xs) (truncate p≤p+q ys) ≡⟨ cong₂ (zipWith f) (take≡truncate p xs) (take≡truncate p ys) ⟨
    zipWith f (take p xs) (take p ys)                 ≡⟨ take-zipWith f xs ys ⟨
    take p (zipWith f xs ys)                          ≡⟨ take≡truncate p (zipWith f xs ys) ⟩
    truncate p≤p+q (zipWith f xs ys) ∎

--- When vectors have different original lengths
module _  (f : A → B → C) {o m n : ℕ} (xs : Vec A (o + m + n)) (ys : Vec B (o + m)) where
  private
    o≤o+m = m≤m+n o m
    o+m≤o+m+n = m≤m+n (o + m) n
    o≤o+m+n = ≤-trans (m≤m+n o m) (m≤m+n (o + m) n)

  zipWith-truncate₁ : zipWith f (truncate o≤o+m+n xs) (truncate (o≤o+m) ys) ≡
    truncate (o≤o+m) (zipWith f (truncate (o+m≤o+m+n) xs) ys)
  zipWith-truncate₁ =
    trans (cong (λ zs → zipWith f zs (truncate (o≤o+m) ys)) (truncate-trans (o≤o+m) (o+m≤o+m+n) xs))
    (zipWith-truncate f (truncate (o+m≤o+m+n) xs) ys)


------------------------------------------------------------------------
-- Interaction with updateAt
truncate-updateAt : (f : A → A) (m≤n : m ≤ n) (xs : Vec A n) (i : Fin m) →
                    updateAt (truncate m≤n xs) i f ≡ truncate m≤n (updateAt xs (inject≤ i m≤n) f)
truncate-updateAt f (s≤s _  ) (_ ∷ _ ) zero = refl
truncate-updateAt f (s≤s m≤n) (x ∷ xs) (suc i) = cong (x ∷_) (truncate-updateAt f m≤n xs i)

-- Interaction with updateAt v2 
-- updateAt and take : 
take-updateAt : (f : A → A) {m n : ℕ} (xs : Vec A (m + n)) (i : Fin m) →
                updateAt (take m xs) i f ≡ take m (updateAt xs (inject≤ i (m≤m+n m n)) f)
take-updateAt f (_ ∷ _ ) zero    = refl
take-updateAt f (x ∷ xs) (suc i) = cong (x ∷_) (take-updateAt f xs i)

-- updateAt and truncate
module _  (f : A → A) {p q : ℕ} (xs : Vec A (p + q)) (i : Fin p) where
  private
    p≤p+q : p ≤ p + q 
    p≤p+q = m≤m+n p q
    i′ : Fin (p + q)
    i′ = inject≤ i p≤p+q
  
  updateAt-truncate : updateAt (truncate p≤p+q xs) i f ≡ truncate p≤p+q (updateAt xs i′ f)
  updateAt-truncate = begin
    updateAt (truncate p≤p+q xs) i f ≡⟨ cong (λ l → updateAt l i f) (sym (take≡truncate p xs)) ⟩
    updateAt (take p xs) i f          ≡⟨ take-updateAt f xs i ⟩
    take p (updateAt xs i′ f)         ≡⟨ take≡truncate p (updateAt xs i′ f) ⟩
    truncate p≤p+q (updateAt xs i′ f) ∎               

------------------------------------------------------------------------
-- Interaction with drop
truncate++drop≡id : (xs : Vec A (m + n)) → truncate (m≤m+n m n) xs ++ drop m xs ≡ xs
truncate++drop≡id {m = m} {n} xs = begin
  truncate (m≤m+n m n) xs ++ drop m xs ≡⟨ cong (_++ drop m xs) (take≡truncate m xs) ⟨
  take m xs ++ drop m xs               ≡⟨ take++drop≡id m xs ⟩
  xs ∎
