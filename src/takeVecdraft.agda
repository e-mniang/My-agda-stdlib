{-# OPTIONS --cubical-compatible --safe #-}

module takeVecdraft where

open import Data.Fin.Base using (Fin; zero; suc; inject≤; _↑ˡ_; toℕ; fromℕ<″)
open import Data.Nat.Base using (ℕ; zero; suc; _+_; _≤_; z≤n; s≤s; _∸_; _<_)
open import Data.Nat.Properties using (≤-refl; ≤-trans; m≤m+n; +-assoc)
open import Data.Vec.Base
open import Data.Vec.Properties using (map-replicate; zipWith-replicate; padRight-trans; map-++; lookup-++ˡ)
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
    m n p : ℕ
 
------------------------------------------------------------------------

-- When you append 2 vectors together and then take the length of the first, you get the first vector back

take-++ : ∀ {A : Set} {m n : ℕ} → (xs : Vec A m) → (ys : Vec A n) → take m (xs ++ ys) ≡ xs
take-++ [] ys = refl
take-++ (x ∷ xs) ys = cong (x ∷_) (take-++ xs ys)

-- When you append 2 vectors together and then take the length or less than the length of the first, you get the first vector back or less than the first
take-++-more : ∀ {A : Set} {m k n : ℕ} (p : ℕ) → (xs : Vec A m) → (ys : Vec A n) → (m≤p : m ≤ p) →
  {p≡m+k : p ≡ m + k} → {m+n=pkn : m + n ≡ p + (n ∸ k)} → {n=k+n-k : n ≡ k + (n ∸ k)} →
  cast p≡m+k (take p (cast m+n=pkn (xs ++ ys))) ≡  xs ++ take k (cast n=k+n-k  ys)
take-++-more p [] ys z≤n = {!   !}
take-++-more p (x ∷ xs) ys (s≤s m≤p) = {!   !}

------------------------------------------------------------------------
-- Take : Other def of take
take' : ∀ {A : Set} (k : ℕ) {m : ℕ} → k ≤ m → Vec A m → Vec A k
take' zero p xs = []
take' (suc k) (s≤s p) (x ∷ xs) = x ∷ take' k p xs

takeFin : ∀ {A : Set} {m : ℕ} → (k : Fin (suc m)) → Vec A m → Vec A (toℕ k)
takeFin {m = zero} zero [] = []
takeFin {m = suc m} zero (x ∷ xs) = []
takeFin {m = suc m} (suc k') (x ∷ xs) = x ∷ takeFin k' xs


takeFin-++-more : ∀ {A : Set} {m k n : ℕ} (p : ℕ) → (xs : Vec A m) → (ys : Vec A n) → (m≤p : m ≤ p) → (p : Fin (suc (m + n))) →
                  takeFin p (xs ++ ys) ≡ takeFin (p ∸ m) ys

takeFin-++-more = ?

{-
take : ∀ m {n} → Vec A (m + n) → Vec A m
take m xs = proj₁ (splitAt m xs)
-}

{-
_≈[_]_ : ∀ {n m} → Vec A n → .(eq : n ≡ m) → Vec A m → Set _
xs ≈[ eq ] ys = cast eq xs ≡ ys
-}