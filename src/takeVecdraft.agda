{-# OPTIONS --cubical-compatible --safe #-}

module takeVecdraft where

open import Data.Fin.Base using (Fin; zero; suc; inject≤; _↑ˡ_; toℕ; fromℕ<; reduce≥; _↑ʳ_; inject₁; pred)
open import Data.Nat.Base using (ℕ; zero; suc; _+_; _≤_; z≤n; s≤s; _∸_; _<_;  s≤s⁻¹; _⊓_)
open import Data.Nat.Properties using (≤-refl; ≤-trans; m≤m+n; +-assoc; ∸-monoˡ-≤; m∸n≤m)
open import Data.Fin.Properties using (splitAt-≥)
open import Data.Product using (proj₁; proj₂)
open import Data.Vec.Base
open import Data.List.Base as List
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

take-++ : ∀ {A : Set} {m n : ℕ} → (xs : Vec A m) → (ys : Vec A n) → Data.Vec.Base.take m (xs Data.Vec.Base.++ ys) ≡ xs
take-++ [] ys = refl
take-++ (x ∷ xs) ys = cong (x ∷_) (take-++ xs ys)

-- When you append 2 vectors together and then take more than the length of the first, you get the first vector back plus a bit of the second vector

take-++-more : ∀ {A : Set} {m n k : ℕ} →
  (xs : Vec A m) →
  (ys : Vec A n) →
  (p : ℕ) →
  (m≤p : m ≤ p) →
  (m+n≡p+k∸n : m + n ≡ p + (n ∸ k)) → 
  (n≡k+n-k : n ≡ k + (n ∸ k)) → 
  toList (Data.Vec.Base.take p (cast m+n≡p+k∸n (xs Data.Vec.Base.++ ys))) ≡ toList (xs Data.Vec.Base.++  (Data.Vec.Base.take k (cast n≡k+n-k ys)))
take-++-more = {!   !}

------------------------------------------------------------------------
-- Take : Other def of take
takeNat : ∀ {A : Set} {m : ℕ} → (k : ℕ) → Vec A m → Vec A (k ⊓ m)
takeNat zero xs = []
takeNat (suc k) [] = []
takeNat (suc k) (x ∷ xs) = x ∷ takeNat k xs

takeNat-++-more : ∀ {A : Set} {m n : ℕ} → (xs : Vec A m) → (ys : Vec A n) → (p : ℕ) → m ≤ p
                  → toList (takeNat p (xs Data.Vec.Base.++ ys)) ≡ toList (xs Data.Vec.Base.++ takeNat (p ∸ m) ys)
takeNat-++-more {m = zero} [] ys p z≤n = refl
takeNat-++-more {m = suc m} {n = n} (x ∷ xs) ys (suc p) m≤p = cong (λ l → x List.∷ l ) (takeNat-++-more xs ys p (s≤s⁻¹ m≤p))
