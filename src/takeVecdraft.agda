{-# OPTIONS --cubical-compatible --safe #-}

module takeVecdraft where

open import Data.Fin.Base using (Fin; zero; suc; inject≤; _↑ˡ_; toℕ; fromℕ<; reduce≥; _↑ʳ_; inject₁)
open import Data.Nat.Base using (ℕ; zero; suc; _+_; _≤_; z≤n; s≤s; _∸_; _<_)
open import Data.Nat.Properties using (≤-refl; ≤-trans; m≤m+n; +-assoc; ∸-monoˡ-≤; m∸n≤m)
open import Data.Fin.Properties using (splitAt-≥)
open import Data.Product using (proj₁; proj₂)
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

-- When you append 2 vectors together and then take more than the length of the first, you get the first vector back plus a bit of the second vector
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

{-
takeFin-++-more :
 ∀ {A : Set} {m n : ℕ}
 → (xs : Vec A m)
 → (ys : Vec A n)
 → (p : Fin (suc (m + n)))
 → (m≤p : m ≤ toℕ p)
 → takeFin p (xs ++ ys) ≡ cast (toℕ p) (xs ++ takeFin (reduce≥ p m≤p) ys)

takeFin-++-more = ?
-}

takeFin-++-more : ∀ {A : Set} {m n : ℕ}
                → (xs : Vec A m)
                → (ys : Vec A n)
                → (p : Fin (suc (m + n)))
                → (m≤p : m ≤ toℕ p)
                → takeFin p (xs ++ ys) ≡ fromList (toList xs ++ take (toℕ p ∸ m) (toList ys))
takeFin-++-more {A} {m} {n} xs ys p m≤p = ?

{- 
toList : Vec A n → List A
toList []       = List.[]
toList (x ∷ xs) = List._∷_ x (toList xs)

fromList : (xs : List A) → Vec A (List.length xs)
fromList List.[]         = []
fromList (List._∷_ x xs) = x ∷ fromList xs
-}

{- 
-- injection on the left: "i" ↑ˡ n = "i" in Fin (m + n)
infixl 5 _↑ˡ_
_↑ˡ_ : ∀ {m} → Fin m → ∀ n → Fin (m ℕ.+ n)
zero    ↑ˡ n = zero
(suc i) ↑ˡ n = suc (i ↑ˡ n)

-- injection on the right: n ↑ʳ "i" = "n + i" in Fin (n + m)
infixr 5 _↑ʳ_
_↑ʳ_ : ∀ {m} n → Fin m → Fin (n ℕ.+ m)
zero    ↑ʳ i = i
(suc n) ↑ʳ i = suc (n ↑ʳ i)
-}



{-
take : ∀ m {n} → Vec A (m + n) → Vec A m
take m xs = proj₁ (splitAt m xs)
-}

{-
_≈[_]_ : ∀ {n m} → Vec A n → .(eq : n ≡ m) → Vec A m → Set _
xs ≈[ eq ] ys = cast eq xs ≡ ys
-}