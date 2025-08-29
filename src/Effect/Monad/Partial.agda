------------------------------------------------------------------------
-- The Agda standard library
--
-- The partial monad
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Effect.Monad.Partial where

open import Level using (Level; _⊔_; suc)
open import Data.Product using (_×_; Σ; Σ-syntax; _,_)
open import Data.Empty.Polymorphic using (⊥; ⊥-elim)
open import Data.Unit.Polymorphic  using (⊤)

private
  variable
    a ℓ ℓ' : Level
    A B : Set a

------------------------------------------------------------------------
-- The partial monad

record ↯ (A : Set a) (ℓ : Level) : Set (a ⊔ suc ℓ) where
  field
    dom : Set ℓ
    l : dom → A

open ↯

always : A → ↯ A ℓ
always {ℓ = ℓ} a .dom   = ⊤ {ℓ = ℓ}
always a .l _         = a

never : ↯ A ℓ
never {ℓ = ℓ} .dom = ⊥ {ℓ = ℓ}
never .l         = ⊥-elim

↯-map : (A → B) → ↯ A ℓ → ↯ B ℓ
↯-map f x .dom   = x .dom
↯-map f x .l d = f (x .l d)

↯-bind : ↯ A ℓ → (A → ↯ B ℓ') → ↯ B (ℓ ⊔ ℓ')
↯-bind x f .dom            = Σ[ d ∈ x .dom ] (f (x .l d)) .dom
↯-bind x f .l (dx , dfx) = (f (x .l dx)) .l dfx

↯-ap : ↯ (A → B) ℓ → ↯ A ℓ' → ↯ B (ℓ ⊔ ℓ')
↯-ap ff xx .dom            = ff .dom × xx .dom
↯-ap ff xx .l (df , dx)  = ff .l df (xx .l dx)