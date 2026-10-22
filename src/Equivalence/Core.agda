------------------------------------------------------------------------
-- Core definitions for Equivalence/
--
-- Equivalence/ 的核心定义
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module Equivalence.Core where

open import Agda.Primitive using (Level; _⊔_)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Sigma using (Σ; _,_)
open import Data.Product.Base using (_×_)

open import Base.IndexedMType using (Mᵢ)

------------------------------------------------------------------------
-- Fibre-wise adjunction skeleton: unit and counit are independent
-- round-trip propositions, so a product suffices.
--
-- 纤维层面的伴随骨架：unit 与 counit 是互相独立的往返命题，
-- 故乘积即可。

module _ {a b c d e : Level}
         {S : Set a} {T : Set c} (P : T → Set b) (R : S → Set d)
         {F : Set e} (shape : F → S → T)
         (posL : (f : F) → ∀ {s} → R s → P (shape f s))
         (posR : (f : F) → ∀ {s} → P (shape f s) → R s) where

  Adj-Unit   = ∀ f {s} (r : R s) → posR f (posL f r) ≡ r

  Adj-Counit = ∀ f {s} (p : P (shape f s)) → posL f (posR f p) ≡ p

  _⊣_ : Set (a ⊔ b ⊔ d ⊔ e)
  _⊣_ = Adj-Unit × Adj-Counit

------------------------------------------------------------------------
-- Application of Mᵢ; index is X × X, and the successor advances both
-- components by step.
--
-- 作为 Mᵢ 的应用；索引为 X × X，
-- 后继用 step 同时推进两个分量。

module _ {a b c : Level} {X : Set a}
         (Obs : X → Set b)
         (step : (x : X) → Obs x → X)
         (layer : X → X → Set c)
         (obs-map : (x y : X) → layer x y → Obs x → Obs y) where
  LayeredEqGen : (x y : X) → Set (c ⊔ b)
  LayeredEqGen x y = Mᵢ A B next (x , y)
    where
      A : X × X → Set c
      A (x , y) = layer x y
      B : (i : X × X) → A i → Set b
      B (x , _) _ = Obs x
      next : (i : X × X) (p : A i) (s : B i p) → X × X
      next (x , y) p s = step x s , step y (obs-map x y p s)

------------------------------------------------------------------------
-- Application of Mᵢ; index is Σ I (λ j → X' j × X' j), the successor
-- moves the shared index by next and advances both states with stepI.
--
-- 作为 Mᵢ 的应用；索引为 Σ I (λ j → X' j × X' j)，
-- 后继用 next 移动共享索引，并用 stepI 推进两个状态。

module _ {a b c d : Level}
         {I : Set a} (X' : I → Set b)
         (next : I → I)
         (ObsI : I → Set c)
         (stepI : (i : I) → X' i → ObsI i → X' (next i))
         (layerI : (i : I) → X' i → X' i → Set d) where
  IndexedLayeredEq : (i : I) (x y : X' i) → Set (d ⊔ c)
  IndexedLayeredEq i x y = Mᵢ {I = I'} A B next' (i , x , y)
    where
      I' : Set (a ⊔ b)
      I' = Σ I (λ j → X' j × X' j)
      A : I' → Set d
      A (_ , x , y) = layerI _ x y
      B : (i' : I') → A i' → Set c
      B (i , _ , _) _ = ObsI i
      next' : (i' : I') (p : A i') (s : B i' p) → I'
      next' (i , x , y) p s = next i , stepI i x s , stepI i y s

------------------------------------------------------------------------
-- Specialization at a constant observation family, with obs-map the
-- identity.
--
-- 在常数观察族处的特化，obs-map 为恒等。

LayeredEq : {a b c : Level} {X : Set a}
            (Obs : Set b) (step : X → Obs → X) (layer : X → X → Set c)
            (x y : X) → Set (c ⊔ b)
LayeredEq Obs step layer x y =
  LayeredEqGen (λ _ → Obs) step layer (λ _ _ _ o → o) x y
