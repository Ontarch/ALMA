------------------------------------------------------------------------
-- Depth-bounded truncation of LayeredEqGen
--
-- LayeredEqGen is coinductive and hence infinite; this module provides
-- its finite truncation at every depth n, the projection from the
-- infinite relation, and monotonicity in n. Downstream proofs can then
-- reason by induction on n rather than by guarded coinduction.
--
-- LayeredEqGen 的深度有界截断
--
-- LayeredEqGen 是余归纳的、因而无穷；本模块给出它在每个深度 n 处的
-- 有限截断、从无穷关系的投影，以及截断在 n 上的单调性。下游证明因此
-- 可对 n 作归纳，而不必使用受守卫的余归纳。
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module Equivalence.LayeredEqGenDepth where

open import Agda.Primitive using (_⊔_)
open import Agda.Builtin.Sigma using (Σ; _,_)
open import Data.Unit.Polymorphic.Base using (⊤; tt)
open import Data.Product.Base using (proj₁; proj₂)
open import Data.Nat.Base using (ℕ; zero; suc; _≤_; z≤n; s≤s)

open import Base.IndexedMType using (fst; snd)
open import Equivalence.Core using (LayeredEqGen)

------------------------------------------------------------------------
-- Finite truncation of LayeredEqGen
--
-- LayeredEqGen 的有限截断

module LayeredEqGen-Depth
    {a b c} {X : Set a}
    {Obs : X → Set b}
    {step : (x : X) → Obs x → X}
    {layer : X → X → Set c}
    {obs-map : (x y : X) → layer x y → Obs x → Obs y} where

  -- obs-map is a function rather than an equality, so the recursive
  -- case needs no subst: the target-side observation is obtained by
  -- applying obs-map directly.
  --
  -- obs-map 是函数而非等式，故递归情形不需要 subst：目标侧观察由
  -- obs-map 直接给出。
  LE-depth : (n : ℕ) → (x y : X) → Set (a ⊔ b ⊔ c)
  LE-depth zero    x y = ⊤
  LE-depth (suc n) x y =
    Σ (layer x y) (λ l →
      ∀ (s : Obs x) → LE-depth n
        (step x s)
        (step y (obs-map x y l s)))

  le→LE-depth : ∀ {x y} → LayeredEqGen Obs step layer obs-map x y
              → ∀ n → LE-depth n x y
  le→LE-depth p zero    = tt
  le→LE-depth p (suc n) =
    ( p .fst
    , λ s → le→LE-depth (p .snd s) n )

  LE-depth-mono : ∀ {m n} (m≤n : m ≤ n) {x y : X}
                → LE-depth n x y → LE-depth m x y
  LE-depth-mono z≤n       p = tt
  LE-depth-mono (s≤s m≤n) p =
    ( proj₁ p
    , λ s → LE-depth-mono m≤n (proj₂ p s) )
