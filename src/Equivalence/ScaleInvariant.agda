------------------------------------------------------------------------
-- Scale invariance
--
-- LayeredEq at the trivial layer ⊤. This is the coinductive form of
-- scale invariance / transformation invariance / renormalisation-group
-- fixed points.
--
-- 尺度不变性
--
-- 平凡层 ⊤ 处的 LayeredEq。这是尺度不变性 / 变换不变性 / 重整化群
-- 不动点的余归纳形式。
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module Equivalence.ScaleInvariant where

open import Agda.Primitive using (Level; _⊔_; lzero)
open import Agda.Builtin.Equality using (_≡_)
open import Data.Unit.Polymorphic.Base using (⊤; tt)
open import Relation.Binary.PropositionalEquality.Core using (sym; cong)
open import Relation.Binary.PropositionalEquality using (module ≡-Reasoning)
open ≡-Reasoning

open import Base.IndexedMType using (fst; snd)
open import Equivalence.Core using (LayeredEq)

------------------------------------------------------------------------
-- Degeneration: trivialise layer
--
-- ScaleInvariant is LayeredEq at the trivial layer ⊤.
--
-- 退化：把 layer 平凡化
--
-- ScaleInvariant 是平凡层 ⊤ 处的 LayeredEq。

ScaleInvariant
    : {a b : Level} {X : Set a} {Obs : Set b}
      (step : X → Obs → X) (x y : X) → Set b
ScaleInvariant step x y = LayeredEq {c = lzero} _ step (λ _ _ → ⊤) x y

------------------------------------------------------------------------
-- Scale invariance and renormalisation-group fixed points
--
-- 尺度不变性与重整化群不动点

module ScaleInvariance
    {a b s} {X : Set a} {Obs : Set b} {S : Set s}
    (step  : X → Obs → X)
    (scale : X → S → X)
    (comm  : ∀ x ob p → step (scale x p) ob ≡ scale (step x ob) p)
  where

  -- Forward direction: rewrite the composite step via comm and recurse.
  --
  -- 正向：经 comm 重写复合 step 并递归。
  scale-invariant : ∀ x p → ScaleInvariant step x (scale x p)
  scale-invariant x p .fst = tt
  scale-invariant x p .snd ob
    rewrite comm x ob p = scale-invariant (step x ob) p

  IsFixedPoint : X → Set (a ⊔ s)
  IsFixedPoint x = ∀ p → scale x p ≡ x

  -- comm preserves the fixed-point property along step.
  --
  -- comm 保证不动点性质沿 step 保持。
  fixed-point-preserved
    : ∀ x → IsFixedPoint x → ∀ ob → IsFixedPoint (step x ob)
  fixed-point-preserved x fp ob p =
    begin
      scale (step x ob) p
    ≡⟨ sym (comm x ob p) ⟩
      step (scale x p) ob
    ≡⟨ cong (λ z → step z ob) (fp p) ⟩
      step x ob
    ∎

  fixed-point-invariant
    : ∀ x → IsFixedPoint x → ScaleInvariant step x x
  fixed-point-invariant x fp .fst = tt
  fixed-point-invariant x fp .snd ob =
    fixed-point-invariant (step x ob) (fixed-point-preserved x fp ob)
