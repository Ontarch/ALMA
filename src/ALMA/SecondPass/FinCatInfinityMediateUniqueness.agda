------------------------------------------------------------------------
-- Weak uniqueness of the mediating morphism
--
-- Any h satisfying the triangle equation against a cocone g agrees
-- with mediate on every colimit-cocone component. This is weak
-- uniqueness: it does not assert h ≈ mediate directly, only that the
-- composites with colimitCocone tower m are _≈⇒ℱX_-equivalent.
--
-- 中介态射的弱唯一性
--
-- 任何相对余锥 g 满足三角等式的 h，都与 mediate 在余极限余锥的每个
-- 分量上一致。这是弱唯一性：它不断言 h ≈ mediate，而只断言与
-- colimitCocone tower m 的复合在 _≈⇒ℱX_ 下等价。
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module ALMA.SecondPass.FinCatInfinityMediateUniqueness where

open import Data.Nat using (ℕ)

open import Categories.Functor using (id)

open import ALMA.SecondPass.Cosmos using (Cosmos)
open import ALMA.SecondPass.FinCatInfinity using (FinCat∞; TrivialFC∞)
open import ALMA.SecondPass.FinCatInfinityColimit using
  (CompatibleTower; towerColimit; _⇒ℱX[_]_; comp⇒ℱX; module TowerShapeFunctors)
open import ALMA.SecondPass.FinCatInfinityColimitUniversal using
  (colimitCocone; _≈⇒ℱX_; ≈⇒ℱX-sym; ≈⇒ℱX-trans)
open import ALMA.SecondPass.FinCatInfinityMediate using (mediate; mediate-triangle)

open _⇒ℱX[_]_
open _≈⇒ℱX_
open CompatibleTower

-- Weak uniqueness: any h satisfying the triangle equation is
-- _≈⇒ℱX_-equivalent to mediate on every cocone component
--
-- 弱唯一性：任何满足三角等式的 h 都与 mediate 在余锥的每个分量上
-- _≈⇒ℱX_-等价
mediate-unique-weak
  : ∀ (tower : CompatibleTower) (Y : Cosmos FinCat∞ TrivialFC∞)
  → (g : ∀ m → CompatibleTower.seq tower m
        ⇒ℱX[ TowerShapeFunctors.S-proj m ] Y)
  → (h : towerColimit tower ⇒ℱX[ id ] Y)
  → (h-tri : ∀ m → comp⇒ℱX h (colimitCocone tower m) ≈⇒ℱX g m)
  → ∀ m
  → comp⇒ℱX h (colimitCocone tower m)
    ≈⇒ℱX
    comp⇒ℱX (mediate tower Y g) (colimitCocone tower m)
mediate-unique-weak tower Y g h h-tri m =
  ≈⇒ℱX-trans (h-tri m) (≈⇒ℱX-sym (mediate-triangle tower Y g m))
