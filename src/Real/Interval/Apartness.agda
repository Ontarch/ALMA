------------------------------------------------------------------------
-- Apartness on interval reals
--
-- 区间实数的分离性
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module Real.Interval.Apartness where

open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_]′)
open import Relation.Nullary using (¬_)
open import Relation.Binary.Structures using (IsApartnessRelation)

open import Real.Interval using (RealI)
open import Real.Interval.Equiv using (_≈ℝ_; ≈ℝ-sym)
open import Real.Interval.Order using (_<ℝ_; <-irrefl; <-cotrans)
open import Real.Interval.OrderLaws using (≈-<-resp)

------------------------------------------------------------------------
-- Definition
--
-- 定义

infix 4 _#ℝ_

_#ℝ_ : RealI → RealI → Set
x #ℝ y = (x <ℝ y) ⊎ (y <ℝ x)

------------------------------------------------------------------------
-- Properties
--
-- 性质

-- Apartness is symmetric.
--
-- 分离性是对称的。
#ℝ-sym : ∀ {x y} → x #ℝ y → y #ℝ x
#ℝ-sym (inj₁ x<y) = inj₂ x<y
#ℝ-sym (inj₂ y<x) = inj₁ y<x

-- Apartness is cotransitive.
--
-- 分离性是余传递的。
#ℝ-cotrans : ∀ {x y} → x #ℝ y → (z : RealI) → (x #ℝ z) ⊎ (z #ℝ y)
#ℝ-cotrans {x} {y} (inj₁ x<y) z =
  [ (λ x<z → inj₁ (inj₁ x<z)) , (λ z<y → inj₂ (inj₁ z<y)) ]′
    (<-cotrans {x} {z} {y} x<y)
#ℝ-cotrans {x} {y} (inj₂ y<x) z =
  [ (λ y<z → inj₂ (inj₂ y<z)) , (λ z<x → inj₁ (inj₂ z<x)) ]′
    (<-cotrans {y} {z} {x} y<x)

-- Apartness is irreflexive w.r.t. equivalence.
--
-- 分离性相对等价非自反。
#ℝ-irrefl : ∀ {x y} → x ≈ℝ y → ¬ (x #ℝ y)
#ℝ-irrefl {x} {y} x≈y (inj₁ x<y) = <-irrefl y (≈-<-resp x≈y x<y)
#ℝ-irrefl {x} {y} x≈y (inj₂ y<x) = <-irrefl x (≈-<-resp (≈ℝ-sym x≈y) y<x)

-- The standard apartness-relation structure.
--
-- 标准分离关系结构。
#ℝ-isApartnessRelation : IsApartnessRelation _≈ℝ_ _#ℝ_
#ℝ-isApartnessRelation = record
  { irrefl  = λ {x} {y} x≈y x#y → #ℝ-irrefl {x} {y} x≈y x#y
  ; sym     = λ {x} {y} → #ℝ-sym {x} {y}
  ; cotrans = #ℝ-cotrans
  }

-- Apartness implies non-equality.
--
-- 分离蕴含不相等。
#ℝ⇒≉ : ∀ {x y} → x #ℝ y → ¬ (x ≈ℝ y)
#ℝ⇒≉ {x} {y} x#y x≈y = #ℝ-irrefl {x} {y} x≈y x#y
