------------------------------------------------------------------------
-- Shape stability under strictStep-suc
--
-- Abstract properties of containers that are preserved by one strict step:
-- singleton shape sets stay singletons
-- distinct shapes stay distinct
-- These are general results about strictStep-suc, not tied to any concrete tower
--
-- strictStep-suc 下的形状稳定性
--
-- 关于容器形状的抽象性质在一步严格提升下的保持：
-- 单点形状集保持单点
-- 相异形状保持相异
-- 这是关于 strictStep-suc 的一般结果，不依赖任何具体塔
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module SecondPass.StrictLiftShape where

open import Agda.Primitive using (Level; _⊔_; lsuc; Setω)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Level using (Lift; lift; lower)
open import Relation.Binary.PropositionalEquality.Core using (cong; sym; trans)
open import Relation.Nullary using (¬_)
open import Data.Product.Base using (∃; _,_)

open import Categories.Category.Core using (Category)
open import Categories.Functor.Core using (Functor)

open import Cosmos.ContCategory using (ContCat)
open import Cosmos.ContCategoryLemmas using (ShapeOf)
open import SecondPass.StrictLift using (StrictLayer; strictStep-suc; lift-lower)
open StrictLayer

variable
  o h e s p : Level

-- A container has distinct shapes if some object carries two different shapes
-- 容器有相异形状：某对象上有两个不同形状
HasDistinctShapes : (C : Category o h e)
                  → (FC : Functor C (ContCat s p)) → Set (o ⊔ s)
HasDistinctShapes C FC =
  ∃ λ (A : Category.Obj C) →
  ∃ λ (s₁ : ShapeOf FC A) →
  ∃ λ (s₂ : ShapeOf FC A) → ¬ (s₁ ≡ s₂)

-- A container has singleton shapes if every object carries at most one shape
-- 容器有单点形状：每个对象至多一个形状
HasSingletonShapes : (C : Category o h e)
                   → (Functor C (ContCat s p)) → Set (o ⊔ s)
HasSingletonShapes C FC =
  ∀ (A : Category.Obj C) (s t : ShapeOf FC A) → s ≡ t

-- Definitional unfolding of the shape type at one step
-- 一步提升下形状类型的定义性展开
step-shape-reduces
  : ∀ {o h e s p} (L : StrictLayer o h e s p)
    (A : Category.Obj (C L))
    (s₀ : ShapeOf (FC L) A)
  → ShapeOf (FC (strictStep-suc L)) (A , s₀)
    ≡ Lift (lsuc (s ⊔ p)) (ShapeOf (FC L) A)
step-shape-reduces L A s₀ = refl

-- Singleton shapes are preserved by one strict step
-- 单点形状在一步严格提升下保持
singleton-preserved-step
  : ∀ {o h e s p} (L : StrictLayer o h e s p)
  → HasSingletonShapes (C L) (FC L)
  → HasSingletonShapes (C (strictStep-suc L)) (FC (strictStep-suc L))
singleton-preserved-step L sing (A , s₀) u v =
  trans (sym (lift-lower u))
    (trans (cong lift (sing (A) (lower u) (lower v)))
           (lift-lower v))

-- Distinct shapes are preserved by one strict step
-- 相异形状在一步严格提升下保持
distinct-preserved-step
  : ∀ {o h e s p} (L : StrictLayer o h e s p)
  → HasDistinctShapes (C L) (FC L)
  → HasDistinctShapes (C (strictStep-suc L)) (FC (strictStep-suc L))
distinct-preserved-step L (A , s₁ , s₂ , ¬eq) =
  (A , s₁) , lift s₁ , lift s₂ , λ eq → ¬eq (cong lower eq)

-- Bundled interface: both properties are preserved under a strict step
-- 打包接口：两种性质在严格提升下都保持
record ShapeStabilityUnderStep : Setω where
  field
    singleton-preserved : ∀ {o h e s p} (L : StrictLayer o h e s p)
                        → HasSingletonShapes (C L) (FC L)
                        → HasSingletonShapes (C (strictStep-suc L))
                                            (FC (strictStep-suc L))
    distinct-preserved  : ∀ {o h e s p} (L : StrictLayer o h e s p)
                        → HasDistinctShapes (C L) (FC L)
                        → HasDistinctShapes (C (strictStep-suc L))
                                           (FC (strictStep-suc L))

shape-stability : ShapeStabilityUnderStep
shape-stability = record
  { singleton-preserved = singleton-preserved-step
  ; distinct-preserved  = distinct-preserved-step
  }
