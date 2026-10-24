------------------------------------------------------------------------
-- Generic obstruction for projective embeddings
--
-- For any embedding rule R and enriched tower over the FinCat n tower,
-- if the layer-0 embedding of some pair of cosmoi collapses to
-- _≈C_-equivalent cosmoi at layer 1, then liftAt 0 cannot separate that
-- pair. Consequently no LiftedLimitStructure along R can have an
-- injective liftAt at layer 0, provided the pair is not already
-- _≈C_-equivalent. This is the common skeleton shared by outer-rule
-- and inner-rule, instantiated in FinCatNOuterObstruction and
-- FinCatNInnerObstruction. The parameter m encodes n = suc (suc m),
-- so n ≥ 2 holds definitionally
--
-- 投影式嵌入的泛型障碍
--
-- 对任意嵌入规则 R 与 FinCat n 塔上的丰富塔，若某对宇宙在层 0 的
-- 嵌入在层 1 上塌缩为 _≈C_ 等价的宇宙，则 liftAt 0 无法区分该对。
-- 从而，只要该对本身不 _≈C_ 等价，沿 R 的 LiftedLimitStructure
-- 就不可能有单射的 liftAt 0。这是 outer-rule 与 inner-rule 共享的
-- 公共骨架，分别在 FinCatNOuterObstruction 与 FinCatNInnerObstruction
-- 中实例化。参数 m 编码 n = suc (suc m)，使 n ≥ 2 定义性成立
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module SecondPass.FinCatNProjectiveObstruction where

open import Relation.Nullary using (¬_)
open import Data.Nat using (ℕ)

open import SecondPass.Cosmos using (Cosmos)
open import SecondPass.Terminal using (_≈C_; ≈C-trans; ≈C-sym)
open import SecondPass.StrictLift using (StrictLayer; EmbeddingRule; EmbedFamily)
open import SecondPass.CumulativeHierarchyLimit
  using (Tower; LiftedLimitStructure; LimitLayer; EnrichedTower)
open import SecondPass.FinCatNWitness

-- Parameterised construction over FinCatN m
-- FinCatN m 上的参数化构造
module FinCatNProjectiveObstruction (m : ℕ) where

  open FinCatN m

  -- The layer-0 collapse of x and y under R implies liftAt 0 identifies them
  -- R 下 x 与 y 的层 0 塌缩蕴含 liftAt 0 将二者等同
  --
  -- Stated within the limit layer's own type, hence no level mismatch:
  -- only the _≈C_ relation at the limit layer is used
  -- 在极限层自身的类型内陈述，故无层级不匹配：
  -- 只用到极限层上的 _≈C_ 关系
  liftAt-0-collapses-general
    : {R : EmbeddingRule}
      (ET : EnrichedTower R nIdx)
      (x y : Cosmos (StrictLayer.C  (Tower.layer (EnrichedTower.tower ET) 0))
                    (StrictLayer.FC (Tower.layer (EnrichedTower.tower ET) 0)))
    → _≈C_ {C = StrictLayer.C  (Tower.layer (EnrichedTower.tower ET) 1)}
           {FC = StrictLayer.FC (Tower.layer (EnrichedTower.tower ET) 1)}
           (EmbeddingRule.Embed R (Tower.layer (EnrichedTower.tower ET) 0) x
              (EmbedFamily.getData (EnrichedTower.fams ET 0) x))
           (EmbeddingRule.Embed R (Tower.layer (EnrichedTower.tower ET) 0) y
              (EmbedFamily.getData (EnrichedTower.fams ET 0) y))
    → (LLS : LiftedLimitStructure R nIdx ET)
    → _≈C_ {C = StrictLayer.C  (LimitLayer.layer∞ (LiftedLimitStructure.limit LLS))}
           {FC = StrictLayer.FC (LimitLayer.layer∞ (LiftedLimitStructure.limit LLS))}
           (LiftedLimitStructure.liftAt LLS 0 x)
           (LiftedLimitStructure.liftAt LLS 0 y)
  liftAt-0-collapses-general ET x y collapse LLS =
    ≈C-trans
      (≈C-sym (LiftedLimitStructure.liftAt-step LLS 0 x))
      (≈C-trans
        (LiftedLimitStructure.liftAt-resp-≈C LLS 1 collapse)
        (LiftedLimitStructure.liftAt-step LLS 0 y))

  -- No LiftedLimitStructure along R has injective liftAt at layer 0 on
  -- the pair (x, y)
  -- 沿 R 的 LiftedLimitStructure 在层 0 上对 (x, y) 不单射
  --
  -- Proof reduces to liftAt-0-collapses-general: injectivity would send
  -- the collapse to x ≈C y, contradicting the given witness x≉y
  -- 证明归约到 liftAt-0-collapses-general：单射性会把塌缩变成
  -- x ≈C y，与给定的见证 x≉y 矛盾
  no-injective-liftAt-general
    : {R : EmbeddingRule}
      (ET : EnrichedTower R nIdx)
      (x y : Cosmos (StrictLayer.C  (Tower.layer (EnrichedTower.tower ET) 0))
                    (StrictLayer.FC (Tower.layer (EnrichedTower.tower ET) 0)))
    → _≈C_ {C = StrictLayer.C  (Tower.layer (EnrichedTower.tower ET) 1)}
           {FC = StrictLayer.FC (Tower.layer (EnrichedTower.tower ET) 1)}
           (EmbeddingRule.Embed R (Tower.layer (EnrichedTower.tower ET) 0) x
              (EmbedFamily.getData (EnrichedTower.fams ET 0) x))
           (EmbeddingRule.Embed R (Tower.layer (EnrichedTower.tower ET) 0) y
              (EmbedFamily.getData (EnrichedTower.fams ET 0) y))
    → ¬ (x ≈C y)
    → (LLS : LiftedLimitStructure R nIdx ET)
    → ¬ (∀ {u v : Cosmos (StrictLayer.C  (Tower.layer (EnrichedTower.tower ET) 0))
                         (StrictLayer.FC (Tower.layer (EnrichedTower.tower ET) 0))}
           → _≈C_ {C = StrictLayer.C  (LimitLayer.layer∞
                       (LiftedLimitStructure.limit LLS))}
                  {FC = StrictLayer.FC (LimitLayer.layer∞
                       (LiftedLimitStructure.limit LLS))}
                  (LiftedLimitStructure.liftAt LLS 0 u)
                  (LiftedLimitStructure.liftAt LLS 0 v)
           → u ≈C v)
  no-injective-liftAt-general ET x y collapse x≉y LLS inj =
    x≉y (inj (liftAt-0-collapses-general ET x y collapse LLS))
