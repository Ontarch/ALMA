------------------------------------------------------------------------
-- Obstruction: outer-rule admits no injective liftAt at layer 0
--
-- This module has no constructive downstream users; it is a diagnostic
-- instance of the general obstruction in FinCatNProjectiveObstruction.
-- It records why any LiftedLimitStructure over the FinCat n tower along
-- outer-rule must identify cosmos-idN and cosmos-const0N at layer 0
-- after lifting. The obstruction is structural: strictEmbed at layer 0
-- collapses the two cosmoi (its unfoldFunctor is independent of the
-- input), so no injective liftAt at layer 0 can exist. Any downstream
-- result requiring liftAt 0 = id (or liftAt 0 injective) is therefore
-- unprovable for outer-rule. The parameter m encodes n = suc (suc m),
-- so n ≥ 2 holds definitionally
--
-- 障碍：outer-rule 在层 0 上不允许单射的 liftAt
--
-- 本模块没有构造性下游使用方；它是 FinCatNProjectiveObstruction 中
-- 一般障碍的诊断实例。它记录：为何沿 outer-rule 的 FinCat n 塔上
-- 任意 LiftedLimitStructure 在提升后必须把层 0 的 cosmos-idN 与
-- cosmos-const0N 等同。障碍是结构性的：层 0 的 strictEmbed 把二者
-- 塌缩（其 unfoldFunctor 与输入无关），故不存在单射的 liftAt 0。
-- 因此任何要求 liftAt 0 = id（或单射）的下游结果对 outer-rule 不可证。
-- 参数 m 编码 n = suc (suc m)，使 n ≥ 2 定义性成立
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module SecondPass.FinCatNOuterObstruction where

open import Agda.Builtin.Equality using (refl)
open import Relation.Nullary using (¬_)
open import Data.Nat using (ℕ)

open import SecondPass.Cosmos using (Cosmos)
open import SecondPass.Terminal using (_≈C_; ≈C-refl)
open import SecondPass.CumulativeHierarchy using (UniformEmbeddingFamily)
open import SecondPass.StrictLift using (StrictLayer; strictEmbed; outer-rule)
open import SecondPass.CumulativeHierarchyLimit
  using (Tower; LiftedLimitStructure; LimitLayer)
open import SecondPass.FinCatNWitness
open import SecondPass.FinCatNColimit
open import SecondPass.FinCatNDefaultUnif
open import SecondPass.FinCatNFunctorial
open import SecondPass.FinCatNProjectiveObstruction

-- Parameterised construction over FinCatN m
-- FinCatN m 上的参数化构造
module FinCatNOuterObstruction (m : ℕ) where

  open FinCatN m
  open FinCatNColimit m using (colimitLayer)
  open FinCatNDefaultUnif m using (default-unif)
  open FinCatNFunctorial m using (enriched-default)
  open FinCatNProjectiveObstruction m

  -- strictEmbed at layer 0 collapses cosmos-idN and cosmos-const0N
  -- 层 0 的 strictEmbed 把 cosmos-idN 与 cosmos-const0N 塌缩
  --
  -- strictEmbed-unfoldFunctor nLayer is independent of the input
  -- cosmos, and actSOf TrivialFCN is constantly lift tt, so all three
  -- _≈C_ fields reduce to refl; the recursion on unfold-next closes
  -- because both sides unfold to themselves
  -- strictEmbed-unfoldFunctor nLayer 与输入宇宙无关，
  -- 且 actSOf TrivialFCN 恒为 lift tt，故三个 _≈C_ 字段均化简为 refl；
  -- unfold-next 的递归闭合，因两侧的 unfold-next 均返回自身
  private
    strictEmbed-id≈const0
      : _≈C_ {C = StrictLayer.C  (Tower.layer nTower 1)}
             {FC = StrictLayer.FC (Tower.layer nTower 1)}
             (strictEmbed nLayer cosmos-idN
               (UniformEmbeddingFamily.getData (default-unif 0) cosmos-idN))
             (strictEmbed nLayer cosmos-const0N
               (UniformEmbeddingFamily.getData (default-unif 0) cosmos-const0N))
    strictEmbed-id≈const0 ._≈C_.unfoldFunctor₀-eq {A} s = refl
    strictEmbed-id≈const0 ._≈C_.pos-to-shape-eq  {A} s p = refl
    strictEmbed-id≈const0 ._≈C_.unfold-next-eq   {A} s = strictEmbed-id≈const0

  -- liftAt 0 collapses the two cosmoi
  -- liftAt 0 塌缩这两个宇宙
  --
  -- Stated within the limit layer's own type, hence no level mismatch
  -- 在极限层自身的类型内陈述，故无层级不匹配
  liftAt-0-collapses
    : (LLS : LiftedLimitStructure outer-rule nIdx enriched-default)
    → _≈C_ {C = StrictLayer.C  (LimitLayer.layer∞ (LiftedLimitStructure.limit LLS))}
           {FC = StrictLayer.FC (LimitLayer.layer∞ (LiftedLimitStructure.limit LLS))}
           (LiftedLimitStructure.liftAt LLS 0 cosmos-idN)
           (LiftedLimitStructure.liftAt LLS 0 cosmos-const0N)
  liftAt-0-collapses =
    liftAt-0-collapses-general enriched-default
      cosmos-idN cosmos-const0N strictEmbed-id≈const0

  -- No LiftedLimitStructure along outer-rule has injective liftAt at layer 0
  -- 沿 outer-rule 的 LiftedLimitStructure 在层 0 上 liftAt 不单射
  --
  -- Proof reduces to liftAt-0-collapses: injectivity would send the
  -- collapse to cosmos-idN ≈C cosmos-const0N, contradicting the witness
  -- from FinCatNWitness
  -- 证明归约到 liftAt-0-collapses：单射性会把塌缩变成
  -- cosmos-idN ≈C cosmos-const0N，与 FinCatNWitness 的见证矛盾
  no-injective-liftAt-outer
    : (LLS : LiftedLimitStructure outer-rule nIdx enriched-default)
    → ¬ (∀ {x y : Cosmos (StrictLayer.C  (Tower.layer nTower 0))
                        (StrictLayer.FC (Tower.layer nTower 0))}
           → _≈C_ {C = StrictLayer.C  (LimitLayer.layer∞
                       (LiftedLimitStructure.limit LLS))}
                  {FC = StrictLayer.FC (LimitLayer.layer∞
                       (LiftedLimitStructure.limit LLS))}
                  (LiftedLimitStructure.liftAt LLS 0 x)
                  (LiftedLimitStructure.liftAt LLS 0 y)
           → x ≈C y)
  no-injective-liftAt-outer =
    no-injective-liftAt-general enriched-default
      cosmos-idN cosmos-const0N strictEmbed-id≈const0 cosmos-idN≉cosmos-const0N

  -- Non-emptiness of LiftedLimitStructure outer-rule (trivial instance)
  -- LiftedLimitStructure outer-rule 的非空性（平凡实例）
  --
  -- Witnesses that the type is inhabited, but carries no information:
  -- liftAt is the constant map to cosmos-idN. Together with
  -- no-injective-liftAt-outer, it shows that outer-rule admits
  -- LiftedLimitStructure only in the trivial form
  -- 见证该类型非空，但不携带信息：liftAt 是到 cosmos-idN 的常值映射。
  -- 结合 no-injective-liftAt-outer，它表明 outer-rule 只允许
  -- 平凡形式的 LiftedLimitStructure
  trivial-liftAt
    : ∀ k
    → Cosmos (StrictLayer.C (Tower.layer nTower k))
             (StrictLayer.FC (Tower.layer nTower k))
    → Cosmos (StrictLayer.C (LimitLayer.layer∞ colimitLayer))
             (StrictLayer.FC (LimitLayer.layer∞ colimitLayer))
  trivial-liftAt k _ = cosmos-idN

  trivial-lifted : LiftedLimitStructure outer-rule nIdx enriched-default
  trivial-lifted = record
    { limit          = colimitLayer
    ; liftAt         = trivial-liftAt
    ; liftAt-resp-≈C = λ k {x} {y} x≈y → ≈C-refl
    ; liftAt-step    = λ k x → ≈C-refl
    }
