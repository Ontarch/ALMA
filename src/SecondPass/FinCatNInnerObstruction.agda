------------------------------------------------------------------------
-- Obstruction: inner-rule admits no injective liftAt at layer 0
-- 障碍：inner-rule 在层 0 上不允许单射的 liftAt
--
-- This module has no constructive downstream users; it is a diagnostic
-- instance of the general obstruction in FinCatNProjectiveObstruction.
-- It records why any LiftedLimitStructure over the FinCat n tower along
-- inner-rule must identify cosmos-idN and cosmos-const0N at layer 0
-- after lifting. The obstruction is structural: strictEmbed-inner at
-- layer 0 collapses the two cosmoi (its unfoldFunctor is independent of
-- the input), so no injective liftAt at layer 0 can exist. Any
-- downstream result requiring liftAt 0 = id (or liftAt 0 injective) is
-- therefore unprovable for inner-rule. The parameter m encodes
-- n = suc (suc m), so n ≥ 2 holds definitionally
--
-- 本模块没有构造性下游使用方；它是 FinCatNProjectiveObstruction 中
-- 一般障碍的诊断实例。它记录：为何沿 inner-rule 的 FinCat n 塔上
-- 任意 LiftedLimitStructure 在提升后必须把层 0 的 cosmos-idN 与
-- cosmos-const0N 等同。障碍是结构性的：层 0 的 strictEmbed-inner 把
-- 二者塌缩（其 unfoldFunctor 与输入无关），故不存在单射的 liftAt 0。
-- 因此任何要求 liftAt 0 = id（或单射）的下游结果对 inner-rule 不可证。
-- 参数 m 编码 n = suc (suc m)，使 n ≥ 2 定义性成立
------------------------------------------------------------------------
{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module SecondPass.FinCatNInnerObstruction where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Level using (lower)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality.Properties using (module ≡-Reasoning)
open ≡-Reasoning
open import Data.Nat using (ℕ; suc)
open import Data.Product.Base using (proj₁)

open import Categories.Category.Core using (Category)

open import Cosmos.ContCategoryLemmas using (ShapeOf; PosOf)
open import SecondPass.Cosmos using (Cosmos; out)
open import SecondPass.Terminal using (_≈C_; ≈C-refl)
open import SecondPass.Unfolding using (Unfolding)
open import SecondPass.CumulativeHierarchy using (UniformEmbeddingFamily; EmbeddingData)
open import SecondPass.StrictLift
  using (StrictLayer; EmbedFamily; strictStep-suc; strictEmbed)
open import SecondPass.CumulativeHierarchyLimit
  using (Tower; LiftedLimitStructure; LimitLayer; EnrichedTower)
open import SecondPass.FinCatNWitness
open import SecondPass.FinCatNInnerSewing
open import SecondPass.FinCatNColimit
open import SecondPass.FinCatNDefaultUnif
open import SecondPass.FinCatNFunctorial
open import SecondPass.FinCatNProjectiveObstruction

-- Parameterised construction over FinCatN m
-- FinCatN m 上的参数化构造
module FinCatNInnerObstruction (m : ℕ) where

  open FinCatN m
  open FinCatNColimit m using (colimitLayer)
  open FinCatNDefaultUnif m using (default-unif)
  open FinCatNFunctorial m using (default-strictEmbed-resp-≈C)
  open FinCatNProjectiveObstruction m

  -- strictEmbed-inner and strictEmbed share the same pos-to-shape on the
  -- same input; this definitional equality is the reuse premise of the
  -- delegation below
  -- strictEmbed-inner 与 strictEmbed 在同一输入上共用 pos-to-shape；
  -- 此定义性相等是下方委托的复用前提
  private
    strictEmbed-inner-pos-to-shape≡strictEmbed
      : ∀ {o h e s p} (L : StrictLayer o h e s p)
        (x : Cosmos (StrictLayer.C L) (StrictLayer.FC L))
        (ed : EmbeddingData x)
        (A : Category.Obj (StrictLayer.C (strictStep-suc L)))
        (s : ShapeOf (StrictLayer.FC (strictStep-suc L)) A)
        (p : PosOf (StrictLayer.FC (strictStep-suc L)) {A = A} s)
      → Unfolding.pos-to-shape (out (strictEmbed-inner L x ed)) {A = A} s p
      ≡ Unfolding.pos-to-shape (out (strictEmbed L x ed)) {A = A} s p
    strictEmbed-inner-pos-to-shape≡strictEmbed L x ed A s p = refl

  -- strictEmbed-inner preserves _≈C_, reusing the outer functoriality
  -- proof's default-strictEmbed-resp-≈C via the coherence lemma above
  -- strictEmbed-inner 保持 _≈C_，经上述相干引理复用外层函子性证明中的
  -- default-strictEmbed-resp-≈C
  default-strictEmbed-inner-resp-≈C
    : ∀ k {x y : Cosmos (StrictLayer.C (Tower.layer nTower k))
                         (StrictLayer.FC (Tower.layer nTower k))}
    → _≈C_ {C = StrictLayer.C (Tower.layer nTower k)}
           {FC = StrictLayer.FC (Tower.layer nTower k)} x y
    → _≈C_ {C = StrictLayer.C (Tower.layer nTower (suc k))}
           {FC = StrictLayer.FC (Tower.layer nTower (suc k))}
         (strictEmbed-inner (Tower.layer nTower k) x
            (UniformEmbeddingFamily.getData (default-unif k) x))
         (strictEmbed-inner (Tower.layer nTower k) y
            (UniformEmbeddingFamily.getData (default-unif k) y))
  default-strictEmbed-inner-resp-≈C k {x} {y} = go x y
    where
    L   = Tower.layer nTower k
    CN  = StrictLayer.C L
    FCN = StrictLayer.FC L

    go : (x y : Cosmos CN FCN)
       → _≈C_ {C = CN} {FC = FCN} x y
       → _≈C_ {C = StrictLayer.C (strictStep-suc L)}
              {FC = StrictLayer.FC (strictStep-suc L)}
            (strictEmbed-inner L x
               (UniformEmbeddingFamily.getData (default-unif k) x))
            (strictEmbed-inner L y
               (UniformEmbeddingFamily.getData (default-unif k) y))

    -- Both strictEmbed-inners share strictEmbed-unfoldFunctor-inner L
    -- 两个 strictEmbed-inner 共用 strictEmbed-unfoldFunctor-inner L
    go x y x≈y ._≈C_.unfoldFunctor₀-eq {A} s = refl

    -- Chain via the outer proof, using the coherence lemma on both ends
    -- 经外层证明链式传递，两端各用一次相干引理
    go x y x≈y ._≈C_.pos-to-shape-eq {A} s p =
      begin
        Unfolding.pos-to-shape (out (strictEmbed-inner L x ed-x)) {A = A} s p
          ≡⟨ strictEmbed-inner-pos-to-shape≡strictEmbed L x ed-x A s p ⟩
        Unfolding.pos-to-shape (out (strictEmbed L x ed-x)) {A = A} s p
          ≡⟨ default-strictEmbed-resp-≈C k x≈y ._≈C_.pos-to-shape-eq {A = A} s p ⟩
        Unfolding.pos-to-shape (out (strictEmbed L y ed-y)) {A = A} s p
          ≡˘⟨ strictEmbed-inner-pos-to-shape≡strictEmbed L y ed-y A s p ⟩
        Unfolding.pos-to-shape (out (strictEmbed-inner L y ed-y)) {A = A} s p
      ∎
      where
        ed-x = UniformEmbeddingFamily.getData (default-unif k) x
        ed-y = UniformEmbeddingFamily.getData (default-unif k) y

    -- Corecursive descent: lower the lifted shape, unfold both sides, recurse
    -- 余递归下降：对提升后的形状做 lower，展开两侧，递归
    go x y x≈y ._≈C_.unfold-next-eq {A} s =
      go (Unfolding.unfold-next (out x) {A = proj₁ A} (lower s))
         (Unfolding.unfold-next (out y) {A = proj₁ A} (lower s))
         (_≈C_.unfold-next-eq x≈y {A = proj₁ A} (lower s))

  -- EmbedFamily inner-rule at every layer
  -- 每一层上沿 inner-rule 的 EmbedFamily
  fams-inner : ∀ k → EmbedFamily inner-rule (Tower.layer nTower k)
  fams-inner k = record
    { uniform = default-unif k
    ; resp-≈C = λ {x} {y} x≈y → default-strictEmbed-inner-resp-≈C k x≈y
    }

  -- EnrichedTower along inner-rule
  -- 沿 inner-rule 的 EnrichedTower
  enriched-inner : EnrichedTower inner-rule nIdx
  enriched-inner = record
    { tower = nTower
    ; fams  = fams-inner
    }

  -- strictEmbed-inner at layer 0 collapses cosmos-idN and cosmos-const0N
  -- 层 0 的 strictEmbed-inner 把 cosmos-idN 与 cosmos-const0N 塌缩
  --
  -- Both sides share strictEmbed-unfoldFunctor-inner nLayer, and
  -- actSOf TrivialFCN is constantly lift tt, so all three _≈C_ fields
  -- reduce to refl; the recursion on unfold-next closes because both
  -- sides unfold to themselves
  -- 两侧共用 strictEmbed-unfoldFunctor-inner nLayer，且
  -- actSOf TrivialFCN 恒为 lift tt，故三个 _≈C_ 字段均化简为 refl；
  -- unfold-next 的递归闭合，因两侧的 unfold-next 均返回自身
  private
    strictEmbed-inner-id≈const0
      : _≈C_ {C = StrictLayer.C  (Tower.layer nTower 1)}
             {FC = StrictLayer.FC (Tower.layer nTower 1)}
             (strictEmbed-inner nLayer cosmos-idN
               (UniformEmbeddingFamily.getData (default-unif 0) cosmos-idN))
             (strictEmbed-inner nLayer cosmos-const0N
               (UniformEmbeddingFamily.getData (default-unif 0) cosmos-const0N))
    strictEmbed-inner-id≈const0 ._≈C_.unfoldFunctor₀-eq {A} s = refl
    strictEmbed-inner-id≈const0 ._≈C_.pos-to-shape-eq  {A} s p = refl
    strictEmbed-inner-id≈const0 ._≈C_.unfold-next-eq   {A} s =
      strictEmbed-inner-id≈const0

  -- liftAt 0 collapses the two cosmoi
  -- liftAt 0 塌缩这两个宇宙
  --
  -- Stated within the limit layer's own type, hence no level mismatch
  -- 在极限层自身的类型内陈述，故无层级不匹配
  liftAt-0-collapses-inner
    : (LLS : LiftedLimitStructure inner-rule nIdx enriched-inner)
    → _≈C_ {C = StrictLayer.C  (LimitLayer.layer∞ (LiftedLimitStructure.limit LLS))}
           {FC = StrictLayer.FC (LimitLayer.layer∞ (LiftedLimitStructure.limit LLS))}
           (LiftedLimitStructure.liftAt LLS 0 cosmos-idN)
           (LiftedLimitStructure.liftAt LLS 0 cosmos-const0N)
  liftAt-0-collapses-inner =
    liftAt-0-collapses-general enriched-inner
      cosmos-idN cosmos-const0N strictEmbed-inner-id≈const0

  -- No LiftedLimitStructure along inner-rule has injective liftAt at layer 0
  -- 沿 inner-rule 的 LiftedLimitStructure 在层 0 上 liftAt 不单射
  --
  -- Proof reduces to liftAt-0-collapses-inner: injectivity would send the
  -- collapse to cosmos-idN ≈C cosmos-const0N, contradicting the witness
  -- from FinCatNWitness
  -- 证明归约到 liftAt-0-collapses-inner：单射性会把塌缩变成
  -- cosmos-idN ≈C cosmos-const0N，与 FinCatNWitness 的见证矛盾
  no-injective-liftAt-inner
    : (LLS : LiftedLimitStructure inner-rule nIdx enriched-inner)
    → ¬ (∀ {x y : Cosmos (StrictLayer.C  (Tower.layer nTower 0))
                        (StrictLayer.FC (Tower.layer nTower 0))}
           → _≈C_ {C = StrictLayer.C  (LimitLayer.layer∞
                       (LiftedLimitStructure.limit LLS))}
                  {FC = StrictLayer.FC (LimitLayer.layer∞
                       (LiftedLimitStructure.limit LLS))}
                  (LiftedLimitStructure.liftAt LLS 0 x)
                  (LiftedLimitStructure.liftAt LLS 0 y)
           → x ≈C y)
  no-injective-liftAt-inner =
    no-injective-liftAt-general enriched-inner
      cosmos-idN cosmos-const0N strictEmbed-inner-id≈const0 cosmos-idN≉cosmos-const0N

  -- Non-emptiness of LiftedLimitStructure inner-rule (trivial instance)
  -- LiftedLimitStructure inner-rule 的非空性（平凡实例）
  --
  -- Witnesses that the type is inhabited, but carries no information:
  -- liftAt is the constant map to cosmos-idN. Together with
  -- no-injective-liftAt-inner, it shows that inner-rule admits
  -- LiftedLimitStructure only in the trivial form
  -- 见证该类型非空，但不携带信息：liftAt 是到 cosmos-idN 的常值映射。
  -- 结合 no-injective-liftAt-inner，它表明 inner-rule 只允许
  -- 平凡形式的 LiftedLimitStructure
  trivial-liftAt-inner
    : ∀ k
    → Cosmos (StrictLayer.C (Tower.layer nTower k))
             (StrictLayer.FC (Tower.layer nTower k))
    → Cosmos (StrictLayer.C (LimitLayer.layer∞ colimitLayer))
             (StrictLayer.FC (LimitLayer.layer∞ colimitLayer))
  trivial-liftAt-inner k _ = cosmos-idN

  trivial-lifted-inner : LiftedLimitStructure inner-rule nIdx enriched-inner
  trivial-lifted-inner = record
    { limit          = colimitLayer
    ; liftAt         = trivial-liftAt-inner
    ; liftAt-resp-≈C = λ k {x} {y} x≈y → ≈C-refl
    ; liftAt-step    = λ k x → ≈C-refl
    }
