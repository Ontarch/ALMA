------------------------------------------------------------------------
-- Conditional framework for the FinCat n tower with dep-embed-tower
--
-- Replaces the EmbeddingRule parameter of FinCatNColimit.WithSurjectivity
-- by the concrete tower-level embedding dep-embed-tower, eliminating the
-- embed-eq side condition. Given a uniform embedding family unif and its
-- surjectivity witness surj, constructs UniversalLimitDep and
-- NontrivialLimitDep. Both hypotheses are discharged unconditionally
-- downstream (unif by FinCatNDefaultUnif, surj by FinCatNSurjectivity).
-- The parameter m encodes n = suc (suc m), so n ≥ 2 holds definitionally
--
-- FinCat n 塔上以 dep-embed-tower 为嵌入的条件性框架
--
-- 将 FinCatNColimit.WithSurjectivity 的 EmbeddingRule 参数替换为具体
-- 塔层嵌入 dep-embed-tower，消除 embed-eq 边条件。给定一致嵌入族 unif
-- 与其满射性见证 surj，构造 UniversalLimitDep 与 NontrivialLimitDep
-- 两个假设均在下游被无条件消解（unif 由 FinCatNDefaultUnif，
-- surj 由 FinCatNSurjectivity）。参数 m 编码 n = suc (suc m)，
-- 使 n ≥ 2 定义性成立
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module SecondPass.FinCatNColimitWithDep where

open import Agda.Primitive using (Level; Setω)
open import Agda.Builtin.Equality using (refl)
open import Agda.Builtin.Sigma using (Σ; _,_)
open import Relation.Nullary using (¬_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product.Base using (proj₁; proj₂)

open import SecondPass.Unfolding using (Unfolding)
open import SecondPass.Cosmos using (Cosmos; out)
open import SecondPass.Terminal using (_≈C_; ≈C-refl; ≈C-sym; ≈C-trans)
open import SecondPass.CumulativeHierarchy using (EmbeddingData; UniformEmbeddingFamily)
open import SecondPass.StrictLift using (StrictLayer)
open import SecondPass.CumulativeHierarchyLimit using (Tower; LimitLayer)
open import SecondPass.FinCatNWitness
open import SecondPass.FinCatNTowerLemmas
open import SecondPass.FinCatNColimit
open import SecondPass.DependentEmbedding using (DependentEmbeddingRule; dep-rule)
open DependentEmbeddingRule

-- Parameterised construction over FinCatN m
-- FinCatN m 上的参数化构造
module FinCatNColimitWithDep (m : ℕ) where

  open FinCatN m
  open FinCatNTowerLemmas m
  open FinCatNColimit m

  -- Instantiate dep-rule.EmbedDep at tower layers. The three preconditions
  -- (pos-inhabited-tower, pos-singleton-tower, shape-singleton-at) are all
  -- intrinsic to the tower, so the instantiation is unconditional
  -- 把 dep-rule.EmbedDep 实例化到塔层。三个前提
  -- （pos-inhabited-tower、pos-singleton-tower、shape-singleton-at）
  -- 均为塔的固有结构，故该实例化无条件成立
  dep-embed-tower
    : ∀ k (x : Cosmos (StrictLayer.C (Tower.layer nTower k))
                       (StrictLayer.FC (Tower.layer nTower k)))
    → EmbeddingData x
    → Cosmos (StrictLayer.C (Tower.layer nTower (suc k)))
             (StrictLayer.FC (Tower.layer nTower (suc k)))
  dep-embed-tower k =
    EmbedDep dep-rule
      (Tower.layer nTower k)
      (λ {A} → pos-inhabited-tower k A)
      (λ {A} → pos-singleton-tower k A)
      (shape-singleton-at (suc k))

  -- Correspondence to FinCatNColimit.dep-embed. The three _≈C_ fields are
  -- definitional: both sides share the same underlying data
  -- 与 FinCatNColimit.dep-embed 的对应。三个 _≈C_ 字段均为定义性相等：
  -- 两侧共享相同的底层数据
  dep-embed-tower-≈-dep-embed
    : ∀ k x ed → dep-embed-tower k x ed ≈C dep-embed k x ed
  dep-embed-tower-≈-dep-embed k x ed ._≈C_.unfoldFunctor₀-eq {A} s = refl
  dep-embed-tower-≈-dep-embed k x ed ._≈C_.pos-to-shape-eq s p = refl
  dep-embed-tower-≈-dep-embed k x ed ._≈C_.unfold-next-eq {A = A} s =
    dep-embed-tower-≈-dep-embed k
      (Unfolding.unfold-next (out x) {A = proj₁ A} (proj₂ A))
      (EmbeddingData.next ed {A = proj₁ A} (proj₂ A))

  -- Tower-level cocone. Compared to the generic Cocone of
  -- ConditionalNontrivialLimit, the step condition uses dep-embed-tower
  -- directly rather than going through an EmbeddingRule
  -- 塔层余锥。与 ConditionalNontrivialLimit 中泛型的 Cocone 相比，
  -- 步进条件直接使用 dep-embed-tower，不再经过 EmbeddingRule
  record CoconeDep {oD hD eD sD pD : Level}
                   (unif : ∀ k → UniformEmbeddingFamily
                                   {C  = StrictLayer.C  (Tower.layer nTower k)}
                                   {FC = StrictLayer.FC (Tower.layer nTower k)})
                   (D : StrictLayer oD hD eD sD pD) : Setω where
    field
      map : ∀ k → Cosmos (StrictLayer.C (Tower.layer nTower k))
                         (StrictLayer.FC (Tower.layer nTower k))
                → Cosmos (StrictLayer.C D) (StrictLayer.FC D)
      map-resp : ∀ k {x y}
        → _≈C_ {C  = StrictLayer.C  (Tower.layer nTower k)}
               {FC = StrictLayer.FC (Tower.layer nTower k)} x y
        → _≈C_ {C = StrictLayer.C D} {FC = StrictLayer.FC D} (map k x) (map k y)
      step-compat : ∀ k x
        → _≈C_ {C = StrictLayer.C D} {FC = StrictLayer.FC D}
            (map (suc k)
              (dep-embed-tower k x (UniformEmbeddingFamily.getData (unif k) x)))
            (map k x)

  open CoconeDep

  -- Conditional framework: given a uniform embedding family unif and a
  -- surjectivity witness surj for it, we obtain the tower-level universal
  -- limit and a non-triviality witness. surj is discharged unconditionally
  -- by FinCatNSurjectivity; unif by FinCatNDefaultUnif
  -- 条件性框架：给定一致嵌入族 unif 与其满射性见证 surj，
  -- 得到塔层通用极限与非平凡见证。surj 由 FinCatNSurjectivity
  -- 无条件消解，unif 由 FinCatNDefaultUnif 消解
  module WithDepSurjectivity
    (unif : ∀ k → UniformEmbeddingFamily
                    {C  = StrictLayer.C  (Tower.layer nTower k)}
                    {FC = StrictLayer.FC (Tower.layer nTower k)})
    (surj : ∀ k
            (x : Cosmos (StrictLayer.C (Tower.layer nTower (suc k)))
                         (StrictLayer.FC (Tower.layer nTower (suc k))))
          → Σ (Cosmos (StrictLayer.C (Tower.layer nTower k))
                       (StrictLayer.FC (Tower.layer nTower k)))
              (λ y → x ≈C dep-embed-tower k y
                       (UniformEmbeddingFamily.getData (unif k) y)))
    where

    -- liftAt-step for dep-embed-tower: first transfer dep-embed-tower to
    -- dep-embed via the correspondence lemma, then apply dep-liftAt-step
    -- dep-embed-tower 的 liftAt-step：先用对应引理把 dep-embed-tower
    -- 换成 dep-embed，再应用 dep-liftAt-step
    liftAt-step-tower
      : ∀ k
        (x : Cosmos (StrictLayer.C (Tower.layer nTower k))
                     (StrictLayer.FC (Tower.layer nTower k)))
      → dep-liftAt (suc k)
          (dep-embed-tower k x
            (UniformEmbeddingFamily.getData (unif k) x))
        ≈C dep-liftAt k x
    liftAt-step-tower k x =
      ≈C-trans
        (dep-liftAt-resp (suc k)
          (dep-embed-tower-≈-dep-embed k x
            (UniformEmbeddingFamily.getData (unif k) x)))
        (dep-liftAt-step k x (UniformEmbeddingFamily.getData (unif k) x))

    -- mediate-coh for CoconeDep: same proof chain as FinCatNColimit, with
    -- dep-embed-tower inlined and no embed-eq side condition
    -- CoconeDep 的 mediate-coh：与 FinCatNColimit 证明链相同，
    -- 内联 dep-embed-tower，无 embed-eq 边条件
    dep-mediate-coh
      : ∀ {oD hD eD sD pD}
        {D : StrictLayer oD hD eD sD pD}
        (cone : CoconeDep unif D) (k : ℕ)
        (x : Cosmos (StrictLayer.C (Tower.layer nTower k))
                     (StrictLayer.FC (Tower.layer nTower k)))
      → _≈C_ {C = StrictLayer.C D} {FC = StrictLayer.FC D}
          (map cone 0 (dep-liftAt k x))
          (map cone k x)
    dep-mediate-coh cone zero    x = ≈C-refl
    dep-mediate-coh cone (suc k) x =
      let (y , p) = surj k x
          q1 = map-resp cone 0 (dep-liftAt-resp (suc k) p)
          q2 = map-resp cone 0 (liftAt-step-tower k y)
          q3 = dep-mediate-coh cone k y
          q4 = ≈C-trans (≈C-sym (step-compat cone k y))
                        (map-resp cone (suc k) (≈C-sym p))
      in ≈C-trans q1 (≈C-trans q2 (≈C-trans q3 q4))

  -- Tower-level universal limit. The type is deliberately incompatible
  -- with ConditionalNontrivialLimit.UniversalLimit: the latter is
  -- parameterised by an EmbeddingRule R, this one is specialised to
  -- dep-embed-tower. The two are related only through
  -- dependentUniversalLimitDep below
  -- 塔层通用极限。其类型与 ConditionalNontrivialLimit.UniversalLimit
  -- 刻意不兼容：后者以 EmbeddingRule R 为参数，本记录特化到
  -- dep-embed-tower。二者仅通过下方的 dependentUniversalLimitDep 关联
  record UniversalLimitDep
    (unif : ∀ k → UniformEmbeddingFamily
                    {C  = StrictLayer.C  (Tower.layer nTower k)}
                    {FC = StrictLayer.FC (Tower.layer nTower k)})
    : Setω where
    field
      limit          : LimitLayer nIdx nTower
      liftAt         : ∀ k
                     → Cosmos (StrictLayer.C  (Tower.layer nTower k))
                              (StrictLayer.FC (Tower.layer nTower k))
                     → Cosmos (StrictLayer.C  (LimitLayer.layer∞ limit))
                              (StrictLayer.FC (LimitLayer.layer∞ limit))
      liftAt-resp    : ∀ k {x y}
                     → _≈C_ {C  = StrictLayer.C  (Tower.layer nTower k)}
                            {FC = StrictLayer.FC (Tower.layer nTower k)} x y
                     → _≈C_ {C  = StrictLayer.C  (LimitLayer.layer∞ limit)}
                            {FC = StrictLayer.FC (LimitLayer.layer∞ limit)}
                            (liftAt k x) (liftAt k y)
      liftAt-step    : ∀ k
                       (x : Cosmos (StrictLayer.C (Tower.layer nTower k))
                                   (StrictLayer.FC (Tower.layer nTower k)))
                     → _≈C_ {C  = StrictLayer.C  (LimitLayer.layer∞ limit)}
                            {FC = StrictLayer.FC (LimitLayer.layer∞ limit)}
                            (liftAt (suc k)
                              (dep-embed-tower k x
                                (UniformEmbeddingFamily.getData (unif k) x)))
                            (liftAt k x)

      mediate        : ∀ {oD hD eD sD pD : Level}
                     → (D : StrictLayer oD hD eD sD pD)
                     → CoconeDep unif D
                     → Cosmos (StrictLayer.C  (LimitLayer.layer∞ limit))
                              (StrictLayer.FC (LimitLayer.layer∞ limit))
                     → Cosmos (StrictLayer.C D) (StrictLayer.FC D)

      mediate-resp   : ∀ {oD hD eD sD pD : Level}
                     → {D : StrictLayer oD hD eD sD pD}
                     → (cone : CoconeDep unif D)
                     → {x y : Cosmos (StrictLayer.C  (LimitLayer.layer∞ limit))
                                     (StrictLayer.FC (LimitLayer.layer∞ limit))}
                     → _≈C_ {C  = StrictLayer.C  (LimitLayer.layer∞ limit)}
                            {FC = StrictLayer.FC (LimitLayer.layer∞ limit)} x y
                     → _≈C_ {C = StrictLayer.C D} {FC = StrictLayer.FC D}
                             (mediate D cone x) (mediate D cone y)

      mediate-coh    : ∀ {oD hD eD sD pD : Level}
                     → {D : StrictLayer oD hD eD sD pD}
                     → (cone : CoconeDep unif D) (k : ℕ)
                     → (x : Cosmos (StrictLayer.C (Tower.layer nTower k))
                                   (StrictLayer.FC (Tower.layer nTower k)))
                     → _≈C_ {C = StrictLayer.C D} {FC = StrictLayer.FC D}
                         (mediate D cone (liftAt k x))
                         (CoconeDep.map cone k x)

      mediate-unique : ∀ {oD hD eD sD pD : Level}
                     → {D : StrictLayer oD hD eD sD pD}
                     → (cone : CoconeDep unif D)
                     → (g : Cosmos (StrictLayer.C  (LimitLayer.layer∞ limit))
                                   (StrictLayer.FC (LimitLayer.layer∞ limit))
                          → Cosmos (StrictLayer.C D) (StrictLayer.FC D))
                     → (g-resp : ∀ {x y : Cosmos (StrictLayer.C  (LimitLayer.layer∞ limit))
                                                 (StrictLayer.FC (LimitLayer.layer∞ limit))}
                               → _≈C_ {C  = StrictLayer.C  (LimitLayer.layer∞ limit)}
                                      {FC = StrictLayer.FC (LimitLayer.layer∞ limit)} x y
                               → _≈C_ {C = StrictLayer.C D} {FC = StrictLayer.FC D}
                                       (g x) (g y))
                     → (g-coh : ∀ (k : ℕ)
                                  (x : Cosmos (StrictLayer.C (Tower.layer nTower k))
                                              (StrictLayer.FC (Tower.layer nTower k)))
                              → _≈C_ {C = StrictLayer.C D} {FC = StrictLayer.FC D}
                                  (g (liftAt k x))
                                  (CoconeDep.map cone k x))
                     → ∀ (z : Cosmos (StrictLayer.C  (LimitLayer.layer∞ limit))
                                     (StrictLayer.FC (LimitLayer.layer∞ limit)))
                     → _≈C_ {C = StrictLayer.C D} {FC = StrictLayer.FC D}
                         (g z) (mediate D cone z)

  open UniversalLimitDep

  -- A uniform embedding family at every layer of the tower
  -- 塔每一层上的一致嵌入族
  UniformEmbeddingFamilyForTower : Setω
  UniformEmbeddingFamilyForTower =
    ∀ k → UniformEmbeddingFamily
            {C  = StrictLayer.C  (Tower.layer nTower k)}
            {FC = StrictLayer.FC (Tower.layer nTower k)}

  -- Every (suc k)-layer cosmos arises, up to _≈C_, as the dep-embed-tower
  -- image of some k-layer cosmos
  -- 第 (suc k) 层的任意宇宙在 _≈C_ 意义下都等于某第 k 层宇宙的
  -- dep-embed-tower 像
  SurjectivityForTower : UniformEmbeddingFamilyForTower → Setω
  SurjectivityForTower unif =
    ∀ k
      (x : Cosmos (StrictLayer.C (Tower.layer nTower (suc k)))
                   (StrictLayer.FC (Tower.layer nTower (suc k))))
    → Σ (Cosmos (StrictLayer.C (Tower.layer nTower k))
                 (StrictLayer.FC (Tower.layer nTower k)))
        (λ y → x ≈C dep-embed-tower k y
                     (UniformEmbeddingFamily.getData (unif k) y))

  -- Assemble the tower-level universal limit from dep-liftAt and colimitLayer,
  -- with mediate = map cone 0
  -- 由 dep-liftAt 与 colimitLayer 组装塔层通用极限，mediate = map cone 0
  dependentUniversalLimitDep
    : (unif : UniformEmbeddingFamilyForTower)
    → (surj : SurjectivityForTower unif)
    → UniversalLimitDep unif
  dependentUniversalLimitDep unif surj = record
    { limit          = colimitLayer
    ; liftAt         = dep-liftAt
    ; liftAt-resp    = λ k {x} {y} → dep-liftAt-resp k
    ; liftAt-step    = λ k x →
        WithDepSurjectivity.liftAt-step-tower unif surj k x
    ; mediate        = λ D cone z → CoconeDep.map cone 0 z
    ; mediate-resp   = λ {D} cone {x} {y} eq → CoconeDep.map-resp cone 0 eq
    ; mediate-coh    = λ {D} cone k x →
        WithDepSurjectivity.dep-mediate-coh unif surj cone k x
    ; mediate-unique = λ {D} cone g g-resp g-coh z → g-coh 0 z
    }

  -- Non-triviality: liftAt distinguishes a pair of cosmos elements
  -- 非平凡性：liftAt 区分一对宇宙元素
  record NontrivialLimitDep
    {unif : UniformEmbeddingFamilyForTower}
    (UL : UniversalLimitDep unif) : Setω where
    field
      k   : ℕ
      x   : Cosmos (StrictLayer.C (Tower.layer nTower k))
                   (StrictLayer.FC (Tower.layer nTower k))
      y   : Cosmos (StrictLayer.C (Tower.layer nTower k))
                   (StrictLayer.FC (Tower.layer nTower k))
      x≉y : ¬ (_≈C_
                {C  = StrictLayer.C  (LimitLayer.layer∞ (limit UL))}
                {FC = StrictLayer.FC (LimitLayer.layer∞ (limit UL))}
                (liftAt UL k x) (liftAt UL k y))

  open NontrivialLimitDep

  -- Non-triviality at layer 0: liftAt 0 is the identity, so the two
  -- layer-0 cosmoi cosmos-idN and cosmos-const0N remain distinguishable
  -- after lifting, with the same witness as FinCatNWitness
  -- 第 0 层的非平凡性：liftAt 0 为恒等，故两个第 0 层宇宙
  -- cosmos-idN 与 cosmos-const0N 在提升后仍可区分，
  -- 见证与 FinCatNWitness 相同
  dependentNontrivialDep
    : (unif : UniformEmbeddingFamilyForTower)
    → (surj : SurjectivityForTower unif)
    → NontrivialLimitDep (dependentUniversalLimitDep unif surj)
  dependentNontrivialDep unif surj = record
    { k    = 0
    ; x    = cosmos-idN
    ; y    = cosmos-const0N
    ; x≉y  = cosmos-idN≉cosmos-const0N
    }
