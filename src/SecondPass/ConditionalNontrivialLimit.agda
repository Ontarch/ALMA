------------------------------------------------------------------------
-- Conditional non-triviality of a limit over the FinCat n tower
-- FinCat n 塔上极限的条件性非平凡性
--
-- Defines the ideal universal property a limit over an enriched tower
-- would have to satisfy (Cocone, UniversalLimit), non-triviality as
-- separation by liftAt (NontrivialLimit), and shows that no non-trivial
-- limit can exist when the target space is trivial (all cosmoi
-- bisimilar); UnitCat is such a trivial target
-- ColimitCoherence and NontrivialLimitWitness are stated generically
-- over any EnrichedTower outer-rule i. The construction of a
-- non-triviality witness is parameterised over FinCatN m and lives in
-- the nested module FinCatNVariants
-- 定义丰富塔上极限应满足的理想泛性质（Cocone、UniversalLimit），
-- 以 liftAt 的区分性定义非平凡性（NontrivialLimit），并证明：
-- 若目标空间平凡（所有宇宙互模拟），则不存在非平凡极限；
-- UnitCat 就是这样的平凡目标
-- ColimitCoherence 与 NontrivialLimitWitness 对任意
-- EnrichedTower outer-rule i 泛型陈述。非平凡见证的构造以
-- FinCatN m 为参数，位于嵌套模块 FinCatNVariants 中
------------------------------------------------------------------------
{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module SecondPass.ConditionalNontrivialLimit where

open import Agda.Primitive using (Level; _⊔_; Setω)
open import Agda.Builtin.Equality using (refl)
open import Relation.Nullary using (¬_)
open import Data.Nat using (ℕ; suc)
open import Data.Empty using (⊥)

open import Categories.Category.Core using (Category)
open import Categories.Functor.Core using (Functor)

open import Cosmos.ContCategory using (ContCat)
open import SecondPass.Cosmos using (Cosmos; UnitCat; UnitContainerFunctor)
open import SecondPass.Terminal using (_≈C_)
open import SecondPass.StrictLift
  using (StrictLayer; EmbeddingRule; EmbedFamily; outer-rule)
open import SecondPass.CumulativeHierarchyLimit
  using (LayerIdx; Tower; EnrichedTower; LimitLayer)
open import SecondPass.FinCatNWitness

open StrictLayer
open EmbeddingRule
open EmbedFamily
open Tower
open EnrichedTower
open LimitLayer
open _≈C_

variable
  o h e s p : Level

-- A cocone over the tower ET with target D
-- 从塔 ET 到目标 D 的锥
record Cocone {oD hD eD sD pD : Level}
              {R : EmbeddingRule} {i : LayerIdx}
              (ET : EnrichedTower R i)
              (D : StrictLayer oD hD eD sD pD) : Setω where
  private
    T   = tower ET
    Cn  = λ n → C  (layer T n)
    FCn = λ n → FC (layer T n)
  field
    map : ∀ n → Cosmos (Cn n) (FCn n) → Cosmos (C D) (FC D)
    map-resp : ∀ n {x y}
      → _≈C_ {C = Cn n} {FC = FCn n} x y
      → _≈C_ {C = C D} {FC = FC D} (map n x) (map n y)
    step-compat : ∀ n x →
      _≈C_ {C = C D} {FC = FC D}
        (map (suc n)
          (Embed R (layer T n) x (getData (fams ET n) x)))
        (map n x)

-- The universal property a limit over ET would have to satisfy
-- 极限对 ET 必须满足的泛性质
record UniversalLimit {R : EmbeddingRule} {i : LayerIdx}
                      (ET : EnrichedTower R i) : Setω where
  private
    T   = tower ET
    Cn  = λ n → C  (layer T n)
    FCn = λ n → FC (layer T n)
  field
    limit : LimitLayer i T
  private
    C∞  = C  (layer∞ limit)
    FC∞ = FC (layer∞ limit)
  field
    liftAt : ∀ n → Cosmos (Cn n) (FCn n) → Cosmos C∞ FC∞
    liftAt-resp : ∀ n {x y}
      → _≈C_ {C = Cn n} {FC = FCn n} x y
      → _≈C_ {C = C∞} {FC = FC∞} (liftAt n x) (liftAt n y)
    liftAt-step : ∀ n x →
      _≈C_ {C = C∞} {FC = FC∞}
        (liftAt (suc n)
          (Embed R (layer T n) x (getData (fams ET n) x)))
        (liftAt n x)

    mediate
      : ∀ {oD hD eD sD pD : Level}
      → (D : StrictLayer oD hD eD sD pD)
      → Cocone ET D
      → Cosmos C∞ FC∞ → Cosmos (C D) (FC D)

    mediate-resp
      : ∀ {oD hD eD sD pD : Level}
      → {D : StrictLayer oD hD eD sD pD}
      → (cone : Cocone ET D)
      → {x y : Cosmos C∞ FC∞}
      → _≈C_ {C = C∞} {FC = FC∞} x y
      → _≈C_ {C = C D} {FC = FC D}
               (mediate D cone x) (mediate D cone y)

    mediate-coh
      : ∀ {oD hD eD sD pD : Level}
      → {D : StrictLayer oD hD eD sD pD}
      → (cone : Cocone ET D) (n : ℕ)
      → (x : Cosmos (C  (layer T n)) (FC (layer T n)))
      → _≈C_ {C = C D} {FC = FC D}
          (mediate D cone (liftAt n x))
          (Cocone.map cone n x)

    mediate-unique
      : ∀ {oD hD eD sD pD : Level}
      → {D : StrictLayer oD hD eD sD pD}
      → (cone : Cocone ET D)
      → (g : Cosmos C∞ FC∞ → Cosmos (C D) (FC D))
      → (g-resp : ∀ {x y : Cosmos C∞ FC∞}
                → _≈C_ {C = C∞} {FC = FC∞} x y
                → _≈C_ {C = C D} {FC = FC D} (g x) (g y))
      → (g-coh : ∀ (n : ℕ)
                 (x : Cosmos (C  (layer T n)) (FC (layer T n)))
               → _≈C_ {C = C D} {FC = FC D}
                   (g (liftAt n x)) (Cocone.map cone n x))
      → ∀ (z : Cosmos C∞ FC∞)
      → _≈C_ {C = C D} {FC = FC D}
          (g z) (mediate D cone z)

-- Non-triviality: liftAt distinguishes at least one pair
-- 非平凡性：liftAt 至少区分一对
record NontrivialLimit
  {R : EmbeddingRule} {i : LayerIdx} {ET : EnrichedTower R i}
  (UL : UniversalLimit ET) : Setω where
  private
    T = tower ET
  field
    n : ℕ
    x : Cosmos (C  (layer T n)) (FC (layer T n))
    y : Cosmos (C  (layer T n)) (FC (layer T n))
    x≉y : ¬ (UniversalLimit.liftAt UL n x
             ≈C UniversalLimit.liftAt UL n y)

-- If the target space is trivial (all cosmoi bisimilar), no NontrivialLimit
-- can exist
-- 若目标空间平凡（所有宇宙互模拟），则不存在非平凡极限
AllCosmosBisim : (C : Category o h e) (FC : Functor C (ContCat s p))
               → Set (o ⊔ h ⊔ e ⊔ s ⊔ p)
AllCosmosBisim C FC = ∀ (x y : Cosmos C FC) → x ≈C y

no-nontrivial-limit-of-singleton-target
  : ∀ {R : EmbeddingRule} {i : LayerIdx} {ET : EnrichedTower R i}
  → (UL : UniversalLimit ET)
  → AllCosmosBisim (C  (layer∞ (UniversalLimit.limit UL)))
                   (FC (layer∞ (UniversalLimit.limit UL)))
  → NontrivialLimit UL → ⊥
no-nontrivial-limit-of-singleton-target UL all-bisim nl =
  NontrivialLimit.x≉y nl
    (all-bisim (UniversalLimit.liftAt UL (NontrivialLimit.n nl)
                    (NontrivialLimit.x nl))
               (UniversalLimit.liftAt UL (NontrivialLimit.n nl)
                    (NontrivialLimit.y nl)))

-- UnitCat is a trivial target: all cosmoi are bisimilar
-- UnitCat 是平凡目标：所有宇宙都互模拟
unitcat-all-cosmos-bisim
  : ∀ {ℓ} → AllCosmosBisim (UnitCat {ℓ}) (UnitContainerFunctor {ℓ})
unitcat-all-cosmos-bisim {ℓ} x y = bisim x y
  where
    bisim
      : ∀ (x y : Cosmos (UnitCat {ℓ}) (UnitContainerFunctor {ℓ}))
      → x ≈C y
    bisim x y .unfoldFunctor₀-eq {A} s = refl
    bisim x y .pos-to-shape-eq   {A} s p = refl
    bisim x y .unfold-next-eq    {A} s = bisim _ _

-- Coherence hypothesis: liftAt at layer 0 is injective
-- 相容性假设：层 0 的 liftAt 是单射
record ColimitCoherence {i : LayerIdx} (ET : EnrichedTower outer-rule i) : Setω where
  field
    UL : UniversalLimit ET
    lift0-inj
      : ∀ {x y : Cosmos (C (layer (tower ET) 0)) (FC (layer (tower ET) 0))}
      → _≈C_ {C = C (layer∞ (UniversalLimit.limit UL))}
             {FC = FC (layer∞ (UniversalLimit.limit UL))}
             (UniversalLimit.liftAt UL 0 x)
             (UniversalLimit.liftAt UL 0 y)
      → _≈C_ {C = C (layer (tower ET) 0)}
             {FC = FC (layer (tower ET) 0)} x y

-- A witness that a UniversalLimit over ET is non-trivial
-- ET 上 UniversalLimit 非平凡的见证
record NontrivialLimitWitness {i : LayerIdx} (ET : EnrichedTower outer-rule i) : Setω where
  field
    UL : UniversalLimit ET
    nl : NontrivialLimit UL

-- FinCatN m variants: the non-triviality witness over the FinCatN m tower
-- FinCatN m 变体：FinCatN m 塔上的非平凡见证
module FinCatNVariants (m : ℕ) where
  open FinCatN m

  -- Conditional construction: given a coherent UniversalLimit over the
  -- FinCatN m tower, a non-triviality witness exists
  -- 条件性构造：给定 FinCatN m 塔上相容的 UniversalLimit，非平凡见证存在
  nontrivial-witness
    : (ef : ∀ k → EmbedFamily outer-rule (Tower.layer nTower k))
    → ColimitCoherence (record { tower = nTower ; fams = ef })
    → NontrivialLimitWitness (record { tower = nTower ; fams = ef })
  nontrivial-witness ef cc = record
    { UL = ColimitCoherence.UL cc
    ; nl = record
        { n    = 0
        ; x    = cosmos-idN
        ; y    = cosmos-const0N
        ; x≉y  = λ eq → cosmos-idN≉cosmos-const0N (ColimitCoherence.lift0-inj cc eq)
        }
    }
