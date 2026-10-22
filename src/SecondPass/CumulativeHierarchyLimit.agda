------------------------------------------------------------------------
-- Cumulative Hierarchy Limit — the tower and its layers
-- 累积层级的极限 —— 塔及其各层
--
-- Defines the indexing of strictly-growing layers, the Tower record and
-- its iterated layers, the LimitLayer and LimitCompatible records, the
-- iterated embedding iterEmbed together with its composition law, and
-- the unit tower instance. The framework is parameterised by an
-- EmbeddingRule R, making it direction-agnostic; the unit instance uses
-- outer-rule
-- 定义严格增长层级的索引、含迭代层的 Tower 记录、LimitLayer 与
-- LimitCompatible 记录、迭代嵌入 iterEmbed 及其复合律，以及单位塔实例
-- 框架以 EmbeddingRule R 为参数，使其方向无关；单位实例使用 outer-rule
------------------------------------------------------------------------
{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module SecondPass.CumulativeHierarchyLimit where

open import Agda.Primitive using (Level; _⊔_; lsuc; Setω)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.Reasoning.Setoid as Setoid
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Unit.Polymorphic.Base using (tt)

open import Categories.Functor.Core using (Functor)
open import Categories.Functor using (_∘F_)
open import Categories.NaturalTransformation.NaturalIsomorphism
  using (NaturalIsomorphism)
open import Categories.NaturalTransformation.Core using (ntHelper)

open import SecondPass.Cosmos using (Cosmos; UnitCat; UnitContainerFunctor; UnitCosmos)
open import SecondPass.Terminal using (_≈C_; ≈C-refl; ≈C-trans; cosmosSetoid)
open import SecondPass.CoalgCat using (IsTerminalUpToBisim; cosmosIsTerminal)
open import SecondPass.CumulativeHierarchy using (π)
open import SecondPass.StrictLift
  using (StrictLayer; strictStep-suc; EmbeddingRule; EmbedFamily; outer-rule)

-- Indexing for strictly-growing layers
-- 严格增长层级的索引
record LayerIdx : Set₁ where
  field
    o h e s p : Level

open LayerIdx

-- The index of the layer obtained by applying strictStep-suc
-- strictStep-suc 作用后所得层的索引
nextIdx : LayerIdx → LayerIdx
nextIdx i = record
  { o = o i ⊔ s i
  ; h = h i ⊔ s i
  ; e = e i
  ; s = lsuc (s i ⊔ p i)
  ; p = lsuc (s i ⊔ p i)
  }

-- Iterate nextIdx n times from a starting index
-- 从起始索引出发迭代 nextIdx n 次
idxAt : LayerIdx → ℕ → LayerIdx
idxAt i zero    = i
idxAt i (suc n) = nextIdx (idxAt i n)

-- The shape level strictly grows at each step
-- This is definitional from the definition of nextIdx
-- 形状层级在每步严格增长；由 nextIdx 的定义直接得到
s-strict-at : (i : LayerIdx) (n : ℕ)
            → LayerIdx.s (idxAt i (suc n))
            ≡ lsuc (LayerIdx.s (idxAt i n) ⊔ LayerIdx.p (idxAt i n))
s-strict-at i n = refl

-- Tower record
-- Tower 记录
record Tower (i : LayerIdx) : Setω where
  field
    -- Initial (zeroth) layer
    -- 初始（第零）层
    layer₀ : StrictLayer (o i) (h i) (e i) (s i) (p i)

  -- The n-th layer of the tower
  -- 塔的第 n 层
  layer : ∀ n → let j = idxAt i n in
                StrictLayer (o j) (h j) (e j) (s j) (p j)
  layer zero    = layer₀
  layer (suc n) = strictStep-suc (layer n)

-- Every layer is terminal
-- 每一层都是终余代数
layer-terminal :
    ∀ {o h e s p} (L : StrictLayer o h e s p)
  → IsTerminalUpToBisim {C = StrictLayer.C L} {FC = StrictLayer.FC L}
layer-terminal L = cosmosIsTerminal

-- Every layer of a tower is terminal, indexed by n
-- 塔中每一层都是终余代数，按 n 索引
tower-layer-terminal :
    (i : LayerIdx) (T : Tower i) (n : ℕ)
  → IsTerminalUpToBisim
      {C = StrictLayer.C (Tower.layer T n)}
      {FC = StrictLayer.FC (Tower.layer T n)}
tower-layer-terminal i T n = layer-terminal (Tower.layer T n)

-- Embeddings between consecutive layers preserve bisimulation, for a
-- general embedding rule R
-- 相邻层之间的嵌入保持互模拟，对一般嵌入规则 R
tower-step-preserves-≈C :
    (R : EmbeddingRule)
    (i : LayerIdx) (T : Tower i)
  → (fams : ∀ n → EmbedFamily R (Tower.layer T n))
  → ∀ n {x y}
  → _≈C_ {C = StrictLayer.C (Tower.layer T n)}
          {FC = StrictLayer.FC (Tower.layer T n)} x y
  → _≈C_ {C = StrictLayer.C (Tower.layer T (suc n))}
          {FC = StrictLayer.FC (Tower.layer T (suc n))}
          (EmbeddingRule.Embed R (Tower.layer T n) x
             (EmbedFamily.getData (fams n) x))
          (EmbeddingRule.Embed R (Tower.layer T n) y
             (EmbedFamily.getData (fams n) y))
tower-step-preserves-≈C R i T fams n =
  EmbedFamily.resp-≈C (fams n)

-- Cumulative Hierarchy Limit — limit layer as parameter
-- 累积层级的极限 —— 极限层作为参数

-- The limit layer record
-- 极限层记录
record LimitLayer (i : LayerIdx) (T : Tower i) : Setω where
  field
    o∞ h∞ e∞ s∞ p∞ : Level
    layer∞ : StrictLayer o∞ h∞ e∞ s∞ p∞

    -- Projection functor from the n-th tower layer into the limit layer
    -- 从第 n 个塔层到极限层的投影函子
    projC : ∀ n
          → Functor (StrictLayer.C (Tower.layer T n))
                    (StrictLayer.C layer∞)

open LimitLayer

-- Terminality at the limit layer
-- 极限层的终余代数性质
limit-terminal :
    (i : LayerIdx) (T : Tower i) (L∞ : LimitLayer i T)
  → IsTerminalUpToBisim
      {C  = StrictLayer.C  (L∞ .layer∞)}
      {FC = StrictLayer.FC (L∞ .layer∞)}
limit-terminal i T L∞ = cosmosIsTerminal

-- Compatibility of the tower's step with projC: the projection from the
-- (suc n)-th layer agrees, up to natural isomorphism, with projecting from
-- the n-th layer after the step functor π
-- 塔的步进与 projC 的相容性：从第 suc n 层投影，
-- 与先经步进函子 π 再从第 n 层投影，在自然同构意义下一致
record LimitCompatible {i : LayerIdx} {T : Tower i}
                       (L∞ : LimitLayer i T) : Setω where
  field
    proj-step-coh :
      ∀ n
      → NaturalIsomorphism
          (projC L∞ (suc n))
          (projC L∞ n
            ∘F π (StrictLayer.C  (Tower.layer T n))
                 (StrictLayer.FC (Tower.layer T n)))

open LimitCompatible

-- Cumulative Hierarchy Limit — concrete unit tower
-- 累积层级的极限 —— 具体单位塔

-- The initial layer index for the unit tower, at a fixed universe level ℓ
-- 单位塔的初始层索引，固定宇宙层级 ℓ
unitIdx : (ℓ : Level) → LayerIdx
unitIdx ℓ = record
  { o = ℓ
  ; h = ℓ
  ; e = ℓ
  ; s = ℓ
  ; p = ℓ
  }

-- The initial layer: UnitCat paired with UnitContainerFunctor
-- 初始层：UnitCat 与 UnitContainerFunctor 的配对
unitLayer₀ : (ℓ : Level) → StrictLayer ℓ ℓ ℓ ℓ ℓ
unitLayer₀ ℓ = record
  { C  = UnitCat {ℓ}
  ; FC = UnitContainerFunctor {ℓ}
  }

-- The unit tower: iterating strictStep-suc from the unit initial layer
-- 单位塔：从单位初始层出发迭代 strictStep-suc
unitTower : (ℓ : Level) → Tower (unitIdx ℓ)
unitTower ℓ .Tower.layer₀ = unitLayer₀ ℓ

-- Every layer of the unit tower is terminal
-- 单位塔的每一层都是终余代数
unit-tower-layer-terminal :
    (ℓ : Level) (n : ℕ)
  → IsTerminalUpToBisim
      {C  = StrictLayer.C  (Tower.layer (unitTower ℓ) n)}
      {FC = StrictLayer.FC (Tower.layer (unitTower ℓ) n)}
unit-tower-layer-terminal ℓ n =
  tower-layer-terminal (unitIdx ℓ) (unitTower ℓ) n

-- Layer-level comparison
-- 层级间的比较

-- Enriched towers: iterated strict embeddings preserve bisimulation,
-- parameterised by an embedding rule R
-- 丰富塔：迭代严格嵌入保持互模拟，以嵌入规则 R 为参数
record EnrichedTower (R : EmbeddingRule) (i : LayerIdx) : Setω where
  field
    tower : Tower i
    fams  : ∀ n → EmbedFamily R (Tower.layer tower n)

open EnrichedTower

-- Iterated strict embedding from the zeroth layer
-- Endpoint index is zero + m so that Agda reduces it definitionally to m
-- 从第零层出发的迭代严格嵌入
-- 终点索引为 zero + m，使 Agda 定义性归约为 m
iterEmbed :
    (R : EmbeddingRule) (i : LayerIdx) (ET : EnrichedTower R i) (m : ℕ)
  → Cosmos (StrictLayer.C  (Tower.layer (tower ET) zero))
           (StrictLayer.FC (Tower.layer (tower ET) zero))
  → Cosmos (StrictLayer.C  (Tower.layer (tower ET) (zero + m)))
           (StrictLayer.FC (Tower.layer (tower ET) (zero + m)))
iterEmbed R i ET zero    x = x
iterEmbed R i ET (suc m) x =
  EmbeddingRule.Embed R (Tower.layer (tower ET) (zero + m))
    (iterEmbed R i ET m x)
    (EmbedFamily.getData
       (EnrichedTower.fams ET (zero + m))
       (iterEmbed R i ET m x))

-- Definitional unfolding of iterEmbed at suc
-- iterEmbed 在 suc 处的定义性展开
iterEmbed-suc :
    (R : EmbeddingRule) (i : LayerIdx) (ET : EnrichedTower R i)
    (n : ℕ) (x : _)
  → iterEmbed R i ET (suc n) x
    ≡ EmbeddingRule.Embed R (Tower.layer (tower ET) n)
        (iterEmbed R i ET n x)
        (EmbedFamily.getData
           (EnrichedTower.fams ET n)
           (iterEmbed R i ET n x))
iterEmbed-suc R i ET n x = refl

-- Preservation of bisimulation under iteration
-- 迭代下互模拟的保持
iterEmbed-preserves-≈C :
    (R : EmbeddingRule) (i : LayerIdx) (ET : EnrichedTower R i) (n : ℕ)
  → ∀ {x y : Cosmos (StrictLayer.C  (Tower.layer (tower ET) zero))
                    (StrictLayer.FC (Tower.layer (tower ET) zero))}
  → _≈C_ {C  = StrictLayer.C  (Tower.layer (tower ET) zero)}
          {FC = StrictLayer.FC (Tower.layer (tower ET) zero)}
          x y
  → _≈C_ {C  = StrictLayer.C  (Tower.layer (tower ET) (zero + n))}
          {FC = StrictLayer.FC (Tower.layer (tower ET) (zero + n))}
          (iterEmbed R i ET n x) (iterEmbed R i ET n y)
iterEmbed-preserves-≈C R i ET zero    eq = eq
iterEmbed-preserves-≈C R i ET (suc n) eq =
  EmbedFamily.resp-≈C (EnrichedTower.fams ET n)
    (iterEmbed-preserves-≈C R i ET n eq)

-- Addition recursing on its second argument, so that k +ʳ zero reduces
-- definitionally to k (unlike the standard _+_)
-- 在第二参数上递归的加法，使 k +ʳ zero 定义性归约为 k
--（标准 _+_ 不具备此性质）
infixl 6 _+ʳ_
_+ʳ_ : ℕ → ℕ → ℕ
m +ʳ zero  = m
m +ʳ suc n = suc (m +ʳ n)

-- Iterated strict embedding from an arbitrary layer k
-- Endpoint index uses _+ʳ_ so that k +ʳ zero reduces definitionally to k
-- 从任意第 k 层出发的迭代严格嵌入
-- 终点索引使用 _+ʳ_，使 k +ʳ zero 定义性归约为 k
iterEmbedFrom :
    (R : EmbeddingRule) (i : LayerIdx) (ET : EnrichedTower R i)
  → (k m : ℕ)
  → Cosmos (StrictLayer.C  (Tower.layer (tower ET) k))
           (StrictLayer.FC (Tower.layer (tower ET) k))
  → Cosmos (StrictLayer.C  (Tower.layer (tower ET) (k +ʳ m)))
           (StrictLayer.FC (Tower.layer (tower ET) (k +ʳ m)))
iterEmbedFrom R i ET k zero    x = x
iterEmbedFrom R i ET k (suc m) x =
  EmbeddingRule.Embed R (Tower.layer (tower ET) (k +ʳ m))
    (iterEmbedFrom R i ET k m x)
    (EmbedFamily.getData
       (EnrichedTower.fams ET (k +ʳ m))
       (iterEmbedFrom R i ET k m x))

-- Composite law of iterated embedding at layer zero
-- 第零层上迭代嵌入的复合律
iterEmbed-add :
    (R : EmbeddingRule) (i : LayerIdx) (ET : EnrichedTower R i)
    (m n : ℕ)
    (x : Cosmos (StrictLayer.C  (Tower.layer (tower ET) zero))
                (StrictLayer.FC (Tower.layer (tower ET) zero)))
  → _≈C_ {C  = StrictLayer.C  (Tower.layer (tower ET) (m +ʳ n))}
          {FC = StrictLayer.FC (Tower.layer (tower ET) (m +ʳ n))}
          (iterEmbed R i ET (m +ʳ n) x)
          (iterEmbedFrom R i ET m n (iterEmbed R i ET m x))
iterEmbed-add R i ET m zero    x = ≈C-refl
iterEmbed-add R i ET m (suc n) x =
  EmbedFamily.resp-≈C (EnrichedTower.fams ET (m +ʳ n))
    (iterEmbed-add R i ET m n x)

-- Every layer of an enriched tower is terminal
-- 丰富塔的每一层都是终余代数
enriched-layer-terminal :
    (R : EmbeddingRule) (i : LayerIdx) (ET : EnrichedTower R i) (n : ℕ)
  → IsTerminalUpToBisim
      {C  = StrictLayer.C  (Tower.layer (tower ET) n)}
      {FC = StrictLayer.FC (Tower.layer (tower ET) n)}
enriched-layer-terminal R i ET n =
  tower-layer-terminal i (tower ET) n

-- Cumulative Hierarchy Limit — stitching Stage 2 with EnrichedTower
-- 累积层级的极限 —— 缝合阶段 2 与 EnrichedTower

-- Lifted limit structure
-- 提升极限结构
record LiftedLimitStructure (R : EmbeddingRule) (i : LayerIdx)
                             (ET : EnrichedTower R i) : Setω where
  private
    T  = EnrichedTower.tower ET
    FS = EnrichedTower.fams ET
  field
    limit : LimitLayer i T

    -- Layer-lifting map from the n-th layer's Cosmos to the limit layer's
    -- 从第 n 层 Cosmos 到极限层 Cosmos 的层提升映射
    liftAt : ∀ n
           → Cosmos (StrictLayer.C  (Tower.layer T n))
                    (StrictLayer.FC (Tower.layer T n))
           → Cosmos (StrictLayer.C  (LimitLayer.layer∞ limit))
                    (StrictLayer.FC (LimitLayer.layer∞ limit))

    -- liftAt preserves bisimulation at every layer
    -- liftAt 在每一层保持互模拟
    liftAt-resp-≈C : ∀ n {x y}
                   → _≈C_ {C  = StrictLayer.C  (Tower.layer T n)}
                           {FC = StrictLayer.FC (Tower.layer T n)}
                           x y
                   → _≈C_ {C  = StrictLayer.C  (LimitLayer.layer∞ limit)}
                           {FC = StrictLayer.FC (LimitLayer.layer∞ limit)}
                           (liftAt n x) (liftAt n y)

    -- Compatibility with one strict step: lifting after embedding equals
    -- lifting directly from the previous layer
    -- 与一步严格嵌入的相容性：嵌入后再提升，等于直接从上一层提升
    liftAt-step : ∀ n x
                → liftAt (suc n)
                    (EmbeddingRule.Embed R (Tower.layer T n) x
                       (EmbedFamily.getData (FS n) x))
                  ≈C liftAt n x

open LiftedLimitStructure

-- Compatibility of iteration with lifting
-- 迭代与提升的相容性
liftAt-iterEmbed :
    (R : EmbeddingRule) (i : LayerIdx) (ET : EnrichedTower R i)
    (LLS : LiftedLimitStructure R i ET)
  → ∀ n (x : Cosmos (StrictLayer.C  (Tower.layer (EnrichedTower.tower ET) zero))
                    (StrictLayer.FC (Tower.layer (EnrichedTower.tower ET) zero)))
  → liftAt LLS n (iterEmbed R i ET n x)
    ≈C liftAt LLS zero x
liftAt-iterEmbed R i ET LLS zero    x = ≈C-refl
liftAt-iterEmbed R i ET LLS (suc n) x =
  ≈C-trans
    (liftAt-step LLS n (iterEmbed R i ET n x))
    (liftAt-iterEmbed R i ET LLS n x)

-- Compatibility of iterated embedding from an arbitrary layer with lifting
-- 任意层出发的迭代嵌入与提升的相容性
liftAt-iterEmbedFrom :
    (R : EmbeddingRule) (i : LayerIdx) (ET : EnrichedTower R i)
    (LLS : LiftedLimitStructure R i ET)
  → ∀ k m
    (x : Cosmos (StrictLayer.C  (Tower.layer (EnrichedTower.tower ET) k))
                (StrictLayer.FC (Tower.layer (EnrichedTower.tower ET) k)))
  → liftAt LLS (k +ʳ m) (iterEmbedFrom R i ET k m x)
    ≈C liftAt LLS k x
liftAt-iterEmbedFrom R i ET LLS k zero    x = ≈C-refl
liftAt-iterEmbedFrom R i ET LLS k (suc m) x =
  ≈C-trans
    (liftAt-step LLS (k +ʳ m) (iterEmbedFrom R i ET k m x))
    (liftAt-iterEmbedFrom R i ET LLS k m x)

-- Composition law for liftAt: iterating m then n steps agrees with
-- iterating m +ʳ n steps at the limit layer
-- 提升的复合律：先 m 步再 n 步与一次 m +ʳ n 步在极限层一致
liftAt-compose :
    (R : EmbeddingRule) (i : LayerIdx) (ET : EnrichedTower R i)
    (LLS : LiftedLimitStructure R i ET)
  → ∀ k m n
    (x : Cosmos (StrictLayer.C  (Tower.layer (EnrichedTower.tower ET) k))
                (StrictLayer.FC (Tower.layer (EnrichedTower.tower ET) k)))
  → liftAt LLS (k +ʳ (m +ʳ n)) (iterEmbedFrom R i ET k (m +ʳ n) x)
    ≈C liftAt LLS ((k +ʳ m) +ʳ n)
         (iterEmbedFrom R i ET (k +ʳ m) n (iterEmbedFrom R i ET k m x))
liftAt-compose R i ET LLS k m n x =
  let
    C∞  = StrictLayer.C  (LimitLayer.layer∞ (limit LLS))
    FC∞ = StrictLayer.FC (LimitLayer.layer∞ (limit LLS))
    module R' = Setoid (cosmosSetoid {C = C∞} {FC = FC∞})
  in R'.begin
      liftAt LLS (k +ʳ (m +ʳ n)) (iterEmbedFrom R i ET k (m +ʳ n) x)
        R'.≈⟨ liftAt-iterEmbedFrom R i ET LLS k (m +ʳ n) x ⟩
      liftAt LLS k x
        R'.≈˘⟨ liftAt-iterEmbedFrom R i ET LLS k m x ⟩
      liftAt LLS (k +ʳ m) (iterEmbedFrom R i ET k m x)
        R'.≈˘⟨ liftAt-iterEmbedFrom R i ET LLS (k +ʳ m) n
                                          (iterEmbedFrom R i ET k m x) ⟩
      liftAt LLS ((k +ʳ m) +ʳ n)
        (iterEmbedFrom R i ET (k +ʳ m) n (iterEmbedFrom R i ET k m x))
    R'.∎

-- Preservation of _≈C_ through the composite
-- 复合路径下 _≈C_ 的保持
liftAt-iterEmbed-resp-≈C :
    (R : EmbeddingRule) (i : LayerIdx) (ET : EnrichedTower R i)
    (LLS : LiftedLimitStructure R i ET) (n : ℕ)
  → ∀ {x y : Cosmos (StrictLayer.C  (Tower.layer (EnrichedTower.tower ET) zero))
                    (StrictLayer.FC (Tower.layer (EnrichedTower.tower ET) zero))}
  → _≈C_ {C  = StrictLayer.C  (Tower.layer (EnrichedTower.tower ET) zero)}
          {FC = StrictLayer.FC (Tower.layer (EnrichedTower.tower ET) zero)}
          x y
  → _≈C_ {C  = StrictLayer.C  (LimitLayer.layer∞ (limit LLS))}
          {FC = StrictLayer.FC (LimitLayer.layer∞ (limit LLS))}
          (liftAt LLS n (iterEmbed R i ET n x))
          (liftAt LLS n (iterEmbed R i ET n y))
liftAt-iterEmbed-resp-≈C R i ET LLS n eq =
  liftAt-resp-≈C LLS n (iterEmbed-preserves-≈C R i ET n eq)

-- Direct lifting from the zeroth layer preserves _≈C_
-- 从第零层直接提升保持 _≈C_
lift-zero-resp-≈C :
    (R : EmbeddingRule) (i : LayerIdx) (ET : EnrichedTower R i)
    (LLS : LiftedLimitStructure R i ET)
  → ∀ {x y : Cosmos (StrictLayer.C  (Tower.layer (EnrichedTower.tower ET) zero))
                    (StrictLayer.FC (Tower.layer (EnrichedTower.tower ET) zero))}
  → _≈C_ {C  = StrictLayer.C  (Tower.layer (EnrichedTower.tower ET) zero)}
          {FC = StrictLayer.FC (Tower.layer (EnrichedTower.tower ET) zero)}
          x y
  → _≈C_ {C  = StrictLayer.C  (LimitLayer.layer∞ (limit LLS))}
          {FC = StrictLayer.FC (LimitLayer.layer∞ (limit LLS))}
          (liftAt LLS zero x) (liftAt LLS zero y)
lift-zero-resp-≈C R i ET LLS = liftAt-resp-≈C LLS zero

-- Terminality at the lifted limit layer
-- 提升极限层的终余代数性
lifted-limit-terminal :
    (R : EmbeddingRule) (i : LayerIdx) (ET : EnrichedTower R i)
    (LLS : LiftedLimitStructure R i ET)
  → IsTerminalUpToBisim
      {C  = StrictLayer.C  (LimitLayer.layer∞ (limit LLS))}
      {FC = StrictLayer.FC (LimitLayer.layer∞ (limit LLS))}
lifted-limit-terminal R i ET LLS =
  limit-terminal i (EnrichedTower.tower ET) (limit LLS)

-- Cumulative Hierarchy Limit — Unit Instance
-- 累积层级的极限 —— 单位实例

-- A family of functorial embedding data at every layer of the unit tower,
-- along the outer-preserving rule
-- 单位塔每一层上沿保外层规则的函子性嵌入数据族
UnitFamily : (ℓ : Level) → Setω
UnitFamily ℓ =
  ∀ n → EmbedFamily outer-rule (Tower.layer (unitTower ℓ) n)

-- The enriched unit tower, parameterised by the family
-- 以嵌入族为参数的丰富单位塔
unitEnrichedTower : (ℓ : Level) → UnitFamily ℓ
                  → EnrichedTower outer-rule (unitIdx ℓ)
unitEnrichedTower ℓ fams = record
  { tower = unitTower ℓ
  ; fams  = fams
  }

-- The limit layer over the unit tower
-- 单位塔上的极限层
unitLimit : (ℓ ℓ∞ : Level) → LimitLayer (unitIdx ℓ) (unitTower ℓ)
unitLimit ℓ ℓ∞ = record
  { o∞ = ℓ∞
  ; h∞ = ℓ∞
  ; e∞ = ℓ∞
  ; s∞ = ℓ∞
  ; p∞ = ℓ∞
  ; layer∞ = record
      { C  = UnitCat {ℓ∞}
      ; FC = UnitContainerFunctor {ℓ∞}
      }
  ; projC = λ n → record
      { F₀           = λ _ → tt
      ; F₁           = λ _ → tt
      ; identity     = tt
      ; homomorphism = tt
      ; F-resp-≈     = λ _ → tt
      }
  }

-- The natural isomorphism witnessing that projC is compatible with the
-- tower step: projC (suc n) ≅ projC n ∘F π_n
-- 见证 projC 与塔步进相容的自然同构：projC (suc n) ≅ projC n ∘F π_n
unitLimit-compatible : (ℓ ℓ∞ : Level) → LimitCompatible (unitLimit ℓ ℓ∞)
unitLimit-compatible ℓ ℓ∞ = record
  { proj-step-coh = λ n → record
      { F⇒G = ntHelper record
          { η       = λ _ → tt
          ; commute = λ _ → tt
          }
      ; F⇐G = ntHelper record
          { η       = λ _ → tt
          ; commute = λ _ → tt
          }
      ; iso = λ _ → record { isoˡ = tt ; isoʳ = tt }
      }
  }

-- The lifted limit structure
-- 提升极限结构

-- The unit tower's lifting map: every layer collapses to UnitCosmos
-- 单位塔的提升映射：每一层都坍缩到 UnitCosmos
unitLiftAt : (ℓ ℓ∞ : Level) (n : ℕ)
           → Cosmos (StrictLayer.C  (Tower.layer (unitTower ℓ) n))
                    (StrictLayer.FC (Tower.layer (unitTower ℓ) n))
           → Cosmos (UnitCat {ℓ∞}) (UnitContainerFunctor {ℓ∞})
unitLiftAt ℓ ℓ∞ n _ = UnitCosmos {ℓ∞}

unitLiftedLimitStructure :
    (ℓ ℓ∞ : Level) (fams : UnitFamily ℓ)
  → LiftedLimitStructure outer-rule (unitIdx ℓ) (unitEnrichedTower ℓ fams)
unitLiftedLimitStructure ℓ ℓ∞ fams = record
  { limit          = unitLimit ℓ ℓ∞
  ; liftAt         = unitLiftAt ℓ ℓ∞
  ; liftAt-resp-≈C = λ n _ → ≈C-refl
  ; liftAt-step    = λ n x → ≈C-refl
  }

-- Stitching theorem at the unit tower
-- 单位塔上的缝合定理
unit-liftAt-iterEmbed :
    (ℓ ℓ∞ : Level) (fams : UnitFamily ℓ) (n : ℕ)
    (x : Cosmos (StrictLayer.C  (Tower.layer (unitTower ℓ) zero))
                (StrictLayer.FC (Tower.layer (unitTower ℓ) zero)))
  → _≈C_ {C  = UnitCat {ℓ∞}}
          {FC = UnitContainerFunctor {ℓ∞}}
          (LiftedLimitStructure.liftAt
            (unitLiftedLimitStructure ℓ ℓ∞ fams) n
            (iterEmbed outer-rule (unitIdx ℓ)
                       (unitEnrichedTower ℓ fams) n x))
          (LiftedLimitStructure.liftAt
            (unitLiftedLimitStructure ℓ ℓ∞ fams) zero x)
unit-liftAt-iterEmbed ℓ ℓ∞ fams =
  liftAt-iterEmbed outer-rule (unitIdx ℓ)
                   (unitEnrichedTower ℓ fams)
                   (unitLiftedLimitStructure ℓ ℓ∞ fams)
