------------------------------------------------------------------------
-- CumulativeHierarchySewing — stitching, obstruction, and direction dichotomy
-- UnitSewing: unit tower stitches; unit limit is terminal
-- FinCatSewing: outer-rule obstruction at layer 1
-- DirectionDichotomy: for a rigid strict layer, outer-rule propagates
-- EmbeddingData iff every shape type is a singleton
--
-- 累积层级缝合 —— 缝合、障碍与方向二分
-- UnitSewing：单位塔缝合；单位极限终余代数
-- FinCatSewing：outer-rule 在第 1 层的障碍
-- DirectionDichotomy：对刚性严格层，outer-rule 传播 EmbeddingData
-- 当且仅当每个形状类型单元素
------------------------------------------------------------------------
{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module SecondPass.CumulativeHierarchySewing where

open import Agda.Primitive using (Level; lzero; _⊔_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Sigma using (_,_)
open import Level using (lift; lower)
open import Relation.Binary.PropositionalEquality.Core
  using (_≢_; sym; cong; trans; subst)
open import Relation.Nullary using (¬_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Fin.Base using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.Unit.Polymorphic.Base using (tt)
open import Data.Product.Base using (proj₁; proj₂; ∃)
open import Data.Product.Properties using (Σ-≡,≡→≡)
open import Function.Bundles using (_⇔_; mk⇔)

open import Categories.Category.Core using (Category)
open import Categories.Functor.Core using (Functor)

open import Cosmos.ContCategory using (_≈sr_)
open import Cosmos.ContCategoryLemmas using (ShapeOf; actSOf)
open import Cosmos.ContCatEquiv using (ShapeCat)
open import SecondPass.Unfolding using (Unfolding)
open import SecondPass.Cosmos using (Cosmos; out; UnitCosmos)
open import SecondPass.Terminal using (_≈C_; ≈C-refl)
open import SecondPass.CoalgCat using (IsTerminalUpToBisim)
open import SecondPass.CumulativeHierarchy
  using (π; Collapsible; collapsible→ShapeCat-collapsible; EmbeddingData
        ; EmbeddingFamily; UniformEmbeddingFamily; FC∘π)
open import SecondPass.StrictLift
  using (StrictLayer; strictEmbed; strictStep-suc; EmbedFamily; outer-rule)
open import SecondPass.CumulativeHierarchyInstances
  using (module BuildUniformFrom; module FinCatHierarchy)
open FinCatHierarchy using (FinCat; FinFC; embedFin)
open import SecondPass.CumulativeHierarchyLimit
  using (unitIdx; Tower; EnrichedTower; unitTower; LimitLayer; unitLimit
        ; LiftedLimitStructure; iterEmbed; liftAt-iterEmbed; lifted-limit-terminal)

-- The unit tower stitches successfully not because it uses a different
-- direction, but because UnitCat's shape type is ⊤ (a singleton), which
-- makes the outer direction's obstruction vacuous
--
-- 单位塔缝合成功并非因为使用了不同方向，而是因为 UnitCat 的形状类型
-- 是 ⊤（单元素），使外层方向的障碍空洞化
module UnitSewing {ℓ : Level} where
  -- Shapes at every layer of the unit tower are singletons
  --
  -- 单位塔每一层的形状是单元素
  shape-unique
    : (n : ℕ)
      (A : Category.Obj (StrictLayer.C (Tower.layer (unitTower ℓ) n)))
    → (s t : ShapeOf (StrictLayer.FC (Tower.layer (unitTower ℓ) n)) A)
    → s ≡ t
  shape-unique zero    A s t = refl
  shape-unique (suc n) (A , _) (lift u) (lift v) =
    cong lift (shape-unique n A u v)

  -- Objects at every layer of the unit tower are singletons
  --
  -- 单位塔每一层的对象是单元素
  obj-unique
    : (n : ℕ)
    → (X Y : Category.Obj (StrictLayer.C (Tower.layer (unitTower ℓ) n)))
    → X ≡ Y
  obj-unique zero    X Y = refl
  obj-unique (suc n) (A₁ , s₁) (A₂ , s₂) =
    Σ-≡,≡→≡ (A≡ , B-eq)
    where
      A≡ : A₁ ≡ A₂
      A≡ = obj-unique n A₁ A₂

      B-eq : subst (ShapeOf (StrictLayer.FC (Tower.layer (unitTower ℓ) n)))
                   A≡ s₁
             ≡ s₂
      B-eq = shape-unique n A₂ _ s₂

  -- Every layer of the unit tower is collapsible
  --
  -- 单位塔的每一层都是可坍缩的
  collapse
    : (n : ℕ)
    → Collapsible (StrictLayer.C (Tower.layer (unitTower ℓ) n))
  collapse zero    = λ _ _ → tt
  collapse (suc n) =
    collapsible→ShapeCat-collapsible
      {C  = StrictLayer.C  (Tower.layer (unitTower ℓ) n)}
      {FC = StrictLayer.FC (Tower.layer (unitTower ℓ) n)}
      (collapse n)

  -- Uniform embedding family at each layer
  --
  -- 每一层的一致嵌入族
  uniformAt : (n : ℕ)
    → UniformEmbeddingFamily
        {C  = StrictLayer.C  (Tower.layer (unitTower ℓ) n)}
        {FC = StrictLayer.FC (Tower.layer (unitTower ℓ) n)}
  uniformAt n =
    BuildUniformFrom.uniform
      (StrictLayer.C  (Tower.layer (unitTower ℓ) n))
      (StrictLayer.FC (Tower.layer (unitTower ℓ) n))
      (obj-unique n)
      (collapse n)

  -- strictEmbed preserves _≈C_ at every layer
  --
  -- strictEmbed 在每一层保持 _≈C_
  resp
    : (n : ℕ)
    → ∀ {x y : Cosmos (StrictLayer.C  (Tower.layer (unitTower ℓ) n))
                       (StrictLayer.FC (Tower.layer (unitTower ℓ) n))}
    → (edx : EmbeddingData x) (edy : EmbeddingData y)
    → x ≈C y
    → _≈C_
        {C  = StrictLayer.C  (Tower.layer (unitTower ℓ) (suc n))}
        {FC = StrictLayer.FC (Tower.layer (unitTower ℓ) (suc n))}
        (strictEmbed (Tower.layer (unitTower ℓ) n) x edx)
        (strictEmbed (Tower.layer (unitTower ℓ) n) y edy)
  resp n {x} {y} edx edy eq ._≈C_.unfoldFunctor₀-eq s = refl
  resp n {x} {y} edx edy eq ._≈C_.pos-to-shape-eq {A} s p =
    shape-unique (suc n) (proj₁ A , lower s) _ _
  resp n {x} {y} edx edy eq ._≈C_.unfold-next-eq s =
    resp n
      (EmbeddingData.next edx (lower s))
      (EmbeddingData.next edy (lower s))
      (eq ._≈C_.unfold-next-eq (lower s))

  -- Specialisation to the canonical uniform family
  --
  -- 特化到典范一致族
  resp-specialized
    : (n : ℕ)
    → ∀ {x y : Cosmos (StrictLayer.C  (Tower.layer (unitTower ℓ) n))
                       (StrictLayer.FC (Tower.layer (unitTower ℓ) n))}
    → x ≈C y
    → _≈C_
        {C  = StrictLayer.C  (Tower.layer (unitTower ℓ) (suc n))}
        {FC = StrictLayer.FC (Tower.layer (unitTower ℓ) (suc n))}
        (strictEmbed (Tower.layer (unitTower ℓ) n) x
          (EmbeddingFamily.getData
            (UniformEmbeddingFamily.family (uniformAt n)) x))
        (strictEmbed (Tower.layer (unitTower ℓ) n) y
          (EmbeddingFamily.getData
            (UniformEmbeddingFamily.family (uniformAt n)) y))
  resp-specialized n {x} {y} eq =
    resp n
      (EmbeddingFamily.getData
        (UniformEmbeddingFamily.family (uniformAt n)) x)
      (EmbeddingFamily.getData
        (UniformEmbeddingFamily.family (uniformAt n)) y)
      eq

  -- EmbedFamily outer-rule at every layer
  --
  -- 每一层上沿保外层规则的嵌入族
  unitFam
    : (n : ℕ)
    → EmbedFamily outer-rule (Tower.layer (unitTower ℓ) n)
  unitFam n = record
    { uniform  = uniformAt n
    ; resp-≈C = resp-specialized n
    }

  -- The concrete enriched unit tower, along the outer-preserving rule
  --
  -- 沿保外层规则的具体丰富单位塔
  unitEnrichedTower : EnrichedTower outer-rule (unitIdx ℓ)
  unitEnrichedTower = record
    { tower = unitTower ℓ
    ; fams  = unitFam
    }

  -- The concrete lifted limit structure
  --
  -- 具体提升极限结构
  unitLiftedStructure
    : LiftedLimitStructure outer-rule (unitIdx ℓ) unitEnrichedTower
  unitLiftedStructure = record
    { limit          = unitLimit ℓ ℓ
    ; liftAt         = λ _ _ → UnitCosmos {ℓ}
    ; liftAt-resp-≈C = λ _ _ → ≈C-refl
    ; liftAt-step    = λ _ _ → ≈C-refl
    }

  -- Stitching theorem for the unit tower
  --
  -- 单位塔的缝合定理
  unitSewing
    : ∀ n
      (x : Cosmos (StrictLayer.C  (Tower.layer (unitTower ℓ) zero))
                  (StrictLayer.FC (Tower.layer (unitTower ℓ) zero)))
    → _≈C_
        {C  = StrictLayer.C  (LimitLayer.layer∞ (unitLimit ℓ ℓ))}
        {FC = StrictLayer.FC (LimitLayer.layer∞ (unitLimit ℓ ℓ))}
        (LiftedLimitStructure.liftAt unitLiftedStructure n
          (iterEmbed outer-rule (unitIdx ℓ) unitEnrichedTower n x))
        (LiftedLimitStructure.liftAt unitLiftedStructure zero x)
  unitSewing =
    liftAt-iterEmbed outer-rule (unitIdx ℓ) unitEnrichedTower unitLiftedStructure

  -- Corollary: the unit limit is terminal
  --
  -- 推论：单位极限是终余代数
  unit-limit-terminal
    : IsTerminalUpToBisim
        {C  = StrictLayer.C  (LimitLayer.layer∞ (unitLimit ℓ ℓ))}
        {FC = StrictLayer.FC (LimitLayer.layer∞ (unitLimit ℓ ℓ))}
  unit-limit-terminal =
    lifted-limit-terminal outer-rule (unitIdx ℓ)
                          unitEnrichedTower unitLiftedStructure

-- FinCat 2 tower — single-step stitching and obstruction
--
-- FinCat 2 塔 —— 单步缝合与障碍
module FinCatSewing where

  -- Zeroth and first layers of the FinCat 2 tower
  --
  -- FinCat 2 塔的第零层与第一层
  Cosmos₀ : Set lzero
  Cosmos₀ = Cosmos (FinCat 2) (FinFC 2)

  Cosmos₁ : Set lzero
  Cosmos₁ = Cosmos (ShapeCat (FinCat 2) (FinFC 2)) (FC∘π (FinFC 2))

  -- Single-step embedding and its bisimulation preservation
  --
  -- 单步嵌入及其互模拟保持性
  embed-step : Cosmos₀ → Cosmos₁
  embed-step = embedFin 2

  -- Obstruction theorem: multi-step stitching fails at layer 1
  -- A concrete cosmos at layer 0. Since FinCat 2 has _⇒_ = ⊤, the
  -- unfoldFunctor can be defined by first-component projection and
  -- all structural fields are trivial
  --
  -- 障碍定理：多步缝合在第 1 层失败
  -- 第 0 层的一个具体宇宙。因 FinCat 2 的 _⇒_ = ⊤，
  -- unfoldFunctor 可取第一分量投影，所有结构字段均为平凡值
  fin-cosmos₀ : Cosmos (FinCat 2) (FinFC 2)
  fin-cosmos₀ .out = record
    { unfoldFunctor = record
        { F₀           = proj₁
        ; F₁           = proj₁
        ; identity     = refl
        ; homomorphism = refl
        ; F-resp-≈     = λ _ → refl
        }
    ; unfold-next     = λ _ → fin-cosmos₀
    ; pos-to-shape    = λ _ _ → fzero {1}
    ; pos-actS-compat = λ _ _ _ → refl
    }

  -- The counterexample cosmos at layer 1
  --
  -- 第 1 层的反例宇宙
  x₁ : Cosmos₁
  x₁ = embed-step fin-cosmos₀

  -- In Fin 2, 1 ≠ 0
  -- Fin 2 中 1 ≠ 0
  1≢0-fin2 : ¬ (fsuc {n = 1} (fzero {0}) ≡ fzero {1})
  1≢0-fin2 ()

  -- Obstruction: if x changes some shape s₀ to s' ≢ s₀, EmbeddingData x
  -- is impossible (ShapeCat morphisms carry a proof s' ≡ s₀)
  --
  -- 若 x 的展开函子在某处把形状 s₀ 改成 s' ≢ s₀，则 EmbeddingData x
  -- 不可构造（因 ShapeCat 的态射携带 s' ≡ s₀ 的证明）
  obstruction-from-shape-change
    : ∀ (x : Cosmos₁) (A : Fin 2) (s₀ s₁ : Fin 2)
    → proj₂ (Functor.₀ (Unfolding.unfoldFunctor (out x))
                       ((A , s₀) , s₁)) ≢ s₀
    → ¬ (EmbeddingData x)
  obstruction-from-shape-change x A s₀ s₁ s'≢s₀ ed =
    s'≢s₀ (proj₂ (EmbeddingData.retract ed {A = (A , s₀)} s₁))

  -- x₁ is an instance: for x₁ = embed-step fin-cosmos₀, the outer
  -- unfold functor has F₀ ((A, s₀), s₁) = (A, s₁), so its second
  -- component at (fzero, fzero, fsuc fzero) is fsuc fzero ≢ fzero
  --
  -- x₁ 是一般定理的实例：x₁ = embed-step fin-cosmos₀ 的外层展开函子
  -- 满足 F₀ ((A, s₀), s₁) = (A, s₁)，故在 (fzero, fzero, fsuc fzero)
  -- 处第二分量为 fsuc fzero ≢ fzero
  x₁-shape-changed
    : proj₂ (Functor.₀ (Unfolding.unfoldFunctor (out x₁))
                       ((fzero , fzero) , fsuc fzero)) ≢ fzero
  x₁-shape-changed = 1≢0-fin2

  embedding-blocked : ¬ (EmbeddingData x₁)
  embedding-blocked =
    obstruction-from-shape-change x₁ fzero fzero (fsuc fzero) x₁-shape-changed

  -- Multi-step stitching is obstructed: there exists x : Cosmos₁
  -- such that EmbeddingData x is unconstructible
  --
  -- 多步缝合受阻：存在 x : Cosmos₁ 使 EmbeddingData x 不可构造
  stitching-obstructed : ∃ (λ (x : Cosmos₁) → ¬ (EmbeddingData x))
  stitching-obstructed = x₁ , embedding-blocked

  -- If x changes the shape component somewhere, x is obstructed
  --
  -- 若 x 在某处改变了形状分量，则 x 受阻
  obstructed-if-shape-not-preserved
    : ∀ (x : Cosmos₁)
    → (∃ λ (A : Fin 2) → ∃ λ (s₀ : Fin 2) → ∃ λ (s₁ : Fin 2) →
         proj₂ (Functor.₀ (Unfolding.unfoldFunctor (out x))
                          ((A , s₀) , s₁)) ≢ s₀)
    → ¬ (EmbeddingData x)
  obstructed-if-shape-not-preserved x (A , s₀ , s₁ , s'≢s₀) =
    obstruction-from-shape-change x A s₀ s₁ s'≢s₀

-- DirectionDichotomy — outer-rule propagation boundary
--
-- 方向二分 —— outer-rule 传播边界
module DirectionDichotomy
  {o h e s p : Level} (L : StrictLayer o h e s p) where
  private
    C_L  = StrictLayer.C L
    FC_L = StrictLayer.FC L
    FC'  = StrictLayer.FC (strictStep-suc L)
    module C_L' = Category (ShapeCat C_L FC_L)
    module C_L  = Category C_L

  -- Rigidity: an endomorphism carries s to t only when s ≡ t.
  -- Equivalent to shape-constancy, but stated without referring to the
  -- action of a specific endomorphism
  --
  -- 刚性：自态射把 s 送到 t 仅当 s ≡ t。
  -- 等价于形状作用平凡，但表述不依赖于某个特定自态射的作用
  Rigid : Set (o ⊔ h ⊔ s)
  Rigid =
    ∀ {A : Category.Obj C_L} (s t : ShapeOf FC_L A)
    → (∃ λ (f : Category._⇒_ C_L A A) → actSOf FC_L f s ≡ t)
    → s ≡ t

  -- Identity acts trivially on shapes, by the functor identity law
  --
  -- 恒等态射在形状上作用平凡，由函子恒等律给出
  actSOf-id
    : ∀ {A : Category.Obj C_L} (s : ShapeOf FC_L A)
    → actSOf FC_L (Category.id C_L) s ≡ s
  actSOf-id {A} s =
    _≈sr_.shape-eq identity s
    where
      open Functor FC_L using (identity)

  private
    -- The canonical cosmos on the projection π: unfoldFunctor = π,
    -- pos-to-shape = id
    --
    -- 投影 π 上的典范宇宙：unfoldFunctor = π，pos-to-shape = id
    trivial-cosmos : Cosmos C_L FC_L
    trivial-cosmos .out = record
      { unfoldFunctor   = π C_L FC_L
      ; unfold-next     = λ _ → trivial-cosmos
      ; pos-to-shape    = λ s _ → s
      ; pos-actS-compat = λ f eq p → sym eq
      }

    -- Its canonical EmbeddingData: retract = id, naturality from unit laws
    --
    -- 其典范 EmbeddingData：retract = id，自然性由单位律给出
    trivial-ed : EmbeddingData trivial-cosmos
    trivial-ed .EmbeddingData.retract {A} s =
      Category.id C_L
    trivial-ed .EmbeddingData.retract-natural {A} {B} {s} {t} f eq =
      C_L.Equiv.trans
        (C_L.identityʳ {f = f})
        (C_L.Equiv.sym (C_L.identityˡ {f = f}))
    trivial-ed .EmbeddingData.next s = trivial-ed

  -- Sufficiency: singletons make outer propagate unconditionally
  --
  -- 充分性：形状单元素使外层无条件传播
  outer-propagates-of-singleton
    : (singleton : ∀ (A : Category.Obj C_L)
                 → (σ τ : ShapeOf FC_L A) → σ ≡ τ)
    → (x : Cosmos C_L FC_L) (ed : EmbeddingData x)
    → EmbeddingData (strictEmbed L x ed)
  outer-propagates-of-singleton singleton x ed
    .EmbeddingData.retract {A} s-lift =
      ( Category.id C_L
      , trans (actSOf-id (lower s-lift))
              (singleton (proj₁ A) (lower s-lift) (proj₂ A)) )
  outer-propagates-of-singleton singleton x ed
    .EmbeddingData.retract-natural {A} {B} {s-lift} {t-lift} g eq =
    C_L.Equiv.trans
      (C_L.identityʳ {f = proj₁ g})
      (C_L.Equiv.sym (C_L.identityˡ {f = proj₁ g}))
  outer-propagates-of-singleton singleton x ed
    .EmbeddingData.next {A} s-lift =
      outer-propagates-of-singleton singleton
        (Unfolding.unfold-next (out x) {A = proj₁ A} (lower s-lift))
        (EmbeddingData.next ed {A = proj₁ A} (lower s-lift))

  -- Dichotomy (under rigidity): outer propagates iff shapes are singletons
  --
  -- 二分定理（在刚性假设下）：外层传播当且仅当形状单元素
  outer-propagates-iff-singleton
      : (rigid : Rigid)
      → ((x : Cosmos C_L FC_L) (ed : EmbeddingData x)
         → EmbeddingData (strictEmbed L x ed))
        ⇔ (∀ (A : Category.Obj C_L)
           → (σ τ : ShapeOf FC_L A) → σ ≡ τ)
  outer-propagates-iff-singleton rigid = mk⇔ to from
    where
      to : ((x : Cosmos C_L FC_L) (ed : EmbeddingData x)
            → EmbeddingData (strictEmbed L x ed))
           → ∀ (A : Category.Obj C_L)
             → (σ τ : ShapeOf FC_L A) → σ ≡ τ
      to p A σ τ =
        let edy = p trivial-cosmos trivial-ed
            A'  = A , τ
            r   = EmbeddingData.retract edy {A = A'} (lift σ)
        in rigid σ τ (proj₁ r , proj₂ r)

      from : (∀ (A : Category.Obj C_L)
              → (σ τ : ShapeOf FC_L A) → σ ≡ τ)
           → (x : Cosmos C_L FC_L) (ed : EmbeddingData x)
           → EmbeddingData (strictEmbed L x ed)
      from = outer-propagates-of-singleton
