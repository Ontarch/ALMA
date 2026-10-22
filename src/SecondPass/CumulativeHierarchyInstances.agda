------------------------------------------------------------------------
-- Cumulative Hierarchy of Cosmoi — Concrete Instances
-- Provides concrete instances of EmbeddingData, UniformEmbeddingFamily,
-- FunctorialEmbeddingFamily, and LambekConsistency for the terminal
-- category UnitCat and for FinCat n, together with the hierarchy
-- constructions based on them
--
-- 宇宙的累积层级 —— 具体实例
-- 为终范畴 UnitCat 及 FinCat n 提供 EmbeddingData、UniformEmbeddingFamily、
-- FunctorialEmbeddingFamily 与 LambekConsistency 的具体实例，
-- 并给出基于这些实例的层级构造
------------------------------------------------------------------------
{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module SecondPass.CumulativeHierarchyInstances where

open import Agda.Primitive using (Level; lsuc; lzero)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Sigma using (_,_)
open import Level using (lift; lower)
open import Relation.Binary.PropositionalEquality.Core using (sym; cong; subst)
open import Relation.Binary.PropositionalEquality.Properties using (module ≡-Reasoning)
open ≡-Reasoning
open import Data.Nat using (ℕ)
open import Data.Fin.Base using (Fin)
open import Data.Unit.Polymorphic.Base using (tt)
open import Data.Product.Base using (proj₁)
open import Function.Base using (_∘_)

open import Categories.Category.Core using (Category)
open import Categories.Category.Indiscrete using (Indiscrete)
open import Categories.Functor.Core using (Functor)

open import Cosmos.ContCategory using (ContCat; ≈sr-refl)
open import Cosmos.ContCategoryLemmas using (ShapeOf; PosOf)
open import Cosmos.ContCatEquiv using (ShapeCat)
open import SecondPass.Unfolding using (Unfolding)
open import SecondPass.Cosmos using (Cosmos; out; UnitCat; UnitContainerFunctor; UnitCosmos)
open import SecondPass.Terminal using (_≈C_)
open import SecondPass.Lambek using (in-F; in∘out≈id)
open import SecondPass.CumulativeHierarchy
open import SecondPass.StrictLift
  using (StrictLayer; strictStep-suc; strictEmbed; StrictLambekConsistency
        ; EmbedFamily; outer-rule)

-- Shared uniform family builder
-- Abstract out the common logic of UnitHierarchy and StrictUnitHierarchy
-- Given a degenerate category (unique object, collapsible morphisms),
-- one obtains a UniformEmbeddingFamily
--
-- 公共一致族构造子
-- 抽象出 UnitHierarchy 与 StrictUnitHierarchy 的公共逻辑
-- 给定一个退化范畴（对象唯一、态射可坍缩），即可构造 UniformEmbeddingFamily
module BuildUniformFrom {o h e s p : Level}
  (C : Category o h e) (FC : Functor C (ContCat s p))
  (obj-unique : ∀ (X Y : Category.Obj C) → X ≡ Y)
  (collapse : Collapsible C) where
  private
    module CL = Category C

  retract : ∀ (x : Cosmos C FC) {A : CL.Obj} (s : ShapeOf FC A)
          → CL._⇒_ (Functor.₀ (Unfolding.unfoldFunctor (out x)) (A , s)) A
  retract x {A} s =
    let UX  = Unfolding.unfoldFunctor (out x)
        src = Functor.₀ UX (A , s)
        eq  = obj-unique A src
    in subst (λ X → CL._⇒_ X A) eq (CL.id {A = A})

  uniform : UniformEmbeddingFamily {C = C} {FC = FC}
  uniform = record
    { family = record { getData = mkEmbeddingData retract collapse }
    ; next-consistent = λ _ _ → refl
    }

-- Unit hierarchy (stagnating levels)
--
-- 单位层级（层级保持不变）
module UnitHierarchy {ℓ : Level} where
  private
    UCat = UnitCat {ℓ}
    UFC  = UnitContainerFunctor {ℓ}

  Layer₀ : Layer ℓ ℓ ℓ ℓ ℓ
  Layer₀ = record { C = UCat ; FC = UFC }

  Layer₁ : Layer ℓ ℓ ℓ ℓ ℓ
  Layer₁ = step Layer₀

  Layer₂ : Layer ℓ ℓ ℓ ℓ ℓ
  Layer₂ = step Layer₁

  U₀ = Cosmos (C Layer₀) (FC Layer₀)
  U₁ = Cosmos (C Layer₁) (FC Layer₁)
  U₂ = Cosmos (C Layer₂) (FC Layer₂)

  trivial₀ : Collapsible UCat
  trivial₀ _ _ = tt

  obj-unique₀ : ∀ (X Y : Category.Obj UCat) → X ≡ Y
  obj-unique₀ _ _ = refl

  -- Objects of Layer₁ are of the form (tt, tt), hence unique
  --
  -- Layer₁ 的对象形如 (tt, tt)，唯一
  obj-unique₁ : ∀ (X Y : Category.Obj (C Layer₁)) → X ≡ Y
  obj-unique₁ _ _ = refl

  obj-unique₂ : ∀ (X Y : Category.Obj (C Layer₂)) → X ≡ Y
  obj-unique₂ _ _ = refl

  uniform₀ = BuildUniformFrom.uniform UCat UFC obj-unique₀ trivial₀

  uniform₁ = BuildUniformFrom.uniform
    (C Layer₁) (FC Layer₁) obj-unique₁
    (collapsible→ShapeCat-collapsible {C = C Layer₀} {FC = FC Layer₀} trivial₀)

  uniform₂ = BuildUniformFrom.uniform
    (C Layer₂) (FC Layer₂) obj-unique₂
    (collapsible→ShapeCat-collapsible
     {C = C Layer₁} {FC = FC Layer₁}
     (collapsible→ShapeCat-collapsible {C = C Layer₀} {FC = FC Layer₀} trivial₀))

  embed₀₁ : U₀ → U₁
  embed₀₁ = EmbeddingFamily.embed′ (UniformEmbeddingFamily.family uniform₀)

  embed₁₂ : U₁ → U₂
  embed₁₂ = EmbeddingFamily.embed′ (UniformEmbeddingFamily.family uniform₁)

  embed₀₂ : U₀ → U₂
  embed₀₂ x = embed₁₂ (embed₀₁ x)

  unit₀ : U₀
  unit₀ = UnitCosmos {ℓ}

  unit₁ : U₁
  unit₁ = embed₀₁ unit₀

  unit₂ : U₂
  unit₂ = embed₁₂ unit₁

  -- refl holds: embed₀₂ = embed₁₂ ∘ embed₀₁, so embed₀₂ unit₀ is
  -- definitionally equal to unit₂
  --
  -- refl 成立：embed₀₂ = embed₁₂ ∘ embed₀₁，
  -- 故 embed₀₂ unit₀ 在定义上等于 unit₂
  embed₀₂-unit : embed₀₂ unit₀ ≡ unit₂
  embed₀₂-unit = refl

  private
    resp-≈C : ∀ {x y : U₀} → x ≈C y → embed₀₁ x ≈C embed₀₁ y
    resp-≈C x≈y ._≈C_.unfoldFunctor₀-eq _ = refl
    resp-≈C x≈y ._≈C_.pos-to-shape-eq _ _ = refl
    resp-≈C x≈y ._≈C_.unfold-next-eq s = resp-≈C (_≈C_.unfold-next-eq x≈y s)

    resp-≈C₁ : ∀ {x y : U₁} → x ≈C y → embed₁₂ x ≈C embed₁₂ y
    resp-≈C₁ x≈y ._≈C_.unfoldFunctor₀-eq _ = refl
    resp-≈C₁ x≈y ._≈C_.pos-to-shape-eq _ _ = refl
    resp-≈C₁ x≈y ._≈C_.unfold-next-eq s = resp-≈C₁ (_≈C_.unfold-next-eq x≈y s)

  functorial₀ : FunctorialEmbeddingFamily {C = C Layer₀} {FC = FC Layer₀}
  functorial₀ = record { uniform = uniform₀ ; embed′-resp-≈C = resp-≈C }

  functorial₁ : FunctorialEmbeddingFamily {C = C Layer₁} {FC = FC Layer₁}
  functorial₁ = record { uniform = uniform₁ ; embed′-resp-≈C = resp-≈C₁ }

  -- Lambek consistency: corresponds to StrictUnitHierarchy.lambek₀/₁/₂
  --
  -- Lambek 一致性：与 StrictUnitHierarchy.lambek₀/₁/₂ 相对应
  lambek₀ : LambekConsistency uniform₀
  lambek₀ = mkLambekConsistency uniform₀

  lambek₁ : LambekConsistency uniform₁
  lambek₁ = mkLambekConsistency uniform₁

  lambek₂ : LambekConsistency uniform₂
  lambek₂ = mkLambekConsistency uniform₂

-- FinCat hierarchy
--
-- FinCat 层级
module FinCatHierarchy where
  open import Data.Container.Core using (Container)

  -- FinCat n: the category with exactly n objects, and exactly one morphism
  -- between any two objects
  --
  -- FinCat n：恰有 n 个对象、任意两对象间恰有一个态射的范畴
  FinCat : (n : ℕ) → Category lzero lzero lzero
  FinCat n = Indiscrete (Fin n)

  -- Container whose shape and position are both Fin 2
  --
  -- 形状与位置均为 Fin 2 的容器
  FinContainer : Container lzero lzero
  FinContainer = record { Shape = Fin 2 ; Position = λ _ → Fin 2 }

  -- Constant functor from FinCat n to ContCat, taking the value FinContainer
  --
  -- 从 FinCat n 到 ContCat 的常值函子，取值恒为 FinContainer
  FinFC : (n : ℕ) → Functor (FinCat n) (ContCat lzero lzero)
  FinFC n = record
    { F₀ = λ _ → FinContainer
    ; F₁ = λ _ → Category.id (ContCat lzero lzero)
    ; identity = ≈sr-refl
    ; homomorphism = ≈sr-refl
    ; F-resp-≈ = λ _ → ≈sr-refl
    }

  Fin-EmbeddingData : (n : ℕ) (x : Cosmos (FinCat n) (FinFC n)) → EmbeddingData x
  Fin-EmbeddingData n = mkEmbeddingData (λ _ _ → tt) (λ _ _ → refl)

  Fin-EmbeddingFamily : (n : ℕ) → EmbeddingFamily {C = FinCat n} {FC = FinFC n}
  Fin-EmbeddingFamily n = record { getData = Fin-EmbeddingData n }

  Fin-UniformEmbeddingFamily : (n : ℕ) → UniformEmbeddingFamily {C = FinCat n} {FC = FinFC n}
  Fin-UniformEmbeddingFamily n = record
    { family = Fin-EmbeddingFamily n
    ; next-consistent = λ _ _ → refl
    }

  embedFin : (n : ℕ) → Cosmos (FinCat n) (FinFC n)
           → Cosmos (ShapeCat (FinCat n) (FinFC n)) (FC∘π (FinFC n))
  embedFin n x = embed x (Fin-EmbeddingData n x)

  private
    subst-FinFCπ : ∀ {n} {X Y : Category.Obj (ShapeCat (FinCat n) (FinFC n))}
                 → (eq : X ≡ Y) (z : Fin 2)
                 → subst (ShapeOf (FC∘π (FinFC n))) eq z ≡ z
    subst-FinFCπ refl z = refl

    subst-FinFC : ∀ {n} {X Y : Fin n} → (eq : X ≡ Y) (z : Fin 2)
               → subst (ShapeOf (FinFC n)) eq z ≡ z
    subst-FinFC refl z = refl

    embedFin-pos-to-shape
      : (n : ℕ) (y : Cosmos (FinCat n) (FinFC n))
      → (A : Category.Obj (ShapeCat (FinCat n) (FinFC n)))
      → (s : ShapeOf (FC∘π (FinFC n)) A)
      → (p : PosOf (FC∘π (FinFC n)) {A = A} s)
      → Unfolding.pos-to-shape (out (embedFin n y)) {A = A} s p
        ≡ Unfolding.pos-to-shape (out y) {A = proj₁ A} s p
    embedFin-pos-to-shape n y A s p = refl

    embedFin-uf₀-eq
        : ∀ n {x y : Cosmos (FinCat n) (FinFC n)}
            {A : Category.Obj (ShapeCat (FinCat n) (FinFC n))}
            (s : ShapeOf (FC∘π (FinFC n)) A)
        → Functor.₀ (Unfolding.unfoldFunctor (out (embedFin n x))) (A , s)
        ≡ Functor.₀ (Unfolding.unfoldFunctor (out (embedFin n y))) (A , s)
    embedFin-uf₀-eq n {x} {y} {A} s = refl

    Fin-resp-≈C : (n : ℕ) {x y : Cosmos (FinCat n) (FinFC n)}
      → x ≈C y
      → _≈C_ {C = ShapeCat (FinCat n) (FinFC n)} {FC = FC∘π (FinFC n)}
            (embedFin n x) (embedFin n y)
    Fin-resp-≈C n {x} {y} x≈y ._≈C_.unfoldFunctor₀-eq {A = A} s = refl
    Fin-resp-≈C n {x} {y} x≈y ._≈C_.pos-to-shape-eq {A = A} s p =
      let
        A₀     = proj₁ A
        uf-eq  = embedFin-uf₀-eq n {x} {y} {A} s
        eq₀    = _≈C_.unfoldFunctor₀-eq x≈y {A = A₀} s
        pts-eq = _≈C_.pos-to-shape-eq x≈y {A = A₀} s p
        x-pts  = Unfolding.pos-to-shape (out x) {A = A₀} s p
        y-pts  = Unfolding.pos-to-shape (out y) {A = A₀} s p
      in
      begin
        subst (ShapeOf (FC∘π (FinFC n))) uf-eq
          (Unfolding.pos-to-shape (out (embedFin n x)) {A = A} s p)
          ≡⟨ subst-FinFCπ uf-eq _ ⟩
        Unfolding.pos-to-shape (out (embedFin n x)) {A = A} s p
          ≡⟨ embedFin-pos-to-shape n x A s p ⟩
        x-pts
          ≡⟨ sym (subst-FinFC eq₀ x-pts) ⟩
        subst (ShapeOf (FinFC n)) eq₀ x-pts
          ≡⟨ pts-eq ⟩
        y-pts
          ≡⟨ sym (embedFin-pos-to-shape n y A s p) ⟩
        Unfolding.pos-to-shape (out (embedFin n y)) {A = A} s p
      ∎
    Fin-resp-≈C n {x} {y} x≈y ._≈C_.unfold-next-eq {A = A} s =
      Fin-resp-≈C n
        {x = Unfolding.unfold-next (out x) {A = proj₁ A} s}
        {y = Unfolding.unfold-next (out y) {A = proj₁ A} s}
        (_≈C_.unfold-next-eq x≈y {A = proj₁ A} s)

  Fin-FunctorialEmbeddingFamily : (n : ℕ) → FunctorialEmbeddingFamily {C = FinCat n} {FC = FinFC n}
  Fin-FunctorialEmbeddingFamily n = record
    { uniform = Fin-UniformEmbeddingFamily n
    ; embed′-resp-≈C = Fin-resp-≈C n
    }

  Fin-LambekConsistency : (n : ℕ) → LambekConsistency (Fin-UniformEmbeddingFamily n)
  Fin-LambekConsistency n = mkLambekConsistency (Fin-UniformEmbeddingFamily n)

-- Strict Unit Hierarchy: strictly-growing counterpart of UnitHierarchy
-- Contrast with UnitHierarchy:
--   UnitHierarchy uses `step`, which keeps container levels fixed:
--     Layer ℓ ℓ ℓ ℓ ℓ  →  Layer ℓ ℓ ℓ ℓ ℓ     (stagnation)
--   StrictUnitHierarchy uses `strictStep-suc`, which strictly raises them:
--     StrictLayer ℓ ℓ ℓ ℓ ℓ  →  StrictLayer ℓ ℓ ℓ (lsuc ℓ) (lsuc ℓ)  →  ...
--
-- 严格单位层级：UnitHierarchy 的严格增长对应物
-- 与 UnitHierarchy 的对比：
--   UnitHierarchy 使用 step，容器层级保持不变（停滞）；
--   StrictUnitHierarchy 使用 strictStep-suc，容器层级严格增长
module StrictUnitHierarchy {ℓ : Level} where
  private
    UCat = UnitCat {ℓ}
    UFC  = UnitContainerFunctor {ℓ}

  -- Three successive strict layers; container levels grow strictly at each step
  -- Type correctness relies on Agda's level normalisation:
  --   ℓ ⊔ lsuc ℓ = lsuc ℓ, and lsuc ℓ ⊔ lsuc ℓ = lsuc ℓ,
  -- i.e. in general s ⊔ lsuc (s ⊔ p) = lsuc (s ⊔ p) (since s ≤ s ⊔ p)
  --
  -- 三个连续严格层级，容器层级每步严格增长
  -- 类型正确性依赖 Agda 的层级归一化：
  --   ℓ ⊔ lsuc ℓ = lsuc ℓ，且 lsuc ℓ ⊔ lsuc ℓ = lsuc ℓ，
  -- 即一般地 s ⊔ lsuc (s ⊔ p) = lsuc (s ⊔ p)（因为 s ≤ s ⊔ p）
  SL₀ : StrictLayer ℓ ℓ ℓ ℓ ℓ
  SL₀ = record { C = UCat ; FC = UFC }

  SL₁ : StrictLayer ℓ ℓ ℓ (lsuc ℓ) (lsuc ℓ)
  SL₁ = strictStep-suc SL₀

  SL₂ : StrictLayer (lsuc ℓ) (lsuc ℓ) ℓ (lsuc (lsuc ℓ)) (lsuc (lsuc ℓ))
  SL₂ = strictStep-suc SL₁

  -- Cosmos types at each layer
  --
  -- 各层的宇宙类型
  SU₀ = Cosmos (StrictLayer.C SL₀) (StrictLayer.FC SL₀)
  SU₁ = Cosmos (StrictLayer.C SL₁) (StrictLayer.FC SL₁)
  SU₂ = Cosmos (StrictLayer.C SL₂) (StrictLayer.FC SL₂)

  -- Collapsibility: each layer has a single object, and morphism equivalence
  -- is trivial
  --
  -- 可坍缩性：三层都只有一个对象，态射等价平凡
  collapse₀ : Collapsible (StrictLayer.C SL₀)
  collapse₀ _ _ = tt

  collapse₁ : Collapsible (StrictLayer.C SL₁)
  collapse₁ _ _ = tt

  collapse₂ : Collapsible (StrictLayer.C SL₂)
  collapse₂ _ _ = tt

  -- Object uniqueness: C of SL₀ is UnitCat (single object)
  -- C of SL₁ is ShapeCat UnitCat UFC, whose objects have the form (tt, s)
  -- with s : ⊤, so there is again only one object (tt, tt); refl holds.
  -- SL₂ is analogous
  --
  -- 对象唯一性：SL₀ 的 C 是 UnitCat（单对象）
  -- SL₁ 的 C = ShapeCat UnitCat UFC，对象形如 (tt, s)，其中 s : ⊤，
  -- 因此也只有一个对象 (tt, tt)，refl 成立；SL₂ 同理
  obj-unique₀ : ∀ (X Y : Category.Obj (StrictLayer.C SL₀)) → X ≡ Y
  obj-unique₀ _ _ = refl

  obj-unique₁ : ∀ (X Y : Category.Obj (StrictLayer.C SL₁)) → X ≡ Y
  obj-unique₁ _ _ = refl

  obj-unique₂ : ∀ (X Y : Category.Obj (StrictLayer.C SL₂)) → X ≡ Y
  obj-unique₂ _ _ = refl

  uniform₀ = BuildUniformFrom.uniform (StrictLayer.C SL₀) (StrictLayer.FC SL₀)
                                      obj-unique₀ collapse₀
  uniform₁ = BuildUniformFrom.uniform (StrictLayer.C SL₁) (StrictLayer.FC SL₁)
                                      obj-unique₁ collapse₁
  uniform₂ = BuildUniformFrom.uniform (StrictLayer.C SL₂) (StrictLayer.FC SL₂)
                                      obj-unique₂ collapse₂

  -- Lambek consistency at each strict layer
  --
  -- 每个严格层级的 Lambek 一致性
  lambek₀ : LambekConsistency uniform₀
  lambek₀ = mkLambekConsistency uniform₀

  lambek₁ : LambekConsistency uniform₁
  lambek₁ = mkLambekConsistency uniform₁

  lambek₂ : LambekConsistency uniform₂
  lambek₂ = mkLambekConsistency uniform₂

  -- EmbeddingData at each strict layer
  --
  -- 各层的嵌入数据（退化情形：对象唯一、态射唯一）
  ed₀ : (x : SU₀) → EmbeddingData x
  ed₀ = UniformEmbeddingFamily.getData uniform₀

  ed₁ : (x : SU₁) → EmbeddingData x
  ed₁ = UniformEmbeddingFamily.getData uniform₁

  ed₂ : (x : SU₂) → EmbeddingData x
  ed₂ = UniformEmbeddingFamily.getData uniform₂

  -- Cross-layer embeddings via strictEmbed
  --
  -- 经 strictEmbed 的跨层嵌入
  se₀₁ : SU₀ → SU₁
  se₀₁ x = strictEmbed SL₀ x (ed₀ x)

  se₁₂ : SU₁ → SU₂
  se₁₂ x = strictEmbed SL₁ x (ed₁ x)

  se₀₂ : SU₀ → SU₂
  se₀₂ = se₁₂ ∘ se₀₁

  -- Unit elements at each layer
  --
  -- 每层的单位元
  su₀ : SU₀
  su₀ = UnitCosmos {ℓ}

  su₁ : SU₁
  su₁ = se₀₁ su₀

  su₂ : SU₂
  su₂ = se₁₂ su₁

  -- Composition law: definitionally refl
  --
  -- 复合律：由定义即可得（因为 se₀₂ = se₁₂ ∘ se₀₁）
  se₀₂-su : se₀₂ su₀ ≡ su₂
  se₀₂-su = refl

  -- se preserves _≈C_ (cross-layer embeddings are functors between Setoids)
  --
  -- se 保持 _≈C_（跨层嵌入是 Setoid 间的函子）
  private
    se₀₁-resp-≈C : ∀ {x y : SU₀} → x ≈C y → se₀₁ x ≈C se₀₁ y
    se₀₁-resp-≈C {x} {y} x≈y ._≈C_.unfoldFunctor₀-eq _ = refl
    se₀₁-resp-≈C {x} {y} x≈y ._≈C_.pos-to-shape-eq s p =
      cong lift (x≈y ._≈C_.pos-to-shape-eq (lower s) (lower p))
    se₀₁-resp-≈C {x} {y} x≈y ._≈C_.unfold-next-eq s =
      se₀₁-resp-≈C (x≈y ._≈C_.unfold-next-eq (lower s))

    se₁₂-resp-≈C : ∀ {x y : SU₁} → x ≈C y → se₁₂ x ≈C se₁₂ y
    se₁₂-resp-≈C {x} {y} x≈y ._≈C_.unfoldFunctor₀-eq _ = refl
    se₁₂-resp-≈C {x} {y} x≈y ._≈C_.pos-to-shape-eq s p =
      cong lift (x≈y ._≈C_.pos-to-shape-eq (lower s) (lower p))
    se₁₂-resp-≈C {x} {y} x≈y ._≈C_.unfold-next-eq s =
      se₁₂-resp-≈C (x≈y ._≈C_.unfold-next-eq (lower s))

  -- Embedding family SL₀ → SL₁: uniform₀ together with se₀₁'s preservation
  --
  -- SL₀ → SL₁ 的嵌入族：一致族 uniform₀ 加上 se₀₁ 的 _≈C_-保持性
  strictFunctorial₀ : EmbedFamily outer-rule SL₀
  strictFunctorial₀ = record { uniform = uniform₀ ; resp-≈C = se₀₁-resp-≈C }

  strictFunctorial₁ : EmbedFamily outer-rule SL₁
  strictFunctorial₁ = record { uniform = uniform₁ ; resp-≈C = se₁₂-resp-≈C }

  -- StrictLambekConsistency for SL₀, SL₁
  --
  -- SL₀、SL₁ 的 StrictLambekConsistency
  strictLambek₀ : StrictLambekConsistency SL₀ uniform₀
  strictLambek₀ = record
    { in-F-consistency = λ y → in∘out≈id′ (se₀₁ (in-F y))
    ; out-consistency  = λ x {A} s → refl
    }
    where
      C′  = StrictLayer.C SL₁
      FC′ = StrictLayer.FC SL₁
      in∘out≈id′ = in∘out≈id {C = C′} {FC = FC′}

  strictLambek₁ : StrictLambekConsistency SL₁ uniform₁
  strictLambek₁ = record
    { in-F-consistency = λ y → in∘out≈id′ (se₁₂ (in-F y))
    ; out-consistency  = λ x {A} s → refl
    }
    where
      C′  = StrictLayer.C SL₂
      FC′ = StrictLayer.FC SL₂
      in∘out≈id′ = in∘out≈id {C = C′} {FC = FC′}
