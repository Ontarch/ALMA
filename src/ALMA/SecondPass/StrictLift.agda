------------------------------------------------------------------------
-- StrictLift: level raising for the cumulative hierarchy
-- LiftContainerFunctor — Functor (ContCat s p) → Functor (ContCat (s ⊔ s′) (p ⊔ p′))
-- StrictLayer / strictStep / strictStep-suc — layer stepping
-- strictEmbed — embedding a cosmos into the strictly-raised next layer
--
-- 严格层级提升：累积层级的层级递增迭代
-- LiftContainerFunctor —— 函子 ContCat s p → ContCat (s ⊔ s′) (p ⊔ p′)
-- StrictLayer / strictStep / strictStep-suc —— 层级步进
-- strictEmbed —— 将宇宙嵌入严格提升后的下一层
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module ALMA.SecondPass.StrictLift where

open import Agda.Primitive using (Level; _⊔_; lsuc; Setω)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Level using (Lift; lift; lower)
open import Relation.Binary.PropositionalEquality.Core using (cong; sym; trans; subst)
open import Relation.Binary.PropositionalEquality.Properties using (module ≡-Reasoning)
open import Data.Product.Base using (_,_; proj₁; proj₂)
open import Data.Container.Core using (Container; Shape; Position; _⇒_)
open import Data.Container.Morphism using (id; _∘_)

open import Categories.Category.Core using (Category)
open import Categories.Functor.Core using (Functor)
open import Categories.Functor using (_∘F_)

open import ALMA.Cosmos.ContCategory using (ContCat; _≈sr_)
open import ALMA.Cosmos.ContCategoryLemmas using (ShapeOf; PosOf; actSOf; actPOf)
open import ALMA.Cosmos.ContCatEquiv using (ShapeCat)
open import ALMA.SecondPass.Unfolding using (Unfolding)
open import ALMA.SecondPass.Cosmos using (Cosmos; out; UnitCat; UnitContainerFunctor)
open import ALMA.SecondPass.Terminal using (_≈C_)
open import ALMA.SecondPass.Lambek using (in-F)
open import ALMA.SecondPass.CumulativeHierarchy
  using (FC∘π; EmbeddingData; UniformEmbeddingFamily)

-- Level-raising preliminaries
-- Eta rule for Lift: lift ∘ lower is the identity
--
-- 层级提升的预备构造
-- Lift 的 eta 规则：lift ∘ lower 是恒等
lift-lower : ∀ {a b : Level} {A : Set a} (x : Lift b A) → lift (lower x) ≡ x
lift-lower (lift _) = refl

-- subst along a lift-equality commutes with lift, for the specific shape
-- of P used by position types: the input is an arbitrary lifted element,
-- and the family is applied after lowering
--
-- 沿 lift 等式的 subst 与 lift 交换，针对位置类型所用的 P 的形状：
-- 输入为任意提升元素，族在降层后应用
subst-lift-pos : ∀ {a b c d : Level} {A : Set a} {P : A → Set b} {x y : A}
                   (q : x ≡ y) (p : Lift {b} d (P x))
                 → subst (λ z → Lift {b} d (P (lower {a} {c} z)))
                         (cong (lift {a} {c}) q)
                         p
                   ≡ lift (subst P q (lower p))
subst-lift-pos refl p = sym (lift-lower p)

-- lower of subst-lift-pos: the result is the unlifted substitution on
-- the lowered input
--
-- subst-lift-pos 的降层形式：结果为对降层输入的未提升替换
lower-subst-lift : ∀ {a b c d : Level} {A : Set a} {P : A → Set b} {x y : A}
                     (q : x ≡ y) (p : Lift {b} d (P x))
                   → lower (subst (λ z → Lift {b} d (P (lower {a} {c} z)))
                                  (cong (lift {a} {c}) q) p)
                     ≡ subst P q (lower p)
lower-subst-lift q p = cong lower (subst-lift-pos q p)

-- Lift shape and position types by levels s′ and p′
-- Position is defined via lower so that its interaction with subst stays definitional
--
-- 将形状与位置类型的层级分别提升 s′、p′
-- Position 用 lower 定义，使与 subst 的交互保持定义性
LiftContainer : ∀ {s p : Level} (s′ p′ : Level) → Container s p
              → Container (s ⊔ s′) (p ⊔ p′)
LiftContainer {s} {p} s′ p′ C = record
  { Shape    = Lift {s} s′ (Shape C)
  ; Position = λ z → Lift {p} p′ (Position C (lower z))
  }

-- General form: subst along a lift-equality commutes with lift for an
-- arbitrary family P, with input given as lift u
--
-- 一般形式：沿 lift 等式的 subst 对任意族 P 与 lift 交换，
-- 输入以 lift u 的形式给出
subst-lift : ∀ {a b c d : Level} {A : Set a} (P : A → Set b)
               {x y : A} (e : x ≡ y) (u : P x)
             → subst (λ (z : Lift {a} c A) → Lift {b} d (P (lower z)))
                     (cong (lift {a} {c}) e)
                     (lift {b} {d} u)
               ≡ lift {b} {d} (subst P e u)
subst-lift P refl u = refl

-- lower of subst-lift applied to lift u: simplifies to the unlifted
-- substitution on u
--
-- subst-lift 作用于 lift u 后的降层形式：化简为对 u 的未提升替换
subst-lift-lower : ∀ {a b c d : Level} {A : Set a} (P : A → Set b)
                     {x y : A} (e : x ≡ y) (u : P x)
                   → lower (subst (λ (z : Lift {a} c A) → Lift {b} d (P (lower z)))
                                  (cong (lift {a} {c}) e)
                                  (lift {b} {d} u))
                     ≡ subst P e u
subst-lift-lower P e u = cong lower (subst-lift P e u)

-- Lift a ContCat-valued functor one level up
--
-- 将 ContCat 值函子提升一层
LiftContainerFunctor : ∀ {s p : Level} (s′ p′ : Level)
                     → Functor (ContCat s p) (ContCat (s ⊔ s′) (p ⊔ p′))
LiftContainerFunctor {s} {p} s′ p′ = record
  { F₀           = LiftContainer s′ p′
  ; F₁           = liftF₁
  ; identity     = lift-id
  ; homomorphism = λ {X} {Y} {Z} {f} {g} →
                    lift-hom {X = X} {Y = Y} {Z = Z} {f = f} {g = g}
  ; F-resp-≈     = lift-resp
  }
  where
    liftF₁ : ∀ {X Y : Container s p} → X ⇒ Y
           → LiftContainer s′ p′ X ⇒ LiftContainer s′ p′ Y
    liftF₁ f = record
      { shape    = λ { (lift sh) → lift (_⇒_.shape f sh) }
      ; position = λ { {sh} q → lift (_⇒_.position f {lower sh} (lower q)) }
      }

    lift-id : ∀ {X} → liftF₁ {X = X} {Y = X} (id X)
                      ≈sr id (LiftContainer s′ p′ X)
    lift-id = record
      { shape-eq = λ { (lift sh) → refl }
      ; position-eq   = λ { (lift sh) (lift q) → refl }
      }

    lift-hom : ∀ {X Y Z : Container s p} {f : X ⇒ Y} {g : Y ⇒ Z}
             → liftF₁ (g ∘ f) ≈sr (liftF₁ g ∘ liftF₁ f)
    lift-hom {X = X} {Y = Y} {Z = Z} {f = f} {g = g} = record
      { shape-eq = λ { (lift sh) → refl }
      ; position-eq   = λ { (lift sh) (lift q) → refl }
      }

    lift-resp : ∀ {X Y} {f g : X ⇒ Y} → f ≈sr g → liftF₁ f ≈sr liftF₁ g
    lift-resp {X} {Y} {f} {g} f≈g = record
      { shape-eq = λ { (lift sh) → cong lift (Fe.shape-eq sh) }
      ; position-eq   = λ { (lift sh) (lift q) →
          trans (cong lift (Fe.position-eq sh q))
                (cong (λ u → lift (_⇒_.position g {sh} u))
                      (sym (subst-lift-lower (Position Y) (Fe.shape-eq sh) q))) }
      }
      where
        module Fe = _≈sr_ f≈g

-- Strict layers and strictly-growing step
-- Universally quantifies over the source category's levels, hence resides in Setω
--
-- 严格层级与严格增长的步进
-- 对源范畴的层级做全称量化，故位于 Setω
LiftFC-Strategy : ∀ {s p s′ p′ : Level} → Setω
LiftFC-Strategy {s} {p} {s′} {p′} =
  ∀ {o h e} {C : Category o h e}
  → Functor C (ContCat s p)
  → Functor C (ContCat (s ⊔ s′) (p ⊔ p′))

concreteLiftFC : ∀ {s p s′ p′} {o h e} {C : Category o h e}
  → Functor C (ContCat s p)
  → Functor C (ContCat (s ⊔ s′) (p ⊔ p′))
concreteLiftFC {s} {p} {s′} {p′} FC =
  LiftContainerFunctor {s} {p} s′ p′ ∘F FC

-- Layer record and the strictly-growing step operation
--
-- 层级记录与严格增长的步进操作
record StrictLayer (o h e s p : Level) : Set (lsuc (o ⊔ h ⊔ e ⊔ s ⊔ p)) where
  field
    C  : Category o h e
    FC : Functor C (ContCat s p)

open StrictLayer public

strictStep : ∀ {o h e s p s′ p′ : Level}
           → LiftFC-Strategy {s} {p} {s′} {p′}
           → StrictLayer o h e s p
           → StrictLayer (o ⊔ s) (h ⊔ s) e (s ⊔ s′) (p ⊔ p′)
strictStep liftFC L = record
  { C  = ShapeCat (StrictLayer.C L) (StrictLayer.FC L)
  ; FC = liftFC (FC∘π (StrictLayer.FC L))
  }

concreteStrictStep : ∀ {o h e s p s′ p′}
  → StrictLayer o h e s p
  → StrictLayer (o ⊔ s) (h ⊔ s) e (s ⊔ s′) (p ⊔ p′)
concreteStrictStep {s = s} {p = p} {s′ = s′} {p′ = p′} L =
  strictStep {s = s} {p = p} {s′ = s′} {p′ = p′}
    (concreteLiftFC {s = s} {p = p} {s′ = s′} {p′ = p′})
    L

-- Type depends on Agda's level normalization:
-- s ⊔ lsuc (s ⊔ p) = lsuc (s ⊔ p) since s ≤ s ⊔ p
--
-- 类型依赖 Agda 的层级归一化：
-- 因 s ≤ s ⊔ p，故 s ⊔ lsuc (s ⊔ p) = lsuc (s ⊔ p)
strictStep-suc : ∀ {o h e s p}
  → StrictLayer o h e s p
  → StrictLayer (o ⊔ s) (h ⊔ s) e (lsuc (s ⊔ p)) (lsuc (s ⊔ p))
strictStep-suc {s = s} {p = p} =
  concreteStrictStep {s = s} {p = p}
                     {s′ = lsuc (s ⊔ p)} {p′ = lsuc (s ⊔ p)}

-- strictEmbed — embedding into the strictly-raised next layer
-- lift ∘ lower is the identity on equality proofs
--
-- strictEmbed —— 嵌入到严格提升后的下一层
-- 在等式证明上，lift ∘ lower 是恒等
lift-lower-cong : ∀ {a b : Level} {A : Set a} {x y : Lift b A}
                  (q : x ≡ y) → cong lift (cong lower q) ≡ q
lift-lower-cong refl = refl

-- The unfold functor of the strict embedding:
-- forgets the outer shape and keeps the inner one
--
-- 严格嵌入的展开函子：遗忘外层形状，保留内层形状
strictEmbed-unfoldFunctor
  : ∀ {o h e s p}
  → (L : StrictLayer o h e s p)
  → Functor (ShapeCat (StrictLayer.C (strictStep-suc L))
                      (StrictLayer.FC (strictStep-suc L)))
            (ShapeCat (StrictLayer.C L) (StrictLayer.FC L))
strictEmbed-unfoldFunctor L = record
  { F₀           = λ z → proj₁ (proj₁ z) , lower (proj₂ z)
  ; F₁           = λ f → proj₁ (proj₁ f) , cong lower (proj₂ f)
  ; identity     = λ {z} →
                     Category.Equiv.refl (StrictLayer.C L)
                       {x = Category.id (StrictLayer.C L)}
  ; homomorphism = λ {X} {Y} {Z} {f} {g} →
                     Category.Equiv.refl (StrictLayer.C L)
                       {x = Category._∘_ (StrictLayer.C L)
                                         (proj₁ (proj₁ g))
                                         (proj₁ (proj₁ f))}
  ; F-resp-≈     = λ ff≈gg → ff≈gg
  }

-- Subst along a lift-equality commutes with lower, specialised to the
-- container functor of a strict layer
--
-- 沿 lift 等式的 subst 与 lower 交换，特化到严格层的容器函子
module _ {o h e s p : Level} (L : StrictLayer o h e s p)
         (x : Cosmos (StrictLayer.C L) (StrictLayer.FC L))
         (ed : EmbeddingData x) where
  private
    C_L  = StrictLayer.C L
    FC_L = StrictLayer.FC L
    C′   = StrictLayer.C (strictStep-suc L)
    FC′  = StrictLayer.FC (strictStep-suc L)
    module FCat  = Category C_L
    module C′Cat = Category C′
    open ≡-Reasoning
    UX = out x
    module UX = Unfolding UX

  strictEmbed-bridge
    : ∀ {A B : Category.Obj C′}
        {s : ShapeOf FC′ A} {t : ShapeOf FC′ B}
        (g : A C′Cat.⇒ B) (p : actSOf FC′ g s ≡ t)
        (p₁ : PosOf FC′ {A = B} (actSOf FC′ g s))
      → lower (subst (PosOf FC′ {A = B}) p p₁)
        ≡ subst (PosOf FC_L {A = proj₁ B}) (cong lower p) (lower p₁)
  strictEmbed-bridge {A} {B} {s} {t} g p p₁ =
    begin
      lower (subst (PosOf FC′ {A = B}) p p₁)
        ≡⟨ cong lower (cong (λ e → subst (PosOf FC′ {A = B}) e p₁)
                            (sym (lift-lower-cong p))) ⟩
      lower (subst (PosOf FC′ {A = B}) (cong lift (cong lower p)) p₁)
        ≡⟨ lower-subst-lift {P = PosOf FC_L {A = proj₁ B}}
                            (cong lower p) p₁ ⟩
      subst (PosOf FC_L {A = proj₁ B}) (cong lower p) (lower p₁)
    ∎

  strictEmbed-compat
    : ∀ {A B : Category.Obj C_L}
        {s : ShapeOf FC_L A} {t : ShapeOf FC_L B}
      → (f : A FCat.⇒ B)
      → (q : actSOf FC_L f s ≡ t)
      → (p : PosOf FC_L (actSOf FC_L f s))
      → actSOf FC_L (EmbeddingData.retract ed t)
          (UX.pos-to-shape t (subst (PosOf FC_L) q p))
        ≡ actSOf FC_L f
            (actSOf FC_L (EmbeddingData.retract ed s)
               (UX.pos-to-shape s (actPOf FC_L f s p)))
  strictEmbed-compat {A} {B} {s} {t} f q p =
    begin
      actSOf FC_L (EmbeddingData.retract ed t)
        (UX.pos-to-shape t (subst (PosOf FC_L) q p))
        ≡⟨ cong (actSOf FC_L (EmbeddingData.retract ed t))
                (UX.pos-actS-compat f q p) ⟩
      actSOf FC_L (EmbeddingData.retract ed t) (actSOf FC_L g₁ x₀)
        ≡⟨ sym (_≈sr_.shape-eq
                (Functor.homomorphism FC_L {f = g₁}
                 {g = EmbeddingData.retract ed t}) x₀) ⟩
      actSOf FC_L (EmbeddingData.retract ed t FCat.∘ g₁) x₀
        ≡⟨ sym (_≈sr_.shape-eq
                (Functor.F-resp-≈ FC_L
                 {f = f FCat.∘ EmbeddingData.retract ed s}
                 {g = EmbeddingData.retract ed t FCat.∘ g₁}
                 (EmbeddingData.retract-natural ed f q)) x₀) ⟩
      actSOf FC_L (f FCat.∘ EmbeddingData.retract ed s) x₀
        ≡⟨ _≈sr_.shape-eq
             (Functor.homomorphism FC_L {f = EmbeddingData.retract ed s}
                {g = f}) x₀ ⟩
      actSOf FC_L f (actSOf FC_L (EmbeddingData.retract ed s) x₀)
    ∎
    where
      x₀ = UX.pos-to-shape s (actPOf FC_L f s p)
      g₁ = Functor.₁ UX.unfoldFunctor (f , q)

strictEmbed
  : ∀ {o h e s p}
  → (L : StrictLayer o h e s p)
  → (x : Cosmos (StrictLayer.C L) (StrictLayer.FC L))
  → EmbeddingData x
  → Cosmos (StrictLayer.C (strictStep-suc L))
           (StrictLayer.FC (strictStep-suc L))
strictEmbed L x ed .out = record
  { unfoldFunctor   = strictEmbed-unfoldFunctor L
  ; unfold-next     = λ { {A} u →
      strictEmbed L
        (UX.unfold-next {A = proj₁ A} (lower u))
        (EmbeddingData.next ed {A = proj₁ A} (lower u)) }
  ; pos-to-shape    = λ {A} s p →
      lift (actSOf FC_L (EmbeddingData.retract ed (lower s))
                       (UX.pos-to-shape (lower s) (lower p)))
  ; pos-actS-compat = λ {A} {B} {s} {t} g p p₁ →
      cong lift (begin
        actSOf FC_L (EmbeddingData.retract ed {A = proj₁ B} (lower t))
          (UX.pos-to-shape {A = proj₁ B} (lower t)
             (lower (subst (PosOf FC′ {A = B}) p p₁)))
          ≡⟨ cong (actSOf FC_L (EmbeddingData.retract ed {A = proj₁ B} (lower t)))
                  (cong (UX.pos-to-shape {A = proj₁ B} (lower t))
                        (strictEmbed-bridge L x ed {A = A} {B = B}
                           {s = s} {t = t} g p p₁)) ⟩
        actSOf FC_L (EmbeddingData.retract ed {A = proj₁ B} (lower t))
          (UX.pos-to-shape {A = proj₁ B} (lower t)
             (subst (PosOf FC_L {A = proj₁ B}) (cong lower p) (lower p₁)))
          ≡⟨ strictEmbed-compat L x ed {A = proj₁ A} {B = proj₁ B}
                  {s = lower s} {t = lower t}
                  (proj₁ g) (cong lower p) (lower p₁) ⟩
        actSOf FC_L (proj₁ g)
          (actSOf FC_L (EmbeddingData.retract ed {A = proj₁ A} (lower s))
             (UX.pos-to-shape {A = proj₁ A} (lower s)
                (actPOf FC_L (proj₁ g) (lower s) (lower p₁))))
          ≡⟨ refl ⟩
        actSOf FC_L (proj₁ g)
          (actSOf FC_L (EmbeddingData.retract ed {A = proj₁ A} (lower s))
             (UX.pos-to-shape {A = proj₁ A} (lower s)
                (lower (actPOf FC′ g s p₁))))
      ∎)
  }
  where
    FC_L = StrictLayer.FC L
    FC′  = StrictLayer.FC (strictStep-suc L)
    open ≡-Reasoning
    UX = out x
    module UX = Unfolding UX

-- Example: strictly-growing Unit hierarchy
--
-- 示例：严格增长的单位层级
module StrictUnitHierarchyExample {ℓ : Level} where

  L₀ : StrictLayer ℓ ℓ ℓ ℓ ℓ
  L₀ = record { C = UnitCat {ℓ} ; FC = UnitContainerFunctor {ℓ} }

  L₁ : StrictLayer ℓ ℓ ℓ (lsuc ℓ) (lsuc ℓ)
  L₁ = strictStep-suc L₀

  L₂ : StrictLayer (lsuc ℓ) (lsuc ℓ) ℓ (lsuc (lsuc ℓ)) (lsuc (lsuc ℓ))
  L₂ = strictStep-suc L₁

-- An embedding rule: a first-class notion of how to embed a cosmos into
-- the next strict layer. This captures the "direction" of the unfold
-- functor as data, so that the framework in CumulativeHierarchyLimit
-- becomes direction-agnostic
--
-- 嵌入规则：把"如何把宇宙嵌入下一严格层"提升为一等公民
-- 这把展开函子的"方向"捕获为数据，使 CumulativeHierarchyLimit
-- 中的框架成为方向无关的
record EmbeddingRule : Setω where
  field
    Embed : ∀ {o h e s p} (L : StrictLayer o h e s p)
          → (x : Cosmos (StrictLayer.C L) (StrictLayer.FC L))
          → EmbeddingData x
          → Cosmos (StrictLayer.C (strictStep-suc L))
                   (StrictLayer.FC (strictStep-suc L))

-- A family of embedding data along a given rule R. When R = outer-rule,
-- this specialises to the outer-preserving family used by
-- CumulativeHierarchy; when R = inner-rule (defined in FinCatInnerSewing),
-- it gives the inner-preserving family
--
-- 给定规则 R 下的嵌入数据族。当 R = outer-rule 时，它特化为
-- CumulativeHierarchy 所用的保外层族；当 R = inner-rule
-- （定义于 FinCatInnerSewing）时，它给出保内层族
record EmbedFamily (R : EmbeddingRule) {o h e s p}
                   (L : StrictLayer o h e s p)
  : Set (lsuc (o ⊔ h ⊔ e ⊔ s ⊔ p)) where
  field
    uniform : UniformEmbeddingFamily
                {C  = StrictLayer.C L}
                {FC = StrictLayer.FC L}
  open UniformEmbeddingFamily uniform public
  field
    resp-≈C : ∀ {x y}
            → _≈C_ {C  = StrictLayer.C L} {FC = StrictLayer.FC L} x y
            → _≈C_ {C  = StrictLayer.C (strictStep-suc L)}
                   {FC = StrictLayer.FC (strictStep-suc L)}
                   (EmbeddingRule.Embed R L x (getData x))
                   (EmbeddingRule.Embed R L y (getData y))

-- The outer-preserving rule (the default direction of CumulativeHierarchy)
--
-- 保外层规则（CumulativeHierarchy 的默认方向）
outer-rule : EmbeddingRule
outer-rule .EmbeddingRule.Embed = strictEmbed

-- StrictLambekConsistency: Lambek-consistency for the strict embedding
--
-- StrictLambekConsistency：严格嵌入的 Lambek 一致性
record StrictLambekConsistency {o h e s p}
  (L : StrictLayer o h e s p)
  (uniform : UniformEmbeddingFamily {C = StrictLayer.C L} {FC = StrictLayer.FC L})
  : Set (lsuc (o ⊔ h ⊔ e ⊔ s ⊔ p)) where
  private
    C_L  = StrictLayer.C L
    FC_L = StrictLayer.FC L
    C_L'  = StrictLayer.C (strictStep-suc L)
    FC_L' = StrictLayer.FC (strictStep-suc L)
    getData = UniformEmbeddingFamily.getData uniform
    se : Cosmos C_L FC_L → Cosmos C_L' FC_L'
    se x = strictEmbed L x (getData x)
    in-F' : Unfolding FC_L' (Cosmos C_L' FC_L') → Cosmos C_L' FC_L'
    in-F' = in-F {C = C_L'} {FC = FC_L'}
  field

    -- in-F′ ∘ out is bisimilar to the identity on strict embeddings
    --
    -- in-F′ ∘ out 与严格嵌入上的恒等互模拟
    in-F-consistency : ∀ y
                     → in-F' (out (se (in-F {C = C_L} {FC = FC_L} y)))
                       ≈C se (in-F {C = C_L} {FC = FC_L} y)

    -- unfold-next commutes with strictEmbed on the lifted shape
    --
    -- unfold-next 与 strictEmbed 在提升形状上交换
    out-consistency  : ∀ (x : Cosmos C_L FC_L) {A : Category.Obj C_L'}
                         (s : ShapeOf FC_L' A)
                     → Unfolding.unfold-next (out (se x)) {A = A} s
                       ≡ se (Unfolding.unfold-next (out x) {A = proj₁ A}
                                                    (lower s))
