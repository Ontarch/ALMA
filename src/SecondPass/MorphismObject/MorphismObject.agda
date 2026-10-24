------------------------------------------------------------------------
-- Object-level homomorphisms between unfolding systems
--
--   Raw            : contravariant position map under an arbitrary shape
--                    functor S, no unfolding-preservation law
--   MorphismObject : Raw refined with S derived from a container natural
--                    transformation alpha, plus the pts-compat law
--   forget : MorphismObject -> Raw is a forgetful map, proven functorial
--   by forget-id and forget-comp
--
-- 展开系统之间的对象级同态
--
--   Raw            ：任意形状函子 S 下的反变位置映射，无展开保持定律
--   MorphismObject ：S 由 alpha 派生，并追加 pts-compat 定律
--   forget 为遗忘映射，由 forget-id 与 forget-comp 证明函子性
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module SecondPass.MorphismObject.MorphismObject where

open import Agda.Primitive using (Level; _⊔_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Sigma using (_,_)
open import Relation.Binary.PropositionalEquality.Core using (trans; cong)
open import Relation.Binary.PropositionalEquality.Properties using (module ≡-Reasoning)
open import Data.Container.Core using (shape; position)
open import Data.Product.Base using (proj₂)

open import Categories.Category.Core using (Category)
open import Categories.Functor.Core using (Functor)
open import Categories.Functor using (id; _∘F_)
open import Categories.NaturalTransformation.Core
  using (NaturalTransformation; _∘ᵥ_; _∘ʳ_)
open import Categories.NaturalTransformation.NaturalIsomorphism
  using (NaturalIsomorphism; unitorʳ; associator)

open import Cosmos.ContCategory using (ContCat)
open import Cosmos.ContCategoryLemmas
  using (ShapeOf; PosOf; transport; transport-trans; transport-cong)
open import Cosmos.ContCatEquiv using (ShapeCat)
open import SecondPass.ContCatEquivFunctor
  using (ContCatEquivFunctor; mkContCatEquivFunctor; module ShapeCatMorphism)
open import SecondPass.Unfolding using (Unfolding)

------------------------------------------------------------------------
-- Raw: contravariant position map under arbitrary shape functor S
-- No compatibility field; H, S, uc retained at module level so that
-- refining to MorphismObject requires only a parameter change + field.
--
-- Raw：任意形状函子 S 下的反变位置映射
-- 无相容性字段；H、S、uc 保留在模块层，使得精化为 MorphismObject 只需改参数并追加字段
module Raw {o h e o′ ℓ′ e′ s p u v : Level}
              {C : Category o h e} {D : Category o′ ℓ′ e′}
              {FC : Functor C (ContCat s p)} {FD : Functor D (ContCat s p)}
              {X : Set u} {Y : Set v}
              (UF : Unfolding FC X) (UG : Unfolding FD Y)
              (H : Functor C D)
              (S : Functor (ShapeCat C FC) (ShapeCat D FD))
              (uc : ∀ {A} (s : ShapeOf FC A)
                  → Functor.F₀ H (Functor.F₀ (Unfolding.unfoldFunctor UF) (A , s))
                  ≡ Functor.F₀ (Unfolding.unfoldFunctor UG) (Functor.F₀ S (A , s)))
  where
  record Contravariant : Set (o ⊔ o′ ⊔ s ⊔ p) where
    field
      -- Contravariant position map: target position pulled back to source
      --
      -- 反变位置映射：目标位置回拉到源位置
      onPos : ∀ {A} {s : ShapeOf FC A}
            → PosOf FD (proj₂ (Functor.F₀ S (A , s))) → PosOf FC s

  open Contravariant public

  record Covariant : Set (o ⊔ o′ ⊔ s ⊔ p) where
    field
      -- Covariant position map: source position pushed forward to target
      --
      -- 协变位置映射：源位置前推到目标位置
      onPos : ∀ {A} {s : ShapeOf FC A}
            → PosOf FC s → PosOf FD (proj₂ (Functor.₀ S (A , s)))

  open Covariant public


  -- Constructor
  --
  -- 构造子
  mkContravariant :
      (onPos : ∀ {A} {s : ShapeOf FC A}
             → PosOf FD (proj₂ (Functor.F₀ S (A , s))) → PosOf FC s)
    → Contravariant
  mkContravariant onPos = record { onPos = onPos }

  mkRawCovariant :
      (onPos : ∀ {A} {s : ShapeOf FC A}
            → PosOf FC s → PosOf FD (proj₂ (Functor.F₀ S (A , s))))
    → Covariant
  mkRawCovariant onPos = record { onPos = onPos }

open Raw public

-- Identity Contravariant
--
-- 恒等 Contravariant
module IdentityRaw {o h e s p u : Level} {C : Category o h e}
                   {FC : Functor C (ContCat s p)} {X : Set u}
                   (UF : Unfolding FC X) where
  idRaw : Contravariant UF UF id id (λ s → refl)
  idRaw = mkContravariant UF UF id id (λ s → refl) (λ q → q)

-- Composition of Contravariant
--
-- Contravariant 的复合
module CompRaw {o₁ h₁ e₁ o₂ h₂ e₂ o₃ h₃ e₃ s p u v w : Level}
               {C : Category o₁ h₁ e₁} {D : Category o₂ h₂ e₂} {E : Category o₃ h₃ e₃}
               {FC : Functor C (ContCat s p)} {FD : Functor D (ContCat s p)}
               {FE : Functor E (ContCat s p)}
               {X : Set u} {Y : Set v} {Z : Set w}
               (UF : Unfolding FC X) (UG : Unfolding FD Y) (UH : Unfolding FE Z)
               (H₁ : Functor C D) (H₂ : Functor D E)
               (S₁ : Functor (ShapeCat C FC) (ShapeCat D FD))
               (S₂ : Functor (ShapeCat D FD) (ShapeCat E FE))
               (uc₁ : ∀ {A} (s : ShapeOf FC A)
                    → Functor.F₀ H₁ (Functor.F₀ (Unfolding.unfoldFunctor UF) (A , s))
                    ≡ Functor.F₀ (Unfolding.unfoldFunctor UG) (Functor.F₀ S₁ (A , s)))
               (uc₂ : ∀ {A} (s : ShapeOf FD A)
                    → Functor.F₀ H₂ (Functor.F₀ (Unfolding.unfoldFunctor UG) (A , s))
                    ≡ Functor.F₀ (Unfolding.unfoldFunctor UH) (Functor.F₀ S₂ (A , s)))
  where
  private
    H-c : Functor C E
    H-c = H₂ ∘F H₁
    S-c : Functor (ShapeCat C FC) (ShapeCat E FE)
    S-c = S₂ ∘F S₁
    uc-c : ∀ {A} (s : ShapeOf FC A)
         → Functor.F₀ H-c (Functor.F₀ (Unfolding.unfoldFunctor UF) (A , s))
         ≡ Functor.F₀ (Unfolding.unfoldFunctor UH) (Functor.F₀ S-c (A , s))
    uc-c {A} s =
      trans (cong (Functor.F₀ H₂) (uc₁ s)) (uc₂ (proj₂ (Functor.F₀ S₁ (A , s))))

  compRaw : Contravariant UF UG H₁ S₁ uc₁
          → Contravariant UG UH H₂ S₂ uc₂
          → Contravariant UF UH H-c S-c uc-c
  compRaw mo₁ mo₂ = mkContravariant UF UH H-c S-c uc-c
    (λ q → Raw.onPos mo₁ (Raw.onPos mo₂ q))

------------------------------------------------------------------------
-- MorphismObject: S derived from alpha, with onPos + pts-compat
--
-- MorphismObject：S 由 alpha 派生，含 onPos 与 pts-compat
module MObjDef {o h e o′ ℓ′ e′ s p u v : Level}
               {C : Category o h e} {D : Category o′ ℓ′ e′}
               {FC : Functor C (ContCat s p)} {FD : Functor D (ContCat s p)}
               {X : Set u} {Y : Set v}
               (UF : Unfolding FC X) (UG : Unfolding FD Y)
               {H : Functor C D}
               (α : NaturalTransformation FC (FD ∘F H))
               (uc : ∀ {A} (s : ShapeOf FC A)
                   → Functor.F₀ H (Functor.F₀ (Unfolding.unfoldFunctor UF) (A , s))
                   ≡ Functor.F₀ (Unfolding.unfoldFunctor UG)
                       (Functor.F₀ H A , shape (NaturalTransformation.η α A) s))
  where
  private
    module UF = Unfolding UF
    module UG = Unfolding UG

  -- Shape component of alpha at object A
  --
  -- alpha 在对象 A 上的形状分量
  α-shape : ∀ {A} → ShapeOf FC A → ShapeOf FD (Functor.F₀ H A)
  α-shape {A} s = shape (NaturalTransformation.η α A) s

  -- Position component of alpha at object A (contravariant)
  --
  -- alpha 在对象 A 上的位置分量（反变）
  α-pos : ∀ {A} {s : ShapeOf FC A} → PosOf FD (α-shape s) → PosOf FC s
  α-pos {A} {s} = position (NaturalTransformation.η α A) {s = s}

  record MorphismObject : Set (o ⊔ o′ ⊔ s ⊔ p) where
    field
      -- Contravariant action on positions
      --
      -- 位置上的反变作用
      onPos : ∀ {A} {s : ShapeOf FC A}
            → PosOf FD (α-shape s) → PosOf FC s
      -- Two paths from a target position to a target shape coincide along uc
      --
      -- 从目标位置到目标形状的两条路径沿 uc 重合
      pts-compat : ∀ {A} {s : ShapeOf FC A} (q : PosOf FD (α-shape s))
                 → transport FD (uc s)
                       (α-shape (UF.pos-to-shape s (onPos q)))
                 ≡ UG.pos-to-shape (α-shape s) q

  open MorphismObject public

  -- Smart constructor
  --
  -- 智能构造子
  mkMorphismObject :
      (onPos : ∀ {A} {s : ShapeOf FC A}
             → PosOf FD (α-shape s) → PosOf FC s)
    → (pts : ∀ {A} {s : ShapeOf FC A} (q : PosOf FD (α-shape s))
           → transport FD (uc s)
                 (α-shape (UF.pos-to-shape s (onPos q)))
           ≡ UG.pos-to-shape (α-shape s) q)
    → MorphismObject
  mkMorphismObject onPos pts = record { onPos = onPos ; pts-compat = pts }

  -- Strict constructor: onPos forced to alpha's position component
  --
  -- 严格构造子：onPos 强制取 alpha 的位置分量
  strictMorphismObject :
      (pts : ∀ {A} {s : ShapeOf FC A} (q : PosOf FD (α-shape s))
           → transport FD (uc s)
                 (α-shape (UF.pos-to-shape s (α-pos q)))
           ≡ UG.pos-to-shape (α-shape s) q)
    → MorphismObject
  strictMorphismObject pts = record
    { onPos      = α-pos
    ; pts-compat = pts
    }

open MObjDef public

------------------------------------------------------------------------
-- Identity MorphismObject
--
-- 恒等 MorphismObject
module IdentityMorphismObject
  {o h e s p u : Level} {C : Category o h e}
  {FC : Functor C (ContCat s p)} {X : Set u}
  (UF : Unfolding FC X) where

  idα : NaturalTransformation FC (FC ∘F id)
  idα = NaturalIsomorphism.F⇐G (unitorʳ {F = FC})

  iduc : ∀ {A : Category.Obj C} (s : ShapeOf FC A)
       → Functor.F₀ {C = C} {D = C} id
           (Functor.F₀ {C = _} {D = C} (Unfolding.unfoldFunctor UF) (A , s))
       ≡ Functor.F₀ {C = _} {D = C} (Unfolding.unfoldFunctor UF)
           (Functor.F₀ {C = C} {D = C} id A ,
            shape (NaturalTransformation.η idα A) s)
  iduc {A = A} s = refl

  idMorphismObject : MorphismObject UF UF idα iduc
  idMorphismObject = mkMorphismObject UF UF idα iduc
    (λ q → q)
    (λ q → refl)

------------------------------------------------------------------------
-- Composition of MorphismObjects
-- H-c, alpha-c, uc-c are public: reused by ForgetComposition
--
-- MorphismObject 的复合
-- H-c、alpha-c、uc-c 声明为 public，供 ForgetComposition 复用
module CompMorphismObject
  {o₁ h₁ e₁ o₂ h₂ e₂ o₃ h₃ e₃ s p u v w : Level}
  {C : Category o₁ h₁ e₁} {D : Category o₂ h₂ e₂} {E : Category o₃ h₃ e₃}
  {FC : Functor C (ContCat s p)} {FD : Functor D (ContCat s p)}
  {FE : Functor E (ContCat s p)}
  {X : Set u} {Y : Set v} {Z : Set w}
  (UF : Unfolding FC X) (UG : Unfolding FD Y) (UH : Unfolding FE Z)
  {H₁ : Functor C D} {H₂ : Functor D E}
  {α₁ : NaturalTransformation FC (FD ∘F H₁)}
  {α₂ : NaturalTransformation FD (FE ∘F H₂)}
  {uc₁ : ∀ {A} (s : ShapeOf FC A)
       → Functor.F₀ H₁ (Functor.F₀ (Unfolding.unfoldFunctor UF) (A , s))
       ≡ Functor.F₀ (Unfolding.unfoldFunctor UG)
           (Functor.F₀ H₁ A , shape (NaturalTransformation.η α₁ A) s)}
  {uc₂ : ∀ {A} (s : ShapeOf FD A)
       → Functor.F₀ H₂ (Functor.F₀ (Unfolding.unfoldFunctor UG) (A , s))
       ≡ Functor.F₀ (Unfolding.unfoldFunctor UH)
           (Functor.F₀ H₂ A , shape (NaturalTransformation.η α₂ A) s)}
  where
  open ≡-Reasoning

  private
    H₂-obj : Category.Obj D → Category.Obj E
    H₂-obj = Functor.F₀ H₂

    α₁-shape : ∀ {A} → ShapeOf FC A → ShapeOf FD (Functor.F₀ H₁ A)
    α₁-shape {A} s = shape (NaturalTransformation.η α₁ A) s

    α₂-shape : ∀ {A} → ShapeOf FD A → ShapeOf FE (Functor.F₀ H₂ A)
    α₂-shape {A} s = shape (NaturalTransformation.η α₂ A) s

  H-c : Functor C E
  H-c = H₂ ∘F H₁

  α-c : NaturalTransformation FC (FE ∘F H-c)
  α-c = NaturalIsomorphism.F⇒G (associator H₁ H₂ FE)
        ∘ᵥ (α₂ ∘ʳ H₁) ∘ᵥ α₁

  uc-c : ∀ {A} (s : ShapeOf FC A)
       → Functor.F₀ H-c (Functor.F₀ (Unfolding.unfoldFunctor UF) (A , s))
       ≡ Functor.F₀ (Unfolding.unfoldFunctor UH)
           (Functor.F₀ H-c A , shape (NaturalTransformation.η α-c A) s)
  uc-c {A} s = trans (cong H₂-obj (uc₁ s)) (uc₂ (α₁-shape {A} s))

  module M₁  = MObjDef UF UG {H = H₁} α₁ uc₁
  module M₂  = MObjDef UG UH {H = H₂} α₂ uc₂
  module M-c = MObjDef UF UH {H = H-c} α-c uc-c

  compMorphismObject : M₁.MorphismObject → M₂.MorphismObject → M-c.MorphismObject
  compMorphismObject mo₁ mo₂ = M-c.mkMorphismObject
    (λ q → M₁.onPos mo₁ (M₂.onPos mo₂ q))
    (λ {A} {s} q →
      let p = M₁.onPos mo₁ (M₂.onPos mo₂ q)
      in begin
        transport FE (uc-c s)
          (shape (NaturalTransformation.η α-c
                  (Functor.F₀ (Unfolding.unfoldFunctor UF) (A , s)))
                (Unfolding.pos-to-shape UF s p))
        ≡⟨ refl ⟩
        transport FE
          (trans (cong H₂-obj (uc₁ s)) (uc₂ (α₁-shape {A} s)))
          (α₂-shape (α₁-shape (Unfolding.pos-to-shape UF s p)))
        ≡⟨ transport-trans FE
            (cong H₂-obj (uc₁ s)) (uc₂ (α₁-shape {A} s)) _ ⟩
        transport FE (uc₂ (α₁-shape {A} s))
          (transport FE (cong H₂-obj (uc₁ s))
            (α₂-shape (α₁-shape (Unfolding.pos-to-shape UF s p))))
        ≡⟨ cong (transport FE (uc₂ (α₁-shape {A} s)))
            (transport-cong FD FE {H = H₂} {f = α₂-shape} (uc₁ s)
                (α₁-shape (Unfolding.pos-to-shape UF s p))) ⟩
        transport FE (uc₂ (α₁-shape {A} s))
          (α₂-shape (transport FD (uc₁ s)
                    (α₁-shape (Unfolding.pos-to-shape UF s p))))
        ≡⟨ cong (transport FE (uc₂ (α₁-shape {A} s)))
            (cong α₂-shape (M₁.pts-compat mo₁ (M₂.onPos mo₂ q))) ⟩
        transport FE (uc₂ (α₁-shape {A} s))
          (α₂-shape (Unfolding.pos-to-shape UG (α₁-shape {A} s) (M₂.onPos mo₂ q)))
        ≡⟨ M₂.pts-compat mo₂ q ⟩
        Unfolding.pos-to-shape UH (α₂-shape (α₁-shape {A} s)) q
        ∎)

------------------------------------------------------------------------
-- MorphismObject -> Raw
-- S is the alpha-derived shape functor, exposed publicly so that
-- ForgetIdentity / ForgetComposition can reference it.
--
-- MorphismObject -> Raw
-- S 为由 alpha 派生的形状函子，公开暴露，
-- 供 ForgetIdentity / ForgetComposition 引用
module Forget {o h e o′ ℓ′ e′ s p u v : Level}
              {C : Category o h e} {D : Category o′ ℓ′ e′}
              {FC : Functor C (ContCat s p)} {FD : Functor D (ContCat s p)}
              {X : Set u} {Y : Set v}
              (UF : Unfolding FC X) (UG : Unfolding FD Y)
              {H : Functor C D}
              (α : NaturalTransformation FC (FD ∘F H))
              (uc : ∀ {A} (s : ShapeOf FC A)
                  → Functor.F₀ H (Functor.F₀ (Unfolding.unfoldFunctor UF) (A , s))
                  ≡ Functor.F₀ (Unfolding.unfoldFunctor UG)
                      (Functor.F₀ H A , shape (NaturalTransformation.η α A) s))
  where
  private
    cf : ContCatEquivFunctor FC FD H α
    cf = mkContCatEquivFunctor H FC FD α
    module SCM = ShapeCatMorphism cf

  S : Functor (ShapeCat C FC) (ShapeCat D FD)
  S = SCM.S

  forget : MorphismObject UF UG {H = H} α uc
         → Contravariant UF UG H S uc
  forget mo = mkContravariant UF UG H S uc (onPos mo)

-- forget idMorphismObject ≡ idRaw (with alpha-derived S)
--
-- forget idMorphismObject ≡ idRaw（S 由 alpha 派生）
module ForgetIdentity {o h e s p u : Level} {C : Category o h e}
                      {FC : Functor C (ContCat s p)} {X : Set u}
                      (UF : Unfolding FC X) where
  open IdentityMorphismObject UF
  open Forget UF UF {H = id} idα iduc

  idRaw-forget : Contravariant UF UF id S iduc
  idRaw-forget = mkContravariant UF UF id S iduc (λ q → q)

  forget-id : forget idMorphismObject ≡ idRaw-forget
  forget-id = refl

-- forgetting the composite MorphismObject
-- Given mo₁ : MorphismObject UF UG α₁ uc₁ and mo₂ : MorphismObject UG UH
-- α₂ uc₂, the composite C.compMorphismObject mo₁ mo₂ is a MorphismObject
-- UF UH C.α-c C.uc-c. Forgetting it along F yields a Raw over
-- (UF, UH, C.H-c, F.S, C.uc-c) whose onPos is the pointwise composite
-- M₁.onPos mo₁ ∘ M₂.onPos mo₂
--   F.forget (C.compMorphismObject mo₁ mo₂)
--     ≡ compRaw (F.forget mo₁) (F.forget mo₂) is not available
--
-- 遗忘复合 MorphismObject
-- 给定 mo₁ : MorphismObject UF UG α₁ uc₁ 与 mo₂ : MorphismObject UG UH
-- α₂ uc₂，复合 C.compMorphismObject mo₁ mo₂ 是 MorphismObject
-- UF UH C.α-c C.uc-c。沿 F 遗忘后得到 (UF, UH, C.H-c, F.S, C.uc-c)
-- 上的 Raw，其 onPos 为逐点复合 M₁.onPos mo₁ ∘ M₂.onPos mo₂
--   F.forget (C.compMorphismObject mo₁ mo₂)
--     ≡ compRaw (F.forget mo₁) (F.forget mo₂) 不可用
module ForgetComposition
  {o₁ h₁ e₁ o₂ h₂ e₂ o₃ h₃ e₃ s p u v w : Level}
  {C : Category o₁ h₁ e₁} {D : Category o₂ h₂ e₂} {E : Category o₃ h₃ e₃}
  {FC : Functor C (ContCat s p)} {FD : Functor D (ContCat s p)}
  {FE : Functor E (ContCat s p)}
  {X : Set u} {Y : Set v} {Z : Set w}
  (UF : Unfolding FC X) (UG : Unfolding FD Y) (UH : Unfolding FE Z)
  {H₁ : Functor C D} {H₂ : Functor D E}
  {α₁ : NaturalTransformation FC (FD ∘F H₁)}
  {α₂ : NaturalTransformation FD (FE ∘F H₂)}
  {uc₁ : ∀ {A} (s : ShapeOf FC A)
       → Functor.F₀ H₁ (Functor.F₀ (Unfolding.unfoldFunctor UF) (A , s))
       ≡ Functor.F₀ (Unfolding.unfoldFunctor UG)
           (Functor.F₀ H₁ A , shape (NaturalTransformation.η α₁ A) s)}
  {uc₂ : ∀ {A} (s : ShapeOf FD A)
       → Functor.F₀ H₂ (Functor.F₀ (Unfolding.unfoldFunctor UG) (A , s))
       ≡ Functor.F₀ (Unfolding.unfoldFunctor UH)
           (Functor.F₀ H₂ A , shape (NaturalTransformation.η α₂ A) s)}
  where
  private
    module C = CompMorphismObject UF UG UH
                 {H₁ = H₁} {H₂ = H₂} {α₁ = α₁} {α₂ = α₂}
                 {uc₁ = uc₁} {uc₂ = uc₂}
    module F = Forget UF UH {H = C.H-c} C.α-c C.uc-c
    module M₁ = MObjDef UF UG {H = H₁} α₁ uc₁
    module M₂ = MObjDef UG UH {H = H₂} α₂ uc₂

  forget-comp :
      (mo₁ : MorphismObject UF UG {H = H₁} α₁ uc₁)
      (mo₂ : MorphismObject UG UH {H = H₂} α₂ uc₂)
    → F.forget (C.compMorphismObject mo₁ mo₂)
    ≡ mkContravariant UF UH C.H-c F.S C.uc-c (λ q → M₁.onPos mo₁ (M₂.onPos mo₂ q))
  forget-comp _ _ = refl
