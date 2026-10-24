------------------------------------------------------------------------
-- MorphismMorphism: compatibility of position maps with hom-actions
--
-- actP-from-S is the canonical position map derived from S.
-- The composition of MorphismMorphisms is direct via functoriality of S.
-- An equivalence _≈MM_ (pointwise propositional equality) is provided.
--
-- 态射间态射：位置映射与态射作用的相容性
--
-- actP-from-S 是由 S 典范导出的位置映射。
-- 借助 S 的函子性，MorphismMorphism 的复合直接成立。
-- 提供逐点命题相等的等价关系 _≈MM_。
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module SecondPass.MorphismMorphism where

open import Agda.Primitive using (Level; _⊔_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Sigma using (_,_)
open import Relation.Binary.PropositionalEquality.Core using (sym; subst; trans; cong)
open import Relation.Binary.PropositionalEquality.Properties using (module ≡-Reasoning)
open ≡-Reasoning
open import Relation.Binary.Structures using (IsEquivalence)
open import Data.Product.Base using (proj₁; proj₂)

open import Categories.Category.Core using (Category)
open import Categories.Functor.Core using (Functor)
open import Categories.Functor using (id; _∘F_)

open import Cosmos.ContCategory using (ContCat)
open import Cosmos.ContCategoryLemmas using (ShapeOf; PosOf; actSOf; actPOf)
open import Cosmos.ContCatEquiv using (ShapeCat)
open import SecondPass.Unfolding using (Unfolding)
open import SecondPass.MorphismObject
  using (MorphismObject; idMorphismObject; compMorphismObject)

-- Canonical actP derived from the functor S itself.
-- 由函子 S 本身导出的典范 actP。
module _ {o h e o′ ℓ′ e′ s p : Level}
         {C : Category o h e} {D : Category o′ ℓ′ e′}
         (FC : Functor C (ContCat s p)) (FD : Functor D (ContCat s p))
         (S  : Functor (ShapeCat C FC) (ShapeCat D FD)) where
  private
    module C  = Category C
    module Sf = Functor S

  actP-from-S : ∀ {A B} (f : C._⇒_ A B) {s : ShapeOf FC A} {t : ShapeOf FC B}
                → (p : actSOf FC f s ≡ t)
                → PosOf FD (proj₂ (Sf.₀ (B , t)))
                → PosOf FD (proj₂ (Sf.₀ (A , s)))
  actP-from-S {A} {B} f {s} {t} p q =
    actPOf FD (proj₁ (Sf.₁ (f , p))) (proj₂ (Sf.₀ (A , s)))
      (subst (PosOf FD) (sym (proj₂ (Sf.₁ (f , p)))) q)

-- Given a MorphismObject, a MorphismMorphism witnesses that onPos commutes
-- with the container position maps actPOf, where the position transport
-- is canonically given by actP-from-S.
-- 给定一个 MorphismObject，MorphismMorphism 见证 onPos 与容器位置映射 actPOf
-- 的交换性，其中位置运输由 actP-from-S 典范给出。
module _ {o h e o′ ℓ′ e′ s p u v : Level}
         {C : Category o h e} {D : Category o′ ℓ′ e′}
         {FC : Functor C (ContCat s p)} {FD : Functor D (ContCat s p)}
         {X : Set u} {Y : Set v}
         (UF : Unfolding FC X) (UG : Unfolding FD Y)
         (S  : Functor (ShapeCat C FC) (ShapeCat D FD))
         (shapeTrans : ∀ {A} {s : ShapeOf FC A}
                     → PosOf FC s
                     → ShapeOf FD (Functor.₀ (Unfolding.unfoldFunctor UG)
                                             (Functor.₀ S (A , s))))
         (MO : MorphismObject UF UG S shapeTrans) where
  private
    module C  = Category C
    module MO = MorphismObject MO

  record MorphismMorphism : Set (o ⊔ h ⊔ s ⊔ p) where
    field
      onActP : ∀ {A B} (f : C._⇒_ A B) {s : ShapeOf FC A} {t : ShapeOf FC B}
             → (p : actSOf FC f s ≡ t)
             → (q : PosOf FC t)
             → MO.onPos (actPOf FC f s (subst (PosOf FC) (sym p) q))
               ≡ actP-from-S FC FD S f p (MO.onPos q)

  -- Equivalence relation on MorphismMorphism: pointwise equality of onActP
  -- MorphismMorphism 上的等价关系：onActP 的逐点命题相等
  record _≈MM_ (m n : MorphismMorphism) : Set (o ⊔ h ⊔ s ⊔ p) where
    field
      onActP-≈ : ∀ {A B} (f : C._⇒_ A B) {s : ShapeOf FC A} {t : ShapeOf FC B}
               → (p : actSOf FC f s ≡ t) (q : PosOf FC t)
               → MorphismMorphism.onActP m f p q ≡ MorphismMorphism.onActP n f p q

  open _≈MM_ public

  ≈MM-refl : {m : MorphismMorphism} → m ≈MM m
  ≈MM-refl = record { onActP-≈ = λ _ _ _ → refl }

  ≈MM-sym : {m n : MorphismMorphism} → m ≈MM n → n ≈MM m
  ≈MM-sym eq = record { onActP-≈ = λ f p q → sym (eq .onActP-≈ f p q) }

  ≈MM-trans : {m n k : MorphismMorphism} → m ≈MM n → n ≈MM k → m ≈MM k
  ≈MM-trans eq₁ eq₂ = record { onActP-≈ = λ f p q → trans (eq₁ .onActP-≈ f p q) (eq₂ .onActP-≈ f p q) }

  ≈MM-isEquivalence : IsEquivalence _≈MM_
  ≈MM-isEquivalence = record { refl = ≈MM-refl ; sym = ≈MM-sym ; trans = ≈MM-trans }

-- Identity MorphismMorphism
-- 恒等态射间态射
module _ {o h e s p u : Level} {C : Category o h e}
         {FC : Functor C (ContCat s p)} {X : Set u}
         (UF : Unfolding FC X) where
  private
    module UF = Unfolding UF
    S = id {C = ShapeCat C FC}
    shapeTrans : ∀ {A} {s : ShapeOf FC A} → PosOf FC s
               → ShapeOf FC (Functor.₀ (Unfolding.unfoldFunctor UF) (A , s))
    shapeTrans = λ p → UF.pos-to-shape _ p
    MO = idMorphismObject UF

  idMorphismMorphism : MorphismMorphism UF UF S shapeTrans MO
  idMorphismMorphism = record { onActP = λ f p q → refl }

-- Composition of MorphismMorphisms
-- 态射间态射的复合
module _ {o₁ h₁ e₁ o₂ h₂ e₂ o₃ h₃ e₃ s p u v w : Level}
         {C : Category o₁ h₁ e₁} {D : Category o₂ h₂ e₂} {E : Category o₃ h₃ e₃}
         {FC : Functor C (ContCat s p)} {FD : Functor D (ContCat s p)} {FE : Functor E (ContCat s p)}
         {X : Set u} {Y : Set v} {Z : Set w}
         (UF : Unfolding FC X) (UG : Unfolding FD Y) (UH : Unfolding FE Z)
         (S₁ : Functor (ShapeCat C FC) (ShapeCat D FD))
         (S₂ : Functor (ShapeCat D FD) (ShapeCat E FE))
         (shTrans₁ : ∀ {A} {s : ShapeOf FC A} → PosOf FC s
                   → ShapeOf FD (Functor.₀ (Unfolding.unfoldFunctor UG) (Functor.₀ S₁ (A , s))))
         (shTrans₂ : ∀ {A} {s : ShapeOf FD A} → PosOf FD s
                   → ShapeOf FE (Functor.₀ (Unfolding.unfoldFunctor UH) (Functor.₀ S₂ (A , s)))) where
  private
    module S₁ = Functor S₁
    open MorphismObject

  -- The composition of MorphismMorphisms is automatic: the needed coherence
  -- follows directly from the functor composition. The step is proved by reflexivity.
  -- 态射间态射的复合自动成立：所需融贯性直接源于函子复合，该步骤由自反性证明。
  compMorphismMorphism :
      {MOf : MorphismObject UF UG S₁ shTrans₁}
      {MOg : MorphismObject UG UH S₂ shTrans₂}
      (MMf : MorphismMorphism UF UG S₁ shTrans₁ MOf)
      (MMg : MorphismMorphism UG UH S₂ shTrans₂ MOg)
    → MorphismMorphism UF UH (S₂ ∘F S₁)
        (λ p → shTrans₂ (MorphismObject.onPos MOf p))
        (compMorphismObject UF UG UH S₁ S₂ shTrans₁ shTrans₂ MOf MOg)
  compMorphismMorphism {MOf = MOf} {MOg = MOg} MMf MMg = record
    { onActP = λ {A} {B} f {s} {t} p q →
      let g  = proj₁ (S₁.₁ (f , p))
          p′ = proj₂ (S₁.₁ (f , p))
      in begin
        onPos MOg (onPos MOf (actPOf FC f s (subst (PosOf FC) (sym p) q)))
          ≡⟨ cong (onPos MOg) (MorphismMorphism.onActP MMf f p q) ⟩
        onPos MOg (actP-from-S FC FD S₁ f p (onPos MOf q))
          ≡⟨ MorphismMorphism.onActP MMg g p′ (onPos MOf q) ⟩
        actP-from-S FD FE S₂ g p′ (onPos MOg (onPos MOf q))
          ≡⟨ refl ⟩
        actP-from-S FC FE (S₂ ∘F S₁) f p (onPos MOg (onPos MOf q))
      ∎
    }
