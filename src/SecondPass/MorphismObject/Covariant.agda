------------------------------------------------------------------------
-- Object-level homomorphisms between unfolding systems
--
-- A Covariant witnesses the commutation of object/position mappings
-- with the container natural isomorphism
--
-- 展开系统之间的对象级同态
--
-- Covariant 见证对象映射与位置映射同容器自然同构之间的交换性
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module SecondPass.MorphismObject.Covariant where

open import Agda.Primitive using (Level; _⊔_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Sigma using (_,_)
open import Data.Product.Base using (proj₂)
open import Data.Container.Core using (shape)

open import Categories.Category.Core using (Category)
open import Categories.Functor.Core using (Functor)
open import Categories.Functor using (id; _∘F_)
open import Categories.NaturalTransformation.Core using (NaturalTransformation)
open import Categories.NaturalTransformation.NaturalIsomorphism using (NaturalIsomorphism)

open import Cosmos.ContCategory using (ContCat)
open import Cosmos.ContCategoryLemmas using (ShapeOf; PosOf)
open import Cosmos.ContCatEquiv using (ShapeCat)
open import SecondPass.ContCatEquivFunctor
  using (ContCatEquivFunctor; module ShapeCatMorphism)
open import SecondPass.Unfolding using (Unfolding)

-- A morphism object between two unfolding systems UF and UG:
-- onPos maps positions of FC to positions of FD along the shape functor S
-- pts-compat asserts that shapeTrans agrees with pos-to-shape ∘ onPos
-- 两个展开系统 UF 与 UG 之间的态射对象：
-- onPos 沿形状函子 S 将 FC 的位置映射为 FD 的位置
-- pts-compat 断言 shapeTrans 与 pos-to-shape ∘ onPos 一致
module _ {o h e o′ ℓ′ e′ s p u v : Level}
         {C : Category o h e} {D : Category o′ ℓ′ e′}
         {FC : Functor C (ContCat s p)} {FD : Functor D (ContCat s p)}
         {X : Set u} {Y : Set v}
         (UF : Unfolding FC X) (UG : Unfolding FD Y)
         (S  : Functor (ShapeCat C FC) (ShapeCat D FD))
         (shapeTrans : ∀ {A} {s : ShapeOf FC A}
                     → PosOf FC s
                     → ShapeOf FD
                         (Functor.₀ (Unfolding.unfoldFunctor UG)
                                    (Functor.₀ S (A , s)))) where
  private
    module UG = Unfolding UG; module Sf = Functor S
  record Covariant : Set (o ⊔ s ⊔ p) where
    field
      -- Position mapping: sends each position of FC over shape s
      -- to a position of FD over the image shape S(A, s)
      -- 位置映射：将 FC 在形状 s 上的每个位置
      -- 映为 FD 在像形状 S(A, s) 上的位置
      onPos      : ∀ {A} {s : ShapeOf FC A} → PosOf FC s → PosOf FD (proj₂ (Sf.₀ (A , s)))
      -- Compatibility: shapeTrans p ≡ pos-to-shape (S(A,s)) (onPos p)
      -- 相容性：shapeTrans p ≡ pos-to-shape (S(A,s)) (onPos p)
      pts-compat : ∀ {A} {s : ShapeOf FC A} (p : PosOf FC s) → shapeTrans p ≡ UG.pos-to-shape (proj₂ (Sf.₀ (A , s))) (onPos p)

-- Identity morphism object: positions map to themselves, compatibility is definitional
-- 恒等态射对象：位置映为自身，相容性由定义等式给出
module _ {o h e s p u : Level} {C : Category o h e}
         {FC : Functor C (ContCat s p)} {X : Set u} (UF : Unfolding FC X) where
  private module UF = Unfolding UF
  idCovariant : Covariant UF UF id (λ p → UF.pos-to-shape _ p)
  idCovariant = record { onPos = λ p → p ; pts-compat = λ p → refl }

-- Composition of morphism objects: positions compose sequentially,
-- compatibility reduces to mo₂'s since shTrans₁ is absorbed into the composite shapeTrans
-- 态射对象的复合：位置逐层复合，
-- 因 shTrans₁ 已被吸收进复合 shapeTrans 的定义，相容性归结为 mo₂ 的相容性
module _ {o₁ h₁ e₁ o₂ h₂ e₂ o₃ h₃ e₃ s p u v w : Level}
         {C : Category o₁ h₁ e₁} {D : Category o₂ h₂ e₂} {E : Category o₃ h₃ e₃}
         {FC : Functor C (ContCat s p)} {FD : Functor D (ContCat s p)} {FE : Functor E (ContCat s p)}
         {X : Set u} {Y : Set v} {Z : Set w}
         (UF : Unfolding FC X) (UG : Unfolding FD Y) (UH : Unfolding FE Z)
         (S₁ : Functor (ShapeCat C FC) (ShapeCat D FD))
         (S₂ : Functor (ShapeCat D FD) (ShapeCat E FE))
         (shTrans₁ : ∀ {A} {s : ShapeOf FC A} → PosOf FC s → ShapeOf FD (Functor.₀ (Unfolding.unfoldFunctor UG) (Functor.₀ S₁ (A , s))))
         (shTrans₂ : ∀ {A} {s : ShapeOf FD A} → PosOf FD s → ShapeOf FE (Functor.₀ (Unfolding.unfoldFunctor UH) (Functor.₀ S₂ (A , s)))) where
  compCovariant : (mo₁ : Covariant UF UG S₁ shTrans₁) (mo₂ : Covariant UG UH S₂ shTrans₂)
                     → Covariant UF UH (S₂ ∘F S₁) (λ p → shTrans₂ (Covariant.onPos mo₁ p))
  compCovariant mo₁ mo₂ = record
    { onPos = λ p → onPos mo₂ (onPos mo₁ p)
    ; pts-compat = λ p → pts-compat mo₂ (onPos mo₁ p)
    } where open Covariant

-- Construct a Covariant from a ContCatEquivFunctor and a natural isomorphism
-- 由 ContCatEquivFunctor 与自然同构构造 Covariant
module _ {o h e o′ ℓ′ e′ s p u v : Level}
         {C : Category o h e} {D : Category o′ ℓ′ e′}
         {FC : Functor C (ContCat s p)} {FD : Functor D (ContCat s p)}
         {X : Set u} {Y : Set v} (UF : Unfolding FC X) (UG : Unfolding FD Y) where
  private
    module UF  = Unfolding UF
    module UG  = Unfolding UG
    module FD  = Functor FD
    module UFf = Functor UF.unfoldFunctor

  -- Given:
  -- cf : a ContCatEquivFunctor witnessing FC ≈ FD ∘ H
  -- ni : a natural isomorphism H ∘ unfoldFunctor UF ≅ unfoldFunctor UG ∘ S
  -- onPos₀ : a position mapping along S
  -- coh : coherence between shapeTrans (induced by α and ni) and pos-to-shape ∘ onPos₀
  -- 给定：
  -- cf : 见证 FC ≈ FD ∘ H 的 ContCatEquivFunctor
  -- ni : 自然同构 H ∘ unfoldFunctor UF ≅ unfoldFunctor UG ∘ S
  -- onPos₀ : 沿 S 的位置映射
  -- coh : 由 α 与 ni 诱导的 shapeTrans 同 pos-to-shape ∘ onPos₀ 之间的相容条件
  mkCovariant :
    ∀ {H : Functor C D} {α : NaturalTransformation FC (FD ∘F H)}
    → (cf : ContCatEquivFunctor FC FD H α)
    → let module SCM = ShapeCatMorphism cf in
      (ni : NaturalIsomorphism (H ∘F UF.unfoldFunctor) (UG.unfoldFunctor ∘F SCM.S))
    → (onPos₀ : ∀ {A} {s : ShapeOf FC A} → PosOf FC s → PosOf FD (proj₂ (Functor.₀ SCM.S (A , s))))
    → (coh : ∀ {A} {s : ShapeOf FC A} (p : PosOf FC s)
           → shape (FD.₁ (NaturalTransformation.η (NaturalIsomorphism.F⇒G ni) (A , s)))
                   (shape (NaturalTransformation.η α (UFf.₀ (A , s))) (UF.pos-to-shape s p))
             ≡ UG.pos-to-shape (proj₂ (Functor.₀ SCM.S (A , s))) (onPos₀ p))
    → Covariant UF UG SCM.S
        (λ {A} {s} p → shape (FD.₁ (NaturalTransformation.η (NaturalIsomorphism.F⇒G ni) (A , s)))
                             (shape (NaturalTransformation.η α (UFf.₀ (A , s))) (UF.pos-to-shape s p)))
  mkCovariant cf ni onPos₀ coh = record { onPos = onPos₀ ; pts-compat = coh }
