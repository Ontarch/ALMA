------------------------------------------------------------------------
-- Morphisms between ContCat-valued functors
--
-- A natural transformation α : FC ⟹ FD ∘ H
-- where FC, FD : ContCat-valued functors, H : C → D
--
-- ContCat 值函子之间的态射
--
-- 自然变换 α : FC ⟹ FD ∘ H，
-- 其中 FC、FD 为取值于 ContCat 的函子，H : C → D 为基函子
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module SecondPass.ContCatEquivFunctor where

open import Agda.Primitive using (Level)
open import Agda.Builtin.Equality using (_≡_)
open import Relation.Binary.PropositionalEquality.Core using (cong; sym; trans)
open import Data.Product.Base using (_,_)
open import Data.Container.Core using (shape)

open import Categories.Category.Core using (Category)
open import Categories.Functor.Core using (Functor)
open import Categories.Functor using (id; _∘F_)
open import Categories.NaturalTransformation.Core
  using (NaturalTransformation; _∘ᵥ_; _∘ʳ_)
open import Categories.NaturalTransformation.NaturalIsomorphism
  using (NaturalIsomorphism; unitorʳ; associator)

open import Cosmos.ContCategory using (ContCat)
open import Cosmos.ContCategoryLemmas using (shape-eq-from-≈sr)
open import Cosmos.ContCatEquiv using (ShapeCat)

-- Pairs a base functor H : C → D with a natural transformation α : FC ⟹ FD ∘ H
-- between ContCat-valued functors
--
-- 将基函子 H : C → D 与 ContCat 值函子间的自然变换 α : FC ⟹ FD ∘ H 配对
module _ {o h e o′ ℓ′ e′ s p : Level}
    {C : Category o h e}
    {D : Category o′ ℓ′ e′}
    (FC : Functor C (ContCat s p))
    (FD : Functor D (ContCat s p))
    (baseFunctor : Functor C D)
    (containerNat : NaturalTransformation FC (FD ∘F baseFunctor)) where

  -- Parameterised record: packages two ContCat-valued functors FC, FD,
  -- a base functor C → D, and a natural transformation FC ⟹ FD ∘F baseFunctor
  -- as module context; has no fields, so instantiation is trivial (record {})
  --
  -- 参数化 record：将两个取值于 ContCat 的函子 FC、FD，
  -- 一个基函子 C → D，以及自然变换 FC ⟹ FD ∘F baseFunctor
  -- 封装为模块上下文；无字段，故实例化是平凡的（record {}）
  record ContCatEquivFunctor : Set where

-- Identity ContCatEquivFunctor: FC ⟹ FC ∘ id, via the right unitor
--
-- 恒等 ContCatEquivFunctor：FC ⟹ FC ∘ id，由右单位同构给出
idContCatEquivFunctor : ∀ {o h e s p} {C : Category o h e}
  (FC : Functor C (ContCat s p))
  → ContCatEquivFunctor FC FC id (NaturalIsomorphism.F⇐G unitorʳ)
idContCatEquivFunctor FC = record {}

-- Composition of ContCatEquivFunctors:
-- using the associator to rebracket (FE ∘ bg) ∘ bf ≅ FE ∘ (bg ∘ bf)
--
-- ContCatEquivFunctor 的复合：
-- 利用结合同构将 (FE ∘ bg) ∘ bf 重括号为 FE ∘ (bg ∘ bf)
compContCatEquivFunctor : ∀ {o h e o′ ℓ′ e′ o″ ℓ″ e″ s p}
    {C : Category o h e}
    {D : Category o′ ℓ′ e′}
    {E : Category o″ ℓ″ e″}
    (FC : Functor C (ContCat s p))
    (FD : Functor D (ContCat s p))
    (FE : Functor E (ContCat s p))
    {bg : Functor D E} {bf : Functor C D}
    {ng : NaturalTransformation FD (FE ∘F bg)}
    {nf : NaturalTransformation FC (FD ∘F bf)}
  → ContCatEquivFunctor FD FE bg ng
  → ContCatEquivFunctor FC FD bf nf
  → ContCatEquivFunctor FC FE (bg ∘F bf)
      ( NaturalIsomorphism.F⇒G (associator bf bg FE)
          ∘ᵥ (ng ∘ʳ bf)
          ∘ᵥ nf
      )
compContCatEquivFunctor _ _ _ _ _ = record {}

-- Trivial constructor assembling a base functor and a natural transformation
--
-- 将基函子与自然变换组装为 ContCatEquivFunctor 的平凡构造子
mkContCatEquivFunctor : ∀ {o h e o′ ℓ′ e′ s p}
    {C : Category o h e} {D : Category o′ ℓ′ e′}
    (F : Functor C D)
    (FC : Functor C (ContCat s p))
    (FD : Functor D (ContCat s p))
    (α : NaturalTransformation FC (FD ∘F F))
  → ContCatEquivFunctor FC FD F α
mkContCatEquivFunctor _ _ _ _ = record {}

-- Functor between shape categories induced by a ContCatEquivFunctor:
-- ShapeCat(C, FC) → ShapeCat(D, FD)
-- Objects (A, s) map to (H A, shape(η_A)(s));
-- morphisms use the shape component of the naturality square
--
-- 由 ContCatEquivFunctor 诱导的形状范畴间的函子：
-- ShapeCat(C, FC) → ShapeCat(D, FD)
-- 对象 (A, s) 映至 (H A, shape(η_A)(s))；
-- 态射利用自然性方格的形状分量
module ShapeCatMorphism {o h e o′ ℓ′ e′ s p}
    {C : Category o h e} {D : Category o′ ℓ′ e′}
    {FC : Functor C (ContCat s p)} {FD : Functor D (ContCat s p)}
    {H : Functor C D}
    {α : NaturalTransformation FC (FD ∘F H)}
    (cf : ContCatEquivFunctor FC FD H α)
    where
  private
    open NaturalTransformation α
    module H = Functor H
    module FC = Functor FC
    module FD = Functor FD
  S : Functor (ShapeCat C FC) (ShapeCat D FD)
  S = record
    { F₀ = λ { (A , s) → (H.₀ A , shape (η A) s) }
    ; F₁ = λ { {(A , s)} {(B , t)} (f , p) →
        let
          -- Shape-level equation extracted from the naturality square
          --
          -- 从自然性方格中提取的形状层等式
          comm-shape : shape (η B) (shape (FC.F₁ f) s) ≡ shape (FD.F₁ (H.F₁ f)) (shape (η A) s)
          comm-shape = shape-eq-from-≈sr (commute f) s

          -- Reindexing proof: transport the target shape along comm-shape and p
          --
          -- 重索引证明：沿 comm-shape 与 p 传输目标形状
          q : shape (FD.F₁ (H.F₁ f)) (shape (η A) s) ≡ shape (η B) t
          q = trans (sym comm-shape) (cong (shape (η B)) p)
        in (H.F₁ f , q) }

    -- Identity, composition, and equivalence preservation
    -- are inherited from the base functor H
    --
    -- 恒等、复合及等价保持性均继承自基函子 H
    ; identity     = λ { {A , s} → H.identity }
    ; homomorphism = λ { {f = _} {g = _} → H.homomorphism }
    ; F-resp-≈     = λ { {f = _} {g = _} f≈g → H.F-resp-≈ f≈g }
    }
