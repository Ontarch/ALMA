------------------------------------------------------------------------
-- Proves substitution–commutation for position maps, and naturality
-- of shape components for ContCat-valued natural transformations
--
-- 证明位置映射与替换的交换性，以及取值于 ContCat 的自然变换
-- 其形状分量的自然性
------------------------------------------------------------------------
{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module SecondPass.ContCatEquivLemmas where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Sigma using (_,_)
open import Relation.Binary.PropositionalEquality.Core using (subst)
open import Data.Product.Base using (proj₂)
open import Data.Container.Core using (shape)

open import Categories.Category.Core using (Category)
open import Categories.Functor.Core using (Functor)
open import Categories.NaturalTransformation.Core using (NaturalTransformation)

open import Cosmos.ContCategory using (ContCat)
open import Cosmos.ContCategoryLemmas using (shape-eq-from-≈sr; ShapeOf; PosOf)
open import Cosmos.ContCatEquiv using (ShapeCat)
open import SecondPass.Unfolding using (Unfolding)
open import SecondPass.MorphismObject using (MorphismObject)

-- Substitution commutes with the position map of a MorphismObject:
-- applying onPos after substituting along a shape equality in the source
-- equals substituting along the induced shape equality in the target
-- after applying onPos
--
-- 替换与 MorphismObject 的位置映射交换：
-- 在源端沿形状等式替换后再施加 onPos，
-- 等于先施加 onPos 再在目标端沿诱导的形状等式替换
onPos-subst-comm :
  ∀ {o h e o′ ℓ′ e′ s p u v}
    {C : Category o h e} {D : Category o′ ℓ′ e′}
    {FC : Functor C (ContCat s p)} {FD : Functor D (ContCat s p)}
    {X : Set u} {Y : Set v}
    {UF : Unfolding FC X} {UG : Unfolding FD Y}
    {S : Functor (ShapeCat C FC) (ShapeCat D FD)}
    {shapeTrans : ∀ {A} {s : ShapeOf FC A}
                → PosOf FC s
                → ShapeOf FD (Functor.₀ (Unfolding.unfoldFunctor UG)
                                        (Functor.₀ S (A , s)))}
    (MO : MorphismObject UF UG S shapeTrans)
    {A : Category.Obj C}
    {s₁ s₂ : ShapeOf FC A}
    (eq : s₁ ≡ s₂)
    (p : PosOf FC s₁)
  → MorphismObject.onPos MO (subst (PosOf FC) eq p)
    ≡ subst (λ s → PosOf FD (proj₂ (Functor.₀ S (A , s))))
            eq
            (MorphismObject.onPos MO p)
onPos-subst-comm MO refl p = refl

-- Naturality of the shape component: for any ContCat-valued natural
-- transformation η : F ⟹ G, the shape map of η commutes with the
-- shape action of F and G. Extracted from η's commute law via
-- shape-eq-from-≈sr (setoid equivalence → propositional equality)
--
-- 形状分量的自然性：对任意取值于 ContCat 的自然变换 η : F ⟹ G，
-- η 的形状映射与 F、G 的形状作用交换。由 η 的 commute 定律经
-- shape-eq-from-≈sr（setoid 等价 → 命题相等）提取得到
nat-shape-eq : ∀ {o h e s p}
  {C : Category o h e}
  {F G : Functor C (ContCat s p)}
  {η : NaturalTransformation F G}
  {A B : Category.Obj C} (f : Category._⇒_ C A B) (s : ShapeOf F A)
  → shape (NaturalTransformation.η η B) (shape (Functor.F₁ F f) s)
    ≡ shape (Functor.F₁ G f) (shape (NaturalTransformation.η η A) s)
nat-shape-eq {η = η} f s = shape-eq-from-≈sr (NaturalTransformation.commute η f) s
