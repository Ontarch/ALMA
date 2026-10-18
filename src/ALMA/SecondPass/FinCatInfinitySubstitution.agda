------------------------------------------------------------------------
-- Generic substitution lemmas for cross-cosmos morphisms
--
-- Source and target substitution for _⇒ℱX_, their interaction with
-- composition, and congruence of _≈⇒ℱX_ under substitution.
--
-- 跨宇宙态射的通用替换引理
--
-- _⇒ℱX_ 的源端与目标端替换、它们与复合的交互，以及 _≈⇒ℱX_ 在替换下的同余性。
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module ALMA.SecondPass.FinCatInfinitySubstitution where

open import Agda.Primitive using (Level)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Level using (Lift; lift)
open import Data.Product.Base using (proj₁; proj₂; _,_)
open import Data.Unit.Polymorphic.Base using (⊤; tt)
open import Relation.Binary.PropositionalEquality.Core using (cong; cong₂; sym; trans; subst)
open import Relation.Binary.PropositionalEquality.Properties using (subst-∘; subst-sym-subst)

open import Categories.Category.Core using (Category)
open import Categories.Functor.Core using (Functor)
open import Categories.Functor using (id)

open import ALMA.Cosmos.ContCategory using (ContCat)
open import ALMA.Cosmos.ContCategoryLemmas using (ShapeOf; PosOf)
open import ALMA.Cosmos.ContCatEquiv using (ShapeCat)
open import ALMA.SecondPass.Unfolding using (Unfolding; module Unfolding)
open import ALMA.SecondPass.Cosmos using (Cosmos; out; _⇒ℱ[_]_; _⇒ℱ_; ⇒ℱLayer[_])
open import ALMA.SecondPass.MorphismObject using (MorphismObject)
open import ALMA.SecondPass.MorphismMorphism using (MorphismMorphism)
open import ALMA.SecondPass.FinCatNWitness using (module FinCatN)
open import ALMA.SecondPass.FinCatInfinity using (FinCat∞; TrivialFC∞)
open import ALMA.SecondPass.FinCatInfinityColimit using
  (CompatibleTower; _⇒ℱX[_]_; ⇒ℱXLayer[_]; comp⇒ℱX; id⇒ℱX; module TowerShapeFunctors)
open import ALMA.SecondPass.FinCatInfinityColimitUniversal using
  (_≈⇒ℱX_; ≈⇒ℱXLayer; ≈⇒ℱX-refl; ≈⇒ℱX-sym; ≈⇒ℱX-trans; ≡-to-≈⇒ℱX)

open ⇒ℱLayer[_]
open _⇒ℱX[_]_
open ⇒ℱXLayer[_]
open _≈⇒ℱX_
open ≈⇒ℱXLayer
open MorphismObject
open MorphismMorphism

-- Source substitution: transport a cross-category morphism along an
-- equality of the source cosmos
--
-- 源端替换：沿源宇宙的等式传输跨范畴态射
subst-src-FinCatN : ∀ {m}
  {x x' : Cosmos (FinCatN.FinCatN m) (FinCatN.TrivialFCN m)}
  {Y : Cosmos FinCat∞ TrivialFC∞}
  → x ≡ x'
  → (x ⇒ℱX[ TowerShapeFunctors.S-proj m ] Y)
  → (x' ⇒ℱX[ TowerShapeFunctors.S-proj m ] Y)
subst-src-FinCatN {m} {x} {x'} {Y} eq f =
  subst (λ z → z ⇒ℱX[ TowerShapeFunctors.S-proj m ] Y) eq f

-- Source substitution round-trip: substituting along eq and then sym eq
-- is _≈⇒ℱX_-equivalent to the original morphism
--
-- 源端替换的往返：沿 eq 与 sym eq 连续替换后 _≈⇒ℱX_-等价于原态射
subst-src-sym-sym-≈⇒ℱX :
  ∀ {m} {x x′ : Cosmos (FinCatN.FinCatN m) (FinCatN.TrivialFCN m)}
    {Y : Cosmos FinCat∞ TrivialFC∞}
  (eq : x ≡ x′)
  (f : x ⇒ℱX[ TowerShapeFunctors.S-proj m ] Y)
  → subst-src-FinCatN (sym eq) (subst-src-FinCatN eq f)
    ≈⇒ℱX f
subst-src-sym-sym-≈⇒ℱX {m} {x} {x′} {Y = Y} eq f =
  ≡-to-≈⇒ℱX
    (subst-sym-subst
       {P = λ z → z ⇒ℱX[ TowerShapeFunctors.S-proj m ] Y}
       eq
       {p = f})

-- Source substitution preserves _≈⇒ℱX_
--
-- 源端替换保持 _≈⇒ℱX_
subst-src-≈ : ∀ {m}
  {x x' : Cosmos (FinCatN.FinCatN m) (FinCatN.TrivialFCN m)}
  {Y : Cosmos FinCat∞ TrivialFC∞}
  (eq : x ≡ x')
  {f g : x ⇒ℱX[ TowerShapeFunctors.S-proj m ] Y}
  → f ≈⇒ℱX g
  → subst-src-FinCatN eq f ≈⇒ℱX subst-src-FinCatN eq g
subst-src-≈ refl p = p

-- Composition commutes with source substitution
--
-- 复合与源端替换交换
comp⇒ℱX-subst-src : ∀ {m}
  {x x' : Cosmos (FinCatN.FinCatN m) (FinCatN.TrivialFCN m)}
  {Y Z : Cosmos FinCat∞ TrivialFC∞}
  {g : Y ⇒ℱX[ id ] Z}
  {f : x ⇒ℱX[ TowerShapeFunctors.S-proj m ] Y}
  (eq : x ≡ x')
  → subst-src-FinCatN eq (comp⇒ℱX g f) ≡ comp⇒ℱX g (subst-src-FinCatN eq f)
comp⇒ℱX-subst-src refl = refl

-- Target substitution distributes over onunfold-next
--
-- 目标端替换关于 onunfold-next 分配
subst-⇒ℱX-dst-onunfold-next :
  ∀ {o h e o′ h′ e′ s p}
    {C : Category o h e} {D : Category o′ h′ e′}
    {FC : Functor C (ContCat s p)} {FD : Functor D (ContCat s p)}
    {S : Functor (ShapeCat C FC) (ShapeCat D FD)}
    {x : Cosmos C FC} {y y′ : Cosmos D FD}
    (eq : y ≡ y′)
    (f : x ⇒ℱX[ S ] y)
    {A : Category.Obj C}
    (s : ShapeOf FC A)
  → (subst (λ (z : Cosmos _ _) → x ⇒ℱX[ S ] z) eq f)
      .out .onunfold-next {A = A} s
    ≡ subst
        (λ (z : Cosmos _ _) →
           Unfolding.unfold-next (out x) {A = A} s
           ⇒ℱX[ S ]
           Unfolding.unfold-next (out z)
             {A = proj₁ (Functor.F₀ S (A , s))}
             (proj₂ (Functor.F₀ S (A , s))))
        eq
        (f .out .onunfold-next {A = A} s)
subst-⇒ℱX-dst-onunfold-next {y = y} {y′ = y′} eq f {A = A} s with y′ | eq
... | .y | refl = refl

-- Lift ⊤ is a singleton
--
-- Lift ⊤ 的元素唯一性
≡-Lift-⊤ : ∀ {ℓ} (x y : Lift ℓ (⊤ {ℓ})) → x ≡ y
≡-Lift-⊤ (lift tt) (lift tt) = refl

-- subst commutes with cong
--
-- subst 与 cong 交换
subst-cong′ :
  ∀ {a b c} {A : Set a} {B : Set b} {P : B → Set c}
    {x y : A} (f : A → B) (e : x ≡ y) {u : P (f x)}
  → subst (λ z → P (f z)) e u ≡ subst P (cong f e) u
subst-cong′ {x = x} {y = y} f e with y | e
... | .x | refl = refl

-- Target substitution on shapeTrans
--
-- 目标端替换在 shapeTrans 上
subst-⇒ℱX-dst-shapeTrans :
  ∀ {o h e o′ h′ e′ s p}
    {C : Category o h e} {D : Category o′ h′ e′}
    {FC : Functor C (ContCat s p)} {FD : Functor D (ContCat s p)}
    {S : Functor (ShapeCat C FC) (ShapeCat D FD)}
    {x : Cosmos C FC} {y y′ : Cosmos D FD}
  (eq : y ≡ y′) (f : x ⇒ℱX[ S ] y)
  {A : Category.Obj C} {s : ShapeOf FC A} (p : PosOf FC s)
  → ⇒ℱXLayer[_].shapeTrans
      ((subst (λ z → x ⇒ℱX[ S ] z) eq f) .out) p
    ≡ subst
        (λ z → ShapeOf FD
          (Functor.F₀ (Unfolding.unfoldFunctor (out z))
                      (Functor.F₀ S (A , s))))
        eq
        (⇒ℱXLayer[_].shapeTrans (f .out) p)
subst-⇒ℱX-dst-shapeTrans {y = y} {y′ = y′} eq f {A = A} {s = s} p with y′ | eq
... | .y | refl = refl

-- Target substitution on onPos
--
-- 目标端替换在 onPos 上
subst-⇒ℱX-dst-onPos :
  ∀ {o h e o′ h′ e′ s p}
    {C : Category o h e} {D : Category o′ h′ e′}
    {FC : Functor C (ContCat s p)} {FD : Functor D (ContCat s p)}
    {S : Functor (ShapeCat C FC) (ShapeCat D FD)}
    {x : Cosmos C FC} {y y′ : Cosmos D FD}
  (eq : y ≡ y′) (f : x ⇒ℱX[ S ] y)
  {A : Category.Obj C} {s : ShapeOf FC A} (p : PosOf FC s)
  → MorphismObject.onPos
      (⇒ℱXLayer[_].morphismObj
         ((subst (λ z → x ⇒ℱX[ S ] z) eq f) .out)) p
    ≡ MorphismObject.onPos
        (⇒ℱXLayer[_].morphismObj (f .out)) p
subst-⇒ℱX-dst-onPos {y = y} {y′ = y′} eq f {A = A} {s = s} p with y′ | eq
... | .y | refl = refl

subst-dst-general-≈⇒ℱX
  : ∀ {o h e o′ h′ e′ s p}
    {C : Category o h e} {D : Category o′ h′ e′}
    {FC : Functor C (ContCat s p)} {FD : Functor D (ContCat s p)}
    {S : Functor (ShapeCat C FC) (ShapeCat D FD)}
    {x : Cosmos C FC} {Y Y' : Cosmos D FD}
    (eq : Y ≡ Y')
    {f : x ⇒ℱX[ S ] Y} {g : x ⇒ℱX[ S ] Y'}
  → subst (λ Z → x ⇒ℱX[ S ] Z) eq f ≈⇒ℱX g
  → subst (λ Z → x ⇒ℱX[ S ] Z) (sym eq) g ≈⇒ℱX f
subst-dst-general-≈⇒ℱX refl p = ≈⇒ℱX-sym p

subst-sym-subst-≈⇒ℱX
  : ∀ {o h e o′ h′ e′ s p}
    {C : Category o h e} {D : Category o′ h′ e′}
    {FC : Functor C (ContCat s p)} {FD : Functor D (ContCat s p)}
    {S : Functor (ShapeCat C FC) (ShapeCat D FD)}
    {x : Cosmos C FC} {Y Y' : Cosmos D FD}
    (eq : Y ≡ Y')
    {f : x ⇒ℱX[ S ] Y}
  → subst (λ Z → x ⇒ℱX[ S ] Z) (sym eq)
      (subst (λ Z → x ⇒ℱX[ S ] Z) eq f)
    ≈⇒ℱX f
subst-sym-subst-≈⇒ℱX refl = ≈⇒ℱX-refl

-- Source substitution on shapeTrans
--
-- 源端替换在 shapeTrans 上
subst-⇒ℱX-src-shapeTrans : ∀ {o h e o′ h′ e′ s p}
  {C : Category o h e} {D : Category o′ h′ e′}
  {FC : Functor C (ContCat s p)} {FD : Functor D (ContCat s p)}
  {S : Functor (ShapeCat C FC) (ShapeCat D FD)}
  {x x' : Cosmos C FC} {Y : Cosmos D FD}
  (eq : x ≡ x') (f : x ⇒ℱX[ S ] Y)
  {A : Category.Obj C} {s : ShapeOf FC A} (p : PosOf FC s)
  → ⇒ℱXLayer[_].shapeTrans ((subst (λ z → z ⇒ℱX[ S ] Y) eq f) .out) p
    ≡ ⇒ℱXLayer[_].shapeTrans (f .out) p
subst-⇒ℱX-src-shapeTrans refl f p = refl

-- Source substitution on onPos
--
-- 源端替换在 onPos 上
subst-⇒ℱX-src-onPos : ∀ {o h e o′ h′ e′ s p}
  {C : Category o h e} {D : Category o′ h′ e′}
  {FC : Functor C (ContCat s p)} {FD : Functor D (ContCat s p)}
  {S : Functor (ShapeCat C FC) (ShapeCat D FD)}
  {x x' : Cosmos C FC} {Y : Cosmos D FD}
  (eq : x ≡ x') (f : x ⇒ℱX[ S ] Y)
  {A : Category.Obj C} {s : ShapeOf FC A} (p : PosOf FC s)
  → MorphismObject.onPos (⇒ℱXLayer[_].morphismObj ((subst (λ z → z ⇒ℱX[ S ] Y) eq f) .out)) p
    ≡ MorphismObject.onPos (⇒ℱXLayer[_].morphismObj (f .out)) p
subst-⇒ℱX-src-onPos refl f p = refl

-- Source substitution on onunfold-next
--
-- 源端替换在 onunfold-next 上
subst-⇒ℱX-src-onunfold-next : ∀ {o h e o′ h′ e′ s p}
  {C : Category o h e} {D : Category o′ h′ e′}
  {FC : Functor C (ContCat s p)} {FD : Functor D (ContCat s p)}
  {S : Functor (ShapeCat C FC) (ShapeCat D FD)}
  {x x' : Cosmos C FC} {Y : Cosmos D FD}
  (eq : x ≡ x') (f : x ⇒ℱX[ S ] Y)
  {A : Category.Obj C} (s : ShapeOf FC A)
  → (subst (λ z → z ⇒ℱX[ S ] Y) eq f) .out .onunfold-next {A = A} s
    ≡ subst (λ z → z ⇒ℱX[ S ]
              Unfolding.unfold-next (out Y)
                {A = proj₁ (Functor.F₀ S (A , s))}
                (proj₂ (Functor.F₀ S (A , s))))
            (cong (λ z → Unfolding.unfold-next (out z) {A = A} s) eq)
            (f .out .onunfold-next {A = A} s)
subst-⇒ℱX-src-onunfold-next refl f p = refl

-- _≈⇒ℱX_-congruence of source substitution
--
-- 源端替换的 _≈⇒ℱX_-同余性
subst-src-≈-coind : ∀ {o h e o′ h′ e′ s p}
  {C : Category o h e} {D : Category o′ h′ e′}
  {FC : Functor C (ContCat s p)} {FD : Functor D (ContCat s p)}
  {S : Functor (ShapeCat C FC) (ShapeCat D FD)}
  {x x' : Cosmos C FC} {Y : Cosmos D FD}
  (eq : x ≡ x')
  {f g : x ⇒ℱX[ S ] Y}
  → f ≈⇒ℱX g
  → subst (λ z → z ⇒ℱX[ S ] Y) eq f ≈⇒ℱX subst (λ z → z ⇒ℱX[ S ] Y) eq g
subst-src-≈-coind eq {f} {g} p .out .shapeTrans-eq {A} {s} p' =
  trans (subst-⇒ℱX-src-shapeTrans eq f p')
        (trans (p .out .shapeTrans-eq {A} {s} p')
               (sym (subst-⇒ℱX-src-shapeTrans eq g p')))
subst-src-≈-coind eq {f} {g} p .out .onPos-eq {A} {s} p' =
  trans (subst-⇒ℱX-src-onPos eq f p')
        (trans (p .out .onPos-eq {A} {s} p')
               (sym (subst-⇒ℱX-src-onPos eq g p')))
subst-src-≈-coind eq {f} {g} p .out .onunfold-next-eq {A = A} s
  rewrite subst-⇒ℱX-src-onunfold-next eq f {A} s
        | subst-⇒ℱX-src-onunfold-next eq g {A} s
  = subst-src-≈-coind
      (cong (λ z → Unfolding.unfold-next (out z) {A = A} s) eq)
      (p .out .onunfold-next-eq {A = A} s)
