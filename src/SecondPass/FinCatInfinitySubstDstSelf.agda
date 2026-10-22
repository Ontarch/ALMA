------------------------------------------------------------------------
-- Target substitution by a self-equality is _≈⇒ℱX_-trivial
--
-- Under a shape-UIP hypothesis, substituting the target of a morphism
-- along a self-equality does not change it up to _≈⇒ℱX_.
--
-- 沿自等式的目标端替换在 _≈⇒ℱX_ 下平凡
--
-- 在 shape UIP 假设下，沿自等式替换态射的目标端不改变其
-- _≈⇒ℱX_-等价类。
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module SecondPass.FinCatInfinitySubstDstSelf where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Product.Base using (proj₁; proj₂; _,_)
open import Function.Base using (_∘_)
open import Relation.Binary.PropositionalEquality.Core using (cong; sym; trans; subst)

open import Categories.Category.Core using (Category)
open import Categories.Functor.Core using (Functor)

open import Cosmos.ContCategory using (ContCat)
open import Cosmos.ContCategoryLemmas using (ShapeOf)
open import Cosmos.ContCatEquiv using (ShapeCat)
open import SecondPass.Unfolding using (Unfolding)
open Unfolding using (unfold-next; unfoldFunctor)
open import SecondPass.Cosmos using (Cosmos; out)
open import SecondPass.FinCatInfinityColimit using (_⇒ℱX[_]_; ⇒ℱXLayer[_])
open import SecondPass.FinCatInfinityColimitUniversal using (_≈⇒ℱX_; ≈⇒ℱXLayer)
open import SecondPass.FinCatInfinitySubstitution

open _⇒ℱX[_]_
open ⇒ℱXLayer[_]
open _≈⇒ℱX_
open ≈⇒ℱXLayer

-- Target substitution by a self-equality is _≈⇒ℱX_-trivial, under
-- shape UIP
--
-- 沿自等式的目标端替换在 _≈⇒ℱX_ 下平凡（在 shape UIP 下）
subst-dst-self-≈⇒ℱX
  : ∀ {o h e o′ h′ e′ s p}
    {C : Category o h e} {D : Category o′ h′ e′}
    {FC : Functor C (ContCat s p)} {FD : Functor D (ContCat s p)}
    {S : Functor (ShapeCat C FC) (ShapeCat D FD)}
    {x : Cosmos C FC} {Y : Cosmos D FD}
    (shape-uip : ∀ (Y′ : Cosmos D FD) {A s}
               → (u v : ShapeOf FD
                          (Functor.F₀ (unfoldFunctor (out Y′))
                                      (Functor.F₀ S (A , s))))
               → u ≡ v)
    {eq : Y ≡ Y}
    {f : x ⇒ℱX[ S ] Y}
  → subst (λ Z → x ⇒ℱX[ S ] Z) eq f ≈⇒ℱX f
subst-dst-self-≈⇒ℱX {C = C} {D = D} {FC = FC} {FD = FD} {S = S}
  {x = x} {Y = Y} shape-uip {eq = eq} {f = f} =
  go x Y f eq
  where
    subst-∘' : ∀ {a b c} {A : Set a} {B : Set b} {x y : A}
               (P : B → Set c) (f : A → B) (e : x ≡ y)
               (p : P (f x))
             → subst (P ∘ f) e p ≡ subst P (cong f e) p
    subst-∘' P f refl p = refl

    go : (x′ : Cosmos C FC) (Y′ : Cosmos D FD)
         (g : x′ ⇒ℱX[ S ] Y′) (e : Y′ ≡ Y′)
       → subst (λ Z → x′ ⇒ℱX[ S ] Z) e g ≈⇒ℱX g
    go x′ Y′ g e .out .shapeTrans-eq {A} {s} p =
      trans (subst-⇒ℱX-dst-shapeTrans e g p)
            (shape-uip Y′ _ _)
    go x′ Y′ g e .out .onPos-eq {A} {s} p =
      subst-⇒ℱX-dst-onPos e g p
    go x′ Y′ g e .out .onunfold-next-eq {A = A} s
      rewrite subst-⇒ℱX-dst-onunfold-next e g s
            | subst-∘' (λ W → unfold-next (out x′) {A = A} s
                                 ⇒ℱX[ S ] W)
                       (λ z → unfold-next (out z)
                                {A = proj₁ (Functor.F₀ S (A , s))}
                                (proj₂ (Functor.F₀ S (A , s))))
                       e
                       (g .out .onunfold-next {A = A} s)
      = go (unfold-next (out x′) {A = A} s)
           (unfold-next (out Y′)
              {A = proj₁ (Functor.F₀ S (A , s))}
              (proj₂ (Functor.F₀ S (A , s))))
           (g .out .onunfold-next {A = A} s)
           (cong (λ z → unfold-next (out z)
                          {A = proj₁ (Functor.F₀ S (A , s))}
                          (proj₂ (Functor.F₀ S (A , s))))
                 e)
