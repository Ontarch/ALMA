------------------------------------------------------------------------
-- Lemmas for ContCatEquiv: onPos-subst and composite naturality shape
--
-- Provides onPos-subst-comm (onPos commutes with shape substitution)
-- and comp-nat-shape-eq (shape extraction for composite naturality)
------------------------------------------------------------------------
{-# OPTIONS --safe --cubical-compatible --exact-split --guardedness --double-check #-}
module SketchPass.ContCatEquivLemmas where

open import Agda.Primitive using (lsuc)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂; subst; trans-reflʳ; module ≡-Reasoning)
open import Data.Container.Core using (shape)
open import Data.Container.Morphism using (_∘_)
open import Categories.Category using (Category)
open import Categories.Functor using (Functor)

open import SketchPass.ContCategory using (≈M-sym; ≈M-trans; ∘M-assoc; ∘M-resp-≈ˡ; ∘M-resp-≈ʳ)
open import SketchPass.ObjEquivCat using (ObjEquivCat)
open import SketchPass.ObjEquivFunctor using (ObjEquivFunctor)
open import SketchPass.ContCatEquiv using (ContCatEquiv)
open import SketchPass.ContCatEquivFunctor using (ContCatEquivFunctor; compContCatEquivFunctor)
open import SketchPass.Unfolding using (Unfolding)
open import SketchPass.MorphismObject using (MorphismObject)
open import SketchPass.ContCategoryLemmas
  using (shape-eq-from-≈M; ShapeOf; PosOf; shape-eq-sym; shape-eq-trans; shape-eq-assoc; shape-eq-resp-ˡ; shape-eq-resp-ʳ)

onPos-subst-comm :
  ∀ {ℓ} {F G : ContCatEquiv ℓ} {CF : ContCatEquivFunctor F G}
  {X Y : Set (lsuc (lsuc ℓ))} {UF : Unfolding ℓ F X} {UG : Unfolding ℓ G Y}
  (MO : MorphismObject CF UF UG)
  {A : Category.Obj (ObjEquivCat.cat (ContCatEquiv.base F))}
  {s₁ s₂ : ShapeOf (ContCatEquiv.containerFunctor F) A}
  (eq : s₁ ≡ s₂)
  (p : PosOf (ContCatEquiv.containerFunctor F) s₁)
  → MorphismObject.onPos MO (subst (PosOf (ContCatEquiv.containerFunctor F)) eq p)
    ≡ subst (PosOf (ContCatEquiv.containerFunctor G))
            (cong (shape (ContCatEquivFunctor.containerNat CF)) eq)
            (MorphismObject.onPos MO p)
onPos-subst-comm MO refl p = refl

comp-nat-shape-eq :
  ∀ {ℓ} {F G H : ContCatEquiv ℓ}
  (g : ContCatEquivFunctor G H) (f : ContCatEquivFunctor F G)
  {A B : Category.Obj (ObjEquivCat.cat (ContCatEquiv.base F))}
  (h : Category._⇒_ (ObjEquivCat.cat (ContCatEquiv.base F)) A B)
  (s : ShapeOf (ContCatEquiv.containerFunctor F) A)
  → shape-eq-from-≈M (ContCatEquivFunctor.natural (compContCatEquivFunctor g f) h) s
    ≡ trans
        (cong (shape (ContCatEquivFunctor.containerNat g))
              (shape-eq-from-≈M (ContCatEquivFunctor.natural f h) s))
        (shape-eq-from-≈M
          (ContCatEquivFunctor.natural g
            (Functor.₁ (ObjEquivFunctor.baseFunctor (ContCatEquivFunctor.objEquivFunctor f)) h))
          (shape (ContCatEquivFunctor.containerNat f) s))
comp-nat-shape-eq {F = F} {G} {H} g f {A} {B} h s =
  let
    open ≡-Reasoning
    module FCE = ContCatEquiv F
    module GCE = ContCatEquiv G
    module HCE = ContCatEquiv H
    module fCF = ContCatEquivFunctor f
    module gCF = ContCatEquivFunctor g
    fctr = FCE.containerFunctor
    gctr = GCE.containerFunctor
    hctr = HCE.containerFunctor
    fobj = ObjEquivFunctor.baseFunctor fCF.objEquivFunctor
    gobj = ObjEquivFunctor.baseFunctor gCF.objEquivFunctor
    module fobj = Functor fobj
    module gobj = Functor gobj
    module fctr = Functor fctr
    module gctr = Functor gctr
    module hctr = Functor hctr
    fN-A = fCF.containerNat {A}
    fN-B = fCF.containerNat {B}
    gN-fA = gCF.containerNat {fobj.₀ A}
    gN-fB = gCF.containerNat {fobj.₀ B}
    Fh = fctr.₁ h
    Gfh = gctr.₁ (fobj.₁ h)
    Hgfh = hctr.₁ (gobj.₁ (fobj.₁ h))
    s1 = ∘M-assoc {f = Fh} {g = fN-B} {h = gN-fB}
    s2 = ∘M-resp-≈ʳ {g = gN-fB} (fCF.natural h)
    s3 = ≈M-sym (∘M-assoc {f = fN-A} {g = Gfh} {h = gN-fB})
    s4 = ∘M-resp-≈ˡ {f = fN-A} (gCF.natural (fobj.₁ h))
    s5 = ∘M-assoc {f = fN-A} {g = gN-fA} {h = Hgfh}
    full = ≈M-trans s1 (≈M-trans s2 (≈M-trans s3 (≈M-trans s4 s5)))
  in
  begin
    shape-eq-from-≈M (ContCatEquivFunctor.natural (compContCatEquivFunctor g f) h) s
      ≡⟨ shape-eq-trans s1 (≈M-trans s2 (≈M-trans s3 (≈M-trans s4 s5))) s ⟩
    trans (shape-eq-from-≈M s1 s)
      (shape-eq-from-≈M (≈M-trans s2 (≈M-trans s3 (≈M-trans s4 s5))) s)
      ≡⟨ cong₂ trans
           (shape-eq-assoc {A = fctr.₀ A} {B = fctr.₀ B} {C = gctr.₀ (fobj.₀ B)} {D = hctr.₀ (gobj.₀ (fobj.₀ B))}
                           {f = Fh} {g = fN-B} {h = gN-fB} s)
           refl ⟩
    trans refl
      (shape-eq-from-≈M (≈M-trans s2 (≈M-trans s3 (≈M-trans s4 s5))) s)
      ≡⟨ shape-eq-trans s2 (≈M-trans s3 (≈M-trans s4 s5)) s ⟩
    trans (shape-eq-from-≈M s2 s)
      (shape-eq-from-≈M (≈M-trans s3 (≈M-trans s4 s5)) s)
      ≡⟨ cong₂ trans
           (shape-eq-resp-ʳ {g = gN-fB} (fCF.natural h) s)
           (shape-eq-trans s3 (≈M-trans s4 s5) s) ⟩
    trans (cong (shape gN-fB) (shape-eq-from-≈M (fCF.natural h) s))
      (trans (shape-eq-from-≈M s3 s)
        (shape-eq-from-≈M (≈M-trans s4 s5) s))
      ≡⟨ cong (λ x → trans (cong (shape gN-fB) (shape-eq-from-≈M (fCF.natural h) s))
                          (trans x (shape-eq-from-≈M (≈M-trans s4 s5) s)))
           (begin
             shape-eq-from-≈M s3 s
               ≡⟨ shape-eq-sym (∘M-assoc {f = fN-A} {g = Gfh} {h = gN-fB}) s ⟩
             sym (shape-eq-from-≈M (∘M-assoc {f = fN-A} {g = Gfh} {h = gN-fB}) s)
               ≡⟨ cong sym (shape-eq-assoc {A = fctr.₀ A} {B = gctr.₀ (fobj.₀ A)}
                                            {C = gctr.₀ (fobj.₀ B)} {D = hctr.₀ (gobj.₀ (fobj.₀ B))}
                                            {f = fN-A} {g = Gfh} {h = gN-fB} s) ⟩
             refl
           ∎) ⟩
    trans (cong (shape gN-fB) (shape-eq-from-≈M (fCF.natural h) s))
      (trans refl (shape-eq-from-≈M (≈M-trans s4 s5) s))
      ≡⟨ cong (trans (cong (shape gN-fB) (shape-eq-from-≈M (fCF.natural h) s)))
           (shape-eq-trans s4 s5 s) ⟩
    trans (cong (shape gN-fB) (shape-eq-from-≈M (fCF.natural h) s))
      (trans (shape-eq-from-≈M s4 s) (shape-eq-from-≈M s5 s))
      ≡⟨ cong (λ x → trans (cong (shape gN-fB) (shape-eq-from-≈M (fCF.natural h) s))
                          (trans (shape-eq-from-≈M s4 s) x))
           (shape-eq-assoc {A = fctr.₀ A} {B = gctr.₀ (fobj.₀ A)}
                           {C = hctr.₀ (gobj.₀ (fobj.₀ A))} {D = hctr.₀ (gobj.₀ (fobj.₀ B))}
                           {f = fN-A} {g = gN-fA} {h = Hgfh} s) ⟩
    trans (cong (shape gN-fB) (shape-eq-from-≈M (fCF.natural h) s))
      (trans (shape-eq-from-≈M s4 s) refl)
      ≡⟨ cong (trans (cong (shape gN-fB) (shape-eq-from-≈M (fCF.natural h) s)))
           (trans-reflʳ (shape-eq-from-≈M s4 s)) ⟩
    trans (cong (shape gN-fB) (shape-eq-from-≈M (fCF.natural h) s))
      (shape-eq-from-≈M s4 s)
      ≡⟨ cong (trans (cong (shape gN-fB) (shape-eq-from-≈M (fCF.natural h) s)))
           (shape-eq-resp-ˡ {A = fctr.₀ A} {B = gctr.₀ (fobj.₀ A)} {C = hctr.₀ (gobj.₀ (fobj.₀ B))}
                            {g₁ = gN-fB ∘ Gfh} {g₂ = Hgfh ∘ gN-fA} {f = fN-A}
                            (gCF.natural (fobj.₁ h)) s) ⟩
    trans (cong (shape gN-fB) (shape-eq-from-≈M (fCF.natural h) s))
      (shape-eq-from-≈M (gCF.natural (fobj.₁ h)) (shape fN-A s))
  ∎
