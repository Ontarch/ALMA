------------------------------------------------------------------------
-- MorphismMorphism: compatibility of position maps with hom-actions
--
-- onActP : onPos commutes with the container position maps actPOf,
--          modulo the shape transport induced by the naturality of CF
------------------------------------------------------------------------
{-# OPTIONS --safe --cubical-compatible --exact-split --guardedness --double-check #-}

module InitialPass.MorphismMorphism where

open import Agda.Primitive using (Level; lsuc)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; subst; subst-subst; module ≡-Reasoning)
open import Data.Container.Core using (shape)
open import Categories.Category using (Category)
open import Categories.Functor using (Functor)

open import InitialPass.ObjEquivCat using (ObjEquivCat)
open import InitialPass.ObjEquivFunctor using (ObjEquivFunctor)
open import InitialPass.ContCatEquiv using (ContCatEquiv)
open import InitialPass.ContCatEquivFunctor using (ContCatEquivFunctor; compContCatEquivFunctor)
open import InitialPass.ContCategoryLemmas
  using (shape-eq-from-≈M; ShapeOf; PosOf; actSOf; actPOf)
open import InitialPass.Unfolding using (Unfolding)
open import InitialPass.MorphismObject
  using (MorphismObject; idMorphismObject; compMorphismObject)
open import InitialPass.ContCatEquivLemmas using (onPos-subst-comm; comp-nat-shape-eq)

record MorphismMorphism {ℓ : Level}
  {CEF CEG : ContCatEquiv ℓ}
  {CF : ContCatEquivFunctor CEF CEG}
  {X Y : Set (lsuc (lsuc ℓ))}
  {UF : Unfolding ℓ CEF X}
  {UG : Unfolding ℓ CEG Y}
  (MO : MorphismObject CF UF UG)
  : Set (lsuc ℓ) where
  private
    module CEF      = ContCatEquiv CEF
    module CEG      = ContCatEquiv CEG
    module CFstruct = ContCatEquivFunctor CF
    module CFobj    = ObjEquivFunctor CFstruct.objEquivFunctor
    module BF       = Functor CFobj.baseFunctor
    open Unfolding UF renaming (unfoldFunctor to UF-functor)
    open Unfolding UG renaming (unfoldFunctor to UG-functor)
    module UF = Functor UF-functor
    module UG = Functor UG-functor
    module MO       = MorphismObject MO
    module CatF     = Category (ObjEquivCat.cat CEF.base)
    module CatG     = Category (ObjEquivCat.cat CEG.base)
  field
    -- onPos ∘ actPOf(f) ≡ actPOf(BF.₁ f) ∘ onPos (via shape transport)
    onActP : ∀ {A B} (f : CatF._⇒_ A B) (s : ShapeOf CEF.containerFunctor A)
           → (p : PosOf CEF.containerFunctor (actSOf CEF.containerFunctor f s))
           → MO.onPos (actPOf CEF.containerFunctor f s p)
             ≡ actPOf CEG.containerFunctor (BF.₁ f) (shape CFstruct.containerNat s)
                 (subst (PosOf CEG.containerFunctor)
                        (shape-eq-from-≈M (CFstruct.natural f) s)
                        (MO.onPos p))

-- Identity MorphismMorphism
module _ {ℓ : Level}
  {CE : ContCatEquiv ℓ}
  {X : Set (lsuc (lsuc ℓ))}
  {UF : Unfolding ℓ CE X}
  where
  idMorphismMorphism : MorphismMorphism (idMorphismObject {UF = UF})
  idMorphismMorphism = record
    { onActP = λ f s p → refl
    }

-- Composition of MorphismMorphisms
module _ {ℓ : Level}
  {CEF CEG CEH : ContCatEquiv ℓ}
  {CF : ContCatEquivFunctor CEF CEG}
  {CG : ContCatEquivFunctor CEG CEH}
  {X Y Z : Set (lsuc (lsuc ℓ))}
  {UF : Unfolding ℓ CEF X}
  {UG : Unfolding ℓ CEG Y}
  {UH : Unfolding ℓ CEH Z}
  where
  private
    module CEF = ContCatEquiv CEF
    module CEG = ContCatEquiv CEG
    module CEH = ContCatEquiv CEH
    module CF = ContCatEquivFunctor CF
    module CG = ContCatEquivFunctor CG
    compCF = compContCatEquivFunctor CG CF
    module compCF = ContCatEquivFunctor compCF
    module BFf = Functor (ObjEquivFunctor.baseFunctor CF.objEquivFunctor)
    module BFg = Functor (ObjEquivFunctor.baseFunctor CG.objEquivFunctor)
    Fctr = CEF.containerFunctor
    Gctr = CEG.containerFunctor
    Hctr = CEH.containerFunctor
  compMorphismMorphism :
      {MOg : MorphismObject CG UG UH}
      {MOf : MorphismObject CF UF UG}
      (MMg : MorphismMorphism MOg)
      (MMf : MorphismMorphism MOf)
      → MorphismMorphism (compMorphismObject MOg MOf)
  compMorphismMorphism {MOg = MOg} {MOf} MMg MMf = record
    { onActP = λ {A B} f s p →
        let
          module MOg = MorphismObject MOg
          module MOf = MorphismObject MOf
          module MMf = MorphismMorphism MMf
          module MMg = MorphismMorphism MMg
          open ≡-Reasoning
          f' = BFf.₁ f
          s' = shape CF.containerNat s
          eq-f = shape-eq-from-≈M (CF.natural f) s
          eq-g = shape-eq-from-≈M (CG.natural f') s'
          eq-comp = shape-eq-from-≈M (compCF.natural f) s
          x = MOg.onPos (MOf.onPos p)
        in begin
          MOg.onPos (MOf.onPos (actPOf Fctr f s p))
            ≡⟨ cong MOg.onPos (MMf.onActP f s p) ⟩
          MOg.onPos (actPOf Gctr (BFf.₁ f) (shape CF.containerNat s)
                    (subst (PosOf Gctr) eq-f (MOf.onPos p)))
            ≡⟨ MMg.onActP f' s' (subst (PosOf Gctr) eq-f (MOf.onPos p)) ⟩
          actPOf Hctr (BFg.₁ f') (shape CG.containerNat s')
            (subst (PosOf Hctr) eq-g
              (MOg.onPos (subst (PosOf Gctr) eq-f (MOf.onPos p))))
            ≡⟨ cong (λ y → actPOf Hctr (BFg.₁ f') (shape CG.containerNat s')
                            (subst (PosOf Hctr) eq-g y))
                    (onPos-subst-comm MOg eq-f (MOf.onPos p)) ⟩
          actPOf Hctr (BFg.₁ f') (shape CG.containerNat s')
            (subst (PosOf Hctr) eq-g
              (subst (PosOf Hctr) (cong (shape CG.containerNat) eq-f) x))
            ≡⟨ cong (actPOf Hctr (BFg.₁ f') (shape CG.containerNat s'))
                    (subst-subst (cong (shape CG.containerNat) eq-f) {y≡z = eq-g}) ⟩
          actPOf Hctr (BFg.₁ f') (shape CG.containerNat s')
            (subst (PosOf Hctr) (trans (cong (shape CG.containerNat) eq-f) eq-g) x)
            ≡⟨ cong (λ e → actPOf Hctr (BFg.₁ f') (shape CG.containerNat s')
                            (subst (PosOf Hctr) e x))
                    (sym (comp-nat-shape-eq CG CF f s)) ⟩
          actPOf Hctr (BFg.₁ f') (shape CG.containerNat s')
            (subst (PosOf Hctr) eq-comp x)
        ∎
    }
