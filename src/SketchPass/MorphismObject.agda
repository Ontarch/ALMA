------------------------------------------------------------------------
-- Object-level homomorphisms between unfolding systems
--
-- A MorphismObject witnesses the commutation of object/position mappings
-- with the container natural transformation, up to object equivalence
------------------------------------------------------------------------
{-# OPTIONS --safe --cubical-compatible --exact-split --guardedness --double-check #-}

module SketchPass.MorphismObject where

open import Agda.Primitive using (Level; lsuc)
open import Relation.Binary.Structures using (IsEquivalence)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; module ≡-Reasoning)
open import Data.Product using (_,_)
open import Data.Container.Core using (shape)
open import Categories.Functor using (Functor)

open import SketchPass.ContCategory using (_≈M_)
open import SketchPass.ObjEquivCat using (ObjEquivCat)
open import SketchPass.ContCatEquiv using (ContCatEquiv)
open import SketchPass.ObjEquivFunctor using (ObjEquivFunctor)
open import SketchPass.ContCatEquivFunctor
  using (ContCatEquivFunctor; idContCatEquivFunctor; compContCatEquivFunctor)
open import SketchPass.Unfolding using (Unfolding)
open import SketchPass.ContCategoryLemmas using (shape-eq-from-≈M; ShapeOf; PosOf)

record MorphismObject {ℓ : Level}
  {CEF CEG : ContCatEquiv ℓ}
  (CF : ContCatEquivFunctor CEF CEG)
  {X Y : Set (lsuc (lsuc ℓ))}
  (UF : Unfolding ℓ CEF X)
  (UG : Unfolding ℓ CEG Y)
  : Set (lsuc ℓ) where
  private
    open ContCatEquiv CEF renaming (containerFunctor to Fctr)
    open ContCatEquiv CEG renaming (containerFunctor to Gctr; transportContainer to Gtrans)
    open ObjEquivCat (ContCatEquiv.base CEG) using (_≈ₒ_)
    module CFstruct = ContCatEquivFunctor CF
    module CFobj = ObjEquivFunctor CFstruct.objEquivFunctor
    module CFbase = Functor CFobj.baseFunctor using (₀)
    open Unfolding UF renaming (unfoldFunctor to UF-functor; pos-to-shape to UF-pos-to-shape)
    open Unfolding UG renaming (unfoldFunctor to UG-functor; pos-to-shape to UG-pos-to-shape)
    module UF = Functor UF-functor
    module UG = Functor UG-functor
  field
    onPos : ∀ {A} {s : ShapeOf Fctr A}
          → PosOf Fctr s
          → PosOf Gctr (shape CFstruct.containerNat s)
    onunfold-obj : ∀ {A} (s : ShapeOf Fctr A)
                 → CFbase.₀ (UF.₀ (A , s)) ≈ₒ
                   UG.₀ (CFbase.₀ A , shape CFstruct.containerNat s)
    onPos-to-shape : ∀ {A} {s : ShapeOf Fctr A} (p : PosOf Fctr s)
                   → shape (Gtrans (onunfold-obj s))
                           (shape (CFstruct.containerNat {UF.₀ (A , s)}) (UF-pos-to-shape s p))
                     ≡ UG-pos-to-shape (shape CFstruct.containerNat s) (onPos p)

-- Identity MorphismObject
idMorphismObject : ∀ {ℓ : Level}
  {CE : ContCatEquiv ℓ}
  {X : Set (lsuc (lsuc ℓ))}
  {UF : Unfolding ℓ CE X}
  → MorphismObject (idContCatEquivFunctor CE) UF UF
idMorphismObject {CE = CE} {UF = UF} = record
  { onPos         = λ p → p
  ; onunfold-obj  = λ s → IsEquivalence.refl (ObjEquivCat.≈ₒ-isEquiv (ContCatEquiv.base CE))
  ; onPos-to-shape = λ {A} {s = s} p →
      let
        module CE = ContCatEquiv CE
        open Unfolding UF
        trans-refl : CE.transportContainer
                       (IsEquivalence.refl (ObjEquivCat.≈ₒ-isEquiv (ContCatEquiv.base CE)))
                     ≈M _
        trans-refl = CE.transportContainer-refl
                       {A = Functor.₀ unfoldFunctor (A , s)}
      in
      _≈M_.shape-eq trans-refl (pos-to-shape s p)
  }

-- Composition of MorphismObjects
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
    module OEH = ObjEquivCat CEH.base
  compMorphismObject :
    (MOg : MorphismObject CG UG UH)
    (MOf : MorphismObject CF UF UG)
    → MorphismObject compCF UF UH
  compMorphismObject MOg MOf = record
    { onPos = λ p → onPos-g (onPos-f p)
    ; onunfold-obj = λ {A} s →
        IsEquivalence.trans OEH.≈ₒ-isEquiv
          (ObjEquivFunctor.≈ₒ-homo CG.objEquivFunctor (onunfold-obj-f s))
          (onunfold-obj-g (shape CF.containerNat s))
    ; onPos-to-shape = λ {A} {s} p →
        let
          module CGfun = ContCatEquivFunctor CG
          open Unfolding UF renaming (pos-to-shape to psF)
          open Unfolding UG renaming (pos-to-shape to psG)
          open Unfolding UH renaming (pos-to-shape to psH)
          s' = shape CF.containerNat s
          eqf = onunfold-obj-f s
          eqg = onunfold-obj-g s'
          eq1 = ObjEquivFunctor.≈ₒ-homo CGfun.objEquivFunctor eqf
          eq-comp = IsEquivalence.trans OEH.≈ₒ-isEquiv eq1 eqg
          y = shape CF.containerNat (psF s p)
          x = shape CGfun.containerNat y
          open ≡-Reasoning
        in begin
          shape (CEH.transportContainer eq-comp) (shape compCF.containerNat (psF s p))
            ≡⟨⟩
          shape (CEH.transportContainer eq-comp) x
            ≡⟨ shape-eq-from-≈M (CEH.transportContainer-trans eq1 eqg) x ⟩
          shape (CEH.transportContainer eqg) (shape (CEH.transportContainer eq1) x)
            ≡⟨ cong (shape (CEH.transportContainer eqg))
                    (sym (shape-eq-from-≈M (CGfun.transport-nat eqf) y)) ⟩
          shape (CEH.transportContainer eqg) (shape CGfun.containerNat (shape (CEG.transportContainer eqf) y))
            ≡⟨ cong (shape (CEH.transportContainer eqg))
                    (cong (shape CGfun.containerNat) (onPos-to-shape-f p)) ⟩
          shape (CEH.transportContainer eqg) (shape CGfun.containerNat (psG s' (onPos-f p)))
            ≡⟨ onPos-to-shape-g (onPos-f p) ⟩
          psH (shape CGfun.containerNat s') (onPos-g (onPos-f p))
            ≡⟨⟩
          psH (shape compCF.containerNat s) (onPos-g (onPos-f p))
        ∎
    }
    where
      open MorphismObject MOg renaming (onPos to onPos-g; onunfold-obj to onunfold-obj-g; onPos-to-shape to onPos-to-shape-g)
      open MorphismObject MOf renaming (onPos to onPos-f; onunfold-obj to onunfold-obj-f; onPos-to-shape to onPos-to-shape-f)
