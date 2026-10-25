------------------------------------------------------------------------
-- Functors between categories with object equivalence
--
-- Preserve object equivalence and commute with transport. Includes
-- composition and a constructor from ordinary functors via isomorphisms.
--
-- 带对象等价的范畴之间的函子
--
-- 保持对象等价并与传输交换。包括复合，以及经由同构从普通函子构造的
-- 构造器。
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --exact-split --guardedness --double-check #-}

module SketchPass.ObjEquivFunctor where

open import Agda.Primitive using (Level; _⊔_)
open import Categories.Category using (Category)
open import Categories.Functor using (Functor; _∘F_)

open import SketchPass.ObjEquivCat using (ObjEquivCat; objEquivCatFromIso)

-- ObjEquivFunctor: functor between categories with object equivalence
record ObjEquivFunctor {o ℓ e : Level} (C D : ObjEquivCat o ℓ e) : Set (o ⊔ ℓ ⊔ e) where
  private
    module C = ObjEquivCat C
    module D = ObjEquivCat D
  field
    baseFunctor : Functor C.cat D.cat
  module BF = Functor baseFunctor
  field
    ≈ₒ-homo : ∀ {A B : Category.Obj C.cat}
            → A C.≈ₒ B → BF.₀ A D.≈ₒ BF.₀ B
    transport-comm : ∀ {A₁ A₂ B₁ B₂ : Category.Obj C.cat}
                     (eqA : A₁ C.≈ₒ A₂) (eqB : B₁ C.≈ₒ B₂)
                     {f : Category._⇒_ C.cat A₁ B₁}
                   → Category._≈_ D.cat
                       (D.transport (≈ₒ-homo eqA) (≈ₒ-homo eqB) (BF.₁ f))
                       (BF.₁ (C.transport eqA eqB f))

-- Identity ObjEquivFunctor
idObjEquivFunctor : ∀ {o ℓ e} {C : ObjEquivCat o ℓ e} → ObjEquivFunctor C C
idObjEquivFunctor {C = C} = record
  { baseFunctor    = record
    { F₀           = λ x → x
    ; F₁           = λ f → f
    ; identity     = Cat.Equiv.refl
    ; homomorphism = Cat.Equiv.refl
    ; F-resp-≈     = λ eq → eq
    }
  ; ≈ₒ-homo        = λ eq → eq
  ; transport-comm = λ eqA eqB {f} → OE.transport-resp-≈ eqA eqB (Cat.Equiv.refl {x = f})
  }
  where
    module OE  = ObjEquivCat C
    module Cat = Category OE.cat

-- Composition of ObjEquivFunctors
compObjEquivFunctor : ∀ {o ℓ e} {C D E : ObjEquivCat o ℓ e}
  → ObjEquivFunctor D E → ObjEquivFunctor C D → ObjEquivFunctor C E
compObjEquivFunctor {C = C} {D} {E} G F = record
  { baseFunctor    = G.baseFunctor ∘F F.baseFunctor
  ; ≈ₒ-homo        = λ eq → G.≈ₒ-homo (F.≈ₒ-homo eq)
  ; transport-comm = λ eqA eqB {f} →
      let
        module EC = Category (ObjEquivCat.cat E)
        open EC
        open Equiv
      in
      trans
        (G.transport-comm (F.≈ₒ-homo eqA) (F.≈ₒ-homo eqB) {f = F.BF.₁ f})
        (Functor.F-resp-≈ G.baseFunctor (F.transport-comm eqA eqB {f = f}))
  }
  where
    module F = ObjEquivFunctor F
    module G = ObjEquivFunctor G

-- Constructor from an ordinary functor (using isomorphisms as object equivalence)
module _ {o ℓ e : Level} {C D : Category o ℓ e} (F : Functor C D) where
  private
    module C = Category C
    module D = Category D
    module F = Functor F
    import Categories.Morphism C as MC
    import Categories.Morphism D as MD
    CE = objEquivCatFromIso C
    DE = objEquivCatFromIso D
  -- Functor F lifts isomorphisms in C to isomorphisms in D
  F-iso : ∀ {A B} → A MC.≅ B → F.₀ A MD.≅ F.₀ B
  F-iso i = record
    { from = F.₁ from
    ; to   = F.₁ to
    ; iso  = record
      { isoˡ = trans (D.Equiv.sym F.homomorphism) (trans (F.F-resp-≈ isoˡ) F.identity)
      ; isoʳ = trans (D.Equiv.sym F.homomorphism) (trans (F.F-resp-≈ isoʳ) F.identity)
      }
    }
    where
      open MC._≅_ i
      open D.Equiv

  -- Main constructor
  objEquivFunctorFromIso : ObjEquivFunctor CE DE
  objEquivFunctorFromIso = record
    { baseFunctor    = F
    ; ≈ₒ-homo        = F-iso
    ; transport-comm = λ eqA eqB {f} →
        let
          open MC._≅_ eqA renaming (to to toA)
          open MC._≅_ eqB renaming (from to fromB)
          open D
          open HomReasoning
          open Equiv
        in begin
          F.₁ fromB ∘ F.₁ f ∘ F.₁ toA   ≈⟨ sym assoc ⟩
          (F.₁ fromB ∘ F.₁ f) ∘ F.₁ toA ≈⟨ ∘-resp-≈ˡ (sym F.homomorphism) ⟩
          F.₁ (fromB C.∘ f) ∘ F.₁ toA   ≈⟨ sym F.homomorphism ⟩
          F.₁ ((fromB C.∘ f) C.∘ toA)    ≈⟨ F.F-resp-≈ C.assoc ⟩
          F.₁ (fromB C.∘ f C.∘ toA)      ∎
    }
