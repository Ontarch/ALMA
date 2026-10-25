------------------------------------------------------------------------
-- Morphism between ContCatEquiv instances
--
-- Combines an ObjEquivFunctor with a container natural transformation.
-- contCatEquivFunctorFromIso: constructor using
-- objEquivFunctorFromIso plus a natural transformation.
--
-- ContCatEquiv 实例间的态射
--
-- 将 ObjEquivFunctor 与容器自然变换组合起来。
-- contCatEquivFunctorFromIso：使用 objEquivFunctorFromIso 加一个自然
-- 变换的构造器。
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --exact-split --guardedness --double-check #-}

module SketchPass.ContCatEquivFunctor where

open import Agda.Primitive using (Level; lsuc)
open import Data.Container.Core using (_⇒_)
open import Data.Container.Morphism using (id; _∘_)
open import Categories.Category using (Category)
open import Categories.Functor  using (Functor)

open import SketchPass.ContCategory
  using (_≈M_; ≈M-refl; ≈M-sym; ∘M-assoc; ∘M-resp-≈ˡ; ∘M-resp-≈ʳ; ContCat; module ≈M-Reasoning)
open import SketchPass.ContCatEquiv using (ContCatEquiv; contCatEquivFromIso)
open import SketchPass.ObjEquivCat using (ObjEquivCat)
open import SketchPass.ObjEquivFunctor
  using (ObjEquivFunctor; compObjEquivFunctor; objEquivFunctorFromIso)

-- Functor between ContCatEquiv instances: preserves object equivalences and container structure
record ContCatEquivFunctor {ℓ : Level} (F G : ContCatEquiv ℓ) : Set (lsuc ℓ) where
  private
    module FC = ObjEquivCat (ContCatEquiv.base F)
    module F  = ContCatEquiv F
    module G  = ContCatEquiv G
  field
    -- Underlying functor preserving object equivalences
    objEquivFunctor : ObjEquivFunctor F.base G.base
  open ObjEquivFunctor objEquivFunctor
  field
    -- container natural transformation at A
    containerNat : ∀ {A : Category.Obj FC.cat}
                 → Functor.₀ F.containerFunctor A ⇒ Functor.₀ G.containerFunctor (BF.₀ A)
    -- naturality of containerNat with respect to morphisms
    natural : ∀ {A B : Category.Obj FC.cat}
              (f : Category._⇒_ FC.cat A B)
            → (containerNat ∘ Functor.₁ F.containerFunctor f) ≈M
              (Functor.₁ G.containerFunctor (BF.₁ f) ∘ containerNat)
    -- naturality of containerNat with respect to object-equivalence transport
    transport-nat : ∀ {A₁ A₂ : Category.Obj FC.cat}
                    (eqA : FC._≈ₒ_ A₁ A₂)
                  → (containerNat ∘ F.transportContainer eqA) ≈M
                    (G.transportContainer (≈ₒ-homo eqA) ∘ containerNat)

-- Identity ContCatEquivFunctor
idContCatEquivFunctor : ∀ {ℓ} (C : ContCatEquiv ℓ) → ContCatEquivFunctor C C
idContCatEquivFunctor C = record
  { objEquivFunctor = record
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
  ; containerNat     = λ {A} → id (Fctr.₀ A)
  ; natural          = λ f → ≈M-refl
  ; transport-nat    = λ eqA → ≈M-refl
  }
  where
    module C   = ContCatEquiv C
    module OE  = ObjEquivCat C.base
    module Cat = Category OE.cat
    module Fctr = Functor C.containerFunctor

-- Composition of ContCatEquivFunctors
compContCatEquivFunctor : ∀ {ℓ} {F G H : ContCatEquiv ℓ}
  → ContCatEquivFunctor G H → ContCatEquivFunctor F G → ContCatEquivFunctor F H
compContCatEquivFunctor {ℓ} {F} {G} {H} g f = record
  { objEquivFunctor = compObjEquivFunctor g.objEquivFunctor f.objEquivFunctor
  ; containerNat    = λ {A} → g.containerNat {fobj.₀ A} ∘ f.containerNat {A}
  ; natural         = λ {A B} h → natural-proof {A} {B} h
  ; transport-nat   = λ {A₁ A₂} eqA → transport-nat-proof {A₁} {A₂} eqA
  }
  where
    module F = ContCatEquiv F
    module G = ContCatEquiv G
    module H = ContCatEquiv H
    module f = ContCatEquivFunctor f
    module g = ContCatEquivFunctor g
    fctr = F.containerFunctor
    gctr = G.containerFunctor
    hctr = H.containerFunctor
    fobj = ObjEquivFunctor.baseFunctor f.objEquivFunctor
    gobj = ObjEquivFunctor.baseFunctor g.objEquivFunctor
    module fobj = Functor fobj
    module gobj = Functor gobj
    module fctr = Functor fctr
    module gctr = Functor gctr
    module hctr = Functor hctr
    open ≈M-Reasoning
    natural-proof : ∀ {A B} (h : Category._⇒_ (ObjEquivCat.cat F.base) A B) → _
    natural-proof {A} {B} h = begin
      (g.containerNat {fobj.₀ B} ∘ f.containerNat {B}) ∘ fctr.₁ h
        ≈⟨ ∘M-assoc {f = fctr.₁ h} {g = f.containerNat {B}} {h = g.containerNat {fobj.₀ B}} ⟩
      g.containerNat {fobj.₀ B} ∘ (f.containerNat {B} ∘ fctr.₁ h)
        ≈⟨ ∘M-resp-≈ʳ {g = g.containerNat {fobj.₀ B}} (f.natural h) ⟩
      g.containerNat {fobj.₀ B} ∘ (gctr.₁ (fobj.₁ h) ∘ f.containerNat {A})
        ≈⟨ ≈M-sym (∘M-assoc {f = f.containerNat {A}} {g = gctr.₁ (fobj.₁ h)} {h = g.containerNat {fobj.₀ B}}) ⟩
      (g.containerNat {fobj.₀ B} ∘ gctr.₁ (fobj.₁ h)) ∘ f.containerNat {A}
        ≈⟨ ∘M-resp-≈ˡ {f = f.containerNat {A}} (g.natural (fobj.₁ h)) ⟩
      (hctr.₁ (gobj.₁ (fobj.₁ h)) ∘ g.containerNat {fobj.₀ A}) ∘ f.containerNat {A}
        ≈⟨ ∘M-assoc {f = f.containerNat {A}} {g = g.containerNat {fobj.₀ A}} {h = hctr.₁ (gobj.₁ (fobj.₁ h))} ⟩
      hctr.₁ (gobj.₁ (fobj.₁ h)) ∘ (g.containerNat {fobj.₀ A} ∘ f.containerNat {A})
        ∎
    transport-nat-proof : ∀ {A₁ A₂} (eqA : ObjEquivCat._≈ₒ_ F.base A₁ A₂) → _
    transport-nat-proof {A₁} {A₂} eqA = begin
      (g.containerNat {fobj.₀ A₂} ∘ f.containerNat {A₂}) ∘ F.transportContainer eqA
        ≈⟨ ∘M-assoc {f = F.transportContainer eqA} {g = f.containerNat {A₂}} {h = g.containerNat {fobj.₀ A₂}} ⟩
      g.containerNat {fobj.₀ A₂} ∘ (f.containerNat {A₂} ∘ F.transportContainer eqA)
        ≈⟨ ∘M-resp-≈ʳ {g = g.containerNat {fobj.₀ A₂}} (f.transport-nat eqA) ⟩
      g.containerNat {fobj.₀ A₂} ∘ (G.transportContainer (≈ₒ-homo-f eqA) ∘ f.containerNat {A₁})
        ≈⟨ ≈M-sym (∘M-assoc {f = f.containerNat {A₁}} {g = G.transportContainer (≈ₒ-homo-f eqA)} {h = g.containerNat {fobj.₀ A₂}}) ⟩
      (g.containerNat {fobj.₀ A₂} ∘ G.transportContainer (≈ₒ-homo-f eqA)) ∘ f.containerNat {A₁}
        ≈⟨ ∘M-resp-≈ˡ {f = f.containerNat {A₁}} (g.transport-nat (≈ₒ-homo-f eqA)) ⟩
      (H.transportContainer (≈ₒ-homo-g (≈ₒ-homo-f eqA)) ∘ g.containerNat {fobj.₀ A₁}) ∘ f.containerNat {A₁}
        ≈⟨ ∘M-assoc {f = f.containerNat {A₁}} {g = g.containerNat {fobj.₀ A₁}} {h = H.transportContainer (≈ₒ-homo-g (≈ₒ-homo-f eqA))} ⟩
      H.transportContainer (≈ₒ-homo-g (≈ₒ-homo-f eqA)) ∘ (g.containerNat {fobj.₀ A₁} ∘ f.containerNat {A₁})
        ∎
      where
        ≈ₒ-homo-f = ObjEquivFunctor.≈ₒ-homo f.objEquivFunctor
        ≈ₒ-homo-g = ObjEquivFunctor.≈ₒ-homo g.objEquivFunctor

-- Constructor: functor + natural transformation → ContCatEquivFunctor
module _ {ℓ} {C D : Category (lsuc ℓ) (lsuc ℓ) (lsuc ℓ)}
         (F : Functor C D)
         (FC : Functor C (ContCat (lsuc ℓ) (lsuc ℓ)))
         (FD : Functor D (ContCat (lsuc ℓ) (lsuc ℓ)))
         (α : ∀ {A : Category.Obj C} → Functor.₀ FC A ⇒ Functor.₀ FD (Functor.₀ F A))
         (nat : ∀ {A B} (f : Category._⇒_ C A B)
              → (α ∘ Functor.₁ FC f) ≈M (Functor.₁ FD (Functor.₁ F f) ∘ α))
       where
  private
    import Categories.Morphism C as MC
    F-contEquiv = contCatEquivFromIso C FC
    G-contEquiv = contCatEquivFromIso D FD
    objEquivF  = objEquivFunctorFromIso {C = C} {D} F
  contCatEquivFunctorFromIso : ContCatEquivFunctor F-contEquiv G-contEquiv
  contCatEquivFunctorFromIso = record
    { objEquivFunctor = objEquivF
    ; containerNat    = α
    ; natural         = nat
    ; transport-nat   = λ eqA → nat (MC._≅_.from eqA)
    }
