------------------------------------------------------------------------
-- Unfolding Functor Record
--
-- Defines the unfolding functor for a cosmos layer, mapping shaped objects to
-- the base category with seeds for the next universe
------------------------------------------------------------------------
{-# OPTIONS --safe --cubical-compatible --exact-split --guardedness --double-check #-}

module SketchPass.Unfolding where

open import Agda.Primitive using (Level; lsuc; _⊔_)
open import Relation.Binary using (IsEquivalence; Reflexive; Symmetric; Transitive)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst; setoid)
open import Relation.Binary.Bundles using (Setoid)
open import Data.Product using (_,_)
open import Data.Container.Core using (Container)
open import Function using (Func; id; _∘_)
open import Categories.Category using (Category)
open import Categories.Category.Instance.Sets using (Sets)
open import Categories.Category.Construction.Elements using (Elements)
open import Categories.Functor using (Functor; _∘F_)

open import SketchPass.ContCategory using (ContCat)
open import SketchPass.ObjEquivCat using (ObjEquivCat)
open import SketchPass.ContCatEquiv using (ContCatEquiv)
open import SketchPass.ContCategoryLemmas
  using (shape-eq-from-≈M; ShapeOf; PosOf; actSOf; actPOf)

-- container-based unfolding system
record Unfolding (ℓ : Level) (CE : ContCatEquiv ℓ) (X : Set (lsuc (lsuc ℓ))) : Set (lsuc (lsuc ℓ)) where
  private
    module CE = ContCatEquiv CE
    module OE = ObjEquivCat CE.base
    open Category OE.cat renaming (_⇒_ to _⇒C_)
    ShapeForget : ∀ {s p} → Functor (ContCat s p) (Sets s)
    ShapeForget = record
      { F₀ = λ C → Container.Shape C
      ; F₁ = λ {C D} f → Data.Container.Core.shape f
      ; identity     = λ _ → refl
      ; homomorphism = λ {A B C} {f} {g} x → refl
      ; F-resp-≈     = λ {f g} f≈g → shape-eq-from-≈M f≈g
      }
    shapeFunctor : Functor OE.cat (Sets (lsuc ℓ))
    shapeFunctor = ShapeForget {s = lsuc ℓ} {p = lsuc ℓ} ∘F CE.containerFunctor
    ShapeCat : Category (lsuc ℓ ⊔ lsuc ℓ) (lsuc ℓ ⊔ lsuc ℓ) (lsuc ℓ)
    ShapeCat = Elements shapeFunctor
    open OE using (_≈ₒ_; ≈ₒ-isEquiv)
    ≡→≈ₒ : {X Y : Category.Obj OE.cat} → X ≡ Y → X ≈ₒ Y
    ≡→≈ₒ {X} eq = subst (X ≈ₒ_) eq (IsEquivalence.refl ≈ₒ-isEquiv)
  field
    unfoldFunctor : Functor ShapeCat OE.cat
    unfold-next : ∀ {A} → ShapeOf CE.containerFunctor A → X
    pos-to-shape : ∀ {A} (s : ShapeOf CE.containerFunctor A)
                 → PosOf CE.containerFunctor s
                 → ShapeOf CE.containerFunctor (Functor.₀ unfoldFunctor (A , s))
    pos-actS-compat : ∀ {A B} (f : A ⇒C B) (s : ShapeOf CE.containerFunctor A)
                    → (p : PosOf CE.containerFunctor (actSOf CE.containerFunctor f s))
                    → pos-to-shape (actSOf CE.containerFunctor f s) p
                      ≡ actSOf CE.containerFunctor
                          (Functor.₁ unfoldFunctor (f , refl))
                          (pos-to-shape s (actPOf CE.containerFunctor f s p))
    pos-to-shape-transport : ∀ {A} {s₁ s₂ : ShapeOf CE.containerFunctor A}
                           → (eq : s₁ ≡ s₂) {p : PosOf CE.containerFunctor s₁}
                           → Data.Container.Core.shape
                               ( CE.transportContainer
                                   (≡→≈ₒ (cong (λ s → Functor.₀ unfoldFunctor (A , s)) eq))
                               )
                               (pos-to-shape s₁ p)
                             ≡ pos-to-shape s₂ (subst (PosOf CE.containerFunctor) eq p)
open Unfolding

module UnfoldingFunctor where
  mapUnfolding : ∀ {ℓ} {CE : ContCatEquiv ℓ} {X Y : Set (lsuc (lsuc ℓ))}
                 (f : X → Y) → Unfolding ℓ CE X → Unfolding ℓ CE Y
  mapUnfolding f u = record
    { unfoldFunctor          = unfoldFunctor u
    ; unfold-next            = λ s → f (unfold-next u s)
    ; pos-to-shape           = pos-to-shape u
    ; pos-actS-compat        = pos-actS-compat u
    ; pos-to-shape-transport = pos-to-shape-transport u
    }
  mapUnfolding-id : ∀ {ℓ} {CE : ContCatEquiv ℓ} {X : Set (lsuc (lsuc ℓ))}
                    (u : Unfolding ℓ CE X) → mapUnfolding id u ≡ u
  mapUnfolding-id u = refl
  mapUnfolding-∘ : ∀ {ℓ} {CE : ContCatEquiv ℓ} {X Y Z : Set (lsuc (lsuc ℓ))}
                   {f : Y → Z} {g : X → Y} (u : Unfolding ℓ CE X)
                 → mapUnfolding (f ∘ g) u ≡ mapUnfolding f (mapUnfolding g u)
  mapUnfolding-∘ u = refl

module UnfoldingSetoid {ℓ : Level} {CE : ContCatEquiv ℓ} where
  open ContCatEquiv CE
  open Unfolding
  open UnfoldingFunctor
  private
    module OE = ObjEquivCat base
    open Category OE.cat renaming (_⇒_ to _⇒C_)
    ShapeForget : ∀ {s p} → Functor (ContCat s p) (Sets s)
    ShapeForget = record
      { F₀ = λ C → Container.Shape C
      ; F₁ = λ {C D} f → Data.Container.Core.shape f
      ; identity     = λ _ → refl
      ; homomorphism = λ {A B C} {f} {g} x → refl
      ; F-resp-≈     = λ {f g} f≈g → shape-eq-from-≈M f≈g
      }
    shapeFunctor : Functor OE.cat (Sets (lsuc ℓ))
    shapeFunctor = ShapeForget {s = lsuc ℓ} {p = lsuc ℓ} ∘F containerFunctor
    ShapeCat : Category (lsuc ℓ ⊔ lsuc ℓ) (lsuc ℓ ⊔ lsuc ℓ) (lsuc ℓ)
    ShapeCat = Elements shapeFunctor
  record _≈U_ (X : Setoid (lsuc (lsuc ℓ)) (lsuc (lsuc ℓ)))
              (u₁ u₂ : Unfolding ℓ CE (Setoid.Carrier X)) : Set (lsuc (lsuc ℓ)) where
    private
      module X = Setoid X
      module U₁ = Unfolding u₁
      module U₂ = Unfolding u₂
    field
      unfoldFunctor-eq : U₁.unfoldFunctor ≡ U₂.unfoldFunctor
      pos-to-shape-eq  : ∀ {A} (s : ShapeOf containerFunctor A) (p : PosOf containerFunctor s)
                       → subst (λ (F : Functor ShapeCat OE.cat)
                                  → ShapeOf containerFunctor (Functor.F₀ F (A , s)))
                               unfoldFunctor-eq
                               (U₁.pos-to-shape s p)
                       ≡ U₂.pos-to-shape s p
      unfold-next-eq   : ∀ {A} (s : ShapeOf containerFunctor A)
                       → X._≈_ (U₁.unfold-next s) (U₂.unfold-next s)
  ≈U-refl : {X : Setoid (lsuc (lsuc ℓ)) (lsuc (lsuc ℓ))} → Reflexive (_≈U_ X)
  ≈U-refl {X = X} = record
    { unfoldFunctor-eq = refl
    ; pos-to-shape-eq  = λ _ _ → refl
    ; unfold-next-eq   = λ _ → Setoid.refl X
    }
    where module X = Setoid X
  ≈U-sym : (X : Setoid (lsuc (lsuc ℓ)) (lsuc (lsuc ℓ))) → Symmetric (_≈U_ X)
  ≈U-sym X (record { unfoldFunctor-eq = refl ; pos-to-shape-eq = pts ; unfold-next-eq = un })
    = record
    { unfoldFunctor-eq = refl
    ; pos-to-shape-eq  = λ s p → sym (pts s p)
    ; unfold-next-eq   = λ s → Setoid.sym X (un s)
    }
    where module X = Setoid X
  ≈U-trans : (X : Setoid (lsuc (lsuc ℓ)) (lsuc (lsuc ℓ))) → Transitive (_≈U_ X)
  ≈U-trans X (record { unfoldFunctor-eq = refl ; pos-to-shape-eq = pts₁ ; unfold-next-eq = un₁ })
             (record { unfoldFunctor-eq = refl ; pos-to-shape-eq = pts₂ ; unfold-next-eq = un₂ })
    = record
    { unfoldFunctor-eq = refl
    ; pos-to-shape-eq  = λ s p → trans (pts₁ s p) (pts₂ s p)
    ; unfold-next-eq   = λ s → Setoid.trans X (un₁ s) (un₂ s)
    }
    where module X = Setoid X
  UnfoldingSetoid : Setoid (lsuc (lsuc ℓ)) (lsuc (lsuc ℓ))
                   → Setoid (lsuc (lsuc ℓ)) (lsuc (lsuc ℓ))
  UnfoldingSetoid X = record
    { Carrier       = Unfolding ℓ CE (Setoid.Carrier X)
    ; _≈_           = _≈U_ X
    ; isEquivalence = record
      { refl  = ≈U-refl
      ; sym   = ≈U-sym X
      ; trans = ≈U-trans X
      }
    }
  record SetoidFunc (A B : Setoid (lsuc (lsuc ℓ)) (lsuc (lsuc ℓ)))
                    : Set (lsuc (lsuc ℓ)) where
    private
      module A = Setoid A
      module B = Setoid B
    field
      _⟨$⟩_  : A.Carrier → B.Carrier
      resp-≈ : ∀ {x y} → A._≈_ x y → B._≈_ (_⟨$⟩_ x) (_⟨$⟩_ y)
  mapUnfolding-resp : (X Y : Setoid (lsuc (lsuc ℓ)) (lsuc (lsuc ℓ)))
                    → SetoidFunc X Y
                    → SetoidFunc (UnfoldingSetoid X) (UnfoldingSetoid Y)
  mapUnfolding-resp X Y f = record
    { _⟨$⟩_  = λ u → mapUnfolding (F._⟨$⟩_) u
    ; resp-≈ = λ {u₁ u₂} eq → helper eq
    }
    where
      module X = Setoid X
      module Y = Setoid Y
      module F = SetoidFunc f
      helper : {u₁ u₂ : Unfolding ℓ CE (Setoid.Carrier X)}
             → _≈U_ X u₁ u₂
             → _≈U_ Y (mapUnfolding (F._⟨$⟩_) u₁) (mapUnfolding (F._⟨$⟩_) u₂)
      helper (record { unfoldFunctor-eq = refl ; pos-to-shape-eq = pts ; unfold-next-eq = un })
        = record
        { unfoldFunctor-eq = refl
        ; pos-to-shape-eq  = λ s p → pts s p
        ; unfold-next-eq   = λ s → F.resp-≈ (un s)
        }

  mapUnfolding-Func : (X Y : Setoid (lsuc (lsuc ℓ)) (lsuc (lsuc ℓ)))
                    → Func X Y → Func (UnfoldingSetoid X) (UnfoldingSetoid Y)
  mapUnfolding-Func X Y f = record
    { to   = λ u → mapUnfolding (Func.to f) u
    ; cong = λ eq → SetoidFunc.resp-≈ sf eq
    }
    where
      sf : SetoidFunc (UnfoldingSetoid X) (UnfoldingSetoid Y)
      sf = mapUnfolding-resp X Y (record
        { _⟨$⟩_  = Func.to f
        ; resp-≈ = Func.cong f
        })

  mapUnfolding-resp-≈ :
    (A B : Set (lsuc (lsuc ℓ)))
    (f g : A → B)
    → (∀ {x} → f x ≡ g x)
    → {u₁ u₂ : Unfolding ℓ CE A}
    → _≈U_ (setoid A) u₁ u₂
    → _≈U_ (setoid B) (mapUnfolding f u₁) (mapUnfolding g u₂)
  mapUnfolding-resp-≈ A B f g f≈g {u₁} {u₂} u₁≈u₂ =
    let
      SA = setoid A
      SB = setoid B
      sf : SetoidFunc SA SB
      sf = record
        { _⟨$⟩_  = f
        ; resp-≈ = λ eq → cong f eq
        }
      module R = SetoidFunc (mapUnfolding-resp SA SB sf)
      fg-eq : _≈U_ SB (mapUnfolding f u₂) (mapUnfolding g u₂)
      fg-eq = record
        { unfoldFunctor-eq = refl
        ; pos-to-shape-eq  = λ s p → refl
        ; unfold-next-eq   = λ s → f≈g {unfold-next u₂ s}
        }
      module SBS = Setoid (UnfoldingSetoid SB)
    in SBS.trans (R.resp-≈ u₁≈u₂) fg-eq
