------------------------------------------------------------------------
-- Category with object equivalence and a container functor
--
-- Defines ContCatEquiv: an ObjEquivCat equipped with a functor to
-- the container category, and a transport of containers coherent
-- with the object equivalence.
--
-- 带对象等价与容器函子的范畴
--
-- 定义 ContCatEquiv：装备了到容器范畴的函子、以及与对象等价相干的
-- 容器传输的 ObjEquivCat。
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --exact-split --guardedness --double-check #-}

module SketchPass.ContCatEquiv where

open import Agda.Primitive using (Level; lsuc)
open import Relation.Binary using (IsEquivalence)
open import Data.Container.Core using (_⇒_)
open import Data.Container.Morphism using (id; _∘_)
open import Categories.Category using (Category)
open import Categories.Functor using (Functor)

open import SketchPass.ContCategory
  using (_≈M_; ≈M-sym; ≈M-trans; ∘M-assoc; ∘M-identityʳ; ∘M-resp-≈ˡ; ∘M-resp-≈ʳ; ContCat; module ≈M-Reasoning)
open import SketchPass.ObjEquivCat using (ObjEquivCat)

-- Functor from the base category to the category of containers
record ContCatEquiv (ℓ : Level) : Set (lsuc (lsuc ℓ)) where
  field
    base : ObjEquivCat (lsuc ℓ) (lsuc ℓ) (lsuc ℓ)
  open ObjEquivCat base
  field
    containerFunctor : Functor cat (ContCat (lsuc ℓ) (lsuc ℓ))
    transportContainer : ∀ {A₁ A₂}
                        → A₁ ≈ₒ A₂
                        → Functor.₀ containerFunctor A₁ ⇒ Functor.₀ containerFunctor A₂
    transportContainer-refl : ∀ {A}
                            → transportContainer (IsEquivalence.refl ≈ₒ-isEquiv) ≈M id (Functor.₀ containerFunctor A)
    transportContainer-trans : ∀ {A₁ A₂ A₃}
                              → (eq1 : A₁ ≈ₒ A₂) (eq2 : A₂ ≈ₒ A₃)
                              → transportContainer (IsEquivalence.trans ≈ₒ-isEquiv eq1 eq2)
                                ≈M (transportContainer eq2 ∘ transportContainer eq1)
    act-natural : ∀ {A₁ A₂ B₁ B₂}
                → (eqA : A₁ ≈ₒ A₂) (eqB : B₁ ≈ₒ B₂)
                → (f : Category._⇒_ cat A₁ B₁)
                → (transportContainer eqB ∘ Functor.₁ containerFunctor f)
                  ≈M
                  (Functor.₁ containerFunctor (transport eqA eqB f) ∘ transportContainer eqA)

module _ {ℓ : Level}
         (C : Category (lsuc ℓ) (lsuc ℓ) (lsuc ℓ))
         (F : Functor C (ContCat (lsuc ℓ) (lsuc ℓ))) where
  private
    module C = Category C
    module F = Functor F
    open import Categories.Morphism C using (_≅_; module ≅; ≅-isEquivalence)
    open _≅_
    -- Transport of morphisms along isomorphisms (defined as to ∘ f ∘ from)
    transport' : ∀ {A₁ A₂ B₁ B₂} → A₁ ≅ A₂ → B₁ ≅ B₂ → (A₁ C.⇒ B₁) → (A₂ C.⇒ B₂)
    transport' A≅ B≅ f = from B≅ C.∘ f C.∘ to A≅
    -- Proofs of ObjEquivCat coherence laws
    transport-resp-≈' : ∀ {A₁ A₂ B₁ B₂}
                      → (eqA : A₁ ≅ A₂) (eqB : B₁ ≅ B₂)
                      → ∀ {f g : A₁ C.⇒ B₁}
                      → f C.≈ g → transport' eqA eqB f C.≈ transport' eqA eqB g
    transport-resp-≈' _ _ f≈g = C.∘-resp-≈ʳ (C.∘-resp-≈ˡ f≈g)
    transport-refl' : ∀ {A B} {f : A C.⇒ B}
                    → transport' ≅.refl ≅.refl f C.≈ f
    transport-refl' = C.Equiv.trans (C.∘-resp-≈ʳ C.identityʳ) C.identityˡ
    transport-trans' : ∀ {A₁ A₂ A₃ B₁ B₂ B₃}
                     → (eqA₁ : A₁ ≅ A₂) (eqA₂ : A₂ ≅ A₃)
                     → (eqB₁ : B₁ ≅ B₂) (eqB₂ : B₂ ≅ B₃)
                     → {f : A₁ C.⇒ B₁}
                     → transport' (≅.trans eqA₁ eqA₂) (≅.trans eqB₁ eqB₂) f
                       C.≈ transport' eqA₂ eqB₂ (transport' eqA₁ eqB₁ f)
    transport-trans' eqA₁ eqA₂ eqB₁ eqB₂ {f} =
      C.Equiv.trans C.assoc (C.Equiv.trans (C.∘-resp-≈ʳ (C.∘-resp-≈ʳ C.sym-assoc))
                               (C.∘-resp-≈ʳ C.sym-assoc))
    transport-∘' : ∀ {A₁ A₂ B₁ B₂ C₁ C₂}
                 → (eqA : A₁ ≅ A₂) (eqB : B₁ ≅ B₂) (eqC : C₁ ≅ C₂)
                 → (f : A₁ C.⇒ B₁) (g : B₁ C.⇒ C₁)
                 → transport' eqB eqC g C.∘ transport' eqA eqB f
                   C.≈ transport' eqA eqC (g C.∘ f)
    transport-∘' eqA eqB eqC f g =
      C.Equiv.trans (C.∘-resp-≈ˡ C.sym-assoc)
      (C.Equiv.trans C.assoc
      (C.Equiv.trans (C.∘-resp-≈ʳ C.sym-assoc)
      (C.Equiv.trans (C.∘-resp-≈ʳ (C.∘-resp-≈ˡ (isoˡ eqB)))
      (C.Equiv.trans (C.∘-resp-≈ʳ C.identityˡ)
      (C.Equiv.trans C.assoc
      (C.∘-resp-≈ʳ C.sym-assoc))))))
    transport-id' : ∀ {A B} (eqA : A ≅ B)
                  → transport' eqA eqA (C.id {A}) C.≈ C.id {B}
    transport-id' eqA = C.Equiv.trans (C.∘-resp-≈ʳ C.identityˡ) (isoʳ eqA)
    -- Construct an ObjEquivCat instance using isomorphisms
    isoObjEquiv : ObjEquivCat (lsuc ℓ) (lsuc ℓ) (lsuc ℓ)
    isoObjEquiv = record
      { cat              = C
      ; _≈ₒ_             = _≅_
      ; ≈ₒ-isEquiv       = ≅-isEquivalence
      ; transport        = transport'
      ; transport-resp-≈ = transport-resp-≈'
      ; transport-refl   = transport-refl'
      ; transport-trans  = transport-trans'
      ; transport-∘      = transport-∘'
      ; transport-id     = transport-id'
      }
    open ObjEquivCat isoObjEquiv

    -- Container transport via functor action on "to"
    transportContainer : ∀ {A₁ A₂} → A₁ ≈ₒ A₂ → F.₀ A₁ ⇒ F.₀ A₂
    transportContainer eq = F.₁ (from eq)
    -- Proofs of container transport properties (refl, sym, trans)
    transportContainer-refl : ∀ {A}
      → transportContainer (IsEquivalence.refl ≈ₒ-isEquiv {A}) ≈M id (F.₀ A)
    transportContainer-refl = F.identity
    transportContainer-sym : ∀ {A B} (eq : A ≅ B)
                          → transportContainer (≅.sym eq) ∘ transportContainer eq ≈M id (F.₀ A)
    transportContainer-sym eq = ≈M-trans
      (≈M-sym F.homomorphism)
      (≈M-trans (F.F-resp-≈ (isoˡ eq)) F.identity)
    transportContainer-trans : ∀ {A₁ A₂ A₃}
      → (eq1 : A₁ ≈ₒ A₂) (eq2 : A₂ ≈ₒ A₃)
      → transportContainer (IsEquivalence.trans ≈ₒ-isEquiv eq1 eq2)
        ≈M (transportContainer eq2 ∘ transportContainer eq1)
    transportContainer-trans eq1 eq2 = F.homomorphism
    -- Naturality of transportContainer: FtB ∘ F₁f ≈M F₁(transport eqA eqB f) ∘ FtA
    act-natural : ∀ {A₁ A₂ B₁ B₂}
                → (eqA : A₁ ≈ₒ A₂) (eqB : B₁ ≈ₒ B₂)
                → (f : C._⇒_ A₁ B₁)
                → (transportContainer eqB ∘ F.₁ f)
                  ≈M
                  (F.₁ (transport eqA eqB f) ∘ transportContainer eqA)
    act-natural {A₁} {A₂} {B₁} {B₂} eqA eqB f = ≈M-sym R≈L
      where
        FtA  : F.₀ A₁ ⇒ F.₀ A₂
        FtA  = transportContainer eqA
        Ff   : F.₀ A₁ ⇒ F.₀ B₁
        Ff   = F.₁ f
        FtB  : F.₀ B₁ ⇒ F.₀ B₂
        FtB  = transportContainer eqB
        Ff∘from : F.₀ A₂ ⇒ F.₀ B₁
        Ff∘from = F.₁ (f C.∘ to eqA)
        open ≈M-Reasoning
        R≈L : F.₁ (transport eqA eqB f) ∘ FtA ≈M FtB ∘ Ff
        R≈L = begin
          F.₁ (transport eqA eqB f) ∘ FtA
            ≈⟨ ∘M-resp-≈ˡ {f = FtA} (F.homomorphism {f = f C.∘ to eqA} {g = from eqB}) ⟩
          (FtB ∘ Ff∘from) ∘ FtA
            ≈⟨ ∘M-assoc {f = FtA} {g = Ff∘from} {h = FtB} ⟩
          FtB ∘ (Ff∘from ∘ FtA)
            ≈⟨ ∘M-resp-≈ʳ {g = FtB}
                (∘M-resp-≈ˡ {f = FtA} (F.homomorphism {f = to eqA} {g = f})) ⟩
          FtB ∘ ((Ff ∘ F.₁ (to eqA)) ∘ FtA)
            ≈⟨ ∘M-resp-≈ʳ {g = FtB}
                (∘M-assoc {f = FtA} {g = F.₁ (to eqA)} {h = Ff}) ⟩
          FtB ∘ (Ff ∘ (F.₁ (to eqA) ∘ FtA))
            ≈⟨ ∘M-resp-≈ʳ {g = FtB}
                (∘M-resp-≈ʳ {g = Ff} (transportContainer-sym eqA)) ⟩
          FtB ∘ (Ff ∘ id (F.₀ A₁))
            ≈⟨ ∘M-resp-≈ʳ {g = FtB} (∘M-identityʳ {f = Ff}) ⟩
          FtB ∘ Ff
            ∎

  -- Construct a ContCatEquiv from a category C and a container functor F : C → ContCat
  contCatEquivFromIso : ContCatEquiv ℓ
  contCatEquivFromIso = record
    { base                = isoObjEquiv
    ; containerFunctor    = F
    ; transportContainer  = transportContainer
    ; transportContainer-refl  = transportContainer-refl
    ; transportContainer-trans = transportContainer-trans
    ; act-natural         = act-natural
    }
