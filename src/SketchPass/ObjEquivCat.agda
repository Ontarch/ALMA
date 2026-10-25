------------------------------------------------------------------------
-- Category with an object equivalence relation
--
-- Defines ObjEquivCat: a Category equipped with an object equivalence
-- _≈ₒ_ and a coherent transport of morphisms. The standard instance
-- uses the notion of isomorphism from category theory.
--
-- 带对象等价关系的范畴
--
-- 定义 ObjEquivCat：装备了对象等价 _≈ₒ_ 与相干态射传输的范畴。标准
-- 实例采用范畴论中的同构概念。
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --exact-split --guardedness --double-check #-}

module SketchPass.ObjEquivCat where

open import Agda.Primitive using (_⊔_; lsuc; Level)
open import Relation.Binary using (IsEquivalence)
open import Categories.Category using (Category)

-- Category with an object equivalence
record ObjEquivCat (o ℓ e : Level) : Set (lsuc (o ⊔ ℓ ⊔ e)) where
  field
    cat : Category o ℓ e
  private
    module Cat = Category cat
  open Cat using (Obj; _⇒_; _≈_; id; _∘_)
  infix 4 _≈ₒ_
  field
    -- Object equivalence relation
    _≈ₒ_       : Obj → Obj → Set (ℓ ⊔ e)
    ≈ₒ-isEquiv : IsEquivalence _≈ₒ_
    -- Transport of morphisms along object equivalences
    transport : ∀ {A₁ A₂ B₁ B₂}
                → A₁ ≈ₒ A₂ → B₁ ≈ₒ B₂
                → A₁ ⇒ B₁
                → A₂ ⇒ B₂
    -- Coherence laws
    transport-resp-≈ : ∀ {A₁ A₂ B₁ B₂}
                        → (eqA : A₁ ≈ₒ A₂) (eqB : B₁ ≈ₒ B₂)
                        → ∀ {f g : A₁ ⇒ B₁}
                        → f ≈ g → transport eqA eqB f ≈ transport eqA eqB g
    transport-refl : ∀ {A B} {f : A ⇒ B}
                        → transport (IsEquivalence.refl ≈ₒ-isEquiv) (IsEquivalence.refl ≈ₒ-isEquiv) f ≈ f
    transport-trans : ∀ {A₁ A₂ A₃ B₁ B₂ B₃}
                        → (eqA₁ : A₁ ≈ₒ A₂) (eqA₂ : A₂ ≈ₒ A₃)
                        → (eqB₁ : B₁ ≈ₒ B₂) (eqB₂ : B₂ ≈ₒ B₃)
                        → {f : A₁ ⇒ B₁}
                        → transport (IsEquivalence.trans ≈ₒ-isEquiv eqA₁ eqA₂)
                                        (IsEquivalence.trans ≈ₒ-isEquiv eqB₁ eqB₂) f
                          ≈
                          transport eqA₂ eqB₂ (transport eqA₁ eqB₁ f)
    transport-∘ : ∀ {A₁ A₂ B₁ B₂ C₁ C₂}
                → (eqA : A₁ ≈ₒ A₂) (eqB : B₁ ≈ₒ B₂) (eqC : C₁ ≈ₒ C₂)
                → (f : A₁ ⇒ B₁) (g : B₁ ⇒ C₁)
                → transport eqB eqC g ∘ transport eqA eqB f
                  ≈ transport eqA eqC (g ∘ f)
    transport-id : ∀ {A B} (eqA : A ≈ₒ B)
                 → transport eqA eqA (id {A}) ≈ id {B}

-- Canonical instance: isomorphism as object equivalence
objEquivCatFromIso : ∀ {o ℓ e} (C : Category o ℓ e) → ObjEquivCat o ℓ e
objEquivCatFromIso C = record
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
  where
    open Category C
    open Equiv
    open import Categories.Morphism C using (_≅_; module ≅; ≅-isEquivalence)
    open _≅_
    transport' : ∀ {A₁ A₂ B₁ B₂} → A₁ ≅ A₂ → B₁ ≅ B₂ → (A₁ ⇒ B₁) → (A₂ ⇒ B₂)
    transport' A≅ B≅ f = from B≅ ∘ f ∘ to A≅
    transport-resp-≈' : ∀ {A₁ A₂ B₁ B₂}
                      → (eqA : A₁ ≅ A₂) (eqB : B₁ ≅ B₂)
                      → ∀ {f g : A₁ ⇒ B₁}
                      → f ≈ g → transport' eqA eqB f ≈ transport' eqA eqB g
    transport-resp-≈' _ _ f≈g = ∘-resp-≈ʳ (∘-resp-≈ˡ f≈g)
    transport-refl' : ∀ {A B} {f : A ⇒ B} → transport' ≅.refl ≅.refl f ≈ f
    transport-refl' = trans (∘-resp-≈ʳ identityʳ) identityˡ
    transport-trans' : ∀ {A₁ A₂ A₃ B₁ B₂ B₃}
                     → (eqA₁ : A₁ ≅ A₂) (eqA₂ : A₂ ≅ A₃)
                     → (eqB₁ : B₁ ≅ B₂) (eqB₂ : B₂ ≅ B₃)
                     → {f : A₁ ⇒ B₁}
                     → transport' (≅.trans eqA₁ eqA₂) (≅.trans eqB₁ eqB₂) f
                       ≈ transport' eqA₂ eqB₂ (transport' eqA₁ eqB₁ f)
    transport-trans' eqA₁ eqA₂ eqB₁ eqB₂ {f} =
      trans assoc (trans (∘-resp-≈ʳ (∘-resp-≈ʳ sym-assoc)) (∘-resp-≈ʳ sym-assoc))
    transport-∘' : ∀ {A₁ A₂ B₁ B₂ C₁ C₂}
                 → (eqA : A₁ ≅ A₂) (eqB : B₁ ≅ B₂) (eqC : C₁ ≅ C₂)
                 → (f : A₁ ⇒ B₁) (g : B₁ ⇒ C₁)
                 → transport' eqB eqC g ∘ transport' eqA eqB f
                   ≈ transport' eqA eqC (g ∘ f)
    transport-∘' eqA eqB eqC f g =
      trans (∘-resp-≈ˡ sym-assoc)
      (trans assoc
      (trans (∘-resp-≈ʳ sym-assoc)
      (trans (∘-resp-≈ʳ (∘-resp-≈ˡ (isoˡ eqB)))
      (trans (∘-resp-≈ʳ identityˡ)
      (trans assoc
      (∘-resp-≈ʳ sym-assoc))))))
    transport-id' : ∀ {A B} (eqA : A ≅ B)
                  → transport' eqA eqA (id {A}) ≈ id {B}
    transport-id' eqA = trans (∘-resp-≈ʳ identityˡ) (isoʳ eqA)

-- Equational reasoning for object equivalence _≈ₒ_
module ≈ₒ-Reasoning {o ℓ e : Level} (C : ObjEquivCat o ℓ e) where
  open ObjEquivCat C
  open Category cat using (Obj)
  open import Relation.Binary.Reasoning.Setoid 
    (record
      { Carrier       = Obj
      ; _≈_           = _≈ₒ_
      ; isEquivalence = ≈ₒ-isEquiv
      }) public
