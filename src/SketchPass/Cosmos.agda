------------------------------------------------------------------------
-- ALMA — infinite, unbounded, self-referential dynamic cosmos
--
-- Built with type theory, category theory, containers, and coalgebraic
-- unfolding. Cosmos is the terminal coalgebra of a polynomial functor
-- internalized in type theory.
--
-- ALMA —— 无限、无界、自指的动态宇宙
--
-- 基于类型论、范畴论、容器（containers）和余代数展开（coalgebraic
-- unfolding）构建。Cosmos 是在类型论中内部化的多项式函子的终余代数。
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --exact-split --guardedness --double-check #-}

module SketchPass.Cosmos where

open import Agda.Primitive using (Level; lsuc; _⊔_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂; subst; subst₂; isEquivalence; setoid)
open import Relation.Binary using (Reflexive; Symmetric; Transitive)
open import Relation.Binary.Bundles using (Setoid)
open import Data.Unit.Polymorphic.Base using (⊤; tt)
open import Data.Product using (proj₁)
open import Data.Container.Core using (shape)
open import Function using (id; _∘_; Func)
open import Categories.Category using (Category)
open import Categories.Category.Instance.Sets using (Sets)
open import Categories.Category.Instance.Setoids using (Setoids)
open import Categories.Category.Construction.Elements using (Elements)
open import Categories.Functor using (Functor)

open import SketchPass.ContCategory using (≈M-refl; ContCat)
open import SketchPass.ObjEquivCat using (ObjEquivCat)
open import SketchPass.ContCatEquiv using (ContCatEquiv; contCatEquivFromIso)
open import SketchPass.ContCatEquivFunctor
  using (ContCatEquivFunctor; idContCatEquivFunctor; compContCatEquivFunctor)
open import SketchPass.Unfolding
  using (Unfolding; module UnfoldingSetoid; module UnfoldingFunctor)
open import SketchPass.MorphismObject
  using (MorphismObject; idMorphismObject; compMorphismObject)
open import SketchPass.MorphismMorphism
  using (MorphismMorphism; idMorphismMorphism; compMorphismMorphism)

-- Core Definitions: CosmosF and Cosmos as Terminal Coalgebra
record CosmosF (ℓ : Level) (X : Set (lsuc (lsuc ℓ))) : Set (lsuc (lsuc ℓ)) where
  field
    contEquiv     : ContCatEquiv ℓ
    unfoldingCore : Unfolding ℓ contEquiv X

record Cosmos (ℓ : Level) : Set (lsuc (lsuc ℓ)) where
  coinductive
  field
    out : CosmosF ℓ (Cosmos ℓ)
open Cosmos public

-- Lightweight Functoriality of CosmosF
module CosmosMap {ℓ : Level} where
  open UnfoldingFunctor

  mapCosmosF : {X Y : Set (lsuc (lsuc ℓ))} → (X → Y) → CosmosF ℓ X → CosmosF ℓ Y
  mapCosmosF f c = record
    { contEquiv     = contEquiv
    ; unfoldingCore = mapUnfolding f unfoldingCore
    }
    where open CosmosF c

  map-id : ∀ {X} (c : CosmosF ℓ X) → mapCosmosF (λ x → x) c ≡ c
  map-id c = refl
  map-∘ : ∀ {X Y Z} {f : Y → Z} {g : X → Y} (c : CosmosF ℓ X) →
          mapCosmosF (f ∘ g) c ≡ mapCosmosF f (mapCosmosF g c)
  map-∘ c = refl
  map-cong : {X Y : Set (lsuc (lsuc ℓ))} {f g : X → Y} → f ≡ g → mapCosmosF f ≡ mapCosmosF g
  map-cong refl = refl

-- Universe Morphisms: Coalgebra Homomorphisms
mutual
  record _⇒ℱ_ {ℓ} (F G : Cosmos ℓ) : Set (lsuc ℓ) where
    coinductive
    field
      out : ⇒ℱLayer F G

  record ⇒ℱLayer {ℓ} (F G : Cosmos ℓ) : Set (lsuc ℓ) where
    inductive
    private
      module FL = CosmosF (out F)
      module GL = CosmosF (out G)
      module CE-F = ContCatEquiv FL.contEquiv
      module CE-G = ContCatEquiv GL.contEquiv
      open Unfolding FL.unfoldingCore
        renaming (unfoldFunctor to UF-functor; unfold-next to UF-next; pos-to-shape to UF-pos-to-shape)
      open Unfolding GL.unfoldingCore
        renaming (unfoldFunctor to UG-functor; unfold-next to UG-next; pos-to-shape to UG-pos-to-shape)
    field
      contEquivFunctor : ContCatEquivFunctor FL.contEquiv GL.contEquiv
      morphismObj      : MorphismObject contEquivFunctor FL.unfoldingCore GL.unfoldingCore
      morphismMor      : MorphismMorphism morphismObj
      onunfold-next    : ∀ {A}
        (s : Data.Container.Core.Shape (Functor.₀ CE-F.containerFunctor A)) →
        UF-next s ⇒ℱ UG-next (Data.Container.Core.shape (ContCatEquivFunctor.containerNat contEquivFunctor) s)

open _⇒ℱ_ public

-- Identity coalgebra homomorphism
id⇒ℱ : ∀ {ℓ} {F : Cosmos ℓ} → F ⇒ℱ F
id⇒ℱ {F = F} .out =
  let open CosmosF (out F)
  in record
    { contEquivFunctor = idContCatEquivFunctor contEquiv
    ; morphismObj      = idMorphismObject {UF = unfoldingCore}
    ; morphismMor      = idMorphismMorphism {UF = unfoldingCore}
    ; onunfold-next    = λ _ → id⇒ℱ
    }

-- Composition of coalgebra homomorphisms
_∘⇒ℱ_ : ∀ {ℓ} {F G H : Cosmos ℓ} → G ⇒ℱ H → F ⇒ℱ G → F ⇒ℱ H
_∘⇒ℱ_ {ℓ} {F} {G} {H} g f .out = record
  { contEquivFunctor = compCF
  ; morphismObj      = compMO
  ; morphismMor      = compMM
  ; onunfold-next    = λ {A} s → nextG (shape (ContCatEquivFunctor.containerNat cF) s) ∘⇒ℱ nextF s
  }
  where
    open ⇒ℱLayer (g .out)
      renaming (contEquivFunctor to cG; morphismObj to moG; morphismMor to mmG; onunfold-next to nextG)
    open ⇒ℱLayer (f .out)
      renaming (contEquivFunctor to cF; morphismObj to moF; morphismMor to mmF; onunfold-next to nextF)
    compCF = compContCatEquivFunctor cG cF
    compMO = compMorphismObject moG moF
    compMM = compMorphismMorphism mmG mmF

-- UnitCosmos: Trivial One-Object Cosmos
UnitCat : ∀ {ℓ} → Category (lsuc ℓ) (lsuc ℓ) (lsuc ℓ)
UnitCat = record
  { Obj       = ⊤
  ; _⇒_       = λ _ _ → ⊤
  ; _≈_       = _≡_
  ; id        = tt
  ; _∘_       = λ _ _ → tt
  ; equiv     = record { refl = refl ; sym = sym ; trans = trans }
  ; ∘-resp-≈  = λ _ _ → refl
  ; assoc     = λ {_ _ _ _ _ _ _} → refl
  ; sym-assoc = λ {_ _ _ _ _ _ _} → refl
  ; identityˡ = λ {_ _ _} → refl
  ; identityʳ = λ {_ _ _} → refl
  ; identity² = λ {_} → refl
  }
UnitContainerFunctor : ∀ {ℓ} → Functor (UnitCat {ℓ}) (ContCat (lsuc ℓ) (lsuc ℓ))
UnitContainerFunctor = record
  { F₀           = λ _ → record { Shape = ⊤ ; Position = λ _ → ⊤ }
  ; F₁           = λ _ → record { shape = λ _ → tt ; position = λ _ → tt }
  ; identity     = ≈M-refl
  ; homomorphism = ≈M-refl
  ; F-resp-≈     = λ _ → ≈M-refl
  }
UnitContCatEquiv : ∀ {ℓ} → ContCatEquiv ℓ
UnitContCatEquiv = contCatEquivFromIso UnitCat UnitContainerFunctor
UnitCosmos : ∀ {ℓ} → Cosmos ℓ
UnitCosmos {ℓ} .out = record
  { contEquiv     = UnitContCatEquiv
  ; unfoldingCore = unitUnfolding
  }
  where
    open ContCatEquiv UnitContCatEquiv
    open ObjEquivCat base
    module Cat = Category cat
    ShapeForget : Functor cat (Sets (lsuc ℓ))
    ShapeForget = record
      { F₀       = λ _ → ⊤
      ; F₁       = λ _ _ → tt
      ; identity     = λ _ → refl
      ; homomorphism = λ _ → refl
      ; F-resp-≈     = λ _ _ → refl
      }
    UnitShapeCat : Category (lsuc ℓ ⊔ lsuc ℓ) (lsuc ℓ ⊔ lsuc ℓ) (lsuc ℓ)
    UnitShapeCat = Elements ShapeForget
    unitUnfoldFunctor : Functor UnitShapeCat cat
    unitUnfoldFunctor = record
      { F₀           = proj₁
      ; F₁           = proj₁
      ; identity     = Cat.Equiv.refl
      ; homomorphism = Cat.Equiv.refl
      ; F-resp-≈     = λ p → p
      }
    unitUnfolding : Unfolding ℓ UnitContCatEquiv (Cosmos ℓ)
    unitUnfolding = record
      { unfoldFunctor          = unitUnfoldFunctor
      ; unfold-next            = λ _ → UnitCosmos
      ; pos-to-shape           = λ _ _ → tt
      ; pos-actS-compat        = λ _ _ _ → refl
      ; pos-to-shape-transport = λ _ → refl
      }

-- StrictSets Category
StrictSets : (ℓ : Level) → Category (lsuc ℓ) ℓ ℓ
StrictSets ℓ = record
  { Obj       = Set ℓ
  ; _⇒_       = λ A B → A → B
  ; _≈_       = λ f g → ∀ {x} → f x ≡ g x
  ; id        = λ x → x
  ; _∘_       = λ g f x → g (f x)
  ; assoc     = refl
  ; sym-assoc = refl
  ; identityˡ = refl
  ; identityʳ = refl
  ; identity² = refl
  ; equiv     = record
    { refl  = refl
    ; sym   = λ eq → sym eq
    ; trans = λ eq₁ eq₂ → trans eq₁ eq₂
    }
  ; ∘-resp-≈  = λ {_ _ _ h i f g} eq₁ eq₂ {x} → trans (eq₁ {f x}) (cong i (eq₂ {x}))
  }

-- CosmosF Functor: StrictSets → Setoids
module CosmosFFunctor {ℓ : Level} where
  open UnfoldingFunctor
  open CosmosF
  open CosmosMap
  -- Helper: lift plain functions to setoid morphisms
  private
    toStdFunc : {X Y : Set (lsuc (lsuc ℓ))} → (X → Y) → Func (setoid X) (setoid Y)
    toStdFunc f = record { to = f ; cong = λ eq → cong f eq }
  -- Equivalence relation on CosmosF elements
  record _≈F_ (X : Setoid (lsuc (lsuc ℓ)) (lsuc (lsuc ℓ)))
              (c₁ c₂ : CosmosF ℓ (Setoid.Carrier X)) : Set (lsuc (lsuc ℓ)) where
    private
      module X  = Setoid X
      module C₁ = CosmosF c₁
      module C₂ = CosmosF c₂
    field
      contEquiv-eq : C₁.contEquiv ≡ C₂.contEquiv
      unfolding-eq :
        let module US = UnfoldingSetoid {CE = C₂.contEquiv}
        in US._≈U_ X
             (subst (λ ce → Unfolding ℓ ce (X.Carrier)) contEquiv-eq C₁.unfoldingCore)
             C₂.unfoldingCore
  -- Equivalence proofs
  ≈F-refl : {X : Setoid _ _} → Reflexive (_≈F_ X)
  ≈F-refl {X = X} = record
    { contEquiv-eq = refl
    ; unfolding-eq = UnfoldingSetoid.≈U-refl {X = X}
    }
  ≈F-sym : {X : Setoid _ _} → Symmetric (_≈F_ X)
  ≈F-sym {X = X} (record { contEquiv-eq = refl ; unfolding-eq = ue }) = record
    { contEquiv-eq = refl
    ; unfolding-eq = UnfoldingSetoid.≈U-sym X ue
    }
  ≈F-trans : {X : Setoid _ _} → Transitive (_≈F_ X)
  ≈F-trans {X = X}
    (record { contEquiv-eq = refl ; unfolding-eq = ue₁ })
    (record { contEquiv-eq = refl ; unfolding-eq = ue₂ }) = record
      { contEquiv-eq = refl
      ; unfolding-eq = UnfoldingSetoid.≈U-trans X ue₁ ue₂
      }
  -- CosmosF as a Setoid
  CosmosFSetoid : Setoid (lsuc (lsuc ℓ)) (lsuc (lsuc ℓ))
                → Setoid (lsuc (lsuc ℓ)) (lsuc (lsuc ℓ))
  CosmosFSetoid X = record
    { Carrier       = CosmosF ℓ (Setoid.Carrier X)
    ; _≈_           = _≈F_ X
    ; isEquivalence = record { refl = ≈F-refl ; sym = ≈F-sym ; trans = ≈F-trans }
    }
  -- mapCosmosF respects the equivalence
  mapCosmosF-resp : {X Y : Setoid _ _} → Func X Y
                  → Func (CosmosFSetoid X) (CosmosFSetoid Y)
  mapCosmosF-resp f = record
    { to   = λ c → mapCosmosF (Func.to f) c
    ; cong = helper
    }
    where
      helper : {c₁ c₂ : CosmosF ℓ _} → _≈F_ _ c₁ c₂
             → _≈F_ _ (mapCosmosF (Func.to f) c₁) (mapCosmosF (Func.to f) c₂)
      helper (record { contEquiv-eq = refl ; unfolding-eq = ue }) = record
        { contEquiv-eq = refl
        ; unfolding-eq = Func.cong (UnfoldingSetoid.mapUnfolding-Func _ _ f) ue
        }
  -- The CosmosF functor
  CosmosFFunctor : Functor (StrictSets (lsuc (lsuc ℓ)))
                           (Setoids (lsuc (lsuc ℓ)) (lsuc (lsuc ℓ)))
  CosmosFFunctor = record
    { F₀           = λ X → CosmosFSetoid (setoid X)
    ; F₁           = λ f → mapCosmosF-resp (toStdFunc f)
    ; identity     = λ {X} → ≈F-refl {X = setoid X}
    ; homomorphism = λ {X Y Z} {f g} → ≈F-refl {X = setoid Z}
    ; F-resp-≈     = λ {X Y} {f g} f≈g {c} →
        let open UnfoldingSetoid {CE = contEquiv c}
        in record
          { contEquiv-eq = refl
          ; unfolding-eq = mapUnfolding-resp-≈ X Y f g f≈g ≈U-refl
          }
    }
