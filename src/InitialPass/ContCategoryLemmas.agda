------------------------------------------------------------------------
-- Container morphism equivalence lemmas and container functor basics
--
-- shape-level laws for _≈M_ (sym, trans, assoc, whiskering) and
-- basic functoriality of actSOf/actPOf (id, comp, resp-≈)
------------------------------------------------------------------------
{-# OPTIONS --safe --cubical-compatible --exact-split --guardedness --double-check #-}

module InitialPass.ContCategoryLemmas where

open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; trans-reflʳ)
open import Data.Container.Core using (Container; _⇒_; shape; position)
open import Categories.Category using (Category)
open import Categories.Functor using (Functor)

open import InitialPass.ContCategory
  using (_≈M_; ≈M-sym; ≈M-trans; ∘M-assoc; ∘M-resp-≈ˡ; ∘M-resp-≈ʳ; ContCat)

-- Basic ≈M operations

-- extract shape equality from ≈M proof
shape-eq-from-≈M : ∀ {s p} {C D : Container s p} {f g : C ⇒ D}
                  → f ≈M g → ∀ x → _⇒_.shape f x ≡ _⇒_.shape g x
shape-eq-from-≈M eq x = let open _≈M_ eq in shape-eq x

-- ≈M algebraic laws (shape layer)

-- shape-eq of sym
shape-eq-sym : ∀ {s p} {C D : Container s p} {f g : C ⇒ D}
              → (eq : f ≈M g) (x : Container.Shape C)
              → shape-eq-from-≈M (≈M-sym eq) x ≡ sym (shape-eq-from-≈M eq x)
shape-eq-sym _ _ = refl
-- shape-eq of trans
shape-eq-trans : ∀ {s p} {C D : Container s p} {f g h : C ⇒ D}
                → (eq1 : f ≈M g) (eq2 : g ≈M h) (x : Container.Shape C)
                → shape-eq-from-≈M (≈M-trans eq1 eq2) x
                  ≡ trans (shape-eq-from-≈M eq1 x) (shape-eq-from-≈M eq2 x)
shape-eq-trans _ _ _ = refl
-- shape-eq of assoc is refl
shape-eq-assoc : ∀ {s p} {A B C D : Container s p}
              → {f : A ⇒ B} {g : B ⇒ C} {h : C ⇒ D}
              → (x : Container.Shape A)
              → shape-eq-from-≈M (∘M-assoc {A = A} {B} {C} {D} {f} {g} {h}) x ≡ refl
shape-eq-assoc _ = refl
-- shape-eq respects left whiskering
shape-eq-resp-ˡ : ∀ {s p} {A B C : Container s p}
                  → {g₁ g₂ : B ⇒ C} {f : A ⇒ B}
                  → (eq : g₁ ≈M g₂) (x : Container.Shape A)
                  → shape-eq-from-≈M (∘M-resp-≈ˡ {f = f} eq) x
                    ≡ shape-eq-from-≈M eq (_⇒_.shape f x)
shape-eq-resp-ˡ {f = f} eq x = trans-reflʳ (shape-eq-from-≈M eq (_⇒_.shape f x))
-- shape-eq respects right whiskering
shape-eq-resp-ʳ : ∀ {s p} {A B C : Container s p}
                → {g : B ⇒ C} {f₁ f₂ : A ⇒ B}
                → (eq : f₁ ≈M f₂) (x : Container.Shape A)
                → shape-eq-from-≈M (∘M-resp-≈ʳ {g = g} eq) x
                  ≡ cong (shape g) (shape-eq-from-≈M eq x)
shape-eq-resp-ʳ _ _ = refl

-- Container functor helpers

-- shape set of a container functor at object A
ShapeOf : ∀ {o ℓ e s p} {C : Category o ℓ e}
        → Functor C (ContCat s p) → Category.Obj C → Set s
ShapeOf F A = Container.Shape (Functor.₀ F A)
-- position set of a container functor at shape s
PosOf : ∀ {o ℓ e s p} {C : Category o ℓ e}
      → (F : Functor C (ContCat s p)) {A : Category.Obj C}
      → ShapeOf F A → Set p
PosOf F {A} s = Container.Position (Functor.₀ F A) s
-- action of a container functor on shapes
actSOf : ∀ {o ℓ e s p} {C : Category o ℓ e}
        → (F : Functor C (ContCat s p)) {A B : Category.Obj C}
        → Category._⇒_ C A B → ShapeOf F A → ShapeOf F B
actSOf F f = shape (Functor.₁ F f)
-- action of a container functor on positions
actPOf : ∀ {o ℓ e s p} {C : Category o ℓ e}
        → (F : Functor C (ContCat s p)) {A B : Category.Obj C}
        → (f : Category._⇒_ C A B) (s : ShapeOf F A)
        → PosOf F (actSOf F f s) → PosOf F s
actPOf F f s = position (Functor.₁ F f) {s}
