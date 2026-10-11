------------------------------------------------------------------------
-- The category of containers (syntactic presentations of polynomial
-- functors)
--
-- The morphism equivalence is the generic pointwise-with-transport
-- relation from SubstTransport-Right, instantiated at container
-- morphisms, and the container-specific composition laws and the
-- Category instance are added.
--
-- 容器范畴（容器是多项式函子的语法表示；多项式函子是容器的语义解释）
--
-- 态射等价在 SubstTransport-Right 的逐点相等 + 传输关系在容器态射上
-- 实例化并添加容器特有的复合定律与 Category 实例。
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module ALMA.Cosmos.ContCategory where

open import Agda.Primitive using (Level; lsuc; _⊔_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Container.Core using (Container; Shape; Position; _⇒_)
open import Data.Container.Morphism using (id; _∘_)
open import Relation.Binary.PropositionalEquality.Core using (cong; subst)
open import Relation.Binary.PropositionalEquality.Properties using (module ≡-Reasoning)
open ≡-Reasoning

open import Categories.Category.Core using (Category)

open import ALMA.Base.Equivalence.SubstTransport using (module SubstTransport-Right)

------------------------------------------------------------------------
-- Container morphism equivalence
--
-- The generic pointwise-with-transport relation from
-- SubstTransport-Right, instantiated at container morphisms.
--
-- 容器态射等价
--
-- SubstTransport-Right 的逐点相等 + 传输关系在容器态射上的实例化。

module _ {s p : Level} {X Y : Container s p} where
  open SubstTransport-Right
    {S = Shape X} {T = Shape Y}
    (Position Y) (Position X)
    {F = X ⇒ Y}
    _⇒_.shape _⇒_.position public

-- Position commutes with substitution along shape map equalities.
--
-- 位置映射与沿形状映射相等的传输交换。
position-subst : ∀ {s p} {B C : Container s p}
               → (g : B ⇒ C) {t₁ t₂ : Shape B} (eq : t₁ ≡ t₂)
               → (q : Position C (_⇒_.shape g t₁))
               → subst (Position B) eq (_⇒_.position g {t₁} q)
                 ≡ _⇒_.position g {t₂} (subst (Position C) (cong (_⇒_.shape g) eq) q)
position-subst g refl q = refl

------------------------------------------------------------------------
-- Composition laws
--
-- 复合定律

module _ {s p} {A B C : Container s p} where

  -- Left/Right whiskering.
  --
  -- 左/右 whiskering。
  ∘M-resp-≈ˡ : {g₁ g₂ : B ⇒ C} {f : A ⇒ B}
             → _≈sr_ g₁ g₂ → _≈sr_ (g₁ ∘ f) (g₂ ∘ f)
  ∘M-resp-≈ˡ {g₁} {g₂} {f} eq = record
    { shape-eq    = λ sh → _≈sr_.shape-eq eq (f.shape sh)
    ; position-eq = λ sh q →
        cong (f.position {sh}) (_≈sr_.position-eq eq (f.shape sh) q)
    }
    where module f = _⇒_ f

  ∘M-resp-≈ʳ : {g : B ⇒ C} {f₁ f₂ : A ⇒ B}
             → _≈sr_ f₁ f₂ → _≈sr_ (g ∘ f₁) (g ∘ f₂)
  ∘M-resp-≈ʳ {g} {f₁} {f₂} eq = record
    { shape-eq    = λ sh → cong (g.shape) (_≈sr_.shape-eq eq sh)
    ; position-eq = λ sh q →
        let q₁ = g.position {f₁.shape sh} q
            e  = _≈sr_.shape-eq eq sh
        in begin
          f₁.position {sh} q₁
            ≡⟨ _≈sr_.position-eq eq sh q₁ ⟩
          f₂.position {sh} (subst (Position B) e q₁)
            ≡⟨ cong (f₂.position {sh}) (position-subst g e q) ⟩
          f₂.position {sh}
            (g.position {f₂.shape sh} (subst (Position C) (cong (g.shape) e) q))
            ∎
    }
    where
      module f₁ = _⇒_ f₁
      module f₂ = _⇒_ f₂
      module g  = _⇒_ g

  -- Composition respects equivalence.
  --
  -- 复合保持等价。
  ∘M-resp-≈ : {g₁ g₂ : B ⇒ C} {f₁ f₂ : A ⇒ B}
            → _≈sr_ g₁ g₂ → _≈sr_ f₁ f₂
            → _≈sr_ (g₁ ∘ f₁) (g₂ ∘ f₂)
  ∘M-resp-≈ {g₁} {g₂} {f₁} {f₂} eq-g eq-f =
    ≈sr-trans
      (∘M-resp-≈ˡ {f = f₁} eq-g)
      (∘M-resp-≈ʳ {g = g₂} eq-f)

------------------------------------------------------------------------
-- Category laws
--
-- 范畴律

∘M-assoc : ∀ {s p} {A B C D : Container s p}
         → {f : A ⇒ B} {g : B ⇒ C} {h : C ⇒ D}
         → _≈sr_ ((h ∘ g) ∘ f) (h ∘ (g ∘ f))
∘M-assoc = record
  { shape-eq    = λ _ → refl
  ; position-eq = λ _ _ → refl
  }

-- Left/Right identity law.
--
-- 左/右单位律。
module _ {s p} {A B : Container s p} where

  ∘M-identityˡ : {f : A ⇒ B} → _≈sr_ (id B ∘ f) f
  ∘M-identityˡ = record
    { shape-eq    = λ _ → refl
    ; position-eq = λ _ _ → refl
    }

  ∘M-identityʳ : {f : A ⇒ B} → _≈sr_ (f ∘ id A) f
  ∘M-identityʳ = record
    { shape-eq    = λ _ → refl
    ; position-eq = λ _ _ → refl
    }

------------------------------------------------------------------------
-- Container category instance
--
-- 容器范畴实例

ContCat : (s p : Level) → Category (lsuc (s ⊔ p)) (s ⊔ p) (s ⊔ p)
ContCat s p = record
  { Obj       = Container s p
  ; _⇒_       = _⇒_
  ; _≈_       = _≈sr_
  ; id        = λ {A} → id A
  ; _∘_       = _∘_
  ; equiv     = ≈sr-isEquivalence
  ; ∘-resp-≈  = ∘M-resp-≈
  ; assoc     = λ {A B C D f g h} → ∘M-assoc {f = f} {g = g} {h = h}
  ; sym-assoc = λ {A B C D f g h} → ≈sr-sym (∘M-assoc {f = f} {g = g} {h = h})
  ; identityˡ = ∘M-identityˡ
  ; identityʳ = ∘M-identityʳ
  ; identity² = λ {A} → ∘M-identityˡ {f = id A}
  }
