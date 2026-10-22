------------------------------------------------------------------------
-- CosmosCategory: the category of Cosmos objects and structured simulations
-- 宇宙范畴：以 Cosmos 为对象、_⇒ℱ_ 为态射的范畴
--
-- Defines the equivalence _≈ℱ_ on _⇒ℱ_ witnesses (coinductive bisimulation),
-- proves the category laws, and assembles a Category instance.
-- 定义 _⇒ℱ_ 见证上的等价 _≈ℱ_（余归纳互模拟），验证范畴律，
-- 并构造 Category 实例
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module SecondPass.CosmosCategory where

open import Agda.Primitive using (Level; _⊔_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality.Core using (trans; cong; sym)
open import Relation.Binary.PropositionalEquality.Properties using (module ≡-Reasoning)
open ≡-Reasoning

open import Categories.Category.Core using (Category)
open import Categories.Functor.Core using (Functor)

open import Cosmos.ContCategory using (ContCat)
open import Cosmos.ContCategoryLemmas using (ShapeOf; PosOf)
open import SecondPass.MorphismObject using (MorphismObject)
open import SecondPass.Cosmos using
  (Cosmos; _⇒ℱ_; id⇒ℱ; _∘⇒ℱ_; module _⇒ℱ[_]_ ; module ⇒ℱLayer[_])
open _⇒ℱ[_]_
open ⇒ℱLayer[_]

module _ {o h e s p : Level}
         {C : Category o h e}
         {FC : Functor C (ContCat s p)} where

  private
    L = o ⊔ h ⊔ e ⊔ s ⊔ p
    open MorphismObject using (onPos; pts-compat)

  -- Bisimulation equivalence on _⇒ℱ_ witnesses
  -- _⇒ℱ_ 见证上的互模拟等价
  record _≈ℱ_ {F G : Cosmos C FC} (m n : F ⇒ℱ G) : Set L where
    coinductive
    field
      shapeTrans-≈ : ∀ {A} {s : ShapeOf FC A} (p : PosOf FC s)
                   → shapeTrans (m .out) p ≡ shapeTrans (n .out) p

      onPos-≈ : ∀ {A} {s : ShapeOf FC A} (p : PosOf FC s)
              → onPos (morphismObj (m .out)) p ≡ onPos (morphismObj (n .out)) p

      unfold-next-≈ : ∀ {A} (s : ShapeOf FC A)
                    → onunfold-next (m .out) s ≈ℱ onunfold-next (n .out) s
  open _≈ℱ_

  -- Equivalence proof
  -- 等价性证明
  ≈ℱ-refl : ∀ {F G} {m : F ⇒ℱ G} → m ≈ℱ m
  ≈ℱ-refl .shapeTrans-≈ _ = refl
  ≈ℱ-refl .onPos-≈ _ = refl
  ≈ℱ-refl .unfold-next-≈ _ = ≈ℱ-refl

  ≈ℱ-sym : ∀ {F G} {m n : F ⇒ℱ G} → m ≈ℱ n → n ≈ℱ m
  ≈ℱ-sym eq .shapeTrans-≈ p = sym (eq .shapeTrans-≈ p)
  ≈ℱ-sym eq .onPos-≈ p = sym (eq .onPos-≈ p)
  ≈ℱ-sym eq .unfold-next-≈ s = ≈ℱ-sym (eq .unfold-next-≈ s)

  ≈ℱ-trans : ∀ {F G} {m n k : F ⇒ℱ G} → m ≈ℱ n → n ≈ℱ k → m ≈ℱ k
  ≈ℱ-trans eq₁ eq₂ .shapeTrans-≈ p = trans (eq₁ .shapeTrans-≈ p) (eq₂ .shapeTrans-≈ p)
  ≈ℱ-trans eq₁ eq₂ .onPos-≈ p = trans (eq₁ .onPos-≈ p) (eq₂ .onPos-≈ p)
  ≈ℱ-trans eq₁ eq₂ .unfold-next-≈ s =
    ≈ℱ-trans (eq₁ .unfold-next-≈ s) (eq₂ .unfold-next-≈ s)

  -- Category laws
  -- 范畴律
  identityˡ : ∀ {F G} {f : F ⇒ℱ G} → (id⇒ℱ ∘⇒ℱ f) ≈ℱ f
  identityˡ {f = f} .shapeTrans-≈ p = sym (pts-compat (morphismObj (f .out)) p)
  identityˡ .onPos-≈ _ = refl
  identityˡ .unfold-next-≈ _ = identityˡ

  identityʳ : ∀ {F G} {f : F ⇒ℱ G} → (f ∘⇒ℱ id⇒ℱ) ≈ℱ f
  identityʳ .shapeTrans-≈ _ = refl
  identityʳ .onPos-≈ _ = refl
  identityʳ .unfold-next-≈ _ = identityʳ

  assoc : ∀ {F G H I} {f : F ⇒ℱ G} {g : G ⇒ℱ H} {h : H ⇒ℱ I}
        → ((h ∘⇒ℱ g) ∘⇒ℱ f) ≈ℱ (h ∘⇒ℱ (g ∘⇒ℱ f))
  assoc .shapeTrans-≈ _ = refl
  assoc .onPos-≈ _ = refl
  assoc .unfold-next-≈ _ = assoc

  ∘-resp-≈ : ∀ {A B C : Cosmos C FC}
             {f h : B ⇒ℱ C} {g i : A ⇒ℱ B}
           → f ≈ℱ h → g ≈ℱ i → (f ∘⇒ℱ g) ≈ℱ (h ∘⇒ℱ i)
  ∘-resp-≈ {f = f} {h = h} {g = g} {i = i} eq-f eq-g .shapeTrans-≈ p =
    begin
      shapeTrans (f .out) (onPos (morphismObj (g .out)) p)
        ≡⟨ cong (λ q → shapeTrans (f .out) q) (eq-g .onPos-≈ p) ⟩
      shapeTrans (f .out) (onPos (morphismObj (i .out)) p)
        ≡⟨ eq-f .shapeTrans-≈ (onPos (morphismObj (i .out)) p) ⟩
      shapeTrans (h .out) (onPos (morphismObj (i .out)) p)
    ∎
  ∘-resp-≈ {f = f} {h = h} {g = g} {i = i} eq-f eq-g .onPos-≈ p =
    begin
      onPos (morphismObj (f .out)) (onPos (morphismObj (g .out)) p)
        ≡⟨ cong (λ q → onPos (morphismObj (f .out)) q) (eq-g .onPos-≈ p) ⟩
      onPos (morphismObj (f .out)) (onPos (morphismObj (i .out)) p)
        ≡⟨ eq-f .onPos-≈ (onPos (morphismObj (i .out)) p) ⟩
      onPos (morphismObj (h .out)) (onPos (morphismObj (i .out)) p)
    ∎
  ∘-resp-≈ {f = f} {h = h} {g = g} {i = i} eq-f eq-g .unfold-next-≈ s =
    ∘-resp-≈ {f = onunfold-next (f .out) s} {h = onunfold-next (h .out) s}
             {g = onunfold-next (g .out) s} {i = onunfold-next (i .out) s}
             (eq-f .unfold-next-≈ s) (eq-g .unfold-next-≈ s)

  -- The category with objects Cosmos and morphisms _⇒ℱ_
  -- 以 Cosmos 为对象、_⇒ℱ_ 为态射的范畴
  CosmosCategory : Category L (o ⊔ h ⊔ s ⊔ p) L
  CosmosCategory = record
    { Obj       = Cosmos C FC
    ; _⇒_       = _⇒ℱ_
    ; _≈_       = _≈ℱ_
    ; id        = id⇒ℱ
    ; _∘_       = _∘⇒ℱ_
    ; equiv     = record
      { refl  = ≈ℱ-refl
      ; sym   = ≈ℱ-sym
      ; trans = ≈ℱ-trans
      }
    ; ∘-resp-≈  = ∘-resp-≈
    ; assoc     = assoc
    ; sym-assoc = λ {f} {g} {h} → ≈ℱ-sym assoc
    ; identityˡ = identityˡ
    ; identityʳ = identityʳ
    ; identity² = λ {F} → identityˡ {f = id⇒ℱ {F = F}}
    }
