------------------------------------------------------------------------
-- Position automorphisms on the carried M base
--
-- Two subst-free pieces: Part A, the algebraic position-permutation
-- group PosAutˢ over an arbitrary indexed type family (S , P), a
-- per-index permutation with a carried two-sided inverse and no
-- naturality field; Part B, the induced fibre action, where a position
-- permutation acts on edge fibres and the induced bijection is a
-- carried FiberAdjˢ. Self-fibre adjunctions form a group pointwise via
-- idAdjˢ / compAdjˢ / symAdjˢ, whose inverse laws are the carried η/ε.
--
-- 携带 M 底座上的位置自同构
--
-- 两块内容，均零 subst：A 部，任意索引类型族 (S , P) 上的代数位置置换群
-- PosAutˢ，即带携带双侧逆的逐索引置换，无自然性字段；B 部，诱导的纤维
-- 作用，位置置换作用于边纤维，诱导双射是携带的 FiberAdjˢ。自纤维伴随经
-- idAdjˢ / compAdjˢ / symAdjˢ 逐点成群，其逆律即携带的 η/ε。
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module Cosmos.M.ContainerAutomorphism where

open import Agda.Primitive using (Level; _⊔_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Sigma using (_,_)
open import Algebra.Bundles using (Group)
open import Relation.Binary.PropositionalEquality.Core using (cong; sym; trans)
open import Relation.Binary.PropositionalEquality.Properties using (module ≡-Reasoning)
open import Relation.Binary.Structures using (IsEquivalence)

open import Base.MCorr.Setoid using (EqOn; FiberAdjˢ; idAdjˢ; symAdjˢ; compAdjˢ)

------------------------------------------------------------------------
-- Part A
--
-- The algebraic position-permutation group.
--
-- A 部
--
-- 代数位置置换群。

module PositionPermutationGroup {s p : Level}
                                (S : Set s) (P : S → Set p) where

  -- No naturality field: positions at distinct shapes live in distinct
  -- fibres, related by a carried FiberAdjˢ (Part B), never by subst.
  --
  -- 无自然性字段：不同形状处的位置属于不同纤维，由携带的 FiberAdjˢ
  -- （B 部）联系，绝不 subst。
  record PosAutˢ : Set (s ⊔ p) where
    field
      τ       : (sh : S) → P sh → P sh
      τ⁻¹     : (sh : S) → P sh → P sh
      τ-τ⁻¹   : (sh : S) (q : P sh) → τ sh (τ⁻¹ sh q) ≡ q
      τ⁻¹-τ   : (sh : S) (q : P sh) → τ⁻¹ sh (τ sh q) ≡ q
  open PosAutˢ public

  idPosAutˢ : PosAutˢ
  idPosAutˢ = record
    { τ       = λ _ q → q
    ; τ⁻¹     = λ _ q → q
    ; τ-τ⁻¹   = λ _ _ → refl
    ; τ⁻¹-τ   = λ _ _ → refl
    }

  infixl 20 _∘PosAutˢ_
  _∘PosAutˢ_ : PosAutˢ → PosAutˢ → PosAutˢ
  φ ∘PosAutˢ ψ = record
    { τ       = λ sh q → τ φ sh (τ ψ sh q)
    ; τ⁻¹     = λ sh q → τ⁻¹ ψ sh (τ⁻¹ φ sh q)
    ; τ-τ⁻¹   = λ sh q →
        begin
          τ φ sh (τ ψ sh (τ⁻¹ ψ sh (τ⁻¹ φ sh q)))
            ≡⟨ cong (τ φ sh) (τ-τ⁻¹ ψ sh (τ⁻¹ φ sh q)) ⟩
          τ φ sh (τ⁻¹ φ sh q)
            ≡⟨ τ-τ⁻¹ φ sh q ⟩
          q
        ∎
    ; τ⁻¹-τ = λ sh q →
        begin
          τ⁻¹ ψ sh (τ⁻¹ φ sh (τ φ sh (τ ψ sh q)))
            ≡⟨ cong (τ⁻¹ ψ sh) (τ⁻¹-τ φ sh (τ ψ sh q)) ⟩
          τ⁻¹ ψ sh (τ ψ sh q)
            ≡⟨ τ⁻¹-τ ψ sh q ⟩
          q
        ∎
    }
    where open ≡-Reasoning

  -- Swap forward and backward maps and exchange the two round-trip
  -- laws.
  --
  -- 交换正反映射并对调两条往返律。
  invPosAutˢ : PosAutˢ → PosAutˢ
  invPosAutˢ φ = record
    { τ       = τ⁻¹ φ
    ; τ⁻¹     = τ φ
    ; τ-τ⁻¹   = λ sh q → τ⁻¹-τ φ sh q
    ; τ⁻¹-τ   = λ sh q → τ-τ⁻¹ φ sh q
    }

  infix 4 _≈PAˢ_
  _≈PAˢ_ : PosAutˢ → PosAutˢ → Set (s ⊔ p)
  φ ≈PAˢ ψ = ∀ (sh : S) (q : P sh) → τ φ sh q ≡ τ ψ sh q

  ≈PAˢ-isEquivalence : IsEquivalence _≈PAˢ_
  ≈PAˢ-isEquivalence = record
    { refl  = λ _ _ → refl
    ; sym   = λ eq sh q → sym (eq sh q)
    ; trans = λ eq₁ eq₂ sh q → trans (eq₁ sh q) (eq₂ sh q)
    }

  ∘PosAutˢ-resp-≈ : ∀ {φ φ' ψ ψ'} → φ ≈PAˢ φ' → ψ ≈PAˢ ψ'
                  → (φ ∘PosAutˢ ψ) ≈PAˢ (φ' ∘PosAutˢ ψ')
  ∘PosAutˢ-resp-≈ {φ} {φ'} {ψ} {ψ'} φ≈φ' ψ≈ψ' sh q =
    begin
      τ φ sh (τ ψ sh q)
        ≡⟨ cong (τ φ sh) (ψ≈ψ' sh q) ⟩
      τ φ sh (τ ψ' sh q)
        ≡⟨ φ≈φ' sh (τ ψ' sh q) ⟩
      τ φ' sh (τ ψ' sh q)
    ∎
    where open ≡-Reasoning

  -- The inverse permutation is uniquely determined by the forward map.
  --
  -- 逆置换由正向映射唯一确定。
  τ⁻¹-unique : {φ ψ : PosAutˢ} → φ ≈PAˢ ψ
             → (sh : S) (q : P sh) → τ⁻¹ φ sh q ≡ τ⁻¹ ψ sh q
  τ⁻¹-unique {φ} {ψ} φ≈ψ sh q =
    trans
      (sym (τ⁻¹-τ φ sh (τ⁻¹ φ sh q)))
      (trans
        (cong (τ⁻¹ φ sh) eq)
        (τ⁻¹-τ φ sh (τ⁻¹ ψ sh q)))
    where
      eq : τ φ sh (τ⁻¹ φ sh q) ≡ τ φ sh (τ⁻¹ ψ sh q)
      eq = trans
             (τ-τ⁻¹ φ sh q)
             (sym (trans (φ≈ψ sh (τ⁻¹ ψ sh q)) (τ-τ⁻¹ ψ sh q)))

  invPosAutˢ-cong : {φ ψ : PosAutˢ} → φ ≈PAˢ ψ
                  → invPosAutˢ φ ≈PAˢ invPosAutˢ ψ
  invPosAutˢ-cong {φ} {ψ} φ≈ψ sh q = τ⁻¹-unique {φ} {ψ} φ≈ψ sh q

  ∘PosAutˢ-assoc : ∀ φ ψ χ
                 → (φ ∘PosAutˢ ψ) ∘PosAutˢ χ ≈PAˢ φ ∘PosAutˢ (ψ ∘PosAutˢ χ)
  ∘PosAutˢ-assoc _ _ _ _ _ = refl

  ∘PosAutˢ-identityˡ : ∀ φ → idPosAutˢ ∘PosAutˢ φ ≈PAˢ φ
  ∘PosAutˢ-identityˡ _ _ _ = refl

  ∘PosAutˢ-identityʳ : ∀ φ → φ ∘PosAutˢ idPosAutˢ ≈PAˢ φ
  ∘PosAutˢ-identityʳ _ _ _ = refl

  invPosAutˢ-left-inverse : ∀ φ → invPosAutˢ φ ∘PosAutˢ φ ≈PAˢ idPosAutˢ
  invPosAutˢ-left-inverse φ sh q = τ⁻¹-τ φ sh q

  invPosAutˢ-right-inverse : ∀ φ → φ ∘PosAutˢ invPosAutˢ φ ≈PAˢ idPosAutˢ
  invPosAutˢ-right-inverse φ sh q = τ-τ⁻¹ φ sh q

  ----------------------------------------------------------------------
  -- The group PosAutˢ
  --
  -- 群 PosAutˢ

  posAutˢGroup : Group (s ⊔ p) (s ⊔ p)
  posAutˢGroup = record
    { Carrier = PosAutˢ
    ; _≈_     = _≈PAˢ_
    ; _∙_     = _∘PosAutˢ_
    ; ε       = idPosAutˢ
    ; _⁻¹     = invPosAutˢ
    ; isGroup = record
        { isMonoid = record
            { isSemigroup = record
                { isMagma = record
                    { isEquivalence = ≈PAˢ-isEquivalence
                    ; ∙-cong = λ {x y u v} x≈y u≈v →
                        ∘PosAutˢ-resp-≈ {x} {y} {u} {v} x≈y u≈v
                    }
                ; assoc = ∘PosAutˢ-assoc
                }
            ; identity = ( ∘PosAutˢ-identityˡ , ∘PosAutˢ-identityʳ )
            }
        ; inverse = ( invPosAutˢ-left-inverse , invPosAutˢ-right-inverse )
        ; ⁻¹-cong = λ {x y} x≈y → invPosAutˢ-cong {x} {y} x≈y
        }
    }

------------------------------------------------------------------------
-- Part B
--
-- The group of carried self-fibre adjunctions. A self-fibre adjunction
-- is a carried bijection of P to itself; the inverse laws are the
-- carried η/ε, so no equality is eliminated and no naturality / subst
-- appears.
--
-- B 部
--
-- 携带自纤维伴随的群。自纤维伴随即 P 到自身的携带双射；逆律即携带的
-- η/ε，故不消去任何等式，也不出现自然性 / subst。

module FibreSelfAdjunctionGroup {c ℓ : Level} {P : Set c}
                               (E : EqOn {ℓ = ℓ} P) where
  open EqOn E using (_≈_) renaming (refl to ≈refl)

  SelfAdj : Set (c ⊔ ℓ)
  SelfAdj = FiberAdjˢ E E

  idSelf : SelfAdj
  idSelf = idAdjˢ E

  compSelf : SelfAdj → SelfAdj → SelfAdj
  compSelf a₁ a₂ = compAdjˢ E E E a₁ a₂

  invSelf : SelfAdj → SelfAdj
  invSelf = symAdjˢ

  -- Group laws on the forward direction: inverse laws are the carried
  -- ε/η, and associativity / identity are definitional because
  -- composition of the to-maps is ordinary function composition.
  --
  -- 正向上的群律：逆律即携带的 ε/η；结合律与单位律是定义性的，因为
  -- to 映射的复合即普通函数复合。
  comp-identityʳ-to : (a : SelfAdj) (p : P)
                    → FiberAdjˢ.to (compSelf a idSelf) p ≈ FiberAdjˢ.to a p
  comp-identityʳ-to a p = ≈refl

  comp-identityˡ-to : (a : SelfAdj) (p : P)
                    → FiberAdjˢ.to (compSelf idSelf a) p ≈ FiberAdjˢ.to a p
  comp-identityˡ-to a p = ≈refl

  comp-inverseˡ-to : (a : SelfAdj) (r : P)
                   → FiberAdjˢ.to (compSelf a (invSelf a)) r ≈ r
  comp-inverseˡ-to a r = FiberAdjˢ.η a r

  comp-inverseʳ-to : (a : SelfAdj) (p : P)
                   → FiberAdjˢ.to (compSelf (invSelf a) a) p ≈ p
  comp-inverseʳ-to a p = FiberAdjˢ.ε a p

  comp-assoc-to : (a b c : SelfAdj) (p : P)
                → FiberAdjˢ.to (compSelf (compSelf a b) c) p
                ≈ FiberAdjˢ.to (compSelf a (compSelf b c)) p
  comp-assoc-to a b c p = ≈refl
