------------------------------------------------------------------------
-- Position automorphisms of a container C and their induced
-- endomorphisms on Cosmos objects over the constant functor returning C
-- 容器 C 的位置自同构及其在基于常值函子返回 C 的 Cosmos 对象上
-- 诱导的自态射
--
-- Defines PosAut (position automorphisms with naturality), its group
-- structure under composition (posAutGroup), and the map aut→⇒ℱ sending
-- each position automorphism to a structured simulation x ⇒ℱ x. Proves
-- aut→⇒ℱ is a group homomorphism (aut-id, aut-comp, aut-inv), injective
-- (aut-injective), and respects _≈PA_ (aut→⇒ℱ-resp-≈)
-- 定义 PosAut（具有自然性的位置自同构）、其复合下的群结构
-- （posAutGroup），以及将每个位置自同构映射为结构化模拟 x ⇒ℱ x 的
-- 映射 aut→⇒ℱ。证明 aut→⇒ℱ 是群同态（aut-id、aut-comp、aut-inv）、
-- 单射（aut-injective），并保持 _≈PA_（aut→⇒ℱ-resp-≈）
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module ALMA.SecondPass.ContainerAutomorphism where

open import Agda.Primitive using (Level; _⊔_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Sigma using (_,_)
open import Algebra.Bundles using (Group)
open import Relation.Binary.PropositionalEquality.Core using (cong; sym; trans; subst)
open import Relation.Binary.PropositionalEquality.Properties using (module ≡-Reasoning)
open import Relation.Binary.Structures using (IsEquivalence)
open import Data.Container.Core using (Container; Shape; Position)

open import Categories.Category.Core using (Category)
open import Categories.Functor.Core using (Functor)
open import Categories.Functor.Construction.Constant using (const)
open import Categories.Functor using (id)

open import ALMA.Cosmos.ContCategory using (ContCat)
open import ALMA.Cosmos.ContCategoryLemmas using (actSOf; actPOf)
open import ALMA.SecondPass.Unfolding using (Unfolding)
open import ALMA.SecondPass.MorphismMorphism using (actP-from-S)
open import ALMA.SecondPass.Cosmos using (Cosmos; out; _⇒ℱ_; UnitCat; id⇒ℱ; _∘⇒ℱ_)
open import ALMA.SecondPass.CosmosCategory using (_≈ℱ_)

-- Parameterised by a container C
-- 以容器 C 为参数
module _ {s p : Level} (C : Container s p) where
  open Container C

  private
    -- The level of the terminal category used as base category
    -- 用作基范畴的终范畴的层级
    ℓ : Level
    ℓ = s ⊔ p

    C₀ : Category ℓ ℓ ℓ
    C₀ = UnitCat {ℓ}

  private
    -- Constant functor picking out the container C
    -- 选取容器 C 的常值函子
    constFC : Functor C₀ (ContCat s p)
    constFC = const C

  -- Position automorphisms
  -- 位置自同构

  -- Position automorphisms with explicit shape parameters to avoid
  -- metavariable issues when constructing the standard library Group.
  -- 带有显式形状参数的位置自同构，以避免在构造标准库 Group 时
  -- 出现元变量推断问题。
  record PosAut : Set (s ⊔ p) where
    field
      -- Forward position map
      -- 正向位置映射
      τ      : (s : Shape C) → Position C s → Position C s
      -- Inverse position map
      -- 逆向位置映射
      τ⁻¹    : (s : Shape C) → Position C s → Position C s
      -- τ⁻¹ is a right inverse of τ
      -- τ⁻¹ 是 τ 的右逆
      τ-τ⁻¹  : (s : Shape C) (p : Position C s) → τ s (τ⁻¹ s p) ≡ p
      -- τ⁻¹ is a left inverse of τ
      -- τ⁻¹ 是 τ 的左逆
      τ⁻¹-τ  : (s : Shape C) (p : Position C s) → τ⁻¹ s (τ s p) ≡ p
      -- Naturality: τ commutes with substitution along shape equality
      -- 自然性：τ 与沿形状等式的替换交换
      τ-nat  : {s t : Shape C} (e : s ≡ t) (p : Position C s)
             → τ t (subst (Position C) e p) ≡ subst (Position C) e (τ s p)

  open PosAut

  -- Identity position automorphism
  -- 恒等位置自同构
  idPosAut : PosAut
  idPosAut = record
    { τ     = λ _ p → p
    ; τ⁻¹   = λ _ p → p
    ; τ-τ⁻¹ = λ _ _ → refl
    ; τ⁻¹-τ = λ _ _ → refl
    ; τ-nat = λ _ _ → refl
    }

  -- Composition of position automorphisms
  -- 位置自同构的复合
  infixl 20 _∘PosAut_
  _∘PosAut_ : PosAut → PosAut → PosAut
  φ ∘PosAut ψ = record
    { τ     = λ s p → τ φ s (τ ψ s p)
    ; τ⁻¹   = λ s p → τ⁻¹ ψ s (τ⁻¹ φ s p)
    ; τ-τ⁻¹ = λ s p →
        begin
          τ φ s (τ ψ s (τ⁻¹ ψ s (τ⁻¹ φ s p)))
            ≡⟨ cong (τ φ s) (τ-τ⁻¹ ψ s (τ⁻¹ φ s p)) ⟩
          τ φ s (τ⁻¹ φ s p)
            ≡⟨ τ-τ⁻¹ φ s p ⟩
          p
        ∎
    ; τ⁻¹-τ = λ s p →
        begin
          τ⁻¹ ψ s (τ⁻¹ φ s (τ φ s (τ ψ s p)))
            ≡⟨ cong (τ⁻¹ ψ s) (τ⁻¹-τ φ s (τ ψ s p)) ⟩
          τ⁻¹ ψ s (τ ψ s p)
            ≡⟨ τ⁻¹-τ ψ s p ⟩
          p
        ∎
    ; τ-nat = λ {s} {t} e p →
        begin
          τ φ t (τ ψ t (subst (Position C) e p))
            ≡⟨ cong (τ φ t) (τ-nat ψ e p) ⟩
          τ φ t (subst (Position C) e (τ ψ s p))
            ≡⟨ τ-nat φ e (τ ψ s p) ⟩
          subst (Position C) e (τ φ s (τ ψ s p))
        ∎
    }
    where open ≡-Reasoning

  -- Inverse of a position automorphism
  -- 位置自同构的逆
  invPosAut : PosAut → PosAut
  invPosAut φ = record
    { τ     = τ⁻¹ φ
    ; τ⁻¹   = τ φ
    ; τ-τ⁻¹ = λ s p → τ⁻¹-τ φ s p
    ; τ⁻¹-τ = λ s p → τ-τ⁻¹ φ s p
    ; τ-nat = λ {s} {t} e p →
        begin
          τ⁻¹ φ t (subst (Position C) e p)
            ≡⟨ cong (τ⁻¹ φ t) (cong (subst (Position C) e) (sym (τ-τ⁻¹ φ s p))) ⟩
          τ⁻¹ φ t (subst (Position C) e (τ φ s (τ⁻¹ φ s p)))
            ≡⟨ cong (τ⁻¹ φ t) (sym (τ-nat φ e (τ⁻¹ φ s p))) ⟩
          τ⁻¹ φ t (τ φ t (subst (Position C) e (τ⁻¹ φ s p)))
            ≡⟨ τ⁻¹-τ φ t (subst (Position C) e (τ⁻¹ φ s p)) ⟩
          subst (Position C) e (τ⁻¹ φ s p)
        ∎
    }
    where open ≡-Reasoning

  -- Equivalence and Group structure
  -- 等价关系与群结构

  -- Equivalence of position automorphisms: pointwise equality of the
  -- forward position maps.
  -- 位置自同构的等价：正向位置映射的逐点相等。
  infix 4 _≈PA_
  _≈PA_ : PosAut → PosAut → Set (s ⊔ p)
  φ ≈PA ψ = ∀ (s : Shape C) (p : Position C s) → τ φ s p ≡ τ ψ s p

  -- Equivalence relation for _≈PA_
  -- _≈PA_ 的等价关系证明
  ≈PA-isEquivalence : IsEquivalence _≈PA_
  ≈PA-isEquivalence = record
    { refl  = λ _ _ → refl
    ; sym   = λ eq s p → sym (eq s p)
    ; trans = λ eq₁ eq₂ s p → trans (eq₁ s p) (eq₂ s p)
    }

  -- Composition respects the equivalence _≈PA_
  -- 复合操作保持等价 _≈PA_
  ∘PosAut-resp-≈ : ∀ {φ φ' ψ ψ'} → φ ≈PA φ' → ψ ≈PA ψ'
                 → (φ ∘PosAut ψ) ≈PA (φ' ∘PosAut ψ')
  ∘PosAut-resp-≈ {φ} {φ'} {ψ} {ψ'} φ≈φ' ψ≈ψ' s p =
    begin
      τ φ s (τ ψ s p)
        ≡⟨ cong (τ φ s) (ψ≈ψ' s p) ⟩
      τ φ s (τ ψ' s p)
        ≡⟨ φ≈φ' s (τ ψ' s p) ⟩
      τ φ' s (τ ψ' s p)
    ∎
    where open ≡-Reasoning

  -- The inverse maps are uniquely determined by the forward maps.
  -- 逆映射由正向映射唯一确定。
  τ⁻¹-unique : {φ ψ : PosAut} → φ ≈PA ψ
             → (s : Shape C) (p : Position C s) → τ⁻¹ φ s p ≡ τ⁻¹ ψ s p
  τ⁻¹-unique {φ} {ψ} φ≈ψ s p =
    begin
      τ⁻¹ φ s p
        ≡⟨ sym (τ⁻¹-τ φ s (τ⁻¹ φ s p)) ⟩
      τ⁻¹ φ s (τ φ s (τ⁻¹ φ s p))
        ≡⟨ cong (τ⁻¹ φ s) eq ⟩
      τ⁻¹ φ s (τ φ s (τ⁻¹ ψ s p))
        ≡⟨ τ⁻¹-τ φ s (τ⁻¹ ψ s p) ⟩
      τ⁻¹ ψ s p
    ∎
    where
      open ≡-Reasoning
      eq : τ φ s (τ⁻¹ φ s p) ≡ τ φ s (τ⁻¹ ψ s p)
      eq = begin
        τ φ s (τ⁻¹ φ s p)
          ≡⟨ τ-τ⁻¹ φ s p ⟩
        p
          ≡⟨ sym (trans (φ≈ψ s (τ⁻¹ ψ s p)) (τ-τ⁻¹ ψ s p)) ⟩
        τ φ s (τ⁻¹ ψ s p)
        ∎

  -- Inverse operation respects equivalence
  -- 逆操作保持等价
  invPosAut-cong : {φ ψ : PosAut} → φ ≈PA ψ → invPosAut φ ≈PA invPosAut ψ
  invPosAut-cong {φ} {ψ} φ≈ψ s p = τ⁻¹-unique {φ} {ψ} φ≈ψ s p

  -- Group laws for PosAut (up to _≈PA_)
  -- PosAut 的群公理（模 _≈PA_）
  ∘PosAut-assoc : ∀ φ ψ χ → (φ ∘PosAut ψ) ∘PosAut χ ≈PA φ ∘PosAut (ψ ∘PosAut χ)
  ∘PosAut-assoc φ ψ χ s p = refl

  ∘PosAut-identityˡ : ∀ φ → idPosAut ∘PosAut φ ≈PA φ
  ∘PosAut-identityˡ φ s p = refl

  ∘PosAut-identityʳ : ∀ φ → φ ∘PosAut idPosAut ≈PA φ
  ∘PosAut-identityʳ φ s p = refl

  invPosAut-left-inverse : ∀ φ → invPosAut φ ∘PosAut φ ≈PA idPosAut
  invPosAut-left-inverse φ s p = τ⁻¹-τ φ s p

  invPosAut-right-inverse : ∀ φ → φ ∘PosAut invPosAut φ ≈PA idPosAut
  invPosAut-right-inverse φ s p = τ-τ⁻¹ φ s p

  -- Standard library Group bundle
  -- 标准库 Group（群）打包
  posAutGroup : Group (s ⊔ p) (s ⊔ p)
  posAutGroup = record
    { Carrier = PosAut
    ; _≈_     = _≈PA_
    ; _∙_     = _∘PosAut_
    ; ε       = idPosAut
    ; _⁻¹     = invPosAut
    ; isGroup = record
        { isMonoid = record
            { isSemigroup = record
                { isMagma = record
                    { isEquivalence = ≈PA-isEquivalence
                    ; ∙-cong = λ {x y u v} x≈y u≈v → ∘PosAut-resp-≈ {x} {y} {u} {v} x≈y u≈v
                    }
                ; assoc = ∘PosAut-assoc
                }
            ; identity = (∘PosAut-identityˡ , ∘PosAut-identityʳ)
            }
        ; inverse = (invPosAut-left-inverse , invPosAut-right-inverse)
        ; ⁻¹-cong = λ {x y} x≈y → invPosAut-cong {x} {y} x≈y
        }
    }

  -- Constant functor helpers
  -- 常值函子辅助引理

  -- Lemma: the action of the constant functor on positions is identity
  -- 引理：常值函子在位置上的作用是恒等
  actPOf-const : ∀ {A B} (f : Category._⇒_ C₀ A B) (s : Shape C)
                 (q : Position C s) → actPOf constFC f s q ≡ q
  actPOf-const _ _ _ = refl

  -- Lemma: actP-from-S for the constant functor and id shape functor
  -- simplifies to a substitution
  -- 引理：常值函子与恒等形状函子的 actP-from-S 简化为替换
  actP-from-S-const : ∀ {A B} (f : Category._⇒_ C₀ A B) (s t : Shape C)
                      (p : actSOf constFC f s ≡ t) (q : Position C t)
                    → actP-from-S constFC constFC id f p q
                      ≡ subst (Position C) (sym p) q
  actP-from-S-const _ _ _ refl _ = refl

  -- Induced structured simulation and homomorphism properties
  -- 诱导的结构化模拟及同态性质

  -- Canonical structured simulation induced by a position automorphism
  -- 位置自同构诱导的典范结构化模拟
  aut→⇒ℱ : PosAut → ∀ (x : Cosmos C₀ constFC) → x ⇒ℱ x
  aut→⇒ℱ φ x .out = record
    { shapeTrans  = λ {A} {s} p → Unfolding.pos-to-shape (out x) s (τ φ s p)
    ; morphismObj = record
        { onPos      = λ {A} {s} p → τ φ s p
        ; pts-compat = λ _ → refl
        }
    ; morphismMor = record
        { onActP = λ f {s} {t} p q →
            begin
              τ φ s (actPOf constFC f s (subst (Position C) (sym p) q))
                ≡⟨ cong (τ φ s) (actPOf-const f s _) ⟩
              τ φ s (subst (Position C) (sym p) q)
                ≡⟨ τ-nat φ (sym p) q ⟩
              subst (Position C) (sym p) (τ φ t q)
                ≡⟨ sym (actP-from-S-const f s t p (τ φ t q)) ⟩
              actP-from-S constFC constFC id f p (τ φ t q)
            ∎
        }
    ; onunfold-next = λ {A} s → aut→⇒ℱ φ (Unfolding.unfold-next (out x) s)
    }
    where open ≡-Reasoning

  -- Identity homomorphism property
  -- 恒等同态性质
  aut-id : (x : Cosmos C₀ constFC) → aut→⇒ℱ idPosAut x ≈ℱ id⇒ℱ
  aut-id x ._≈ℱ_.shapeTrans-≈ _ = refl
  aut-id x ._≈ℱ_.onPos-≈ _ = refl
  aut-id x ._≈ℱ_.unfold-next-≈ s = aut-id (Unfolding.unfold-next (out x) s)

  -- Composition homomorphism property
  -- 复合同态性质
  aut-comp : (φ ψ : PosAut) (x : Cosmos C₀ constFC)
           → aut→⇒ℱ (φ ∘PosAut ψ) x ≈ℱ ((aut→⇒ℱ φ x) ∘⇒ℱ (aut→⇒ℱ ψ x))
  aut-comp φ ψ x ._≈ℱ_.shapeTrans-≈ _ = refl
  aut-comp φ ψ x ._≈ℱ_.onPos-≈ _ = refl
  aut-comp φ ψ x ._≈ℱ_.unfold-next-≈ s = aut-comp φ ψ (Unfolding.unfold-next (out x) s)

  -- Inverse homomorphism property
  -- 逆同态性质
  aut-inv : (φ : PosAut) (x : Cosmos C₀ constFC)
          → ((aut→⇒ℱ (invPosAut φ) x) ∘⇒ℱ (aut→⇒ℱ φ x)) ≈ℱ id⇒ℱ
  aut-inv φ x ._≈ℱ_.shapeTrans-≈ {s = s} p =
    cong (Unfolding.pos-to-shape (out x) s) (τ⁻¹-τ φ s p)
  aut-inv φ x ._≈ℱ_.onPos-≈ {s = s} p = τ⁻¹-τ φ s p
  aut-inv φ x ._≈ℱ_.unfold-next-≈ s = aut-inv φ (Unfolding.unfold-next (out x) s)

  -- The induced map respects equivalence
  -- 诱导映射保持等价
  aut→⇒ℱ-resp-≈ : {φ ψ : PosAut} (x : Cosmos C₀ constFC)
                → φ ≈PA ψ → aut→⇒ℱ φ x ≈ℱ aut→⇒ℱ ψ x
  aut→⇒ℱ-resp-≈ {φ} {ψ} x φ≈ψ ._≈ℱ_.shapeTrans-≈ {s = s} p =
    cong (Unfolding.pos-to-shape (out x) s) (φ≈ψ s p)
  aut→⇒ℱ-resp-≈ {φ} {ψ} x φ≈ψ ._≈ℱ_.onPos-≈ {s = s} p = φ≈ψ s p
  aut→⇒ℱ-resp-≈ {φ} {ψ} x φ≈ψ ._≈ℱ_.unfold-next-≈ s =
    aut→⇒ℱ-resp-≈ (Unfolding.unfold-next (out x) s) φ≈ψ

  -- Injectivity of aut→⇒ℱ with respect to _≈PA_ and _≈ℱ_.
  -- If the induced simulations are ≈ℱ‑equivalent, then the original
  -- position automorphisms are pointwise equal on positions.
  -- aut→⇒ℱ 相对于 _≈PA_ 和 _≈ℱ_ 的单射性：
  -- 若诱导的模拟 ≈ℱ‑等价，则原位置自同构在位置上逐点相等。
  aut-injective : {φ ψ : PosAut} (x : Cosmos C₀ constFC)
                → aut→⇒ℱ φ x ≈ℱ aut→⇒ℱ ψ x → φ ≈PA ψ
  aut-injective x eq s p = _≈ℱ_.onPos-≈ eq p
