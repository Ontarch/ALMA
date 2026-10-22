------------------------------------------------------------------------
-- Subst-transport and the adjunction bridge
--
-- Three modules: SubstTransport-Right (pointwise equality with
-- target-side transport, projection side, posR), SubstTransport-Left
-- (pointwise equality with source-side transport, embedding side,
-- posL), and SubstTransport-Adjoint (bridge: under posL ⊣ posR the two
-- layer relations interderive). These lift the fibre-wise adjunction
-- skeleton _⊣_ from Core to concrete same-layer relations on F.
--
-- subst 传输与伴随桥接
--
-- 三个模块：SubstTransport-Right（逐点相等 + 目标侧传输，投影侧，
-- posR）、SubstTransport-Left（逐点相等 + 源侧传输，嵌入侧，posL）、
-- 以及 SubstTransport-Adjoint（桥接：在 posL ⊣ posR 下两个同层关系
-- 互推）。这些模块把 Core 中的纤维伴随骨架 _⊣_ 提升为 F 上的具体
-- 同层关系。
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module Equivalence.SubstTransport where

open import Agda.Primitive using (Level; _⊔_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality.Core using (sym; trans; cong; subst)
open import Relation.Binary.Structures using (IsEquivalence)
open import Relation.Binary.PropositionalEquality.Properties using
  (subst-subst; subst-subst-sym; subst-sym-subst; module ≡-Reasoning)
open ≡-Reasoning

open import Equivalence.Core using (_⊣_)

module _ {a b c d e : Level} {S : Set a} {T : Set c} (P : T → Set b)
         (R : S → Set d) {F : Set e} (shape : F → S → T) where

  ----------------------------------------------------------------------
  -- Pointwise equality with target-side transport
  --
  -- Shapes agree, and pos-values agree after transporting the input
  -- along the shape equality (via posR).
  --
  -- 逐点相等 + 目标侧传输
  --
  -- shape 一致，且把输入沿 shape 等式传输后 pos 值一致（经 posR）。

  module SubstTransport-Right
      (pos : (f : F) → ∀ {s : S} → P (shape f s) → R s)
    where

    record _≈sr_ (f g : F) : Set (a ⊔ b ⊔ c ⊔ d) where
      field
        shape-eq    : ∀ s → shape f s ≡ shape g s
        position-eq : ∀ s (q : P (shape f s))
                    → pos f q ≡ pos g (subst P (shape-eq s) q)

    open _≈sr_

    ≈sr-refl : ∀ {f} → f ≈sr f
    ≈sr-refl = record
      { shape-eq    = λ _ → refl
      ; position-eq = λ _ _ → refl
      }

    -- Symmetry: invert shape-eq and absorb the two subst round-trips
    -- via subst-subst-sym.
    --
    -- 对称：反转 shape-eq，用 subst-subst-sym 吸收两个 subst 往返。
    ≈sr-sym : ∀ {f g} → f ≈sr g → g ≈sr f
    ≈sr-sym {f} {g} p = record
      { shape-eq    = λ s → sym (p .shape-eq s)
      ; position-eq = λ s q →
          let e = p .shape-eq s
          in begin
            pos g q
              ≡⟨ cong (pos g) (sym (subst-subst-sym {P = P} e {p = q})) ⟩
            pos g (subst P e (subst P (sym e) q))
              ≡⟨ sym (p .position-eq s (subst P (sym e) q)) ⟩
            pos f (subst P (sym e) q)
            ∎
      }

    -- Transitivity: chain the two shape equalities, transport r
    -- through e₁ first, and merge the two subst steps via subst-subst.
    --
    -- 传递：串联两个 shape 等式，先沿 e₁ 传输 r，再用 subst-subst
    -- 合并两个 subst 步骤。
    ≈sr-trans : ∀ {f g h} → f ≈sr g → g ≈sr h → f ≈sr h
    ≈sr-trans {f} {g} {h} p q = record
      { shape-eq    = λ s → trans (p .shape-eq s) (q .shape-eq s)
      ; position-eq = λ s r →
          let e₁ = p .shape-eq s
              e₂ = q .shape-eq s
              r₁ = subst P e₁ r
          in begin
            pos f r
              ≡⟨ p .position-eq s r ⟩
            pos g r₁
              ≡⟨ q .position-eq s r₁ ⟩
            pos h (subst P e₂ r₁)
              ≡⟨ cong (pos h) (subst-subst {P = P} e₁ {y≡z = e₂} {p = r}) ⟩
            pos h (subst P (trans e₁ e₂) r)
            ∎
      }

    ≈sr-isEquivalence : IsEquivalence _≈sr_
    ≈sr-isEquivalence = record
      { refl  = ≈sr-refl
      ; sym   = ≈sr-sym
      ; trans = ≈sr-trans
      }

    module ≈sr-Reasoning where
      open import Relation.Binary.Reasoning.Setoid (record
        { Carrier       = F
        ; _≈_           = _≈sr_
        ; isEquivalence = ≈sr-isEquivalence
        }) public

  ----------------------------------------------------------------------
  -- Pointwise equality with source-side transport
  --
  -- Dual to SubstTransport-Right: the transport is applied to the
  -- output rather than the input (via posL).
  --
  -- 逐点相等 + 源侧传输
  --
  -- 与 SubstTransport-Right 对偶：传输施加在输出而非输入上
  -- （经 posL）。

  module SubstTransport-Left
      (pos : (f : F) → ∀ {s : S} → R s → P (shape f s))
    where

    record _≈sl_ (f g : F) : Set (a ⊔ b ⊔ c ⊔ d) where
      field
        shape-eq    : ∀ s → shape f s ≡ shape g s
        position-eq : ∀ s (q : R s)
                    → subst P (shape-eq s) (pos f q) ≡ pos g q

    open _≈sl_

    ≈sl-refl : ∀ {f} → f ≈sl f
    ≈sl-refl = record
      { shape-eq    = λ _ → refl
      ; position-eq = λ _ _ → refl
      }

    -- Symmetry: invert shape-eq and collapse the two subst round-trips
    -- via subst-sym-subst.
    --
    -- 对称：反转 shape-eq，用 subst-sym-subst 折叠两个 subst 往返。
    ≈sl-sym : ∀ {f g} → f ≈sl g → g ≈sl f
    ≈sl-sym {f} {g} p = record
      { shape-eq    = λ s → sym (p .shape-eq s)
      ; position-eq = λ s q →
          let e = p .shape-eq s
          in begin
            subst P (sym e) (pos g q)
              ≡⟨ sym (cong (subst P (sym e)) (p .position-eq s q)) ⟩
            subst P (sym e) (subst P e (pos f q))
              ≡⟨ subst-sym-subst {P = P} e {p = pos f q} ⟩
            pos f q
            ∎
      }

    -- Transitivity: split the composed transport via subst-subst,
    -- then chain the two position equalities.
    --
    -- 传递：用 subst-subst 拆分复合传输，再串联两个 position 等式。
    ≈sl-trans : ∀ {f g h} → f ≈sl g → g ≈sl h → f ≈sl h
    ≈sl-trans {f} {g} {h} p q = record
      { shape-eq    = λ s → trans (p .shape-eq s) (q .shape-eq s)
      ; position-eq = λ s r →
          let e₁ = p .shape-eq s
              e₂ = q .shape-eq s
          in begin
            subst P (trans e₁ e₂) (pos f r)
              ≡⟨ sym (subst-subst {P = P} e₁ {y≡z = e₂} {p = pos f r}) ⟩
            subst P e₂ (subst P e₁ (pos f r))
              ≡⟨ cong (subst P e₂) (p .position-eq s r) ⟩
            subst P e₂ (pos g r)
              ≡⟨ q .position-eq s r ⟩
            pos h r
            ∎
      }

    ≈sl-isEquivalence : IsEquivalence _≈sl_
    ≈sl-isEquivalence = record
      { refl  = ≈sl-refl
      ; sym   = ≈sl-sym
      ; trans = ≈sl-trans
      }

    module ≈sl-Reasoning where
      open import Relation.Binary.Reasoning.Setoid (record
        { Carrier       = F
        ; _≈_           = _≈sl_
        ; isEquivalence = ≈sl-isEquivalence
        }) public

  ----------------------------------------------------------------------
  -- Adjunction bridge
  --
  -- Under posL ⊣ posR, _≈R_ (from posR) and _≈L_ (from posL)
  -- interderive at the same shape-equality: each determines the other.
  --
  -- 伴随桥接
  --
  -- 在 posL ⊣ posR 下，_≈R_（由 posR 给出）与 _≈L_（由 posL 给出）
  -- 在同一 shape 等式下互推：彼此互相确定。

  module SubstTransport-Adjoint
      (posL : (f : F) → ∀ {s : S} → R s → P (shape f s))
      (posR : (f : F) → ∀ {s : S} → P (shape f s) → R s)
      (adj : _⊣_ P R shape posL posR)
    where

    unit   : ∀ f {s} (r : R s) → posR f (posL f r) ≡ r
    unit   = proj₁ adj

    counit : ∀ f {s} (p : P (shape f s)) → posL f (posR f p) ≡ p
    counit = proj₂ adj

    open SubstTransport-Right posR using (_≈sr_)
    open SubstTransport-Left  posL using (_≈sl_)

    -- _≈R_ implies _≈L_: apply _≈R_'s position-eq at posL f r, then
    -- collapse the g-side round-trip using counit and unit.
    --
    -- _≈R_ 蕴含 _≈L_：先在 posL f r 处应用 _≈R_ 的 position-eq，
    -- 再用 counit 与 unit 折叠 g 侧往返。
    ≈R→≈L : ∀ {f g} → f ≈sr g → f ≈sl g
    ≈R→≈L {f} {g} p = record
      { shape-eq    = _≈sr_.shape-eq p
      ; position-eq = λ s r →
          let e  = _≈sr_.shape-eq p s
              h₁ = _≈sr_.position-eq p s (posL f r)
              h₂ = unit f r
              h₃ = counit g (subst P e (posL f r))
          in begin
            subst P e (posL f r)
              ≡⟨ sym h₃ ⟩
            posL g (posR g (subst P e (posL f r)))
              ≡⟨ cong (posL g) (trans (sym h₁) h₂) ⟩
            posL g r
            ∎
      }

    -- _≈L_ implies _≈R_: dual to ≈R→≈L.
    --
    -- _≈L_ 蕴含 _≈R_：与 ≈R→≈L 对偶。
    ≈L→≈R : ∀ {f g} → f ≈sl g → f ≈sr g
    ≈L→≈R {f} {g} p = record
      { shape-eq    = _≈sl_.shape-eq p
      ; position-eq = λ s q →
          let e  = _≈sl_.shape-eq p s
              h₁ = _≈sl_.position-eq p s (posR f q)
              h₂ = counit f q
              h₃ = unit g (posR f q)
          in begin
            posR f q
              ≡⟨ sym h₃ ⟩
            posR g (posL g (posR f q))
              ≡⟨ cong (posR g) (trans (sym h₁) (cong (subst P e) h₂)) ⟩
            posR g (subst P e q)
            ∎
      }

    ≈R↔≈L : ∀ {f g} → (f ≈sr g → f ≈sl g) × (f ≈sl g → f ≈sr g)
    ≈R↔≈L = ≈R→≈L , ≈L→≈R
