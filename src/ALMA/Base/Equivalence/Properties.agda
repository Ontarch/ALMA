------------------------------------------------------------------------
-- Generic properties of LayeredEqGen and its specialisation LayeredEq
--
-- A reflexive / symmetric / transitive layer makes LayeredEqGen itself
-- reflexive / symmetric / transitive, given three coherence conditions
-- relating obs-map to the three layer operations. LayeredEq is the
-- specialisation at constant observation, where all three coherences
-- reduce to refl.
--
-- LayeredEqGen 及其特化 LayeredEq 的通用性质
--
-- layer 自反 / 对称 / 传递的 LayeredEqGen 自身也自反 / 对称 / 传递，
-- 前提是三条相干性条件把 obs-map 与三种 layer 运算联系起来。
-- LayeredEq 是常数观察处的特化，三条相干性均退化为 refl。
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module ALMA.Base.Equivalence.Properties where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (module ≡-Reasoning)
open ≡-Reasoning
open import Relation.Binary.PropositionalEquality.Core using (trans; sym; cong; subst)
open import Relation.Binary.Structures using (IsEquivalence; IsPreorder)

open import ALMA.Base.IndexedMType using (Mᵢ)
open import ALMA.Base.Equivalence.Core using (LayeredEqGen; LayeredEq)

------------------------------------------------------------------------
-- Generic properties of LayeredEqGen
--
-- LayeredEqGen 的通用性质

module LayeredEqGen-Properties
    {a b c} {X : Set a}
    {Obs : X → Set b}
    {step : (x : X) → Obs x → X}
    {layer : X → X → Set c}
    {obs-map : (x y : X) → layer x y → Obs x → Obs y} where

  -- Coherence: obs-map along layer-refl fixes observations.
  --
  -- 相干性：沿 layer-refl 的 obs-map 固定观察。
  le-refl
    : (layer-refl : ∀ x → layer x x)
    → (obs-refl : ∀ x (s : Obs x) → obs-map x x (layer-refl x) s ≡ s)
    → ∀ x → LayeredEqGen Obs step layer obs-map x x
  le-refl layer-refl obs-refl x .Mᵢ.fst = layer-refl x
  le-refl layer-refl obs-refl x .Mᵢ.snd s
    rewrite (begin
      obs-map x x (layer-refl x) s
    ≡⟨ obs-refl x s ⟩
      s
    ∎)
    = le-refl layer-refl obs-refl (step x s)

  -- Coherence: obs-map along layer-sym cancels the reverse obs-map.
  --
  -- 相干性：沿 layer-sym 的 obs-map 抵消反向 obs-map。
  le-sym
    : (layer-sym : ∀ {x y} → layer x y → layer y x)
    → (obs-sym : ∀ {x y} (l : layer x y) (s : Obs y)
               → obs-map x y l (obs-map y x (layer-sym l) s) ≡ s)
    → ∀ {x y} → LayeredEqGen Obs step layer obs-map x y
              → LayeredEqGen Obs step layer obs-map y x
  le-sym layer-sym obs-sym {x} {y} p .Mᵢ.fst =
    layer-sym (p .Mᵢ.fst)
  le-sym layer-sym obs-sym {x} {y} p .Mᵢ.snd s =
    le-sym layer-sym obs-sym
      (subst (λ T → LayeredEqGen Obs step layer obs-map (step x s') T)
             (begin
                step y (obs-map x y l s')
              ≡⟨ cong (step y) (obs-sym {x} {y} l s) ⟩
                step y s
              ∎)
             (p .Mᵢ.snd s'))
    where
      l  = p .Mᵢ.fst
      s' = obs-map y x (layer-sym l) s

  -- Coherence: obs-map along layer-trans composes the two obs-maps.
  --
  -- 相干性：沿 layer-trans 的 obs-map 复合两个 obs-map。
  le-trans
    : (layer-trans : ∀ {x y z} → layer x y → layer y z → layer x z)
    → (obs-trans : ∀ {x y z} (l : layer x y) (m : layer y z) (s : Obs x)
                 → obs-map y z m (obs-map x y l s)
                   ≡ obs-map x z (layer-trans l m) s)
    → ∀ {x y z} → LayeredEqGen Obs step layer obs-map x y
                → LayeredEqGen Obs step layer obs-map y z
                → LayeredEqGen Obs step layer obs-map x z
  le-trans layer-trans obs-trans {x} {y} {z} p q .Mᵢ.fst =
    layer-trans (p .Mᵢ.fst) (q .Mᵢ.fst)
  le-trans layer-trans obs-trans {x} {y} {z} p q .Mᵢ.snd s =
    le-trans layer-trans obs-trans
      (p .Mᵢ.snd s)
      (subst (λ T → LayeredEqGen Obs step layer obs-map (step y s_y) T)
             (begin
                step z (obs-map y z l_yz (obs-map x y l_xy s))
              ≡⟨ cong (step z) (obs-trans l_xy l_yz s) ⟩
                step z (obs-map x z (layer-trans l_xy l_yz) s)
              ∎)
             (q .Mᵢ.snd s_y))
    where
      l_xy = p .Mᵢ.fst
      l_yz = q .Mᵢ.fst
      s_y  = obs-map x y l_xy s

  le-isPreorder
    : (layer-refl  : ∀ x → layer x x)
    → (layer-trans : ∀ {x y z} → layer x y → layer y z → layer x z)
    → (obs-refl  : ∀ x (obs : Obs x)
        → obs-map x x (layer-refl x) obs ≡ obs)
    → (obs-trans : ∀ {x y z} (l : layer x y) (m : layer y z) (obs : Obs x)
        → obs-map y z m (obs-map x y l obs)
        ≡ obs-map x z (layer-trans l m) obs)
    → IsPreorder _≡_ (LayeredEqGen Obs step layer obs-map)
  le-isPreorder layer-refl layer-trans obs-refl obs-trans = record
    { isEquivalence = record { refl = refl ; sym = sym ; trans = trans }
    ; reflexive = λ { {x} refl → le-refl layer-refl obs-refl x }
    ; trans = λ p q → le-trans layer-trans obs-trans p q
    }

  -- Bundled equivalence; the three coherences come alongside the
  -- IsEquivalence layer.
  --
  -- 打包等价关系；三条相干性与 IsEquivalence layer 一同提供。
  le-isEquivalence
    : (layer-eq : IsEquivalence layer)
    → (obs-refl : ∀ x (s : Obs x)
                → obs-map x x (IsEquivalence.refl layer-eq) s ≡ s)
    → (obs-sym : ∀ {x y} (l : layer x y) (s : Obs y)
               → obs-map x y l
                   (obs-map y x (IsEquivalence.sym layer-eq l) s) ≡ s)
    → (obs-trans : ∀ {x y z} (l : layer x y) (m : layer y z) (s : Obs x)
                 → obs-map y z m (obs-map x y l s)
                   ≡ obs-map x z (IsEquivalence.trans layer-eq l m) s)
    → IsEquivalence (LayeredEqGen Obs step layer obs-map)
  le-isEquivalence layer-eq obs-refl obs-sym obs-trans = record
    { refl  = λ {x} →
        le-refl (λ y → IsEquivalence.refl layer-eq {x = y}) obs-refl x
    ; sym   = le-sym (IsEquivalence.sym layer-eq) obs-sym
    ; trans = le-trans (IsEquivalence.trans layer-eq) obs-trans
    }

------------------------------------------------------------------------
-- Specialisation to LayeredEq
--
-- obs-map is the identity, so all three coherences reduce to refl.
--
-- 在 LayeredEq 处的特化
--
-- obs-map 为恒等，三条相干性均退化为 refl。

module LayeredEq-Equiv
    {a b c} {X : Set a} {Obs : Set b} {step : X → Obs → X}
    {layer : X → X → Set c}
    (layer-equiv : IsEquivalence layer) where

  open LayeredEqGen-Properties
    {X = X} {Obs = λ _ → Obs} {step = step} {layer = layer}
    {obs-map = λ _ _ _ o → o}

  LE-isEquivalence : IsEquivalence (LayeredEq Obs step layer)
  LE-isEquivalence =
    le-isEquivalence layer-equiv
      (λ _ _ → refl)
      (λ _ _ → refl)
      (λ _ _ _ → refl)
