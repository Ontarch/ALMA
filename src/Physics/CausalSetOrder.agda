------------------------------------------------------------------------
-- Bridge: combinatorial causal sets land in the causal order skeleton
--
-- A causal set (Fin n, _≺_) is turned into an edge-family system by
--   I = Fin n,  A = const ⊤,  E i _ j = T (i ≺ j).
-- The positive reachability _⇝⁺_ of CausalOrder then coincides with
-- the transitive closure of _≺_, and IsCausalSet entails Acyclic.
--
-- 桥接：组合因果集落入因果序骨架
--
-- 因果集 (Fin n, _≺_) 通过 I = Fin n、A = const ⊤、E i _ j = T (i ≺ j)
-- 成为边族系统。因果序骨架的正可达 _⇝⁺_ 于是与 _≺_ 的传递闭包一致，
-- 且 IsCausalSet 蕴含 Acyclic。
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module Physics.CausalSetOrder where

open import Agda.Primitive using (lzero)
open import Data.Nat using (ℕ)
open import Data.Fin using (Fin)
open import Data.Bool using (Bool; T)
open import Data.Unit.Polymorphic.Base using (⊤; tt)

open import Base.MCorr.Setoid using (SysEq; propEqOn)
open import Physics.CausalSet using (IsCausalSet; diamond; diamond-causal)
import Physics.CausalOrder as CO

module Bridge (n : ℕ) (_≺_ : Fin n → Fin n → Bool) where

  ----------------------------------------------------------------------
  -- Edge-family system extracted from a causal set
  --
  -- 从因果集提取的边族系统

  causalSys : SysEq lzero lzero lzero lzero lzero
  causalSys = record
    { I  = Fin n
    ; A  = λ _ → ⊤ {lzero}
    ; E  = λ i _ j → T (i ≺ j)
    ; ≈A = λ _ → propEqOn (⊤ {lzero})
    ; ≈E = λ i _ j → propEqOn (T (i ≺ j))
    }

  ----------------------------------------------------------------------
  -- Transitive closure of _≺_ as an inductive family
  --
  -- _≺_ 的传递闭包作为归纳族

  data _≺⁺_ : Fin n → Fin n → Set where
    step : ∀ {i j} → T (i ≺ j) → i ≺⁺ j
    more : ∀ {i j k} → T (i ≺ j) → j ≺⁺ k → i ≺⁺ k

  ----------------------------------------------------------------------
  -- Positive reachability and the transitive closure coincide
  --
  -- 正可达与传递闭包一致

  ⇝⁺→≺⁺ : ∀ {i j} → CO._⇝⁺_ causalSys i j → i ≺⁺ j
  ⇝⁺→≺⁺ (CO.step _ e) = step e
  ⇝⁺→≺⁺ (CO.more _ e q) = more e (⇝⁺→≺⁺ q)

  ≺⁺→⇝⁺ : ∀ {i j} → i ≺⁺ j → CO._⇝⁺_ causalSys i j
  ≺⁺→⇝⁺ (step p) = CO.step tt p
  ≺⁺→⇝⁺ (more p q) = CO.more tt p (≺⁺→⇝⁺ q)

  ----------------------------------------------------------------------
  -- Under IsCausalSet the transitive closure reflects _≺_
  --
  -- IsCausalSet 下传递闭包反映 _≺_

  ≺⁺-implies-≺ : IsCausalSet n _≺_ → ∀ {i j} → i ≺⁺ j → T (i ≺ j)
  ≺⁺-implies-≺ cs (step p) = p
  ≺⁺-implies-≺ cs (more p q) =
    IsCausalSet.trans cs _ _ _ p (≺⁺-implies-≺ cs q)

  ----------------------------------------------------------------------
  -- Main corollary: every causal set is acyclic in the causal order
  --
  -- 主要推论：每个因果集在因果序骨架中无环

  causal-acyclic : IsCausalSet n _≺_ → CO.Acyclic causalSys
  causal-acyclic cs p =
    IsCausalSet.irrefl cs _ (≺⁺-implies-≺ cs (⇝⁺→≺⁺ p))

------------------------------------------------------------------------
-- End-to-end validation: the four-point diamond is acyclic
--
-- Instantiates causal-acyclic at the concrete diamond causal set, whose
-- IsCausalSet instance is diamond-causal. This is the smallest
-- non-trivial causal set, so it serves as the reference check that the
-- bridge CausalSet → CausalOrder composes correctly on a concrete
-- example.
--
-- 端到端验证：四点菱形无环
--
-- 在具体菱形因果集上实例化 causal-acyclic，其 IsCausalSet 实例为
-- diamond-causal。这是最小的非平凡因果集，故作为参考检验，验证
-- CausalSet → CausalOrder 这条桥在具体例子上正确复合。

diamond-acyclic : CO.Acyclic (Bridge.causalSys 4 diamond)
diamond-acyclic = Bridge.causal-acyclic 4 diamond diamond-causal
