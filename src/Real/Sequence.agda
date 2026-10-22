------------------------------------------------------------------------
-- Sequences as E-M trees and Cauchy reals as the carrying subtype
--
-- 序列作为 E-M 树，柯西实数作为携带式子类型
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module Real.Sequence where

open import Data.Nat using (ℕ; suc; zero; _≥_; _+_)
open import Data.Nat.Properties using (+-identityʳ; +-suc)
open import Data.Rational using (ℚ; ∣_∣; _-_; _<_)
open import Data.Product using (Σ; _,_)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; trans; sym; cong; cong₂; subst)

open import Base.MCorr using (M; here; below)
open import Real using (CauchySeq; ε)
open CauchySeq renaming (f to seq-f; μ to seq-μ; cauchy to seq-cauchy)

------------------------------------------------------------------------
-- Instantiation of the E-M skeleton over ℕ
--
-- Deterministic successor edges: A i = ℚ and E i a y = y ≡ suc i.
-- The native E-M bisimulation _≈M_ compares trees pointwise, i.e.
-- propositional equality of sequences; the Cauchy metric equivalence
-- _≈_ is strictly coarser.
--
-- 在 ℕ 上实例化 E-M 骨架
--
-- 确定性后继边：A i = ℚ，E i a y = y ≡ suc i。
-- 原生 E-M 互模拟 _≈M_ 逐点比较树，即序列的命题相等；
-- 柯西度量等价 _≈_ 严格更粗。

-- Deterministic successor edge family
--
-- 确定性后继边族
A : ℕ → Set
A _ = ℚ

E : (i : ℕ) (a : ℚ) (y : ℕ) → Set
E i a y = y ≡ suc i

-- An E-M tree over ℕ is the carried form of an arbitrary sequence.
--
-- ℕ 上的 E-M 树即任意序列的携带式。
SeqTree : ℕ → Set
SeqTree = M A E

------------------------------------------------------------------------
-- Build a sequence tree from a function
--
-- 由函数构造序列树

mkTree : (i : ℕ) (f : ℕ → ℚ) → SeqTree i
mkTree i f .here      = f i
mkTree i f .below y _ = mkTree y f

------------------------------------------------------------------------
-- Extract the i-th term from a tree rooted at r
--
-- 从根为 r 的树抽取第 i 项

extract : (i : ℕ) {r : ℕ} (t : SeqTree r) → ℚ
extract zero    t = here t
extract (suc i) {r} t = extract i (below t (suc r) refl)

-- Round trip: extract i (mkTree r f) = f (r + i).
--
-- 往返：extract i (mkTree r f) = f (r + i)。
extract∘mkTree : ∀ i r f → extract i {r} (mkTree r f) ≡ f (r + i)
extract∘mkTree zero r f = cong f (sym (+-identityʳ r))
extract∘mkTree (suc i) r f =
  trans (extract∘mkTree i (suc r) f)
        (cong f (sym (+-suc r i)))

------------------------------------------------------------------------
-- Convergence certificate
--
-- A sequence tree carries a modulus together with the metric Cauchy
-- condition on its terms.
--
-- 收敛证书
--
-- 序列树携带模数，连同其项上的度量柯西条件。

HasConvergence : SeqTree 0 → Set
HasConvergence t =
  Σ (ℕ → ℕ) λ μ' →
    ∀ k n m → n ≥ μ' k → m ≥ μ' k →
      ∣ extract n t - extract m t ∣ < ε k

------------------------------------------------------------------------
-- Cauchy sequences as sequence trees carrying a convergence
-- certificate
--
-- 柯西序列作为携带收敛证书的序列树

cauchy→tree : CauchySeq → SeqTree 0
cauchy→tree x = mkTree 0 (seq-f x)

-- extract n (cauchy→tree x) ≡ seq-f x n.
--
-- 从柯西树抽取第 n 项即原序列第 n 项。
extract-seq : ∀ n x → extract n (cauchy→tree x) ≡ seq-f x n
extract-seq n x = extract∘mkTree n 0 (seq-f x)

-- The tree of a Cauchy sequence carries the convergence certificate.
--
-- 柯西序列的树携带收敛证书。
cauchy-cert : (x : CauchySeq) → HasConvergence (cauchy→tree x)
cauchy-cert x = (seq-μ x) , λ k n m n≥ m≥ →
  let eqn : extract n (cauchy→tree x) ≡ seq-f x n
      eqn = extract-seq n x
      eqm : extract m (cauchy→tree x) ≡ seq-f x m
      eqm = extract-seq m x
      base = seq-cauchy x k n m n≥ m≥
      abs-eq : ∣ extract n (cauchy→tree x) - extract m (cauchy→tree x) ∣
             ≡ ∣ seq-f x n - seq-f x m ∣
      abs-eq = cong₂ (λ a b → ∣ a - b ∣) eqn eqm
  in subst (λ z → z < ε k) (sym abs-eq) base
