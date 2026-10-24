------------------------------------------------------------------------
-- Modulus regularization
--
-- 模数正规化
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module Real.Regular where

open import Data.Nat using (ℕ; zero; suc; _⊔_; _∸_)
  renaming (_≤_ to _≤N_; _≥_ to _≥N_; _+_ to _+ℕ_)
open import Data.Nat.Properties using
  (m≤m⊔n; m≤n⊔m; m+[n∸m]≡n; +-comm; module ≤-Reasoning)
  renaming (≤-trans to ≤N-trans; ≤-refl to ≤N-refl)
open ≤-Reasoning
open import Data.Rational using (∣_∣; _-_; _<_)
open import Relation.Binary.PropositionalEquality using (_≡_; trans; cong)

open import Real using (CauchySeq; ε)
open CauchySeq using (f; μ; cauchy)

------------------------------------------------------------------------
-- The regular modulus: a running maximum that also tracks k.
--
-- 正规模数：同时追踪 k 的运行最大值。

μr : (x : CauchySeq) → ℕ → ℕ
μr x zero    = μ x zero ⊔ zero
μr x (suc k) = μr x k ⊔ μ x (suc k) ⊔ suc k

-- One-step monotonicity: μr x k ≤ μr x (suc k).
--
-- 一步单调性：μr x k ≤ μr x (suc k)。
μr-mono1 : (x : CauchySeq) (k : ℕ) → μr x k ≤N μr x (suc k)
μr-mono1 x k =
  ≤N-trans (m≤m⊔n (μr x k) (μ x (suc k)))
           (m≤m⊔n (μr x k ⊔ μ x (suc k)) (suc k))

-- The regular modulus dominates k.
--
-- 正规模数支配 k。
μr≥k : (x : CauchySeq) (k : ℕ) → k ≤N μr x k
μr≥k x zero = m≤n⊔m (μ x zero) zero
μr≥k x (suc k) = m≤n⊔m (μr x k ⊔ μ x (suc k)) (suc k)

-- The regular modulus dominates μ x k.
--
-- 正规模数支配 μ x k。
μr≥μ : (x : CauchySeq) (k : ℕ) → μ x k ≤N μr x k
μr≥μ x zero = m≤m⊔n (μ x zero) zero
μr≥μ x (suc k) =
  ≤N-trans (m≤n⊔m (μr x k) (μ x (suc k)))
           (m≤m⊔n (μr x k ⊔ μ x (suc k)) (suc k))

------------------------------------------------------------------------
-- Iterated monotonicity
--
-- μr x a ≤ μr x (a + d), by d repeated growth steps.
-- Recursion is on the plain natural d, never on a proof, so no
-- constructor-injectivity is required.
--
-- 迭代单调性
--
-- μr x a ≤ μr x (a + d)，由 d 次增长步组成；仅对普通自然数 d 递归，
-- 不匹配任何证明，因此不依赖构造子的单射性。
μr-step : (x : CauchySeq) (a d : ℕ) → μr x a ≤N μr x (d +ℕ a)
μr-step x a zero = ≤N-refl
μr-step x a (suc d) =
  ≤N-trans (μr-step x a d) (μr-mono1 x (d +ℕ a))

-- μ x a is bounded by μr x b whenever a ≤ b.
--
-- 当 a ≤ b 时，μ x a 被 μr x b 控制。
μ≤μr : (x : CauchySeq) (b a : ℕ) → a ≤N b → μ x a ≤N μr x b
μ≤μr x b a a≤b = begin
  μ x a
    ≤⟨ μr≥μ x a ⟩
  μr x a
    ≤⟨ μr-step x a (b ∸ a) ⟩
  μr x (b ∸ a +ℕ a)
    ≡⟨ cong (μr x) (idx a≤b) ⟩
  μr x b
  ∎
  where
  idx : a ≤N b → b ∸ a +ℕ a ≡ b
  idx a≤b = trans (+-comm (b ∸ a) a)
                  (m+[n∸m]≡n {m = a} {n = b} a≤b)

-- μr is monotone in its index.
--
-- μr 对其索引单调。
μr-mono≤ : (x : CauchySeq) (a b : ℕ) → a ≤N b → μr x a ≤N μr x b
μr-mono≤ x a b a≤b = begin
  μr x a
    ≤⟨ μr-step x a (b ∸ a) ⟩
  μr x (b ∸ a +ℕ a)
    ≡⟨ cong (μr x) idx ⟩
  μr x b
  ∎
  where
  idx : b ∸ a +ℕ a ≡ b
  idx = trans (+-comm (b ∸ a) a)
              (m+[n∸m]≡n {m = a} {n = b} a≤b)

------------------------------------------------------------------------
-- Regularization leaves the rational sequence unchanged.
--
-- 正规化不改变有理序列。

regularize : CauchySeq → CauchySeq
regularize x = record
  { f = f x
  ; μ = μr x
  ; cauchy = cauchy-proof
  }
  where
  cauchy-proof : ∀ k n m → n ≥N μr x k → m ≥N μr x k →
    ∣ f x n - f x m ∣ < ε k
  cauchy-proof k n m n≥ m≥ =
    cauchy x k n m
      (≤N-trans (μr≥μ x k) n≥)
      (≤N-trans (μr≥μ x k) m≥)
