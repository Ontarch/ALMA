------------------------------------------------------------------------
-- CauchySeq-layer arithmetic and convergence
--
-- CauchySeq 层的算术与收敛
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module Real.CauchyConvergence where

open import Data.Nat using (ℕ; suc; _≥_; _⊔_; _*_)
open import Data.Nat.Properties using (m≤m⊔n; m≤n⊔m; ≤-trans)
open import Data.Rational using (ℚ; _+_; _-_; _<_; _≤_; ∣_∣)
  renaming (-_ to neg)
open import Data.Rational.Properties using
  (+-mono-<; ≤-<-trans; ∣p+q∣≤∣p∣+∣q∣)
open import Relation.Binary.PropositionalEquality using (_≡_; sym; subst)

open import Real using (CauchySeq; ε; ε-half)
open CauchySeq
open import Real.Convergence using
  (Converges; neg-abs; neg-converges; add-converges)
open import Real.Interval.Rational using (sub-add)

------------------------------------------------------------------------
-- Negation of a Cauchy sequence
--
-- The modulus is unchanged: negating both terms preserves the absolute
-- gap, so the same modulus witnesses the Cauchy condition.
--
-- 柯西序列取负
--
-- 模数不变：两项同时取负保持绝对差，同一模数即可见证柯西条件。

neg-s : CauchySeq → CauchySeq
neg-s x = record
  { f      = λ n → neg (f x n)
  ; μ      = μ x
  ; cauchy = λ k n m n≥μ m≥μ →
      let h : ∣ f x n - f x m ∣ < ε k
          h = cauchy x k n m n≥μ m≥μ
          eq : ∣ f x n - f x m ∣ ≡ ∣ neg (f x n) - neg (f x m) ∣
          eq = sym (neg-abs (f x n) (f x m))
      in subst (λ z → z < ε k) eq h
  }

------------------------------------------------------------------------
-- Addition of Cauchy sequences
--
-- At target precision k we demand each summand's gap below the halved
-- tolerance ε (suc (2*k)); ε-half turns their sum into ε k. The new
-- modulus is the pointwise maximum of the two finer moduli.
--
-- 柯西序列相加
--
-- 在目标精度处，要求各加项的差小于折半容差；折半引理把二者之和化回
-- 目标容差。新模数取两个更细模数的逐点最大值。

-- The precision index at which the half tolerance is taken.
--
-- 取折半容差时使用的精度索引。
half-index : ℕ → ℕ
half-index k = suc (2 * k)

_+s_ : CauchySeq → CauchySeq → CauchySeq
_+s_ x y = record
  { f      = λ n → f x n + f y n
  ; μ      = λ k → μ x (half-index k) ⊔ μ y (half-index k)
  ; cauchy = λ k n m n≥N m≥N →
      let j = half-index k
          n≥μx : n ≥ μ x j
          n≥μx = ≤-trans (m≤m⊔n (μ x j) (μ y j)) n≥N
          n≥μy : n ≥ μ y j
          n≥μy = ≤-trans (m≤n⊔m (μ x j) (μ y j)) n≥N
          m≥μx : m ≥ μ x j
          m≥μx = ≤-trans (m≤m⊔n (μ x j) (μ y j)) m≥N
          m≥μy : m ≥ μ y j
          m≥μy = ≤-trans (m≤n⊔m (μ x j) (μ y j)) m≥N
          hx : ∣ f x n - f x m ∣ < ε j
          hx = cauchy x j n m n≥μx m≥μx
          hy : ∣ f y n - f y m ∣ < ε j
          hy = cauchy y j n m n≥μy m≥μy
          path : (f x n - f x m) + (f y n - f y m)
               ≡ (f x n + f y n) - (f x m + f y m)
          path = sym (sub-add (f x n) (f y n) (f x m) (f y m))
          tri : ∣ (f x n + f y n) - (f x m + f y m) ∣
              ≤ ∣ f x n - f x m ∣ + ∣ f y n - f y m ∣
          tri = subst (λ z → ∣ z ∣ ≤ ∣ f x n - f x m ∣
                           + ∣ f y n - f y m ∣) path
                  (∣p+q∣≤∣p∣+∣q∣ (f x n - f x m) (f y n - f y m))
          sum< : ∣ f x n - f x m ∣ + ∣ f y n - f y m ∣
               < ε j + ε j
          sum< = +-mono-< hx hy
          half-eq : ε j + ε j ≡ ε k
          half-eq = ε-half k
          goal : ∣ f x n - f x m ∣ + ∣ f y n - f y m ∣ < ε k
          goal = subst (λ z → _ < z) half-eq sum<
      in ≤-<-trans tri goal
  }

------------------------------------------------------------------------
-- Convergence through the f field
--
-- A CauchySeq converges to a rational limit exactly when its underlying
-- rational sequence does.
--
-- 经 f 字段的收敛
--
-- 柯西序列收敛到有理极限，当且仅当其底层有理序列收敛。

-- Convergence of a CauchySeq's underlying rational sequence.
--
-- 柯西序列底层有理序列的收敛。
Converges-s : CauchySeq → ℚ → Set
Converges-s x l = Converges (f x) l

-- Negation transports the limit.
--
-- 取负传递极限。
neg-s-converges : ∀ {x l} → Converges-s x l →
  Converges-s (neg-s x) (neg l)
neg-s-converges {x} {l} h = neg-converges {g = f x} {l = l} h

-- Addition transports the limits.
--
-- 加法传递极限。
+s-converges : ∀ {x y l m} → Converges-s x l →
  Converges-s y m → Converges-s (x +s y) (l + m)
+s-converges {x} {y} {l} {m} h k =
  add-converges {g = f x} {h = f y} {l = l} {m = m} h k
