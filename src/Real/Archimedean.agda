------------------------------------------------------------------------
-- Archimedean precision selection for rational tolerances
--
-- 有理容差的阿基米德精度选择
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module Real.Archimedean where

open import Data.Empty using (⊥-elim)
open import Data.Integer using (+_; -[1+_]) renaming (+<+ to ℤ+<+)
open import Data.Integer.Properties using (<-irrefl; *-identityˡ)
open import Data.Nat using (ℕ; suc; _*_; _+_; s≤s)
open import Data.Nat.Properties as Nat using (≤-refl; m≤m+n)
open import Data.Product using (Σ; _,_)
open import Data.Rational using (ℚ; 0ℚ; _<_; *<*)
open import Data.Rational.Base using (↥_; ↧_; ↧ₙ_)
open import Relation.Binary.PropositionalEquality using
  (_≡_; sym; cong; refl; subst; subst₂; inspect; [_])
open import Relation.Nullary.Negation using (¬_)

open import Real using (ε)

-- The denominator of the k-th precision is suc k.
--
-- 第 k 层精度的分母为 suc k。
den-eq : ∀ k → ↧ (ε k) ≡ + (suc k)
den-eq k = refl

-- Natural-number cross inequality.
--
-- 自然数交叉不等式：d 严格小于 (suc n) 与 (suc d) 的乘积。
cross : ∀ d n → d Data.Nat.< (suc n) * (suc d)
cross d n =
  let base : d Data.Nat.< suc d
      base = s≤s ≤-refl
      mult : suc d Data.Nat.≤ (suc n) * (suc d)
      mult = m≤m+n (suc d) (n * suc d)
  in Nat.<-≤-trans base mult

-- Numerator of a rational.
--
-- 有理数的分子。
num-of : ℚ → Data.Integer.ℤ
num-of x = ↥ x

-- Zero cannot satisfy the positive condition.
--
-- 零不满足此正性条件。
no-zero : ¬_ (+ 0 Data.Integer.< + 0 Data.Integer.* + 1)
no-zero = <-irrefl refl

-- Negative integers cannot satisfy the positive condition.
--
-- 负整数不满足该正性条件。
no-neg : ∀ n → ¬_ (+ 0 Data.Integer.< (-[1+ n ]) Data.Integer.* + 1)
no-neg n ()

-- For positive e, the precision at index ↧ₙ e has width strictly
-- below e.
--
-- 对正 e，精度索引 ↧ₙ e 处的层宽严格小于 e。
build : (e : ℚ) → 0ℚ < e → ε (↧ₙ e) < e
build e (*<* w) with num-of e | inspect num-of e
build e (*<* w) | + (suc n) | [ num-eq ] =
  let num = num-of e
      den = ↧ₙ e
      sd = + (suc den)
      all< = ℤ+<+ (cross den n)
      all<′ = subst (λ x → + den Data.Integer.< x Data.Integer.* sd)
                    (sym num-eq) all<
      lhs-eq = sym (*-identityˡ (↧ e))
      rhs-eq = cong (num Data.Integer.*_) (sym (den-eq den))
      aligned = subst₂ (λ a b → a Data.Integer.< b)
                      lhs-eq rhs-eq all<′
  in *<* aligned
build e (*<* w) | + 0 | _ = ⊥-elim (no-zero w)
build e (*<* w) | -[1+ n ] | _ = ⊥-elim (no-neg n w)

-- For every positive rational tolerance e there is a precision k whose
-- layer width ε k is strictly below e.
--
-- 对每个正有理容差 e，存在精度 k，使该层宽度 ε k 严格小于 e。
ε-archimedean : (e : ℚ) → 0ℚ < e → Σ ℕ (λ k → ε k < e)
ε-archimedean e pos = ↧ₙ e , build e pos
