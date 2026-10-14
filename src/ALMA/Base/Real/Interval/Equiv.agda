------------------------------------------------------------------------
-- Equivalence of real intervals
--
-- Two interval sequences are equivalent when their centres eventually
-- agree to within every rational tolerance ε k. The relation is an
-- equivalence: reflexivity is immediate, symmetry uses ∣−p∣ = ∣p∣, and
-- transitivity splits the tolerance via the triangle inequality and
-- ε k = ε (2k) + ε (2k).
--
-- 实数区间等价
--
-- 两个区间序列等价，当且仅当它们的中点最终在每个有理容差 ε k 内一致。
-- 该关系是等价关系：自反显然，对称用 ∣−p∣ = ∣p∣，传递用三角不等式与
-- ε k = ε (2k) + ε (2k) 拆分容差。
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module ALMA.Base.Real.Interval.Equiv where

open import Data.Nat using (ℕ; suc; _≥_; _⊔_; _*_)
open import Data.Nat.Properties using (m≤m⊔n; m≤n⊔m) renaming (≤-trans to ≤-transℕ)
open import Data.Rational using (0ℚ; _+_; _-_; _<_; _≤_; ∣_∣)
open import Data.Product using (Σ; _,_)
open import Data.Rational.Properties using
  (+-mono-<; +-inverseʳ; 0≤p⇒∣p∣≡p; ∣p+q∣≤∣p∣+∣q∣; ∣-p∣≡∣p∣; ≤-refl; ≤-<-trans)
open import Relation.Binary.PropositionalEquality using (_≡_; cong; sym; trans; subst)
open import Relation.Binary.Structures using (IsEquivalence)

open import ALMA.Base.Real using (ε; 0<ε; ε-half; telescope)
open import ALMA.Base.Real.Interval using (RealI)
open import ALMA.Base.Real.IntervalEquiv using (centre)
open import ALMA.Base.Real.Interval.Rational using (negsub)

------------------------------------------------------------------------
-- Real equivalence
--
-- Two interval sequences are equivalent when, for every tolerance ε k,
-- there is a threshold N beyond which the centres stay within ε k.
--
-- 实数等价
--
-- 两个区间序列等价，当且仅当对每个容差 ε k，存在阈值 N，超过后中点
-- 始终落在 ε k 内。

infix 4 _≈ℝ_

_≈ℝ_ : RealI → RealI → Set
x ≈ℝ y = ∀ k → Σ ℕ (λ N → ∀ n → n ≥ N →
           ∣ centre x n - centre y n ∣ < ε k)

------------------------------------------------------------------------
-- Reflexivity
--
-- The difference of a centre with itself is zero, and zero lies below
-- every ε k.
--
-- 自反
--
-- 中点与自身之差为零，而零小于每个 ε k。

≈ℝ-refl : ∀ {x} → x ≈ℝ x
≈ℝ-refl {x} k = 0 , λ n _ →
  let eq0 : centre x n - centre x n ≡ 0ℚ
      eq0 = +-inverseʳ (centre x n)
      abs0 : ∣ centre x n - centre x n ∣ ≡ 0ℚ
      abs0 = trans (cong ∣_∣ eq0) (0≤p⇒∣p∣≡p {0ℚ} (≤-refl {0ℚ}))
  in subst (λ z → z < ε k) (sym abs0) (0<ε k)

------------------------------------------------------------------------
-- Symmetry
--
-- Swap the two centres and rewrite the absolute value via
-- ∣−(p − q)∣ = ∣p − q∣.
--
-- 对称
--
-- 交换两个中点，并用 ∣−(p − q)∣ = ∣p − q∣ 重写绝对值。

≈ℝ-sym : ∀ {x y} → x ≈ℝ y → y ≈ℝ x
≈ℝ-sym {x} {y} p k =
  let N , h = p k
  in N , λ n n≥N →
    let d = h n n≥N
        abs-eq : ∣ centre y n - centre x n ∣
               ≡ ∣ centre x n - centre y n ∣
        abs-eq =
          trans (cong ∣_∣ (sym (negsub (centre x n) (centre y n))))
                (∣-p∣≡∣p∣ (centre x n - centre y n))
    in subst (λ z → z < ε k) (sym abs-eq) d

------------------------------------------------------------------------
-- Transitivity
--
-- Split the target tolerance as ε k = ε (2k) + ε (2k), obtain thresholds
-- for both hypotheses at ε (2k), take their maximum, and combine the two
-- bounds via the triangle inequality after rewriting the sum of
-- differences to the difference of the outer centres.
--
-- 传递
--
-- 把目标容差拆为 ε k = ε (2k) + ε (2k)，对两个假设分别在 ε (2k) 处
-- 取得阈值，取二者最大值，再用三角不等式合并两个界，并先把两个差
-- 之和重写为外侧中点之差。

≈ℝ-trans : ∀ {x y z} → x ≈ℝ y → y ≈ℝ z → x ≈ℝ z
≈ℝ-trans {x} {y} {z} p q k =
  let twice = 2 * k
      fine  = suc twice
      N1 , h1 = p fine
      N2 , h2 = q fine
      N = N1 ⊔ N2
  in N , λ n n≥N →
    let n≥N1 = ≤-transℕ (m≤m⊔n N1 N2) n≥N
        n≥N2 = ≤-transℕ (m≤n⊔m N1 N2) n≥N
        d1 = h1 n n≥N1
        d2 = h2 n n≥N2

        c  = ε fine
        a  = centre x n - centre y n
        b  = centre y n - centre z n

        sum-eq : a + b ≡ centre x n - centre z n
        sum-eq = telescope (centre x n) (centre y n) (centre z n)

        tri : ∣ a + b ∣ ≤ ∣ a ∣ + ∣ b ∣
        tri = ∣p+q∣≤∣p∣+∣q∣ a b

        sum< : ∣ a ∣ + ∣ b ∣ < c + c
        sum< = +-mono-< d1 d2

        abs-sum< : ∣ a + b ∣ < c + c
        abs-sum< = ≤-<-trans tri sum<

        cc : c + c ≡ ε k
        cc = ε-half k

        result : ∣ a + b ∣ < ε k
        result = subst (λ r → ∣ a + b ∣ < r) cc abs-sum<
    in subst (λ r → ∣ r ∣ < ε k) sum-eq result

------------------------------------------------------------------------
-- Equivalence relation
--
-- 等价关系

≈ℝ-isEquivalence : IsEquivalence _≈ℝ_
≈ℝ-isEquivalence = record
  { refl  = λ {x} → ≈ℝ-refl {x}
  ; sym   = λ {x y} → ≈ℝ-sym {x} {y}
  ; trans = λ {x y z} → ≈ℝ-trans {x} {y} {z}
  }
