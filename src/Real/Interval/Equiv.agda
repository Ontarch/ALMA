------------------------------------------------------------------------
-- Equivalence of real intervals
--
-- 实数区间等价
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module Real.Interval.Equiv where

open import Data.Nat using (ℕ; suc; _≥_; _⊔_; _*_)
open import Data.Nat.Properties using (m≤m⊔n; m≤n⊔m)
  renaming (≤-trans to ≤-transℕ)
open import Data.Product using (Σ; _,_)
open import Data.Rational using (0ℚ; _+_; _-_; _<_; ∣_∣; -_)
open import Data.Rational.Properties using
  (+-mono-<; +-inverseʳ; 0≤p⇒∣p∣≡p; ∣p+q∣≤∣p∣+∣q∣; ∣-p∣≡∣p∣; ≤-refl
  ; ≤-<-trans; <-≤-trans; module ≤-Reasoning)
open ≤-Reasoning
open import Relation.Binary.PropositionalEquality using (_≡_; cong; sym)
open import Relation.Binary.Structures using (IsEquivalence)

open import Base.RationalRing using (telescope)
open import Real using (ε; 0<ε; ε-half)
open import Real.Interval using (RealI)
open import Real.IntervalEquiv using (centre)
open import Real.Interval.Rational using (negsub)

------------------------------------------------------------------------
-- Real equivalence
--
-- Two interval sequences are equivalent when their centres eventually
-- agree to within every rational tolerance ε k. The relation is an
-- equivalence: reflexivity is immediate, symmetry uses ∣−p∣ = ∣p∣, and
-- transitivity splits the tolerance via the triangle inequality and
-- ε k = ε (2k) + ε (2k).
--
-- 实数等价
--
-- 两个区间序列等价，当且仅当它们的中心最终在每个有理容差 ε k 内一致。
-- 该关系是等价关系：自反显然，对称用 ∣−p∣ = ∣p∣，传递用三角不等式与
-- ε k = ε (2k) + ε (2k) 拆分容差。

infix 4 _≈ℝ_

_≈ℝ_ : RealI → RealI → Set
x ≈ℝ y = ∀ k → Σ ℕ (λ N → ∀ n → n ≥ N →
           ∣ centre x n - centre y n ∣ < ε k)

-- Reflexivity
--
-- 自反
≈ℝ-refl : ∀ {x} → x ≈ℝ x
≈ℝ-refl {x} k = 0 , λ n _ →
  ≤-<-trans
    (begin
       ∣ centre x n - centre x n ∣
         ≡⟨ cong ∣_∣ (+-inverseʳ (centre x n)) ⟩
       ∣ 0ℚ ∣
         ≡⟨ 0≤p⇒∣p∣≡p {0ℚ} (≤-refl {0ℚ}) ⟩
       0ℚ
     ∎)
    (0<ε k)

-- Symmetry
--
-- 对称
≈ℝ-sym : ∀ {x y} → x ≈ℝ y → y ≈ℝ x
≈ℝ-sym {x} {y} p k =
  let N , h = p k
  in N , λ n n≥N →
    ≤-<-trans
      (begin
         ∣ centre y n - centre x n ∣
           ≡⟨ cong ∣_∣ (sym (negsub (centre x n) (centre y n))) ⟩
         ∣ -(centre x n - centre y n) ∣
           ≡⟨ ∣-p∣≡∣p∣ (centre x n - centre y n) ⟩
         ∣ centre x n - centre y n ∣
       ∎)
      (h n n≥N)

-- Transitivity
--
-- 传递
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

        abs-sum< : ∣ a + b ∣ < c + c
        abs-sum< = ≤-<-trans (∣p+q∣≤∣p∣+∣q∣ a b) (+-mono-< d1 d2)

        cc : c + c ≡ ε k
        cc = ε-half k
    in <-≤-trans
         (≤-<-trans
           (begin
              ∣ centre x n - centre z n ∣
                ≡⟨ cong ∣_∣ (sym sum-eq) ⟩
              ∣ a + b ∣
            ∎)
           abs-sum<)
         (begin
            c + c
              ≡⟨ cc ⟩
            ε k
          ∎)

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
