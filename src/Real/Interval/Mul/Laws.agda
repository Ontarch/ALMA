------------------------------------------------------------------------
-- Multiplicative and distributive laws for RealI
--
-- RealI 的乘法与分配律
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module Real.Interval.Mul.Laws where

open import Data.Nat using (ℕ) renaming (_*_ to _ℕ*_)
import Data.Nat.Properties as ℕP
open import Data.Product using (proj₁; proj₂)
open import Data.Rational using (ℚ; 0ℚ; 1ℚ; _+_; _-_; _*_; _≤_; ∣_∣)
open import Data.Rational.Properties using
  (+-identityʳ; +-inverseʳ; *-identityˡ; *-zeroˡ; *-assoc; *-comm; *-distribʳ-+
  ; *-distribˡ-+; ≤-refl; ≤-reflexive; ≤-trans; +-mono-≤; ∣p+q∣≤∣p∣+∣q∣
  ; 0≤∣p∣; ∣p*q∣≡∣p∣*∣q∣; 0≤p⇒∣p∣≡p)
open import Relation.Binary.PropositionalEquality using
  (_≡_; cong; cong₂; trans; sym; subst; module ≡-Reasoning)
open ≡-Reasoning

open import Base.RationalRing using (*ʳ-sub)
open import Real using (half)
open import Real.Interval using (RealI)
open import Real.Interval.Arith using (0ℝ; 1ℝ; _+ℝ_)
open import Real.Interval.Mul using (_*ℝ_; le-addˡ; le-addʳ)
open import Real.Interval.Mul.Core using
  (centre-*ℝ≤; centre-mag; tri-add; add3-eq; mul-shift; sub-distribˡ; telesc2)
open import Real.IntervalEquiv using
  (centre; width; width-n; centre-diff; recipPow2)
open import Real.Interval.Equiv using (_≈ℝ_; ≈ℝ-trans)
open import Real.Interval.Node using
  (centre-add; centre-0ℝ; centre-1ℝ; width-rec; width-rec4; width-prod
  ; width-sum-rec; width-x-sum; prod-rec; mul-nonNeg; add2-nonNeg
  ; 0≤width-n; recipPow2≤1)
open import Real.Interval.Kit using
  (≈ℝ-of-rec; half-drop; tri-diff; abs-swap; 2*2n≡4n
  ; n≤2n; 2n≤4n; 0≤recipPow2; two-half; *-mono-≤-nonNeg)
open import Real.Interval.Reasoning using (begin≤_; _≤⟨_⟩_; _≤∎)

------------------------------------------------------------------------
-- Commutativity: auxiliary lemmas
--
-- 交换律：辅助引理

comm-swap-rewrite : (x y : RealI) (n : ℕ) →
  ∣ centre x (2 ℕ* n) * centre y (2 ℕ* n) - centre (y *ℝ x) n ∣
  ≡ ∣ centre (y *ℝ x) n - centre y (2 ℕ* n) * centre x (2 ℕ* n) ∣
comm-swap-rewrite x y n = begin
  ∣ centre x (2 ℕ* n) * centre y (2 ℕ* n) - centre (y *ℝ x) n ∣
    ≡⟨ abs-swap (centre x (2 ℕ* n) * centre y (2 ℕ* n))
                (centre (y *ℝ x) n) ⟩
  ∣ centre (y *ℝ x) n - centre x (2 ℕ* n) * centre y (2 ℕ* n) ∣
    ≡⟨ cong ∣_∣ (cong (centre (y *ℝ x) n -_)
                      (*-comm (centre x (2 ℕ* n)) (centre y (2 ℕ* n)))) ⟩
  ∣ centre (y *ℝ x) n - centre y (2 ℕ* n) * centre x (2 ℕ* n) ∣
  ∎

comm-sum-eq : (x y : RealI) (n : ℕ) →
  (width x (2 ℕ* n) * width y (2 ℕ* n)) * half
  + (width y (2 ℕ* n) * width x (2 ℕ* n)) * half
  ≡ width x (2 ℕ* n) * width y (2 ℕ* n)
comm-sum-eq x y n = begin
  (width x (2 ℕ* n) * width y (2 ℕ* n)) * half
    + (width y (2 ℕ* n) * width x (2 ℕ* n)) * half
    ≡⟨ cong (λ z → (width x (2 ℕ* n) * width y (2 ℕ* n)) * half + z * half)
              (*-comm (width y (2 ℕ* n)) (width x (2 ℕ* n))) ⟩
  (width x (2 ℕ* n) * width y (2 ℕ* n)) * half
    + (width x (2 ℕ* n) * width y (2 ℕ* n)) * half
    ≡⟨ two-half (width x (2 ℕ* n) * width y (2 ℕ* n)) ⟩
  width x (2 ℕ* n) * width y (2 ℕ* n)
  ∎

------------------------------------------------------------------------
-- Commutativity
--
-- 交换律

*ℝ-comm : (x y : RealI) → x *ℝ y ≈ℝ y *ℝ x
*ℝ-comm x y =
  ≈ℝ-of-rec (x *ℝ y) (y *ℝ x) (width x 0 * width y 0)
    (mul-nonNeg (0≤width-n x 0) (0≤width-n y 0))
    (λ n →
      begin≤
        ∣ centre (x *ℝ y) n - centre (y *ℝ x) n ∣
          ≤⟨ tri-diff (centre (x *ℝ y) n)
                      (centre x (2 ℕ* n) * centre y (2 ℕ* n))
                      (centre (y *ℝ x) n) ⟩
        ∣ centre (x *ℝ y) n - centre x (2 ℕ* n) * centre y (2 ℕ* n) ∣
          + ∣ centre x (2 ℕ* n) * centre y (2 ℕ* n) - centre (y *ℝ x) n ∣
          ≤⟨ +-mono-≤ (centre-*ℝ≤ x y n)
                      (≤-trans (≤-reflexive (comm-swap-rewrite x y n))
                               (centre-*ℝ≤ y x n)) ⟩
        (width x (2 ℕ* n) * width y (2 ℕ* n)) * half
          + (width y (2 ℕ* n) * width x (2 ℕ* n)) * half
          ≤⟨ ≤-reflexive (comm-sum-eq x y n) ⟩
        width x (2 ℕ* n) * width y (2 ℕ* n)
          ≤⟨ width-prod x y n ⟩
        width x 0 * width y 0 * recipPow2 n
      ≤∎)

------------------------------------------------------------------------
-- Zero laws: auxiliary lemma
--
-- 零元律：辅助引理

zero-term : (x : RealI) (n : ℕ) →
  ∣ centre 0ℝ (2 ℕ* n) * centre x (2 ℕ* n) - 0ℚ ∣ ≤ 0ℚ
zero-term x n =
  ≤-reflexive (begin
    ∣ centre 0ℝ (2 ℕ* n) * centre x (2 ℕ* n) - 0ℚ ∣
      ≡⟨ cong (λ z → ∣ z * centre x (2 ℕ* n) - 0ℚ ∣)
                (centre-0ℝ (2 ℕ* n)) ⟩
    ∣ 0ℚ * centre x (2 ℕ* n) - 0ℚ ∣
      ≡⟨ cong (λ z → ∣ z - 0ℚ ∣) (*-zeroˡ (centre x (2 ℕ* n))) ⟩
    ∣ 0ℚ - 0ℚ ∣
      ≡⟨ cong ∣_∣ (+-inverseʳ 0ℚ) ⟩
    ∣ 0ℚ ∣
      ≡⟨ 0≤p⇒∣p∣≡p {0ℚ} (≤-refl {0ℚ}) ⟩
    0ℚ
    ∎)

------------------------------------------------------------------------
-- Zero laws
--
-- 零元律

*ℝ-zeroˡ : (x : RealI) → 0ℝ *ℝ x ≈ℝ 0ℝ
*ℝ-zeroˡ x =
  ≈ℝ-of-rec (0ℝ *ℝ x) 0ℝ (width 0ℝ 0 * width x 0)
    (mul-nonNeg (0≤width-n 0ℝ 0) (0≤width-n x 0))
    (λ n →
      begin≤
        ∣ centre (0ℝ *ℝ x) n - centre 0ℝ n ∣
          ≤⟨ ≤-reflexive (cong (λ z → ∣ centre (0ℝ *ℝ x) n - z ∣)
                                (centre-0ℝ n)) ⟩
        ∣ centre (0ℝ *ℝ x) n - 0ℚ ∣
          ≤⟨ tri-diff (centre (0ℝ *ℝ x) n)
                      (centre 0ℝ (2 ℕ* n) * centre x (2 ℕ* n)) 0ℚ ⟩
        ∣ centre (0ℝ *ℝ x) n
            - centre 0ℝ (2 ℕ* n) * centre x (2 ℕ* n) ∣
          + ∣ centre 0ℝ (2 ℕ* n) * centre x (2 ℕ* n) - 0ℚ ∣
          ≤⟨ +-mono-≤ (centre-*ℝ≤ 0ℝ x n) (zero-term x n) ⟩
        (width 0ℝ (2 ℕ* n) * width x (2 ℕ* n)) * half + 0ℚ
          ≤⟨ ≤-reflexive (+-identityʳ
                            ((width 0ℝ (2 ℕ* n) * width x (2 ℕ* n)) * half)) ⟩
        (width 0ℝ (2 ℕ* n) * width x (2 ℕ* n)) * half
          ≤⟨ half-drop (mul-nonNeg (0≤width-n 0ℝ (2 ℕ* n))
                                   (0≤width-n x (2 ℕ* n)))
                       (width-prod 0ℝ x n) ⟩
        width 0ℝ 0 * width x 0 * recipPow2 n
      ≤∎)

*ℝ-zeroʳ : (x : RealI) → x *ℝ 0ℝ ≈ℝ 0ℝ
*ℝ-zeroʳ x = ≈ℝ-trans (*ℝ-comm x 0ℝ) (*ℝ-zeroˡ x)

------------------------------------------------------------------------
-- Identity laws: auxiliary lemma
--
-- 单位元律：辅助引理

one-term : (x : RealI) (n : ℕ) →
  ∣ centre 1ℝ (2 ℕ* n) * centre x (2 ℕ* n) - centre x n ∣ ≤ width x n
one-term x n =
  begin≤
    ∣ centre 1ℝ (2 ℕ* n) * centre x (2 ℕ* n) - centre x n ∣
      ≤⟨ ≤-reflexive
            (cong (λ z → ∣ z * centre x (2 ℕ* n) - centre x n ∣)
                  (centre-1ℝ (2 ℕ* n))) ⟩
    ∣ 1ℚ * centre x (2 ℕ* n) - centre x n ∣
      ≤⟨ ≤-reflexive
            (cong (λ z → ∣ z - centre x n ∣)
                  (*-identityˡ (centre x (2 ℕ* n)))) ⟩
    ∣ centre x (2 ℕ* n) - centre x n ∣
      ≤⟨ centre-diff x n (2 ℕ* n) n (n≤2n n) (ℕP.≤-refl {n}) ⟩
    width x n
  ≤∎

------------------------------------------------------------------------
-- Identity laws
--
-- 单位元律

*ℝ-identityˡ : (x : RealI) → 1ℝ *ℝ x ≈ℝ x
*ℝ-identityˡ x =
  ≈ℝ-of-rec (1ℝ *ℝ x) x (width 1ℝ 0 * width x 0 + width x 0)
    (≤-trans (mul-nonNeg (0≤width-n 1ℝ 0) (0≤width-n x 0))
             (le-addʳ (≤-refl {width 1ℝ 0 * width x 0})
                      (0≤width-n x 0)))
    (λ n →
      begin≤
        ∣ centre (1ℝ *ℝ x) n - centre x n ∣
          ≤⟨ tri-diff (centre (1ℝ *ℝ x) n)
                      (centre 1ℝ (2 ℕ* n) * centre x (2 ℕ* n))
                      (centre x n) ⟩
        ∣ centre (1ℝ *ℝ x) n - centre 1ℝ (2 ℕ* n) * centre x (2 ℕ* n) ∣
          + ∣ centre 1ℝ (2 ℕ* n) * centre x (2 ℕ* n) - centre x n ∣
          ≤⟨ +-mono-≤ (centre-*ℝ≤ 1ℝ x n) (one-term x n) ⟩
        (width 1ℝ (2 ℕ* n) * width x (2 ℕ* n)) * half + width x n
          ≤⟨ +-mono-≤ (half-drop (mul-nonNeg (0≤width-n 1ℝ (2 ℕ* n))
                                              (0≤width-n x (2 ℕ* n)))
                                  (width-prod 1ℝ x n))
                      (width-n x n) ⟩
        (width 1ℝ 0 * width x 0) * recipPow2 n + width x 0 * recipPow2 n
          ≤⟨ ≤-reflexive (sym (*-distribʳ-+ (recipPow2 n)
                                  (width 1ℝ 0 * width x 0) (width x 0))) ⟩
        (width 1ℝ 0 * width x 0 + width x 0) * recipPow2 n
      ≤∎)

*ℝ-identityʳ : (x : RealI) → x *ℝ 1ℝ ≈ℝ x
*ℝ-identityʳ x = ≈ℝ-trans (*ℝ-comm x 1ℝ) (*ℝ-identityˡ x)

------------------------------------------------------------------------
-- Distributivity (left): auxiliary lemmas
--
-- 左分配律：辅助引理

distribˡ-pair-xy : (x y : RealI) (n : ℕ) →
  ∣ centre x (2 ℕ* n) * centre y (2 ℕ* n) - centre (x *ℝ y) n ∣
    ≤ (width x (2 ℕ* n) * width y (2 ℕ* n)) * half
distribˡ-pair-xy x y n =
  ≤-trans (≤-reflexive
            (abs-swap (centre x (2 ℕ* n) * centre y (2 ℕ* n))
                      (centre (x *ℝ y) n)))
          (centre-*ℝ≤ x y n)

distribˡ-pair-xz : (x z : RealI) (n : ℕ) →
  ∣ centre x (2 ℕ* n) * centre z (2 ℕ* n) - centre (x *ℝ z) n ∣
    ≤ (width x (2 ℕ* n) * width z (2 ℕ* n)) * half
distribˡ-pair-xz x z n =
  ≤-trans (≤-reflexive
            (abs-swap (centre x (2 ℕ* n) * centre z (2 ℕ* n))
                      (centre (x *ℝ z) n)))
          (centre-*ℝ≤ x z n)

distribˡ-mid-rewrite : (x y z : RealI) (n : ℕ) →
  ∣ centre x (2 ℕ* n) * centre (y +ℝ z) (2 ℕ* n)
    - centre ((x *ℝ y) +ℝ (x *ℝ z)) n ∣
  ≡ ∣ (centre x (2 ℕ* n) * centre y (2 ℕ* n)
        + centre x (2 ℕ* n) * centre z (2 ℕ* n))
      - (centre (x *ℝ y) n + centre (x *ℝ z) n) ∣
distribˡ-mid-rewrite x y z n =
  cong ∣_∣
    (cong₂ _-_
      (trans (cong (centre x (2 ℕ* n) *_) (centre-add y z (2 ℕ* n)))
              (*-distribˡ-+ (centre x (2 ℕ* n))
                            (centre y (2 ℕ* n)) (centre z (2 ℕ* n))))
      (centre-add (x *ℝ y) (x *ℝ z) n))

distribˡ-mid-split : (x y z : RealI) (n : ℕ) →
  ∣ (centre x (2 ℕ* n) * centre y (2 ℕ* n)
      + centre x (2 ℕ* n) * centre z (2 ℕ* n))
    - (centre (x *ℝ y) n + centre (x *ℝ z) n) ∣
  ≤ (width x (2 ℕ* n) * width y (2 ℕ* n)) * half
    + (width x (2 ℕ* n) * width z (2 ℕ* n)) * half
distribˡ-mid-split x y z n =
  begin≤
    ∣ (centre x (2 ℕ* n) * centre y (2 ℕ* n)
        + centre x (2 ℕ* n) * centre z (2 ℕ* n))
      - (centre (x *ℝ y) n + centre (x *ℝ z) n) ∣
      ≤⟨ tri-add (centre x (2 ℕ* n) * centre y (2 ℕ* n))
                  (centre x (2 ℕ* n) * centre z (2 ℕ* n))
                  (centre (x *ℝ y) n) (centre (x *ℝ z) n) ⟩
    ∣ centre x (2 ℕ* n) * centre y (2 ℕ* n) - centre (x *ℝ y) n ∣
      + ∣ centre x (2 ℕ* n) * centre z (2 ℕ* n) - centre (x *ℝ z) n ∣
      ≤⟨ +-mono-≤ (distribˡ-pair-xy x y n) (distribˡ-pair-xz x z n) ⟩
    (width x (2 ℕ* n) * width y (2 ℕ* n)) * half
      + (width x (2 ℕ* n) * width z (2 ℕ* n)) * half
  ≤∎

distribˡ-rec1 : (x y z : RealI) (n : ℕ) →
  (width x (2 ℕ* n) * width (y +ℝ z) (2 ℕ* n)) * half
    ≤ (width x 0 * (width y 0 + width z 0)) * recipPow2 n
distribˡ-rec1 x y z n =
  half-drop (mul-nonNeg (0≤width-n x (2 ℕ* n))
                        (0≤width-n (y +ℝ z) (2 ℕ* n)))
            (width-x-sum x y z n)

distribˡ-rec2 : (x y z : RealI) (n : ℕ) →
  (width x (2 ℕ* n) * width y (2 ℕ* n)) * half
    ≤ (width x 0 * width y 0) * recipPow2 n
distribˡ-rec2 x y z n =
  half-drop (mul-nonNeg (0≤width-n x (2 ℕ* n)) (0≤width-n y (2 ℕ* n)))
            (width-prod x y n)

distribˡ-rec3 : (x y z : RealI) (n : ℕ) →
  (width x (2 ℕ* n) * width z (2 ℕ* n)) * half
    ≤ (width x 0 * width z 0) * recipPow2 n
distribˡ-rec3 x y z n =
  half-drop (mul-nonNeg (0≤width-n x (2 ℕ* n)) (0≤width-n z (2 ℕ* n)))
            (width-prod x z n)

------------------------------------------------------------------------
-- Distributive law (left)
--
-- 左分配律

*ℝ-distribˡ-+ : (x y z : RealI) →
  x *ℝ (y +ℝ z) ≈ℝ (x *ℝ y) +ℝ (x *ℝ z)
*ℝ-distribˡ-+ x y z =
  ≈ℝ-of-rec (x *ℝ (y +ℝ z)) ((x *ℝ y) +ℝ (x *ℝ z))
    (width x 0 * (width y 0 + width z 0)
      + (width x 0 * width y 0 + width x 0 * width z 0))
    (le-addˡ {x = 0ℚ} {y = width x 0 * (width y 0 + width z 0)}
             {z = width x 0 * width y 0 + width x 0 * width z 0}
             (add2-nonNeg (mul-nonNeg (0≤width-n x 0) (0≤width-n y 0))
                          (mul-nonNeg (0≤width-n x 0) (0≤width-n z 0)))
             (mul-nonNeg (0≤width-n x 0)
                         (add2-nonNeg (0≤width-n y 0) (0≤width-n z 0))))
    (λ n →
      begin≤
        ∣ centre (x *ℝ (y +ℝ z)) n
            - centre ((x *ℝ y) +ℝ (x *ℝ z)) n ∣
          ≤⟨ tri-diff (centre (x *ℝ (y +ℝ z)) n)
                      (centre x (2 ℕ* n) * centre (y +ℝ z) (2 ℕ* n))
                      (centre ((x *ℝ y) +ℝ (x *ℝ z)) n) ⟩
        ∣ centre (x *ℝ (y +ℝ z)) n
            - centre x (2 ℕ* n) * centre (y +ℝ z) (2 ℕ* n) ∣
          + ∣ centre x (2 ℕ* n) * centre (y +ℝ z) (2 ℕ* n)
              - centre ((x *ℝ y) +ℝ (x *ℝ z)) n ∣
          ≤⟨ +-mono-≤ (≤-trans (centre-*ℝ≤ x (y +ℝ z) n)
                              (distribˡ-rec1 x y z n))
                      (≤-trans (≤-reflexive (distribˡ-mid-rewrite x y z n))
                               (distribˡ-mid-split x y z n)) ⟩
        (width x 0 * (width y 0 + width z 0)) * recipPow2 n
          + ((width x (2 ℕ* n) * width y (2 ℕ* n)) * half
             + (width x (2 ℕ* n) * width z (2 ℕ* n)) * half)
          ≤⟨ +-mono-≤ (≤-refl {(width x 0 * (width y 0 + width z 0)) * recipPow2 n})
                      (+-mono-≤ (distribˡ-rec2 x y z n)
                                (distribˡ-rec3 x y z n)) ⟩
        (width x 0 * (width y 0 + width z 0)) * recipPow2 n
          + ((width x 0 * width y 0) * recipPow2 n
             + (width x 0 * width z 0) * recipPow2 n)
          ≤⟨ ≤-reflexive (add3-eq (width x 0 * (width y 0 + width z 0))
                                  (width x 0 * width y 0)
                                  (width x 0 * width z 0)
                                  (recipPow2 n)) ⟩
        (width x 0 * (width y 0 + width z 0)
         + (width x 0 * width y 0 + width x 0 * width z 0)) * recipPow2 n
      ≤∎)

------------------------------------------------------------------------
-- Distributivity (right): auxiliary lemmas
--
-- 右分配律：辅助引理

distribʳ-pair-xz : (x z : RealI) (n : ℕ) →
  ∣ centre x (2 ℕ* n) * centre z (2 ℕ* n) - centre (x *ℝ z) n ∣
    ≤ (width x (2 ℕ* n) * width z (2 ℕ* n)) * half
distribʳ-pair-xz x z n =
  ≤-trans (≤-reflexive
            (abs-swap (centre x (2 ℕ* n) * centre z (2 ℕ* n))
                      (centre (x *ℝ z) n)))
          (centre-*ℝ≤ x z n)

distribʳ-pair-yz : (y z : RealI) (n : ℕ) →
  ∣ centre y (2 ℕ* n) * centre z (2 ℕ* n) - centre (y *ℝ z) n ∣
    ≤ (width y (2 ℕ* n) * width z (2 ℕ* n)) * half
distribʳ-pair-yz y z n =
  ≤-trans (≤-reflexive
            (abs-swap (centre y (2 ℕ* n) * centre z (2 ℕ* n))
                      (centre (y *ℝ z) n)))
          (centre-*ℝ≤ y z n)

distribʳ-mid-rewrite : (x y z : RealI) (n : ℕ) →
  ∣ centre (x +ℝ y) (2 ℕ* n) * centre z (2 ℕ* n)
    - centre ((x *ℝ z) +ℝ (y *ℝ z)) n ∣
  ≡ ∣ (centre x (2 ℕ* n) * centre z (2 ℕ* n)
        + centre y (2 ℕ* n) * centre z (2 ℕ* n))
      - (centre (x *ℝ z) n + centre (y *ℝ z) n) ∣
distribʳ-mid-rewrite x y z n =
  cong ∣_∣
    (cong₂ _-_
      (trans (cong (_* centre z (2 ℕ* n)) (centre-add x y (2 ℕ* n)))
              (*-distribʳ-+ (centre z (2 ℕ* n))
                            (centre x (2 ℕ* n)) (centre y (2 ℕ* n))))
      (centre-add (x *ℝ z) (y *ℝ z) n))

distribʳ-mid-split : (x y z : RealI) (n : ℕ) →
  ∣ (centre x (2 ℕ* n) * centre z (2 ℕ* n)
      + centre y (2 ℕ* n) * centre z (2 ℕ* n))
    - (centre (x *ℝ z) n + centre (y *ℝ z) n) ∣
  ≤ (width x (2 ℕ* n) * width z (2 ℕ* n)) * half
    + (width y (2 ℕ* n) * width z (2 ℕ* n)) * half
distribʳ-mid-split x y z n =
  begin≤
    ∣ (centre x (2 ℕ* n) * centre z (2 ℕ* n)
        + centre y (2 ℕ* n) * centre z (2 ℕ* n))
      - (centre (x *ℝ z) n + centre (y *ℝ z) n) ∣
      ≤⟨ tri-add (centre x (2 ℕ* n) * centre z (2 ℕ* n))
                  (centre y (2 ℕ* n) * centre z (2 ℕ* n))
                  (centre (x *ℝ z) n) (centre (y *ℝ z) n) ⟩
    ∣ centre x (2 ℕ* n) * centre z (2 ℕ* n) - centre (x *ℝ z) n ∣
      + ∣ centre y (2 ℕ* n) * centre z (2 ℕ* n) - centre (y *ℝ z) n ∣
      ≤⟨ +-mono-≤ (distribʳ-pair-xz x z n) (distribʳ-pair-yz y z n) ⟩
    (width x (2 ℕ* n) * width z (2 ℕ* n)) * half
      + (width y (2 ℕ* n) * width z (2 ℕ* n)) * half
  ≤∎

distribʳ-rec1-aux : (x y z : RealI) (n : ℕ) →
  width (x +ℝ y) (2 ℕ* n) * width z (2 ℕ* n)
    ≤ (width z 0 * (width x 0 + width y 0)) * recipPow2 n
distribʳ-rec1-aux x y z n =
  ≤-trans
    (prod-rec {a = width (x +ℝ y) (2 ℕ* n)}
              {a' = width x 0 + width y 0}
              {b = width z (2 ℕ* n)}
              {b' = width z 0}
              {r = recipPow2 n}
              (0≤recipPow2 n) (recipPow2≤1 n)
              (width-sum-rec x y n) (width-rec z n)
              (0≤width-n (x +ℝ y) (2 ℕ* n)) (0≤width-n z (2 ℕ* n))
              (add2-nonNeg (0≤width-n x 0) (0≤width-n y 0))
              (0≤width-n z 0))
    (≤-reflexive (cong (_* recipPow2 n)
                      (*-comm (width x 0 + width y 0) (width z 0))))

distribʳ-rec1 : (x y z : RealI) (n : ℕ) →
  (width (x +ℝ y) (2 ℕ* n) * width z (2 ℕ* n)) * half
    ≤ (width z 0 * (width x 0 + width y 0)) * recipPow2 n
distribʳ-rec1 x y z n =
  half-drop {a = width (x +ℝ y) (2 ℕ* n) * width z (2 ℕ* n)}
            {b = (width z 0 * (width x 0 + width y 0)) * recipPow2 n}
            (mul-nonNeg (0≤width-n (x +ℝ y) (2 ℕ* n))
                        (0≤width-n z (2 ℕ* n)))
            (distribʳ-rec1-aux x y z n)

distribʳ-rec2 : (x y z : RealI) (n : ℕ) →
  (width x (2 ℕ* n) * width z (2 ℕ* n)) * half
    ≤ (width z 0 * width x 0) * recipPow2 n
distribʳ-rec2 x y z n =
  half-drop (mul-nonNeg (0≤width-n x (2 ℕ* n)) (0≤width-n z (2 ℕ* n)))
    (≤-trans (width-prod x z n)
              (≤-reflexive (cong (_* recipPow2 n)
                                (*-comm (width x 0) (width z 0)))))

distribʳ-rec3 : (x y z : RealI) (n : ℕ) →
  (width y (2 ℕ* n) * width z (2 ℕ* n)) * half
    ≤ (width z 0 * width y 0) * recipPow2 n
distribʳ-rec3 x y z n =
  half-drop (mul-nonNeg (0≤width-n y (2 ℕ* n)) (0≤width-n z (2 ℕ* n)))
    (≤-trans (width-prod y z n)
              (≤-reflexive (cong (_* recipPow2 n)
                                (*-comm (width y 0) (width z 0)))))

------------------------------------------------------------------------
-- Distributive law (right)
--
-- 右分配律

*ℝ-distribʳ-+ : (x y z : RealI) →
  (x +ℝ y) *ℝ z ≈ℝ (x *ℝ z) +ℝ (y *ℝ z)
*ℝ-distribʳ-+ x y z =
  ≈ℝ-of-rec ((x +ℝ y) *ℝ z) ((x *ℝ z) +ℝ (y *ℝ z))
    (width z 0 * (width x 0 + width y 0)
      + (width z 0 * width x 0 + width z 0 * width y 0))
    (le-addˡ {x = 0ℚ} {y = width z 0 * (width x 0 + width y 0)}
             {z = width z 0 * width x 0 + width z 0 * width y 0}
             (add2-nonNeg (mul-nonNeg (0≤width-n z 0) (0≤width-n x 0))
                          (mul-nonNeg (0≤width-n z 0) (0≤width-n y 0)))
             (mul-nonNeg (0≤width-n z 0)
                         (add2-nonNeg (0≤width-n x 0) (0≤width-n y 0))))
    (λ n →
      begin≤
        ∣ centre ((x +ℝ y) *ℝ z) n
            - centre ((x *ℝ z) +ℝ (y *ℝ z)) n ∣
          ≤⟨ tri-diff (centre ((x +ℝ y) *ℝ z) n)
                      (centre (x +ℝ y) (2 ℕ* n) * centre z (2 ℕ* n))
                      (centre ((x *ℝ z) +ℝ (y *ℝ z)) n) ⟩
        ∣ centre ((x +ℝ y) *ℝ z) n
            - centre (x +ℝ y) (2 ℕ* n) * centre z (2 ℕ* n) ∣
          + ∣ centre (x +ℝ y) (2 ℕ* n) * centre z (2 ℕ* n)
              - centre ((x *ℝ z) +ℝ (y *ℝ z)) n ∣
          ≤⟨ +-mono-≤ (≤-trans (centre-*ℝ≤ (x +ℝ y) z n)
                              (distribʳ-rec1 x y z n))
                      (≤-trans (≤-reflexive (distribʳ-mid-rewrite x y z n))
                               (distribʳ-mid-split x y z n)) ⟩
        (width z 0 * (width x 0 + width y 0)) * recipPow2 n
          + ((width x (2 ℕ* n) * width z (2 ℕ* n)) * half
             + (width y (2 ℕ* n) * width z (2 ℕ* n)) * half)
          ≤⟨ +-mono-≤ (≤-refl {(width z 0 * (width x 0 + width y 0)) * recipPow2 n})
                      (+-mono-≤ (distribʳ-rec2 x y z n)
                                (distribʳ-rec3 x y z n)) ⟩
        (width z 0 * (width x 0 + width y 0)) * recipPow2 n
          + ((width z 0 * width x 0) * recipPow2 n
             + (width z 0 * width y 0) * recipPow2 n)
          ≤⟨ ≤-reflexive (add3-eq (width z 0 * (width x 0 + width y 0))
                                  (width z 0 * width x 0)
                                  (width z 0 * width y 0)
                                  (recipPow2 n)) ⟩
        (width z 0 * (width x 0 + width y 0)
         + (width z 0 * width x 0 + width z 0 * width y 0)) * recipPow2 n
      ≤∎)

------------------------------------------------------------------------
-- Associativity: private module with all helpers
--
-- 结合律：收集全部辅助引理的私有模块

module AssocCore (x y z : RealI) where
  Mx My Mz : ℚ
  Mx = proj₁ (centre-mag x)
  My = proj₁ (centre-mag y)
  Mz = proj₁ (centre-mag z)

  0≤Mx : 0ℚ ≤ Mx
  0≤Mx = proj₁ (proj₂ (centre-mag x))
  0≤My : 0ℚ ≤ My
  0≤My = proj₁ (proj₂ (centre-mag y))
  0≤Mz : 0ℚ ≤ Mz
  0≤Mz = proj₁ (proj₂ (centre-mag z))

  ≤Mx : ∀ m → ∣ centre x m ∣ ≤ Mx
  ≤Mx m = proj₂ (proj₂ (centre-mag x)) m
  ≤My : ∀ m → ∣ centre y m ∣ ≤ My
  ≤My m = proj₂ (proj₂ (centre-mag y)) m
  ≤Mz : ∀ m → ∣ centre z m ∣ ≤ Mz
  ≤Mz m = proj₂ (proj₂ (centre-mag z)) m

  P1 P2 P3 P4 P5 K : ℚ
  P1 = width (x *ℝ y) 0 * width z 0
  P2 = Mz * (width x 0 * width y 0)
  P3 = My * (Mz * width x 0 + Mx * width z 0)
  P4 = Mx * (width y 0 * width z 0)
  P5 = width x 0 * width (y *ℝ z) 0
  K  = P1 + ((P2 + (P3 + P4)) + P5)

  P1≥0 : 0ℚ ≤ P1
  P1≥0 = mul-nonNeg (0≤width-n (x *ℝ y) 0) (0≤width-n z 0)
  P2≥0 : 0ℚ ≤ P2
  P2≥0 = mul-nonNeg 0≤Mz (mul-nonNeg (0≤width-n x 0) (0≤width-n y 0))
  P3≥0 : 0ℚ ≤ P3
  P3≥0 = mul-nonNeg 0≤My
            (add2-nonNeg (mul-nonNeg 0≤Mz (0≤width-n x 0))
                        (mul-nonNeg 0≤Mx (0≤width-n z 0)))
  P4≥0 : 0ℚ ≤ P4
  P4≥0 = mul-nonNeg 0≤Mx (mul-nonNeg (0≤width-n y 0) (0≤width-n z 0))
  P5≥0 : 0ℚ ≤ P5
  P5≥0 = mul-nonNeg (0≤width-n x 0) (0≤width-n (y *ℝ z) 0)
  P234≥0 : 0ℚ ≤ P2 + (P3 + P4)
  P234≥0 = le-addˡ {x = 0ℚ} {y = P2} {z = P3 + P4}
              (add2-nonNeg P3≥0 P4≥0) P2≥0

  K≥0 : 0ℚ ≤ K
  K≥0 = le-addˡ {x = 0ℚ} {y = P1} {z = (P2 + (P3 + P4)) + P5}
          (add2-nonNeg P234≥0 P5≥0) P1≥0

  cx2 cx4 cy4 cz2 cz4 cyz2 cxy2 : ℕ → ℚ
  cx2 n = centre x (2 ℕ* n)
  cx4 n = centre x (4 ℕ* n)
  cy4 n = centre y (4 ℕ* n)
  cz2 n = centre z (2 ℕ* n)
  cz4 n = centre z (4 ℕ* n)
  cyz2 n = centre (y *ℝ z) (2 ℕ* n)
  cxy2 n = centre (x *ℝ y) (2 ℕ* n)

  Lo Hi : ℕ → ℚ
  Lo n = centre ((x *ℝ y) *ℝ z) n
  Hi n = centre (x *ℝ (y *ℝ z)) n

  A B : ℕ → ℚ
  A n = cxy2 n * cz2 n
  B n = cx2 n * cyz2 n

  t1 ta tb tc t5 : ℕ → ℚ
  t1 n = (width (x *ℝ y) (2 ℕ* n) * width z (2 ℕ* n)) * half
  ta n = Mz * ((width x (4 ℕ* n) * width y (4 ℕ* n)) * half)
  tb n = My * (Mz * width x (2 ℕ* n) + Mx * width z (2 ℕ* n))
  tc n = Mx * ((width y (4 ℕ* n) * width z (4 ℕ* n)) * half)
  t5 n = (width x (2 ℕ* n) * width (y *ℝ z) (2 ℕ* n)) * half

  w2 : ∀ (r : RealI) n → width r (2 ℕ* n) ≤ width r 0 * recipPow2 n
  w2 r n = width-rec r n
  w4 : ∀ (r : RealI) n → width r (4 ℕ* n) ≤ width r 0 * recipPow2 n
  w4 r n = width-rec4 r n

  h1 : ∀ n → ∣ Lo n - A n ∣ ≤ t1 n
  h1 n = centre-*ℝ≤ (x *ℝ y) z n

  h5 : ∀ n → ∣ B n - Hi n ∣ ≤ t5 n
  h5 n =
    begin≤
      ∣ B n - Hi n ∣
        ≤⟨ ≤-reflexive (abs-swap (cx2 n * cyz2 n)
                                  (centre (x *ℝ (y *ℝ z)) n)) ⟩
      ∣ centre (x *ℝ (y *ℝ z)) n - cx2 n * cyz2 n ∣
        ≤⟨ centre-*ℝ≤ x (y *ℝ z) n ⟩
      t5 n
    ≤∎

  mA-eqA : ∀ n → cxy2 n * cz2 n - cx4 n * cy4 n * cz2 n
                 ≡ (cxy2 n - cx4 n * cy4 n) * cz2 n
  mA-eqA n = sym (*ʳ-sub (cxy2 n) (cx4 n * cy4 n) (cz2 n))

  mA-inner : ∀ n → ∣ cxy2 n - cx4 n * cy4 n ∣
                   ≤ (width x (4 ℕ* n) * width y (4 ℕ* n)) * half
  mA-inner n =
    subst (λ m → ∣ cxy2 n - centre x m * centre y m ∣
                    ≤ (width x m * width y m) * half)
          (2*2n≡4n n) (centre-*ℝ≤ x y (2 ℕ* n))

  mA : ∀ n → ∣ cxy2 n * cz2 n - cx4 n * cy4 n * cz2 n ∣ ≤ ta n
  mA n =
    begin≤
      ∣ cxy2 n * cz2 n - cx4 n * cy4 n * cz2 n ∣
        ≤⟨ ≤-reflexive (cong ∣_∣ (mA-eqA n)) ⟩
      ∣ (cxy2 n - cx4 n * cy4 n) * cz2 n ∣
        ≤⟨ ≤-reflexive
              (trans (∣p*q∣≡∣p∣*∣q∣ (cxy2 n - cx4 n * cy4 n) (cz2 n))
                     (*-comm (∣ cxy2 n - cx4 n * cy4 n ∣) (∣ cz2 n ∣))) ⟩
      ∣ cz2 n ∣ * ∣ cxy2 n - cx4 n * cy4 n ∣
        ≤⟨ *-mono-≤-nonNeg (0≤∣p∣ (cz2 n)) (≤Mz (2 ℕ* n))
                            (0≤∣p∣ (cxy2 n - cx4 n * cy4 n))
                            (mA-inner n) ⟩
      Mz * ((width x (4 ℕ* n) * width y (4 ℕ* n)) * half)
    ≤∎

  mB-rwY : ∀ n → cx2 n * (cy4 n * cz4 n) ≡ cy4 n * (cx2 n * cz4 n)
  mB-rwY n = begin
    cx2 n * (cy4 n * cz4 n)
      ≡⟨ cong (cx2 n *_) (*-comm (cy4 n) (cz4 n)) ⟩
    cx2 n * (cz4 n * cy4 n)
      ≡⟨ sym (*-assoc (cx2 n) (cz4 n) (cy4 n)) ⟩
    (cx2 n * cz4 n) * cy4 n
      ≡⟨ *-comm (cx2 n * cz4 n) (cy4 n) ⟩
    cy4 n * (cx2 n * cz4 n)
    ∎

  mB-eqX : ∀ n → cx4 n * cy4 n * cz2 n - cx2 n * (cy4 n * cz4 n)
                 ≡ cy4 n * (cx4 n * cz2 n - cx2 n * cz4 n)
  mB-eqX n = begin
    cx4 n * cy4 n * cz2 n - cx2 n * (cy4 n * cz4 n)
      ≡⟨ cong (λ w → w * cz2 n - cx2 n * (cy4 n * cz4 n))
                (*-comm (cx4 n) (cy4 n)) ⟩
    cy4 n * cx4 n * cz2 n - cx2 n * (cy4 n * cz4 n)
      ≡⟨ cong (λ w → w - cx2 n * (cy4 n * cz4 n))
                (*-assoc (cy4 n) (cx4 n) (cz2 n)) ⟩
    cy4 n * (cx4 n * cz2 n) - cx2 n * (cy4 n * cz4 n)
      ≡⟨ cong (cy4 n * (cx4 n * cz2 n) -_) (mB-rwY n) ⟩
    cy4 n * (cx4 n * cz2 n) - cy4 n * (cx2 n * cz4 n)
      ≡⟨ sym (sub-distribˡ (cy4 n) (cx4 n * cz2 n) (cx2 n * cz4 n)) ⟩
    cy4 n * (cx4 n * cz2 n - cx2 n * cz4 n)
    ∎

  mB-l1 : ∀ n → ∣ cx4 n * cz2 n - cx2 n * cz4 n ∣
                 ≤ ∣ cz2 n * (cx4 n - cx2 n) ∣
                   + ∣ cx2 n * (cz2 n - cz4 n) ∣
  mB-l1 n =
    ≤-trans (≤-reflexive (cong ∣_∣
              (telesc2 (cx4 n) (cx2 n) (cz2 n) (cz4 n))))
            (∣p+q∣≤∣p∣+∣q∣ (cz2 n * (cx4 n - cx2 n))
                            (cx2 n * (cz2 n - cz4 n)))

  mB-d1 : ∀ n → ∣ cx4 n - cx2 n ∣ ≤ width x (2 ℕ* n)
  mB-d1 n =
    ≤-trans (≤-reflexive (abs-swap (cx4 n) (cx2 n)))
            (centre-diff x (2 ℕ* n) (2 ℕ* n) (4 ℕ* n)
                        (ℕP.≤-refl {2 ℕ* n}) (2n≤4n n))

  mB-l2 : ∀ n → ∣ cz2 n * (cx4 n - cx2 n) ∣ ≤ Mz * width x (2 ℕ* n)
  mB-l2 n =
    ≤-trans (≤-reflexive (∣p*q∣≡∣p∣*∣q∣ (cz2 n) (cx4 n - cx2 n)))
            (≤-trans (*-mono-≤-nonNeg (0≤∣p∣ (cz2 n)) (≤Mz (2 ℕ* n))
                      (0≤∣p∣ (cx4 n - cx2 n)) (mB-d1 n))
                    (≤-refl {Mz * width x (2 ℕ* n)}))

  mB-d3 : ∀ n → ∣ cz2 n - cz4 n ∣ ≤ width z (2 ℕ* n)
  mB-d3 n =
    centre-diff z (2 ℕ* n) (2 ℕ* n) (4 ℕ* n)
                (ℕP.≤-refl {2 ℕ* n}) (2n≤4n n)

  mB-l3 : ∀ n → ∣ cx2 n * (cz2 n - cz4 n) ∣ ≤ Mx * width z (2 ℕ* n)
  mB-l3 n =
    ≤-trans (≤-reflexive (∣p*q∣≡∣p∣*∣q∣ (cx2 n) (cz2 n - cz4 n)))
            (≤-trans (*-mono-≤-nonNeg (0≤∣p∣ (cx2 n)) (≤Mx (2 ℕ* n))
                      (0≤∣p∣ (cz2 n - cz4 n)) (mB-d3 n))
                    (≤-refl {Mx * width z (2 ℕ* n)}))

  mB-inner : ∀ n → ∣ cx4 n * cz2 n - cx2 n * cz4 n ∣
                   ≤ Mz * width x (2 ℕ* n) + Mx * width z (2 ℕ* n)
  mB-inner n = ≤-trans (mB-l1 n) (+-mono-≤ (mB-l2 n) (mB-l3 n))

  mB : ∀ n → ∣ cx4 n * cy4 n * cz2 n - cx2 n * (cy4 n * cz4 n) ∣ ≤ tb n
  mB n =
    begin≤
      ∣ cx4 n * cy4 n * cz2 n - cx2 n * (cy4 n * cz4 n) ∣
        ≤⟨ ≤-reflexive (cong ∣_∣ (mB-eqX n)) ⟩
      ∣ cy4 n * (cx4 n * cz2 n - cx2 n * cz4 n) ∣
        ≤⟨ ≤-reflexive
              (∣p*q∣≡∣p∣*∣q∣ (cy4 n) (cx4 n * cz2 n - cx2 n * cz4 n)) ⟩
      ∣ cy4 n ∣ * ∣ cx4 n * cz2 n - cx2 n * cz4 n ∣
        ≤⟨ *-mono-≤-nonNeg (0≤∣p∣ (cy4 n)) (≤My (4 ℕ* n))
                            (0≤∣p∣ (cx4 n * cz2 n - cx2 n * cz4 n))
                            (mB-inner n) ⟩
      My * (Mz * width x (2 ℕ* n) + Mx * width z (2 ℕ* n))
    ≤∎

  mC-inner : ∀ n → ∣ cy4 n * cz4 n - cyz2 n ∣
                   ≤ (width y (4 ℕ* n) * width z (4 ℕ* n)) * half
  mC-inner n =
    subst (λ m → ∣ centre y m * centre z m - cyz2 n ∣
                    ≤ (width y m * width z m) * half)
          (2*2n≡4n n)
          (≤-trans (≤-reflexive
                      (abs-swap (centre y (2 ℕ* (2 ℕ* n))
                                        * centre z (2 ℕ* (2 ℕ* n)))
                                (cyz2 n)))
                    (centre-*ℝ≤ y z (2 ℕ* n)))

  mC : ∀ n → ∣ cx2 n * (cy4 n * cz4 n) - cx2 n * cyz2 n ∣ ≤ tc n
  mC n =
    begin≤
      ∣ cx2 n * (cy4 n * cz4 n) - cx2 n * cyz2 n ∣
        ≤⟨ ≤-reflexive (cong ∣_∣ (sym (sub-distribˡ (cx2 n)
                                        (cy4 n * cz4 n) (cyz2 n)))) ⟩
      ∣ cx2 n * (cy4 n * cz4 n - cyz2 n) ∣
        ≤⟨ ≤-reflexive
              (∣p*q∣≡∣p∣*∣q∣ (cx2 n) (cy4 n * cz4 n - cyz2 n)) ⟩
      ∣ cx2 n ∣ * ∣ cy4 n * cz4 n - cyz2 n ∣
        ≤⟨ *-mono-≤-nonNeg (0≤∣p∣ (cx2 n)) (≤Mx (2 ℕ* n))
                            (0≤∣p∣ (cy4 n * cz4 n - cyz2 n))
                            (mC-inner n) ⟩
      Mx * ((width y (4 ℕ* n) * width z (4 ℕ* n)) * half)
    ≤∎

  hM : ∀ n → ∣ cxy2 n * cz2 n - cx2 n * cyz2 n ∣ ≤ ta n + (tb n + tc n)
  hM n =
    begin≤
      ∣ cxy2 n * cz2 n - cx2 n * cyz2 n ∣
        ≤⟨ tri-diff (cxy2 n * cz2 n) (cx4 n * cy4 n * cz2 n)
                    (cx2 n * cyz2 n) ⟩
      ∣ cxy2 n * cz2 n - cx4 n * cy4 n * cz2 n ∣
        + ∣ cx4 n * cy4 n * cz2 n - cx2 n * cyz2 n ∣
        ≤⟨ +-mono-≤ (mA n)
                    (≤-trans (tri-diff (cx4 n * cy4 n * cz2 n)
                                      (cx2 n * (cy4 n * cz4 n))
                                      (cx2 n * cyz2 n))
                             (+-mono-≤ (mB n) (mC n))) ⟩
      ta n + (tb n + tc n)
    ≤∎

  chain : ∀ n → ∣ Lo n - Hi n ∣ ≤ t1 n + ((ta n + (tb n + tc n)) + t5 n)
  chain n =
    begin≤
      ∣ Lo n - Hi n ∣
        ≤⟨ tri-diff (Lo n) (cxy2 n * cz2 n) (Hi n) ⟩
      ∣ Lo n - cxy2 n * cz2 n ∣ + ∣ cxy2 n * cz2 n - Hi n ∣
        ≤⟨ +-mono-≤ (h1 n) (≤-refl {∣ cxy2 n * cz2 n - Hi n ∣}) ⟩
      t1 n + ∣ cxy2 n * cz2 n - Hi n ∣
        ≤⟨ +-mono-≤ (≤-refl {t1 n})
                    (tri-diff (cxy2 n * cz2 n) (cx2 n * cyz2 n) (Hi n)) ⟩
      t1 n + (∣ cxy2 n * cz2 n - cx2 n * cyz2 n ∣
              + ∣ cx2 n * cyz2 n - Hi n ∣)
        ≤⟨ +-mono-≤ (≤-refl {t1 n})
                    (+-mono-≤ (hM n) (≤-refl {∣ cx2 n * cyz2 n - Hi n ∣})) ⟩
      t1 n + ((ta n + (tb n + tc n)) + ∣ cx2 n * cyz2 n - Hi n ∣)
        ≤⟨ +-mono-≤ (≤-refl {t1 n})
                    (+-mono-≤ (≤-refl {ta n + (tb n + tc n)}) (h5 n)) ⟩
      t1 n + ((ta n + (tb n + tc n)) + t5 n)
    ≤∎

  c1 : ∀ n → t1 n ≤ P1 * recipPow2 n
  c1 n =
    half-drop {a = width (x *ℝ y) (2 ℕ* n) * width z (2 ℕ* n)}
              {b = (width (x *ℝ y) 0 * width z 0) * recipPow2 n}
              (mul-nonNeg (0≤width-n (x *ℝ y) (2 ℕ* n))
                          (0≤width-n z (2 ℕ* n)))
      (prod-rec {a = width (x *ℝ y) (2 ℕ* n)}
                {a' = width (x *ℝ y) 0}
                {b = width z (2 ℕ* n)}
                {b' = width z 0}
                {r = recipPow2 n}
                (0≤recipPow2 n) (recipPow2≤1 n)
                (w2 (x *ℝ y) n) (w2 z n)
                (0≤width-n (x *ℝ y) (2 ℕ* n)) (0≤width-n z (2 ℕ* n))
                (0≤width-n (x *ℝ y) 0) (0≤width-n z 0))

  ca : ∀ n → ta n ≤ P2 * recipPow2 n
  ca n =
    begin≤
      ta n
        ≤⟨ mul-shift 0≤Mz
                    (half-drop {a = width x (4 ℕ* n) * width y (4 ℕ* n)}
                                {b = (width x 0 * width y 0) * recipPow2 n}
                                (mul-nonNeg (0≤width-n x (4 ℕ* n))
                                            (0≤width-n y (4 ℕ* n)))
                      (prod-rec {a = width x (4 ℕ* n)}
                                {a' = width x 0}
                                {b = width y (4 ℕ* n)}
                                {b' = width y 0}
                                {r = recipPow2 n}
                                (0≤recipPow2 n) (recipPow2≤1 n)
                                (w4 x n) (w4 y n)
                                (0≤width-n x (4 ℕ* n))
                                (0≤width-n y (4 ℕ* n))
                                (0≤width-n x 0) (0≤width-n y 0))) ⟩
      Mz * ((width x 0 * width y 0) * recipPow2 n)
        ≤⟨ ≤-reflexive (sym (*-assoc Mz (width x 0 * width y 0)
                                    (recipPow2 n))) ⟩
      (Mz * (width x 0 * width y 0)) * recipPow2 n
    ≤∎

  cb-inner : ∀ n → Mz * width x (2 ℕ* n) + Mx * width z (2 ℕ* n)
                   ≤ (Mz * width x 0 + Mx * width z 0) * recipPow2 n
  cb-inner n =
    begin≤
      Mz * width x (2 ℕ* n) + Mx * width z (2 ℕ* n)
        ≤⟨ +-mono-≤
              (≤-trans (mul-shift 0≤Mz (w2 x n))
                      (≤-reflexive (sym (*-assoc Mz (width x 0)
                                                  (recipPow2 n)))))
              (≤-trans (mul-shift 0≤Mx (w2 z n))
                      (≤-reflexive (sym (*-assoc Mx (width z 0)
                                                  (recipPow2 n))))) ⟩
      (Mz * width x 0) * recipPow2 n + (Mx * width z 0) * recipPow2 n
        ≤⟨ ≤-reflexive (sym (*-distribʳ-+ (recipPow2 n)
                              (Mz * width x 0) (Mx * width z 0))) ⟩
      (Mz * width x 0 + Mx * width z 0) * recipPow2 n
    ≤∎

  cb : ∀ n → tb n ≤ P3 * recipPow2 n
  cb n =
    begin≤
      tb n
        ≤⟨ mul-shift 0≤My (cb-inner n) ⟩
      My * ((Mz * width x 0 + Mx * width z 0) * recipPow2 n)
        ≤⟨ ≤-reflexive (sym (*-assoc My (Mz * width x 0 + Mx * width z 0)
                                    (recipPow2 n))) ⟩
      (My * (Mz * width x 0 + Mx * width z 0)) * recipPow2 n
    ≤∎

  cc : ∀ n → tc n ≤ P4 * recipPow2 n
  cc n =
    begin≤
      tc n
        ≤⟨ mul-shift 0≤Mx
                    (half-drop {a = width y (4 ℕ* n) * width z (4 ℕ* n)}
                                {b = (width y 0 * width z 0) * recipPow2 n}
                                (mul-nonNeg (0≤width-n y (4 ℕ* n))
                                            (0≤width-n z (4 ℕ* n)))
                      (prod-rec {a = width y (4 ℕ* n)}
                                {a' = width y 0}
                                {b = width z (4 ℕ* n)}
                                {b' = width z 0}
                                {r = recipPow2 n}
                                (0≤recipPow2 n) (recipPow2≤1 n)
                                (w4 y n) (w4 z n)
                                (0≤width-n y (4 ℕ* n))
                                (0≤width-n z (4 ℕ* n))
                                (0≤width-n y 0) (0≤width-n z 0))) ⟩
      Mx * ((width y 0 * width z 0) * recipPow2 n)
        ≤⟨ ≤-reflexive (sym (*-assoc Mx (width y 0 * width z 0)
                                    (recipPow2 n))) ⟩
      (Mx * (width y 0 * width z 0)) * recipPow2 n
    ≤∎

  c5 : ∀ n → t5 n ≤ P5 * recipPow2 n
  c5 n =
    half-drop {a = width x (2 ℕ* n) * width (y *ℝ z) (2 ℕ* n)}
              {b = (width x 0 * width (y *ℝ z) 0) * recipPow2 n}
              (mul-nonNeg (0≤width-n x (2 ℕ* n))
                          (0≤width-n (y *ℝ z) (2 ℕ* n)))
      (prod-rec {a = width x (2 ℕ* n)}
                {a' = width x 0}
                {b = width (y *ℝ z) (2 ℕ* n)}
                {b' = width (y *ℝ z) 0}
                {r = recipPow2 n}
                (0≤recipPow2 n) (recipPow2≤1 n)
                (w2 x n) (w2 (y *ℝ z) n)
                (0≤width-n x (2 ℕ* n)) (0≤width-n (y *ℝ z) (2 ℕ* n))
                (0≤width-n x 0) (0≤width-n (y *ℝ z) 0))

  cM : ∀ n → ta n + (tb n + tc n) ≤ (P2 + (P3 + P4)) * recipPow2 n
  cM n =
    begin≤
      ta n + (tb n + tc n)
        ≤⟨ +-mono-≤ (ca n) (+-mono-≤ (cb n) (cc n)) ⟩
      P2 * recipPow2 n + (P3 * recipPow2 n + P4 * recipPow2 n)
        ≤⟨ ≤-reflexive (add3-eq P2 P3 P4 (recipPow2 n)) ⟩
      (P2 + (P3 + P4)) * recipPow2 n
    ≤∎

  body : ∀ n → ∣ Lo n - Hi n ∣ ≤ K * recipPow2 n
  body n =
    begin≤
      ∣ Lo n - Hi n ∣
        ≤⟨ chain n ⟩
      t1 n + ((ta n + (tb n + tc n)) + t5 n)
        ≤⟨ +-mono-≤ (c1 n) (+-mono-≤ (cM n) (c5 n)) ⟩
      P1 * recipPow2 n
        + ((P2 + (P3 + P4)) * recipPow2 n + P5 * recipPow2 n)
        ≤⟨ ≤-reflexive (add3-eq P1 (P2 + (P3 + P4)) P5 (recipPow2 n)) ⟩
      K * recipPow2 n
    ≤∎

  proof : (x *ℝ y) *ℝ z ≈ℝ x *ℝ (y *ℝ z)
  proof = ≈ℝ-of-rec ((x *ℝ y) *ℝ z) (x *ℝ (y *ℝ z)) K K≥0 body

------------------------------------------------------------------------
-- Associativity
--
-- 结合律

*ℝ-assoc : (x y z : RealI) → (x *ℝ y) *ℝ z ≈ℝ x *ℝ (y *ℝ z)
*ℝ-assoc x y z = AssocCore.proof x y z
