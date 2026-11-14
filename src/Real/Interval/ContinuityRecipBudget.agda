------------------------------------------------------------------------
-- Budget base: budget, positivity, multiplication and width
--
-- 预算底座：预算、正性、乘法与宽度
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module Real.Interval.ContinuityRecipBudget where

open import Data.Nat using (ℕ; suc) renaming (_+_ to _+ℕ_)
open import Data.Nat.Properties using (+-suc; +-identityʳ)
open import Data.Rational using (ℚ; 0ℚ; 1ℚ; _+_; _<_; _≤_; _*_)
open import Data.Rational.Base using (NonZero; positive; 1/_; nonNegative)
open import Data.Rational.Properties using
  (*-assoc; *-comm; *-inverseʳ; *-identityˡ; *-distribʳ-+; pos⇒nonZero; <⇒≤
  ; ≤-trans; *-monoˡ-≤-nonNeg; positive⁻¹; 1/pos⇒pos; pos*pos⇒pos)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; sym; cong; trans; module ≡-Reasoning)
open ≡-Reasoning

open import Real using (ε; embed; embed-+-hom; embed-suc-pos)
open import Real.Interval using (RealI)
open import Real.IntervalEquiv using (width; recip2^t)
open import Real.Interval.ContinuityProdBudget using (width-deep)
open import Real.Interval.DensityArch using (embed1≡1)

------------------------------------------------------------------------
-- eps 9 is one tenth
--
-- eps 9 是十分之一

10ε9≡1 : embed 10 * ε 9 ≡ 1ℚ
10ε9≡1 = *-inverseʳ (embed 10) {{pos⇒nonZero (embed 10) {{embed-suc-pos {9}}}}}

------------------------------------------------------------------------
-- One plus one is two
--
-- 一加一等于二

1+1≡2 : 1ℚ + 1ℚ ≡ embed 2
1+1≡2 = refl

------------------------------------------------------------------------
-- Two copies of eps 9 are twice eps 9
--
-- 两份 eps 9 等于二倍

e+e≡2e : ε 9 + ε 9 ≡ embed 2 * ε 9
e+e≡2e = begin
    ε 9 + ε 9
      ≡⟨ cong (λ z → z + ε 9) (sym (*-identityˡ (ε 9))) ⟩
    1ℚ * ε 9 + ε 9
      ≡⟨ cong (λ z → 1ℚ * ε 9 + z) (sym (*-identityˡ (ε 9))) ⟩
    1ℚ * ε 9 + 1ℚ * ε 9
      ≡⟨ sym (*-distribʳ-+ (ε 9) 1ℚ 1ℚ) ⟩
    (1ℚ + 1ℚ) * ε 9
      ≡⟨ cong (λ z → z * ε 9) 1+1≡2 ⟩
    embed 2 * ε 9
  ∎

------------------------------------------------------------------------
-- The embedded constants 8 and 2 add up to the embedded 10
--
-- 嵌入常数 8 与 2 合成嵌入 10

8+2≡10 : embed 8 + embed 2 ≡ embed 10
8+2≡10 = sym (embed-+-hom 8 2)

------------------------------------------------------------------------
-- Eight copies plus two copies are ten copies, hence one
--
-- 八份加两份共十份，故为一

budget-eq : embed 8 * ε 9 + (ε 9 + ε 9) ≡ 1ℚ
budget-eq = begin
    embed 8 * ε 9 + (ε 9 + ε 9)
      ≡⟨ cong (λ z → embed 8 * ε 9 + z) e+e≡2e ⟩
    embed 8 * ε 9 + embed 2 * ε 9
      ≡⟨ sym (*-distribʳ-+ (ε 9) (embed 8) (embed 2)) ⟩
    (embed 8 + embed 2) * ε 9
      ≡⟨ cong (λ z → z * ε 9) 8+2≡10 ⟩
    embed 10 * ε 9
      ≡⟨ 10ε9≡1 ⟩
    1ℚ
  ∎

------------------------------------------------------------------------
-- Successor in the natural numbers seen as plus one
--
-- 自然数后继写成加一

suc≡+1 : (n : ℕ) → suc n ≡ n +ℕ 1
suc≡+1 n = sym (trans (+-suc n 0) (cong suc (+-identityʳ n)))

------------------------------------------------------------------------
-- A successor coefficient splits off one copy
--
-- 后继系数拆出一份

embed-suc-mul : (n : ℕ) (q : ℚ) → embed (suc n) * q ≡ embed n * q + q
embed-suc-mul n q = begin
    embed (suc n) * q
      ≡⟨ cong (λ z → z * q) (cong embed (suc≡+1 n)) ⟩
    embed (n +ℕ 1) * q
      ≡⟨ cong (λ z → z * q) (embed-+-hom n 1) ⟩
    (embed n + embed 1) * q
      ≡⟨ *-distribʳ-+ q (embed n) (embed 1) ⟩
    embed n * q + embed 1 * q
      ≡⟨ cong (λ z → embed n * q + z) (cong (λ z → z * q) embed1≡1) ⟩
    embed n * q + 1ℚ * q
      ≡⟨ cong (λ z → embed n * q + z) (*-identityˡ q) ⟩
    embed n * q + q
  ∎

------------------------------------------------------------------------
-- Coefficient expansions
--
-- 系数展开

coef2 : (q : ℚ) → embed 2 * q ≡ q + q
coef2 q = begin
    embed 2 * q
      ≡⟨ embed-suc-mul 1 q ⟩
    embed 1 * q + q
      ≡⟨ cong (λ z → z * q + q) embed1≡1 ⟩
    1ℚ * q + q
      ≡⟨ cong (λ z → z + q) (*-identityˡ q) ⟩
    q + q
  ∎

coef3 : (q : ℚ) → embed 3 * q ≡ (q + q) + q
coef3 q = begin
    embed 3 * q
      ≡⟨ embed-suc-mul 2 q ⟩
    embed 2 * q + q
      ≡⟨ cong (λ z → z + q) (coef2 q) ⟩
    (q + q) + q
  ∎

coef4 : (q : ℚ) → embed 4 * q ≡ ((q + q) + q) + q
coef4 q = begin
    embed 4 * q
      ≡⟨ embed-suc-mul 3 q ⟩
    embed 3 * q + q
      ≡⟨ cong (λ z → z + q) (coef3 q) ⟩
    ((q + q) + q) + q
  ∎

coef5 : (q : ℚ) → embed 5 * q ≡ (((q + q) + q) + q) + q
coef5 q = begin
    embed 5 * q
      ≡⟨ embed-suc-mul 4 q ⟩
    embed 4 * q + q
      ≡⟨ cong (λ z → z + q) (coef4 q) ⟩
    (((q + q) + q) + q) + q
  ∎

coef6 : (q : ℚ) → embed 6 * q ≡ ((((q + q) + q) + q) + q) + q
coef6 q = begin
    embed 6 * q
      ≡⟨ embed-suc-mul 5 q ⟩
    embed 5 * q + q
      ≡⟨ cong (λ z → z + q) (coef5 q) ⟩
    ((((q + q) + q) + q) + q) + q
  ∎

coef7 : (q : ℚ) → embed 7 * q ≡ (((((q + q) + q) + q) + q) + q) + q
coef7 q = begin
    embed 7 * q
      ≡⟨ embed-suc-mul 6 q ⟩
    embed 6 * q + q
      ≡⟨ cong (λ z → z + q) (coef6 q) ⟩
    (((((q + q) + q) + q) + q) + q) + q
  ∎

coef8 : (q : ℚ) → embed 8 * q ≡ ((((((q + q) + q) + q) + q) + q) + q) + q
coef8 q = begin
    embed 8 * q
      ≡⟨ embed-suc-mul 7 q ⟩
    embed 7 * q + q
      ≡⟨ cong (λ z → z + q) (coef7 q) ⟩
    ((((((q + q) + q) + q) + q) + q) + q) + q
  ∎

------------------------------------------------------------------------
-- Embedded successors are positive
--
-- 嵌入的后继为正

0<embed-suc : (n : ℕ) → 0ℚ < embed (suc n)
0<embed-suc n = positive⁻¹ (embed (suc n)) {{embed-suc-pos {n}}}

------------------------------------------------------------------------
-- The two fixed divisors
--
-- 两个固定的除数

0<3 : 0ℚ < embed 3
0<3 = 0<embed-suc 2

0<6 : 0ℚ < embed 6
0<6 = 0<embed-suc 5

------------------------------------------------------------------------
-- Reciprocals of positive rationals are positive
--
-- 正有理数的倒数为正

0<inv :
  (q : ℚ) (q>0 : 0ℚ < q) →
  0ℚ < 1/_ q {{pos⇒nonZero q {{positive q>0}}}}
0<inv q q>0 =
  positive⁻¹ (1/_ q {{pos⇒nonZero q {{positive q>0}}}})
    {{1/pos⇒pos q {{positive q>0}}}}

------------------------------------------------------------------------
-- Products of positive rationals are positive
--
-- 正有理数之积为正

0<mul :
  (a b : ℚ) (a>0 : 0ℚ < a) (b>0 : 0ℚ < b) →
  0ℚ < a * b
0<mul a b a>0 b>0 =
  positive⁻¹ (a * b) {{pos*pos⇒pos a {{positive a>0}} b {{positive b>0}}}}

------------------------------------------------------------------------
-- A squared factor cancels against its own reciprocal
--
-- 平方因子与其倒数相消

d-cancel :
  (c e : ℚ) {{nz : NonZero (c * c)}} →
  ((c * c) * e) * (1/_ (c * c)) ≡ e
d-cancel c e = begin
    ((c * c) * e) * (1/_ (c * c))
      ≡⟨ *-assoc (c * c) e (1/_ (c * c)) ⟩
    (c * c) * (e * (1/_ (c * c)))
      ≡⟨ cong (λ z → (c * c) * z) (*-comm e (1/_ (c * c))) ⟩
    (c * c) * ((1/_ (c * c)) * e)
      ≡⟨ sym (*-assoc (c * c) (1/_ (c * c)) e) ⟩
    ((c * c) * (1/_ (c * c))) * e
      ≡⟨ cong (λ z → z * e) (*-inverseʳ (c * c)) ⟩
    1ℚ * e
      ≡⟨ *-identityˡ e ⟩
    e
  ∎

------------------------------------------------------------------------
-- The eightfold gap term keeps only its coefficient
--
-- 八倍间隙项只留下系数

d-eight :
  (c e : ℚ) {{nz : NonZero (c * c)}} →
  (embed 8 * ((c * c) * e)) * (1/_ (c * c)) ≡ embed 8 * e
d-eight c e = begin
    (embed 8 * ((c * c) * e)) * (1/_ (c * c))
      ≡⟨ *-assoc (embed 8) ((c * c) * e) (1/_ (c * c)) ⟩
    embed 8 * (((c * c) * e) * (1/_ (c * c)))
      ≡⟨ cong (λ z → embed 8 * z) (d-cancel c e) ⟩
    embed 8 * e
  ∎

------------------------------------------------------------------------
-- The budget splits over the multiplication
--
-- 预算在乘法上拆开

budget-split :
  (A B q : ℚ) → (A + B) * q ≡ A * q + B * q
budget-split A B q = *-distribʳ-+ q A B

------------------------------------------------------------------------
-- The width is bounded by the scaled dyadic factor
--
-- 宽度被缩放的二进因子控制

width-small :
  (r : RealI) (N n : ℕ) (q : ℚ) →
  width r 0 ≤ embed N →
  0ℚ ≤ embed N →
  recip2^t n < q →
  width r n ≤ embed N * q
width-small r N n q w0≤ 0≤N small =
  ≤-trans (width-deep r N n w0≤)
    (*-monoˡ-≤-nonNeg (embed N) {{nonNegative 0≤N}}
      (<⇒≤ small))
