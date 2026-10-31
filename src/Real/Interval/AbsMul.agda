------------------------------------------------------------------------
-- Multiplicative law of the absolute value
--
-- 绝对值的乘性定律
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module Real.Interval.AbsMul where

open import Data.Product using (_,_; proj₁; proj₂)
open import Data.Nat using (ℕ; zero; suc) renaming (_*_ to _ℕ*_; _+_ to _+N_)
open import Data.Nat.Properties using (+-suc; *-suc)
open import Data.Rational using (ℚ; 0ℚ; 1ℚ; _+_; _-_; _*_; _≤_; ∣_∣; nonNegative)
  renaming (-_ to neg)
open import Data.Rational.Properties as QP using
  (≤-refl; ≤-reflexive; ≤-trans; <⇒≤; +-mono-≤; +-comm; +-assoc; +-identityʳ
  ; +-identityˡ; +-inverseˡ; +-inverseʳ; *-assoc; *-comm; *-identityʳ; *-zeroˡ
  ; *-distribʳ-+; ∣p+q∣≤∣p∣+∣q∣; ∣p*q∣≡∣p∣*∣q∣; ∣p∣≡p∨∣p∣≡-p
  ; neg-distrib-+; 0≤∣p∣; *-monoˡ-≤-nonNeg; *-monoʳ-≤-nonNeg)
open import Data.Sum using (inj₁; inj₂)
open import Function.Base using (case_of_)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; cong; cong₂; sym; trans; subst; module ≡-Reasoning)
open ≡-Reasoning

open import Base.RationalRing using (telescope)
open import Real using (half)
open import Real.Interval using (RealI)
open import Real.Interval.Mul using (_*ℝ_)
open import Real.Interval.Equiv using (_≈ℝ_)
open import Real.IntervalEquiv using
  (l; u; centre; width; width-n; node; recipPow2; negneg)
open import Real.Interval.Node using (0≤width-n)
open import Real.Interval.Abs using (∣_∣ℝ; absLo; absHi)
open import Real.Interval.Mul.Core using (term1; centre-mag)
open import Real.Interval.Kit using
  (≈ℝ-of-rec; 0<half; halveQ; recipPow2-n≤1; recipPow2-mul; 0≤recipPow2; *-mono-≤-nonNeg)
open import Real.Interval.Reasoning using (begin≤_; _≤⟨_⟩_; _≤∎)
open import Real.Interval.AbsTriangle using
  (abs-centre-≤; centre-abs-node)

------------------------------------------------------------------------
-- Nonnegativity of the assembled constant
--
-- 组装常数的非负性

-- Two nonnegative rationals have a nonnegative sum.
--
-- 两个非负有理数之和非负。
sum-nn : (a b : ℚ) → 0ℚ ≤ a → 0ℚ ≤ b → 0ℚ ≤ a + b
sum-nn a b = +-mono-≤

-- The product of two nonnegative rationals is nonnegative.
--
-- 两个非负有理数之积非负。
mul-nn : (a b : ℚ) → 0ℚ ≤ a → 0ℚ ≤ b → 0ℚ ≤ a * b
mul-nn a b p q =
  let q1 : 0ℚ * b ≤ a * b
      q1 = *-monoʳ-≤-nonNeg b {{nonNegative q}} p
  in subst (λ z → z ≤ a * b) (*-zeroˡ b) q1

-- Rewrite the multiplication-based depth as twice the addition-based
-- depth.
--
-- 把基于乘法的深度改写为两倍加法深度。
mul2eq : (k : ℕ) → 2 ℕ* k ≡ k +N k
mul2eq zero = refl
mul2eq (suc k) =
  let ih = mul2eq k
      step : 2 +N (2 ℕ* k) ≡ 2 +N (k +N k)
      step = cong (2 +N_) ih
      step2 : 2 +N (k +N k) ≡ suc k +N suc k
      step2 =
        begin 2 +N (k +N k)
          ≡⟨ refl ⟩
        suc (suc k +N k)
          ≡⟨ sym (+-suc (suc k) k) ⟩
        suc k +N suc k
        ∎
      main : 2 +N (2 ℕ* k) ≡ suc k +N suc k
      main = trans step step2
  in subst (λ t → t ≡ suc k +N suc k) (sym (*-suc 2 k)) main

-- Expand-diff the outer difference into a right-nested sum of
-- consecutive differences.
--
-- 望远镜和：首尾差等于相邻差之和（右结合）。
expand-diff : (a0 a1 a2 a3 a4 a5 : ℚ) →
  a0 - a5 ≡
  (a0 - a1) + ((a1 - a2) + ((a2 - a3) + ((a3 - a4) + (a4 - a5))))
expand-diff a0 a1 a2 a3 a4 a5 =
  begin a0 - a5
    ≡⟨ sym (telescope a0 a1 a5) ⟩
  (a0 - a1) + (a1 - a5)
    ≡⟨ cong ((a0 - a1) +_)
       (begin a1 - a5
         ≡⟨ sym (telescope a1 a2 a5) ⟩
       (a1 - a2) + (a2 - a5)
         ≡⟨ cong ((a1 - a2) +_)
            (begin a2 - a5
              ≡⟨ sym (telescope a2 a3 a5) ⟩
            (a2 - a3) + (a3 - a5)
              ≡⟨ cong ((a2 - a3) +_)
                 (sym (telescope a3 a4 a5)) ⟩
            (a2 - a3) + ((a3 - a4) + (a4 - a5)) ∎) ⟩
       (a1 - a2) + ((a2 - a3) + ((a3 - a4) + (a4 - a5))) ∎) ⟩
  (a0 - a1) + ((a1 - a2) + ((a2 - a3) + ((a3 - a4) + (a4 - a5)))) ∎

-- Combine two absolute-value error bounds.
--
-- 两项绝对值误差合并。
add-right : {a b k l : ℚ} → ∣ a ∣ ≤ k → ∣ b ∣ ≤ l → ∣ a + b ∣ ≤ k + l
add-right {a} {b} {k} {l} pa pb =
  ≤-trans (∣p+q∣≤∣p∣+∣q∣ a b) (+-mono-≤ pa pb)

-- Combine five right-nested absolute-value error bounds.
--
-- 五项（右结合）误差合并。
add5 : {t1 t2 t3 t4 t5 k1 k2 k3 k4 k5 : ℚ} →
  ∣ t1 ∣ ≤ k1 → ∣ t2 ∣ ≤ k2 → ∣ t3 ∣ ≤ k3 → ∣ t4 ∣ ≤ k4 → ∣ t5 ∣ ≤ k5 →
  ∣ t1 + (t2 + (t3 + (t4 + t5))) ∣ ≤ k1 + (k2 + (k3 + (k4 + k5)))
add5 p1 p2 p3 p4 p5 =
  add-right p1 (add-right p2 (add-right p3 (add-right p4 p5)))

-- Chain five consecutive gap bounds into a bound on the outer
-- difference.
--
-- 五段链：用相邻五段误差之和界住首尾差。
chain5 : (a0 a1 a2 a3 a4 a5 k1 k2 k3 k4 k5 : ℚ) →
  ∣ a0 - a1 ∣ ≤ k1 → ∣ a1 - a2 ∣ ≤ k2 → ∣ a2 - a3 ∣ ≤ k3 →
  ∣ a3 - a4 ∣ ≤ k4 → ∣ a4 - a5 ∣ ≤ k5 →
  ∣ a0 - a5 ∣ ≤ k1 + (k2 + (k3 + (k4 + k5)))
chain5 a0 a1 a2 a3 a4 a5 k1 k2 k3 k4 k5 p1 p2 p3 p4 p5 =
  subst (λ z → ∣ z ∣ ≤ k1 + (k2 + (k3 + (k4 + k5))))
    (sym (expand-diff a0 a1 a2 a3 a4 a5))
    (add5 p1 p2 p3 p4 p5)

------------------------------------------------------------------------
-- Rational helper lemmas (ℚ)
--
-- 有理数引理

-- Reverse triangle inequality.
--
-- 反向三角不等式。
rev-tri : (a b : ℚ) → ∣ a ∣ - ∣ b ∣ ≤ ∣ a - b ∣
rev-tri a b =
  let a≡ : a ≡ (a - b) + b
      a≡ =
        begin
          a
            ≡⟨ sym (+-identityʳ a) ⟩
          a + 0ℚ
            ≡⟨ cong (a +_) (sym (QP.+-inverseˡ b)) ⟩
          a + (neg b + b)
            ≡⟨ sym (+-assoc a (neg b) b) ⟩
          (a + neg b) + b
            ≡⟨ refl ⟩
          (a - b) + b
        ∎
      t : ∣ a ∣ ≤ ∣ a - b ∣ + ∣ b ∣
      t =
        begin≤ ∣ a ∣
          ≤⟨ ≤-reflexive (cong ∣_∣ a≡) ⟩
          ∣ (a - b) + b ∣
          ≤⟨ ∣p+q∣≤∣p∣+∣q∣ (a - b) b ⟩
          ∣ a - b ∣ + ∣ b ∣
        ≤∎
      eq : (∣ a - b ∣ + ∣ b ∣) + neg ∣ b ∣ ≡ ∣ a - b ∣
      eq =
        begin
          (∣ a - b ∣ + ∣ b ∣) + neg ∣ b ∣
            ≡⟨ +-assoc ∣ a - b ∣ ∣ b ∣ (neg ∣ b ∣) ⟩
          ∣ a - b ∣ + (∣ b ∣ + neg ∣ b ∣)
            ≡⟨ cong (∣ a - b ∣ +_) (+-inverseʳ ∣ b ∣) ⟩
          ∣ a - b ∣ + 0ℚ
            ≡⟨ +-identityʳ ∣ a - b ∣ ⟩
          ∣ a - b ∣
        ∎
  in
  begin≤ (∣ a ∣ - ∣ b ∣)
    ≤⟨ QP.+-monoˡ-≤ (neg ∣ b ∣) t ⟩
    (∣ a - b ∣ + ∣ b ∣) + neg ∣ b ∣
    ≤⟨ ≤-reflexive eq ⟩
    ∣ a - b ∣
  ≤∎

-- The absolute value is 1-Lipschitz.
--
-- 绝对值函数是 1-Lipschitz 的。
abs-lip : (a b : ℚ) → ∣ ∣ a ∣ - ∣ b ∣ ∣ ≤ ∣ a - b ∣
abs-lip a b =
  let neg-neg : (c : ℚ) → neg (neg c) ≡ c
      neg-neg c =
        begin neg (neg c)
          ≡⟨ sym (+-identityʳ (neg (neg c))) ⟩
        neg (neg c) + 0ℚ
          ≡⟨ cong (neg (neg c) +_) (sym (+-inverseˡ c)) ⟩
        neg (neg c) + (neg c + c)
          ≡⟨ sym (+-assoc (neg (neg c)) (neg c) c) ⟩
        (neg (neg c) + neg c) + c
          ≡⟨ cong (_+ c) (+-inverseˡ (neg c)) ⟩
        0ℚ + c
          ≡⟨ +-identityˡ c ⟩
        c
        ∎
      X = ∣ a ∣ - ∣ b ∣
      w = ∣ a - b ∣
      d1 : X ≤ w
      d1 = rev-tri a b
      e : b - a ≡ neg (a - b)
      e =
        begin b - a
          ≡⟨ refl ⟩
        b + neg a
          ≡⟨ +-comm b (neg a) ⟩
        neg a + b
          ≡⟨ cong (neg a +_) (sym (neg-neg b)) ⟩
        neg a + neg (neg b)
          ≡⟨ sym (neg-distrib-+ a (neg b)) ⟩
        neg (a + neg b)
        ∎
      eq : ∣ b - a ∣ ≡ w
      eq = trans (cong ∣_∣ e) (QP.∣-p∣≡∣p∣ (a - b))
      d2 : neg X ≤ w
      d2 =
        let k : ∣ b ∣ - ∣ a ∣ ≤ w
            k = subst (λ z → ∣ b ∣ - ∣ a ∣ ≤ z) eq (rev-tri b a)
            neq : neg X ≡ ∣ b ∣ - ∣ a ∣
            neq =
              begin neg X
                ≡⟨ refl ⟩
              neg (∣ a ∣ + neg ∣ b ∣)
                ≡⟨ neg-distrib-+ ∣ a ∣ (neg ∣ b ∣) ⟩
              neg ∣ a ∣ + neg (neg ∣ b ∣)
                ≡⟨ cong (neg ∣ a ∣ +_) (neg-neg ∣ b ∣) ⟩
              neg ∣ a ∣ + ∣ b ∣
                ≡⟨ +-comm (neg ∣ a ∣) ∣ b ∣ ⟩
              ∣ b ∣ + neg ∣ a ∣
              ∎
        in subst (λ z → z ≤ w) (sym neq) k
  in case ∣p∣≡p∨∣p∣≡-p X of λ
       { (inj₁ e) → subst (λ z → z ≤ w) (sym e) d1
       ; (inj₂ e) → subst (λ z → z ≤ w) (sym e) d2
       }

------------------------------------------------------------------------
-- The multiplicative-law constant
--
-- 乘性定律所用的常数

abs-mul-K : (x y : RealI) → ℚ
abs-mul-K x y =
  let Mx = proj₁ (centre-mag x)
      My = proj₁ (centre-mag y)
      T1 = width x 0 * width y 0 * half
      T1abs = width ∣ x ∣ℝ 0 * width ∣ y ∣ℝ 0 * half
      Wxy0 = width (x *ℝ y) 0
      Cross4 = My * width x 0 + Mx * width y 0 + width x 0 * width y 0
  in Wxy0 + (T1 + (0ℚ + (Cross4 + T1abs)))

-- Rewrite term1 with the doubled index in addition form.
--
-- 把 term1 中的二倍下标改写为加法形式。
term1' : (x R : RealI) (n : ℕ) →
  ∣ centre (x *ℝ R) n - centre x (n +N n) * centre R (n +N n) ∣
  ≤ (width x 0 * width R 0 * half) * recipPow2 n
term1' x R n =
  subst
    (λ d → ∣ centre (x *ℝ R) n - d ∣
           ≤ (width x 0 * width R 0 * half) * recipPow2 n)
    (cong₂ (λ p q → centre x p * centre R q)
       (mul2eq n) (mul2eq n))
    (term1 x R n)

-- The constant is nonnegative.
--
-- 该常数非负。
abs-mul-K≥0 : (x y : RealI) → 0ℚ ≤ abs-mul-K x y
abs-mul-K≥0 x y =
  let Mx = proj₁ (centre-mag x)
      Mx0≤ = proj₁ (proj₂ (centre-mag x))
      My = proj₁ (centre-mag y)
      My0≤ = proj₁ (proj₂ (centre-mag y))
      wx0 = width x 0
      wy0 = width y 0
      T1 = wx0 * wy0 * half
      T1abs = width ∣ x ∣ℝ 0 * width ∣ y ∣ℝ 0 * half
      Wxy0 = width (x *ℝ y) 0
      Cross4 = My * wx0 + Mx * wy0 + wx0 * wy0
      wxnn : 0ℚ ≤ wx0
      wxnn = 0≤width-n x 0
      wynn : 0ℚ ≤ wy0
      wynn = 0≤width-n y 0
      c4nn : 0ℚ ≤ Cross4
      c4nn =
        +-mono-≤ (+-mono-≤ (mul-nn My wx0 My0≤ wxnn)
                           (mul-nn Mx wy0 Mx0≤ wynn))
                 (mul-nn wx0 wy0 wxnn wynn)
      t1nn : 0ℚ ≤ T1
      t1nn = mul-nn (wx0 * wy0) half
               (mul-nn wx0 wy0 wxnn wynn) (<⇒≤ 0<half)
      tann : 0ℚ ≤ T1abs
      tann = mul-nn (width ∣ x ∣ℝ 0 * width ∣ y ∣ℝ 0) half
               (mul-nn (width ∣ x ∣ℝ 0) (width ∣ y ∣ℝ 0)
                  (0≤width-n ∣ x ∣ℝ 0) (0≤width-n ∣ y ∣ℝ 0))
               (<⇒≤ 0<half)
      wnn : 0ℚ ≤ Wxy0
      wnn = 0≤width-n (x *ℝ y) 0
      inner : 0ℚ ≤ 0ℚ + (Cross4 + T1abs)
      inner = subst (λ z → z ≤ 0ℚ + (Cross4 + T1abs))
                (sym (+-identityˡ 0ℚ))
                (+-mono-≤ (≤-refl) (+-mono-≤ c4nn tann))
  in +-mono-≤ wnn (+-mono-≤ t1nn inner)

-- Helper for e4/e5: |centre |r| n| vs |centre r (n+n)|
--
-- e4/e5 的辅助引理
abs-centre-gap : (r : RealI) (n : ℕ) →
  ∣ centre ∣ r ∣ℝ n - ∣ centre r (n +N n) ∣ ∣ ≤ width r (n +N n)
abs-centre-gap r n =
  let
    can : centre ∣ r ∣ℝ n ≡
          halveQ (absLo (l r (n +N n)) (u r (n +N n)) +
                 absHi (l r (n +N n)) (u r (n +N n)))
    can = centre-abs-node r n
    raw : ∣ halveQ (absLo (l r (n +N n)) (u r (n +N n)) +
                    absHi (l r (n +N n)) (u r (n +N n)))
                  - ∣ centre r (n +N n) ∣ ∣
          ≤ width r (n +N n)
    raw = abs-centre-≤ (l r (n +N n)) (u r (n +N n))
            (<⇒≤ (RealI.lo (node r (n +N n))))
  in subst (λ z → ∣ z - ∣ centre r (n +N n) ∣ ∣ ≤ width r (n +N n)) (sym can) raw

-- Helper for bxB: |centre |r| n| ≤ M + width r 0
--
-- bxB 的辅助引理
centre-abs-bound : (r : RealI) (n : ℕ) (M : ℚ) →
  (∀ m → ∣ centre r m ∣ ≤ M) →
  ∣ centre ∣ r ∣ℝ n ∣ ≤ M + width r 0
centre-abs-bound r n M M-bnd =
  let
    gap : ∣ centre ∣ r ∣ℝ n - ∣ centre r (n +N n) ∣ ∣ ≤ width r (n +N n)
    gap = abs-centre-gap r n
    M-nn : ∣ centre r (n +N n) ∣ ≤ M
    M-nn = M-bnd (n +N n)
    M-nn' : ∣ ∣ centre r (n +N n) ∣ ∣ ≤ M
    M-nn' =
      subst (λ z → z ≤ M)
        (sym (QP.0≤p⇒∣p∣≡p (QP.0≤∣p∣ (centre r (n +N n)))))
        M-nn
    split :
      centre ∣ r ∣ℝ n ≡
      (centre ∣ r ∣ℝ n - ∣ centre r (n +N n) ∣) + ∣ centre r (n +N n) ∣
    split =
      begin
        centre ∣ r ∣ℝ n
          ≡⟨ sym (+-identityʳ (centre ∣ r ∣ℝ n)) ⟩
        centre ∣ r ∣ℝ n + 0ℚ
          ≡⟨ cong (centre ∣ r ∣ℝ n +_)
                  (sym (QP.+-inverseˡ ∣ centre r (n +N n) ∣)) ⟩
        centre ∣ r ∣ℝ n + (neg ∣ centre r (n +N n) ∣ + ∣ centre r (n +N n) ∣)
          ≡⟨ sym (+-assoc (centre ∣ r ∣ℝ n)
                          (neg ∣ centre r (n +N n) ∣) ∣ centre r (n +N n) ∣) ⟩
        (centre ∣ r ∣ℝ n - ∣ centre r (n +N n) ∣) + ∣ centre r (n +N n) ∣
      ∎
    sum-bound :
      ∣ centre ∣ r ∣ℝ n ∣
      ≤ width r (n +N n) + M
    sum-bound =
      ≤-trans (≤-reflexive (cong ∣_∣ split))
        (≤-trans
          (∣p+q∣≤∣p∣+∣q∣
            (centre ∣ r ∣ℝ n - ∣ centre r (n +N n) ∣)
            ∣ centre r (n +N n) ∣)
          (+-mono-≤ gap M-nn'))
    w-2n-le-w0 : width r (n +N n) ≤ width r 0
    w-2n-le-w0 =
      ≤-trans (width-n r (n +N n))
        (≤-trans (*-monoˡ-≤-nonNeg (width r 0)
                    {{nonNegative (0≤width-n r 0)}}
                    (recipPow2-n≤1 (n +N n)))
                 (≤-reflexive (*-identityʳ (width r 0))))
  in ≤-trans sum-bound
       (≤-trans (+-mono-≤ w-2n-le-w0 (≤-refl {M}))
                (≤-reflexive (+-comm (width r 0) M)))

-- Helper for sumEq: the constant reindexing step
--
-- sumEq 的代数重排
abs-mul-sumEq : (Wxy0 T1 Cross4 T1abs r : ℚ) →
  Wxy0 * r + (T1 * r + (0ℚ + (Cross4 * r + T1abs * r)))
  ≡ (Wxy0 + (T1 + (0ℚ + (Cross4 + T1abs)))) * r
abs-mul-sumEq Wxy0 T1 Cross4 T1abs r =
  let
    fact : (k : ℚ) → k * r ≡ r * k
    fact k = *-comm k r
    term : ℚ
    term = r * Wxy0 + (r * T1 + (0ℚ + (r * Cross4 + r * T1abs)))
    right : 0ℚ + (Cross4 * r + T1abs * r)
            ≡ 0ℚ + (r * Cross4 + r * T1abs)
    right =
      cong₂ _+_ (refl {x = 0ℚ})
        (cong₂ _+_ (fact Cross4) (fact T1abs))
    fact2 : r * (Wxy0 + (T1 + (0ℚ + (Cross4 + T1abs)))) ≡ term
    fact2 =
      begin r * (Wxy0 + (T1 + (0ℚ + (Cross4 + T1abs))))
        ≡⟨ QP.*-distribˡ-+ r Wxy0 (T1 + (0ℚ + (Cross4 + T1abs))) ⟩
      r * Wxy0 + r * (T1 + (0ℚ + (Cross4 + T1abs)))
        ≡⟨ cong (r * Wxy0 +_)
            (QP.*-distribˡ-+ r T1 (0ℚ + (Cross4 + T1abs))) ⟩
      r * Wxy0 + (r * T1 + r * (0ℚ + (Cross4 + T1abs)))
        ≡⟨ cong (λ z → r * Wxy0 + (r * T1 + z))
            (begin r * (0ℚ + (Cross4 + T1abs))
              ≡⟨ QP.*-distribˡ-+ r 0ℚ (Cross4 + T1abs) ⟩
            r * 0ℚ + r * (Cross4 + T1abs)
              ≡⟨ cong (λ z → z + r * (Cross4 + T1abs))
                  (QP.*-zeroʳ r) ⟩
            0ℚ + r * (Cross4 + T1abs)
              ≡⟨ cong (λ z → 0ℚ + z)
                  (QP.*-distribˡ-+ r Cross4 T1abs) ⟩
            0ℚ + (r * Cross4 + r * T1abs) ∎) ⟩
      term ∎
  in
  begin Wxy0 * r + (T1 * r + (0ℚ + (Cross4 * r + T1abs * r)))
    ≡⟨ cong₂ _+_ (fact Wxy0)
        (cong₂ _+_ (fact T1) right) ⟩
  term
    ≡⟨ sym fact2 ⟩
  r * (Wxy0 + (T1 + (0ℚ + (Cross4 + T1abs))))
    ≡⟨ *-comm r (Wxy0 + (T1 + (0ℚ + (Cross4 + T1abs)))) ⟩
  (Wxy0 + (T1 + (0ℚ + (Cross4 + T1abs)))) * r ∎

------------------------------------------------------------------------
-- The pointwise centre bound
--
-- 逐点中心差界

abs-mul-h : (x y : RealI) (n : ℕ) →
  ∣ centre ∣ x *ℝ y ∣ℝ n - centre (∣ x ∣ℝ *ℝ ∣ y ∣ℝ) n ∣
  ≤ abs-mul-K x y * recipPow2 n
abs-mul-h x y n =
  let Mx , Mx0≤ , Mx-bnd = centre-mag x
      My , My0≤ , My-bnd = centre-mag y
      wx0 = width x 0
      wy0 = width y 0
      T1 = wx0 * wy0 * half
      T1abs = width ∣ x ∣ℝ 0 * width ∣ y ∣ℝ 0 * half
      Wxy0 = width (x *ℝ y) 0
      Cross4 = My * wx0 + Mx * wy0 + wx0 * wy0
      K = Wxy0 + (T1 + (0ℚ + (Cross4 + T1abs)))
      nn = n +N n
      4n = nn +N nn
      r2 = recipPow2 nn
      r = recipPow2 n
      r≤1 : r ≤ 1ℚ
      r≤1 = recipPow2-n≤1 n
      0≤r : 0ℚ ≤ r
      0≤r = 0≤recipPow2 n
      r2≡rr : r2 ≡ r * r
      r2≡rr = recipPow2-mul n n
      r2≤r : r2 ≤ r
      r2≤r =
        subst (λ z → z ≤ r) (sym r2≡rr)
          (≤-trans (*-monoˡ-≤-nonNeg r {{nonNegative 0≤r}} r≤1)
             (≤-reflexive (*-identityʳ r)))
      r4 = recipPow2 4n
      r4≡ : r4 ≡ r2 * r2
      r4≡ = recipPow2-mul nn nn
      r4≤r2 : r4 ≤ r2
      r4≤r2 =
        subst (λ z → z ≤ r2) (sym r4≡)
          (≤-trans (*-monoˡ-≤-nonNeg r2
                      {{nonNegative (0≤recipPow2 nn)}}
                      (recipPow2-n≤1 nn))
             (≤-reflexive (*-identityʳ r2)))
      r4≤r : r4 ≤ r
      r4≤r = ≤-trans r4≤r2 r2≤r
      cx4 = centre x (nn +N nn)
      cy4 = centre y (nn +N nn)
      a' = centre (x *ℝ y) nn
      A = centre ∣ x *ℝ y ∣ℝ n
      B = centre (∣ x ∣ℝ *ℝ ∣ y ∣ℝ) n
      bx = centre ∣ x ∣ℝ nn
      by = centre ∣ y ∣ℝ nn

      -- e2: A vs |a'|.
      --
      -- e2：A 与 |a'| 的比较。
      e2 : ∣ A - ∣ a' ∣ ∣ ≤ Wxy0 * r
      e2 =
        let can : centre ∣ x *ℝ y ∣ℝ n ≡
                  halveQ (absLo (l (x *ℝ y) nn) (u (x *ℝ y) nn) +
                         absHi (l (x *ℝ y) nn) (u (x *ℝ y) nn))
            can = centre-abs-node (x *ℝ y) n
            e2raw : ∣ A - ∣ a' ∣ ∣ ≤ width (x *ℝ y) nn
            e2raw =
              subst (λ z → ∣ z - ∣ a' ∣ ∣ ≤ width (x *ℝ y) nn) (sym can)
                (abs-centre-≤ (l (x *ℝ y) nn) (u (x *ℝ y) nn)
                   (<⇒≤ (RealI.lo (node (x *ℝ y) nn))))
        in ≤-trans e2raw
             (≤-trans (width-n (x *ℝ y) nn)
                (*-monoˡ-≤-nonNeg Wxy0
                   {{nonNegative (0≤width-n (x *ℝ y) 0)}}
                   r2≤r))

      -- e2b: a' vs cx4*cy4.
      --
      -- e2b：a' 与 cx4*cy4 的比较。
      e2b : ∣ a' - cx4 * cy4 ∣ ≤ T1 * r
      e2b =
        ≤-trans (term1' x y nn)
          (*-monoˡ-≤-nonNeg T1
            {{nonNegative
               (mul-nn (wx0 * wy0) half
                  (mul-nn wx0 wy0 (0≤width-n x 0) (0≤width-n y 0))
                  (<⇒≤ 0<half))}} r2≤r)

      -- e3: B vs bx*by.
      --
      -- e3：B 与 bx*by 的比较。
      e3 : ∣ B - bx * by ∣ ≤ T1abs * r
      e3 =
        subst (λ d → ∣ B - d ∣ ≤ T1abs * r)
          (cong₂ (λ a b → centre ∣ x ∣ℝ a * centre ∣ y ∣ℝ b)
             (mul2eq n) (mul2eq n))
          (term1 ∣ x ∣ℝ ∣ y ∣ℝ n)

      -- e4: bx vs |cx4|.
      --
      -- e4：bx 与 |cx4| 的比较。
      e4 : ∣ bx - ∣ cx4 ∣ ∣ ≤ wx0 * r
      e4 =
        ≤-trans (abs-centre-gap x nn)
          (≤-trans (width-n x 4n)
             (*-monoˡ-≤-nonNeg wx0
                {{nonNegative (0≤width-n x 0)}} r4≤r))

      -- e5: by vs |cy4|.
      --
      -- e5：by 与 |cy4| 的比较。
      e5 : ∣ by - ∣ cy4 ∣ ∣ ≤ wy0 * r
      e5 =
        ≤-trans (abs-centre-gap y nn)
          (≤-trans (width-n y 4n)
             (*-monoˡ-≤-nonNeg wy0
                {{nonNegative (0≤width-n y 0)}} r4≤r))

      -- The absolute value of a product equals the product of absolute values.
      --
      -- 乘积的绝对值等于绝对值的乘积。
      mulabs : ∣ cx4 * cy4 ∣ ≡ ∣ cx4 ∣ * ∣ cy4 ∣
      mulabs = ∣p*q∣≡∣p∣*∣q∣ cx4 cy4

      -- |bx| ≤ Mx + wx0.
      --
      -- |bx| 不超过 Mx + wx0。
      bxB : ∣ bx ∣ ≤ Mx + wx0
      bxB = centre-abs-bound x nn Mx Mx-bnd

      -- Cross term: the difference of the two products is bounded by Cross4*r.
      --
      -- 交叉项：两乘积之差的绝对值不超过 Cross4*r。
      cross : ∣ (∣ cx4 ∣ * ∣ cy4 ∣) - bx * by ∣ ≤ Cross4 * r
      cross =
        let p = ∣ cx4 ∣
            q = ∣ cy4 ∣
            inv0 : neg bx * q + bx * q ≡ 0ℚ
            inv0 =
              begin neg bx * q + bx * q
                ≡⟨ cong (_+ bx * q) (sym (QP.neg-distribˡ-* bx q)) ⟩
              neg (bx * q) + bx * q
                ≡⟨ QP.+-inverseˡ (bx * q) ⟩
              0ℚ ∎
            -- Identity: p*q - bx*by = (p-bx)*q + bx*(q-by).
            --
            -- 恒等式：将 p*q - bx*by 拆成两项。
            ide : p * q + neg (bx * by) ≡
                    (p - bx) * q + bx * (q - by)
            ide =
              sym (
              begin (p - bx) * q + bx * (q - by)
                ≡⟨ refl ⟩
              (p + neg bx) * q + bx * (q + neg by)
                ≡⟨ cong₂ _+_ (*-distribʳ-+ q p (neg bx))
                            (QP.*-distribˡ-+ bx q (neg by)) ⟩
              (p * q + neg bx * q) + (bx * q + bx * neg by)
                ≡⟨ cong (λ z → (p * q + neg bx * q) + (bx * q + z))
                   (sym (QP.neg-distribʳ-* bx by)) ⟩
              (p * q + neg bx * q) + (bx * q + neg (bx * by))
                ≡⟨ sym (+-assoc (p * q + neg bx * q) (bx * q) (neg (bx * by))) ⟩
              ((p * q + neg bx * q) + bx * q) + neg (bx * by)
                ≡⟨ cong (_+ neg (bx * by))
                   (+-assoc (p * q) (neg bx * q) (bx * q)) ⟩
              (p * q + (neg bx * q + bx * q)) + neg (bx * by)
                ≡⟨ cong (λ z → (p * q + z) + neg (bx * by)) inv0 ⟩
              (p * q + 0ℚ) + neg (bx * by)
                ≡⟨ cong (λ z → z + neg (bx * by)) (+-identityʳ (p * q)) ⟩
              p * q + neg (bx * by)
                ∎)
            t1 : ∣ (p - bx) * q ∣ ≤ (wx0 * r) * My
            t1 =
              let a1 : ∣ p - bx ∣ ≤ wx0 * r
                  a1 =
                    let s : p - bx ≡ neg (bx - p)
                        s =
                          begin p - bx
                            ≡⟨ +-comm p (neg bx) ⟩
                          neg bx + p
                            ≡⟨ cong (neg bx +_) (sym (negneg p)) ⟩
                          neg bx + neg (neg p)
                            ≡⟨ sym (neg-distrib-+ bx (neg p)) ⟩
                          neg (bx - p) ∎
                        e : ∣ p - bx ∣ ≡ ∣ bx - p ∣
                        e =
                          begin ∣ p - bx ∣
                            ≡⟨ cong ∣_∣ s ⟩
                          ∣ neg (bx - p) ∣
                            ≡⟨ QP.∣-p∣≡∣p∣ (bx - p) ⟩
                          ∣ bx - p ∣ ∎
                    in subst (λ z → z ≤ wx0 * r) (sym e) e4
                  a2raw : q ≤ My
                  a2raw = My-bnd 4n
                  a2 : ∣ q ∣ ≤ My
                  a2 =
                    subst (λ z → z ≤ My) (sym (QP.∣∣p∣∣≡∣p∣ cy4)) a2raw
                  eq : ∣ (p - bx) * q ∣ ≡ ∣ p - bx ∣ * ∣ q ∣
                  eq = ∣p*q∣≡∣p∣*∣q∣ (p - bx) q
              in subst (λ z → z ≤ (wx0 * r) * My) (sym eq)
                   (*-mono-≤-nonNeg (0≤∣p∣ (p - bx)) a1
                      (0≤∣p∣ q) a2)
            t2 : ∣ bx * (q - by) ∣ ≤ (Mx + wx0) * (wy0 * r)
            t2 =
              let b1 : ∣ q - by ∣ ≤ wy0 * r
                  b1 =
                    let s : q - by ≡ neg (by - q)
                        s =
                          begin q - by
                            ≡⟨ +-comm q (neg by) ⟩
                          neg by + q
                            ≡⟨ cong (neg by +_) (sym (negneg q)) ⟩
                          neg by + neg (neg q)
                            ≡⟨ sym (neg-distrib-+ by (neg q)) ⟩
                          neg (by - q) ∎
                        e : ∣ q - by ∣ ≡ ∣ by - q ∣
                        e =
                          begin ∣ q - by ∣
                            ≡⟨ cong ∣_∣ s ⟩
                          ∣ neg (by - q) ∣
                            ≡⟨ QP.∣-p∣≡∣p∣ (by - q) ⟩
                          ∣ by - q ∣ ∎
                    in subst (λ z → z ≤ wy0 * r) (sym e) e5
                  b2 : ∣ bx ∣ ≤ Mx + wx0
                  b2 = bxB
                  eq : ∣ bx * (q - by) ∣ ≡ ∣ bx ∣ * ∣ q - by ∣
                  eq = ∣p*q∣≡∣p∣*∣q∣ bx (q - by)
              in subst (λ z → z ≤ (Mx + wx0) * (wy0 * r)) (sym eq)
                   (*-mono-≤-nonNeg (0≤∣p∣ bx) b2
                      (0≤∣p∣ (q - by)) b1)
        in
        let inner : My * wx0 + wy0 * (Mx + wx0) ≡ Cross4
            inner =
              begin My * wx0 + wy0 * (Mx + wx0)
                ≡⟨ cong (My * wx0 +_) (QP.*-distribˡ-+ wy0 Mx wx0) ⟩
              My * wx0 + (wy0 * Mx + wy0 * wx0)
                ≡⟨ cong (λ z → My * wx0 + z)
                    (cong₂ _+_ (*-comm wy0 Mx) (*-comm wy0 wx0)) ⟩
              My * wx0 + (Mx * wy0 + wx0 * wy0)
                ≡⟨ sym (+-assoc (My * wx0) (Mx * wy0) (wx0 * wy0)) ⟩
              Cross4 ∎
            tri :
              ∣ (p - bx) * q + bx * (q - by) ∣ ≤
              ∣ (p - bx) * q ∣ + ∣ bx * (q - by) ∣
            tri = ∣p+q∣≤∣p∣+∣q∣ ((p - bx) * q) (bx * (q - by))
            sumEq :
              (wx0 * r) * My + (Mx + wx0) * (wy0 * r)
              ≡ Cross4 * r
            sumEq =
              begin (wx0 * r) * My + (Mx + wx0) * (wy0 * r)
                ≡⟨ cong₂ _+_
                    (*-comm (wx0 * r) My)
                    (*-comm (Mx + wx0) (wy0 * r)) ⟩
              My * (wx0 * r) +
                (wy0 * r) * (Mx + wx0)
                ≡⟨ cong₂ _+_
                    (begin My * (wx0 * r)
                      ≡⟨ cong (My *_) (*-comm wx0 r) ⟩
                    My * (r * wx0)
                      ≡⟨ sym (*-assoc My r wx0) ⟩
                    (My * r) * wx0
                      ≡⟨ cong (_* wx0) (*-comm My r) ⟩
                    (r * My) * wx0
                      ≡⟨ *-assoc r My wx0 ⟩
                    r * (My * wx0) ∎)
                    (begin (wy0 * r) * (Mx + wx0)
                      ≡⟨ cong (_* (Mx + wx0)) (*-comm wy0 r) ⟩
                    (r * wy0) * (Mx + wx0)
                      ≡⟨ *-assoc r wy0 (Mx + wx0) ⟩
                    r * (wy0 * (Mx + wx0)) ∎) ⟩
              r * (My * wx0) + r * (wy0 * (Mx + wx0))
                ≡⟨ sym (QP.*-distribˡ-+ r (My * wx0)
                        (wy0 * (Mx + wx0))) ⟩
              r * (My * wx0 + wy0 * (Mx + wx0))
                ≡⟨ *-comm r (My * wx0 + wy0 * (Mx + wx0)) ⟩
              (My * wx0 + wy0 * (Mx + wx0)) * r
                ≡⟨ cong (λ z → z * r) inner ⟩
              Cross4 * r ∎
            pp : ∣ (p - bx) * q + bx * (q - by) ∣ ≤ Cross4 * r
            pp = ≤-trans tri
                  (subst (λ z →
                    ∣ (p - bx) * q ∣ + ∣ bx * (q - by) ∣ ≤ z)
                    sumEq (+-mono-≤ t1 t2))
        in subst (λ z → ∣ z ∣ ≤ Cross4 * r) (sym ide) pp

      d1 : ∣ A - ∣ a' ∣ ∣ ≤ Wxy0 * r
      d1 = e2
      d2 : ∣ ∣ a' ∣ - ∣ cx4 * cy4 ∣ ∣ ≤ T1 * r
      d2 = ≤-trans (abs-lip a' (cx4 * cy4)) e2b
      d3 : ∣ ∣ cx4 * cy4 ∣ - ∣ cx4 ∣ * ∣ cy4 ∣ ∣ ≤ 0ℚ
      d3 =
        let e : ∣ cx4 * cy4 ∣ ≡ ∣ cx4 ∣ * ∣ cy4 ∣
            e = mulabs
            zz : ∣ (∣ cx4 ∣ * ∣ cy4 ∣) - (∣ cx4 ∣ * ∣ cy4 ∣) ∣ ≡ 0ℚ
            zz = cong ∣_∣ (QP.+-inverseʳ (∣ cx4 ∣ * ∣ cy4 ∣))
        in subst (λ z → ∣ z - (∣ cx4 ∣ * ∣ cy4 ∣) ∣ ≤ 0ℚ) (sym e)
             (≤-reflexive zz)
      d4 : ∣ (∣ cx4 ∣ * ∣ cy4 ∣) - bx * by ∣ ≤ Cross4 * r
      d4 = cross
      d5 : ∣ bx * by - B ∣ ≤ T1abs * r
      d5 =
        let s : B - bx * by ≡ neg (bx * by - B)
            s =
              begin B + neg (bx * by)
                ≡⟨ +-comm B (neg (bx * by)) ⟩
              neg (bx * by) + B
                ≡⟨ cong (neg (bx * by) +_) (sym (negneg B)) ⟩
              neg (bx * by) + neg (neg B)
                ≡⟨ sym (neg-distrib-+ (bx * by) (neg B)) ⟩
              neg (bx * by + neg B) ∎
            e : ∣ B - bx * by ∣ ≡ ∣ bx * by - B ∣
            e =
              begin ∣ B - bx * by ∣
                ≡⟨ cong ∣_∣ s ⟩
              ∣ neg (bx * by - B) ∣
                ≡⟨ QP.∣-p∣≡∣p∣ (bx * by - B) ⟩
              ∣ bx * by - B ∣ ∎
        in subst (λ z → z ≤ T1abs * r) e e3
      S = Wxy0 * r + (T1 * r + (0ℚ + (Cross4 * r + T1abs * r)))
      c5 : ∣ A - B ∣ ≤ S
      c5 = chain5 A (∣ a' ∣) (∣ cx4 * cy4 ∣)
              (∣ cx4 ∣ * ∣ cy4 ∣) (bx * by) B
              (Wxy0 * r) (T1 * r) 0ℚ (Cross4 * r) (T1abs * r)
              d1 d2 d3 d4 d5
      sumEq : S ≡ K * r
      sumEq =
        let fact : (k : ℚ) → k * r ≡ r * k
            fact k = *-comm k r
            term : ℚ
            term = r * Wxy0 + (r * T1 + (0ℚ + (r * Cross4 + r * T1abs)))
            right : 0ℚ + (Cross4 * r + T1abs * r)
                    ≡ 0ℚ + (r * Cross4 + r * T1abs)
            right =
              cong₂ _+_ (refl {x = 0ℚ})
                (cong₂ _+_ (fact Cross4) (fact T1abs))
            fact2 : r * K ≡ term
            fact2 =
              begin r * K
                ≡⟨ QP.*-distribˡ-+ r Wxy0 (T1 + (0ℚ + (Cross4 + T1abs))) ⟩
              r * Wxy0 + r * (T1 + (0ℚ + (Cross4 + T1abs)))
                ≡⟨ cong (r * Wxy0 +_)
                    (QP.*-distribˡ-+ r T1 (0ℚ + (Cross4 + T1abs))) ⟩
              r * Wxy0 + (r * T1 + r * (0ℚ + (Cross4 + T1abs)))
                ≡⟨ cong (λ z → r * Wxy0 + (r * T1 + z))
                    (begin r * (0ℚ + (Cross4 + T1abs))
                      ≡⟨ QP.*-distribˡ-+ r 0ℚ (Cross4 + T1abs) ⟩
                    r * 0ℚ + r * (Cross4 + T1abs)
                      ≡⟨ cong (λ z → z + r * (Cross4 + T1abs))
                          (QP.*-zeroʳ r) ⟩
                    0ℚ + r * (Cross4 + T1abs)
                      ≡⟨ cong (λ z → 0ℚ + z)
                          (QP.*-distribˡ-+ r Cross4 T1abs) ⟩
                    0ℚ + (r * Cross4 + r * T1abs) ∎) ⟩
              term ∎
        in
        begin S
          ≡⟨ cong₂ _+_ (fact Wxy0)
              (cong₂ _+_ (fact T1) right) ⟩
        term
          ≡⟨ sym fact2 ⟩
        r * K
          ≡⟨ *-comm r K ⟩
        K * r ∎
  in subst (λ z → ∣ A - B ∣ ≤ z) sumEq c5

------------------------------------------------------------------------
-- Multiplicative law
--
-- 乘性定律

abs-mul : (x y : RealI) →
  ∣ x *ℝ y ∣ℝ ≈ℝ ∣ x ∣ℝ *ℝ ∣ y ∣ℝ
abs-mul x y =
  ≈ℝ-of-rec ∣ x *ℝ y ∣ℝ (∣ x ∣ℝ *ℝ ∣ y ∣ℝ)
    (abs-mul-K x y) (abs-mul-K≥0 x y) (abs-mul-h x y)
