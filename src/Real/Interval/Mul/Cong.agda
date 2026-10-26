------------------------------------------------------------------------
-- Multiplication compatibility for interval reals
--
-- 区间实数的乘法相容性
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module Real.Interval.Mul.Cong where

open import Data.Nat hiding (NonZero; _+_) renaming (_<_ to _<ℕ_; _≤_ to _≤ℕ_
  ; _*_ to _ℕ*_; _≥_ to _≥ℕ_)
import Data.Nat.Properties as ℕP
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.Rational using
  (ℚ; 0ℚ; 1ℚ; _+_; _-_; _*_; _<_; _≤_; ∣_∣; NonZero; Positive)
open import Data.Rational.Base using
  (1/_; _÷_; mkℚ; positive; nonNegative; *<*) renaming (-_ to neg)
open import Data.Integer using (+_; +<+)
open import Data.Nat.Coprimality using (1-coprimeTo)
open import Data.Nat using (s≤s; z≤n)
open import Data.Rational.Properties using
  (≤-refl; ≤-reflexive; ≤-trans; <⇒≤; ≤-<-trans; <-trans; +-mono-≤; +-mono-<
  ; +-mono-≤-<; +-identityʳ; +-assoc; *-assoc; *-comm; *-identityˡ; *-identityʳ
  ; *-inverseʳ; *-inverseˡ; *-monoˡ-≤-nonNeg; *-monoʳ-≤-nonNeg; *-zeroˡ
  ; pos⇒nonNeg; pos⇒nonZero; pos*pos⇒pos; positive⁻¹; 1/pos⇒pos; *-distribˡ-+
  ; neg-distribˡ-*; 0≤∣p∣; ∣p*q∣≡∣p∣*∣q∣; ∣p+q∣≤∣p∣+∣q∣)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; cong; cong₂; sym; trans; subst; module ≡-Reasoning)
open ≡-Reasoning

open import Base.RationalRing using (0<1; 0≤1)
open import Real using
  (ε; 0<ε; half; telescope; embed; embed-mono-≤; embed-suc-nonZero; 0<embed; embed-*)
open import Real.Interval using (RealI)
open import Real.Interval.Mul using (_*ℝ_)
open import Real.Interval.Bounded using (bounded)
open import Real.IntervalEquiv using
  (centre; width; centre-l; centre-u; recipPow2; embed-mono-<)
open import Real.Interval.Equiv using (_≈ℝ_)
open import Real.Interval.Kit using
  (0≤half; two-half; n+n≡2n; recipPow2-bound; *-mono-≤-nonNeg; tri-diff; abs-swap
  ; recip-antitone; strict-recip; pick)
open import Real.Interval.Node using (0≤width-n)
open import Real.Interval.Mul.Core using (term1)

private
  0<6 : 0ℚ < embed 6
  0<6 = 0<embed 5

  -- Left distributivity of multiplication over subtraction.
  --
  -- 乘法对减法的左分配律。
  *-distribˡ-_- : (x y z : ℚ) → x * (y - z) ≡ x * y - x * z
  *-distribˡ-_- x y z = begin
    x * (y + neg z)
      ≡⟨ *-distribˡ-+ x y (neg z) ⟩
    x * y + x * neg z
      ≡⟨ cong (λ w → x * y + w) (begin
        x * neg z        ≡⟨ *-comm x (neg z) ⟩
        neg z * x        ≡⟨ sym (neg-distribˡ-* z x) ⟩
        neg (z * x)      ≡⟨ cong neg (*-comm z x) ⟩
        neg (x * z)      ∎) ⟩
    x * y + neg (x * z)
      ≡⟨⟩
    x * y - x * z
    ∎

  -- Right distributivity of multiplication over subtraction.
  --
  -- 乘法对减法的右分配律。
  *-distribʳ-_- : (y x z : ℚ) → (x - z) * y ≡ x * y - z * y
  *-distribʳ-_- y x z = begin
    (x + neg z) * y
      ≡⟨ *-comm (x + neg z) y ⟩
    y * (x + neg z)
      ≡⟨ *-distribˡ-_- y x z ⟩
    y * x - y * z
      ≡⟨ cong₂ _-_ (*-comm y x) (*-comm y z) ⟩
    x * y - z * y
    ∎

-- Cross-product difference bound:
-- |a*b - a'*b'| ≤ |a|*|b-b'| + |b'|*|a-a'|.
--
-- 叉积差界：
-- |a*b - a'*b'| ≤ |a|*|b-b'| + |b'|*|a-a'|。
cross-lemma : (a b a' b' : ℚ) →
  ∣ a * b + neg (a' * b') ∣ ≤
    ∣ a ∣ * ∣ b + neg b' ∣ + ∣ b' ∣ * ∣ a + neg a' ∣
cross-lemma a b a' b' = outer
  where
  nb = b + neg b'
  na = a + neg a'
  d1 = a * nb
  d2 = na * b'
  goal = ∣ a ∣ * ∣ nb ∣ + ∣ b' ∣ * ∣ na ∣
  abs1≡ : ∣ d1 ∣ ≡ ∣ a ∣ * ∣ nb ∣
  abs1≡ = ∣p*q∣≡∣p∣*∣q∣ a nb
  abs2≡ : ∣ d2 ∣ ≡ ∣ b' ∣ * ∣ na ∣
  abs2≡ = trans (∣p*q∣≡∣p∣*∣q∣ na b')
                (*-comm ∣ na ∣ ∣ b' ∣)
  sum≡ : ∣ d1 ∣ + ∣ d2 ∣ ≡ goal
  sum≡ = cong₂ _+_ abs1≡ abs2≡
  p = a * b ; q = a * b' ; r = a' * b'
  t1≡ : d1 ≡ p + neg q
  t1≡ = *-distribˡ-_- a b b'
  t2≡ : d2 ≡ q + neg r
  t2≡ = *-distribʳ-_- b' a a'
  idn : (a * b + neg (a' * b')) ≡ d1 + d2
  idn = trans (sym (telescope p q r))
              (cong₂ _+_ (sym t1≡) (sym t2≡))
  inner : ∣ d1 + d2 ∣ ≤ goal
  inner = subst (λ s → ∣ d1 + d2 ∣ ≤ s) sum≡ (∣p+q∣≤∣p∣+∣q∣ d1 d2)
  outer : ∣ a * b + neg (a' * b') ∣ ≤ goal
  outer = subst P (sym idn) inner
    where P : ℚ → Set _
          P z = ∣ z ∣ ≤ goal

tri3-lemma : (p1 Q Q' p2 : ℚ) →
  (∣ (p1 - p2) ∣) ≤
    ((∣ (p1 - Q) ∣) + (∣ (Q - Q') ∣)) + (∣ (p2 - Q') ∣)
tri3-lemma p1 Q Q' p2 = ≤-trans outer (≤-trans add-monoˡ assoc)
  where
  outer : (∣ (p1 - p2) ∣) ≤ (∣ (p1 - Q) ∣) + (∣ (Q - p2) ∣)
  outer = tri-diff p1 Q p2
  inner : (∣ (Q - p2) ∣) ≤ (∣ (Q - Q') ∣) + (∣ (p2 - Q') ∣)
  inner = subst (λ z → (∣ (Q - p2) ∣) ≤ (∣ (Q - Q') ∣) + z)
                (abs-swap Q' p2) (tri-diff Q Q' p2)
  add-monoˡ : (∣ (p1 - Q) ∣) + (∣ (Q - p2) ∣)
              ≤ (∣ (p1 - Q) ∣) + ((∣ (Q - Q') ∣) + (∣ (p2 - Q') ∣))
  add-monoˡ = +-mono-≤ (≤-refl {x = ∣ (p1 - Q) ∣}) inner
  assoc : (∣ (p1 - Q) ∣) + ((∣ (Q - Q') ∣) + (∣ (p2 - Q') ∣))
          ≤ ((∣ (p1 - Q) ∣) + (∣ (Q - Q') ∣)) + (∣ (p2 - Q') ∣)
  assoc = ≤-reflexive
    (sym (+-assoc (∣ (p1 - Q) ∣) (∣ (Q - Q') ∣) (∣ (p2 - Q') ∣)))

mul-cong-final : (k : ℕ) (p1 p2 Q Q' εL : ℚ) →
  εL < (ε k) ÷ embed 4 →
  (∣ (p1 - p2) ∣) ≤ εL + εL + εL →
  (∣ (p1 - p2) ∣) < ε k
mul-cong-final k p1 p2 Q Q' εL εL<4 bound-total =
  ≤-<-trans bound-total (<-trans step1 step2)
  where
  q : ℚ
  q = (ε k) ÷ embed 4

  4-nz : NonZero (embed 4)
  4-nz = embed-suc-nonZero {3}

  inv4 : ℚ
  inv4 = 1/_ (embed 4) {{4-nz}}

  inv4-pos : Positive inv4
  inv4-pos = 1/pos⇒pos (embed 4)

  εk-pos : Positive (ε k)
  εk-pos = 1/pos⇒pos (embed (suc k))

  q-pos : Positive q
  q-pos = pos*pos⇒pos (ε k) {{εk-pos}} inv4 {{inv4-pos}}

  0<q : 0ℚ < q
  0<q = positive⁻¹ q {{q-pos}}

  sum3< : ∀ {a b : ℚ} → a < b → a + a + a < b + b + b
  sum3< a<b = +-mono-< (+-mono-< a<b a<b) a<b

  step1 : εL + εL + εL < q + q + q
  step1 = sum3< εL<4

  q*≡ : q ≡ (ε k) * inv4
  q*≡ = refl

  chain : embed 4 * q ≡ ε k
  chain = begin
    embed 4 * q
      ≡⟨ cong (embed 4 *_) q*≡ ⟩
    embed 4 * ((ε k) * inv4)
      ≡⟨ sym (*-assoc (embed 4) (ε k) inv4) ⟩
    (embed 4 * ε k) * inv4
      ≡⟨ cong (λ z → z * inv4) (*-comm (embed 4) (ε k)) ⟩
    ((ε k) * embed 4) * inv4
      ≡⟨ *-assoc (ε k) (embed 4) inv4 ⟩
    (ε k) * (embed 4 * inv4)
      ≡⟨ cong ((ε k) *_) (*-inverseʳ (embed 4) {{4-nz}}) ⟩
    (ε k) * 1ℚ
      ≡⟨ *-identityʳ (ε k) ⟩
    ε k
    ∎

  q2≡ : q + q ≡ q * embed 2
  q2≡ = begin
    q + q
      ≡⟨ cong₂ _+_ (sym (*-identityʳ q)) (sym (*-identityʳ q)) ⟩
    q * 1ℚ + q * 1ℚ
      ≡⟨ sym (*-distribˡ-+ q 1ℚ 1ℚ) ⟩
    q * (1ℚ + 1ℚ)
      ≡⟨⟩
    q * embed 2
    ∎

  s22 : embed 2 + embed 2 ≡ embed 4
  s22 = refl

  q4≡ : q + q + q + q ≡ embed 4 * q
  q4≡ = begin
    q + q + q + q
      ≡⟨ +-assoc (q + q) q q ⟩
    (q + q) + (q + q)
      ≡⟨ cong₂ _+_ q2≡ q2≡ ⟩
    q * embed 2 + q * embed 2
      ≡⟨ sym (*-distribˡ-+ q (embed 2) (embed 2)) ⟩
    q * (embed 2 + embed 2)
      ≡⟨ cong (q *_) s22 ⟩
    q * embed 4
      ≡⟨ *-comm q (embed 4) ⟩
    embed 4 * q
    ∎

  4q≡ : q + q + q + q ≡ ε k
  4q≡ = trans q4≡ chain

  3q<4q : q + q + q < q + q + q + q
  3q<4q = subst (λ z → z < (q + q + q) + q)
                (+-identityʳ (q + q + q))
                (+-mono-≤-< (≤-refl {x = q + q + q}) 0<q)

  step2 : q + q + q < ε k
  step2 = subst (λ z → q + q + q < z) 4q≡ 3q<4q

-- The ε modulus shrinks by a factor of four:
-- ε (4 * (k+1)) < ε k / 4.
--
-- ε 模数缩小为四分之一：
-- ε (4 * (k+1)) < ε k / 4。
mul-cong-ε : (k : ℕ) → ε (4 ℕ* suc k) < (ε k) ÷ embed 4
mul-cong-ε k = subst (λ z → ε (4 ℕ* suc k) < z) (sym εk4≡) raw
  where
  raw1 : ℕ
  raw1 = 4 ℕ* suc k
  den1 : ℕ
  den1 = suc (raw1 ∸ 1)
  den1≡L : den1 ≡ 4 ℕ* suc k
  den1≡L = begin
    den1
      ≡⟨ cong (λ z → suc (z ∸ 1)) (ℕP.*-comm 4 (suc k)) ⟩
    suc (((suc k) ℕ* 4) ∸ 1)
      ≡⟨⟩
    (suc k) ℕ* 4
      ≡⟨ ℕP.*-comm (suc k) 4 ⟩
    4 ℕ* suc k
    ∎
  0<den1 : 0ℚ < embed den1
  0<den1 = 0<embed (den1 ∸ 1)
  den1<den2 : den1 <ℕ suc den1
  den1<den2 = s≤s ℕP.≤-refl
  ed1<ed2 : embed den1 < embed (suc den1)
  ed1<ed2 = embed-mono-< den1<den2
  n1-nz : NonZero (embed (suc k))
  n1-nz = embed-suc-nonZero
  n4-nz : NonZero (embed 4)
  n4-nz = pos⇒nonZero (embed 4)
  den1-nz : NonZero (embed den1)
  den1-nz = pos⇒nonZero (embed den1)
  r1 = 1/_ (embed (suc k)) {{n1-nz}}
  r4 = 1/_ (embed 4) {{n4-nz}}
  rd = mkℚ (+ 1) (raw1 ∸ 1) (1-coprimeTo raw1)
  den1≡ : embed den1 ≡ embed 4 * embed (suc k)
  den1≡ = begin
    embed den1
      ≡⟨ cong embed den1≡L ⟩
    embed (4 ℕ* suc k)
      ≡⟨ cong embed (ℕP.*-comm 4 (suc k)) ⟩
    embed ((suc k) ℕ* 4)
      ≡⟨ sym (embed-* (suc k) 4) ⟩
    embed (suc k) * embed 4
      ≡⟨ *-comm (embed (suc k)) (embed 4) ⟩
    embed 4 * embed (suc k)
      ∎
  lhs≡1 : (r1 * r4) * embed den1 ≡ 1ℚ
  lhs≡1 = begin
    (r1 * r4) * embed den1
      ≡⟨ cong ((r1 * r4) *_) den1≡ ⟩
    (r1 * r4) * (embed 4 * embed (suc k))
      ≡⟨ *-assoc r1 r4 (embed 4 * embed (suc k)) ⟩
    r1 * (r4 * (embed 4 * embed (suc k)))
      ≡⟨ cong (r1 *_) (sym (*-assoc r4 (embed 4) (embed (suc k)))) ⟩
    r1 * ((r4 * embed 4) * embed (suc k))
      ≡⟨ cong (λ z → r1 * (z * embed (suc k)))
              (*-inverseˡ (embed 4) {{n4-nz}}) ⟩
    r1 * (1ℚ * embed (suc k))
      ≡⟨ cong (r1 *_) (*-identityˡ (embed (suc k))) ⟩
    r1 * embed (suc k)
      ≡⟨ *-inverseˡ (embed (suc k)) {{n1-nz}} ⟩
    1ℚ
      ∎
  εk4≡ : (ε k) ÷ embed 4 ≡ rd
  εk4≡ = begin
    (ε k) ÷ embed 4
      ≡⟨⟩
    r1 * r4
      ≡⟨ sym (*-identityʳ (r1 * r4)) ⟩
    (r1 * r4) * 1ℚ
      ≡⟨ cong ((r1 * r4) *_) (sym (*-inverseʳ (embed den1) {{den1-nz}})) ⟩
    (r1 * r4) * (embed den1 * rd)
      ≡⟨ sym (*-assoc (r1 * r4) (embed den1) rd) ⟩
    ((r1 * r4) * embed den1) * rd
      ≡⟨ cong (λ z → z * rd) lhs≡1 ⟩
    1ℚ * rd
      ≡⟨ *-identityˡ rd ⟩
    rd
      ∎
  raw : ε (4 ℕ* suc k) < rd
  raw = strict-recip (embed den1) (embed (suc den1)) 0<den1 ed1<ed2

-- a / 6 ≤ a for positive a.
--
-- 对正 a，有 a / 6 ≤ a。
÷6≤ : (a : ℚ) → 0ℚ < a → a ÷ embed 6 ≤ a
÷6≤ a 0<a = ≤-trans (≤-reflexive (*-comm a inv6))
  (≤-trans (*-monoʳ-≤-nonNeg a {{pos⇒nonNeg a {{positive 0<a}}}} 1/6≤1)
           (≤-reflexive (*-identityˡ a)))
  where
  6-nz : NonZero (embed 6)
  6-nz = pos⇒nonZero (embed 6) {{positive 0<6}}
  inv6 : ℚ
  inv6 = 1/_ (embed 6) {{6-nz}}
  1/6≤1 : inv6 ≤ 1ℚ
  1/6≤1 = ≤-trans (recip-antitone 0<1 (embed-mono-≤ (s≤s z≤n)))
                  (≤-reflexive (sym (*-identityʳ 1ℚ)))

-- a / 6 + a / 6 ≤ a for positive a.
--
-- 对正 a，有 a / 6 + a / 6 ≤ a。
÷6+÷6≤ : (a : ℚ) → 0ℚ < a → a ÷ embed 6 + a ÷ embed 6 ≤ a
÷6+÷6≤ a 0<a =
  ≤-trans (+-mono-≤ e6≤h2 e6≤h2) (≤-reflexive (two-half a))
  where
  6-nz : NonZero (embed 6)
  6-nz = pos⇒nonZero (embed 6) {{positive 0<6}}
  inv6 : ℚ
  inv6 = 1/_ (embed 6) {{6-nz}}
  2≤6ℕ : 2 ≤ℕ 6
  2≤6ℕ = ℕP.m≤n+m 2 4
  0<2 : 0ℚ < embed 2
  0<2 = *<* (+<+ (s≤s z≤n))
  inv6≤half : inv6 ≤ half
  inv6≤half = recip-antitone 0<2 (embed-mono-≤ 2≤6ℕ)
  e6 = a ÷ embed 6
  e6≡ : e6 ≡ a * inv6
  e6≡ = refl
  h2 = a * half
  e6≤h2 : e6 ≤ h2
  e6≤h2 = ≤-trans (≤-reflexive e6≡)
    (Data.Rational.Properties.*-monoˡ-≤-nonNeg a
      {{pos⇒nonNeg a {{positive 0<a}}}} inv6≤half)

-- Adding one preserves the order.
--
-- 加一保持序关系。
≤+1 : (x : ℚ) → x ≤ x + 1ℚ
≤+1 x = ≤-trans (≤-reflexive (sym (+-identityʳ x)))
                 (Data.Rational.Properties.+-monoʳ-≤ x 0≤1)

------------------------------------------------------------------------
-- Multiplication is compatible with interval equality
--
-- 乘法与区间相等相容

*ℝ-cong : {x x' y y' : RealI} → x ≈ℝ x' → y ≈ℝ y' →
  x *ℝ y ≈ℝ x' *ℝ y'
*ℝ-cong {x} {x'} {y} {y'} x≈x' y≈y' k = N , step
  where
  -- Uniform bounds on |centre x _| and |centre y' _|.
  --
  -- |centre x _| 与 |centre y' _| 的一致界。
  Mx = proj₁ (bounded x)
  Mx-b = proj₂ (bounded x)
  Mx-nn = proj₁ Mx-b
  ∣cx∣≤Mx : ∀ m → ∣ centre x m ∣ ≤ Mx
  ∣cx∣≤Mx m = proj₂ Mx-b m (centre x m) (centre-l x m) (centre-u x m)
  Myp = proj₁ (bounded y')
  Myp-b = proj₂ (bounded y')
  Myp-nn = proj₁ Myp-b
  ∣cyp∣≤Myp : ∀ m → ∣ centre y' m ∣ ≤ Myp
  ∣cyp∣≤Myp m = proj₂ Myp-b m (centre y' m) (centre-l y' m) (centre-u y' m)

  -- Geometric constants C1 = (w0x*w0y)*half,
  -- C2 for the primed pair.
  --
  -- 几何常数 C1 = (w0x*w0y)*half，C2 对应带撇的一对。
  C1 = (width x 0) * (width y 0) * half
  C2 = (width x' 0) * (width y' 0) * half
  0≤prod : ∀ {a b} → 0ℚ ≤ a → 0ℚ ≤ b → 0ℚ ≤ a * b
  0≤prod {a} {b} 0≤a 0≤b =
    ≤-trans (≤-reflexive (sym (*-zeroˡ b)))
            (*-monoʳ-≤-nonNeg b {{nonNegative 0≤b}} 0≤a)
  0≤w0xy : 0ℚ ≤ (width x 0) * (width y 0)
  0≤w0xy = 0≤prod (0≤width-n x 0) (0≤width-n y 0)
  0≤C1 : 0ℚ ≤ C1
  0≤C1 = 0≤prod 0≤w0xy 0≤half
  0≤w0xy' : 0ℚ ≤ (width x' 0) * (width y' 0)
  0≤w0xy' = 0≤prod (0≤width-n x' 0) (0≤width-n y' 0)
  0≤C2 : 0ℚ ≤ C2
  0≤C2 = 0≤prod 0≤w0xy' 0≤half

  -- ε L = 1/(4k+5), ε k / 4 = 1/(4k+4);
  -- the former denominator is larger.
  -- den1 is written in suc form so 1/embed den1 reduces canonically.
  --
  -- ε L = 1/(4k+5)，ε k / 4 = 1/(4k+4)；
  -- 前者的分母更大。
  -- den1 写成 suc 形式，使 1/embed den1 按规范方式归约。
  L = 4 ℕ* suc k
  εL<εk/4 : ε L < (ε k) ÷ embed 4
  εL<εk/4 = mul-cong-ε k

  -- Indices past which the two geometric errors are
  -- < ε L < ε k / 4.
  --
  -- 两个几何误差小于 ε L < ε k / 4 的指标下界。
  Ng1 = proj₁ (recipPow2-bound C1 0≤C1 L)
  g1< : ∀ n → Ng1 ≤ℕ n → C1 * recipPow2 n < ε L
  g1< = proj₂ (recipPow2-bound C1 0≤C1 L)
  Ng2 = proj₁ (recipPow2-bound C2 0≤C2 L)
  g2< : ∀ n → Ng2 ≤ℕ n → C2 * recipPow2 n < ε L
  g2< = proj₂ (recipPow2-bound C2 0≤C2 L)

  -- Cross terms: pick moduli at level L so each factor fits
  -- ε L / 6 < ε k / 4.
  --
  -- 交叉项：在层 L 选取模数，使每个因子满足
  -- ε L / 6 < ε k / 4。
  my = proj₁ (pick Mx Mx-nn L)
  my-bound : ε my * (Mx + 1ℚ) ≤ (ε L) ÷ embed 6
  my-bound = proj₂ (pick Mx Mx-nn L)
  mx = proj₁ (pick Myp Myp-nn L)
  mx-bound : ε mx * (Myp + 1ℚ) ≤ (ε L) ÷ embed 6
  mx-bound = proj₂ (pick Myp Myp-nn L)

  -- The equality hypotheses give moduli at which the centres are close.
  --
  -- 相等性假设给出中心值接近的模数。
  Ny = proj₁ (y≈y' my)
  Nx = proj₁ (x≈x' mx)
  Ny-close : ∀ n → n ≥ℕ Ny →
    ∣_∣ ((centre y n) - (centre y' n)) < ε my
  Ny-close = proj₂ (y≈y' my)
  Nx-close : ∀ n → n ≥ℕ Nx →
    ∣_∣ ((centre x n) - (centre x' n)) < ε mx
  Nx-close = proj₂ (x≈x' mx)

  NxNy = Nx ⊔ Ny
  Ng = Ng1 ⊔ Ng2
  -- N must be large enough: geometric tails and doubled indices
  -- for cross.
  --
  -- N 必须足够大：几何尾部以及交叉项的二倍指标。
  N = Ng ⊔ NxNy

  -- We require 2n ≥ Ny and 2n ≥ Nx; since 2n ≥ n it suffices
  -- that n ≥ Ny、Nx.
  --
  -- 我们需要 2n ≥ Ny 且 2n ≥ Nx；由于 2n ≥ n，
  -- 只需 n ≥ Ny、Nx。
  Nx≤NxNy : Nx ≤ℕ NxNy
  Nx≤NxNy = ℕP.m≤m⊔n Nx Ny
  NxNy≤NxNyNg : NxNy ≤ℕ NxNy ⊔ Ng
  NxNy≤NxNyNg = ℕP.m≤m⊔n NxNy Ng
  NxNyNg≤N : NxNy ⊔ Ng ≤ℕ N
  NxNyNg≤N = ℕP.≤-reflexive (ℕP.⊔-comm NxNy Ng)
  NxNy≤N : NxNy ≤ℕ N
  NxNy≤N = ℕP.≤-trans NxNy≤NxNyNg NxNyNg≤N
  N≥Nx : N ≥ℕ Nx
  N≥Nx = ℕP.≤-trans Nx≤NxNy NxNy≤N
  Ny≤NyNx : Ny ≤ℕ Ny ⊔ Nx
  Ny≤NyNx = ℕP.m≤m⊔n Ny Nx
  NyNx≤NxNy : Ny ⊔ Nx ≤ℕ NxNy
  NyNx≤NxNy = ℕP.≤-reflexive (ℕP.⊔-comm Ny Nx)
  Ny≤NxNy : Ny ≤ℕ NxNy
  Ny≤NxNy = ℕP.≤-trans Ny≤NyNx NyNx≤NxNy
  N≥Ny : N ≥ℕ Ny
  N≥Ny = ℕP.≤-trans Ny≤NxNy NxNy≤N
  Ng1≤Ng : Ng1 ≤ℕ Ng
  Ng1≤Ng = ℕP.m≤m⊔n Ng1 Ng2
  Ng≤N : Ng ≤ℕ N
  Ng≤N = ℕP.m≤m⊔n Ng NxNy
  N≥Ng1 : N ≥ℕ Ng1
  N≥Ng1 = ℕP.≤-trans Ng1≤Ng Ng≤N
  Ng2≤Ng : Ng2 ≤ℕ Ng
  Ng2≤Ng = ℕP.m≤n⊔m Ng1 Ng2
  N≥Ng2 : N ≥ℕ Ng2
  N≥Ng2 = ℕP.≤-trans Ng2≤Ng Ng≤N

  -- The cross-product inequality:
  -- |cx*cy - cx'*cy'| ≤ |cx|*|cy-cy'| + |cy'|*|cx-cx'|.
  --
  -- 叉积不等式：
  -- |cx*cy - cx'*cy'| ≤ |cx|*|cy-cy'| + |cy'|*|cx-cx'|。
  cross : ∀ n →
    ∣_∣ ((centre x n) * (centre y n) - (centre x' n) * (centre y' n))
      ≤ ∣_∣ (centre x n) * ∣_∣ ((centre y n) - (centre y' n))
        + ∣_∣ (centre y' n) * ∣_∣ ((centre x n) - (centre x' n))
  cross n = cross-lemma (centre x n) (centre y n) (centre x' n) (centre y' n)

  step : ∀ n → n ≥ℕ N →
    ∣_∣ (centre (x *ℝ y) n - centre (x' *ℝ y') n) < ε k
  step n n≥N = final
    where
    nn = 2 ℕ* n
    n≤nn : n ≤ℕ nn
    n≤nn = subst (λ z → n ≤ℕ z) (n+n≡2n n) (ℕP.m≤m+n n n)
    cx = centre x nn ; cy = centre y nn
    cx' = centre x' nn ; cy' = centre y' nn
    p1 = centre (x *ℝ y) n
    p2 = centre (x' *ℝ y') n
    Q = cx * cy
    Q' = cx' * cy'

    g1≤ : ∣_∣ (p1 - Q) ≤ C1 * recipPow2 n
    g1≤ = term1 x y n
    g2≤ : ∣_∣ (p2 - Q') ≤ C2 * recipPow2 n
    g2≤ = term1 x' y' n
    g1<′ : C1 * recipPow2 n < ε L
    g1<′ = g1< n (ℕP.≤-trans N≥Ng1 n≥N)
    g2<′ : C2 * recipPow2 n < ε L
    g2<′ = g2< n (ℕP.≤-trans N≥Ng2 n≥N)
    g1≤εL : ∣_∣ (p1 - Q) ≤ ε L
    g1≤εL = ≤-trans g1≤ (<⇒≤ g1<′)
    g2≤εL : ∣_∣ (p2 - Q') ≤ ε L
    g2≤εL = ≤-trans g2≤ (<⇒≤ g2<′)

    n≥Ny : n ≥ℕ Ny
    n≥Ny = ℕP.≤-trans N≥Ny n≥N
    nn≥Ny : nn ≥ℕ Ny
    nn≥Ny = ℕP.≤-trans n≥Ny n≤nn
    cy-close : ∣_∣ (cy - cy') < ε my
    cy-close = Ny-close nn nn≥Ny
    n≥Nx : n ≥ℕ Nx
    n≥Nx = ℕP.≤-trans N≥Nx n≥N
    nn≥Nx : nn ≥ℕ Nx
    nn≥Nx = ℕP.≤-trans n≥Nx n≤nn
    cx-close : ∣_∣ (cx - cx') < ε mx
    cx-close = Nx-close nn nn≥Nx

    t1 = ∣_∣ cx * ∣_∣ (cy - cy')
    t2 = ∣_∣ cy' * ∣_∣ (cx - cx')
    c1≤ : t1 ≤ (ε L) ÷ embed 6
    c1≤ = ≤-trans
      (*-mono-≤-nonNeg (0≤∣p∣ cx) (∣cx∣≤Mx nn)
                        (0≤∣p∣ (cy - cy')) (<⇒≤ cy-close))
      (≤-trans (≤-reflexive (*-comm Mx (ε my)))
        (≤-trans (*-monoˡ-≤-nonNeg (ε my) (≤+1 Mx))
                 my-bound))
    c2≤ : t2 ≤ (ε L) ÷ embed 6
    c2≤ = ≤-trans
      (*-mono-≤-nonNeg (0≤∣p∣ cy') (∣cyp∣≤Myp nn)
                       (0≤∣p∣ (cx - cx')) (<⇒≤ cx-close))
      (≤-trans (≤-reflexive (*-comm Myp (ε mx)))
        (≤-trans (*-monoˡ-≤-nonNeg (ε mx) (≤+1 Myp))
                 mx-bound))

    cross-≤ : ∣_∣ (Q - Q') ≤ t1 + t2
    cross-≤ = cross nn
    c12≤εL : t1 + t2 ≤ ε L
    c12≤εL = ≤-trans (+-mono-≤ c1≤ c2≤) (÷6+÷6≤ (ε L) (0<ε L))
    cross≤εL : ∣_∣ (Q - Q') ≤ ε L
    cross≤εL = ≤-trans cross-≤ c12≤εL

    tri3 : ∣ (p1 - p2) ∣ ≤
            ((∣ (p1 - Q) ∣) + (∣ (Q - Q') ∣)) + (∣ (p2 - Q') ∣)
    tri3 = tri3-lemma p1 Q Q' p2
    bound-total : ∣_∣ (p1 - p2) ≤ (ε L) + (ε L) + (ε L)
    bound-total = ≤-trans tri3
      (+-mono-≤ (+-mono-≤ g1≤εL cross≤εL) g2≤εL)

    final : ∣ (p1 - p2) ∣ < ε k
    final = mul-cong-final k p1 p2 Q Q' (ε L) εL<εk/4 bound-total
