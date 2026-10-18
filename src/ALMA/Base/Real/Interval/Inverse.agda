------------------------------------------------------------------------
-- Reciprocal of a non-zero interval real
--
-- The product of an interval real and its reciprocal is approximately
-- one, for positive interval reals; the non-zero case reduces to the
-- positive case via negation.
--
-- 非零区间实数的倒数
--
-- 正区间实数与其倒数之积近似等于 1；非零情形经取负化归到正情形。
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module ALMA.Base.Real.Interval.Inverse where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Integer using (+_) renaming (_*_ to _ℤ*_; _+_ to _ℤ+_)
open import Data.Integer.Properties using (+◃n≡+n)
open import Data.Nat using
  (ℕ; zero; suc; _⊔_; _^_; s≤s; z≤n; _≥_; _∸_)
  renaming (_≤_ to _≤ℕ_; _+_ to _+ℕ_; _*_ to _ℕ*_; _<_ to _<ℕ_)
open import Data.Nat.Coprimality using (1-coprimeTo) renaming (sym to coprime-sym)
open import Data.Nat.Properties using
  (m≤m⊔n; m≤n⊔m; ^-monoʳ-≤; *-suc; m≤m+n; m≤n+m; n≤1+n; +-suc; *-mono-≤
  ; ^-distribʳ-*; ^-distribˡ-+-*)
  renaming (≤-trans to ≤ℕ-trans; ≤-refl to ≤ℕ-refl; *-comm to *-commℕ
  ; *-assoc to *-assocℕ; *-identityʳ to *-identityʳℕ)
import Data.Nat.Properties as ℕP
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.Rational using
  (ℚ; 0ℚ; 1ℚ; _+_; _-_; _*_; _/_; _<_; _≤_; ∣_∣; NonZero; Positive
  ; NonNegative; positive; nonNegative)
open import Data.Rational.Base using (1/_) renaming (-_ to neg)
open import Data.Rational.Properties using
  (≤-refl; ≤-reflexive; ≤-trans; <⇒≤; ≤-<-trans; <-≤-trans; <-trans; <-irrefl
  ; +-mono-≤; *-comm; *-assoc; *-identityʳ; *-inverseʳ; *-monoˡ-≤-nonNeg
  ; *-monoʳ-≤-nonNeg; *-monoˡ-<-pos; pos*pos⇒pos; positive⁻¹; 1/pos⇒pos
  ; pos⇒nonZero; pos⇒nonNeg; 0≤∣p∣; ∣p*q∣≡∣p∣*∣q∣; 0≤p⇒∣p∣≡p
  ; *-distribʳ-+; neg-distribˡ-*; normalize-coprime; /-cong
  ; nonNeg*nonNeg⇒nonNeg; nonNeg+nonNeg⇒nonNeg; nonNegative⁻¹)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; cong; sym; trans; module ≡-Reasoning)
open ≡-Reasoning

open import ALMA.Base.Real using (CauchySeq; embed; embed-suc-pos)
open CauchySeq renaming (f to seq-f; μ to seq-μ)
open import ALMA.Base.Real.Interval using (RealI; δ-pos)
open import ALMA.Base.Real.Interval.Arith using (0ℝ; 1ℝ)
open import ALMA.Base.Real.Interval.Mul using (_*ℝ_)
open import ALMA.Base.Real.Interval.Equiv using (_≈ℝ_)
open import ALMA.Base.Real.IntervalEquiv using
  (l; u; centre; width; centre-diff; 0<width; bound-w; recipPow2; n<2^n
  ; embed-mono-<; suc∸1; realI→cauchy)
open import ALMA.Base.Real.Interval.Order using (_<ℝ_)
open import ALMA.Base.Real.Interval.Kit using
  (half; 0≤half; n≤2n; *-mono-≤-nonNeg; 0≤recipPow2; embed-mono-≤
  ; recipPow2-bound; recip-antitone; tri-diff)
open import ALMA.Base.Real.Interval.Node using
  (centre-1ℝ; recipPow2≤1; rr≤r; mul-nonNeg; 0≤width-n; width-rec)
open import ALMA.Base.Real.Interval.MulLaws using (centre-*ℝ≈)
open import ALMA.Base.Real.Interval.Recip using
  (recipℝ; recipCauchy; realI→posCauchy; PosCauchy; u-0ℝ; recip-modulus)
open import ALMA.Base.Real.CauchyToInterval using (M; K; centre-cauchy→realI)
open import ALMA.Base.Real.Interval.Reasoning using (begin≤_; _≈⟨_⟩_; _≤⟨_⟩_; _≤∎)

------------------------------------------------------------------------
-- Embedding homomorphisms
--
-- Denominators are both 1; the unnormalised fractions of the sum and
-- product are (m+n)/1 and (m*n)/1, normalised back to mkℚ (i.e. embed)
-- via 1-coprimeTo and normalize-coprime. Numerator arithmetic:
-- (+m)·1 + (+n)·1 ≡ +(m+n).
--
-- 嵌入同态
--
-- 分母均为 1；两数之和/积的未规范化分数为 (m+n)/1、(m*n)/1，
-- 由 1-coprimeTo 与 normalize-coprime 收回到 mkℚ（即 embed）。
-- 分子算术：(+m)·1 + (+n)·1 ≡ +(m+n)。

num-add : ∀ m n → (+ m ℤ* + 1 ℤ+ + n ℤ* + 1) ≡ + (m +ℕ n)
num-add m n = begin
  (+ m ℤ* + 1 ℤ+ + n ℤ* + 1)
    ≡⟨ cong (λ z → z ℤ+ (+ n ℤ* + 1)) (Data.Integer.Properties.*-identityʳ (+ m)) ⟩
  (+ m ℤ+ + n ℤ* + 1)
    ≡⟨ cong (λ z → (+ m) ℤ+ z) (Data.Integer.Properties.*-identityʳ (+ n)) ⟩
  (+ m ℤ+ + n)
    ≡⟨⟩
  + (m +ℕ n)
  ∎

embed-+-hom : ∀ m n → embed (m +ℕ n) ≡ embed m + embed n
embed-+-hom m n = begin
  embed (m +ℕ n)
    ≡⟨ sym (normalize-coprime (coprime-sym (1-coprimeTo (m +ℕ n)))) ⟩
  (+ (m +ℕ n) / 1)
    ≡⟨ sym (/-cong (num-add m n) refl) ⟩
  ((+ m ℤ* + 1 ℤ+ + n ℤ* + 1) / (1 ℕ* 1))
    ≡⟨⟩
  embed m + embed n
  ∎

-- Numerator arithmetic: (+m)·(+n) ≡ +(m*n).
--
-- 分子算术：(+m)·(+n) ≡ +(m*n)。
num-mul : ∀ m n → (+ m ℤ* + n) ≡ + (m ℕ* n)
num-mul m n = +◃n≡+n (m ℕ* n)

embed-*-hom : ∀ m n → embed (m ℕ* n) ≡ embed m * embed n
embed-*-hom m n = begin
  embed (m ℕ* n)
    ≡⟨ sym (normalize-coprime (coprime-sym (1-coprimeTo (m ℕ* n)))) ⟩
  (+ (m ℕ* n) / 1)
    ≡⟨ sym (/-cong (num-mul m n) refl) ⟩
  ((+ m ℤ* + n) / (1 ℕ* 1))
    ≡⟨⟩
  embed m * embed n
  ∎

------------------------------------------------------------------------
-- Modulus comparison
--
-- The combined modulus M dominates the reciprocal modulus at K n,
-- and K dominates the identity.
--
-- 模数比较
--
-- 合并模数 M 支配 K n 处的倒数模数，K 支配恒等。

M≥μK : (x : CauchySeq) (n : ℕ) → M x n ≥ seq-μ x (K n)
M≥μK x zero    = ≤ℕ-refl
M≥μK x (suc n) = m≤n⊔m (M x n) (seq-μ x (K (suc n)))

K≥k : (k : ℕ) → K k ≥ k
K≥k k = ≤ℕ-trans (ℕP.<⇒≤ (n<2^n k)) (^-monoʳ-≤ 2 (m≤n+m k 2))

------------------------------------------------------------------------
-- Auxiliary lemmas
--
-- 辅助引理

private
  0≤embed' : (n : ℕ) → 0ℚ ≤ embed n
  0≤embed' zero    = ≤-refl
  0≤embed' (suc n) =
    <⇒≤ (positive⁻¹ (embed (suc n)) {{embed-suc-pos}})

  2^n*2^n≡4^n : ∀ n → 2 ^ n ℕ* 2 ^ n ≡ 4 ^ n
  2^n*2^n≡4^n n = sym (^-distribʳ-* n 2 2)

  4n²≤4^n : ∀ n → n ≥ 4 → 4 ℕ* (n ℕ* n) ≤ℕ 4 ^ n
  4n²≤4^n n n≥4 = goal
    where
    0<n : 0 <ℕ n
    0<n = ℕP.<-≤-trans (s≤s (z≤n {3})) n≥4
    m = n ∸ 1
    sm≡n : suc m ≡ n
    sm≡n = suc∸1 0<n
    n≡sucm : n ≡ suc m
    n≡sucm = sym sm≡n
    n≤2^m : n ≤ℕ 2 ^ m
    n≤2^m = ≤ℕ-trans (ℕP.≤-reflexive n≡sucm) (n<2^n m)
    n²≤4^m : n ℕ* n ≤ℕ 4 ^ m
    n²≤4^m = ≤ℕ-trans (*-mono-≤ n≤2^m n≤2^m)
                        (ℕP.≤-reflexive (2^n*2^n≡4^n m))
    4n²≤4^m : 4 ℕ* (n ℕ* n) ≤ℕ 4 ℕ* (4 ^ m)
    4n²≤4^m = *-mono-≤ (≤ℕ-refl {4}) n²≤4^m
    goal : 4 ℕ* (n ℕ* n) ≤ℕ 4 ^ n
    goal = ≤ℕ-trans 4n²≤4^m
                      (ℕP.≤-reflexive (cong (4 ^_) (sym n≡sucm)))

  4^n≤K-2n : ∀ n → 4 ^ n ≤ℕ K (2 ℕ* n)
  4^n≤K-2n n = ≤ℕ-trans (≤ℕ-trans p1 p2) (≤ℕ-trans p3 p4)
    where
    p1 : 4 ^ n ≤ℕ 2 ^ n ℕ* 2 ^ n
    p1 = ℕP.≤-reflexive (sym (2^n*2^n≡4^n n))
    p2 : 2 ^ n ℕ* 2 ^ n ≤ℕ 2 ^ (n +ℕ n)
    p2 = ℕP.≤-reflexive (sym (^-distribˡ-+-* 2 n n))
    m = 2 ^ (n +ℕ n)
    p3 : m ≤ℕ m ℕ* 4
    p3 = ≤ℕ-trans (m≤m+n m (m ℕ* 3))
                    (ℕP.≤-reflexive (sym (*-suc m 3)))
    2n≡n+n : 2 ℕ* n ≡ n +ℕ n
    2n≡n+n = trans (*-commℕ 2 n)
               (trans (*-suc n 1) (cong (n +ℕ_) (*-identityʳℕ n)))
    +2≡suc² : ∀ m → m +ℕ 2 ≡ suc (suc m)
    +2≡suc² m = begin
      m +ℕ 2
        ≡⟨ +-suc m 1 ⟩
      suc (m +ℕ 1)
        ≡⟨ cong suc (+-suc m 0) ⟩
      suc (suc (m +ℕ 0))
        ≡⟨ cong (λ k → suc (suc k)) (ℕP.+-identityʳ m) ⟩
      suc (suc m)
      ∎
    exp-eq : (n +ℕ n) +ℕ 2 ≡ suc (suc (2 ℕ* n))
    exp-eq = trans (+2≡suc² (n +ℕ n))
              (cong (λ k → suc (suc k)) (sym 2n≡n+n))
    p4 : m ℕ* 4 ≤ℕ K (2 ℕ* n)
    p4 = ℕP.≤-reflexive
      (begin
        m ℕ* 4
          ≡⟨ sym (^-distribˡ-+-* 2 (n +ℕ n) 2) ⟩
        2 ^ ((n +ℕ n) +ℕ 2)
          ≡⟨ cong (2 ^_) exp-eq ⟩
        K (2 ℕ* n)
        ∎)

------------------------------------------------------------------------
-- Ordering lemma
--
-- n ≤ m follows from ¬(suc m ≤ n).
--
-- 序关系引理
--
-- 由 ¬(suc m ≤ n) 推出 n ≤ m。

from-not : ∀ m n → ¬_ (suc m ≤ℕ n) → n ≤ℕ m
from-not m n f = ℕP.≤-pred (ℕP.≰⇒> f)

------------------------------------------------------------------------
-- Strict lower bound for recip-modulus
--
-- embed (suc k) < b² · embed (suc (recip-modulus b 0<b k)).
--
-- recip-modulus 的严格下界
--
-- embed (suc k) < b² · embed (suc (recip-modulus b 0<b k))。

recip-modulus-lower :
    (b : ℚ) (0<b : 0ℚ < b) (k : ℕ) →
    embed (suc k) < b * b * embed (suc (recip-modulus b 0<b k))
recip-modulus-lower b 0<b k = goal
  where
    bsq = b * b
    bsq-pos : Positive bsq
    bsq-pos = pos*pos⇒pos b {{positive 0<b}} b {{positive 0<b}}
    bsq-nz : NonZero bsq
    bsq-nz = pos⇒nonZero bsq {{bsq-pos}}
    bsq-nn : NonNegative bsq
    bsq-nn = pos⇒nonNeg bsq {{bsq-pos}}
    inv-bsq = (1/ bsq) {{bsq-nz}}
    e-sk = embed (suc k)
    e-sk-pos : Positive e-sk
    e-sk-pos = embed-suc-pos
    w = e-sk * inv-bsq
    inv-bsq-pos : Positive inv-bsq
    inv-bsq-pos = 1/pos⇒pos bsq {{bsq-pos}}
    w-pos : Positive w
    w-pos = pos*pos⇒pos e-sk {{e-sk-pos}} inv-bsq {{inv-bsq-pos}}
    Mm = recip-modulus b 0<b k
    w≤eM : w ≤ embed Mm
    w≤eM = proj₂ (bound-w w (<⇒≤ (positive⁻¹ w {{w-pos}})))
    w*bsq-eq : w * bsq ≡ e-sk
    w*bsq-eq = begin
      w * bsq
        ≡⟨ *-assoc e-sk inv-bsq bsq ⟩
      e-sk * (inv-bsq * bsq)
        ≡⟨ cong (e-sk *_) (*-comm inv-bsq bsq) ⟩
      e-sk * (bsq * inv-bsq)
        ≡⟨ cong (e-sk *_) (*-inverseʳ bsq {{bsq-nz}}) ⟩
      e-sk * 1ℚ
        ≡⟨ *-identityʳ e-sk ⟩
      e-sk
      ∎
    key1 : e-sk ≤ embed Mm * bsq
    key1 = begin≤
      e-sk
        ≈⟨ sym w*bsq-eq ⟩
      w * bsq
        ≤⟨ *-monoʳ-≤-nonNeg bsq {{bsq-nn}} w≤eM ⟩
      embed Mm * bsq
      ≤∎
    M<sM : embed Mm < embed (suc Mm)
    M<sM = embed-mono-< (s≤s (≤ℕ-refl {Mm}))
    key2 : embed Mm * bsq < embed (suc Mm) * bsq
    key2 = *-monoˡ-<-pos bsq {{bsq-pos}} M<sM
    goal : e-sk < bsq * embed (suc Mm)
    goal = <-≤-trans
      (≤-<-trans key1 key2)
      (≤-reflexive (*-comm (embed (suc Mm)) bsq))

-- If embed 2 * b * b ≤ embed N, then it holds for all n ≥ N.
--
-- 若 embed 2 * b * b ≤ embed N，则对所有 n ≥ N 也成立。
embed-n≥2b² :
    (b : ℚ) (N : ℕ) →
    embed 2 * b * b ≤ embed N →
    ∀ n → n ≥ N → embed 2 * b * b ≤ embed n
embed-n≥2b² b N base n n≥N =
  ≤-trans base (embed-mono-≤ n≥N)

-- Under 2*b² ≤ embed N and N ≥ 4, for n ≥ N we have
--   embed (2n) * b * b ≤ embed (4^n).
--
-- 在 2*b² ≤ embed N、N ≥ 4 的条件下，对 n ≥ N 有
--   embed (2n) * b * b ≤ embed (4^n)。
2n*b²≤4^n :
    (b : ℚ) (0<b : 0ℚ < b) (N : ℕ) →
    N ≥ 4 →
    (∀ n → n ≥ N → embed 2 * b * b ≤ embed n) →
    ∀ n → n ≥ N → embed (2 ℕ* n) * b * b ≤ embed (4 ^ n)
2n*b²≤4^n b 0<b N N≥4 hb n n≥N = goal
  where
    b-pos : Positive b
    b-pos = positive 0<b
    bsq = b * b
    bsq-pos : Positive bsq
    bsq-pos = pos*pos⇒pos b {{b-pos}} b {{b-pos}}
    bsq-nn = pos⇒nonNeg bsq {{bsq-pos}}
    e2n = embed (2 ℕ* n)
    e2n-nn = nonNegative (0≤embed' (2 ℕ* n))
    assoc : (embed 2 * b) * b ≡ embed 2 * bsq
    assoc = *-assoc (embed 2) b b
    2b²≤e2n : embed 2 * bsq ≤ e2n
    2b²≤e2n = begin≤
      embed 2 * bsq
        ≈⟨ sym assoc ⟩
      (embed 2 * b) * b
        ≤⟨ hb (2 ℕ* n) (≤ℕ-trans n≥N (n≤2n n)) ⟩
      e2n
      ≤∎
    1≤2 : 1ℚ ≤ embed 2
    1≤2 = embed-mono-≤ (s≤s z≤n)
    mono : bsq * 1ℚ ≤ bsq * embed 2
    mono = *-monoˡ-≤-nonNeg bsq {{bsq-nn}} 1≤2
    bsq≤2b² : bsq ≤ embed 2 * bsq
    bsq≤2b² = begin≤
      bsq
        ≈⟨ sym (*-identityʳ bsq) ⟩
      bsq * 1ℚ
        ≤⟨ mono ⟩
      bsq * embed 2
        ≈⟨ *-comm bsq (embed 2) ⟩
      embed 2 * bsq
      ≤∎
    bsq≤e2n : bsq ≤ e2n
    bsq≤e2n = ≤-trans bsq≤2b² 2b²≤e2n
    step1 : e2n * bsq ≤ e2n * e2n
    step1 = *-monoˡ-≤-nonNeg e2n {{e2n-nn}} bsq≤e2n
    prod-eq : e2n * e2n ≡ embed ((2 ℕ* n) ℕ* (2 ℕ* n))
    prod-eq = sym (embed-*-hom (2 ℕ* n) (2 ℕ* n))
    step2 : e2n * bsq ≤ embed ((2 ℕ* n) ℕ* (2 ℕ* n))
    step2 = ≤-trans step1 (≤-reflexive prod-eq)
    4n²≡ : (2 ℕ* n) ℕ* (2 ℕ* n) ≡ 4 ℕ* (n ℕ* n)
    4n²≡ = begin
      (2 ℕ* n) ℕ* (2 ℕ* n)
        ≡⟨ *-assocℕ 2 n (2 ℕ* n) ⟩
      2 ℕ* (n ℕ* (2 ℕ* n))
        ≡⟨ cong (2 ℕ*_) (*-commℕ n (2 ℕ* n)) ⟩
      2 ℕ* ((2 ℕ* n) ℕ* n)
        ≡⟨ cong (2 ℕ*_) (*-assocℕ 2 n n) ⟩
      2 ℕ* (2 ℕ* (n ℕ* n))
        ≡⟨ sym (*-assocℕ 2 2 (n ℕ* n)) ⟩
      (2 ℕ* 2) ℕ* (n ℕ* n)
        ≡⟨ cong (λ k → k ℕ* (n ℕ* n)) (*-suc 2 1) ⟩
      4 ℕ* (n ℕ* n)
        ∎
    step3 : e2n * bsq ≤ embed (4 ℕ* (n ℕ* n))
    step3 = ≤-trans step2 (≤-reflexive (cong embed 4n²≡))
    goal' : e2n * bsq ≤ embed (4 ^ n)
    goal' = ≤-trans step3
      (embed-mono-≤ (4n²≤4^n n (≤ℕ-trans N≥4 n≥N)))
    assocg : (e2n * b) * b ≡ e2n * bsq
    assocg = *-assoc e2n b b
    goal : e2n * b * b ≤ embed (4 ^ n)
    goal = begin≤
      e2n * b * b
        ≈⟨ assocg ⟩
      e2n * bsq
        ≤⟨ goal' ⟩
      embed (4 ^ n)
      ≤∎

-- recip-modulus at K(2n) is at least 2n.
--
-- recip-modulus 在 K(2n) 处的值不小于 2n。
recip-modulus-≥2n :
    (b : ℚ) (0<b : 0ℚ < b) (N : ℕ) →
    (∀ n → n ≥ N → embed (2 ℕ* n) * b * b ≤ embed (4 ^ n)) →
    ∀ n → n ≥ N → recip-modulus b 0<b (K (2 ℕ* n)) ≥ 2 ℕ* n
recip-modulus-≥2n b 0<b N h n n≥N = helper
  where
    b-pos : Positive b
    b-pos = positive 0<b
    bsq = b * b
    bsq-pos : Positive bsq
    bsq-pos = pos*pos⇒pos b {{b-pos}} b {{b-pos}}
    bsq-nn : NonNegative bsq
    bsq-nn = pos⇒nonNeg bsq {{bsq-pos}}
    k = K (2 ℕ* n)
    Nm = recip-modulus b 0<b k
    lb = recip-modulus-lower b 0<b k
    4n<sK : 4 ^ n <ℕ suc k
    4n<sK = ℕP.≤-<-trans (4^n≤K-2n n) (s≤s (≤ℕ-refl {k}))
    e4n<esK : embed (4 ^ n) < embed (suc k)
    e4n<esK = embed-mono-< 4n<sK
    chain :
      suc Nm ≤ℕ 2 ℕ* n → bsq * embed (suc Nm) ≤ embed (4 ^ n)
    chain h' = begin≤
      bsq * embed (suc Nm)
        ≤⟨ *-monoˡ-≤-nonNeg bsq {{bsq-nn}} (embed-mono-≤ h') ⟩
      bsq * embed (2 ℕ* n)
        ≈⟨ *-comm bsq (embed (2 ℕ* n)) ⟩
      embed (2 ℕ* n) * bsq
        ≈⟨ sym (*-assoc (embed (2 ℕ* n)) b b) ⟩
      (embed (2 ℕ* n) * b) * b
        ≤⟨ h n n≥N ⟩
      embed (4 ^ n)
      ≤∎
    absurd : suc Nm ≤ℕ 2 ℕ* n → ⊥
    absurd h' =
      <-irrefl refl
        (<-trans e4n<esK (<-≤-trans lb (chain h')))
    helper : 2 ℕ* n ≤ℕ Nm
    helper = from-not Nm (2 ℕ* n) absurd

-- Closed-form bound on the centre error of multiplication:
--   |centre (x *ℝ R) n - centre x (2n) * centre R (2n)|
--     ≤ (width x 0 * width R 0 * half) * recipPow2 n.
--
-- 乘法中心误差的闭式界：
--   |centre (x *ℝ R) n - centre x (2n) * centre R (2n)|
--     ≤ (width x 0 * width R 0 * half) * recipPow2 n。
term1 :
    (x R : RealI) (n : ℕ) →
    ∣ centre (x *ℝ R) n - centre x (2 ℕ* n) * centre R (2 ℕ* n) ∣
      ≤ (width x 0 * width R 0 * half) * recipPow2 n
term1 x R n = ≤-trans (centre-*ℝ≈ x R n) step
  where
    w0 = width x 0
    wR0 = width R 0
    wx : width x (2 ℕ* n) ≤ w0 * recipPow2 n
    wx = width-rec x n
    wR : width R (2 ℕ* n) ≤ wR0 * recipPow2 n
    wR = width-rec R n
    prod : width x (2 ℕ* n) * width R (2 ℕ* n)
         ≤ w0 * wR0 * recipPow2 n
    prod = ≤-trans (*-mono-≤-nonNeg
                     (0≤width-n x (2 ℕ* n)) wx
                     (0≤width-n R (2 ℕ* n)) wR)
      (≤-trans (≤-reflexive raw-eq)
               (sq≤ (recipPow2 n) (0≤recipPow2 n) (recipPow2≤1 n)))
      where
      raw-eq : (w0 * recipPow2 n) * (wR0 * recipPow2 n)
            ≡ w0 * wR0 * (recipPow2 n * recipPow2 n)
      raw-eq = begin
        (w0 * r) * (wR0 * r)
          ≡⟨ sym (*-assoc (w0 * r) wR0 r) ⟩
        ((w0 * r) * wR0) * r
          ≡⟨ cong (_* r) (*-comm (w0 * r) wR0) ⟩
        (wR0 * (w0 * r)) * r
          ≡⟨ cong (_* r) (sym (*-assoc wR0 w0 r)) ⟩
        ((wR0 * w0) * r) * r
          ≡⟨ *-assoc (wR0 * w0) r r ⟩
        (wR0 * w0) * (r * r)
          ≡⟨ cong (λ z → z * (r * r)) (*-comm wR0 w0) ⟩
        (w0 * wR0) * (r * r)
          ∎
        where r = recipPow2 n
      sq≤ : ∀ r → 0ℚ ≤ r → r ≤ 1ℚ
          → w0 * wR0 * (r * r) ≤ w0 * wR0 * r
      sq≤ r 0≤r r≤1 =
        *-monoˡ-≤-nonNeg (w0 * wR0)
          {{nonNegative (mul-nonNeg (0≤width-n x 0)
                                    (0≤width-n R 0))}}
          (rr≤r 0≤r r≤1)
    step : (width x (2 ℕ* n) * width R (2 ℕ* n)) * half
         ≤ (w0 * wR0 * half) * recipPow2 n
    step = ≤-trans (*-monoʳ-≤-nonNeg half {{nonNegative 0≤half}} prod)
      (≤-reflexive final-eq)
      where
      final-eq : (w0 * wR0 * recipPow2 n) * half
              ≡ (w0 * wR0 * half) * recipPow2 n
      final-eq = begin
        (w0 * wR0 * recipPow2 n) * half
          ≡⟨ *-assoc (w0 * wR0) (recipPow2 n) half ⟩
        w0 * wR0 * (recipPow2 n * half)
          ≡⟨ cong (w0 * wR0 *_) (*-comm (recipPow2 n) half) ⟩
        w0 * wR0 * (half * recipPow2 n)
          ≡⟨ sym (*-assoc (w0 * wR0) half (recipPow2 n)) ⟩
        (w0 * wR0 * half) * recipPow2 n
          ∎

------------------------------------------------------------------------
-- Carried modulus lower bound
--
-- The modulus of realI→cauchy is μ k = suc (M * suc k). The initial
-- width w0 is strictly positive, so bound-w yields M ≥ 1, hence
-- μ k ≥ k.
--
-- 携带模数下界
--
-- realI→cauchy 的模数 μ k = suc (M * suc k)。初始宽度 w0 严格为正，
-- 故 bound-w 所得 M ≥ 1，从而 μ k ≥ k。

embed-pos→≥1 : ∀ m → 0ℚ < embed m → 1 ≤ℕ m
embed-pos→≥1 zero   pr = ⊥-elim (<-irrefl refl pr)
embed-pos→≥1 (suc m) _ = s≤s z≤n

μx-dom : (r : RealI) (k : ℕ) → seq-μ (realI→cauchy r) k ≥ k
μx-dom r zero = z≤n
μx-dom r (suc k) = s≤s (≤ℕ-trans mid monoA)
  where
  w0 = width r 0
  0≤w0 = <⇒≤ (0<width r)
  Mx = proj₁ (bound-w w0 0≤w0)
  w0≤Mx = proj₂ (bound-w w0 0≤w0)
  0<eMx = <-≤-trans (0<width r) w0≤Mx
  Mx≥1 : 1 ≤ℕ Mx
  Mx≥1 = embed-pos→≥1 Mx 0<eMx
  -- k ≤ 2+k ≤ suc(suc k) ≤ Mx · suc(suc k)
  mid : k ≤ℕ suc (suc k)
  mid = ≤ℕ-trans (n≤1+n k) (s≤s (n≤1+n k))
  monoA : suc (suc k) ≤ℕ Mx ℕ* suc (suc k)
  monoA =
    ≤ℕ-trans (ℕP.≤-reflexive (sym (ℕP.*-identityˡ (suc (suc k)))))
             (*-mono-≤ Mx≥1 (≤ℕ-refl {suc (suc k)}))

------------------------------------------------------------------------
-- Tail convergence engine
--
-- The geometric bound |centre difference| ≤ C · recipPow2 n is only
-- required eventually, for n ≥ N₀. The finite prefix does not affect
-- equivalence (same as ≈ℝ-of-rec, only relaxed to the tail).
--
-- 尾部收敛引擎
--
-- |中心差| ≤ C · recipPow2 n 仅需对 n ≥ N₀ 成立。有限前段不影响
-- 等价性（与 ≈ℝ-of-rec 相同，仅放宽为尾部）。

≈ℝ-of-recN : (x y : RealI) (N₀ : ℕ) (C : ℚ) → 0ℚ ≤ C →
  (∀ n → n ≥ N₀ → ∣ centre x n - centre y n ∣ ≤ C * recipPow2 n) →
  x ≈ℝ y
≈ℝ-of-recN x y N₀ C 0≤C h k =
  let N₁ , w = recipPow2-bound C 0≤C k
      N = N₀ ⊔ N₁
  in N , λ n n≥N →
       let n≥N₀ = ≤ℕ-trans (m≤m⊔n N₀ N₁) n≥N
           n≥N₁ = ≤ℕ-trans (m≤n⊔m N₀ N₁) n≥N
       in ≤-<-trans (h n n≥N₀) (w n n≥N₁)

------------------------------------------------------------------------
-- Setup for reciprocal theorems
--
-- 倒数定理的参数设置

module ReciprocalSetup (x : RealI) (0<x : 0ℝ <ℝ x) where

  R : RealI
  R = recipℝ x 0<x

  pc : PosCauchy
  pc = realI→posCauchy x 0<x

  cs : CauchySeq
  cs = recipCauchy pc

  n₀ : ℕ
  n₀ = proj₁ 0<x

  b : ℚ
  b = l x n₀

  δn<lxn : u 0ℝ n₀ < b
  δn<lxn = proj₂ 0<x

  0<b : 0ℚ < b
  0<b = <-trans (δ-pos n₀)
          (≤-<-trans (≤-reflexive (sym (u-0ℝ n₀))) δn<lxn)

  b-pos : Positive b
  b-pos = positive 0<b

  b-nz : NonZero b
  b-nz = pos⇒nonZero b {{b-pos}}

  w0 : ℚ
  w0 = width x 0

  wR0 : ℚ
  wR0 = width R 0

  0≤w0 : 0ℚ ≤ w0
  0≤w0 = 0≤width-n x 0

  0≤wR0 : 0ℚ ≤ wR0
  0≤wR0 = 0≤width-n R 0

  w0-nn : NonNegative w0
  w0-nn = nonNegative 0≤w0

  wR0-nn : NonNegative wR0
  wR0-nn = nonNegative 0≤wR0

  half-nn : NonNegative half
  half-nn = nonNegative 0≤half

  invb : ℚ
  invb = (1/ b) {{b-nz}}

  invb-pos : Positive invb
  invb-pos = 1/pos⇒pos b {{b-pos}}

  invb-nn : NonNegative invb
  invb-nn = pos⇒nonNeg invb {{invb-pos}}

  w0*wR0-nn : NonNegative (w0 * wR0)
  w0*wR0-nn = nonNeg*nonNeg⇒nonNeg w0 {{w0-nn}} wR0 {{wR0-nn}}

  t1-nn : NonNegative (w0 * wR0 * half)
  t1-nn = nonNeg*nonNeg⇒nonNeg (w0 * wR0) {{w0*wR0-nn}} half {{half-nn}}

  t2-nn : NonNegative (w0 * invb)
  t2-nn = nonNeg*nonNeg⇒nonNeg w0 {{w0-nn}} invb {{invb-nn}}

  C : ℚ
  C = w0 * wR0 * half + w0 * invb

  0≤C : 0ℚ ≤ C
  0≤C = nonNegative⁻¹ C
    {{nonNeg+nonNeg⇒nonNeg (w0 * wR0 * half) {{t1-nn}}
                           (w0 * invb) {{t2-nn}}}}

  e2-pos : Positive (embed 2)
  e2-pos = embed-suc-pos

  e2-nn : NonNegative (embed 2)
  e2-nn = pos⇒nonNeg (embed 2) {{e2-pos}}

  b-nn : NonNegative b
  b-nn = pos⇒nonNeg b {{b-pos}}

  e2*b-nn : NonNegative (embed 2 * b)
  e2*b-nn = nonNeg*nonNeg⇒nonNeg (embed 2) {{e2-nn}} b {{b-nn}}

  C-aux : ℚ
  C-aux = embed 2 * b * b

  0≤C-aux : 0ℚ ≤ C-aux
  0≤C-aux = nonNegative⁻¹ C-aux
    {{nonNeg*nonNeg⇒nonNeg (embed 2 * b) {{e2*b-nn}} b {{b-nn}}}}

  N-b : ℕ
  N-b = proj₁ (bound-w C-aux 0≤C-aux)

  C-aux≤N-b : C-aux ≤ embed N-b
  C-aux≤N-b = proj₂ (bound-w C-aux 0≤C-aux)

  N : ℕ
  N = 4 ⊔ N-b

  N≥4 : N ≥ 4
  N≥4 = m≤m⊔n 4 N-b

  N≥N-b : N ≥ N-b
  N≥N-b = m≤n⊔m 4 N-b

  embed-2b²≤N : embed 2 * b * b ≤ embed N
  embed-2b²≤N =
    ≤-trans C-aux≤N-b
      (embed-mono-≤ (≤ℕ-trans N≥N-b (≤ℕ-refl {N})))

  embed-n≥2b²-inst : ∀ n → n ≥ N → embed 2 * b * b ≤ embed n
  embed-n≥2b²-inst = embed-n≥2b² b N embed-2b²≤N

  2n-inst : ∀ n → n ≥ N → embed (2 ℕ* n) * b * b ≤ embed (4 ^ n)
  2n-inst = 2n*b²≤4^n b 0<b N N≥4 embed-n≥2b²-inst

  recip-modulus-≥2n-inst :
    ∀ n → n ≥ N → recip-modulus b 0<b (K (2 ℕ* n)) ≥ 2 ℕ* n
  recip-modulus-≥2n-inst = recip-modulus-≥2n b 0<b N 2n-inst

  term1-inst :
    ∀ n →
    ∣ centre (x *ℝ R) n - centre x (2 ℕ* n) * centre R (2 ℕ* n) ∣
      ≤ (w0 * wR0 * half) * recipPow2 n
  term1-inst n = term1 x R n

  -- j n = N₀ + M cs (2n).
  --
  -- M cs (2n) is at least the modulus of cs at K(2n) (prefix max),
  -- and the modulus of cs is μ-h (K(2n)) = seq-μ (realI→cauchy x) r,
  -- where r = recip-modulus b 0<b (K(2n)). The carried modulus is
  -- dominated by its index (μx-dom), so seq-μ ... r ≥ r; and
  -- recip-modulus-≥2n gives r ≥ 2n. Hence M cs (2n) ≥ 2n, and
  -- adding N₀ yields j n ≥ 2n.
  --
  -- j n = N₀ + M cs (2n)。
  --
  -- M cs (2n) 不小于 cs 在 K(2n) 处的模数（前缀最大），而 cs 的模数
  -- 为 μ-h (K(2n)) = seq-μ (realI→cauchy x) r，其中
  -- r = recip-modulus b 0<b (K(2n))。携带模数被其下标控制
  -- （μx-dom），故 seq-μ ... r ≥ r；又由 recip-modulus-≥2n 有
  -- r ≥ 2n。于是 M cs (2n) ≥ 2n，加上 N₀ 即得 j n ≥ 2n。
  j : ℕ → ℕ
  j n = PosCauchy.N₀ pc +ℕ M cs (2 ℕ* n)

  Mcs≥2n : ∀ n → n ≥ N → M cs (2 ℕ* n) ≥ 2 ℕ* n
  Mcs≥2n n n≥N =
    ≤ℕ-trans (≤ℕ-trans (recip-modulus-≥2n-inst n n≥N)
                       (μx-dom x r))
             (M≥μK cs (2 ℕ* n))
    where
      r = recip-modulus b 0<b (K (2 ℕ* n))

  j≥2n : ∀ n → n ≥ N → j n ≥ 2 ℕ* n
  j≥2n n n≥N =
    ≤ℕ-trans (Mcs≥2n n n≥N)
             (m≤n+m (M cs (2 ℕ* n)) (PosCauchy.N₀ pc))

  jn≥N₀ : ∀ n → PosCauchy.N₀ pc ≤ℕ j n
  jn≥N₀ n = m≤m+n (PosCauchy.N₀ pc) (M cs (2 ℕ* n))

  -- The centre of R at level 2n is the reciprocal of the centre of
  -- x at level j n.
  --
  -- R 第 2n 层的中心是 x 在 j n 处中心的倒数。
  centre-R-close : ∀ n → n ≥ N →
    ∣ centre R (2 ℕ* n) * centre x (2 ℕ* n) - 1ℚ ∣
      ≤ (1/ b) {{b-nz}} * width x (2 ℕ* n)
  centre-R-close n n≥N = begin≤
    ∣ centre R (2 ℕ* n) * c - 1ℚ ∣
      ≈⟨ abs-target ⟩
    ∣ c * invd - 1ℚ ∣
      ≈⟨ abs-lemma ⟩
    ∣ c - d ∣ * invd
      ≤⟨ step1 ⟩
    width x (2 ℕ* n) * invd
      ≤⟨ step2 ⟩
    width x (2 ℕ* n) * invb
      ≈⟨ *-comm (width x (2 ℕ* n)) invb ⟩
    invb * width x (2 ℕ* n)
    ≤∎
    where
      c = centre x (2 ℕ* n)
      d = centre x (j n)

      b≤d : b ≤ d
      b≤d = PosCauchy.lower pc (j n) (jn≥N₀ n)

      0<d : 0ℚ < d
      0<d = <-≤-trans 0<b b≤d

      d-pos : Positive d
      d-pos = positive 0<d

      d-nz : NonZero d
      d-nz = pos⇒nonZero d {{d-pos}}

      invd = (1/ d) {{d-nz}}

      invd-pos : Positive invd
      invd-pos = 1/pos⇒pos d {{d-pos}}

      0≤invd : 0ℚ ≤ invd
      0≤invd = <⇒≤ (positive⁻¹ invd {{invd-pos}})

      centreR≡ : centre R (2 ℕ* n) ≡ invd
      centreR≡ =
        begin
          centre R (2 ℕ* n)
            ≡⟨ centre-cauchy→realI cs (2 ℕ* n) ⟩
          seq-f cs (M cs (2 ℕ* n))
            ≡⟨⟩
          invd
        ∎

      diff≤width : ∣ c - d ∣ ≤ width x (2 ℕ* n)
      diff≤width =
        centre-diff x (2 ℕ* n) (2 ℕ* n) (j n)
                     (≤ℕ-refl {2 ℕ* n}) (j≥2n n n≥N)

      invd≤invb : invd ≤ invb
      invd≤invb = recip-antitone 0<b b≤d

      prod-minus1 : c * invd - 1ℚ ≡ (c - d) * invd
      prod-minus1 =
        begin
          c * invd - 1ℚ
            ≡⟨ cong (λ z → c * invd - z)
                   (sym (*-inverseʳ d {{d-nz}})) ⟩
          c * invd - d * invd
            ≡⟨ cong (λ z → c * invd + z) (neg-distribˡ-* d invd) ⟩
          c * invd + neg d * invd
            ≡⟨ sym (*-distribʳ-+ invd c (neg d)) ⟩
          (c + neg d) * invd
            ≡⟨⟩
          (c - d) * invd
        ∎

      abs-lemma : ∣ c * invd - 1ℚ ∣ ≡ ∣ c - d ∣ * invd
      abs-lemma =
        begin
          ∣ c * invd - 1ℚ ∣
            ≡⟨ cong ∣_∣ prod-minus1 ⟩
          ∣ (c - d) * invd ∣
            ≡⟨ ∣p*q∣≡∣p∣*∣q∣ (c - d) invd ⟩
          ∣ c - d ∣ * ∣ invd ∣
            ≡⟨ cong (∣ c - d ∣ *_) (0≤p⇒∣p∣≡p 0≤invd) ⟩
          ∣ c - d ∣ * invd
        ∎

      abs-target : ∣ centre R (2 ℕ* n) * c - 1ℚ ∣
                 ≡ ∣ c * invd - 1ℚ ∣
      abs-target =
        begin
          ∣ centre R (2 ℕ* n) * c - 1ℚ ∣
            ≡⟨ cong (λ z → ∣ z * c - 1ℚ ∣) centreR≡ ⟩
          ∣ invd * c - 1ℚ ∣
            ≡⟨ cong (λ z → ∣ z - 1ℚ ∣) (*-comm invd c) ⟩
          ∣ c * invd - 1ℚ ∣
        ∎

      step1 : ∣ c - d ∣ * invd ≤ width x (2 ℕ* n) * invd
      step1 =
        *-mono-≤-nonNeg (0≤∣p∣ (c - d)) diff≤width
                        0≤invd (≤-refl {invd})

      step2 : width x (2 ℕ* n) * invd
            ≤ width x (2 ℕ* n) * invb
      step2 =
        *-monoˡ-≤-nonNeg (width x (2 ℕ* n))
          {{nonNegative (0≤width-n x (2 ℕ* n))}} invd≤invb

  -- Combine centre-R-close with the geometric width decay
  -- width x (2n) ≤ w0 · recipPow2 n to obtain the closed-form bound
  -- for the second error term.
  --
  -- 由 centre-R-close 与几何宽度 width x (2n) ≤ w0 · recipPow2 n，
  -- 得到第二误差项的闭式界。
  term2 : ∀ n → n ≥ N →
    ∣ centre x (2 ℕ* n) * centre R (2 ℕ* n) - 1ℚ ∣
      ≤ (w0 * invb) * recipPow2 n
  term2 n n≥N = begin≤
    ∣ c * centre R (2 ℕ* n) - 1ℚ ∣
      ≈⟨ abs-comm ⟩
    ∣ centre R (2 ℕ* n) * c - 1ℚ ∣
      ≤⟨ centre-R-close n n≥N ⟩
    invb * width x (2 ℕ* n)
      ≤⟨ *-monoˡ-≤-nonNeg invb {{invb-nn}} (width-rec x n) ⟩
    invb * (w0 * r)
      ≈⟨ reorder ⟩
    (w0 * invb) * r
    ≤∎
    where
      c = centre x (2 ℕ* n)
      r = recipPow2 n

      abs-comm :
        ∣ c * centre R (2 ℕ* n) - 1ℚ ∣
        ≡ ∣ centre R (2 ℕ* n) * c - 1ℚ ∣
      abs-comm =
        cong (λ z → ∣ z - 1ℚ ∣)
             (*-comm c (centre R (2 ℕ* n)))

      reorder : invb * (w0 * r) ≡ (w0 * invb) * r
      reorder =
        begin
          invb * (w0 * r)
            ≡⟨ sym (*-assoc invb w0 r) ⟩
          (invb * w0) * r
            ≡⟨ cong (_* r) (*-comm invb w0) ⟩
          (w0 * invb) * r
        ∎

  -- Triangle inequality:
  --   centre(x*R)n − 1 = [centre(x*R)n − c·Rc] + [c·Rc − 1],
  -- where the first part is bounded by term1 with
  -- (w0·wR0·half)·recipPow2 n, and the second by term2 with
  -- (w0·invb)·recipPow2 n. Factoring out gives C · recipPow2 n.
  --
  -- 三角不等式：
  --   centre(x*R)n − 1 = [centre(x*R)n − c·Rc] + [c·Rc − 1]，
  -- 第一段由 term1 界为 (w0·wR0·half)·recipPow2 n，
  -- 第二段由 term2 界为 (w0·invb)·recipPow2 n，
  -- 提公因子即得 C · recipPow2 n。
  body : ∀ n → n ≥ N →
    ∣ centre (x *ℝ R) n - centre 1ℝ n ∣ ≤ C * recipPow2 n
  body n n≥N = begin≤
    ∣ centre (x *ℝ R) n - centre 1ℝ n ∣
      ≈⟨ cong (λ z → ∣ centre (x *ℝ R) n - z ∣) (centre-1ℝ n) ⟩
    ∣ P - 1ℚ ∣
      ≤⟨ tri-diff P Q 1ℚ ⟩
    ∣ P - Q ∣ + ∣ Q - 1ℚ ∣
      ≤⟨ +-mono-≤ (term1-inst n) (term2 n n≥N) ⟩
    t1c * r + t2c * r
      ≈⟨ sym (*-distribʳ-+ r t1c t2c) ⟩
    C * r
    ≤∎
    where
      P = centre (x *ℝ R) n
      Q = centre x (2 ℕ* n) * centre R (2 ℕ* n)
      r = recipPow2 n
      t1c = w0 * wR0 * half
      t2c = w0 * invb

------------------------------------------------------------------------
-- Main theorem
--
-- The product of a positive interval real and its reciprocal is
-- approximately one.
--
-- 主定理
--
-- 正实数的倒数与自身相乘近似等于 1。

*ℝ-inverse-pos : (x : RealI) (0<x : 0ℝ <ℝ x)
               → x *ℝ recipℝ x 0<x ≈ℝ 1ℝ
*ℝ-inverse-pos x 0<x = ≈ℝ-of-recN (x *ℝ R) 1ℝ N C 0≤C body
  where
    open ReciprocalSetup x 0<x
