------------------------------------------------------------------------
-- Rational algebra and convergence engines
--
-- The rational-level lemmas and the two convergence engines on which
-- every algebraic law over RealI depends.
--
-- 有理代数与收敛引擎
--
-- 本模块收集 RealI 上所有代数律共用的有理层引理与两个收敛引擎。
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module ALMA.Base.Real.Interval.Kit where

open import Data.Nat using
  (ℕ; suc; _^_; _∸_; s≤s; z≤n) renaming (_*_ to _ℕ*_; _≤_ to _≤ℕ_; _+_ to _+ℕ_)
open import Data.Nat.Properties using
  (*-suc; m≤m+n; ^-monoʳ-≤) renaming (≤-trans to ≤-transℕ; ≤-reflexive to ≤-reflexiveℕ
  ; *-assoc to *-assocℕ; *-comm to *-commℕ; *-identityʳ to *-identityʳℕ)
open import Data.Integer using (+≤+) renaming (+_ to +ℤ_)
import Data.Integer.Properties as ℤP
open import Data.Product using (_,_; Σ; proj₁; proj₂)
open import Data.Rational.Base using (1/_; *≤*; positive)
open import Data.Rational using
  (ℚ; 0ℚ; 1ℚ; _+_; _-_; -_; _*_; _≤_; _<_; ∣_∣; nonNegative; NonZero)
open import Data.Rational.Properties using
  (+-inverseʳ; *-identityˡ; *-identityʳ; *-assoc; *-comm; *-inverseʳ; *-distribʳ-+
  ; *-distribˡ-+; ≤-refl; ≤-reflexive; ≤-trans; 0≤p⇒∣p∣≡p; pos⇒nonZero; positive⁻¹
  ; 1/pos⇒pos; pos*pos⇒pos; <-≤-trans; ≤-<-trans; <⇒≤; *-monoˡ-≤-nonNeg
  ; *-monoʳ-≤-nonNeg; *-cancelˡ-≤-pos; ∣p+q∣≤∣p∣+∣q∣; ∣-p∣≡∣p∣)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; cong; sym; subst; module ≡-Reasoning)
open ≡-Reasoning

open import ALMA.Base.Real using (embed; 2ℚ; 2ℚ≡1+1; ε; 0<ε; embed-suc-pos; telescope)
open import ALMA.Base.Real.Interval using (RealI; pos-pow)
open import ALMA.Base.Real.Interval.Equiv using (_≈ℝ_)
open import ALMA.Base.Real.IntervalEquiv using
  (centre; recipPow2; bound-w; frac-strict; B<2^sucB; suc∸1; 0<2^n; negsub)

------------------------------------------------------------------------
-- Half and its NonZero instance
--
-- 二分之一及其非零实例

embed2-nz : NonZero (embed 2)
embed2-nz = pos⇒nonZero (embed 2) {{pos-pow 0}}

half : ℚ
half = Data.Rational.Base.1/_ (embed 2) {{embed2-nz}}

------------------------------------------------------------------------
-- Convergence engines
--
-- ≈ℝ-of-eq   pointwise centre equality ⟹ _≈ℝ_
-- ≈ℝ-of-rec  |centre difference| ≤ C · recipPow2 n ⟹ _≈ℝ_
--
-- 收敛引擎
--
-- 由逐点中心相等得到 _≈ℝ_。
-- 误差被 C · recipPow2 n 控制得到 _≈ℝ_。

≈ℝ-of-eq : (x y : RealI)
         → (∀ n → centre x n ≡ centre y n) → x ≈ℝ y
≈ℝ-of-eq x y h k = 0 , λ n _ →
  let
    eq0 : centre x n - centre y n ≡ 0ℚ
    eq0 = begin
      centre x n - centre y n
        ≡⟨ cong (λ w → w - centre y n) (h n) ⟩
      centre y n - centre y n
        ≡⟨ +-inverseʳ (centre y n) ⟩
      0ℚ
      ∎

    abs0 : ∣ centre x n - centre y n ∣ ≡ 0ℚ
    abs0 = begin
      ∣ centre x n - centre y n ∣
        ≡⟨ cong ∣_∣ eq0 ⟩
      ∣ 0ℚ ∣
        ≡⟨ 0≤p⇒∣p∣≡p {0ℚ} (≤-refl {0ℚ}) ⟩
      0ℚ
      ∎
  in subst (λ z → z < ε k) (sym abs0) (0<ε k)

------------------------------------------------------------------------
-- ℚ embedding monotonicity
--
-- ℚ 嵌入保序

embed-mono-≤ : ∀ {n m : ℕ} → n ≤ℕ m → embed n ≤ embed m
embed-mono-≤ {n} {m} n≤m =
  *≤* (ℤP.≤-trans (ℤP.≤-reflexive (ℤP.*-identityʳ (+ℤ n)))
       (ℤP.≤-trans (+≤+ n≤m)
                   (ℤP.≤-reflexive (sym (ℤP.*-identityʳ (+ℤ m))))))

------------------------------------------------------------------------
-- recipPow2 basics
--
-- recipPow2 基础

embed-suc∸1 : ∀ k → embed (suc (2 ^ k ∸ 1)) ≡ embed (2 ^ k)
embed-suc∸1 k = begin
  embed (suc (2 ^ k ∸ 1))
    ≡⟨ cong embed (suc∸1 (0<2^n k)) ⟩
  embed (2 ^ k)
  ∎

0<recipPow2 : ∀ n → 0ℚ < recipPow2 n
0<recipPow2 n =
  positive⁻¹ (recipPow2 n)
    {{1/pos⇒pos (embed (suc (2 ^ n ∸ 1))) {{embed-suc-pos}}}}

0≤recipPow2 : ∀ n → 0ℚ ≤ recipPow2 n
0≤recipPow2 n = <⇒≤ (0<recipPow2 n)

------------------------------------------------------------------------
-- Reciprocal antitone
--
-- 0 < a ≤ b ⟹ 1/b ≤ 1/a
--
-- 倒数反单调
--
-- 0 < a ≤ b ⟹ 1/b ≤ 1/a

recip-antitone : ∀ {a b : ℚ} (0<a : 0ℚ < a) (a≤b : a ≤ b) →
   1/_ (b) {{pos⇒nonZero b {{positive (<-≤-trans 0<a a≤b)}}}}
   ≤ 1/_ (a) {{pos⇒nonZero a {{positive 0<a}}}}
recip-antitone {a} {b} 0<a a≤b =
  *-cancelˡ-≤-pos (a * b) {{pos*pos⇒pos a {{positive 0<a}} b {{positive 0<b}}}}
    (≤-trans (≤-reflexive ab·b⁻¹≡a)
    (≤-trans a≤b
             (≤-reflexive (sym ab·a⁻¹≡b))))
  where
    0<b : 0ℚ < b
    0<b = <-≤-trans 0<a a≤b

    ab·b⁻¹≡a : (a * b) * (1/_ (b) {{pos⇒nonZero b {{positive 0<b}}}}) ≡ a
    ab·b⁻¹≡a =
      begin
        (a * b) * (1/_ (b) {{pos⇒nonZero b {{positive 0<b}}}})
          ≡⟨ *-assoc a b (1/_ (b) {{pos⇒nonZero b {{positive 0<b}}}}) ⟩
        a * (b * (1/_ (b) {{pos⇒nonZero b {{positive 0<b}}}}))
          ≡⟨ cong (a *_) (*-inverseʳ b {{pos⇒nonZero b {{positive 0<b}}}}) ⟩
        a * 1ℚ
          ≡⟨ *-identityʳ a ⟩
        a
      ∎

    ab·a⁻¹≡b : (a * b) * (1/_ (a) {{pos⇒nonZero a {{positive 0<a}}}}) ≡ b
    ab·a⁻¹≡b =
      begin
        (a * b) * (1/_ (a) {{pos⇒nonZero a {{positive 0<a}}}})
          ≡⟨ *-assoc a b (1/_ (a) {{pos⇒nonZero a {{positive 0<a}}}}) ⟩
        a * (b * (1/_ (a) {{pos⇒nonZero a {{positive 0<a}}}}))
          ≡⟨ cong (a *_) (*-comm b (1/_ (a) {{pos⇒nonZero a {{positive 0<a}}}})) ⟩
        a * ((1/_ (a) {{pos⇒nonZero a {{positive 0<a}}}}) * b)
          ≡⟨ sym (*-assoc a (1/_ (a) {{pos⇒nonZero a {{positive 0<a}}}}) b) ⟩
        (a * (1/_ (a) {{pos⇒nonZero a {{positive 0<a}}}})) * b
          ≡⟨ cong (_* b) (*-inverseʳ a {{pos⇒nonZero a {{positive 0<a}}}}) ⟩
        1ℚ * b
          ≡⟨ *-identityˡ b ⟩
        b
      ∎

recipPow2-mono : ∀ {n m : ℕ} → n ≤ℕ m → recipPow2 m ≤ recipPow2 n
recipPow2-mono {n} {m} n≤m =
  recip-antitone {a = embed (suc (2 ^ n ∸ 1))} {b = embed (suc (2 ^ m ∸ 1))}
    (positive⁻¹ (embed (suc (2 ^ n ∸ 1))) {{embed-suc-pos}})
    (≤-trans (≤-reflexive (embed-suc∸1 n))
    (≤-trans (embed-mono-≤ (^-monoʳ-≤ 2 n≤m))
             (≤-reflexive (sym (embed-suc∸1 m)))))

------------------------------------------------------------------------
-- Natural-number inequalities
--
-- n ≤ 2n ≤ 4n
--
-- 自然数不等式
--
-- n ≤ 2n ≤ 4n

n+n≡2n : ∀ n → n +ℕ n ≡ 2 ℕ* n
n+n≡2n n =
  sym (begin
    2 ℕ* n
      ≡⟨ *-commℕ 2 n ⟩
    n ℕ* 2
      ≡⟨ *-suc n 1 ⟩
    n +ℕ (n ℕ* 1)
      ≡⟨ cong (n +ℕ_) (*-identityʳℕ n) ⟩
    n +ℕ n
  ∎)

n≤2n : ∀ n → n ≤ℕ 2 ℕ* n
n≤2n n = ≤-transℕ (m≤m+n n n) (≤-reflexiveℕ (n+n≡2n n))

2*2n≡4n : ∀ n → 2 ℕ* (2 ℕ* n) ≡ 4 ℕ* n
2*2n≡4n n =
  begin
    2 ℕ* (2 ℕ* n)
      ≡⟨ sym (*-assocℕ 2 2 n) ⟩
    (2 ℕ* 2) ℕ* n
      ≡⟨ refl ⟩
    4 ℕ* n
  ∎

2n≤4n : ∀ n → 2 ℕ* n ≤ℕ 4 ℕ* n
2n≤4n n = ≤-transℕ (n≤2n (2 ℕ* n)) (≤-reflexiveℕ (2*2n≡4n n))

n≤4n : ∀ n → n ≤ℕ 4 ℕ* n
n≤4n n = ≤-transℕ (n≤2n n) (2n≤4n n)

------------------------------------------------------------------------
-- Monotone multiplication by a non-negative factor
--
-- 非负因子下的乘法单调

*-mono-≤-nonNeg : ∀ {a a' b b' : ℚ} → 0ℚ ≤ a → a ≤ a' → 0ℚ ≤ b → b ≤ b' →
                  a * b ≤ a' * b'
*-mono-≤-nonNeg {a} {a'} {b} {b'} 0≤a a≤a' 0≤b b≤b' =
  ≤-trans (*-monoʳ-≤-nonNeg b {{nonNegative 0≤b}} a≤a')
          (*-monoˡ-≤-nonNeg a' {{nonNegative (≤-trans 0≤a a≤a')}} b≤b')

------------------------------------------------------------------------
-- Archimedean tail
--
-- C · recipPow2 n eventually < ε k.
--
-- 阿基米德收尾
--
-- C · recipPow2 n 最终小于 ε k。

recipPow2-bound : (C : ℚ) → 0ℚ ≤ C → (k : ℕ) →
  Σ ℕ (λ N → ∀ n → N ≤ℕ n → C * recipPow2 n < ε k)
recipPow2-bound C 0≤C k =
  N , λ n N≤n → ≤-<-trans (mono n N≤n) key
  where
    M : ℕ
    M = proj₁ (bound-w C 0≤C)

    C≤M : C ≤ embed M
    C≤M = proj₂ (bound-w C 0≤C)

    N : ℕ
    N = suc (M ℕ* suc k)

    key : embed M * recipPow2 N < ε k
    key = frac-strict M k N (B<2^sucB (M ℕ* suc k))

    mono : ∀ n → N ≤ℕ n → C * recipPow2 n ≤ embed M * recipPow2 N
    mono n N≤n =
      *-mono-≤-nonNeg 0≤C C≤M (0≤recipPow2 n) (recipPow2-mono N≤n)

≈ℝ-of-rec : (x y : RealI) (C : ℚ) → 0ℚ ≤ C →
  (∀ n → ∣ centre x n - centre y n ∣ ≤ C * recipPow2 n) → x ≈ℝ y
≈ℝ-of-rec x y C 0≤C h k =
  let N , w = recipPow2-bound C 0≤C k
  in N , λ n N≤n → ≤-<-trans (h n) (w n N≤n)

------------------------------------------------------------------------
-- Absolute value and triangle utilities
--
-- 绝对值与三角不等式工具

abs-swap : ∀ a b → ∣ a - b ∣ ≡ ∣ b - a ∣
abs-swap a b = begin
  ∣ a - b ∣
    ≡⟨ cong ∣_∣ (sym (negsub b a)) ⟩
  ∣ - (b - a) ∣
    ≡⟨ ∣-p∣≡∣p∣ (b - a) ⟩
  ∣ b - a ∣
  ∎

tri-diff : ∀ a b c → ∣ a - c ∣ ≤ ∣ a - b ∣ + ∣ b - c ∣
tri-diff a b c =
  subst (λ z → ∣ z ∣ ≤ ∣ a - b ∣ + ∣ b - c ∣) (telescope a b c)
        (∣p+q∣≤∣p∣+∣q∣ (a - b) (b - c))

------------------------------------------------------------------------
-- Half-scale utilities
--
-- 二分之一尺度工具

add-self : ∀ W → W + W ≡ 2ℚ * W
add-self W =
  begin
    W + W
      ≡⟨ cong (λ z → z + W) (sym (*-identityˡ W)) ⟩
    1ℚ * W + W
      ≡⟨ cong (λ z → 1ℚ * W + z) (sym (*-identityˡ W)) ⟩
    1ℚ * W + 1ℚ * W
      ≡⟨ sym (*-distribʳ-+ W 1ℚ 1ℚ) ⟩
    (1ℚ + 1ℚ) * W
      ≡⟨ cong (λ z → z * W) (sym 2ℚ≡1+1) ⟩
    2ℚ * W
  ∎

2ℚ*half≡1 : 2ℚ * half ≡ 1ℚ
2ℚ*half≡1 = begin
  2ℚ * half
    ≡⟨ *-inverseʳ (embed 2) {{embed2-nz}} ⟩
  1ℚ
  ∎

half+half≡1 : half + half ≡ 1ℚ
half+half≡1 =
  begin
    half + half
      ≡⟨ add-self half ⟩
    2ℚ * half
      ≡⟨ 2ℚ*half≡1 ⟩
    1ℚ
  ∎

two-half : ∀ X → X * half + X * half ≡ X
two-half X =
  begin
    X * half + X * half
      ≡⟨ sym (*-distribˡ-+ X half half) ⟩
    X * (half + half)
      ≡⟨ cong (X *_) half+half≡1 ⟩
    X * 1ℚ
      ≡⟨ *-identityʳ X ⟩
    X
  ∎

0<half : 0ℚ < half
0<half = positive⁻¹ half {{1/pos⇒pos (embed 2) {{embed-suc-pos}}}}

0≤half : 0ℚ ≤ half
0≤half = <⇒≤ 0<half

half≤1 : half ≤ 1ℚ
half≤1 =
  *-cancelˡ-≤-pos 2ℚ {{embed-suc-pos {1}}}
    (≤-trans (≤-reflexive 2ℚ*half≡1)
    (≤-trans (embed-mono-≤ {1} {2} (s≤s z≤n))
             (≤-reflexive (sym (*-identityʳ 2ℚ)))))

half-drop : ∀ {a b : ℚ} → 0ℚ ≤ a → a ≤ b → a * half ≤ b
half-drop {a} {b} 0≤a a≤b =
  ≤-trans (*-mono-≤-nonNeg 0≤a a≤b 0≤half half≤1)
          (≤-reflexive (*-identityʳ b))
