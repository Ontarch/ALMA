------------------------------------------------------------------------
-- Rational algebra and convergence engines
--
-- 有理代数与收敛引擎
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module Real.Interval.Kit where

open import Data.Nat using (ℕ; zero; suc; _^_; _∸_; s≤s; z≤n)
  renaming (_*_ to _ℕ*_; _≤_ to _≤ℕ_; _+_ to _+ℕ_)
open import Data.Nat.Properties using (*-suc; m≤m+n; ^-monoʳ-≤)
  renaming (≤-trans to ≤-transℕ; ≤-reflexive to ≤-reflexiveℕ
  ; *-assoc to *-assocℕ; *-comm to *-commℕ; *-identityʳ to *-identityʳℕ)
import Data.Nat.Properties as ℕP
import Data.Integer.Properties as ℤP
open import Data.Product using (_,_; Σ; proj₁; proj₂)
open import Data.Rational.Base using (1/_; _÷_; positive)
open import Data.Rational using
  (ℚ; 0ℚ; 1ℚ; _+_; _-_; _*_; _≤_; _<_; ∣_∣; nonNegative; NonZero
  ; Positive; NonNegative)  renaming (-_ to neg)
open import Data.Rational.Properties using
  (+-inverseʳ; +-identityˡ; +-mono-≤; *-identityˡ; *-identityʳ; *-assoc; *-comm
  ; *-inverseʳ; *-inverseˡ; *-distribʳ-+; *-distribˡ-+; ≤-refl; ≤-reflexive
  ; ≤-trans; 0≤p⇒∣p∣≡p; pos⇒nonZero; positive⁻¹; 1/pos⇒pos; pos*pos⇒pos
  ; pos⇒nonNeg; <-≤-trans; ≤-<-trans; <⇒≤; *-monoˡ-≤-nonNeg; *-monoʳ-≤-nonNeg
  ; *-cancelˡ-≤-pos; *-cancelˡ-<-nonNeg; ∣p+q∣≤∣p∣+∣q∣; ∣-p∣≡∣p∣
  ; <-trans; +-assoc; +-comm; +-inverseˡ; +-identityʳ; *-zeroˡ; *-zeroʳ
  ; *-monoʳ-<-pos; 0≤∣p∣; <-cmp; neg-distribˡ-*; <-asym; <-irrefl)
open import Relation.Binary.Definitions using (tri<; tri≈; tri>)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; cong; cong₂; sym; trans; subst; module ≡-Reasoning)
open ≡-Reasoning

open import Base.RationalRing using (0<1; telescope)
open import Real using
  (embed; half; embed2-nonZero; 2ℚ; 2ℚ≡1+1; ε; 0<ε; embed-mono-≤; embed-suc-pos
  ; 0<embed; embed-mono-<; reciprocal-cong; embed-*-hom)
open import Real.Interval using (RealI)
open import Real.Interval.Equiv using (_≈ℝ_)
open import Real.IntervalEquiv using
  (centre; recipPow2; bound-w; frac-strict; B<2^sucB; n<2^n; 1≤2^n)
open import Real.Interval.Rational using (suc∸1; 0<2^t; negsub)

------------------------------------------------------------------------
-- Convergence engines
--
-- ≈ℝ-of-eq   pointwise centre equality ⟹ _≈ℝ_
-- ≈ℝ-of-rec  |centre difference| ≤ C · recipPow2 n ⟹ _≈ℝ_
--
-- 收敛引擎
--
-- 由逐点中心相等得到 _≈ℝ_。
-- 误差被逐层几何衰减界控制得到 _≈ℝ_。

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
-- recipPow2 basics
--
-- recipPow2 基础

embed-suc∸1 : ∀ k → embed (suc (2 ^ k ∸ 1)) ≡ embed (2 ^ k)
embed-suc∸1 k = begin
  embed (suc (2 ^ k ∸ 1))
    ≡⟨ cong embed (suc∸1 (0<2^t k)) ⟩
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

recip-antitone : ∀ {a b : ℚ} (0<a : 0ℚ < a) (a≤b : a ≤ b) →
   1/_ (b) {{pos⇒nonZero b {{positive (<-≤-trans 0<a a≤b)}}}}
   ≤ 1/_ (a) {{pos⇒nonZero a {{positive 0<a}}}}
recip-antitone {a} {b} 0<a a≤b =
  *-cancelˡ-≤-pos (a * b)
    {{pos*pos⇒pos a {{positive 0<a}} b {{positive 0<b}}}}
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
-- 几何衰减项最终落在给定精度之下。

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
  ∣ neg (b - a) ∣
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
    ≡⟨ *-inverseʳ (embed 2) {{embed2-nonZero}} ⟩
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

------------------------------------------------------------------------
-- Positivity of B + 1
--
-- B + 1 的正性

B+1-pos : (B : ℚ) → 0ℚ ≤ B → Positive (B + 1ℚ)
B+1-pos B 0≤B = positive (<-≤-trans 0<1 1≤B+1)
  where
  1≤B+1 : 1ℚ ≤ B + 1ℚ
  1≤B+1 = ≤-trans (≤-reflexive (sym (+-identityˡ 1ℚ)))
                  (+-mono-≤ 0≤B (≤-refl {1ℚ}))

------------------------------------------------------------------------
-- Reciprocal distributivity
--
-- 倒数分配

inv-distrib : (p q : ℚ) → .{{pp : Positive p}} → .{{qq : Positive q}} →
  1/_ (p * q) {{pos⇒nonZero (p * q) {{pos*pos⇒pos p {{pp}} q {{qq}}}}}} ≡
  (1/_ p {{pos⇒nonZero p {{pp}}}}) * (1/_ q {{pos⇒nonZero q {{qq}}}})
inv-distrib p q {{pp}} {{qq}} = begin
  invpq
    ≡⟨ sym (*-identityʳ invpq) ⟩
  invpq * 1ℚ
    ≡⟨ cong (invpq *_) (sym prod-inv) ⟩
  invpq * ((p * q) * (invp * invq))
    ≡⟨ sym (*-assoc invpq (p * q) _) ⟩
  (invpq * (p * q)) * (invp * invq)
    ≡⟨ cong (_* (invp * invq)) (*-inverseˡ (p * q) {{pq-nz}}) ⟩
  1ℚ * (invp * invq)
    ≡⟨ *-identityˡ (invp * invq) ⟩
  invp * invq
  ∎
  where
  p-nz = pos⇒nonZero p {{pp}}
  q-nz = pos⇒nonZero q {{qq}}
  pq-nz = pos⇒nonZero (p * q) {{pos*pos⇒pos p {{pp}} q {{qq}}}}
  invp = 1/_ p {{p-nz}}
  invq = 1/_ q {{q-nz}}
  invpq = 1/_ (p * q) {{pq-nz}}
  prod-inv : (p * q) * (invp * invq) ≡ 1ℚ
  prod-inv = begin
    (p * q) * (invp * invq)
      ≡⟨ *-assoc p q _ ⟩
    p * (q * (invp * invq))
      ≡⟨ cong (p *_) (sym (*-assoc q invp invq)) ⟩
    p * ((q * invp) * invq)
      ≡⟨ cong (p *_) (cong (_* invq) (*-comm q invp)) ⟩
    p * ((invp * q) * invq)
      ≡⟨ cong (p *_) (*-assoc invp q invq) ⟩
    p * (invp * (q * invq))
      ≡⟨ sym (*-assoc p invp (q * invq)) ⟩
    (p * invp) * (q * invq)
      ≡⟨ cong₂ _*_ (*-inverseʳ p {{p-nz}}) (*-inverseʳ q {{q-nz}}) ⟩
    1ℚ * 1ℚ
      ≡⟨ *-identityˡ 1ℚ ⟩
    1ℚ
    ∎

------------------------------------------------------------------------
-- Reciprocal strictly antitone
--
-- 倒数严格反单调

strict-recip : (a b : ℚ) → (0<a : 0ℚ < a) → (a<b : a < b) →
  1/_ b {{pos⇒nonZero b {{positive (<-≤-trans 0<a (<⇒≤ a<b))}}}}
  < 1/_ a {{pos⇒nonZero a {{positive 0<a}}}}
strict-recip a b 0<a a<b =
  let
    0<b = <-≤-trans 0<a (<⇒≤ a<b)
    a-nz = pos⇒nonZero a {{positive 0<a}}
    b-nz = pos⇒nonZero b {{positive 0<b}}
    ab-pos : Positive (a * b)
    ab-pos = pos*pos⇒pos a {{positive 0<a}} b {{positive 0<b}}
    ab-nn : NonNegative (a * b)
    ab-nn = pos⇒nonNeg (a * b) {{ab-pos}}
    lhs-eq : (a * b) * 1/_ b {{b-nz}} ≡ a
    lhs-eq =
      begin
        (a * b) * 1/_ b {{b-nz}}
          ≡⟨ *-assoc a b _ ⟩
        a * (b * 1/_ b {{b-nz}})
          ≡⟨ cong (a *_) (*-inverseʳ b {{b-nz}}) ⟩
        a * 1ℚ
          ≡⟨ *-identityʳ a ⟩
        a
        ∎
    rhs-eq : b ≡ (a * b) * 1/_ a {{a-nz}}
    rhs-eq =
      begin
        b
          ≡⟨ sym (*-identityʳ b) ⟩
        b * 1ℚ
          ≡⟨ cong (b *_) (sym (*-inverseʳ a {{a-nz}})) ⟩
        b * (a * 1/_ a {{a-nz}})
          ≡⟨ sym (*-assoc b a (1/_ a {{a-nz}})) ⟩
        (b * a) * 1/_ a {{a-nz}}
          ≡⟨ cong (λ z → z * 1/_ a {{a-nz}}) (*-comm b a) ⟩
        (a * b) * 1/_ a {{a-nz}}
        ∎
  in *-cancelˡ-<-nonNeg (a * b) {{ab-nn}}
       (<-≤-trans (≤-<-trans (≤-reflexive lhs-eq) a<b)
                  (≤-reflexive rhs-eq))

------------------------------------------------------------------------
-- ε tail selection
--
-- ε 尾部选取

pick : (B : ℚ) → 0ℚ ≤ B → (k : ℕ) →
  Σ ℕ (λ m → ε m * (B + 1ℚ) ≤ (ε k) ÷ embed 6)
pick B 0≤B k = m , bound
  where
  Bp = B + 1ℚ
  1≤Bp : 1ℚ ≤ Bp
  1≤Bp = ≤-trans (≤-reflexive (sym (+-identityˡ 1ℚ)))
                  (+-mono-≤ 0≤B (≤-refl {1ℚ}))
  0<Bp : 0ℚ < Bp
  0<Bp = <-≤-trans 0<1 1≤Bp
  D = embed (suc k) * embed 6 * Bp
  PE = embed (suc k) * embed 6
  PE-pos : Positive PE
  PE-pos = pos*pos⇒pos (embed (suc k)) {{embed-suc-pos}}
                       (embed 6) {{positive (0<embed 5)}}
  0<D : 0ℚ < D
  0<D = positive⁻¹ D {{pos*pos⇒pos PE {{PE-pos}} Bp {{positive 0<Bp}}}}
  0≤D : 0ℚ ≤ D
  0≤D = <⇒≤ 0<D
  M = proj₁ (bound-w D 0≤D)
  D≤M : D ≤ embed M
  D≤M = proj₂ (bound-w D 0≤D)
  m = suc M
  0<embedM : 0ℚ < embed M
  0<embedM = <-≤-trans 0<D D≤M
  M≤sM : embed M ≤ embed (suc (suc M))
  M≤sM = embed-mono-≤
           (ℕP.m≤n⇒m≤1+n (ℕP.m≤n⇒m≤1+n (ℕP.≤-refl {M})))
  M-nz : NonZero (embed M)
  M-nz = pos⇒nonZero (embed M) {{positive 0<embedM}}
  invM = 1/_ (embed M) {{M-nz}}
  step1 : ε m ≤ invM
  step1 = recip-antitone 0<embedM M≤sM
  D-nz : NonZero D
  D-nz = pos⇒nonZero D {{positive 0<D}}
  invD = 1/_ D {{D-nz}}
  step2 : invM ≤ invD
  step2 = recip-antitone 0<D D≤M
  εm≤1/D : ε m ≤ invD
  εm≤1/D = ≤-trans step1 step2
  Bp-nn : NonNegative Bp
  Bp-nn = pos⇒nonNeg Bp {{positive 0<Bp}}
  mult = *-monoʳ-≤-nonNeg Bp {{Bp-nn}} εm≤1/D
  A = embed (suc k)
  E = embed 6
  P = A * E
  A-nz : NonZero A
  A-nz = pos⇒nonZero A {{embed-suc-pos}}
  E-nz : NonZero E
  E-nz = pos⇒nonZero E {{positive (0<embed 5)}}
  P-pos : Positive P
  P-pos = pos*pos⇒pos A {{embed-suc-pos}} E {{positive (0<embed 5)}}
  Bp-pos : Positive Bp
  Bp-pos = positive 0<Bp
  Bp-nz : NonZero Bp
  Bp-nz = pos⇒nonZero Bp {{Bp-pos}}
  invBp = 1/_ Bp {{Bp-nz}}
  invA = 1/_ A {{A-nz}}
  invE = 1/_ E {{E-nz}}
  invP = invA * invE
  invD-expand : invD ≡ invA * invE * invBp
  invD-expand = begin
    invD
      ≡⟨ inv-distrib P Bp {{P-pos}} {{Bp-pos}} ⟩
    (1/_ P {{pos⇒nonZero P {{P-pos}}}}) * invBp
      ≡⟨ cong (_* invBp) (inv-distrib A E {{embed-suc-pos}} {{positive (0<embed 5)}}) ⟩
    invA * invE * invBp
    ∎
  cancel : Bp * invD ≡ invP
  cancel = begin
    Bp * invD
      ≡⟨ cong (Bp *_) invD-expand ⟩
    Bp * (invA * invE * invBp)
      ≡⟨ cong (Bp *_) (*-comm (invA * invE) invBp) ⟩
    Bp * (invBp * (invA * invE))
      ≡⟨ sym (*-assoc Bp invBp (invA * invE)) ⟩
    (Bp * invBp) * invP
      ≡⟨ cong (_* invP) (*-inverseʳ Bp {{Bp-nz}}) ⟩
    1ℚ * invP
      ≡⟨ *-identityˡ invP ⟩
    invP
    ∎
  eq : invD * Bp ≡ (ε k) ÷ E
  eq = begin
    invD * Bp
      ≡⟨ *-comm invD Bp ⟩
    Bp * invD
      ≡⟨ cancel ⟩
    invP
      ≡⟨⟩
    (ε k) ÷ E
    ∎
  bound : ε m * Bp ≤ (ε k) ÷ E
  bound = ≤-trans mult (≤-reflexive eq)

------------------------------------------------------------------------
-- Rational and Nat toolkit used by the norm development
--
-- 范数开发所用的有理数/自然数工具

0<1Q : 0ℚ < 1ℚ
0<1Q = positive⁻¹ 1ℚ

-- embed 2 and embed 3 are positive.
--
-- embed 2 与 embed 3 为正。
0<embed2 : 0ℚ < embed 2
0<embed2 = embed-mono-< (s≤s z≤n)

0<embed3 : 0ℚ < embed 3
0<embed3 = <-trans 0<embed2 (embed-mono-< (s≤s (s≤s (s≤s z≤n))))

-- Double negation.
--
-- 双重取负。
neg-neg : (x : ℚ) → neg (neg x) ≡ x
neg-neg x =
  begin neg (neg x)
    ≡⟨ sym (+-identityʳ (neg (neg x))) ⟩ neg (neg x) + 0ℚ
    ≡⟨ cong (neg (neg x) +_) (sym (+-inverseˡ x)) ⟩ neg (neg x) + (neg x + x)
    ≡⟨ sym (+-assoc (neg (neg x)) (neg x) x) ⟩ (neg (neg x) + neg x) + x
    ≡⟨ cong (_+ x) (+-inverseˡ (neg x)) ⟩ 0ℚ + x
    ≡⟨ +-identityˡ x ⟩ x ∎

-- Nonpositive inputs have nonnegative negation.
--
-- 非正数的取负非负。
neg-of-nonpos : {x : ℚ} → x ≤ 0ℚ → 0ℚ ≤ neg x
neg-of-nonpos {x} x≤0 =
  let step : x + neg x ≤ 0ℚ + neg x
      step = +-mono-≤ x≤0 ≤-refl
      lhs0 : x + neg x ≡ 0ℚ
      lhs0 = +-inverseʳ x
      step1 : 0ℚ ≤ 0ℚ + neg x
      step1 = subst (λ z → z ≤ 0ℚ + neg x) lhs0 step
      rhs : 0ℚ + neg x ≡ neg x
      rhs = +-identityˡ (neg x)
  in subst (λ z → 0ℚ ≤ z) rhs step1

-- The absolute value of a nonpositive rational is its negation.
--
-- 非正数的绝对值等于其相反数。
npos⇒∣p∣≡neg : {x : ℚ} → x ≤ 0ℚ → ∣ x ∣ ≡ neg x
npos⇒∣p∣≡neg {x} x≤0 =
  begin ∣ x ∣
       ≡⟨ sym (∣-p∣≡∣p∣ x) ⟩ ∣ neg x ∣
       ≡⟨ 0≤p⇒∣p∣≡p (neg-of-nonpos x≤0) ⟩ neg x ∎

------------------------------------------------------------------------
-- Reciprocal utilities
--
-- 倒数工具

inv-pos : (e : ℚ) → {{e-pos : Positive e}} →
  Positive ((1/_) e {{pos⇒nonZero e {{e-pos}}}})
inv-pos e {{e-pos}} with <-cmp 0ℚ ((1/_) e {{pos⇒nonZero e {{e-pos}}}})
... | tri< 0<ie _ _ = positive 0<ie
... | tri≈ _ 0≡ie _ =
  let ie = (1/_) e {{pos⇒nonZero e {{e-pos}}}}
      e·ie≡1 : e * ie ≡ 1ℚ
      e·ie≡1 = *-inverseʳ e {{pos⇒nonZero e {{e-pos}}}}
      e·ie≡0 : e * ie ≡ 0ℚ
      e·ie≡0 =
        begin e * ie ≡⟨ cong (e *_) (sym 0≡ie) ⟩ e * 0ℚ ≡⟨ *-zeroʳ e ⟩ 0ℚ ∎
      1≡0 : 1ℚ ≡ 0ℚ
      1≡0 = trans (sym e·ie≡1) e·ie≡0
      0<0 : 0ℚ < 0ℚ
      0<0 = subst (λ z → 0ℚ < z) 1≡0 0<1Q
  in contradiction 0<0 (<-irrefl refl)
... | tri> _ _ ie<0 =
  let ie = (1/_) e {{pos⇒nonZero e {{e-pos}}}}
      e·ie≡1 : e * ie ≡ 1ℚ
      e·ie≡1 = *-inverseʳ e {{pos⇒nonZero e {{e-pos}}}}
      e·ie<0 : e * ie < 0ℚ
      e·ie<0 =
        let step : e * ie < e * 0ℚ
            step = *-monoʳ-<-pos e {{e-pos}} ie<0
        in subst (λ z → e * ie < z) (*-zeroʳ e) step
      1<0 : 1ℚ < 0ℚ
      1<0 = subst (λ z → z < 0ℚ) e·ie≡1 e·ie<0
  in contradiction 1<0 (<-asym 0<1Q)

1≤⇒inv≤1 : {e : ℚ} ⦃ _ : NonZero e ⦄ → 0ℚ < e → 1ℚ ≤ e → (1/_) e ≤ 1ℚ
1≤⇒inv≤1 {e} 0e p =
  let inv = (1/_) e {{pos⇒nonZero e {{positive 0e}}}}
      pinv : Positive inv
      pinv = inv-pos e {{positive 0e}}
      q : inv * 1ℚ ≤ inv * e
      q = *-monoˡ-≤-nonNeg inv {{pos⇒nonNeg inv {{pinv}}}} p
      e1 : inv * e ≡ 1ℚ
      e1 = *-inverseˡ e {{pos⇒nonZero e {{positive 0e}}}}
  in subst (λ z → z ≤ 1ℚ) (*-identityʳ inv)
       (subst (λ z → inv * 1ℚ ≤ z) e1 q)

recip-*-hom : (a b : ℚ) ⦃ na : NonZero a ⦄ ⦃ nb : NonZero b ⦄
  ⦃ nab : NonZero (a * b) ⦄ →
  (1/_) (a * b) ≡ (1/_) a * (1/_) b
recip-*-hom a b ⦃ na ⦄ ⦃ nb ⦄ ⦃ nab ⦄ =
  let ia = (1/_) a
      ib = (1/_) b
      x = ia * ib
      p : x * (a * b) ≡ 1ℚ
      p =
        begin (ia * ib) * (a * b)
          ≡⟨ *-assoc ia ib (a * b) ⟩
        ia * (ib * (a * b))
          ≡⟨ cong (ia *_) (sym (*-assoc ib a b)) ⟩
        ia * ((ib * a) * b)
          ≡⟨ cong (ia *_) (cong (λ z → z * b) (*-comm ib a)) ⟩
        ia * ((a * ib) * b)
          ≡⟨ cong (ia *_) (*-assoc a ib b) ⟩
        ia * (a * (ib * b))
          ≡⟨ sym (*-assoc ia a (ib * b)) ⟩
        (ia * a) * (ib * b)
          ≡⟨ cong₂ (λ u v → u * v) (*-inverseˡ a) (*-inverseˡ b) ⟩
        1ℚ ∎
      q : x ≡ (1/_) (a * b)
      q =
        begin x
          ≡⟨ sym (*-identityʳ x) ⟩
        x * 1ℚ
          ≡⟨ cong (x *_) (sym (*-inverseʳ (a * b) ⦃ nab ⦄)) ⟩
        x * ((a * b) * (1/_) (a * b))
          ≡⟨ sym (*-assoc x (a * b) ((1/_) (a * b))) ⟩
        (x * (a * b)) * (1/_) (a * b)
          ≡⟨ cong (λ z → z * (1/_) (a * b)) p ⟩
        1ℚ * (1/_) (a * b)
          ≡⟨ *-identityˡ ((1/_) (a * b)) ⟩
        (1/_) (a * b) ∎
  in sym q

------------------------------------------------------------------------
-- halveQ algebra
--
-- halveQ 的代数

halveQ : ℚ → ℚ
halveQ x = x * half

half≥0' : 0ℚ ≤ half
half≥0' =
  let embed2-pos = positive (embed-mono-< (s≤s z≤n))
      half-pos : Positive half
      half-pos = inv-pos (embed 2) {{embed2-pos}}
  in <⇒≤ (positive⁻¹ half {{half-pos}})

halveQ-mono : {a b : ℚ} → a ≤ b → halveQ a ≤ halveQ b
halveQ-mono {a} {b} p =
  let embed2-pos : Positive (embed 2)
      embed2-pos = positive (embed-mono-< (s≤s z≤n))
      half≡ : half ≡ (1/_) (embed 2) {{pos⇒nonZero (embed 2) {{embed2-pos}}}}
      half≡ = refl
      half-pos : Positive half
      half-pos = subst Positive (sym half≡)
                   (inv-pos (embed 2) {{embed2-pos}})
      half≥0 : NonNegative half
      half≥0 = pos⇒nonNeg half {{half-pos}}
  in *-monoʳ-≤-nonNeg half {{half≥0}} p

0≤halveQ : {x : ℚ} → 0ℚ ≤ x → 0ℚ ≤ halveQ x
0≤halveQ {x} 0≤x =
  subst (λ z → z ≤ halveQ x) (sym (*-zeroˡ half)) (halveQ-mono 0≤x)

halveQ-distrib : (a b : ℚ) → halveQ (a + b) ≡ halveQ a + halveQ b
halveQ-distrib a b = *-distribʳ-+ half a b

halveQ-double : (x : ℚ) → halveQ (x + x) ≡ x
halveQ-double x =
  begin (x + x) * half
    ≡⟨ *-distribʳ-+ half x x ⟩ x * half + x * half
    ≡⟨ sym (*-distribˡ-+ x half half) ⟩ x * (half + half)
    ≡⟨ cong (x *_) half+half≡1 ⟩ x * 1ℚ
    ≡⟨ *-identityʳ x ⟩ x ∎

halveQ-neg : (a : ℚ) → halveQ (neg a) ≡ neg (halveQ a)
halveQ-neg a =
  begin (neg a) * half
    ≡⟨ sym (neg-distribˡ-* a half) ⟩ neg (a * half) ∎

------------------------------------------------------------------------
-- Order and difference utilities on ℚ
--
-- ℚ 上的序与差工具

x≤∣x∣ : (x : ℚ) → x ≤ ∣ x ∣
x≤∣x∣ x with <-cmp x 0ℚ
... | tri< x<0 _ _ = ≤-trans (<⇒≤ x<0) (0≤∣p∣ x)
... | tri≈ _ x=0 _ = subst (λ z → z ≤ ∣ z ∣) (sym x=0) (0≤∣p∣ 0ℚ)
... | tri> _ _ x>0 = ≤-reflexive (sym (0≤p⇒∣p∣≡p (<⇒≤ x>0)))

same⇒diff0 : {a b : ℚ} → a ≡ b → ∣ a - b ∣ ≡ 0ℚ
same⇒diff0 {a} {b} eq =
  begin ∣ a - b ∣
    ≡⟨ cong ∣_∣ (trans (cong (λ x → x - b) eq) (+-inverseʳ b)) ⟩ ∣ 0ℚ ∣
    ≡⟨ 0≤p⇒∣p∣≡p ≤-refl ⟩ 0ℚ ∎

0≤diff : {a b : ℚ} → a ≤ b → 0ℚ ≤ b - a
0≤diff {a} {b} a≤b =
  ≤-trans (≤-reflexive (sym (+-inverseʳ a))) (+-mono-≤ a≤b ≤-refl)

move-≤ : {a b w : ℚ} → a - b ≤ w → a ≤ b + w
move-≤ {a} {b} {w} h =
  let e : (a + neg b) + b ≡ a
      e = trans (+-assoc a (neg b) b)
            (trans (cong (a +_) (+-inverseˡ b)) (+-identityʳ a))
  in subst (λ z → z ≤ b + w) e
       (subst (λ z → (a + neg b) + b ≤ z) (+-comm w b)
              (+-mono-≤ h ≤-refl))

move-≤-back : {a b w : ℚ} → a ≤ b + w → a - b ≤ w
move-≤-back {a} {b} {w} h =
  let e : (b + w) + neg b ≡ w
      e = trans (+-comm (b + w) (neg b))
            (trans (sym (+-assoc (neg b) b w))
                   (trans (cong (_+ w) (+-inverseˡ b)) (+-identityˡ w)))
  in subst (λ z → a + neg b ≤ z) e (+-mono-≤ h ≤-refl)

+-monoʳ-≤ : (c : ℚ) → {a b : ℚ} → a ≤ b → c + a ≤ c + b
+-monoʳ-≤ c {a} {b} h = +-mono-≤ (≤-refl {c}) h

------------------------------------------------------------------------
-- recipPow2 utilities
--
-- recipPow2 工具

nz2n : (n : ℕ) → NonZero (embed (2 ^ n))
nz2n n = pos⇒nonZero (embed (2 ^ n))
  {{positive (embed-mono-< (ℕP.≤-<-trans z≤n (n<2^n n)))}}

nzSuc : (n : ℕ) → NonZero (embed (suc (2 ^ n ∸ 1)))
nzSuc n = pos⇒nonZero (embed (suc (2 ^ n ∸ 1)))
  {{positive (embed-mono-< (s≤s z≤n))}}

recipPow2≡ : (n : ℕ) →
  recipPow2 n ≡ (1/_) (embed (2 ^ n)) {{nz2n n}}
recipPow2≡ n =
  reciprocal-cong (embed (suc (2 ^ n ∸ 1))) (embed (2 ^ n))
    {{nzSuc n}} {{nz2n n}}
    (embed-suc∸1 n)

recipPow2-pos : (n : ℕ) → Positive (recipPow2 n)
recipPow2-pos n =
  let e-pos : Positive (embed (2 ^ n))
      e-pos = positive (embed-mono-< (ℕP.≤-<-trans z≤n (n<2^n n)))
  in subst Positive (sym (recipPow2≡ n))
       (inv-pos (embed (2 ^ n)) {{e-pos}})

recipPow2-mul : (a b : ℕ) →
  recipPow2 (a +ℕ b) ≡ recipPow2 a * recipPow2 b
recipPow2-mul a b =
  let ea = embed (2 ^ a)
      eb = embed (2 ^ b)
      pa : Positive ea
      pa = positive (embed-mono-< (ℕP.≤-<-trans z≤n (n<2^n a)))
      pb : Positive eb
      pb = positive (embed-mono-< (ℕP.≤-<-trans z≤n (n<2^n b)))
      e0 : 2 ^ (a +ℕ b) ≡ (2 ^ a) ℕ* (2 ^ b)
      e0 = ℕP.^-distribˡ-+-* 2 a b
      e1 : embed (2 ^ (a +ℕ b)) ≡ ea * eb
      e1 =
        begin embed (2 ^ (a +ℕ b))
          ≡⟨ cong embed e0 ⟩
        embed ((2 ^ a) ℕ* (2 ^ b))
          ≡⟨ embed-*-hom (2 ^ a) (2 ^ b) ⟩
        ea * eb ∎
      nab : NonZero (ea * eb)
      nab = pos⇒nonZero (ea * eb)
              {{pos*pos⇒pos ea {{pa}} eb {{pb}}}}
      step : (1/_) (embed (2 ^ (a +ℕ b))) {{nz2n (a +ℕ b)}}
               ≡ (1/_) (ea * eb) {{nab}}
      step = reciprocal-cong (embed (2 ^ (a +ℕ b))) (ea * eb)
               {{nz2n (a +ℕ b)}} {{nab}} e1
  in begin recipPow2 (a +ℕ b)
       ≡⟨ recipPow2≡ (a +ℕ b) ⟩
     (1/_) (embed (2 ^ (a +ℕ b))) {{nz2n (a +ℕ b)}}
       ≡⟨ step ⟩
     (1/_) (ea * eb) {{nab}}
       ≡⟨ recip-*-hom ea eb {{nz2n a}} {{nz2n b}} {{nab}} ⟩
     (1/_) ea {{nz2n a}} * (1/_) eb {{nz2n b}}
       ≡⟨ cong₂ (λ p q → p * q) (sym (recipPow2≡ a)) (sym (recipPow2≡ b)) ⟩
     recipPow2 a * recipPow2 b ∎

n≤suc : (n : ℕ) → n ≤ℕ suc n
n≤suc zero = z≤n
n≤suc (suc n) = s≤s (n≤suc n)

recipPow2-n≤1 : (n : ℕ) → recipPow2 n ≤ 1ℚ
recipPow2-n≤1 n =
  let e = embed (2 ^ n)
      0e : 0ℚ < e
      0e = embed-mono-< (ℕP.≤-<-trans z≤n (n<2^n n))
      1≤e : 1ℚ ≤ e
      1≤e = embed-mono-≤ (1≤2^n n)
      q : (1/_) e {{nz2n n}} ≤ 1ℚ
      q = 1≤⇒inv≤1 {{nz2n n}} 0e 1≤e
  in subst (λ z → z ≤ 1ℚ) (sym (recipPow2≡ n)) q

recipPow2-≤ : (n : ℕ) → recipPow2 (n +ℕ n) ≤ recipPow2 n
recipPow2-≤ n =
  let r = recipPow2 n
      0≤r = 0≤recipPow2 n
      e : recipPow2 (n +ℕ n) ≡ r * r
      e = recipPow2-mul n n
      s : r * r ≤ r
      s = subst (λ z → r * r ≤ z) (*-identityʳ r)
            (*-monoˡ-≤-nonNeg r {{nonNegative 0≤r}} (recipPow2-n≤1 n))
  in ≤-trans (≤-reflexive e) s

------------------------------------------------------------------------
-- Tail bound and absolute-error composition
--
-- 衰减收尾界与绝对值误差合并

frac-< : (d e : ℚ) (0<d : 0ℚ < d) {e-pos : Positive e} (C : ℚ)
  → C < d * e
  → C * (1/_) e {{pos⇒nonZero e {{e-pos}}}} < d
frac-< d e 0<d {e-pos} C h =
  let ie = (1/_) e {{pos⇒nonZero e {{e-pos}}}}
      ie-pos : Positive ie
      ie-pos = inv-pos e {{e-pos}}
      ie·de≡d : ie * (d * e) ≡ d
      ie·de≡d =
        begin ie * (d * e)
          ≡⟨ sym (*-assoc ie d e) ⟩ (ie * d) * e
          ≡⟨ cong (_* e) (*-comm ie d) ⟩ (d * ie) * e
          ≡⟨ *-assoc d ie e ⟩ d * (ie * e)
          ≡⟨ cong (d *_) (*-inverseˡ e {{pos⇒nonZero e {{e-pos}}}}) ⟩
          d * 1ℚ ≡⟨ *-identityʳ d ⟩ d ∎
      ie·C< : ie * C < d
      ie·C< = subst (λ z → ie * C < z) ie·de≡d
                (*-monoʳ-<-pos ie {{ie-pos}} h)
  in subst (λ z → z < d) (sym (*-comm C ie)) ie·C<

tail-bound : (C : ℚ) → 0ℚ ≤ C → (d : ℚ) → 0ℚ < d →
  Σ ℕ (λ N → ∀ n → N ≤ℕ n → C * recipPow2 n < d)
tail-bound C 0≤C d 0<d =
  let d-nz = pos⇒nonZero d {{positive 0<d}}
      id = (1/_) d ⦃ d-nz ⦄
      id-pos : Positive id
      id-pos = inv-pos d {{positive 0<d}}
      q = C * id
      0≤q : 0ℚ ≤ q
      0≤q = subst (λ z → z ≤ q) (*-zeroˡ id)
              (*-monoʳ-≤-nonNeg id {{pos⇒nonNeg id {{id-pos}}}} 0≤C)
      K = proj₁ (bound-w q 0≤q)
      q≤K = proj₂ (bound-w q 0≤q)
      proof : ∀ n → K ≤ℕ n → C * recipPow2 n < d
      proof n K≤n =
        let K<2n : K Data.Nat.< 2 ^ n
            K<2n = ℕP.<-≤-trans (n<2^n K) (^-monoʳ-≤ 2 K≤n)
            e = embed (2 ^ n)
            e-pos : Positive e
            e-pos = positive (embed-mono-< (ℕP.≤-<-trans z≤n K<2n))
            dq≡C : d * q ≡ C
            dq≡C =
              begin d * (C * id) ≡⟨ sym (*-assoc d C id) ⟩ (d * C) * id
                ≡⟨ cong (_* id) (*-comm d C) ⟩ (C * d) * id
                ≡⟨ *-assoc C d id ⟩ C * (d * id)
                ≡⟨ cong (C *_) (*-inverseʳ d {{d-nz}}) ⟩ C * 1ℚ
                ≡⟨ *-identityʳ C ⟩ C ∎
            d·e>C : C < d * e
            d·e>C =
              let d-nn : NonNegative d
                  d-nn = pos⇒nonNeg d {{positive 0<d}}
              in subst (λ z → z < d * e) dq≡C
                   (≤-<-trans (*-monoˡ-≤-nonNeg d {{d-nn}} q≤K)
                              (*-monoʳ-<-pos d {{positive 0<d}}
                                (embed-mono-< K<2n)))
        in subst (λ z → C * z < d) (sym (recipPow2≡ n))
             (frac-< d e 0<d {e-pos} C d·e>C)
  in K , proof

add-right : {a b k l : ℚ} → ∣ a ∣ ≤ k → ∣ b ∣ ≤ l → ∣ a + b ∣ ≤ k + l
add-right {a} {b} {k} {l} pa pb =
  ≤-trans (∣p+q∣≤∣p∣+∣q∣ a b) (+-mono-≤ pa pb)
