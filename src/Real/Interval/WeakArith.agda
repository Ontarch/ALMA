------------------------------------------------------------------------
-- Rational arithmetic helpers for weak completeness
--
-- 弱完备性所需的有理数算术辅助
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module Real.Interval.WeakArith where

open import Data.Nat using (ℕ; zero; suc; _∸_; _^_; s≤s; z≤n)
  renaming (_≤_ to _≤N_; _≥_ to _≥N_; _+_ to _+ℕ_; _*_ to _*ℕ_; _<_ to _<N_)
open import Data.Nat.Properties using
  (m≤m+n; m≤n+m; m+[n∸m]≡n; n≤1+n; +-suc; *-suc; *-monoʳ-≤; *-distribˡ-+)
  renaming (≤-trans to ≤N-trans; ≤-refl to ≤N-refl; ≤-reflexive to ≤N-reflexive
  ; +-comm to +-commℕ; +-assoc to +-assocℕ; *-assoc to *-assocℕ
  ; *-comm to *-commℕ; *-identityʳ to *-identityʳℕ)
open import Data.Rational using
  (ℚ; 0ℚ; 1ℚ; _+_; _-_; _*_; _<_; _≤_; positive; Positive; NonZero; NonNegative)
open import Data.Rational.Base using (1/_; *<*; -_)
open import Data.Integer using (+<+)
open import Data.Rational.Properties using
  (≤-refl; ≤-reflexive; ≤-trans; ≤-<-trans; <-≤-trans; +-mono-<; +-mono-≤-<
  ; +-identityʳ; +-identityˡ; +-assoc; +-inverseˡ; neg-distrib-+; pos⇒nonNeg
  ; pos⇒nonZero; pos*pos⇒pos; *-inverseʳ; *-inverseˡ; *-assoc; *-comm
  ; *-identityˡ; *-identityʳ; <⇒≤; *-distribʳ-+; +-comm; *-cancelˡ-<-nonNeg)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; cong; cong₂; sym; trans; subst; module ≡-Reasoning)
open ≡-Reasoning

open import Real using
  (ε; embed; embed-suc-nonZero; 2ℚ; 2*embed; halve; 0<embed; reciprocal-cong
  ; 1/embed; embed-mono-<; embed-mono-≤; embed-+-hom; embed-*)

------------------------------------------------------------------------
-- Half and its NonZero proof
--
-- 二分之一及其非零证明

embed2-nonZero : NonZero (embed 2)
embed2-nonZero = embed-suc-nonZero {1}

half : ℚ
half = (1/ embed 2) {{embed2-nonZero}}

------------------------------------------------------------------------
-- Strict reciprocal antitonicity
--
-- 严格倒数反单调

strict-recip : (a b : ℚ) → (0<a : 0ℚ < a) → (a<b : a < b) →
  1/_ b {{pos⇒nonZero b {{positive (<-≤-trans 0<a (<⇒≤ a<b))}}}}
  < 1/_ a {{pos⇒nonZero a {{positive 0<a}}}}
strict-recip a b 0<a a<b =
  *-cancelˡ-<-nonNeg (a * b) {{ab-nn}}
    (<-≤-trans (≤-<-trans lhs a<b) rhs)
  where
  0<b = <-≤-trans 0<a (<⇒≤ a<b)
  a-nz = pos⇒nonZero a {{positive 0<a}}
  b-nz = pos⇒nonZero b {{positive 0<b}}
  ab-pos : Positive (a * b)
  ab-pos = pos*pos⇒pos a {{positive 0<a}} b {{positive 0<b}}
  ab-nn : NonNegative (a * b)
  ab-nn = pos⇒nonNeg (a * b) {{ab-pos}}
  lhs : (a * b) * 1/_ b {{b-nz}} ≤ a
  lhs = ≤-reflexive (begin
    (a * b) * 1/_ b {{b-nz}}
      ≡⟨ *-assoc a b _ ⟩
    a * (b * 1/_ b {{b-nz}})
      ≡⟨ cong (a *_) (*-inverseʳ b {{b-nz}}) ⟩
    a * 1ℚ
      ≡⟨ *-identityʳ a ⟩
    a
    ∎)
  rhs : b ≤ (a * b) * 1/_ a {{a-nz}}
  rhs = ≤-reflexive (begin
    b
      ≡⟨ sym (*-identityʳ b) ⟩
    b * 1ℚ
      ≡⟨ cong (b *_) (sym (*-inverseʳ a {{a-nz}})) ⟩
    b * (a * 1/_ a {{a-nz}})
      ≡⟨ sym (*-assoc b a (1/_ a {{a-nz}})) ⟩
    (b * a) * 1/_ a {{a-nz}}
      ≡⟨ cong (λ z → z * 1/_ a {{a-nz}}) (*-comm b a) ⟩
    (a * b) * 1/_ a {{a-nz}}
    ∎)

------------------------------------------------------------------------
-- Product of reciprocals and cancellation
--
-- 倒数之积与消去

1/* : ∀ p q .{{_ : NonZero p}} .{{_ : NonZero q}} .{{_ : NonZero (p * q)}} →
  (1/ p) * (1/ q) ≡ 1/ (p * q)
1/* p q =
  begin
    (1/ p) * (1/ q)
      ≡⟨ sym (*-identityʳ ((1/ p) * (1/ q))) ⟩
    ((1/ p) * (1/ q)) * 1ℚ
      ≡⟨ cong (((1/ p) * (1/ q)) *_) (sym (*-inverseʳ (p * q))) ⟩
    ((1/ p) * (1/ q)) * ((p * q) * (1/ (p * q)))
      ≡⟨ sym (*-assoc ((1/ p) * (1/ q)) (p * q) (1/ (p * q))) ⟩
    (((1/ p) * (1/ q)) * (p * q)) * (1/ (p * q))
      ≡⟨ cong (λ x → x * (1/ (p * q))) rearrange₀ ⟩
    (((1/ p) * p) * ((1/ q) * q)) * (1/ (p * q))
      ≡⟨ cong (λ x → x * (1/ (p * q)))
             (cong₂ _*_ (*-inverseˡ p) (*-inverseˡ q)) ⟩
    (1ℚ * 1ℚ) * (1/ (p * q))
      ≡⟨ *-identityˡ (1/ (p * q)) ⟩
    1/ (p * q)
      ∎
  where
  rearrange₀ : ((1/ p) * (1/ q)) * (p * q) ≡ ((1/ p) * p) * ((1/ q) * q)
  rearrange₀ =
    begin
      ((1/ p) * (1/ q)) * (p * q)
        ≡⟨ *-assoc (1/ p) (1/ q) (p * q) ⟩
      (1/ p) * ((1/ q) * (p * q))
        ≡⟨ cong ((1/ p) *_) (begin
          (1/ q) * (p * q)
            ≡⟨ sym (*-assoc (1/ q) p q) ⟩
          ((1/ q) * p) * q
            ≡⟨ cong (λ x → x * q) (*-comm (1/ q) p) ⟩
          (p * (1/ q)) * q
            ≡⟨ *-assoc p (1/ q) q ⟩
          p * ((1/ q) * q) ∎) ⟩
      (1/ p) * (p * ((1/ q) * q))
        ≡⟨ sym (*-assoc (1/ p) p ((1/ q) * q)) ⟩
      ((1/ p) * p) * ((1/ q) * q)
        ∎

cancel-* : ∀ x y .{{_ : NonZero x}} .{{_ : NonZero y}}
            .{{_ : NonZero (x * y)}} →
  x * (1/(x * y)) ≡ 1/ y
cancel-* x y =
  begin
    x * t
      ≡⟨ sym (*-identityʳ (x * t)) ⟩
    (x * t) * 1ℚ
      ≡⟨ cong ((x * t) *_) (sym (*-inverseʳ y)) ⟩
    (x * t) * (y * s)
      ≡⟨ rearrange ⟩
    ((x * y) * t) * s
      ≡⟨ cong (_* s) (*-inverseʳ (x * y)) ⟩
    1ℚ * s
      ≡⟨ *-identityˡ s ⟩
    s
      ∎
  where
  t = 1/(x * y)
  s = 1/ y
  rearrange : (x * t) * (y * s) ≡ ((x * y) * t) * s
  rearrange =
    begin
      (x * t) * (y * s)
        ≡⟨ sym (*-assoc (x * t) y s) ⟩
      ((x * t) * y) * s
        ≡⟨ cong (_* s) (begin
          (x * t) * y
            ≡⟨ *-assoc x t y ⟩
          x * (t * y)
            ≡⟨ cong (x *_) (*-comm t y) ⟩
          x * (y * t)
            ≡⟨ sym (*-assoc x y t) ⟩
          (x * y) * t
          ∎) ⟩
      ((x * y) * t) * s
      ∎

------------------------------------------------------------------------
-- Index function h k = 2k + 1
--
-- 索引函数 h k = 2k + 1

h : ℕ → ℕ
h zero    = 1
h (suc k) = suc (suc (h k))

h≥1 : ∀ a → 1 ≤N h a
h≥1 zero    = s≤s z≤n
h≥1 (suc a) = s≤s z≤n

h-mono : (k a : ℕ) → k ≤N a → h k ≤N h a
h-mono .zero a z≤n = h≥1 a
h-mono .(suc k) .(suc a) (s≤s {m = k} {n = a} le) =
  s≤s (s≤s (h-mono k a le))

h≡suc2c : ∀ c → h c ≡ suc (2 *ℕ c)
h≡suc2c zero    = refl
h≡suc2c (suc c) =
  begin
    h (suc c)
      ≡⟨⟩
    suc (suc (h c))
      ≡⟨ cong (λ x → suc (suc x)) (h≡suc2c c) ⟩
    suc (suc (suc (2 *ℕ c)))
      ≡⟨ cong suc (sym (*-suc 2 c)) ⟩
    suc (2 *ℕ suc c)
      ∎

h≥2k : ∀ k → 2 *ℕ k ≤N h k
h≥2k zero    = z≤n
h≥2k (suc k) =
  subst (λ x → x ≤N 2 +ℕ h k) (sym (*-suc 2 k))
        (s≤s (s≤s (h≥2k k)))

------------------------------------------------------------------------
-- Index function h+1 k = 2k + 2
--
-- 索引函数 h+1 k = 2k + 2

h+1 : ℕ → ℕ
h+1 zero    = 2
h+1 (suc k) = suc (suc (h+1 k))

h+1≡suc : ∀ k → h+1 k ≡ suc (h k)
h+1≡suc zero    = refl
h+1≡suc (suc k) = cong (λ x → suc (suc x)) (h+1≡suc k)

h+1≥2 : ∀ a → 2 ≤N h+1 a
h+1≥2 zero    = s≤s (s≤s z≤n)
h+1≥2 (suc a) = s≤s (s≤s z≤n)

h+1-mono : (k a : ℕ) → k ≤N a → h+1 k ≤N h+1 a
h+1-mono .zero a z≤n = h+1≥2 a
h+1-mono .(suc k) .(suc a) (s≤s {m = k} {n = a} le) =
  s≤s (s≤s (h+1-mono k a le))

s1nat : ∀ k a → k ≤N a → h+1 k ≤N suc (h a)
s1nat k a le =
  subst (λ x → h+1 k ≤N x) (h+1≡suc a) (h+1-mono k a le)

------------------------------------------------------------------------
-- Index functions 2ss and s2idx
--
-- 索引函数 2ss 与 s2idx

2ss : ℕ → ℕ
2ss zero    = 4
2ss (suc k) = suc (suc (2ss k))

s2idx : ℕ → ℕ
s2idx c = 2ss (h c)

s2idx-suc : ∀ c → s2idx (suc c) ≡ suc (suc (suc (suc (s2idx c))))
s2idx-suc c = refl

h+1<s2idx : ∀ c → h+1 c <N s2idx c
h+1<s2idx zero    = s≤s (s≤s (s≤s z≤n))
h+1<s2idx (suc c) =
  ≤N-trans (s≤s (s≤s (h+1<s2idx c)))
           (let X = suc (suc (s2idx c))
            in ≤N-trans (n≤1+n X) (n≤1+n (suc X)))

s2nat : ∀ k c → k ≤N c → h+1 k <N s2idx c
s2nat k c le =
  ≤N-trans (s≤s (h+1-mono k c le)) (h+1<s2idx c)

------------------------------------------------------------------------
-- Reciprocal antitonicity for natural-number embed
--
-- 自然数嵌入的倒数反单调

recip-antitone : ∀ a b → (0ℚ < embed a) → a <N b →
  .{{_ : NonZero (embed a)}} .{{_ : NonZero (embed b)}} →
  1/ embed b < 1/ embed a
recip-antitone a b 0<a a<b =
  strict-recip (embed a) (embed b) 0<a (embed-mono-< a<b)

pos-+ : ∀ d a → 0ℚ < embed a → 0ℚ < embed (d +ℕ a)
pos-+ d a 0<a =
  <-≤-trans 0<a (embed-mono-≤ (m≤n+m a d))

recip-step : ∀ d a → 0ℚ < embed a →
  .{{_ : NonZero (embed a)}} .{{_ : NonZero (embed (d +ℕ a))}} →
  1/ embed (d +ℕ a) ≤ 1/ embed a
recip-step zero    a 0<a = ≤-refl
recip-step (suc d) a 0<a {{nz-a}} {{nz-da}} =
  let i = d +ℕ a
      pi : 0ℚ < embed i
      pi = pos-+ d a 0<a
      nz-i : NonZero (embed i)
      nz-i = pos⇒nonZero (embed i) {{positive pi}}
      nz-si : NonZero (embed (suc i))
      nz-si = pos⇒nonZero (embed (suc i)) {{positive (0<embed i)}}
      strict = recip-antitone i (suc i) pi (s≤s ≤N-refl)
                 {{nz-i}} {{nz-si}}
      ih = recip-step d a 0<a {{nz-a}} {{nz-i}}
  in ≤-trans (<⇒≤ strict) ih

recip-antitone-≤ : ∀ a b → 0ℚ < embed a → a ≤N b →
  .{{_ : NonZero (embed a)}} .{{_ : NonZero (embed b)}} →
  1/ embed b ≤ 1/ embed a
recip-antitone-≤ a b 0<a a≤b {{nz-a}} {{nz-b}}
  rewrite sym (m+[n∸m]≡n a≤b) | +-commℕ a (b ∸ a) =
  recip-step (b ∸ a) a 0<a {{nz-a}} {{nz-b}}

------------------------------------------------------------------------
-- 2ss equations and NonZero proofs
--
-- 2ss 等式与非零证明

2ss-eq : ∀ k → 2ss k ≡ 2 *ℕ suc (suc k)
2ss-eq zero    = refl
2ss-eq (suc k) =
  begin
    2ss (suc k)
      ≡⟨⟩
    suc (suc (2ss k))
      ≡⟨ cong (λ x → suc (suc x)) (2ss-eq k) ⟩
    suc (suc (2 *ℕ suc (suc k)))
      ≡⟨ sym (*-suc 2 (suc (suc k))) ⟩
    2 *ℕ suc (suc (suc k))
      ∎

2ss-nonZero : ∀ {k} → NonZero (embed (2ss k))
2ss-nonZero {k} =
  let p = embed (suc (suc k))
      eq : 2ℚ * p ≡ embed (2ss k)
      eq = trans (2*embed (suc (suc k)))
                 (cong embed (sym (2ss-eq k)))
      pos-2p : Positive (2ℚ * p)
      pos-2p = pos*pos⇒pos 2ℚ p
  in subst NonZero eq (pos⇒nonZero (2ℚ * p) {{pos-2p}})

εs-half : ∀ k → ε (suc k) * half ≡ (1/ embed (2ss k)) {{2ss-nonZero {k}}}
εs-half k =
  let p = embed (suc (suc k))
      eq : 2ℚ * p ≡ embed (2ss k)
      eq = trans (2*embed (suc (suc k)))
                 (cong embed (sym (2ss-eq k)))
      nz-2ℚ : NonZero 2ℚ
      nz-2ℚ = embed-suc-nonZero {1}
      nz-p : NonZero p
      nz-p = embed-suc-nonZero {suc k}
      pos-2p : Positive (2ℚ * p)
      pos-2p = pos*pos⇒pos 2ℚ p
      nz-2p : NonZero (2ℚ * p)
      nz-2p = pos⇒nonZero (2ℚ * p) {{pos-2p}}
  in
  begin
    ε (suc k) * half
      ≡⟨ *-comm ((1/ p) {{nz-p}}) half ⟩
    half * ((1/ p) {{nz-p}})
      ≡⟨ 1/* 2ℚ p {{nz-2ℚ}} {{nz-p}} {{nz-2p}} ⟩
    (1/ (2ℚ * p)) {{nz-2p}}
      ≡⟨ reciprocal-cong (2ℚ * p) (embed (2ss k))
             {{nz-2p}} {{2ss-nonZero {k}}} eq ⟩
    (1/ embed (2ss k)) {{2ss-nonZero {k}}}
      ∎

------------------------------------------------------------------------
-- h+1 equations and NonZero proof
--
-- h+1 等式与非零证明

h+1-eq : ∀ k → h+1 k ≡ 2 *ℕ suc k
h+1-eq zero    = refl
h+1-eq (suc k) =
  begin
    h+1 (suc k)
      ≡⟨⟩
    suc (suc (h+1 k))
      ≡⟨ cong (λ x → suc (suc x)) (h+1-eq k) ⟩
    suc (suc (2 *ℕ suc k))
      ≡⟨ sym (*-suc 2 (suc k)) ⟩
    2 *ℕ suc (suc k)
      ∎

h+1-nonZero : ∀ {k} → NonZero (embed (h+1 k))
h+1-nonZero {k} =
  let p = embed (suc k)
      eq : 2ℚ * p ≡ embed (h+1 k)
      eq = trans (2*embed (suc k))
                 (cong embed (sym (h+1-eq k)))
      pos-2p : Positive (2ℚ * p)
      pos-2p = pos*pos⇒pos 2ℚ p
  in subst NonZero eq (pos⇒nonZero (2ℚ * p) {{pos-2p}})

------------------------------------------------------------------------
-- 2ss of 2a
--
-- 2a 的 2ss

2*2a≡4a : ∀ a → 2 *ℕ (2 *ℕ a) ≡ 4 *ℕ a
2*2a≡4a a =
  begin
    2 *ℕ (2 *ℕ a)
      ≡⟨ sym (*-assocℕ 2 2 a) ⟩
    (2 *ℕ 2) *ℕ a
      ≡⟨⟩
    4 *ℕ a
      ∎

2ss2a≡4a : ∀ a → 2ss (2 *ℕ a) ≡ 4 *ℕ suc a
2ss2a≡4a a =
  begin
    2ss (2 *ℕ a)
      ≡⟨ 2ss-eq (2 *ℕ a) ⟩
    2 *ℕ suc (suc (2 *ℕ a))
      ≡⟨ *-suc 2 (suc (2 *ℕ a)) ⟩
    2 +ℕ 2 *ℕ suc (2 *ℕ a)
      ≡⟨ cong (2 +ℕ_) (*-suc 2 (2 *ℕ a)) ⟩
    2 +ℕ (2 +ℕ 2 *ℕ (2 *ℕ a))
      ≡⟨ cong (λ x → 2 +ℕ (2 +ℕ x)) (2*2a≡4a a) ⟩
    2 +ℕ (2 +ℕ 4 *ℕ a)
      ≡⟨ +-assocℕ 2 2 (4 *ℕ a) ⟩
    (2 +ℕ 2) +ℕ 4 *ℕ a
      ≡⟨⟩
    4 +ℕ 4 *ℕ a
      ≡⟨ sym (*-suc 4 a) ⟩
    4 *ℕ suc a
      ∎

------------------------------------------------------------------------
-- h+1 lower bounds
--
-- h+1 下界

h+1≥2*suc-refl : ∀ a → h+1 a ≥N 2 *ℕ suc a
h+1≥2*suc-refl a = ≤N-reflexive (sym (h+1-eq a))

h+1≥2*suc : ∀ a k → a ≥N k → h+1 a ≥N 2 *ℕ suc k
h+1≥2*suc a k a≥k =
  ≤N-trans (*-monoʳ-≤ 2 (s≤s a≥k)) (h+1≥2*suc-refl a)

------------------------------------------------------------------------
-- Double reciprocal
--
-- 双倒数

double-recip : ∀ k →
  (1/ embed (h+1 k)) {{h+1-nonZero {k}}}
    + (1/ embed (h+1 k)) {{h+1-nonZero {k}}} ≡ ε k
double-recip k =
  let nz-p : NonZero (embed (suc k))
      nz-p = embed-suc-nonZero {k}
      pos-2p : Positive (2ℚ * embed (suc k))
      pos-2p = pos*pos⇒pos 2ℚ (embed (suc k))
      nz-2p : NonZero (2ℚ * embed (suc k))
      nz-2p = pos⇒nonZero (2ℚ * embed (suc k)) {{pos-2p}}
      rc : (1/ embed (h+1 k)) {{h+1-nonZero {k}}}
         ≡ (1/ (2ℚ * embed (suc k))) {{nz-2p}}
      rc = reciprocal-cong (embed (h+1 k)) (2ℚ * embed (suc k))
             {{h+1-nonZero {k}}} {{nz-2p}}
             (trans (cong embed (h+1-eq k))
                    (sym (2*embed (suc k))))
  in
  begin
    (1/ embed (h+1 k)) {{h+1-nonZero {k}}}
      + (1/ embed (h+1 k)) {{h+1-nonZero {k}}}
      ≡⟨ cong₂ _+_ rc rc ⟩
    (1/ (2ℚ * embed (suc k))) {{nz-2p}}
      + (1/ (2ℚ * embed (suc k))) {{nz-2p}}
      ≡⟨ halve (embed (suc k)) {{nz-p}} {{nz-2p}} ⟩
    (1/ embed (suc k)) {{nz-p}}
      ≡⟨ 1/embed k ⟩
    ε k
      ∎

------------------------------------------------------------------------
-- 4·embed
--
-- 4·embed

4*embed : ∀ n → 2ℚ * (2ℚ * embed n) ≡ embed (4 *ℕ n)
4*embed n =
  begin
    2ℚ * (2ℚ * embed n)
      ≡⟨ cong (λ x → 2ℚ * x) (2*embed n) ⟩
    2ℚ * embed (2 *ℕ n)
      ≡⟨ 2*embed (2 *ℕ n) ⟩
    embed (2 *ℕ (2 *ℕ n))
      ≡⟨ cong embed (2*2n≡4n n) ⟩
    embed (4 *ℕ n)
      ∎
  where
  2*2n≡4n : ∀ n → 2 *ℕ (2 *ℕ n) ≡ 4 *ℕ n
  2*2n≡4n n =
    begin
      2 *ℕ (2 *ℕ n)
        ≡⟨ sym (*-assocℕ 2 2 n) ⟩
      (2 *ℕ 2) *ℕ n
        ≡⟨ cong (λ x → x *ℕ n) 2*2≡4 ⟩
      4 *ℕ n
        ∎
    where
    2*2≡4 : 2 *ℕ 2 ≡ 4
    2*2≡4 = refl

------------------------------------------------------------------------
-- Negation and difference helpers
--
-- 取负与差助手

neg-neg : ∀ p → - (- p) ≡ p
neg-neg p =
  begin
    - (- p)
      ≡⟨ sym (+-identityʳ (- (- p))) ⟩
    - (- p) + 0ℚ
      ≡⟨ cong (λ x → - (- p) + x) (sym (+-inverseˡ p)) ⟩
    - (- p) + (- p + p)
      ≡⟨ sym (+-assoc (- (- p)) (- p) p) ⟩
    (- (- p) + - p) + p
      ≡⟨ cong (λ x → x + p) (+-inverseˡ (- p)) ⟩
    0ℚ + p
      ≡⟨ +-identityˡ p ⟩
    p
      ∎

diff-neg : ∀ x y → - (x - y) ≡ y - x
diff-neg x y =
  begin
    - (x - y)
      ≡⟨ neg-distrib-+ x (- y) ⟩
    - x + - (- y)
      ≡⟨ cong (λ z → - x + z) (neg-neg y) ⟩
    - x + y
      ≡⟨ +-comm (- x) y ⟩
    y + - x
      ∎

------------------------------------------------------------------------
-- Basic rational inequalities
--
-- 基本有理数不等式

double : ∀ u → 2ℚ * u ≡ u + u
double u =
  begin
    2ℚ * u
      ≡⟨ *-distribʳ-+ u 1ℚ 1ℚ ⟩
    1ℚ * u + 1ℚ * u
      ≡⟨ cong₂ _+_ (*-identityˡ u) (*-identityˡ u) ⟩
    u + u
      ∎

x<2x : ∀ x → 0ℚ < x → x < 2ℚ * x
x<2x x 0<x =
  subst (λ y → x < y) (sym (double x))
    (subst (λ z → z < x + x) idstep
      (+-mono-≤-< (≤-refl {x = x}) 0<x))
  where
  idstep : x + 0ℚ ≡ x
  idstep = +-identityʳ x

x<x+1 : ∀ x → x < x + 1ℚ
x<x+1 x =
  subst (λ z → z < x + 1ℚ) idstep
    (+-mono-≤-< (≤-refl {x = x}) 0<1)
  where
  idstep : x + 0ℚ ≡ x
  idstep = +-identityʳ x
  0<1 : 0ℚ < 1ℚ
  0<1 = *<* (+<+ (s≤s z≤n))

------------------------------------------------------------------------
-- Generic bound for a positive rational u
--
-- 任意正有理数 u 的通用界

u-bound : ∀ u → 0ℚ < u →
  {{_ : NonZero u}} →
  {{_ : NonZero (2ℚ * u)}} →
  {{_ : NonZero (2ℚ * (2ℚ * u))}} →
  {{_ : NonZero (2ℚ * u + 1ℚ)}} →
  1/ (2ℚ * (2ℚ * u)) + 1/ (2ℚ * u + 1ℚ) < 1/ u
u-bound u 0<u {{nz-u}} {{nz-2u}} {{nz-4u}} {{nz-nx}} =
  let two-u = 2ℚ * u
      four-u = 2ℚ * two-u
      next = two-u + 1ℚ
      0<two-u : 0ℚ < two-u
      0<two-u = subst (λ x → 0ℚ < x) (sym (double u))
                      (+-mono-< 0<u 0<u)
      two-u<next : two-u < next
      two-u<next = x<x+1 two-u
      two-u<four-u : two-u < four-u
      two-u<four-u = x<2x two-u 0<two-u
      h1 : (1/ next) {{nz-nx}} < (1/ two-u) {{nz-2u}}
      h1 = strict-recip two-u next 0<two-u two-u<next
      h2 : (1/ four-u) {{nz-4u}} < (1/ two-u) {{nz-2u}}
      h2 = strict-recip two-u four-u 0<two-u two-u<four-u
  in subst (λ x → (1/ four-u) {{nz-4u}} + (1/ next) {{nz-nx}} < x)
           (halve u {{nz-u}} {{nz-2u}})
           (+-mono-< h2 h1)

------------------------------------------------------------------------
-- Base bound
--
-- 基础界

1+n≡ : ∀ n → 1 +ℕ n ≡ suc n
1+n≡ n = refl

base-bound : ∀ k →
  1/ embed (4 *ℕ suc k) + 1/ embed (suc (2 *ℕ suc k)) < ε k
base-bound k =
  let u = embed (suc k)
      e2u : 2ℚ * u ≡ embed (2 *ℕ suc k)
      e2u = 2*embed (suc k)
      e4u : 2ℚ * (2ℚ * u) ≡ embed (4 *ℕ suc k)
      e4u = 4*embed (suc k)
      enx : 2ℚ * u + 1ℚ ≡ embed (suc (2 *ℕ suc k))
      enx =
        begin
          2ℚ * u + 1ℚ
            ≡⟨ cong (λ x → x + 1ℚ) e2u ⟩
          embed (2 *ℕ suc k) + 1ℚ
            ≡⟨ +-comm (embed (2 *ℕ suc k)) 1ℚ ⟩
          1ℚ + embed (2 *ℕ suc k)
            ≡⟨ sym (embed-+-hom 1 (2 *ℕ suc k)) ⟩
          embed (1 +ℕ 2 *ℕ suc k)
            ≡⟨ cong embed (1+n≡ (2 *ℕ suc k)) ⟩
          embed (suc (2 *ℕ suc k))
            ∎
  in go u (0<embed k) refl e2u e4u enx
  where
  E4 = embed (4 *ℕ suc k)
  Enx = embed (suc (2 *ℕ suc k))
  go : (u : ℚ) → 0ℚ < u
     → u ≡ embed (suc k)
     → 2ℚ * u ≡ embed (2 *ℕ suc k)
     → 2ℚ * (2ℚ * u) ≡ embed (4 *ℕ suc k)
     → 2ℚ * u + 1ℚ ≡ embed (suc (2 *ℕ suc k))
     → 1/ E4 + 1/ Enx < ε k
  go u 0<u u≡ e2u e4u enx =
    let two-u = 2ℚ * u
        four-u = 2ℚ * two-u
        next = two-u + 1ℚ
        nz-u : NonZero u
        nz-u = pos⇒nonZero u {{positive 0<u}}
        nz-2u : NonZero two-u
        nz-2u = subst NonZero (sym e2u)
                  (embed-suc-nonZero {k +ℕ (suc k +ℕ 0)})
        nz-4u : NonZero four-u
        nz-4u = subst NonZero (sym e4u)
                  (embed-suc-nonZero
                    {k +ℕ (suc k +ℕ (suc k +ℕ (suc k +ℕ 0)))})
        nz-nx : NonZero next
        nz-nx = subst NonZero (sym enx)
                  (embed-suc-nonZero {suc (k +ℕ (suc k +ℕ 0))})
        nz-E4 : NonZero E4
        nz-E4 = embed-suc-nonZero
                  {k +ℕ (suc k +ℕ (suc k +ℕ (suc k +ℕ 0)))}
        nz-Enx : NonZero Enx
        nz-Enx = embed-suc-nonZero {suc (k +ℕ (suc k +ℕ 0))}
        a = (1/ four-u) {{nz-4u}}
        b = (1/ next) {{nz-nx}}
        c = (1/ u) {{nz-u}}
        gen : a + b < c
        gen = u-bound u 0<u {{nz-u}} {{nz-2u}} {{nz-4u}} {{nz-nx}}
        eq1 : a ≡ (1/ E4) {{nz-E4}}
        eq1 = reciprocal-cong four-u E4 {{nz-4u}} {{nz-E4}} e4u
        eq2 : b ≡ (1/ Enx) {{nz-Enx}}
        eq2 = reciprocal-cong next Enx {{nz-nx}} {{nz-Enx}} enx
        eq3 : c ≡ ε k
        eq3 = trans
                (reciprocal-cong u (embed (suc k))
                  {{nz-u}} {{embed-suc-nonZero {k}}} u≡)
                (1/embed k)
        s1 = subst (λ x → x + b < c) eq1 gen
        s2 = subst (λ x → (1/ E4) {{nz-E4}} + x < c) eq2 s1
        s3 = subst (λ x → (1/ E4) {{nz-E4}} + (1/ Enx) {{nz-Enx}} < x)
                   eq3 s2
    in s3

------------------------------------------------------------------------
-- Natural-number doubling and bounds
--
-- 自然数加倍与界

doubleN : ∀ x → 2 *ℕ x ≡ x +ℕ x
doubleN x =
  begin
    2 *ℕ x
      ≡⟨ *-commℕ 2 x ⟩
    x *ℕ 2
      ≡⟨ *-suc x 1 ⟩
    x +ℕ x *ℕ 1
      ≡⟨ cong (x +ℕ_) (*-identityʳℕ x) ⟩
    x +ℕ x
      ∎

k+4≤2k+4 : ∀ k →
  suc (suc (suc (suc k))) ≤N 2 *ℕ suc (suc k)
k+4≤2k+4 k =
  ≤N-trans mid (≤N-reflexive (sym a≡))
  where
  mid : suc (suc (suc (suc k))) ≤N
        suc (suc (suc (suc (k +ℕ k))))
  mid = s≤s (s≤s (s≤s (s≤s (m≤m+n k k))))
  inner : k +ℕ suc (suc k) ≡ suc (suc (k +ℕ k))
  inner = trans (+-suc k (suc k)) (cong suc (+-suc k k))
  a≡ : 2 *ℕ suc (suc k) ≡
       suc (suc (suc (suc (k +ℕ k))))
  a≡ =
    begin
      2 *ℕ suc (suc k)
        ≡⟨ doubleN (suc (suc k)) ⟩
      suc (suc k) +ℕ suc (suc k)
        ≡⟨ refl ⟩
      suc (suc (k +ℕ suc (suc k)))
        ≡⟨ cong (λ x → suc (suc x)) inner ⟩
      suc (suc (suc (suc (k +ℕ k))))
        ∎

prod≤2^ : ∀ k →
  suc (suc k) *ℕ suc (suc (suc k)) ≤N 2 ^ suc (suc (suc k))
prod≤2^ zero =
  s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))
prod≤2^ (suc k) =
  ≤N-trans (≤N-trans p1 (≤N-reflexive step1)) p3
  where
  a = suc (suc k)
  b = suc a
  c = suc b
  c≤2a : c ≤N 2 *ℕ a
  c≤2a = k+4≤2k+4 k
  p1 : b *ℕ c ≤N b *ℕ (2 *ℕ a)
  p1 = *-monoʳ-≤ b c≤2a
  p3 : 2 *ℕ (a *ℕ b) ≤N 2 *ℕ (2 ^ b)
  p3 = *-monoʳ-≤ 2 (prod≤2^ k)
  step1 : b *ℕ (2 *ℕ a) ≡ 2 *ℕ (a *ℕ b)
  step1 =
    begin
      b *ℕ (2 *ℕ a)
        ≡⟨ cong (b *ℕ_) (doubleN a) ⟩
      b *ℕ (a +ℕ a)
        ≡⟨ *-distribˡ-+ b a a ⟩
      b *ℕ a +ℕ b *ℕ a
        ≡⟨ cong (λ x → x +ℕ b *ℕ a) (*-commℕ b a) ⟩
      a *ℕ b +ℕ b *ℕ a
        ≡⟨ cong (a *ℕ b +ℕ_) (*-commℕ b a) ⟩
      a *ℕ b +ℕ a *ℕ b
        ≡⟨ sym (doubleN (a *ℕ b)) ⟩
      2 *ℕ (a *ℕ b)
        ∎

embed-prod< : ∀ a b c → a *ℕ b <N c → embed a * embed b < embed c
embed-prod< a b c ab<c =
  ≤-<-trans (≤-reflexive (embed-* a b))
            (embed-mono-< {m = a *ℕ b} {n = c} ab<c)
