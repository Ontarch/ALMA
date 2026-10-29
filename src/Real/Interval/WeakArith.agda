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
  ; +-comm to +-commℕ; +-assoc to +-assocℕ; *-assoc to *-assocℕ; *-comm to *-commℕ
  ; +-identityʳ to +-identityʳℕ; *-identityʳ to *-identityʳℕ; *-identityˡ to *-identityˡℕ
  ; +-mono-< to +-mono-<N; ≤-<-trans to ≤N-<-trans)
open import Data.Rational using
  (ℚ; 0ℚ; 1ℚ; _+_; _-_; _*_; _<_; _≤_; positive; Positive; NonZero)
open import Data.Rational.Base using (1/_; -_)
open import Data.Rational.Properties using
  (≤-refl; ≤-reflexive; ≤-trans; ≤-<-trans; <-≤-trans; +-mono-<; +-mono-≤-<
  ; +-identityʳ; neg-distrib-+; pos⇒nonZero; pos*pos⇒pos; *-inverseʳ; +-comm
  ; *-inverseˡ; *-assoc; *-comm; *-identityˡ; *-identityʳ; <⇒≤; *-distribʳ-+)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; cong; cong₂; sym; trans; subst; module ≡-Reasoning)
open ≡-Reasoning

open import Base.RationalRing using (0<1; neg-involutive)
open import Real using
  (ε; embed; half; embed-suc-nonZero; 2ℚ; 2*embed; halve; embed-*; 0<embed
  ; reciprocal-cong; 1/embed; embed-mono-<; embed-mono-≤; embed-+-hom)
open import Real.IntervalEquiv using (recipPow2; n<2^n; 1≤2^n)
open import Real.Interval.Kit using (strict-recip)

------------------------------------------------------------------------
-- Product of reciprocals and cancellation
--
-- 倒数之积与消去

1/*-inner : ∀ p q .{{_ : NonZero p}} .{{_ : NonZero q}} →
  (1/ q) * (p * q) ≡ p * ((1/ q) * q)
1/*-inner p q =
  begin
    (1/ q) * (p * q)
      ≡⟨ sym (*-assoc (1/ q) p q) ⟩
    ((1/ q) * p) * q
      ≡⟨ cong (λ x → x * q) (*-comm (1/ q) p) ⟩
    (p * (1/ q)) * q
      ≡⟨ *-assoc p (1/ q) q ⟩
    p * ((1/ q) * q)
      ∎

1/*-rearrange : ∀ p q .{{_ : NonZero p}} .{{_ : NonZero q}} →
  ((1/ p) * (1/ q)) * (p * q) ≡ ((1/ p) * p) * ((1/ q) * q)
1/*-rearrange p q =
  begin
    ((1/ p) * (1/ q)) * (p * q)
      ≡⟨ *-assoc (1/ p) (1/ q) (p * q) ⟩
    (1/ p) * ((1/ q) * (p * q))
      ≡⟨ cong ((1/ p) *_) (1/*-inner p q) ⟩
    (1/ p) * (p * ((1/ q) * q))
      ≡⟨ sym (*-assoc (1/ p) p ((1/ q) * q)) ⟩
    ((1/ p) * p) * ((1/ q) * q)
      ∎

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
      ≡⟨ cong (λ x → x * (1/ (p * q))) (1/*-rearrange p q) ⟩
    (((1/ p) * p) * ((1/ q) * q)) * (1/ (p * q))
      ≡⟨ cong (λ x → x * (1/ (p * q)))
             (cong₂ _*_ (*-inverseˡ p) (*-inverseˡ q)) ⟩
    (1ℚ * 1ℚ) * (1/ (p * q))
      ≡⟨ *-identityˡ (1/ (p * q)) ⟩
    1/ (p * q)
      ∎

cancel-*-inner : ∀ x y .{{_ : NonZero (x * y)}} →
  (x * (1/(x * y))) * y ≡ (x * y) * (1/(x * y))
cancel-*-inner x y =
  begin
    (x * (1/(x * y))) * y
      ≡⟨ *-assoc x (1/(x * y)) y ⟩
    x * ((1/(x * y)) * y)
      ≡⟨ cong (x *_) (*-comm (1/(x * y)) y) ⟩
    x * (y * (1/(x * y)))
      ≡⟨ sym (*-assoc x y (1/(x * y))) ⟩
    (x * y) * (1/(x * y))
      ∎

cancel-*-rearrange : ∀ x y .{{_ : NonZero x}} .{{_ : NonZero y}}
                     .{{_ : NonZero (x * y)}} →
  (x * (1/(x * y))) * (y * (1/ y))
    ≡ ((x * y) * (1/(x * y))) * (1/ y)
cancel-*-rearrange x y =
  begin
    (x * (1/(x * y))) * (y * (1/ y))
      ≡⟨ sym (*-assoc (x * (1/(x * y))) y (1/ y)) ⟩
    ((x * (1/(x * y))) * y) * (1/ y)
      ≡⟨ cong (_* (1/ y)) (cancel-*-inner x y) ⟩
    ((x * y) * (1/(x * y))) * (1/ y)
      ∎

cancel-* : ∀ x y .{{_ : NonZero x}} .{{_ : NonZero y}}
            .{{_ : NonZero (x * y)}} →
  x * (1/(x * y)) ≡ 1/ y
cancel-* x y =
  begin
    x * (1/(x * y))
      ≡⟨ sym (*-identityʳ (x * (1/(x * y)))) ⟩
    (x * (1/(x * y))) * 1ℚ
      ≡⟨ cong ((x * (1/(x * y))) *_) (sym (*-inverseʳ y)) ⟩
    (x * (1/(x * y))) * (y * (1/ y))
      ≡⟨ cancel-*-rearrange x y ⟩
    ((x * y) * (1/(x * y))) * (1/ y)
      ≡⟨ cong (_* (1/ y)) (*-inverseʳ (x * y)) ⟩
    1ℚ * (1/ y)
      ≡⟨ *-identityˡ (1/ y) ⟩
    1/ y
      ∎

------------------------------------------------------------------------
-- Index function h k = 2k + 1
--
-- 索引函数 h

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
-- 索引函数 h+1

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
  let
    i = d +ℕ a
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
recip-antitone-≤ a b 0<a a≤b {{nz-a}} {{nz-b}} =
  ≤-trans (≤-reflexive cong-recip)
          (recip-step d a 0<a {{nz-a}} {{nz-da}})
  where
  d : ℕ
  d = b ∸ a
  0<b : 0ℚ < embed b
  0<b = <-≤-trans 0<a (embed-mono-≤ a≤b)
  nz-b' : NonZero (embed b)
  nz-b' = pos⇒nonZero (embed b) {{positive 0<b}}
  eq1 : a +ℕ d ≡ b
  eq1 = m+[n∸m]≡n a≤b
  eq2 : d +ℕ a ≡ b
  eq2 = trans (+-commℕ d a) eq1
  nz-da : NonZero (embed (d +ℕ a))
  nz-da = subst (λ z → NonZero (embed z)) (sym eq2) nz-b'
  cong-recip : (1/ embed b) {{nz-b'}} ≡ (1/ embed (d +ℕ a)) {{nz-da}}
  cong-recip = reciprocal-cong (embed b) (embed (d +ℕ a))
                 {{nz-b'}} {{nz-da}} (cong embed (sym eq2))

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
  let
    p = embed (suc (suc k))
    eq : 2ℚ * p ≡ embed (2ss k)
    eq = trans (2*embed (suc (suc k)))
               (cong embed (sym (2ss-eq k)))
    pos-2p : Positive (2ℚ * p)
    pos-2p = pos*pos⇒pos 2ℚ p
  in subst NonZero eq (pos⇒nonZero (2ℚ * p) {{pos-2p}})

εs-half : ∀ k → ε (suc k) * half ≡ (1/ embed (2ss k)) {{2ss-nonZero {k}}}
εs-half k =
  let
    p = embed (suc (suc k))
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
  let
    p = embed (suc k)
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
  let
    nz-p : NonZero (embed (suc k))
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
-- Pow2 baseline
--
-- Pow2 基线

1≤2N : 1 ≤N 2
1≤2N = s≤s z≤n

suc-pow-∸1 : ∀ k → suc (2 ^ k ∸ 1) ≡ 2 ^ k
suc-pow-∸1 k = m+[n∸m]≡n (1≤2^n k)

------------------------------------------------------------------------
-- Half · recipPow2
--
-- 二分之一乘 recipPow2

hr-d : ℕ → ℕ
hr-d n = 2 ^ n ∸ 1

hr-q : ℕ → ℚ
hr-q n = embed (suc (hr-d n))

hr-eq : ∀ n → 2 *ℕ suc (hr-d n) ≡ suc (2 ^ suc n ∸ 1)
hr-eq n =
  begin
    2 *ℕ suc (hr-d n)
      ≡⟨ cong (2 *ℕ_) (suc-pow-∸1 n) ⟩
    2 *ℕ 2 ^ n
      ≡⟨⟩
    2 ^ suc n
      ≡⟨ sym (suc-pow-∸1 (suc n)) ⟩
    suc (2 ^ suc n ∸ 1)
      ∎

hr-2q-nz : ∀ n → NonZero (2ℚ * hr-q n)
hr-2q-nz n =
  pos⇒nonZero (2ℚ * hr-q n) {{pos*pos⇒pos 2ℚ (hr-q n)}}

hr-eqd-nz : ∀ n → NonZero (embed (2 *ℕ suc (hr-d n)))
hr-eqd-nz n =
  subst NonZero (2*embed (suc (hr-d n))) (hr-2q-nz n)

half*recipPow2 : ∀ n → half * recipPow2 n ≡ recipPow2 (suc n)
half*recipPow2 n =
  begin
    half * recipPow2 n
      ≡⟨ 1/* 2ℚ (hr-q n) {{_}} {{_}} {{hr-2q-nz n}} ⟩
    1/_ (2ℚ * hr-q n) {{hr-2q-nz n}}
      ≡⟨ reciprocal-cong (2ℚ * hr-q n)
                          (embed (2 *ℕ suc (hr-d n)))
                          {{hr-2q-nz n}}
                          {{hr-eqd-nz n}}
                          (2*embed (suc (hr-d n))) ⟩
    1/_ (embed (2 *ℕ suc (hr-d n))) {{hr-eqd-nz n}}
      ≡⟨ reciprocal-cong (embed (2 *ℕ suc (hr-d n)))
                          (embed (suc (2 ^ suc n ∸ 1)))
                          {{hr-eqd-nz n}}
                          {{_}}
                          (cong embed (hr-eq n)) ⟩
    1/_ (embed (suc (2 ^ suc n ∸ 1))) {{_}}
      ≡⟨⟩
    recipPow2 (suc n)
    ∎

------------------------------------------------------------------------
-- 4-fold embedding
--
-- 四倍嵌入

4*embed-2*2n≡4n : ∀ n → 2 *ℕ (2 *ℕ n) ≡ 4 *ℕ n
4*embed-2*2n≡4n n =
  begin
    2 *ℕ (2 *ℕ n)
      ≡⟨ sym (*-assocℕ 2 2 n) ⟩
    (2 *ℕ 2) *ℕ n
      ≡⟨⟩
    4 *ℕ n
      ∎

4*embed : ∀ n → 2ℚ * (2ℚ * embed n) ≡ embed (4 *ℕ n)
4*embed n =
  begin
    2ℚ * (2ℚ * embed n)
      ≡⟨ cong (λ x → 2ℚ * x) (2*embed n) ⟩
    2ℚ * embed (2 *ℕ n)
      ≡⟨ 2*embed (2 *ℕ n) ⟩
    embed (2 *ℕ (2 *ℕ n))
      ≡⟨ cong embed (4*embed-2*2n≡4n n) ⟩
    embed (4 *ℕ n)
      ∎

------------------------------------------------------------------------
-- Negation and difference helpers
--
-- 取负与差辅助引理

diff-neg : ∀ x y → - (x - y) ≡ y - x
diff-neg x y =
  begin
    - (x - y)
      ≡⟨ neg-distrib-+ x (- y) ⟩
    - x + - (- y)
      ≡⟨ cong (λ z → - x + z) (neg-involutive y) ⟩
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
    (subst (λ z → z < x + x) (+-identityʳ x)
      (+-mono-≤-< (≤-refl {x = x}) 0<x))

x<x+1 : ∀ x → x < x + 1ℚ
x<x+1 x =
  subst (λ z → z < x + 1ℚ) (+-identityʳ x)
    (+-mono-≤-< (≤-refl {x = x}) 0<1)

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
  let
    two-u = 2ℚ * u
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

base-go : ∀ k (u : ℚ) → 0ℚ < u
       → u ≡ embed (suc k)
       → 2ℚ * u ≡ embed (2 *ℕ suc k)
       → 2ℚ * (2ℚ * u) ≡ embed (4 *ℕ suc k)
       → 2ℚ * u + 1ℚ ≡ embed (suc (2 *ℕ suc k))
       → (1/ embed (4 *ℕ suc k)) + (1/ embed (suc (2 *ℕ suc k))) < ε k
base-go k u 0<u u≡ e2u e4u enx =
  let
    two-u = 2ℚ * u
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
    nz-E4 : NonZero (embed (4 *ℕ suc k))
    nz-E4 = embed-suc-nonZero
              {k +ℕ (suc k +ℕ (suc k +ℕ (suc k +ℕ 0)))}
    nz-Enx : NonZero (embed (suc (2 *ℕ suc k)))
    nz-Enx = embed-suc-nonZero {suc (k +ℕ (suc k +ℕ 0))}
    a = (1/ four-u) {{nz-4u}}
    b = (1/ next) {{nz-nx}}
    c = (1/ u) {{nz-u}}
    gen : a + b < c
    gen = u-bound u 0<u {{nz-u}} {{nz-2u}} {{nz-4u}} {{nz-nx}}
    eq1 : a ≡ (1/ embed (4 *ℕ suc k)) {{nz-E4}}
    eq1 = reciprocal-cong four-u (embed (4 *ℕ suc k))
            {{nz-4u}} {{nz-E4}} e4u
    eq2 : b ≡ (1/ embed (suc (2 *ℕ suc k))) {{nz-Enx}}
    eq2 = reciprocal-cong next (embed (suc (2 *ℕ suc k)))
            {{nz-nx}} {{nz-Enx}} enx
    eq3 : c ≡ ε k
    eq3 = trans
            (reciprocal-cong u (embed (suc k))
              {{nz-u}} {{embed-suc-nonZero {k}}} u≡)
            (1/embed k)
    s1 = subst (λ x → x + b < c) eq1 gen
    s2 = subst (λ x → (1/ embed (4 *ℕ suc k)) {{nz-E4}} + x < c) eq2 s1
    s3 = subst (λ x → (1/ embed (4 *ℕ suc k)) {{nz-E4}}
                       + (1/ embed (suc (2 *ℕ suc k))) {{nz-Enx}} < x)
               eq3 s2
  in s3

base-bound : ∀ k →
  1/ embed (4 *ℕ suc k) + 1/ embed (suc (2 *ℕ suc k)) < ε k
base-bound k =
  let
    u = embed (suc k)
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
  in base-go k u (0<embed k) refl e2u e4u enx

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
  let
    mid : suc (suc (suc (suc k))) ≤N
          suc (suc (suc (suc (k +ℕ k))))
    mid = s≤s (s≤s (s≤s (s≤s (m≤m+n k k))))
    inner : k +ℕ suc (suc k) ≡ suc (suc (k +ℕ k))
    inner = trans (+-suc k (suc k)) (cong suc (+-suc k k))
    a≡ : 2 *ℕ suc (suc k) ≡ suc (suc (suc (suc (k +ℕ k))))
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
  in ≤N-trans mid (≤N-reflexive (sym a≡))

prod≤2^ : ∀ k →
  suc (suc k) *ℕ suc (suc (suc k)) ≤N 2 ^ suc (suc (suc k))
prod≤2^ zero =
  s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))
prod≤2^ (suc k) =
  let
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
  in ≤N-trans (≤N-trans p1 (≤N-reflexive step1)) p3

embed-prod< : ∀ a b c → a *ℕ b <N c → embed a * embed b < embed c
embed-prod< a b c ab<c =
  ≤-<-trans (≤-reflexive (embed-* a b))
            (embed-mono-< {m = a *ℕ b} {n = c} ab<c)

------------------------------------------------------------------------
-- More Nat arithmetic for CauchyI → WeakCauchy
--
-- CauchyI → WeakCauchy 所需的更多自然数算术

four-a : ∀ a → 4 *ℕ a ≡ 2 *ℕ (2 *ℕ a)
four-a a =
  begin
    4 *ℕ a
      ≡⟨ *-commℕ 4 a ⟩
    a *ℕ 4
      ≡⟨ cong (a *ℕ_) (sym (*-commℕ 2 2)) ⟩
    a *ℕ (2 *ℕ 2)
      ≡⟨ sym (*-assocℕ a 2 2) ⟩
    a *ℕ 2 *ℕ 2
      ≡⟨ cong (_*ℕ 2) (*-commℕ a 2) ⟩
    2 *ℕ a *ℕ 2
      ≡⟨ *-commℕ (2 *ℕ a) 2 ⟩
    2 *ℕ (2 *ℕ a)
      ∎

sk≡k+1 : ∀ k → suc k ≡ k +ℕ 1
sk≡k+1 k =
  begin
    suc k
      ≡⟨ cong suc (sym (+-identityʳℕ k)) ⟩
    suc (k +ℕ 0)
      ≡⟨ sym (+-suc k 0) ⟩
    k +ℕ 1
      ∎

ssk≡k+2 : ∀ k → suc (suc k) ≡ k +ℕ 2
ssk≡k+2 k =
  begin
    suc (suc k)
      ≡⟨ cong suc (sk≡k+1 k) ⟩
    suc (k +ℕ 1)
      ≡⟨ sym (+-suc k 1) ⟩
    k +ℕ 2
      ∎

base8<16 : 4 *ℕ 2 <N 16
base8<16 = s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))))))

4<2^k+4 : ∀ k → 4 <N 2 ^ suc (suc (suc (suc k)))
4<2^k+4 k =
  ≤N-<-trans (m≤m+n 4 k) (n<2^n (suc (suc (suc (suc k)))))

4k+8<2^k+4 : ∀ k →
  4 *ℕ suc (suc k) <N 2 ^ suc (suc (suc (suc k)))
4k+8<2^k+4 zero    = base8<16
4k+8<2^k+4 (suc k) =
  let
    r = 2 ^ suc (suc (suc (suc k)))
    eqL : 4 *ℕ suc (suc (suc k)) ≡ 4 +ℕ 4 *ℕ suc (suc k)
    eqL = *-suc 4 (suc (suc k))
    step : 4 *ℕ suc (suc (suc k)) <N r +ℕ r
    step = ≤N-<-trans (≤N-reflexive eqL)
                      (+-mono-<N (4<2^k+4 k) (4k+8<2^k+4 k))
  in subst (λ z → 4 *ℕ suc (suc (suc k)) <N z)
           (cong (r +ℕ_) (sym (*-identityˡℕ r)))
           step

n<2+n : ∀ x → x <N x +ℕ 2
n<2+n x =
  let
    eq2 : x +ℕ 2 ≡ suc (suc x)
    eq2 =
      begin
        x +ℕ 2
          ≡⟨ +-commℕ x 2 ⟩
        2 +ℕ x
          ≡⟨⟩
        suc (suc x)
        ∎
  in subst (λ z → suc x ≤N z) (sym eq2) (s≤s (n≤1+n x))

4k+8<4k+10 : ∀ k →
  4 *ℕ suc (suc k) <N 2 *ℕ (2 *ℕ k +ℕ 5)
4k+8<4k+10 k =
  let
    m = 4 *ℕ suc (suc k)
    a = suc (suc k)
    a≡k+2 : a ≡ k +ℕ 2
    a≡k+2 = ssk≡k+2 k
    two-a-eq : 2 *ℕ a ≡ 2 *ℕ k +ℕ 4
    two-a-eq =
      begin
        2 *ℕ a
          ≡⟨ cong (2 *ℕ_) a≡k+2 ⟩
        2 *ℕ (k +ℕ 2)
          ≡⟨ *-distribˡ-+ 2 k 2 ⟩
        2 *ℕ k +ℕ 2 *ℕ 2
          ≡⟨⟩
        2 *ℕ k +ℕ 4
        ∎
    suc-eq : suc (2 *ℕ a) ≡ 2 *ℕ k +ℕ 5
    suc-eq =
      begin
        suc (2 *ℕ a)
          ≡⟨ cong suc two-a-eq ⟩
        suc (2 *ℕ k +ℕ 4)
          ≡⟨ sym (+-suc (2 *ℕ k) 4) ⟩
        2 *ℕ k +ℕ 5
        ∎
    eq : m +ℕ 2 ≡ 2 *ℕ (2 *ℕ k +ℕ 5)
    eq =
      begin
        4 *ℕ a +ℕ 2
          ≡⟨ cong (_+ℕ 2) (four-a a) ⟩
        2 *ℕ (2 *ℕ a) +ℕ 2
          ≡⟨ +-commℕ (2 *ℕ (2 *ℕ a)) 2 ⟩
        2 +ℕ 2 *ℕ (2 *ℕ a)
          ≡⟨ sym (*-suc 2 (2 *ℕ a)) ⟩
        2 *ℕ suc (2 *ℕ a)
          ≡⟨ cong (2 *ℕ_) suc-eq ⟩
        2 *ℕ (2 *ℕ k +ℕ 5)
        ∎
  in subst (λ z → m <N z) eq (n<2+n m)

hb-a : ℕ → ℕ
hb-a k = suc (suc k)

hb-e : ℕ → ℚ
hb-e k = embed (4 *ℕ hb-a k)

hb-p : ℕ → ℚ
hb-p k = 2ℚ * embed (2ss k)

hb-eq-2ss : ∀ k → 2ss k ≡ suc (2 *ℕ k +ℕ 3)
hb-eq-2ss k =
  begin
    2ss k
      ≡⟨ 2ss-eq k ⟩
    2 *ℕ suc (suc k)
      ≡⟨ cong (2 *ℕ_) (ssk≡k+2 k) ⟩
    2 *ℕ (k +ℕ 2)
      ≡⟨ *-distribˡ-+ 2 k 2 ⟩
    2 *ℕ k +ℕ 2 *ℕ 2
      ≡⟨ +-suc (2 *ℕ k) 3 ⟩
    suc (2 *ℕ k +ℕ 3)
    ∎

hb-pos-2ss : ∀ k → Positive (embed (2ss k))
hb-pos-2ss k =
  positive (subst (λ z → 0ℚ < embed z) (sym (hb-eq-2ss k))
             (0<embed (2 *ℕ k +ℕ 3)))

hb-p-nz : ∀ k → NonZero (hb-p k)
hb-p-nz k =
  pos⇒nonZero (hb-p k)
    {{pos*pos⇒pos 2ℚ (embed (2ss k)) {{hb-pos-2ss k}}}}

hb-2a≡2ss : ∀ k → 2 *ℕ hb-a k ≡ 2ss k
hb-2a≡2ss k =
  begin
    2 *ℕ hb-a k
      ≡⟨ cong (2 *ℕ_) (ssk≡k+2 k) ⟩
    2 *ℕ (k +ℕ 2)
      ≡⟨ *-distribˡ-+ 2 k 2 ⟩
    2 *ℕ k +ℕ 2 *ℕ 2
      ≡⟨ +-suc (2 *ℕ k) 3 ⟩
    suc (2 *ℕ k +ℕ 3)
      ≡⟨ sym (hb-eq-2ss k) ⟩
    2ss k
    ∎

hb-eq4 : ∀ k → 4 *ℕ hb-a k ≡ 2 *ℕ (2ss k)
hb-eq4 k =
  begin
    4 *ℕ hb-a k
      ≡⟨ four-a (hb-a k) ⟩
    2 *ℕ (2 *ℕ hb-a k)
      ≡⟨ cong (2 *ℕ_) (hb-2a≡2ss k) ⟩
    2 *ℕ (2ss k)
    ∎

hb-eqp : ∀ k → hb-p k ≡ hb-e k
hb-eqp k =
  begin
    hb-p k
      ≡⟨⟩
    2ℚ * embed (2ss k)
      ≡⟨ 2*embed (2ss k) ⟩
    embed (2 *ℕ (2ss k))
      ≡⟨ cong embed (sym (hb-eq4 k)) ⟩
    embed (4 *ℕ hb-a k)
      ≡⟨⟩
    hb-e k
      ∎

hb-e-nz : ∀ k → NonZero (hb-e k)
hb-e-nz k = subst NonZero (hb-eqp k) (hb-p-nz k)

hb-step1 : ∀ k →
  (1/_ (hb-e k) {{hb-e-nz k}}) + (1/_ (hb-e k) {{hb-e-nz k}})
    ≡ (1/_ (hb-p k) {{hb-p-nz k}}) + (1/_ (hb-p k) {{hb-p-nz k}})
hb-step1 k =
  begin
    (1/_ (hb-e k) {{hb-e-nz k}}) + (1/_ (hb-e k) {{hb-e-nz k}})
      ≡⟨ cong₂ _+_ rc rc ⟩
    (1/_ (hb-p k) {{hb-p-nz k}}) + (1/_ (hb-p k) {{hb-p-nz k}})
      ∎
  where
  rc : (1/_ (hb-e k) {{hb-e-nz k}}) ≡ (1/_ (hb-p k) {{hb-p-nz k}})
  rc = reciprocal-cong (hb-e k) (hb-p k)
         {{hb-e-nz k}} {{hb-p-nz k}} (sym (hb-eqp k))

H+H≡budget : ∀ k →
  (1/_ (embed (4 *ℕ suc (suc k))) {{hb-e-nz k}})
    + (1/_ (embed (4 *ℕ suc (suc k))) {{hb-e-nz k}})
    ≡ ε (suc k) * half
H+H≡budget k =
  begin
    (1/_ (embed (4 *ℕ suc (suc k))) {{hb-e-nz k}})
      + (1/_ (embed (4 *ℕ suc (suc k))) {{hb-e-nz k}})
      ≡⟨⟩
    (1/_ (hb-e k) {{hb-e-nz k}}) + (1/_ (hb-e k) {{hb-e-nz k}})
      ≡⟨ hb-step1 k ⟩
    (1/_ (hb-p k) {{hb-p-nz k}}) + (1/_ (hb-p k) {{hb-p-nz k}})
      ≡⟨ halve (embed (2ss k)) {{2ss-nonZero {k}}} {{hb-p-nz k}} ⟩
    (1/ embed (2ss k)) {{2ss-nonZero {k}}}
      ≡⟨ sym (εs-half k) ⟩
    ε (suc k) * half
      ∎
