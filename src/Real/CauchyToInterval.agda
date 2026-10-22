------------------------------------------------------------------------
-- Reverse equivalence: Cauchy sequences → nested-interval reals
--
-- From a Cauchy sequence (f, μ) build a nested-interval real. The k-th
-- interval is centred at f (μ (K k)) with radius δ k, where
-- K k = 2^(k+2) is chosen so the Cauchy error ε (K k) is strictly
-- below δ (suc k). This yields the nesting conditions.
--
-- 反向等价：柯西序列 → 嵌套区间实数
--
-- 由柯西序列 (f, μ) 构造嵌套区间实数。第 k 层区间以 f (μ (K k))
-- 为中心、以 δ k 为半径，其中 K k = 2^(k+2) 使柯西误差 ε (K k)
-- 严格小于 δ (suc k)。由此得到嵌套条件。
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module Real.CauchyToInterval where

open import Data.Nat using
  (ℕ; zero; suc; _^_; _⊔_; _≥_; s≤s) renaming (_≤_ to _≤N_; _<_ to _<N_)
import Data.Nat.Properties as ℕP
open import Data.Nat.Properties using
  (m≤m⊔n; m≤n⊔m; ^-monoʳ-≤; m≤n+m) renaming (≤-refl to ≤N-refl; ≤-trans to ≤N-trans; ≤-reflexive to ≤N-reflexive)
open import Data.Product using (_,_)
open import Data.Rational using
  (ℚ; 0ℚ; 1ℚ; _+_; _-_; _*_; _<_; _≤_; ∣_∣; NonNegative; NonZero; positive; nonNegative)
open import Data.Rational.Base using (1/_; _÷_) renaming (-_ to neg)
open import Data.Rational.Properties using
  (+-assoc; +-comm; +-identityˡ; +-identityʳ; +-inverseʳ; +-inverseˡ; neg-distrib-+
  ; ≤-refl; ≤-reflexive; ≤-trans; <⇒≤; ≤-<-trans; <-≤-trans; <-trans; +-mono-≤
  ; +-mono-<-≤; *-inverseʳ; pos⇒nonZero; positive⁻¹; *-cancelˡ-<-nonNeg
  ; *-assoc; *-comm; *-identityʳ; *-identityˡ)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; cong; cong₂; sym; subst; subst₂; module ≡-Reasoning)
open ≡-Reasoning

open import Real using (CauchySeq; ε; embed)
open CauchySeq renaming (f to seq-f; μ to seq-μ; cauchy to seq-cauchy)
open import Real.Interval using
  (RealI; δ; δ-half; negδ<δ; pos-pow; double-half; neg-invol)
open import Real.Interval.Mul using (cancel-z; le-shift; cancelʳ)
open import Real.Interval.Node using (mul-nonNeg)
open import Real.Interval.Rational using (r≤|r|; -r≤|r|; sub-add)
open import Real.IntervalEquiv using (embed-mono-<; node; centre; n<2^n)

------------------------------------------------------------------------
-- Sampling index and position
--
-- K n = 2^(n+2). Chosen so ε (K n) < δ (suc n).
--
-- 采样下标与位置
--
-- K n = 2^(n+2)。选它使 ε (K n) < δ (suc n)。

K : ℕ → ℕ
K n = 2 ^ suc (suc n)

-- Sampling index: prefix maximum, so M is monotone. This replaces the
-- naive M x n = seq-μ x (K n), which need not be monotone since
-- CauchySeq carries no monotonicity assumption on μ.
--
-- 采样下标：前缀最大值，使 M 单调。它替代朴素的
-- M x n = seq-μ x (K n)；由于 CauchySeq 未对 μ 作单调性假设，
-- 朴素定义未必单调。
M : CauchySeq → ℕ → ℕ
M x zero    = seq-μ x (K zero)
M x (suc n) = M x n ⊔ seq-μ x (K (suc n))

-- The sampled centre.
--
-- 采样中心。
centre-c : CauchySeq → ℕ → ℚ
centre-c x n = seq-f x (M x n)

-- seq-μ x (K n) ≤ M x n. Needed so that M x n lies past the modulus
-- seq-μ x (K n).
--
-- seq-μ x (K n) ≤ M x n。用以说明 M x n 落在模数 seq-μ x (K n)
-- 之后。
μ≤M : (x : CauchySeq) (n : ℕ) → seq-μ x (K n) ≤N M x n
μ≤M x zero    = ≤N-reflexive refl
μ≤M x (suc n) = m≤n⊔m (M x n) (seq-μ x (K (suc n)))

-- Monotonicity of M.
--
-- M 的单调性。
M-mono : (x : CauchySeq) (n : ℕ) → M x n ≤N M x (suc n)
M-mono x n = m≤m⊔n (M x n) (seq-μ x (K (suc n)))

μ≤M-suc : (x : CauchySeq) (n : ℕ) → seq-μ x (K n) ≤N M x (suc n)
μ≤M-suc x n = ≤N-trans (μ≤M x n) (M-mono x n)

K<sK : (n : ℕ) → K n <N suc (K n)
K<sK n = s≤s ≤N-refl

------------------------------------------------------------------------
-- Reciprocal is strictly antitone on positive rationals:
--   0 < a → a < b → 1/b < 1/a.
--
-- 正有理数上倒数严格反单调：
--   0 < a → a < b → 1/b < 1/a。

recip-strict : ∀ {a b : ℚ} (0<a : 0ℚ < a) (a<b : a < b) →
  (1/ b) {{pos⇒nonZero b {{positive (<-≤-trans 0<a (<⇒≤ a<b))}}}}
  <
  (1/ a) {{pos⇒nonZero a {{positive 0<a}}}}
recip-strict {a} {b} 0<a a<b =
  *-cancelˡ-<-nonNeg (a * b) {{c-nn}}
    (subst₂ _<_
      (sym eq1) (sym eq2)
      a<b)
  where
    0<b : 0ℚ < b
    0<b = <-≤-trans 0<a (<⇒≤ a<b)

    c-nn : NonNegative (a * b)
    c-nn = nonNegative (mul-nonNeg (<⇒≤ 0<a) (<⇒≤ 0<b))

    a-nz : NonZero a
    a-nz = pos⇒nonZero a {{positive 0<a}}
    b-nz : NonZero b
    b-nz = pos⇒nonZero b {{positive 0<b}}

    eq1 : (a * b) * ((1/ b) {{b-nz}}) ≡ a
    eq1 = begin
      (a * b) * ((1/ b) {{b-nz}})
        ≡⟨ *-assoc a b ((1/ b) {{b-nz}}) ⟩
      a * (b * ((1/ b) {{b-nz}}))
        ≡⟨ cong (a *_) (*-inverseʳ b {{b-nz}}) ⟩
      a * 1ℚ
        ≡⟨ *-identityʳ a ⟩
      a
      ∎

    eq2 : (a * b) * ((1/ a) {{a-nz}}) ≡ b
    eq2 = begin
      (a * b) * ((1/ a) {{a-nz}})
        ≡⟨ *-assoc a b ((1/ a) {{a-nz}}) ⟩
      a * (b * ((1/ a) {{a-nz}}))
        ≡⟨ cong (a *_) (*-comm b ((1/ a) {{a-nz}})) ⟩
      a * (((1/ a) {{a-nz}}) * b)
        ≡⟨ sym (*-assoc a ((1/ a) {{a-nz}}) b) ⟩
      (a * ((1/ a) {{a-nz}})) * b
        ≡⟨ cong (_* b) (*-inverseʳ a {{a-nz}}) ⟩
      1ℚ * b
        ≡⟨ *-identityˡ b ⟩
      b
      ∎

δ-suc≡ : ∀ n → δ (suc n)
  ≡ (1/ (embed (K n))) {{pos⇒nonZero (embed (K n)) {{pos-pow (suc n)}}}}
δ-suc≡ n = refl

ε-K<δ-suc : ∀ n → ε (K n) < δ (suc n)
ε-K<δ-suc n =
  subst (λ z → ε (K n) < z) (sym (δ-suc≡ n))
    (recip-strict
      {a = embed (K n)}
      {b = embed (suc (K n))}
      (positive⁻¹ (embed (K n)) {{pos-pow (suc n)}})
      (embed-mono-< (K<sK n)))

------------------------------------------------------------------------
-- Main construction
--
-- 主构造

module _ (x : CauchySeq) where

  a : ℕ → ℚ
  a n = centre-c x n

  -- Adjacent sampled centres are within δ (suc n).
  --
  -- 相邻采样中心落在 δ (suc n) 内。
  cauchy-adj : ∀ n → ∣ a n - a (suc n) ∣ < δ (suc n)
  cauchy-adj n =
    <-trans
      (seq-cauchy x (K n) (M x n) (M x (suc n))
        (μ≤M x n) (μ≤M-suc x n))
      (ε-K<δ-suc n)

  dn-dsn≡dsn : ∀ n → δ n - δ (suc n) ≡ δ (suc n)
  dn-dsn≡dsn n = begin
    δ n - δ (suc n)
      ≡⟨ cong (λ z → z - δ (suc n)) (sym (δ-half n)) ⟩
    (δ (suc n) + δ (suc n)) - δ (suc n)
      ≡⟨ cancel-z (δ (suc n)) (δ (suc n)) ⟩
    δ (suc n)
      ∎

  sub-shift : ∀ a b c d → a - b ≤ c - d → a - c ≤ b - d
  sub-shift a b c d h =
    subst₂ _≤_
      lhs-eq
      rhs-eq
      (+-mono-≤ h (≤-refl {b - c}))
    where
      lhs-eq : (a - b) + (b - c) ≡ a - c
      lhs-eq = begin
        (a - b) + (b - c)
          ≡⟨⟩
        (a + neg b) + (b + neg c)
          ≡⟨ +-assoc a (neg b) (b + neg c) ⟩
        a + (neg b + (b + neg c))
          ≡⟨ cong (a +_) (sym (+-assoc (neg b) b (neg c))) ⟩
        a + ((neg b + b) + neg c)
          ≡⟨ cong (a +_) (cong (_+ neg c) (+-inverseˡ b)) ⟩
        a + (0ℚ + neg c)
          ≡⟨ cong (a +_) (+-identityˡ (neg c)) ⟩
        a + neg c
          ≡⟨⟩
        a - c
        ∎

      rhs-eq : (c - d) + (b - c) ≡ b - d
      rhs-eq = begin
        (c - d) + (b - c)
          ≡⟨⟩
        (c + neg d) + (b + neg c)
          ≡⟨ +-comm (c + neg d) (b + neg c) ⟩
        (b + neg c) + (c + neg d)
          ≡⟨ +-assoc b (neg c) (c + neg d) ⟩
        b + (neg c + (c + neg d))
          ≡⟨ cong (b +_) (sym (+-assoc (neg c) c (neg d))) ⟩
        b + ((neg c + c) + neg d)
          ≡⟨ cong (b +_) (cong (_+ neg d) (+-inverseˡ c)) ⟩
        b + (0ℚ + neg d)
          ≡⟨ cong (b +_) (+-identityˡ (neg d)) ⟩
        b + neg d
          ≡⟨⟩
        b - d
        ∎

  go : ℕ → RealI
  RealI.l (go n)  = a n - δ n
  RealI.u (go n)  = a n + δ n
  RealI.lo (go n) =
    subst₂ _<_
      (sym (+-comm (a n) (neg (δ n))))
      (sym (+-comm (a n) (δ n)))
      (+-mono-<-≤ (negδ<δ n) (≤-refl {a n}))
  RealI.next (go n) = go (suc n)
  RealI.nest (go n) = nest1 , nest2 , nest3'
    where
      an  = a n
      asn = a (suc n)
      dn  = δ n
      dsn = δ (suc n)
      adj = cauchy-adj n

      asn-an<dsn : asn - an < dsn
      asn-an<dsn =
        subst (λ z → z < dsn)
              (begin
                neg (an - asn)
                  ≡⟨⟩
                neg (an + neg asn)
                  ≡⟨ neg-distrib-+ an (neg asn) ⟩
                neg an + neg (neg asn)
                  ≡⟨ cong (neg an +_) (neg-invol asn) ⟩
                neg an + asn
                  ≡⟨ +-comm (neg an) asn ⟩
                asn + neg an
                  ≡⟨⟩
                asn - an
                ∎)
              (≤-<-trans (-r≤|r| (an - asn)) adj)

      nest1 : an - dn ≤ asn - dsn
      nest1 =
        sub-shift an asn dn dsn
          (subst (λ z → an - asn ≤ z)
                 (sym (dn-dsn≡dsn n))
                 (≤-trans (r≤|r| (an - asn)) (<⇒≤ adj)))

      nest2 : asn + dsn ≤ an + dn
      nest2 =
        let h1 : asn ≤ dsn + an
            h1 = le-shift {x = asn} {y = an} {z = dsn}
                   (<⇒≤ asn-an<dsn)
            h2 : asn + dsn ≤ (dsn + an) + dsn
            h2 = +-mono-≤ h1 (≤-refl {dsn})
            eq : (dsn + an) + dsn ≡ an + dn
            eq = begin
              (dsn + an) + dsn
                ≡⟨ +-assoc dsn an dsn ⟩
              dsn + (an + dsn)
                ≡⟨ cong (dsn +_) (+-comm an dsn) ⟩
              dsn + (dsn + an)
                ≡⟨ sym (+-assoc dsn dsn an) ⟩
              (dsn + dsn) + an
                ≡⟨ cong (_+ an) (δ-half n) ⟩
              dn + an
                ≡⟨ +-comm dn an ⟩
              an + dn
                ∎
        in subst (λ z → asn + dsn ≤ z) eq h2

      diff-sum : ∀ x y → (x + y) - (x - y) ≡ y + y
      diff-sum x y = begin
        (x + y) - (x - y)
          ≡⟨⟩ (x + y) - (x + neg y)
          ≡⟨ sub-add x y x (neg y) ⟩
          (x - x) + (y - neg y)
          ≡⟨ cong₂ _+_ (+-inverseʳ x) (sub-neg y) ⟩
          0ℚ + (y + y) ≡⟨ +-identityˡ (y + y) ⟩ y + y ∎
        where
          sub-neg : ∀ z → z - neg z ≡ z + z
          sub-neg z = begin
            z - neg z ≡⟨⟩ z + neg (neg z) ≡⟨ cong (z +_) (neg-invol z) ⟩ z + z ∎

      nest3 : (asn + dsn) - (asn - dsn) ≤ (dn + dn) ÷ embed 2
      nest3 =
        subst (λ z → (asn + dsn) - (asn - dsn) ≤ z)
              (sym (begin
                (dn + dn) ÷ embed 2
                  ≡⟨ double-half dn ⟩
                dn
                  ≡⟨ dn≡dsn+dsn ⟩
                dsn + dsn
                  ∎))
              (≤-reflexive (diff-sum asn dsn))
        where
          dn≡dsn+dsn : dn ≡ dsn + dsn
          dn≡dsn+dsn = begin
            dn
              ≡⟨ sym (cancelʳ dn dsn) ⟩
            (dn - dsn) + dsn
              ≡⟨ cong (_+ dsn) (dn-dsn≡dsn n) ⟩
            dsn + dsn
              ∎

      -- Convert the RHS from (δ n + δ n) ÷ 2 to
      -- ((a n + δ n) - (a n - δ n)) ÷ 2.
      --
      -- 把右端从 (δ n + δ n) ÷ 2 转成
      -- ((a n + δ n) - (a n - δ n)) ÷ 2。
      nest3' : RealI.u (go (suc n)) - RealI.l (go (suc n))
                 ≤ (RealI.u (go n) - RealI.l (go n)) ÷ embed 2
      nest3' =
        subst (λ z → RealI.u (go (suc n)) - RealI.l (go (suc n)) ≤ z)
              (cong (λ w → w ÷ embed 2) (sym (diff-sum (a n) (δ n))))
              nest3

------------------------------------------------------------------------
-- cauchy→realI
--
-- 柯西序列 → 嵌套区间实数。

cauchy→realI : CauchySeq → RealI
cauchy→realI x = go x 0

------------------------------------------------------------------------
-- node (go x 0) n ≡ go x n
--
-- 迭代后继 n 次后回到 go x n。

node-go : (x : CauchySeq) (n : ℕ) → node (go x 0) n ≡ go x n
node-go x zero    = refl
node-go x (suc n) = cong RealI.next (node-go x n)

------------------------------------------------------------------------
-- Exported lemma: the centre of the n-th layer of cauchy→realI is
-- the sampled centre seq-f x (M x n).
--
-- 导出引理：cauchy→realI 的第 n 层中心就是采样中心
-- seq-f x (M x n)。

centre-cauchy→realI : (x : CauchySeq) (n : ℕ) →
  centre (cauchy→realI x) n ≡ seq-f x (M x n)
centre-cauchy→realI x n = begin
  centre (cauchy→realI x) n
    ≡⟨⟩
  centre (go x 0) n
    ≡⟨ cong₂ (λ p q → (p + q) ÷ embed 2)
             (cong RealI.l (node-go x n))
             (cong RealI.u (node-go x n)) ⟩
  (RealI.l (go x n) + RealI.u (go x n)) ÷ embed 2
    ≡⟨⟩
  ((a x n - δ n) + (a x n + δ n)) ÷ embed 2
    ≡⟨ cong (_÷ embed 2) (cancel-dn (a x n) (δ n)) ⟩
  (a x n + a x n) ÷ embed 2
    ≡⟨ double-half (a x n) ⟩
  a x n
    ≡⟨⟩
  centre-c x n
    ≡⟨⟩
  seq-f x (M x n)
    ∎
  where
    cancel-dn : ∀ a d → (a - d) + (a + d) ≡ a + a
    cancel-dn a d = begin
      (a - d) + (a + d)
        ≡⟨ +-assoc a (neg d) (a + d) ⟩
      a + (neg d + (a + d))
        ≡⟨ cong (a +_) (sym (+-assoc (neg d) a d)) ⟩
      a + ((neg d + a) + d)
        ≡⟨ cong (a +_) (cong (_+ d) (+-comm (neg d) a)) ⟩
      a + ((a + neg d) + d)
        ≡⟨ cong (a +_) (+-assoc a (neg d) d) ⟩
      a + (a + (neg d + d))
        ≡⟨ cong (a +_) (cong (a +_) (+-inverseˡ d)) ⟩
      a + (a + 0ℚ)
        ≡⟨ cong (a +_) (+-identityʳ a) ⟩
      a + a
      ∎

------------------------------------------------------------------------
-- M 与 K 的模数性质
--
-- M 支配 K 处的模数；K 支配恒等。

M≥μK : (x : CauchySeq) (n : ℕ) → M x n ≥ seq-μ x (K n)
M≥μK x zero    = ≤N-refl
M≥μK x (suc n) = m≤n⊔m (M x n) (seq-μ x (K (suc n)))

K≥k : (k : ℕ) → K k ≥ k
K≥k k = ≤N-trans (ℕP.<⇒≤ (n<2^n k)) (^-monoʳ-≤ 2 (m≤n+m k 2))
