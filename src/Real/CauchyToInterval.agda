------------------------------------------------------------------------
-- Reverse equivalence: Cauchy sequences → nested-interval reals
--
-- 反向等价：柯西序列 → 嵌套区间实数
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module Real.CauchyToInterval where

open import Data.Nat using
  (ℕ; zero; suc; _^_; _⊔_; _≥_; s≤s) renaming (_≤_ to _≤N_; _<_ to _<N_)
import Data.Nat.Properties as ℕP
open import Data.Nat.Properties using
  (m≤m⊔n; m≤n⊔m; ^-monoʳ-≤; m≤n+m) renaming (≤-refl to ≤N-refl; ≤-trans to ≤N-trans; ≤-reflexive to ≤N-reflexive)
open import Data.Product using (_,_)
open import Data.Rational using (ℚ; 0ℚ; _+_; _-_; _<_; _≤_; ∣_∣)
open import Data.Rational.Base using (1/_; _÷_) renaming (-_ to neg)
open import Data.Rational.Properties using
  (+-assoc; +-comm; +-identityˡ; +-identityʳ; +-inverseʳ; +-inverseˡ
  ; neg-distrib-+; ≤-refl; ≤-reflexive; ≤-trans; <⇒≤; ≤-<-trans; <-trans
  ; +-mono-≤; +-mono-<-≤; pos⇒nonZero; positive⁻¹)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; cong; cong₂; sym; trans; subst; subst₂; module ≡-Reasoning)
open ≡-Reasoning

open import Base.RationalRing using (neg-involutive; +interchange; telescope)
open import Real using (CauchySeq; ε; embed; embed-mono-<)
open CauchySeq renaming (f to seq-f; μ to seq-μ; cauchy to seq-cauchy)
open import Real.Interval using
  (RealI; δ; δ-half; negδ<δ; pos-pow; double-half)
open import Real.Interval.Mul using (cancel-z; le-shift; cancelʳ)
open import Real.Interval.Rational using (r≤|r|; -r≤|r|; sub-add)
open import Real.IntervalEquiv using (node; centre; n<2^n)
open import Real.Interval.Kit using (strict-recip)

------------------------------------------------------------------------
-- Sampling index and position
--
-- K n = 2^(n+2), chosen so ε (K n) < δ (suc n).
--
-- 采样下标与位置
--
-- K 取 2 的后继后继次幂，使得相应精度上的 ε 严格小于后继层的 δ。

K : ℕ → ℕ
K n = 2 ^ suc (suc n)

-- Sampling index: prefix maximum, so M is monotone. This replaces the
-- naive definition, which need not be monotone since CauchySeq carries
-- no monotonicity assumption on μ.
--
-- 采样下标
--
-- 前缀最大值，从而 M 单调。它替代朴素定义；由于 CauchySeq 未对
-- μ 作单调性假设，朴素定义未必单调。
M : CauchySeq → ℕ → ℕ
M x zero    = seq-μ x (K zero)
M x (suc n) = M x n ⊔ seq-μ x (K (suc n))

-- The sampled centre.
--
-- 采样中心。
centre-c : CauchySeq → ℕ → ℚ
centre-c x n = seq-f x (M x n)

-- M dominates the modulus at the sampled precision, so that M x n lies
-- past seq-μ x (K n).
--
-- M 支配采样精度处的模数，从而 M x n 落在该模数之后。
μ≤M : (x : CauchySeq) (n : ℕ) → seq-μ x (K n) ≤N M x n
μ≤M x zero    = ≤N-reflexive refl
μ≤M x (suc n) = m≤n⊔m (M x n) (seq-μ x (K (suc n)))

-- Monotonicity of M.
--
-- M 的单调性。
M-mono : (x : CauchySeq) (n : ℕ) → M x n ≤N M x (suc n)
M-mono x n = m≤m⊔n (M x n) (seq-μ x (K (suc n)))

-- The modulus at level n is dominated by M at level n+1.
--
-- 第 n 层模数被 M 在第 n+1 层支配。
μ≤M-suc : (x : CauchySeq) (n : ℕ) → seq-μ x (K n) ≤N M x (suc n)
μ≤M-suc x n = ≤N-trans (μ≤M x n) (M-mono x n)

-- The sampling index is strictly below its successor.
--
-- 采样下标严格小于其后继。
K<sK : (n : ℕ) → K n <N suc (K n)
K<sK n = s≤s ≤N-refl

------------------------------------------------------------------------
-- Strict reciprocal antitonicity on positive rationals
--
-- 正有理数上倒数严格反单调

δ-suc≡ : ∀ n → δ (suc n)
  ≡ (1/ (embed (K n))) {{pos⇒nonZero (embed (K n)) {{pos-pow (suc n)}}}}
δ-suc≡ n = refl

-- The sampled precision is strictly below the successor tolerance.
--
-- 采样精度严格低于后继层容差。
ε-K<δ-suc : ∀ n → ε (K n) < δ (suc n)
ε-K<δ-suc n =
  subst (λ z → ε (K n) < z) (sym (δ-suc≡ n))
    (strict-recip (embed (K n)) (embed (suc (K n)))
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
  -- 相邻采样中心落在后继层的二进半径之内。
  cauchy-adj : ∀ n → ∣ a n - a (suc n) ∣ < δ (suc n)
  cauchy-adj n =
    <-trans
      (seq-cauchy x (K n) (M x n) (M x (suc n))
        (μ≤M x n) (μ≤M-suc x n))
      (ε-K<δ-suc n)

  -- A difference of successive tolerances equals the successor tolerance.
  --
  -- 相邻容差之差等于后继容差。
  dn-dsn≡dsn : ∀ n → δ n - δ (suc n) ≡ δ (suc n)
  dn-dsn≡dsn n = begin
    δ n - δ (suc n)
      ≡⟨ cong (λ z → z - δ (suc n)) (sym (δ-half n)) ⟩
    (δ (suc n) + δ (suc n)) - δ (suc n)
      ≡⟨ cancel-z (δ (suc n)) (δ (suc n)) ⟩
    δ (suc n)
      ∎

  -- Rearranging a difference inequality.
  --
  -- 重排差值不等式。
  sub-shift : ∀ x y z w → x - y ≤ z - w → x - z ≤ y - w
  sub-shift x y z w h =
    subst₂ _≤_
      (telescope x y z)
      (trans (+-comm (z - w) (y - z)) (telescope y z w))
      (+-mono-≤ h (≤-refl {y - z}))

  -- The nested-interval real built from the sampled centres and the
  -- dyadic tolerances.
  --
  -- 由采样中心与二进容差构造的嵌套区间实数。
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
                  ≡⟨ cong (neg an +_) (neg-involutive asn) ⟩
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

      -- A sum minus the corresponding difference equals the doubled second term.
      --
      -- 和减去差等于第二项的两倍。
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
          sub-neg z = cong (z +_) (neg-involutive z)

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

      -- Convert the RHS from a power-of-two width at the current level
      -- to the corresponding difference of endpoints.
      --
      -- 把右端从当前层的二进宽度转换为对应端点的差。
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
-- Iterating the successor returns the n-th layer.
--
-- 迭代后继 n 次后回到第 n 层。

node-go : (x : CauchySeq) (n : ℕ) → node (go x 0) n ≡ go x n
node-go x zero    = refl
node-go x (suc n) = cong RealI.next (node-go x n)

------------------------------------------------------------------------
-- Exported lemma: the centre of the n-th layer of cauchy→realI is
-- the sampled centre.
--
-- 导出引理：cauchy→realI 的第 n 层中心就是采样中心。

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
        ≡⟨ refl ⟩
      (a + neg d) + (a + d)
        ≡⟨ +interchange a (neg d) a d ⟩
      (a + a) + (neg d + d)
        ≡⟨ cong ((a + a) +_) (+-inverseˡ d) ⟩
      (a + a) + 0ℚ
        ≡⟨ +-identityʳ (a + a) ⟩
      a + a
      ∎

------------------------------------------------------------------------
-- Modulus lemmas
--
-- 模数性质

-- The sampling index dominates the identity.
--
-- 采样下标支配恒等。
K≥k : (k : ℕ) → K k ≥ k
K≥k k = ≤N-trans (ℕP.<⇒≤ (n<2^n k)) (^-monoʳ-≤ 2 (m≤n+m k 2))
