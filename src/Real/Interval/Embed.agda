------------------------------------------------------------------------
-- Field axioms for RealI: nontriviality and the ℚ embedding
--
-- RealI 的域公理：非平凡性与 ℚ 嵌入
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module Real.Interval.Embed where

open import Data.Nat using (ℕ; s≤s; z≤n) renaming (_*_ to _ℕ*_)
open import Data.Product using (_,_)
open import Data.Rational using
  (ℚ; 0ℚ; 1ℚ; _+_; _-_; _*_; _≤_; _<_; ∣_∣) renaming (-_ to neg)
open import Data.Rational.Properties using
  (+-identityˡ; +-identityʳ; +-inverseˡ; +-comm; +-assoc; *-identityˡ
  ; *-identityʳ; *-assoc; *-comm; *-distribʳ-+; +-monoˡ-<; *-monoˡ-<-pos)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; cong; cong₂; sym; trans; subst; module ≡-Reasoning)
open ≡-Reasoning

open import Real using (half; embed; embed-mono-<; 2ℚ; 2ℚ≡1+1)
open import Real.Interval using (dyadic; δ; δ-half)
open import Real.Interval.Arith using (0ℝ; 1ℝ; _+ℝ_; negℝ)
open import Real.Interval.Mul using (_*ℝ_)
open import Real.Interval.Order using (_<ℝ_)
open import Real.Interval.Equiv using (_≈ℝ_; ≈ℝ-refl)
open import Real.IntervalEquiv using (l; u; centre; width; recipPow2)
open import Real.Interval.Node using
  (l-dyadic; u-dyadic; centre-add; centre-neg; mul-nonNeg; 0≤width-n)
open import Real.Interval.Kit using
  (≈ℝ-of-eq; ≈ℝ-of-rec; 0≤half; 2ℚ*half≡1; abs-swap)
open import Real.Interval.Mul.Core using (term1)

------------------------------------------------------------------------
-- Nontriviality: 0ℝ <ℝ 1ℝ
--
-- 非平凡性
--
-- At depth 1, the upper endpoint of 0ℝ lies strictly below the lower
-- endpoint of 1ℝ.
--
-- 在深度 1 处，0ℝ 的上端点严格低于 1ℝ 的下端点。
half<1 : half < 1ℚ
half<1 =
  let
    1<2 : 1ℚ < embed 2
    1<2 = embed-mono-< {1} {2} (s≤s (s≤s z≤n))

    raw : half * 1ℚ < half * embed 2
    raw = *-monoˡ-<-pos half 1<2

    lhs≡ : half * 1ℚ ≡ half
    lhs≡ = *-identityʳ half

    rhs≡ : half * embed 2 ≡ 1ℚ
    rhs≡ = trans (*-comm half (embed 2)) 2ℚ*half≡1
  in
    subst (λ a → a < half * embed 2) lhs≡
      (subst (λ b → half < b) rhs≡ raw)

δ0≡half : δ 0 ≡ half
δ0≡half = refl

δ0<1 : δ 0 < 1ℚ
δ0<1 = subst (λ z → z < 1ℚ) δ0≡half half<1

δ1+δ1<1 : δ 1 + δ 1 < 1ℚ
δ1+δ1<1 = subst (λ z → z < 1ℚ) (δ-half 0) δ0<1

δ1<negδ1+1 : δ 1 < neg (δ 1) + 1ℚ
δ1<negδ1+1 =
  let
    step : (δ 1 + δ 1) + neg (δ 1) < 1ℚ + neg (δ 1)
    step = +-monoˡ-< (neg (δ 1)) δ1+δ1<1

    lhs≡ : (δ 1 + δ 1) + neg (δ 1) ≡ δ 1
    lhs≡ = begin
      (δ 1 + δ 1) + neg (δ 1)
        ≡⟨ +-assoc (δ 1) (δ 1) (neg (δ 1)) ⟩
      δ 1 + (δ 1 + neg (δ 1))
        ≡⟨ cong (δ 1 +_) (+-inverseˡ (δ 1)) ⟩
      δ 1 + 0ℚ
        ≡⟨ +-identityʳ (δ 1) ⟩
      δ 1
        ∎

    rhs≡ : 1ℚ + neg (δ 1) ≡ neg (δ 1) + 1ℚ
    rhs≡ = +-comm 1ℚ (neg (δ 1))
  in
    subst (λ z → z < neg (δ 1) + 1ℚ) lhs≡
      (subst (λ w → δ 1 < w) rhs≡ step)

u0ℝ1≡δ1 : u 0ℝ 1 ≡ δ 1
u0ℝ1≡δ1 = begin
  u 0ℝ 1
    ≡⟨ u-dyadic 0ℚ 1 ⟩
  δ 1 + 0ℚ
    ≡⟨ +-identityʳ (δ 1) ⟩
  δ 1
    ∎

l1ℝ1≡negδ1+1 : l 1ℝ 1 ≡ neg (δ 1) + 1ℚ
l1ℝ1≡negδ1+1 = l-dyadic 1ℚ 1

0ℝ<ℝ1ℝ : 0ℝ <ℝ 1ℝ
0ℝ<ℝ1ℝ = 1 , goal
  where
    goal : u 0ℝ 1 < l 1ℝ 1
    goal =
      subst (λ a → a < l 1ℝ 1) u0ℝ1≡δ1
        (subst (λ b → δ 1 < b) l1ℝ1≡negδ1+1 δ1<negδ1+1)

------------------------------------------------------------------------
-- embedℚ is a field homomorphism
--
-- embedℚ 是域同态

-- The centre of embedℚ q is q itself. The endpoint terms -δ n and
-- +δ n cancel, leaving twice q, which halves back to q.
--
-- embedℚ q 的中心恰为 q：端点中的容差项相消后剩下两倍 q，再减半即得 q。
centre-embedℚ : (q : ℚ) (n : ℕ) → centre (dyadic q 0) n ≡ q
centre-embedℚ q n =
  let
    dn = δ n

    lq : l (dyadic q 0) n ≡ neg dn + q
    lq = l-dyadic q n

    uq : u (dyadic q 0) n ≡ dn + q
    uq = u-dyadic q n

    sum : (neg dn + q) + (dn + q) ≡ q + q
    sum = begin
      (neg dn + q) + (dn + q)
        ≡⟨ +-assoc (neg dn) q (dn + q) ⟩
      neg dn + (q + (dn + q))
        ≡⟨ cong (neg dn +_)
          (begin
            q + (dn + q)
              ≡⟨ sym (+-assoc q dn q) ⟩
            (q + dn) + q
              ≡⟨ cong (_+ q) (+-comm q dn) ⟩
            (dn + q) + q
              ≡⟨ +-assoc dn q q ⟩
            dn + (q + q)
              ∎) ⟩
      neg dn + (dn + (q + q))
        ≡⟨ sym (+-assoc (neg dn) dn (q + q)) ⟩
      ((neg dn) + dn) + (q + q)
        ≡⟨ cong (_+ (q + q)) (+-inverseˡ dn) ⟩
      0ℚ + (q + q)
        ≡⟨ +-identityˡ (q + q) ⟩
      q + q
        ∎
  in begin
    centre (dyadic q 0) n
      ≡⟨ cong₂ (λ a b → (a + b) * half) lq uq ⟩
    ((neg dn + q) + (dn + q)) * half
      ≡⟨ cong (_* half) sum ⟩
    (q + q) * half
      ≡⟨ cong (_* half) q+q≡2*q ⟩
    2ℚ * q * half
      ≡⟨ cong (_* half) (*-comm 2ℚ q) ⟩
    (q * 2ℚ) * half
      ≡⟨ *-assoc q 2ℚ half ⟩
    q * (2ℚ * half)
      ≡⟨ cong (q *_) 2ℚ*half≡1 ⟩
    q * 1ℚ
      ≡⟨ *-identityʳ q ⟩
    q
      ∎
  where
    q+q≡2*q : q + q ≡ 2ℚ * q
    q+q≡2*q = sym (begin
      2ℚ * q
        ≡⟨ cong (_* q) (sym 2ℚ≡1+1) ⟩
      (1ℚ + 1ℚ) * q
        ≡⟨ *-distribʳ-+ q 1ℚ 1ℚ ⟩
      1ℚ * q + 1ℚ * q
        ≡⟨ cong₂ _+_ (*-identityˡ q) (*-identityˡ q) ⟩
      q + q
        ∎)

-- embedℚ preserves addition: both sides agree in centre at every
-- depth.
--
-- embedℚ 保加法：两侧在每个深度的中心相同。
embedℚ-+ : (p q : ℚ) →
  dyadic (p + q) 0 ≈ℝ dyadic p 0 +ℝ dyadic q 0
embedℚ-+ p q =
  ≈ℝ-of-eq (dyadic (p + q) 0) (dyadic p 0 +ℝ dyadic q 0)
    λ n → begin
      centre (dyadic (p + q) 0) n
        ≡⟨ centre-embedℚ (p + q) n ⟩
      p + q
        ≡⟨ sym (cong₂ _+_ (centre-embedℚ p n) (centre-embedℚ q n)) ⟩
      centre (dyadic p 0) n + centre (dyadic q 0) n
        ≡⟨ sym (centre-add (dyadic p 0) (dyadic q 0) n) ⟩
      centre (dyadic p 0 +ℝ dyadic q 0) n
        ∎

-- embedℚ preserves negation: both sides agree in centre at every
-- depth.
--
-- embedℚ 保取负：两侧在每个深度的中心相同。
embedℚ-neg : (q : ℚ) →
  dyadic (neg q) 0 ≈ℝ negℝ (dyadic q 0)
embedℚ-neg q =
  ≈ℝ-of-eq (dyadic (neg q) 0) (negℝ (dyadic q 0))
    λ n → begin
      centre (dyadic (neg q) 0) n
        ≡⟨ centre-embedℚ (neg q) n ⟩
      neg q
        ≡⟨ sym (cong neg (centre-embedℚ q n)) ⟩
      neg (centre (dyadic q 0) n)
        ≡⟨ sym (centre-neg (dyadic q 0) n) ⟩
      centre (negℝ (dyadic q 0)) n
        ∎

-- embedℚ preserves multiplication. term1 bounds the centre error of
-- x *ℝ R by a geometric series. For x = embedℚ p and R = embedℚ q,
-- the centres at depth 2n are exactly p and q, so the error of the
-- product centre versus p * q is bounded by C * recipPow2 n, where
--   C = width (embedℚ p) 0 * width (embedℚ q) 0 * half.
--
-- embedℚ 保乘法。term1 以几何级数界住乘积的中心误差。两个嵌入区间
-- 在相应深度的中心恰为各自的有理代表，故乘积中心对两代表乘积的误差
-- 由某个常数乘以 recipPow2 n 控制；该常数由两个嵌入区间的初始宽度
-- 与本模块中的 half 相乘得到。
embedℚ-* : (p q : ℚ) →
  dyadic (p * q) 0 ≈ℝ dyadic p 0 *ℝ dyadic q 0
embedℚ-* p q =
  ≈ℝ-of-rec (dyadic (p * q) 0) (dyadic p 0 *ℝ dyadic q 0) C 0≤C
    λ n →
      let
        cp : ℚ
        cp = centre (dyadic p 0 *ℝ dyadic q 0) n

        c2p : ℚ
        c2p = centre (dyadic p 0) (2 ℕ* n)

        c2q : ℚ
        c2q = centre (dyadic q 0) (2 ℕ* n)

        e-p : c2p ≡ p
        e-p = centre-embedℚ p (2 ℕ* n)

        e-q : c2q ≡ q
        e-q = centre-embedℚ q (2 ℕ* n)

        e-pq : centre (dyadic (p * q) 0) n ≡ p * q
        e-pq = centre-embedℚ (p * q) n

        lhs : ℚ
        lhs = ∣ centre (dyadic (p * q) 0) n - cp ∣

        rhs : ℚ
        rhs = ∣ cp - c2p * c2q ∣

        -- Path in the multiplied argument.
        --
        -- 乘积参数中的路径。
        arg-eq : centre (dyadic (p * q) 0) n ≡ c2p * c2q
        arg-eq = trans e-pq
          (sym (cong₂ _*_ e-p e-q))

        eq : lhs ≡ rhs
        eq = trans (abs-swap (centre (dyadic (p * q) 0) n) cp)
              (cong (λ x → ∣ cp - x ∣) arg-eq)

        bound : rhs ≤ C * recipPow2 n
        bound = term1 (dyadic p 0) (dyadic q 0) n
      in
        subst (λ z → z ≤ C * recipPow2 n) (sym eq) bound
  where
    C : ℚ
    C = width (dyadic p 0) 0 * width (dyadic q 0) 0 * half

    0≤C : 0ℚ ≤ C
    0≤C =
      let
        0≤wp : 0ℚ ≤ width (dyadic p 0) 0
        0≤wp = 0≤width-n (dyadic p 0) 0

        0≤wq : 0ℚ ≤ width (dyadic q 0) 0
        0≤wq = 0≤width-n (dyadic q 0) 0

        0≤wp*wq : 0ℚ ≤ width (dyadic p 0) 0 * width (dyadic q 0) 0
        0≤wp*wq = mul-nonNeg 0≤wp 0≤wq
      in
        mul-nonNeg 0≤wp*wq 0≤half

-- embedℚ respects propositional equality, hence ≈ℝ.
--
-- embedℚ 尊重命题相等，因而尊重 ≈ℝ。
embedℚ-cong : {p q : ℚ} → p ≡ q → dyadic p 0 ≈ℝ dyadic q 0
embedℚ-cong {p} {.p} refl = ≈ℝ-refl
