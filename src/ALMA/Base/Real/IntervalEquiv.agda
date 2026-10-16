------------------------------------------------------------------------
-- Representation equivalence
--
-- From nested-interval reals to Cauchy reals. A nested-interval real
-- determines a Cauchy sequence: take the centre of each successive
-- interval. The interval lengths shrink by at least half at every
-- step, so the centres are Cauchy; the carried modulus is constructed
-- by the Archimedean property of the dyadic scale.
--
-- This is one direction of the representation equivalence between the
-- coinductive interval real and the Cauchy real (both carried instances
-- of ℝ).
--
-- 表示等价
--
-- 从嵌套区间实数到柯西实数。嵌套区间实数确定一条柯西序列：取每个相继
-- 区间的中心。区间长度每步至少减半，故中心序列是柯西的；携带模数由
-- 二进刻度的阿基米德性质构造。
--
-- 这是余归纳区间实数与柯西实数表示等价的一个方向（二者都是携带型 ℝ
-- 的实例）。
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module ALMA.Base.Real.IntervalEquiv where

open import Data.Integer using (+_; -[1+_]; +[1+_]; +0; +<+)
import Data.Integer.Properties
open import Data.Nat using
  (ℕ; zero; suc; _≥_; _^_; z≤n; _∸_; s≤s)
  renaming (_+_ to _+N_; _≤_ to _≤N_; _<_ to _<N_; _*_ to _ℕ*_)
open import Data.Nat.Properties using (*-comm; *-suc)
import Data.Nat.Properties as ℕP
open import Data.Nat.Coprimality using (Coprime)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Data.Sum.Base using (inj₁; inj₂)
open import Data.Rational using
  (ℚ; 0ℚ; 1ℚ; _<_; _≤_; _+_; _-_; _*_; ∣_∣; NonZero; Positive; nonNegative; NonNegative)
open import Data.Rational.Base using (mkℚ; 1/_; _÷_) renaming (-_ to neg)
open import Data.Rational.Properties using
  (≤-reflexive; ≤-refl; ≤-trans; <⇒≤; ≤-<-trans; <-≤-trans; +-mono-<-≤; +-inverseʳ
  ; *-inverseʳ; *-inverseˡ; *-assoc; *-identityˡ; *-identityʳ; pos⇒nonZero
  ; 1/pos⇒pos; pos⇒nonNeg; *-monoʳ-≤-nonNeg; *-monoˡ-≤-nonNeg
  ; pos*pos⇒pos; *-cancelˡ-≤-pos; ≤-antisym; neg-antimono-≤; neg-distrib-+)
open import Data.Rational.Unnormalised.Base as ℚᵘ using (ℚᵘ; mkℚᵘ; *≡*)
open import Data.Rational.Unnormalised.Properties as ℚᵘP using (<-respʳ-≃; <-respˡ-≃)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; trans; sym; cong; cong₂; subst; module ≡-Reasoning)

open import ALMA.Base.Real using (CauchySeq; ε; embed; 2ℚ≡1+1; 2*embed; embed-suc-pos)
open import ALMA.Base.Real.Interval using (RealI; pos-pow)

-- Iterate the nested-interval successor.
--
-- 迭代嵌套区间后继。
node : RealI → ℕ → RealI
node r zero    = r
node r (suc n) = RealI.next (node r n)

node-suc : (r : RealI) (n : ℕ) → node r (suc n) ≡ node (RealI.next r) n
node-suc r zero = refl
node-suc r (suc n) = cong RealI.next (node-suc r n)

l u : RealI → ℕ → ℚ
l r n = RealI.l (node r n)
u r n = RealI.u (node r n)

-- Interval width at level n.
--
-- 第 n 层的区间宽度。
width : RealI → ℕ → ℚ
width r n = u r n - l r n

-- Width at the successor level is at most half.
--
-- 后继层的宽度至多为一半。
width-step : (r : RealI) → width r 1 ≤ width r 0 ÷ embed 2
width-step r = proj₂ (proj₂ (RealI.nest r))

-- Centre of the interval at level n.
--
-- 第 n 层区间的中心。
centre : RealI → ℕ → ℚ
centre r n = (l r n + u r n) ÷ embed 2

-- One-step halving at an arbitrary node.
--
-- 任意节点处的单步减半。
width-1step : (r : RealI) (n : ℕ) → width r (suc n) ≤ width r n ÷ embed 2
width-1step r n = proj₂ (proj₂ (RealI.nest (node r n)))

-- Multiplication by a non-negative factor is monotone.
--
-- 乘以非负因子单调。
mono-half : ∀ {a b} → a ≤ b → a ÷ embed 2 ≤ b ÷ embed 2
mono-half {a} {b} a≤b =
  let half = Data.Rational.Base.1/_ (embed 2) {{pos⇒nonZero (embed 2) {{pos-pow 0}}}}
      halfPos : Positive half
      halfPos = 1/pos⇒pos (embed 2) {{pos-pow 0}}
  in Data.Rational.Properties.*-monoʳ-≤-nonNeg half
       {{pos⇒nonNeg half {{halfPos}}}} a≤b

-- Reciprocal of a product (for positive a, b): ≤ bound.
--
-- 乘积的倒数（a、b 为正）：上界。
recip-prod≤ : (a b : ℚ) → (pa : Positive a) → (pb : Positive b) →
  Data.Rational.Base.1/_ a {{pos⇒nonZero a {{pa}}}}
  * Data.Rational.Base.1/_ b {{pos⇒nonZero b {{pb}}}}
  ≤ Data.Rational.Base.1/_ (a * b)
      {{pos⇒nonZero (a * b) {{Data.Rational.Properties.pos*pos⇒pos a {{pa}} b {{pb}}}}}}
recip-prod≤ a b pa pb =
  let open ≡-Reasoning
      i1 = Data.Rational.Base.1/_ a {{pos⇒nonZero a {{pa}}}}
      i2 = Data.Rational.Base.1/_ b {{pos⇒nonZero b {{pb}}}}
      abPos : Positive (a * b)
      abPos = Data.Rational.Properties.pos*pos⇒pos a {{pa}} b {{pb}}
      invab = Data.Rational.Base.1/_ (a * b) {{pos⇒nonZero (a * b) {{abPos}}}}
      ai1 : a * i1 ≡ 1ℚ
      ai1 = begin
        a * i1
          ≡⟨ Data.Rational.Properties.*-comm a i1 ⟩
        i1 * a
          ≡⟨ *-inverseˡ a {{pos⇒nonZero a {{pa}}}} ⟩
        1ℚ
        ∎
      abi1 : (a * b) * i1 ≡ b
      abi1 = begin
        (a * b) * i1
          ≡⟨ *-assoc a b i1 ⟩
        a * (b * i1)
          ≡⟨ cong (a *_) (Data.Rational.Properties.*-comm b i1) ⟩
        a * (i1 * b)
          ≡⟨ sym (*-assoc a i1 b) ⟩
        (a * i1) * b
          ≡⟨ cong (_* b) ai1 ⟩
        1ℚ * b
          ≡⟨ *-identityˡ b ⟩
        b
        ∎
      abp : (a * b) * (i1 * i2) ≡ 1ℚ
      abp = begin
        (a * b) * (i1 * i2)
          ≡⟨ sym (*-assoc (a * b) i1 i2) ⟩
        ((a * b) * i1) * i2
          ≡⟨ cong (_* i2) abi1 ⟩
        b * i2
          ≡⟨ *-inverseʳ b {{pos⇒nonZero b {{pb}}}} ⟩
        1ℚ
        ∎
      abq : (a * b) * invab ≡ 1ℚ
      abq = *-inverseʳ (a * b) {{pos⇒nonZero (a * b) {{abPos}}}}
      p≤q : (a * b) * (i1 * i2) ≤ (a * b) * invab
      p≤q = ≤-reflexive (trans abp (sym abq))
  in Data.Rational.Properties.*-cancelˡ-≤-pos (a * b) {{abPos}} p≤q

-- Powers of two as rationals.
--
-- 二的幂作为有理数。
pow2 : ℕ → ℚ
pow2 n = embed (2 ^ n)

posPow2 : (n : ℕ) → Positive (pow2 n)
posPow2 zero    = record { }
posPow2 (suc n) = pos-pow n

0<2^n : (n : ℕ) → 0 <N 2 ^ n
0<2^n zero    = s≤s z≤n
0<2^n (suc n) = ℕP.≤-trans (s≤s z≤n) (ℕP.*-monoʳ-≤ 2 (0<2^n n))

-- suc (n ∸ 1) ≡ n for n > 0.
--
-- 当 n > 0 时，suc (n ∸ 1) ≡ n。
suc∸1 : {n : ℕ} → 0 <N n → suc (n ∸ 1) ≡ n
suc∸1 {n} 0<n =
  trans (ℕP.+-comm 1 (n ∸ 1))
        (ℕP.m∸n+n≡m 0<n)

-- Denominator identity: (2^n) * 2 = 2^(suc n).
--
-- 分母恒等式：(2^n) * 2 = 2^(suc n)。
denom-eq : (n : ℕ) → pow2 n * pow2 1 ≡ pow2 (suc n)
denom-eq n =
  trans (Data.Rational.Properties.*-comm (pow2 n) (embed 2))
        (2*embed (2 ^ n))

-- Reciprocal of a power of two: 1 / 2^n, written as 1/embed (suc d)
-- with d = 2^n ∸ 1 so that it matches the prod-eq normalizer.
--
-- 二的幂的倒数：1 / 2^n，写作 1/embed (suc d)，d = 2^n ∸ 1，
-- 以便与 prod-eq 归一化器对齐。
recipPow2 : ℕ → ℚ
recipPow2 n =
  let d = 2 ^ n Data.Nat.∸ 1
  in Data.Rational.Base.1/_ (embed (suc d))
       ⦃ pos⇒nonZero (embed (suc d)) ⦃ embed-suc-pos ⦄ ⦄

-- Geometric shrinking of the width.
--
-- 宽度的几何收缩。
width-nV : RealI → ℕ → ℚ
width-nV r n = width r 0 * recipPow2 n

width-n : (r : RealI) (n : ℕ) →
  width r n ≤ width-nV r n
width-n r zero =
  ≤-reflexive (sym (*-identityʳ (width r 0)))
width-n r (suc n) =
  let open ≡-Reasoning
      w0 = width r 0
      an = 2 ^ n Data.Nat.∸ 1
      a1 = 2 ^ 1 Data.Nat.∸ 1
      as = 2 ^ suc n Data.Nat.∸ 1
      A = embed (suc an)
      B = embed (suc a1)
      S = embed (suc as)
      hn = recipPow2 n
      h1 = recipPow2 1
      hs = recipPow2 (suc n)
      w0nn : NonNegative w0
      w0nn = nonNegative
        (≤-trans (≤-reflexive (sym (+-inverseʳ (l r 0))))
                 (Data.Rational.Properties.+-mono-≤ (<⇒≤ (RealI.lo r)) (≤-refl)))
      h1nn : NonNegative h1
      h1nn = pos⇒nonNeg h1 {{1/pos⇒pos B {{embed-suc-pos}}}}
      step1 : width r (suc n) ≤ width r n * h1
      step1 = width-1step r n
      step2 : width r n * h1 ≤ (w0 * hn) * h1
      step2 = Data.Rational.Properties.*-monoʳ-≤-nonNeg h1 {{h1nn}} (width-n r n)
      step3 : (w0 * hn) * h1 ≤ w0 * (hn * h1)
      step3 = ≤-reflexive (*-assoc w0 hn h1)
      step4 : w0 * (hn * h1) ≤ w0 * hs
      step4 =
        let prod = A * B
            prodPos : Positive prod
            prodPos = Data.Rational.Properties.pos*pos⇒pos A {{embed-suc-pos}} B {{embed-suc-pos}}
            invprod = Data.Rational.Base.1/_ prod {{pos⇒nonZero prod {{prodPos}}}}
            s41 : w0 * (hn * h1) ≤ w0 * invprod
            s41 = Data.Rational.Properties.*-monoˡ-≤-nonNeg w0 {{w0nn}}
                    (recip-prod≤ A B embed-suc-pos embed-suc-pos)
            ab1 : prod * invprod ≡ 1ℚ
            ab1 = *-inverseʳ prod {{pos⇒nonZero prod {{prodPos}}}}
            ab2 : S * hs ≡ 1ℚ
            ab2 = *-inverseʳ S {{pos⇒nonZero S {{embed-suc-pos}}}}
            A≡ : A ≡ pow2 n
            A≡ = cong embed (suc∸1 (0<2^n n))
            B≡ : B ≡ pow2 1
            B≡ = cong embed (suc∸1 (0<2^n 1))
            S≡ : S ≡ pow2 (suc n)
            S≡ = cong embed (suc∸1 (0<2^n (suc n)))
            prod≡S : prod ≡ S
            prod≡S = begin
              A * B
                ≡⟨ cong (A *_) B≡ ⟩
              A * pow2 1
                ≡⟨ cong (_* pow2 1) A≡ ⟩
              pow2 n * pow2 1
                ≡⟨ denom-eq n ⟩
              pow2 (suc n)
                ≡⟨ sym S≡ ⟩
              S
                ∎
            ab2' : prod * hs ≡ 1ℚ
            ab2' = trans (cong (λ d → d * hs) prod≡S) ab2
            le : prod * invprod ≤ prod * hs
            le = ≤-reflexive (trans ab1 (sym ab2'))
            ge : prod * hs ≤ prod * invprod
            ge = ≤-reflexive (trans ab2' (sym ab1))
            p≤q : invprod ≤ hs
            p≤q = Data.Rational.Properties.*-cancelˡ-≤-pos prod {{prodPos}} le
            q≤p : hs ≤ invprod
            q≤p = Data.Rational.Properties.*-cancelˡ-≤-pos prod {{prodPos}} ge
            inv-eq : invprod ≡ hs
            inv-eq = Data.Rational.Properties.≤-antisym p≤q q≤p
            s42 : w0 * invprod ≡ w0 * hs
            s42 = cong (λ z → w0 * z) inv-eq
        in ≤-trans s41 (≤-reflexive s42)
  in ≤-trans step1 (≤-trans step2 (≤-trans step3 step4))

-- The centre lies inside the interval: l ≤ centre.
--
-- 中心落在区间内：l ≤ centre。
centre-l : (r : RealI) (n : ℕ) → l r n ≤ centre r n
centre-l r n =
  let open ≡-Reasoning
      l′ = l r n; u′ = u r n
      half = Data.Rational.Base.1/_ (embed 2) {{pos⇒nonZero (embed 2) {{pos-pow 0}}}}
      2h : embed 2 * half ≡ 1ℚ
      2h = *-inverseʳ (embed 2) {{pos⇒nonZero (embed 2) {{pos-pow 0}}}}
      2l : embed 2 * l′ ≡ l′ + l′
      2l = begin
        embed 2 * l′
          ≡⟨ cong (λ z → z * l′) (sym 2ℚ≡1+1) ⟩
        (1ℚ + 1ℚ) * l′
          ≡⟨ Data.Rational.Properties.*-distribʳ-+ l′ 1ℚ 1ℚ ⟩
        1ℚ * l′ + 1ℚ * l′
          ≡⟨ cong (λ z → z + 1ℚ * l′) (Data.Rational.Properties.*-identityˡ l′) ⟩
        l′ + 1ℚ * l′
          ≡⟨ cong (λ z → l′ + z) (Data.Rational.Properties.*-identityˡ l′) ⟩
        l′ + l′
        ∎
      l≤u : l′ ≤ u′
      l≤u = <⇒≤ (RealI.lo (node r n))
      ineq : embed 2 * l′ ≤ l′ + u′
      ineq =
        ≤-trans (≤-reflexive 2l)
        (Data.Rational.Properties.+-mono-≤ (≤-refl {l′}) l≤u)
      mono : (embed 2 * l′) * half ≤ (l′ + u′) * half
      mono = Data.Rational.Properties.*-monoʳ-≤-nonNeg half
               {{pos⇒nonNeg half {{1/pos⇒pos (embed 2) {{pos-pow 0}}}}}} ineq
      chain : (embed 2 * l′) * half ≡ l′
      chain = begin
        (embed 2 * l′) * half
          ≡⟨ Data.Rational.Properties.*-assoc (embed 2) l′ half ⟩
        embed 2 * (l′ * half)
          ≡⟨ cong (λ z → embed 2 * z)
                   (Data.Rational.Properties.*-comm l′ half) ⟩
        embed 2 * (half * l′)
          ≡⟨ sym (Data.Rational.Properties.*-assoc (embed 2) half l′) ⟩
        (embed 2 * half) * l′
          ≡⟨ cong (λ z → z * l′) 2h ⟩
        1ℚ * l′
          ≡⟨ Data.Rational.Properties.*-identityˡ l′ ⟩
        l′
        ∎
      lhs : l′ ≡ (embed 2 * l′) * half
      lhs = sym chain
  in ≤-trans (≤-reflexive lhs) mono

-- The centre lies inside the interval: centre ≤ u.
--
-- 中心落在区间内：centre ≤ u。
centre-u : (r : RealI) (n : ℕ) → centre r n ≤ u r n
centre-u r n =
  let open ≡-Reasoning
      l′ = l r n; u′ = u r n
      half = Data.Rational.Base.1/_ (embed 2) {{pos⇒nonZero (embed 2) {{pos-pow 0}}}}
      2h : embed 2 * half ≡ 1ℚ
      2h = *-inverseʳ (embed 2) {{pos⇒nonZero (embed 2) {{pos-pow 0}}}}
      2u : embed 2 * u′ ≡ u′ + u′
      2u = begin
        embed 2 * u′
          ≡⟨ cong (λ z → z * u′) (sym 2ℚ≡1+1) ⟩
        (1ℚ + 1ℚ) * u′
          ≡⟨ Data.Rational.Properties.*-distribʳ-+ u′ 1ℚ 1ℚ ⟩
        1ℚ * u′ + 1ℚ * u′
          ≡⟨ cong (λ z → z + 1ℚ * u′) (Data.Rational.Properties.*-identityˡ u′) ⟩
        u′ + 1ℚ * u′
          ≡⟨ cong (λ z → u′ + z) (Data.Rational.Properties.*-identityˡ u′) ⟩
        u′ + u′
        ∎
      l≤u : l′ ≤ u′
      l≤u = <⇒≤ (RealI.lo (node r n))
      ineq : l′ + u′ ≤ embed 2 * u′
      ineq =
        ≤-trans (Data.Rational.Properties.+-mono-≤ l≤u (≤-refl {u′}))
                (≤-reflexive (sym 2u))
      mono : (l′ + u′) * half ≤ (embed 2 * u′) * half
      mono = Data.Rational.Properties.*-monoʳ-≤-nonNeg half
               {{pos⇒nonNeg half {{1/pos⇒pos (embed 2) {{pos-pow 0}}}}}} ineq
      chain : (embed 2 * u′) * half ≡ u′
      chain = begin
        (embed 2 * u′) * half
          ≡⟨ Data.Rational.Properties.*-assoc (embed 2) u′ half ⟩
        embed 2 * (u′ * half)
          ≡⟨ cong (λ z → embed 2 * z)
                   (Data.Rational.Properties.*-comm u′ half) ⟩
        embed 2 * (half * u′)
          ≡⟨ sym (Data.Rational.Properties.*-assoc (embed 2) half u′) ⟩
        (embed 2 * half) * u′
          ≡⟨ cong (λ z → z * u′) 2h ⟩
        1ℚ * u′
          ≡⟨ Data.Rational.Properties.*-identityˡ u′ ⟩
        u′
        ∎
      final : (l′ + u′) * half ≤ u′
      final = ≤-trans mono (≤-reflexive chain)
  in final

-- One-step monotonicity of the lower and upper endpoints.
--
-- 下端点与上端点的单步单调性。
l-step : (r : RealI) → RealI.l r ≤ RealI.l (RealI.next r)
l-step r = proj₁ (RealI.nest r)

u-step : (r : RealI) → RealI.u (RealI.next r) ≤ RealI.u r
u-step r = proj₁ (proj₂ (RealI.nest r))

-- Iterated monotonicity: n ≤ m implies l n ≤ l m.
--
-- 迭代单调性：n ≤ m 蕴含 l n ≤ l m。
l-mono0 : (r : RealI) (m : ℕ) → RealI.l r ≤ RealI.l (node r m)
l-mono0 r zero    = ≤-refl
l-mono0 r (suc m) = ≤-trans (l-mono0 r m) (l-step (node r m))

l-mono : (r : RealI) → {n m : ℕ} → n ≤N m →
  RealI.l (node r n) ≤ RealI.l (node r m)
l-mono r {m = m} z≤n = l-mono0 r m
l-mono r {suc n} {suc m} (s≤s p) =
  ≤-trans (≤-reflexive (cong RealI.l (node-suc r n)))
  (≤-trans (l-mono (RealI.next r) p)
           (≤-reflexive (cong RealI.l (sym (node-suc r m)))))

u-mono0 : (r : RealI) (m : ℕ) → RealI.u (node r m) ≤ RealI.u r
u-mono0 r zero    = ≤-refl
u-mono0 r (suc m) = ≤-trans (u-step (node r m)) (u-mono0 r m)

u-mono : (r : RealI) → {n m : ℕ} → n ≤N m →
  RealI.u (node r m) ≤ RealI.u (node r n)
u-mono r {m = m} z≤n = u-mono0 r m
u-mono r {suc n} {suc m} (s≤s p) =
  ≤-trans (≤-reflexive (cong RealI.u (node-suc r m)))
  (≤-trans (u-mono (RealI.next r) p)
           (≤-reflexive (cong RealI.u (sym (node-suc r n)))))

-- A centre at a deeper level lies in a shallower interval.
--
-- 较深层的中心落在较浅的区间内。
centre-in-l : (r : RealI) {n m : ℕ} → n ≤N m → l r n ≤ centre r m
centre-in-l r {n} {m} p = ≤-trans (l-mono r p) (centre-l r m)

centre-in-u : (r : RealI) {n m : ℕ} → n ≤N m → centre r m ≤ u r n
centre-in-u r {n} {m} p = ≤-trans (centre-u r m) (u-mono r p)

-- z := x - y lies inside [ -(u-l), u-l ].
--
-- z := x - y 落在 [ -(u-l), u-l ] 内。
diff+ : {x y l u : ℚ} →
  l ≤ x → x ≤ u → l ≤ y → y ≤ u → (x - y) ≤ (u - l)
diff+ {x} {y} {l} {u} lx xu ly yu =
  ≤-trans (Data.Rational.Properties.+-mono-≤ xu (≤-refl { Data.Rational.Base.- y}))
          (Data.Rational.Properties.+-mono-≤ (≤-refl {u})
             (Data.Rational.Properties.neg-antimono-≤ ly))

-- Double negation on the fraction (matches the three neg branches).
--
-- 分式上的双重取负（对应三个取负分支）。
negneg : ∀ p → Data.Rational.Base.- (Data.Rational.Base.- p) ≡ p
negneg (mkℚ -[1+ n ] d c) = refl
negneg (mkℚ +[1+ n ] d c) = refl
negneg (mkℚ +0 d c) = refl

negsub : ∀ x y → Data.Rational.Base.- (x - y) ≡ y - x
negsub x y =
  begin
    Data.Rational.Base.- (x - y)
  ≡⟨ refl ⟩
    Data.Rational.Base.- (x + Data.Rational.Base.- y)
  ≡⟨ Data.Rational.Properties.neg-distrib-+ x (Data.Rational.Base.- y) ⟩
    neg x + Data.Rational.Base.- (Data.Rational.Base.- y)
  ≡⟨ cong (λ z → neg x + z) (negneg y) ⟩
    neg x + y
  ≡⟨ Data.Rational.Properties.+-comm (Data.Rational.Base.- x) y ⟩
    y + neg x
  ≡⟨ refl ⟩
    y - x
  ∎
  where open Relation.Binary.PropositionalEquality.≡-Reasoning

diff- : {x y l u : ℚ} →
  l ≤ x → x ≤ u → l ≤ y → y ≤ u → Data.Rational.Base.- (x - y) ≤ (u - l)
diff- {x} {y} {l} {u} lx xu ly yu =
  ≤-trans (Data.Rational.Properties.≤-reflexive (negsub x y))
  (≤-trans (Data.Rational.Properties.+-mono-≤ yu (≤-refl { Data.Rational.Base.- x}))
           (Data.Rational.Properties.+-mono-≤ (≤-refl {u})
              (Data.Rational.Properties.neg-antimono-≤ lx)))

-- Two points inside [l, u] differ by at most the width.
--
-- [l, u] 内两点之差至多为宽度。
bounded-diff : {x y l u : ℚ} →
  l ≤ x → x ≤ u → l ≤ y → y ≤ u → ∣ x - y ∣ ≤ u - l
bounded-diff {x} {y} {l} {u} lx xu ly yu
  with Data.Rational.Properties.∣p∣≡p∨∣p∣≡-p (x - y)
...  | inj₁ abs≡ =
  ≤-trans (≤-reflexive abs≡) (diff+ lx xu ly yu)
...  | inj₂ abs≡ =
  ≤-trans (≤-reflexive abs≡) (diff- lx xu ly yu)

-- Centres of two levels both reachable from t differ by at most width t.
--
-- 从 t 可达的两层之中心，其差至多为 width t。
centre-diff : (r : RealI) (t a b : ℕ) →
  t ≤N a → t ≤N b → ∣ centre r a - centre r b ∣ ≤ width r t
centre-diff r t a b ta tb =
  bounded-diff (centre-in-l r ta) (centre-in-u r ta)
               (centre-in-l r tb) (centre-in-u r tb)

-- And width r t ≤ width-n r t.
--
-- 且 width r t ≤ width-n r t。
centre-diff≤ : (r : RealI) (t a b : ℕ) →
  t ≤N a → t ≤N b → ∣ centre r a - centre r b ∣ ≤ width-nV r t
centre-diff≤ r t a b ta tb =
  ≤-trans (centre-diff r t a b ta tb) (width-n r t)

------------------------------------------------------------------------
-- Nat growth of powers of two
--
-- 二的幂的自然数增长

2m : ∀ m → 2 ℕ* m ≡ m +N m
2m m = begin
  2 ℕ* m
    ≡⟨ *-comm 2 m ⟩
  m ℕ* 2
    ≡⟨ *-suc m 1 ⟩
  m +N (m ℕ* 1)
    ≡⟨ cong (m +N_) (Data.Nat.Properties.*-identityʳ m) ⟩
  m +N m
  ∎
  where open ≡-Reasoning

pp : ∀ n → 2 ^ suc n ≡ 2 ℕ* (2 ^ n)
pp n = refl

qq : ∀ n → 2 ^ n +N 2 ^ n ≡ 2 ^ suc n
qq n = begin
  2 ^ n +N 2 ^ n
    ≡⟨ sym (2m (2 ^ n)) ⟩
  2 ℕ* (2 ^ n)
    ≡⟨ sym (pp n) ⟩
  2 ^ suc n
  ∎
  where open ≡-Reasoning

pow≤ : ∀ n → 2 ^ n ≤N 2 ^ suc n
pow≤ n =
  Data.Nat.Properties.≤-trans (Data.Nat.Properties.m≤n+m (2 ^ n) (2 ^ n))
                              (Data.Nat.Properties.≤-reflexive (qq n))

1≤2^n : ∀ n → 1 ≤N 2 ^ n
1≤2^n zero    = Data.Nat.Properties.≤-refl
1≤2^n (suc n) = Data.Nat.Properties.≤-trans (1≤2^n n) (pow≤ n)

-- 1/q ≤ 1 whenever 1 ≤ q.
--
-- 当 1 ≤ q 时，1/q ≤ 1。
1≤⇒Positive : (q : ℚ) → 1ℚ ≤ q → Positive q
1≤⇒Positive q 1≤q =
  Data.Rational.Base.positive
    (Data.Rational.Properties.<-≤-trans (0<1) 1≤q)
  where
    0<1 : 0ℚ < 1ℚ
    0<1 = Data.Rational.Base.*<*
            (Data.Integer.+<+ (s≤s z≤n))

recip≤1 : (q : ℚ) → 1ℚ ≤ q → (nz : NonZero q) →
  Data.Rational.Base.1/_ q {{nz}} ≤ 1ℚ
recip≤1 q 1≤q nz =
  let r = Data.Rational.Base.1/_ q {{nz}}
      pq : Positive q
      pq = 1≤⇒Positive q 1≤q
  in
  begin
    r
    ≡⟨ sym (Data.Rational.Properties.*-identityʳ r) ⟩
    r * 1ℚ
    ≤⟨ Data.Rational.Properties.*-monoˡ-≤-nonNeg r
          {{pos⇒nonNeg r {{1/pos⇒pos q {{pq}}}}}} 1≤q ⟩
      r * q
    ≡⟨ Data.Rational.Properties.*-inverseˡ q {{nz}} ⟩
      1ℚ
    ∎
  where open Data.Rational.Properties.≤-Reasoning
        open Data.Rational.Base using (1/_)

1≤embed-suc : (d : ℕ) → 1ℚ ≤ embed (suc d)
1≤embed-suc d =
  Data.Rational.Base.*≤*
    (Data.Integer.+≤+ (Data.Nat.s≤s Data.Nat.z≤n))

-- embed M is nonnegative.
--
-- embed M 非负。
nonNeg-embed : (M : ℕ) → NonNegative (embed M)
nonNeg-embed zero    = nonNegative (≤-refl)
  where open Data.Rational using (nonNegative)
nonNeg-embed (suc n) =
  pos⇒nonNeg (embed (suc n)) {{embed-suc-pos}}

-- embed M ÷ embed (suc d) ≤ embed M.
--
-- embed M ÷ embed (suc d) ≤ embed M。
frac≤ : (M d : ℕ) →
  let p = embed M
      q = embed (suc d)
      pq : Positive q
      pq = embed-suc-pos
      nz : NonZero q
      nz = pos⇒nonZero q {{pq}}
  in
  p * Data.Rational.Base.1/_ q {{nz}} ≤ p
frac≤ M d =
  let p = embed M
      q = embed (suc d)
      pq : Positive q
      pq = embed-suc-pos
  in
  begin
    p * Data.Rational.Base.1/_ q {{pos⇒nonZero q {{pq}}}}
    ≤⟨ Data.Rational.Properties.*-monoˡ-≤-nonNeg p
          {{nonNeg-embed M}} (recip≤1 q (1≤embed-suc d) (pos⇒nonZero q {{pq}})) ⟩
    p * 1ℚ
    ≡⟨ Data.Rational.Properties.*-identityʳ p ⟩
    p
    ∎
  where open Data.Rational.Properties.≤-Reasoning

-- The product embed M * (1/embed (suc d)) reduces to normalize M (suc d).
--
-- 乘积 embed M * (1/embed (suc d)) 归约为 normalize M (suc d)。
prod-eq : (M d : ℕ) →
  embed M * Data.Rational.Base.1/_ (embed (suc d))
              {{pos⇒nonZero (embed (suc d)) {{embed-suc-pos}}}}
  ≡ Data.Rational.Base.normalize M (suc d)
prod-eq M d =
  Data.Rational.Properties./-cong
    (Data.Integer.Properties.*-identityʳ (+ M))
    (Data.Nat.Properties.*-identityˡ (suc d))

-- The literal fraction mkℚ (+M) d equals the normalized product.
--
-- 字面分式 mkℚ (+M) d 等于规范化乘积。
frac-term-eq : (M d : ℕ) → .(c : Coprime M (suc d)) →
  mkℚ (+ M) d c
  ≡ embed M * Data.Rational.Base.1/_ (embed (suc d))
                {{pos⇒nonZero (embed (suc d)) {{embed-suc-pos}}}}
frac-term-eq M d c =
  trans (sym (Data.Rational.Properties.normalize-coprime c)) (sym (prod-eq M d))

-- Any nonnegative rational w is bounded by embed of a natural.
--
-- 任何非负有理数 w 都被某个自然数的 embed 上界。
bound-w : (w : ℚ) → 0ℚ ≤ w → Σ ℕ (λ M → w ≤ embed M)
bound-w (mkℚ (+ M) d c) _ =
  M , (≤-trans (≤-reflexive (frac-term-eq M d c)) (frac≤ M d))
bound-w (mkℚ -[1+ n ] d c) (Data.Rational.Base.*≤* le) with le
... | ()

-- 2^n < 2^(suc n) strictly.
--
-- 2^n < 2^(suc n)，严格。
pow< : (n : ℕ) → 2 ^ n <N 2 ^ suc n
pow< n =
  Data.Nat.Properties.<-≤-trans
    (Data.Nat.Properties.m<n+m (2 ^ n) {n = 2 ^ n} (0<2^n n))
    (Data.Nat.Properties.≤-reflexive (qq n))

-- n < 2^n for every natural n.
--
-- 对每个自然数 n，n < 2^n。
n<2^n : (n : ℕ) → n <N 2 ^ n
n<2^n zero    = s≤s z≤n
n<2^n (suc n) =
  Data.Nat.Properties.≤-<-trans (n<2^n n) (pow< n)

-- B < 2^(suc B), giving a strict modulus.
--
-- B < 2^(suc B)，给出严格模数。
B<2^sucB : (B : ℕ) → B <N 2 ^ suc B
B<2^sucB B =
  Data.Nat.Properties.<-trans (n<2^n B) (pow< B)

-- embed preserves strict inequalities.
--
-- embed 保持严格不等式。
embed-mono-< : ∀ {m n} → m <N n → embed m < embed n
embed-mono-< {m} {n} h =
  Data.Rational.Base.*<*
    (Data.Integer.Properties.<-≤-trans
       (Data.Integer.Properties.≤-<-trans
          (Data.Integer.Properties.≤-reflexive
             (Data.Integer.Properties.*-identityʳ (+ m)))
          (Data.Integer.+<+ h))
       (Data.Integer.Properties.≤-reflexive
          (sym (Data.Integer.Properties.*-identityʳ (+ n)))))

pos-2^t : (t : ℕ) → Positive (embed (2 ^ t))
pos-2^t t = Data.Rational.Base.positive (embed-mono-< (0<2^n t))

recip2^t : (t : ℕ) → ℚ
recip2^t = recipPow2

rawL : (M t : ℕ) → ℚᵘ
rawL M t = mkℚᵘ (+ M) (2 ^ t Data.Nat.∸ 1)

rawR : (k : ℕ) → ℚᵘ
rawR k = mkℚᵘ (+ 1) k

recip-suc : (k : ℕ) → ℚ
recip-suc k = ε k

nz-2^t : (t : ℕ) → Data.Nat.NonZero (2 ^ t)
nz-2^t t =
  Data.Nat.≢-nonZero
    (Relation.Binary.PropositionalEquality.≢-sym
       (Data.Nat.Properties.<⇒≢ (0<2^n t)))

fracL : (M t : ℕ) → ℚ
fracL M t = Data.Rational.fromℚᵘ (rawL M t)

prod≡fracL : (M t : ℕ) → embed M * recip2^t t ≡ fracL M t
prod≡fracL M t = prod-eq M (2 ^ t Data.Nat.∸ 1)

flip-≃ : {a b : ℚᵘ} → ℚᵘ._≃_ a b → ℚᵘ._≃_ b a
flip-≃ (ℚᵘ.*≡* e) = ℚᵘ.*≡* (sym e)

fracL-strict : (M k t : ℕ) →
  (M ℕ* suc k) <N 2 ^ t →
  fracL M t < recip-suc k
fracL-strict M k t h =
  Data.Rational.Properties.toℚᵘ-cancel-<
    (let crossℚᵘ : ℚᵘ._<_ (rawL M t) (rawR k)
         crossℚᵘ = ℚᵘ.*<* (rawCross h)
         eqL : ℚᵘ._≃_ (Data.Rational.toℚᵘ (fracL M t)) (rawL M t)
         eqL = Data.Rational.Properties.toℚᵘ-fromℚᵘ (rawL M t)
         eqR : ℚᵘ._≃_ (Data.Rational.toℚᵘ (recip-suc k)) (rawR k)
         eqR = ℚᵘP.≃-reflexive refl
         p1 : ℚᵘ._<_ (Data.Rational.toℚᵘ (fracL M t)) (rawR k)
         p1 = ℚᵘP.<-respˡ-≃ (flip-≃ eqL) crossℚᵘ
         p2 : ℚᵘ._<_ (Data.Rational.toℚᵘ (fracL M t))
                       (Data.Rational.toℚᵘ (recip-suc k))
         p2 = ℚᵘP.<-respʳ-≃ (flip-≃ eqR) p1
     in p2)
  where
    open ≡-Reasoning
    d : ℕ
    d = 2 ^ t Data.Nat.∸ 1
    d-eq : suc d ≡ 2 ^ t
    d-eq = begin
      suc d
        ≡⟨ Data.Nat.Properties.+-comm 1 d ⟩
      d +N 1
        ≡⟨ Data.Nat.Properties.m∸n+n≡m (0<2^n t) ⟩
      2 ^ t
      ∎
    rawCross :
      (M ℕ* suc k) <N 2 ^ t →
      ((+ M) Data.Integer.* (+ suc k))
      Data.Integer.<
      ((+ 1) Data.Integer.* (+ suc d))
    rawCross h =
      Data.Integer.Properties.<-≤-trans
        (Data.Integer.Properties.≤-<-trans
           (Data.Integer.Properties.≤-reflexive
              (Data.Integer.Properties.+◃n≡+n (M ℕ* suc k)))
           (Data.Integer.Properties.<-≤-trans
              (Data.Integer.+<+ h)
              (Data.Integer.Properties.≤-reflexive
                 (cong (+_) (sym d-eq)))))
        (Data.Integer.Properties.≤-reflexive
           (sym (Data.Integer.Properties.*-identityˡ (+ suc d))))

-- embed M * (1/embed (2^t)) < 1/embed (suc k) whenever M*(suc k) < 2^t.
--
-- 当 M*(suc k) < 2^t 时，embed M * (1/embed (2^t)) < 1/embed (suc k)。
frac-strict : (M k t : ℕ) →
  (M ℕ* suc k) <N 2 ^ t →
  embed M * recip2^t t < recip-suc k
frac-strict M k t h =
  Data.Rational.Properties.≤-<-trans
    (Data.Rational.Properties.≤-reflexive (prod≡fracL M t))
    (fracL-strict M k t h)

-- 0 < width r 0 (the initial interval is non-degenerate).
--
-- 0 < width r 0（初始区间非退化）。
0<width : (r : RealI) → 0ℚ < width r 0
0<width r =
  Data.Rational.Properties.≤-<-trans
    (Data.Rational.Properties.≤-reflexive
       (sym (Data.Rational.Properties.+-inverseʳ (RealI.l r))))
    (Data.Rational.Properties.+-mono-<-≤
       (RealI.lo r) (Data.Rational.Properties.≤-refl))

-- The carried modulus construction: the centre of each nested interval
-- is a Cauchy sequence.
--
-- 携带模数构造：每个嵌套区间的中心构成柯西序列。
realI→cauchy : RealI → CauchySeq
realI→cauchy r = record
  { f = centre r
  ; μ = μ
  ; cauchy = cauchy
  }
  where
    w0 = width r 0
    0≤w0 : 0ℚ ≤ w0
    0≤w0 = Data.Rational.Properties.<⇒≤ (0<width r)
    M = proj₁ (bound-w w0 0≤w0)
    w0≤M : w0 ≤ embed M
    w0≤M = proj₂ (bound-w w0 0≤w0)

    μ : ℕ → ℕ
    μ k = suc (M ℕ* suc k)

    recip2^t-pos : (t : ℕ) → Positive (recip2^t t)
    recip2^t-pos t =
      let d = 2 ^ t Data.Nat.∸ 1
      in 1/pos⇒pos (embed (suc d))
           ⦃ embed-suc-pos ⦄

    step2 : (t : ℕ) → width-nV r t ≤ embed M * recip2^t t
    step2 t =
      Data.Rational.Properties.*-monoʳ-≤-nonNeg
        (recip2^t t)
        {{pos⇒nonNeg (recip2^t t) {{recip2^t-pos t}}}}
        w0≤M

    cauchy : ∀ k n m → n ≥ μ k → m ≥ μ k →
      ∣ centre r n - centre r m ∣ < ε k
    cauchy k n m n≥μ m≥μ =
      let t = μ k in
      Data.Rational.Properties.≤-<-trans
        (centre-diff≤ r t n m n≥μ m≥μ)
        (Data.Rational.Properties.≤-<-trans
           (step2 t)
           (frac-strict M k t (B<2^sucB (M ℕ* suc k))))
