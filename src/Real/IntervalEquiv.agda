------------------------------------------------------------------------
-- Representation equivalence
--
-- 表示等价
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module Real.IntervalEquiv where

open import Data.Integer using (+_; -[1+_]; +≤+)
import Data.Integer.Properties as ℤP
open import Data.Nat using (ℕ; zero; suc; _≥_; _^_; _∸_; z≤n; s≤s; ≢-nonZero)
  renaming (_+_ to _+N_; _≤_ to _≤N_; _<_ to _<N_; _*_ to _ℕ*_; NonZero to ℕNonZero)
open import Data.Nat.Properties using (*-suc; n≤1+n; *-mono-≤; ^-monoʳ-≤)
  renaming (≤-trans to ≤ℕ-trans; ≤-refl to ≤ℕ-refl)
import Data.Nat.Properties as ℕP
open import Data.Nat.Coprimality using (Coprime; 1-coprimeTo)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Data.Sum.Base using (inj₁; inj₂)
open import Data.Rational using
  (ℚ; 0ℚ; 1ℚ; _<_; _≤_; _+_; _-_; _*_; ∣_∣; NonZero; Positive; nonNegative
  ; NonNegative; fromℚᵘ) renaming (-_ to neg)
open import Data.Rational.Base using (mkℚ; _÷_; 1/_; normalize; positive; *≤*)
open import Data.Rational.Properties using
  (≤-reflexive; ≤-refl; ≤-trans; <⇒≤; <-≤-trans; ≤-<-trans; +-inverseʳ
  ; +-mono-≤; *-assoc; *-comm; *-identityˡ; *-identityʳ; *-inverseˡ; *-inverseʳ
  ; *-distribʳ-+; *-monoˡ-≤-nonNeg; *-monoʳ-≤-nonNeg; pos⇒nonZero; pos⇒nonNeg
  ; pos*pos⇒pos; 1/pos⇒pos; neg-antimono-≤; ∣p∣≡p∨∣p∣≡-p; /-cong
  ; normalize-coprime; mkℚ-cong; module ≤-Reasoning)
open import Data.Rational.Unnormalised.Base using (ℚᵘ; mkℚᵘ)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; trans; sym; cong; subst; ≢-sym; module ≡-Reasoning)

open import Base.RationalRing using (0<1)
open import Real using
  (CauchySeq; ε; embed; 2ℚ≡1+1; 2*embed; embed-suc-pos; embed-pos→≥1
  ; embed-mono-<; reciprocal-cong)
open CauchySeq
open import Real.Interval using (RealI; pos-pow)
open import Real.Interval.Rational using
  (rawR; suc∸1; 0<2^t; negsub; pos-diff; recip-*-hom; combFrac; comb-strict)

-- Iterate the nested-interval successor.
--
-- 迭代嵌套区间后继。
node : RealI → ℕ → RealI
node r zero    = r
node r (suc n) = RealI.next (node r n)

-- Advancing the successor once and then iterating n times equals
-- iterating n times from the successor.
--
-- 先取一次后继再迭代 n 次，等于从后继出发迭代 n 次。
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
  let half = 1/_ (embed 2) {{pos⇒nonZero (embed 2) {{pos-pow 0}}}}
      halfPos : Positive half
      halfPos = 1/pos⇒pos (embed 2) {{pos-pow 0}}
  in *-monoʳ-≤-nonNeg half {{pos⇒nonNeg half {{halfPos}}}} a≤b

-- Reciprocal of a product (for positive a, b): ≤ bound.
--
-- 乘积的倒数（a、b 为正）：上界。
recip-prod≤ : (a b : ℚ) → (pa : Positive a) → (pb : Positive b) →
  1/_ a {{pos⇒nonZero a {{pa}}}}
  * 1/_ b {{pos⇒nonZero b {{pb}}}}
  ≤ 1/_ (a * b)
      {{pos⇒nonZero (a * b) {{pos*pos⇒pos a {{pa}} b {{pb}}}}}}
recip-prod≤ a b pa pb =
  ≤-reflexive (sym (recip-*-hom a b
    ⦃ pos⇒nonZero a {{pa}} ⦄
    ⦃ pos⇒nonZero b {{pb}} ⦄
    ⦃ pos⇒nonZero (a * b) {{pos*pos⇒pos a {{pa}} b {{pb}}}} ⦄))

-- Powers of two as rationals.
--
-- 二的幂作为有理数。
pow2 : ℕ → ℚ
pow2 n = embed (2 ^ n)

posPow2 : (n : ℕ) → Positive (pow2 n)
posPow2 zero    = embed-suc-pos {0}
posPow2 (suc n) = pos-pow n

-- Denominator identity for the dyadic scale.
--
-- 二进刻度的分母恒等式。
denom-eq : (n : ℕ) → pow2 n * pow2 1 ≡ pow2 (suc n)
denom-eq n =
  trans (*-comm (pow2 n) (embed 2))
        (2*embed (2 ^ n))

-- Reciprocal of a power of two, written in the normalized form
-- 1/embed (suc d) with d = 2^n ∸ 1, so it matches the prod-eq
-- normalizer.
--
-- 二的幂的倒数，写作规范化形式 1/embed (suc d)，d = 2^n ∸ 1，
-- 以便与 prod-eq 归一化器对齐。
recipPow2 : ℕ → ℚ
recipPow2 n =
  let d = 2 ^ n ∸ 1
  in 1/_ (embed (suc d))
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
      an = 2 ^ n ∸ 1
      a1 = 2 ^ 1 ∸ 1
      as = 2 ^ suc n ∸ 1
      A = embed (suc an)
      B = embed (suc a1)
      S = embed (suc as)
      hn = recipPow2 n
      h1 = recipPow2 1
      hs = recipPow2 (suc n)
      w0nn : NonNegative w0
      w0nn = nonNegative
        (≤-trans (≤-reflexive (sym (+-inverseʳ (l r 0))))
                 (+-mono-≤ (<⇒≤ (RealI.lo r)) (≤-refl)))
      h1nn : NonNegative h1
      h1nn = pos⇒nonNeg h1 {{1/pos⇒pos B {{embed-suc-pos}}}}
      step1 : width r (suc n) ≤ width r n * h1
      step1 = width-1step r n
      step2 : width r n * h1 ≤ (w0 * hn) * h1
      step2 = *-monoʳ-≤-nonNeg h1 {{h1nn}} (width-n r n)
      step3 : (w0 * hn) * h1 ≤ w0 * (hn * h1)
      step3 = ≤-reflexive (*-assoc w0 hn h1)
      step4 : w0 * (hn * h1) ≤ w0 * hs
      step4 =
        let prod = A * B
            prodPos : Positive prod
            prodPos = pos*pos⇒pos A {{embed-suc-pos}} B {{embed-suc-pos}}
            invprod = 1/_ prod {{pos⇒nonZero prod {{prodPos}}}}
            s41 : w0 * (hn * h1) ≤ w0 * invprod
            s41 = *-monoˡ-≤-nonNeg w0 {{w0nn}}
                    (recip-prod≤ A B embed-suc-pos embed-suc-pos)
            A≡ : A ≡ pow2 n
            A≡ = cong embed (suc∸1 (0<2^t n))
            B≡ : B ≡ pow2 1
            B≡ = cong embed (suc∸1 (0<2^t 1))
            S≡ : S ≡ pow2 (suc n)
            S≡ = cong embed (suc∸1 (0<2^t (suc n)))
            prod≡S : prod ≡ S
            prod≡S = begin
              A * B             ≡⟨ cong (A *_) B≡ ⟩
              A * pow2 1        ≡⟨ cong (_* pow2 1) A≡ ⟩
              pow2 n * pow2 1   ≡⟨ denom-eq n ⟩
              pow2 (suc n)      ≡⟨ sym S≡ ⟩
              S                 ∎
            inv-eq : invprod ≡ hs
            inv-eq = reciprocal-cong prod S
                      {{pos⇒nonZero prod {{prodPos}}}}
                      {{pos⇒nonZero S {{embed-suc-pos}}}}
                      prod≡S
            s42 : w0 * invprod ≡ w0 * hs
            s42 = cong (λ z → w0 * z) inv-eq
        in ≤-trans s41 (≤-reflexive s42)
  in ≤-trans step1 (≤-trans step2 (≤-trans step3 step4))

-- The centre lies at or above the lower endpoint.
--
-- 中心不低于下端点。
centre-l : (r : RealI) (n : ℕ) → l r n ≤ centre r n
centre-l r n =
  let open ≡-Reasoning
      l′ = l r n; u′ = u r n
      half = 1/_ (embed 2) {{pos⇒nonZero (embed 2) {{pos-pow 0}}}}
      2h : embed 2 * half ≡ 1ℚ
      2h = *-inverseʳ (embed 2) {{pos⇒nonZero (embed 2) {{pos-pow 0}}}}
      2l : embed 2 * l′ ≡ l′ + l′
      2l = begin
        embed 2 * l′
          ≡⟨ cong (λ z → z * l′) (sym 2ℚ≡1+1) ⟩
        (1ℚ + 1ℚ) * l′
          ≡⟨ *-distribʳ-+ l′ 1ℚ 1ℚ ⟩
        1ℚ * l′ + 1ℚ * l′
          ≡⟨ cong (λ z → z + 1ℚ * l′) (*-identityˡ l′) ⟩
        l′ + 1ℚ * l′
          ≡⟨ cong (λ z → l′ + z) (*-identityˡ l′) ⟩
        l′ + l′
        ∎
      l≤u : l′ ≤ u′
      l≤u = <⇒≤ (RealI.lo (node r n))
      ineq : embed 2 * l′ ≤ l′ + u′
      ineq =
        ≤-trans (≤-reflexive 2l)
        (+-mono-≤ (≤-refl {l′}) l≤u)
      mono : (embed 2 * l′) * half ≤ (l′ + u′) * half
      mono = *-monoʳ-≤-nonNeg half
               {{pos⇒nonNeg half {{1/pos⇒pos (embed 2) {{pos-pow 0}}}}}} ineq
      chain : (embed 2 * l′) * half ≡ l′
      chain = begin
        (embed 2 * l′) * half
          ≡⟨ *-assoc (embed 2) l′ half ⟩
        embed 2 * (l′ * half)
          ≡⟨ cong (λ z → embed 2 * z) (*-comm l′ half) ⟩
        embed 2 * (half * l′)
          ≡⟨ sym (*-assoc (embed 2) half l′) ⟩
        (embed 2 * half) * l′
          ≡⟨ cong (λ z → z * l′) 2h ⟩
        1ℚ * l′
          ≡⟨ *-identityˡ l′ ⟩
        l′
        ∎
      lhs : l′ ≡ (embed 2 * l′) * half
      lhs = sym chain
  in ≤-trans (≤-reflexive lhs) mono

-- The centre lies at or below the upper endpoint.
--
-- 中心不高于上端点。
centre-u : (r : RealI) (n : ℕ) → centre r n ≤ u r n
centre-u r n =
  let open ≡-Reasoning
      l′ = l r n; u′ = u r n
      half = 1/_ (embed 2) {{pos⇒nonZero (embed 2) {{pos-pow 0}}}}
      2h : embed 2 * half ≡ 1ℚ
      2h = *-inverseʳ (embed 2) {{pos⇒nonZero (embed 2) {{pos-pow 0}}}}
      2u : embed 2 * u′ ≡ u′ + u′
      2u = begin
        embed 2 * u′
          ≡⟨ cong (λ z → z * u′) (sym 2ℚ≡1+1) ⟩
        (1ℚ + 1ℚ) * u′
          ≡⟨ *-distribʳ-+ u′ 1ℚ 1ℚ ⟩
        1ℚ * u′ + 1ℚ * u′
          ≡⟨ cong (λ z → z + 1ℚ * u′) (*-identityˡ u′) ⟩
        u′ + 1ℚ * u′
          ≡⟨ cong (λ z → u′ + z) (*-identityˡ u′) ⟩
        u′ + u′
        ∎
      l≤u : l′ ≤ u′
      l≤u = <⇒≤ (RealI.lo (node r n))
      ineq : l′ + u′ ≤ embed 2 * u′
      ineq =
        ≤-trans (+-mono-≤ l≤u (≤-refl {u′}))
                (≤-reflexive (sym 2u))
      mono : (l′ + u′) * half ≤ (embed 2 * u′) * half
      mono = *-monoʳ-≤-nonNeg half
               {{pos⇒nonNeg half {{1/pos⇒pos (embed 2) {{pos-pow 0}}}}}} ineq
      chain : (embed 2 * u′) * half ≡ u′
      chain = begin
        (embed 2 * u′) * half
          ≡⟨ *-assoc (embed 2) u′ half ⟩
        embed 2 * (u′ * half)
          ≡⟨ cong (λ z → embed 2 * z) (*-comm u′ half) ⟩
        embed 2 * (half * u′)
          ≡⟨ sym (*-assoc (embed 2) half u′) ⟩
        (embed 2 * half) * u′
          ≡⟨ cong (λ z → z * u′) 2h ⟩
        1ℚ * u′
          ≡⟨ *-identityˡ u′ ⟩
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

-- Iterated monotonicity of the lower endpoint.
--
-- 下端点的迭代单调性。
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

-- The difference of two interval points is bounded above by the
-- interval width.
--
-- 区间内两元素之差被区间宽度上界。
diff+ : {x y l u : ℚ} →
  l ≤ x → x ≤ u → l ≤ y → y ≤ u → (x - y) ≤ (u - l)
diff+ {x} {y} {l} {u} lx xu ly yu =
  ≤-trans (+-mono-≤ xu (≤-refl { neg y }))
          (+-mono-≤ (≤-refl {u}) (neg-antimono-≤ ly))

-- The negation of a difference is bounded by the interval width.
--
-- 差之取负被区间宽度上界。
diff- : {x y l u : ℚ} →
  l ≤ x → x ≤ u → l ≤ y → y ≤ u → neg (x - y) ≤ (u - l)
diff- {x} {y} {l} {u} lx xu ly yu =
  ≤-trans (≤-reflexive (negsub x y))
  (≤-trans (+-mono-≤ yu (≤-refl { neg x }))
           (+-mono-≤ (≤-refl {u}) (neg-antimono-≤ lx)))

-- Two points inside an interval differ by at most its width.
--
-- 区间内两点之差至多为该区间宽度。
bounded-diff : {x y l u : ℚ} →
  l ≤ x → x ≤ u → l ≤ y → y ≤ u → ∣ x - y ∣ ≤ u - l
bounded-diff {x} {y} {l} {u} lx xu ly yu
  with ∣p∣≡p∨∣p∣≡-p (x - y)
...  | inj₁ abs≡ =
  ≤-trans (≤-reflexive abs≡) (diff+ lx xu ly yu)
...  | inj₂ abs≡ =
  ≤-trans (≤-reflexive abs≡) (diff- lx xu ly yu)

-- The difference of two reachable centres is bounded by the width at
-- the shallower level.
--
-- 两个可达中心之差被较浅层的宽度上界。
centre-diff : (r : RealI) (t a b : ℕ) →
  t ≤N a → t ≤N b → ∣ centre r a - centre r b ∣ ≤ width r t
centre-diff r t a b ta tb =
  bounded-diff (centre-in-l r ta) (centre-in-u r ta)
               (centre-in-l r tb) (centre-in-u r tb)

-- Combined with the geometric bound.
--
-- 与几何界合并。
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
    ≡⟨ ℕP.*-comm 2 m ⟩
  m ℕ* 2
    ≡⟨ *-suc m 1 ⟩
  m +N (m ℕ* 1)
    ≡⟨ cong (m +N_) (ℕP.*-identityʳ m) ⟩
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

-- The dyadic scale is non-decreasing.
--
-- 二进刻度单调不减。
pow≤ : ∀ n → 2 ^ n ≤N 2 ^ suc n
pow≤ n = ^-monoʳ-≤ 2 (n≤1+n n)

1≤2^n : ∀ n → 1 ≤N 2 ^ n
1≤2^n n = ^-monoʳ-≤ 2 (z≤n {n})

-- Positivity from being at least one.
--
-- 大于等于一时为正。
1≤⇒Positive : (q : ℚ) → 1ℚ ≤ q → Positive q
1≤⇒Positive q 1≤q =
  positive (<-≤-trans (0<1) 1≤q)

recip≤1 : (q : ℚ) → 1ℚ ≤ q → (nz : NonZero q) →
  1/_ q {{nz}} ≤ 1ℚ
recip≤1 q 1≤q nz =
  let r = 1/_ q {{nz}}
      pq : Positive q
      pq = 1≤⇒Positive q 1≤q
  in
  begin
    r
    ≡⟨ sym (*-identityʳ r) ⟩
    r * 1ℚ
    ≤⟨ *-monoˡ-≤-nonNeg r
          {{pos⇒nonNeg r {{1/pos⇒pos q {{pq}}}}}} 1≤q ⟩
      r * q
    ≡⟨ *-inverseˡ q {{nz}} ⟩
      1ℚ
    ∎
  where open ≤-Reasoning

1≤embed-suc : (d : ℕ) → 1ℚ ≤ embed (suc d)
1≤embed-suc d =
  *≤* (+≤+ (s≤s z≤n))

-- embed M is nonnegative.
--
-- embed M 非负。
nonNeg-embed : (M : ℕ) → NonNegative (embed M)
nonNeg-embed zero    = nonNegative (≤-refl)
nonNeg-embed (suc n) =
  pos⇒nonNeg (embed (suc n)) {{embed-suc-pos}}

-- A natural-number embed divided by another is bounded by itself.
--
-- 一个自然数 embed 除以另一个自然数 embed 后仍不超过自身。
frac≤ : (M d : ℕ) →
  let p = embed M
      q = embed (suc d)
      pq : Positive q
      pq = embed-suc-pos
      nz : NonZero q
      nz = pos⇒nonZero q {{pq}}
  in
  p * 1/_ q {{nz}} ≤ p
frac≤ M d =
  let p = embed M
      q = embed (suc d)
      pq : Positive q
      pq = embed-suc-pos
  in
  begin
    p * 1/_ q {{pos⇒nonZero q {{pq}}}}
    ≤⟨ *-monoˡ-≤-nonNeg p
          {{nonNeg-embed M}} (recip≤1 q (1≤embed-suc d) (pos⇒nonZero q {{pq}})) ⟩
    p * 1ℚ
    ≡⟨ *-identityʳ p ⟩
    p
    ∎
  where open ≤-Reasoning

-- Normalization identity for the dyadic product.
--
-- 二进乘积的归一化恒等式。
prod-eq : (M d : ℕ) →
  embed M * 1/_ (embed (suc d))
              {{pos⇒nonZero (embed (suc d)) {{embed-suc-pos}}}}
  ≡ normalize M (suc d)
prod-eq M d =
  /-cong
    (ℤP.*-identityʳ (+ M))
    (ℕP.*-identityˡ (suc d))

-- The literal fraction equals the normalized product.
--
-- 字面分式等于规范化乘积。
frac-term-eq : (M d : ℕ) → .(c : Coprime M (suc d)) →
  mkℚ (+ M) d c
  ≡ embed M * 1/_ (embed (suc d))
                {{pos⇒nonZero (embed (suc d)) {{embed-suc-pos}}}}
frac-term-eq M d c =
  trans (sym (normalize-coprime c)) (sym (prod-eq M d))

-- Any nonnegative rational is bounded by an embed of a natural.
--
-- 任何非负有理数都被某个自然数的 embed 上界。
bound-w : (w : ℚ) → 0ℚ ≤ w → Σ ℕ (λ M → w ≤ embed M)
bound-w (mkℚ (+ M) d c) _ =
  M , (≤-trans (≤-reflexive (frac-term-eq M d c)) (frac≤ M d))
bound-w (mkℚ -[1+ n ] d c) (*≤* le) with le
... | ()

-- Strict growth of the dyadic scale.
--
-- 二进刻度的严格增长。
pow< : (n : ℕ) → 2 ^ n <N 2 ^ suc n
pow< n =
  ℕP.<-≤-trans
    (ℕP.m<n+m (2 ^ n) {n = 2 ^ n} (0<2^t n))
    (ℕP.≤-reflexive (qq n))

-- n < 2^n for every natural n.
--
-- 对每个自然数，n 都小于 2 的 n 次幂。
n<2^n : (n : ℕ) → n <N 2 ^ n
n<2^n zero    = s≤s z≤n
n<2^n (suc n) =
  ℕP.≤-<-trans (n<2^n n) (pow< n)

-- A strict exponential bound, giving a strict modulus.
--
-- 严格的指数上界，由此给出严格模数。
B<2^sucB : (B : ℕ) → B <N 2 ^ suc B
B<2^sucB B =
  ℕP.<-trans (n<2^n B) (pow< B)

pos-2^t : (t : ℕ) → Positive (embed (2 ^ t))
pos-2^t t = positive (embed-mono-< (0<2^t t))

recip2^t : (t : ℕ) → ℚ
recip2^t = recipPow2

rawL : (M t : ℕ) → ℚᵘ
rawL M t = mkℚᵘ (+ M) (2 ^ t ∸ 1)

recip-suc : (k : ℕ) → ℚ
recip-suc k = ε k

nz-2^t : (t : ℕ) → ℕNonZero (2 ^ t)
nz-2^t t =
  ≢-nonZero
    (≢-sym
       (ℕP.<⇒≢ (0<2^t t)))

fracL : (M t : ℕ) → ℚ
fracL M t = fromℚᵘ (rawL M t)

prod≡fracL : (M t : ℕ) → embed M * recip2^t t ≡ fracL M t
prod≡fracL M t = prod-eq M (2 ^ t ∸ 1)

-- The combined fraction at d = 0 is the simple dyadic fraction.
--
-- 在 d = 0 处，组合分数退化为简单的二进分数。
fracL≡combFrac : (M t : ℕ) → fracL M t ≡ combFrac M 0 t
fracL≡combFrac M t =
  cong (λ z → fromℚᵘ (mkℚᵘ (+ M) z))
    (cong (_∸ 1) (sym (ℕP.+-identityʳ (2 ^ t))))

-- The raw dyadic right-hand side equals the precision level.
--
-- 原始二进右端等于精度层。
fromℚᵘ-rawR≡recip-suc : (k : ℕ) → fromℚᵘ (rawR k) ≡ recip-suc k
fromℚᵘ-rawR≡recip-suc k =
  trans (normalize-coprime (1-coprimeTo (suc k)))
        (mkℚ-cong refl refl)

-- Dyadic error bound, stated through the strict power comparison.
--
-- 二进误差界，通过严格幂比较给出。
frac-strict : (M k t : ℕ) →
  (M ℕ* suc k) <N 2 ^ t →
  embed M * recip2^t t < recip-suc k
frac-strict M k t h =
  ≤-<-trans
    (≤-reflexive (trans (prod≡fracL M t) (fracL≡combFrac M t)))
    (<-≤-trans
      (comb-strict M 0 k t h')
      (≤-reflexive (fromℚᵘ-rawR≡recip-suc k)))
  where
  h' = subst (λ z → M ℕ* suc k <N z)
       (sym (ℕP.+-identityʳ (2 ^ t))) h

-- Initial width is strictly positive.
--
-- 初始宽度严格为正。
0<width : (r : RealI) → 0ℚ < width r 0
0<width r = pos-diff (RealI.l r) (RealI.u r) (RealI.lo r)

-- The carried modulus construction: successive interval centres form
-- a Cauchy sequence.
--
-- 携带模数构造：相继的区间中心构成柯西序列。
realI→cauchy : RealI → CauchySeq
realI→cauchy r = record
  { f = centre r
  ; μ = modulus
  ; cauchy = cauchy-proof
  }
  where
    w0 = width r 0
    0≤w0 : 0ℚ ≤ w0
    0≤w0 = <⇒≤ (0<width r)
    M = proj₁ (bound-w w0 0≤w0)
    w0≤M : w0 ≤ embed M
    w0≤M = proj₂ (bound-w w0 0≤w0)

    modulus : ℕ → ℕ
    modulus k = suc (M ℕ* suc k)

    recip2^t-pos : (t : ℕ) → Positive (recip2^t t)
    recip2^t-pos t =
      let d = 2 ^ t ∸ 1
      in 1/pos⇒pos (embed (suc d))
           ⦃ embed-suc-pos ⦄

    step2 : (t : ℕ) → width-nV r t ≤ embed M * recip2^t t
    step2 t =
      *-monoʳ-≤-nonNeg
        (recip2^t t)
        {{pos⇒nonNeg (recip2^t t) {{recip2^t-pos t}}}}
        w0≤M

    cauchy-proof : ∀ k n m → n ≥ modulus k → m ≥ modulus k →
      ∣ centre r n - centre r m ∣ < ε k
    cauchy-proof k n m n≥μ m≥μ =
      let t = modulus k in
      ≤-<-trans
        (centre-diff≤ r t n m n≥μ m≥μ)
        (≤-<-trans
           (step2 t)
           (frac-strict M k t (B<2^sucB (M ℕ* suc k))))

------------------------------------------------------------------------
-- The carried modulus dominates the index
--
-- μ k = suc (M * suc k). The initial width w0 is strictly positive, so
-- bound-w yields M ≥ 1, hence μ k ≥ k.
--
-- 携带模数支配下标
--
-- μ k = suc (M * suc k)。初始宽度 w0 严格为正，故 bound-w 给出
-- M ≥ 1，从而 μ k ≥ k。

μx-dom : (r : RealI) (k : ℕ) → μ (realI→cauchy r) k ≥ k
μx-dom r zero = z≤n
μx-dom r (suc k) = s≤s (≤ℕ-trans mid monoA)
  where
  w0 = width r 0
  0≤w0 = <⇒≤ (0<width r)
  Mx = proj₁ (bound-w w0 0≤w0)
  w0≤Mx = proj₂ (bound-w w0 0≤w0)
  0<eMx = <-≤-trans (0<width r) w0≤Mx
  Mx≥1 : 1 ≤N Mx
  Mx≥1 = embed-pos→≥1 Mx 0<eMx
  mid : k ≤N suc (suc k)
  mid = ≤ℕ-trans (n≤1+n k) (s≤s (n≤1+n k))
  monoA : suc (suc k) ≤N Mx ℕ* suc (suc k)
  monoA =
    ≤ℕ-trans (ℕP.≤-reflexive (sym (ℕP.*-identityˡ (suc (suc k)))))
             (*-mono-≤ Mx≥1 (≤ℕ-refl {suc (suc k)}))
