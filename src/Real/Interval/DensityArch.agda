------------------------------------------------------------------------
-- Density of the rationals and the Archimedean property
--
-- 有理数的稠密性与阿基米德性
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module Real.Interval.DensityArch where

open import Data.Nat using (ℕ; suc) renaming (_+_ to _+N_; _≤_ to _≤N_)
open import Data.Nat.Properties using ()
  renaming (+-comm to +-commℕ)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Data.Rational using
  (ℚ; 0ℚ; 1ℚ; _+_; _-_; _*_; _<_; _>_; _≤_; _≥_; ∣_∣)
open import Data.Rational.Base using (positive; -_)
open import Data.Rational.Properties using
  (≤-trans; ≤-refl; ≤-reflexive; <-≤-trans; ≤-<-trans; +-mono-≤; +-monoˡ-<
  ; +-assoc; +-identityˡ; +-identityʳ; +-inverseˡ; *-assoc; *-identityˡ
  ; *-identityʳ; *-comm; *-distribˡ-+; *-distribʳ-+; pos⇒nonNeg; 0≤∣p∣
  ; neg-antimono-≤; neg-distrib-+; neg-distribˡ-*; +-comm)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; trans; sym; cong; cong₂; subst; module ≡-Reasoning)
open ≡-Reasoning

open import Real using (embed; half; embed-+-hom)
open import Base.RationalRing using (neg-involutive)
open import Real.Interval using (RealI; embedℚ; δ; sub-cancel)
open import Real.IntervalEquiv using (l; u; width; bound-w; l-mono; u-mono)
open import Real.Interval.Node using (l-dyadic; u-dyadic)
open import Real.Interval.Kit using (0<half; half+half≡1; 2ℚ*half≡1)
open import Real.Interval.Order using (_<ℝ_)
open import Real.Interval.OrderLaws using (width-below-strict)
open import Real.Interval.Rational using (r≤|r|; pos-diff)
open import Real.Interval.Reasoning using (begin≤_; _≤∎; _≈⟨_⟩_; _≤⟨_⟩_; _<⟨_⟩≤[_])

------------------------------------------------------------------------
-- Shared rational arithmetic
--
-- 共享的有理算术

-- (x + y) − (x + z) ≡ y − z.
--
-- 消去公共加项。
cancel-plus : ∀ x y z → (x + y) - (x + z) ≡ y - z
cancel-plus x y z = begin
  (x + y) - (x + z)
    ≡⟨ cong (λ w → (x + y) + w) (neg-distrib-+ x z) ⟩
  (x + y) + ((- x) + (- z))
    ≡⟨ +-assoc x y ((- x) + (- z)) ⟩
  x + (y + ((- x) + (- z)))
    ≡⟨ cong (x +_)
            (trans (sym (+-assoc y (- x) (- z)))
                   (cong (λ w → w + (- z)) (Data.Rational.Properties.+-comm y (- x)))) ⟩
  x + (((- x) + y) + (- z))
    ≡⟨ cong (x +_) (+-assoc (- x) y (- z)) ⟩
  x + ((- x) + (y + (- z)))
    ≡⟨ sym (+-assoc x (- x) (y + (- z))) ⟩
  (x + (- x)) + (y + (- z))
    ≡⟨ cong (λ w → w + (y + (- z)))
            (Data.Rational.Properties.+-inverseʳ x) ⟩
  0ℚ + (y + (- z))
    ≡⟨ +-identityˡ (y + (- z)) ⟩
  y + (- z)
    ≡⟨ refl ⟩
  y - z
  ∎

embed1≡1 : embed 1 ≡ 1ℚ
embed1≡1 = refl

1-half≡half : 1ℚ - half ≡ half
1-half≡half = begin
  1ℚ - half
    ≡⟨ cong (λ w → w - half) (sym half+half≡1) ⟩
  (half + half) - half
    ≡⟨ cong (λ w → (half + half) - w) (sym (+-identityʳ half)) ⟩
  (half + half) - (half + 0ℚ)
    ≡⟨ cancel-plus half half 0ℚ ⟩
  half - 0ℚ
    ≡⟨ Data.Rational.Properties.+-identityʳ half ⟩
  half
  ∎

embed-suc-half : ∀ N → embed (suc N) - half ≡ embed N + half
embed-suc-half N = begin
  embed (suc N) - half
    ≡⟨ cong (λ w → w - half) (cong embed (sym (+-commℕ N 1))) ⟩
  embed (N +N 1) - half
    ≡⟨ cong (λ w → w - half) (embed-+-hom N 1) ⟩
  (embed N + embed 1) - half
    ≡⟨ cong (λ w → (embed N + w) - half) embed1≡1 ⟩
  (embed N + 1ℚ) - half
    ≡⟨ +-assoc (embed N) 1ℚ (- half) ⟩
  embed N + (1ℚ - half)
    ≡⟨ cong (embed N +_) 1-half≡half ⟩
  embed N + half
  ∎

------------------------------------------------------------------------
-- The Archimedean property
--
-- Every real is bounded above by the embedding of a natural number.
--
-- 阿基米德性
--
-- 每个实数都被某个自然数的嵌入上界。

archimedean : (x : RealI) → Σ ℕ (λ n → x <ℝ embedℚ (embed n))
archimedean x = n , (0 , goal)
  where
    ux0 : ℚ
    ux0 = u x 0

    abs-ux0 : ℚ
    abs-ux0 = ∣ ux0 ∣

    0≤abs : 0ℚ ≤ abs-ux0
    0≤abs = 0≤∣p∣ ux0

    N : ℕ
    N = proj₁ (bound-w abs-ux0 0≤abs)

    abs≤N : abs-ux0 ≤ embed N
    abs≤N = proj₂ (bound-w abs-ux0 0≤abs)

    ux0≤abs : ux0 ≤ abs-ux0
    ux0≤abs = r≤|r| ux0

    ux0≤N : ux0 ≤ embed N
    ux0≤N = ≤-trans ux0≤abs abs≤N

    n : ℕ
    n = suc N

    raw : 0ℚ + embed N < half + embed N
    raw = +-monoˡ-< (embed N) 0<half

    step1 : embed N < half + embed N
    step1 = subst (λ z → z < half + embed N) (+-identityˡ (embed N)) raw

    N<N+half : embed N < embed N + half
    N<N+half = subst (λ z → embed N < z) (+-comm half (embed N)) step1

    ux0<N+half : ux0 < embed N + half
    ux0<N+half = ≤-<-trans ux0≤N N<N+half

    l-target : l (embedℚ (embed n)) 0 ≡ - δ 0 + embed n
    l-target = l-dyadic (embed n) 0

    commute : (- δ 0) + embed n ≡ embed n - δ 0
    commute = Data.Rational.Properties.+-comm (- δ 0) (embed n)

    δ0≡half : δ 0 ≡ half
    δ0≡half = refl

    half-eq : embed n - δ 0 ≡ embed n - half
    half-eq = cong (λ z → embed n - z) δ0≡half

    target≡ : l (embedℚ (embed n)) 0 ≡ embed N + half
    target≡ = begin
      l (embedℚ (embed n)) 0
        ≡⟨ l-target ⟩
      (- δ 0) + embed n
        ≡⟨ commute ⟩
      embed n - δ 0
        ≡⟨ half-eq ⟩
      embed n - half
        ≡⟨ embed-suc-half N ⟩
      embed N + half
      ∎

    goal : u x 0 < l (embedℚ (embed n)) 0
    goal =
      u x 0
        <⟨ ux0<N+half ⟩≤[
        ≤-reflexive (sym target≡) ]

------------------------------------------------------------------------
-- Density of the rationals
--
-- Between any two distinct reals there is a rational. At the
-- separating level k with u x k < l y k, let d = l y k − u x k.
-- Choose a deeper level m ≥ k with width 0ℝ m < d, i.e.
-- δ m + δ m < d. Take the midpoint q = (u x m + l y m) * half.
-- Since u x m ≤ u x k and l y m ≥ l y k, the gap
-- d_m = l y m − u x m satisfies d_m ≥ d, so
--
--   q − u x m = d_m * half ≥ d * half > δ m,
--   l y m − q = d_m * half ≥ d * half > δ m,
--
-- hence u x m < q − δ m = l (embedℚ q) m and
--       u (embedℚ q) m = q + δ m < l y m.
--
-- 有理数稠密性
--
-- 任意两个不同实数之间存在有理数。在分离层级 k 处令间隙为 d。
-- 取更深层级 m，使零嵌入在该层的宽度低于 d。取中点 q，间隙
-- 在两侧都保持住，从而 q 的嵌入区间把 x 与 y 分离。

-- Width of the zero embedding at level m.
--
-- 零的嵌入在第 m 层的宽度。
width-0ℝ : ∀ m → width (embedℚ 0ℚ) m ≡ δ m + δ m
width-0ℝ m = begin
  width (embedℚ 0ℚ) m
    ≡⟨ cong₂ (λ x y → x - y) (u-dyadic 0ℚ m) (l-dyadic 0ℚ m) ⟩
  (δ m + 0ℚ) - ((- δ m) + 0ℚ)
    ≡⟨ sub-cancel (δ m) (- δ m) 0ℚ ⟩
  δ m + (- (- δ m))
    ≡⟨ cong (δ m +_) (neg-involutive (δ m)) ⟩
  δ m + δ m
  ∎

-- Two copies of a tolerance equal twice the tolerance.
--
-- 两份容差相加等于该容差的两倍。
δ+δ≡2δ : ∀ δ → δ + δ ≡ embed 2 * δ
δ+δ≡2δ δ = sym (begin
  (1ℚ + 1ℚ) * δ
    ≡⟨ *-distribʳ-+ δ 1ℚ 1ℚ ⟩
  1ℚ * δ + 1ℚ * δ
    ≡⟨ cong₂ _+_ (*-identityˡ δ) (*-identityˡ δ) ⟩
  δ + δ
  ∎)

-- A tolerance whose double stays below a bound is itself below half
-- of that bound.
--
-- 若某容差的两倍低于一个界，则该容差低于该界的一半。
2δ<d⇒δ<half-d : ∀ {δ d} → δ + δ < d → δ < d * half
2δ<d⇒δ<half-d {δ} {d} h =
  subst (λ z → z < d * half) lhs≡ step
  where
  h2 : embed 2 * δ < d
  h2 = subst (λ z → z < d) (δ+δ≡2δ δ) h

  step : (embed 2 * δ) * half < d * half
  step = Data.Rational.Properties.*-monoˡ-<-pos half {{positive 0<half}} h2

  lhs≡ : ((embed 2) * δ) * half ≡ δ
  lhs≡ = begin
    ((embed 2) * δ) * half
      ≡⟨ *-assoc (embed 2) δ half ⟩
    (embed 2) * (δ * half)
      ≡⟨ cong ((embed 2) *_) (*-comm δ half) ⟩
    (embed 2) * (half * δ)
      ≡⟨ sym (*-assoc (embed 2) half δ) ⟩
    ((embed 2) * half) * δ
      ≡⟨ cong (_* δ) 2ℚ*half≡1 ⟩
    1ℚ * δ
      ≡⟨ *-identityˡ δ ⟩
    δ
      ∎

-- Midpoint identities: both distances from the midpoint of a, b to
-- a and to b equal half the gap.
--
-- 中点恒等式：中点分别到 a 与到 b 的距离都等于间隙的一半。
midpoint-l : ∀ a b → (a + b) * half - a ≡ (b - a) * half
midpoint-l a b = begin
  (a + b) * half - a
    ≡⟨ cong (λ z → (a + b) * half - z) (sym (*-identityʳ a)) ⟩
  (a + b) * half - a * 1ℚ
    ≡⟨ cong (λ z → (a + b) * half - z) (sym merge) ⟩
  (a + b) * half - (a * half + a * half)
    ≡⟨ cong (λ z → z - (a * half + a * half))
            (*-distribʳ-+ half a b) ⟩
  (a * half + b * half) - (a * half + a * half)
    ≡⟨ cancel-plus (a * half) (b * half) (a * half) ⟩
  b * half - a * half
    ≡⟨ cong (λ z → b * half + z) (neg-distribˡ-* a half) ⟩
  b * half + (- a) * half
    ≡⟨ sym (*-distribʳ-+ half b (- a)) ⟩
  (b + (- a)) * half
    ≡⟨ refl ⟩
  (b - a) * half
  ∎
  where
  merge : a * half + a * half ≡ a * 1ℚ
  merge = trans (sym (*-distribˡ-+ a half half))
                (cong (a *_) half+half≡1)

midpoint-u : ∀ a b → b - (a + b) * half ≡ (b - a) * half
midpoint-u a b = begin
  b - (a + b) * half
    ≡⟨ cong (λ z → b - z) (*-distribʳ-+ half a b) ⟩
  b - (a * half + b * half)
    ≡⟨ cong (λ z → z - (a * half + b * half)) (sym b-double) ⟩
  (b * half + b * half) - (a * half + b * half)
    ≡⟨ cong (λ z → (b * half + b * half) - z)
            (+-comm (a * half) (b * half)) ⟩
  (b * half + b * half) - (b * half + a * half)
    ≡⟨ cancel-plus (b * half) (b * half) (a * half) ⟩
  b * half - a * half
    ≡⟨ cong (λ z → b * half + z) (neg-distribˡ-* a half) ⟩
  b * half + (- a) * half
    ≡⟨ sym (*-distribʳ-+ half b (- a)) ⟩
  (b + (- a)) * half
    ≡⟨ refl ⟩
  (b - a) * half
  ∎
  where
  b-double : b * half + b * half ≡ b
  b-double =
    trans (sym (*-distribˡ-+ b half half))
    (trans (cong (b *_) half+half≡1) (*-identityʳ b))

-- Density of the rationals.
--
-- 有理数的稠密性。
dense : {x y : RealI} → x <ℝ y →
  Σ ℚ (λ q → (x <ℝ embedℚ q) × (embedℚ q <ℝ y))
dense {x} {y} (k , uxk<lyk) = q , ((m , x<q) , (m , q<y))
  where
  d : ℚ
  d = l y k - u x k

  d>0 : 0ℚ < d
  d>0 = pos-diff (u x k) (l y k) uxk<lyk

  sel : Σ ℕ (λ m → (k ≤N m) × width (embedℚ 0ℚ) m < d)
  sel = width-below-strict (embedℚ 0ℚ) d k d>0

  m : ℕ
  m = proj₁ sel

  k≤m : k ≤N m
  k≤m = proj₁ (proj₂ sel)

  width<d : width (embedℚ 0ℚ) m < d
  width<d = proj₂ (proj₂ sel)

  2δ<d : δ m + δ m < d
  2δ<d = subst (λ z → z < d) (width-0ℝ m) width<d

  δm<half-d : δ m < d * half
  δm<half-d = 2δ<d⇒δ<half-d 2δ<d

  uxm : ℚ
  uxm = u x m

  lym : ℚ
  lym = l y m

  uxm≤uxk : u x m ≤ u x k
  uxm≤uxk = u-mono x {n = k} {m = m} k≤m

  lyk≤lym : l y k ≤ l y m
  lyk≤lym = l-mono y {n = k} {m = m} k≤m

  step1 : lym - uxm ≥ l y k - uxm
  step1 = +-mono-≤ lyk≤lym (≤-refl { - uxm })

  step2 : l y k - uxm ≥ l y k - u x k
  step2 = +-mono-≤ (≤-refl { l y k }) (neg-antimono-≤ uxm≤uxk)

  dm≥d : l y m - u x m ≥ d
  dm≥d = ≤-trans step2 step1

  q : ℚ
  q = (uxm + lym) * half

  q-uxm≡ : q - uxm ≡ (l y m - u x m) * half
  q-uxm≡ = midpoint-l uxm lym

  -- The half-gap lower bound in chain form.
  --
  -- 半间隙下界的链式写法。
  q-uxm≥half-d : q - uxm ≥ d * half
  q-uxm≥half-d =
    begin≤
      d * half
        ≤⟨ Data.Rational.Properties.*-monoʳ-≤-nonNeg half
             {{pos⇒nonNeg half {{positive 0<half}}}} dm≥d ⟩
      (l y m - u x m) * half
        ≈⟨ sym q-uxm≡ ⟩
      q - uxm
    ≤∎

  lym-q≡ : lym - q ≡ (l y m - u x m) * half
  lym-q≡ = midpoint-u uxm lym

  -- The symmetric half-gap lower bound in chain form.
  --
  -- 对称的半间隙下界的链式写法。
  lym-q≥half-d : lym - q ≥ d * half
  lym-q≥half-d =
    begin≤
      d * half
        ≤⟨ Data.Rational.Properties.*-monoʳ-≤-nonNeg half
             {{pos⇒nonNeg half {{positive 0<half}}}} dm≥d ⟩
      (l y m - u x m) * half
        ≈⟨ sym lym-q≡ ⟩
      lym - q
    ≤∎

  q-uxm>δm : q - uxm > δ m
  q-uxm>δm = <-≤-trans δm<half-d q-uxm≥half-d

  lym-q>δm : lym - q > δ m
  lym-q>δm = <-≤-trans δm<half-d lym-q≥half-d

  -- Cancellation of a paired addition.
  --
  -- 配对加法的消去。
  cancel-a : uxm + (q - uxm) ≡ q
  cancel-a = begin
    uxm + (q - uxm)
      ≡⟨ cong (uxm +_) (+-comm q (- uxm)) ⟩
    uxm + ((- uxm) + q)
      ≡⟨ sym (+-assoc uxm (- uxm) q) ⟩
    (uxm + (- uxm)) + q
      ≡⟨ cong (λ z → z + q) (Data.Rational.Properties.+-inverseʳ uxm) ⟩
    0ℚ + q
      ≡⟨ +-identityˡ q ⟩
    q
    ∎

  -- Cancellation around a negated leading term.
  --
  -- 带取负首项的相消。
  cancel-l : (- δ m) + (uxm + δ m) ≡ uxm
  cancel-l = begin
    (- δ m) + (uxm + δ m)
      ≡⟨ sym (+-assoc (- δ m) uxm (δ m)) ⟩
    ((- δ m) + uxm) + δ m
      ≡⟨ cong (λ z → z + δ m) (+-comm (- δ m) uxm) ⟩
    (uxm + (- δ m)) + δ m
      ≡⟨ +-assoc uxm (- δ m) (δ m) ⟩
    uxm + ((- δ m) + δ m)
      ≡⟨ cong (uxm +_) (+-inverseˡ (δ m)) ⟩
    uxm + 0ℚ
      ≡⟨ +-identityʳ uxm ⟩
    uxm
    ∎

  -- Cancellation of a trailing difference.
  --
  -- 尾部差的相消。
  cancel-b : q + (lym - q) ≡ lym
  cancel-b = begin
    q + (lym - q)
      ≡⟨ cong (q +_) (+-comm lym (- q)) ⟩
    q + ((- q) + lym)
      ≡⟨ sym (+-assoc q (- q) lym) ⟩
    (q + (- q)) + lym
      ≡⟨ cong (λ z → z + lym) (Data.Rational.Properties.+-inverseʳ q) ⟩
    0ℚ + lym
      ≡⟨ +-identityˡ lym ⟩
    lym
    ∎

  inner : uxm + δ m < q
  inner =
    uxm + δ m
      <⟨ Data.Rational.Properties.+-monoʳ-< uxm q-uxm>δm ⟩≤[
      ≤-reflexive cancel-a ]

  raw1 : uxm < q - δ m
  raw1 =
    ≤-<-trans (≤-reflexive (sym cancel-l))
      (<-≤-trans (Data.Rational.Properties.+-monoʳ-< (- δ m) inner)
                 (≤-reflexive (+-comm (- δ m) q)))

  x<q : u x m < l (embedℚ q) m
  x<q =
    subst (λ z → uxm < z) (sym (l-dyadic q m))
      (subst (λ z → uxm < z) (+-comm q (- δ m)) raw1)

  raw2 : q + δ m < lym
  raw2 =
    q + δ m
      <⟨ Data.Rational.Properties.+-monoʳ-< q lym-q>δm ⟩≤[
      ≤-reflexive cancel-b ]

  q<y : u (embedℚ q) m < l y m
  q<y =
    subst (λ z → z < lym) (sym (u-dyadic q m))
      (subst (λ z → z < lym) (+-comm q (δ m)) raw2)
