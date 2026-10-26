------------------------------------------------------------------------
-- Shared base for order completeness
--
-- 序完备性的共享基础
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module Real.Interval.OrderComplete.Base where

open import Data.Nat using (ℕ; zero; suc; _∸_; _^_; s≤s; z≤n)
  renaming (_≤_ to _≤N_; _*_ to _*N_)
open import Data.Nat.Properties using (m≤n+m; m+[n∸m]≡n)
  renaming (≤-trans to ≤N-trans; *-comm to *-commN)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Data.Sum using (_⊎_)
open import Data.Rational using
  (ℚ; 0ℚ; 1ℚ; _+_; _-_; _*_; _<_; _≤_; NonZero; NonNegative; positive)
open import Data.Rational.Base using (1/_; -_)
open import Data.Rational.Properties using
  (≤-reflexive; ≤-trans; <-≤-trans; +-mono-≤; +-monoˡ-<; +-monoʳ-<; +-comm
  ; +-assoc; *-comm; *-assoc; *-identityˡ; *-identityʳ; *-distribˡ-+; *-inverseˡ
  ; +-identityˡ; +-identityʳ; pos⇒nonNeg; *-monoˡ-<-pos; *-monoʳ-<-pos; *-zeroˡ
  ; *-monoʳ-≤-nonNeg; *-monoˡ-≤-nonNeg; neg-antimono-≤; +-monoˡ-≤)
  renaming (+-inverseʳ to +-invʳ; +-inverseˡ to +-invˡ)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; cong; cong₂; sym; trans; subst; subst₂; module ≡-Reasoning)
open ≡-Reasoning
open import Relation.Nullary.Negation using (¬_)
open Data.Rational.Properties.≤-Reasoning
  renaming (_∎ to _∎≤; begin_ to begin≤_) hiding (step-≡-⟩; step-≡-⟨; step-≡-∣)

open import Base.RationalRing using (neg-involutive)
open import Real using
  (embed; half; embed-suc-nonZero; embed-mono-≤; reciprocal-cong; 0<embed; embed-*-hom)
open import Real.Interval using (RealI; embedℚ; δ; sub-cancel)
open import Real.IntervalEquiv using (width; l; u)
open import Real.Interval.OrderLaws using (width-below)
open import Real.Interval.Node using (u-dyadic; l-dyadic)
open import Real.Interval.Kit using
  (recip-antitone; 0<half; 0≤half; half+half≡1; n≤2n)
open import Real.Interval.Order using (_<ℝ_)
open import Real.Interval.Rational using (0<2^t; pos-diff)

------------------------------------------------------------------------
-- Non-strict order
--
-- x ≤ℝ y when y is not strictly below x.
--
-- 非严格序
--
-- 当 y 不严格低于 x 时，x ≤ℝ y。

infix 4 _≤ℝ_

_≤ℝ_ : RealI → RealI → Set
x ≤ℝ y = ¬ (y <ℝ x)

------------------------------------------------------------------------
-- Rational order and arithmetic lemmas
--
-- 有理序与算术引理

a+d≡b : (a b : ℚ) → a + (b - a) ≡ b
a+d≡b a b =
  begin
    a + (b - a)
      ≡⟨ cong (a +_) (+-comm b (- a)) ⟩
    a + ((- a) + b)
      ≡⟨ sym (+-assoc a (- a) b) ⟩
    (a + (- a)) + b
      ≡⟨ cong (_+ b) (+-invʳ a) ⟩
    0ℚ + b
      ≡⟨ +-identityˡ b ⟩
    b
      ∎

-- Gap lemma: a' ≤ a, b ≤ b' and δ < (b − a)/2 imply a' + δ < b'.
--
-- 间隙引理：a' ≤ a、b ≤ b' 且 δ < (b−a)/2，则 a' + δ < b'。
gapLemma : ∀ {a' b' a b : ℚ} (δ : ℚ) →
  0ℚ < b - a →
  a' ≤ a → b ≤ b' → δ < (b - a) * half → a' + δ < b'
gapLemma {a'} {b'} {a} {b} δ g>0 a'≤a b≤b' δ<halfG = final
  where
  g = b - a
  half≤1 : half ≤ 1ℚ
  half≤1 = subst (λ z → half ≤ z) (sym half+half≡1)
             (+-monoˡ-≤ half 0≤half)
  nng : NonNegative g
  nng = pos⇒nonNeg g {{positive g>0}}
  halfG≤g : g * half ≤ g
  halfG≤g = ≤-trans (*-monoˡ-≤-nonNeg g {{nng}} half≤1)
              (≤-reflexive (*-identityʳ g))
  δ<g : δ < g
  δ<g = <-≤-trans δ<halfG halfG≤g
  diff≥g : g ≤ b' - a'
  diff≥g = +-mono-≤ b≤b' (neg-antimono-≤ a'≤a)
  δ<diff : δ < b' - a'
  δ<diff = <-≤-trans δ<g diff≥g
  final : a' + δ < b'
  final = subst (λ z → a' + δ < z) (a+d≡b a' b')
            (+-monoʳ-< a' δ<diff)

x<x+ : (x : ℚ) {y : ℚ} → 0ℚ < y → x < x + y
x<x+ x {y} 0<y =
  subst₂ _<_ (+-identityˡ x) (+-comm y x) (+-monoˡ-< x 0<y)

------------------------------------------------------------------------
-- Reflection of rational order into the real order
--
-- p < q implies embedℚ p <ℝ embedℚ q.
--
-- 有理序反射到实数序
--
-- p < q 蕴含 embedℚ p <ℝ embedℚ q。

emb< : {p q : ℚ} → p < q → embedℚ p <ℝ embedℚ q
emb< {p} {q} p<q =
  let d = q - p
      0<d = pos-diff p q p<q
      sel = width-below (embedℚ d) d 0<d
      k = proj₁ sel
      w<d : width (embedℚ d) k < d
      w<d = proj₂ sel
      width≡ : width (embedℚ d) k ≡ δ k + δ k
      width≡ =
        begin
          width (embedℚ d) k
            ≡⟨ cong₂ (λ x y → x - y) (u-dyadic d k) (l-dyadic d k) ⟩
          (δ k + d) - (- δ k + d)
            ≡⟨ sub-cancel (δ k) (- δ k) d ⟩
          δ k + (- (- δ k))
            ≡⟨ cong (δ k +_) (neg-involutive (δ k)) ⟩
          δ k + δ k
            ∎
      rad<d : δ k + δ k < d
      rad<d = subst (λ z → z < d) width≡ w<d
      step1 : (δ k + δ k) + p < (q - p) + p
      step1 = +-monoˡ-< p rad<d
      rhs≡ : (q - p) + p ≡ q
      rhs≡ =
        trans (+-assoc q (- p) p)
        (trans (cong (q +_) (+-invˡ p)) (+-identityʳ q))
      lhs≡ : (δ k + δ k) + p ≡ (δ k + p) + δ k
      lhs≡ =
        begin
          (δ k + δ k) + p
            ≡⟨ +-assoc (δ k) (δ k) p ⟩
          δ k + (δ k + p)
            ≡⟨ cong (δ k +_) (+-comm (δ k) p) ⟩
          δ k + (p + δ k)
            ≡⟨ sym (+-assoc (δ k) p (δ k)) ⟩
          (δ k + p) + δ k
            ∎
      step2 : (δ k + p) + δ k < q
      step2 =
        subst (λ z → z < q) lhs≡
          (subst (λ z → (δ k + δ k) + p < z) rhs≡ step1)
      simplL : ((δ k + p) + δ k) + (- δ k) ≡ δ k + p
      simplL =
        trans (+-assoc (δ k + p) (δ k) (- δ k))
        (trans (cong ((δ k + p) +_) (+-invʳ (δ k)))
               (+-identityʳ (δ k + p)))
      step3a : ((δ k + p) + δ k) + (- δ k) < q + (- δ k)
      step3a = +-monoˡ-< (- δ k) step2
      step3 : δ k + p < q + (- δ k)
      step3 = subst (λ z → z < q + (- δ k)) simplL step3a
      goal : δ k + p < (- δ k) + q
      goal = subst (λ z → δ k + p < z) (+-comm q (- δ k)) step3
      finalGoal : u (embedℚ p) k < l (embedℚ q) k
      finalGoal =
        subst₂ _<_ (sym (u-dyadic p k)) (sym (l-dyadic q k)) goal
  in (k , finalGoal)

------------------------------------------------------------------------
-- Dyadic radius decay
--
-- δ is antitone in n: m ≤ n → δ n ≤ δ m.
--
-- 二进半径的递减
--
-- δ 对 n 反单调：m ≤ n → δ n ≤ δ m。

δ-dec : ∀ m n → m ≤N n → δ n ≤ δ m
δ-dec m n p =
  recip-antitone 0<den
    (embed-mono-≤ (Data.Nat.Properties.^-monoʳ-≤ 2 (s≤s p)))
  where
  1≤2sm : ∀ m → 1 ≤N 2 ^ suc m
  1≤2sm zero = s≤s z≤n
  1≤2sm (suc m) =
    ≤N-trans (1≤2sm m) (n≤2n (2 ^ suc m))

  s≡ : suc ((2 ^ suc m) ∸ 1) ≡ 2 ^ suc m
  s≡ = m+[n∸m]≡n {1} {2 ^ suc m} (1≤2sm m)
  0<den : 0ℚ < embed (2 ^ suc m)
  0<den = subst (λ z → 0ℚ < embed z) s≡
            (0<embed ((2 ^ suc m) ∸ 1))

------------------------------------------------------------------------
-- Subsets of the real line
--
-- 实数轴上的子集

Subset : Set₁
Subset = RealI → Set

-- A member as an upper-bound witness: P x and x <ℝ embedℚ b.
--
-- 成员作为上界见证：P x 且 x <ℝ embedℚ b。
Upper : Subset → ℚ → Set
Upper P b = (x : RealI) → P x → x <ℝ embedℚ b

-- A lower bracket is occupied: some member lies strictly above a.
--
-- 下括号被占据：某个成员严格位于 a 之上。
Occupied : Subset → ℚ → Set
Occupied P a = Σ RealI λ x → P x × (embedℚ a <ℝ x)

------------------------------------------------------------------------
-- Locatedness
--
-- For rationals p < q, either some member exceeds p or every member is
-- below q.
--
-- 定位性
--
-- 对有理数 p < q，要么某个成员超过 p，要么每个成员都低于 q。

Located : Subset → Set
Located P = ∀ (p q : ℚ) → p < q → Occupied P p ⊎ Upper P q

------------------------------------------------------------------------
-- Bisection data
--
-- 二分数据

record Bracket (P : Subset) : Set where
  constructor mkB
  field
    a b : ℚ
    a<b   : a < b
    occ   : Occupied P a
    upper : Upper P b

------------------------------------------------------------------------
-- Dyadic quarter algebra
--
-- 二进四分之一代数

quarter : ℚ
quarter = half * half

0<quarter : 0ℚ < quarter
0<quarter = subst (λ z → z < quarter) (*-zeroˡ half)
              (*-monoʳ-<-pos half 0<half)

qq≡h : quarter + quarter ≡ half
qq≡h =
  begin
    quarter + quarter
      ≡⟨ sym (*-distribˡ-+ half half half) ⟩
    half * (half + half)
      ≡⟨ cong (half *_) half+half≡1 ⟩
    half * 1ℚ
      ≡⟨ *-identityʳ half ⟩
    half
      ∎

4q≡1 : embed 4 * quarter ≡ 1ℚ
4q≡1 =
  begin
    embed 4 * quarter
      ≡⟨ refl ⟩
    (quarter + quarter) + (quarter + quarter)
      ≡⟨ cong₂ _+_ qq≡h qq≡h ⟩
    half + half
      ≡⟨ half+half≡1 ⟩
    1ℚ
      ∎

16q²≡1 : embed 16 * (quarter * quarter) ≡ 1ℚ
16q²≡1 =
  begin
    embed 16 * (quarter * quarter)
      ≡⟨ sym (*-assoc (embed 4) (embed 4) (quarter * quarter)) ⟩
    (embed 4 * embed 4) * (quarter * quarter)
      ≡⟨ refl ⟩
    (embed 4 * quarter) * (embed 4 * quarter)
      ≡⟨ cong₂ _*_ 4q≡1 4q≡1 ⟩
    1ℚ * 1ℚ
      ≡⟨ *-identityˡ 1ℚ ⟩
    1ℚ
      ∎

64q3≡1 : embed 64 * (quarter * quarter * quarter) ≡ 1ℚ
64q3≡1 =
  begin
    embed 64 * (quarter * quarter * quarter)
      ≡⟨ refl ⟩
    (embed 4 * quarter) * (embed 16 * (quarter * quarter))
      ≡⟨ cong₂ _*_ 4q≡1 16q²≡1 ⟩
    1ℚ * 1ℚ
      ≡⟨ *-identityˡ 1ℚ ⟩
    1ℚ
      ∎

3/4 : ℚ
3/4 = half + quarter

3/4≡3q : 3/4 ≡ embed 3 * quarter
3/4≡3q =
  begin
    3/4
      ≡⟨ refl ⟩
    half + quarter
      ≡⟨ cong (_+ quarter) (sym qq≡h) ⟩
    (quarter + quarter) + quarter
      ≡⟨ +-assoc quarter quarter quarter ⟩
    quarter + (quarter + quarter)
      ≡⟨ refl ⟩
    embed 3 * quarter
      ∎

cube≡27 : (3/4 * 3/4) * 3/4 ≡
            embed 27 * (quarter * quarter * quarter)
cube≡27 =
  begin
    (3/4 * 3/4) * 3/4
      ≡⟨ cong (λ z → (z * z) * z) 3/4≡3q ⟩
    ((embed 3 * quarter) * (embed 3 * quarter)) * (embed 3 * quarter)
      ≡⟨ refl ⟩
    embed 27 * (quarter * quarter * quarter)
      ∎

q3 : ℚ
q3 = quarter * quarter * quarter

half≡32 : half ≡ embed 32 * (quarter * quarter * quarter)
half≡32 =
  begin
    half
      ≡⟨ sym (*-identityʳ half) ⟩
    half * 1ℚ
      ≡⟨ cong (half *_) (sym 64q3≡1) ⟩
    half * (embed 64 * q3)
      ≡⟨ refl ⟩
    embed 32 * q3
      ∎

0<q2 : 0ℚ < quarter * quarter
0<q2 = *-monoˡ-<-pos quarter 0<quarter
0<q3 : 0ℚ < q3
0<q3 = *-monoˡ-<-pos quarter 0<q2

27≤32 : 27 ≤N 32
27≤32 = m≤n+m 27 5

cube≤half : (3/4 * 3/4) * 3/4 ≤ half
cube≤half =
  begin≤
    (3/4 * 3/4) * 3/4
      ≤⟨ ≤-reflexive (sym cube≡27) ⟩
    embed 27 * q3
      ≤⟨ *-monoʳ-≤-nonNeg q3 (embed-mono-≤ 27≤32) ⟩
    embed 32 * q3
      ≤⟨ ≤-reflexive (sym half≡32) ⟩
    half
  ∎≤

------------------------------------------------------------------------
-- Reciprocal of a product
--
-- 乘积的倒数

recip-mul : (p q : ℚ) → .{{np : NonZero p}} → .{{nq : NonZero q}} →
  .{{npq : NonZero (p * q)}} →
  (1/ p) * (1/ q) ≡ 1/ (p * q)
recip-mul p q {{_}} {{_}} {{npq}} = sym (
  begin
    rpq
      ≡⟨ sym (*-identityʳ rpq) ⟩
    rpq * 1ℚ
      ≡⟨ cong (rpq *_) (sym prod≡1) ⟩
    rpq * (rp * rq * (p * q))
      ≡⟨ sym (*-assoc rpq (rp * rq) (p * q)) ⟩
    (rpq * (rp * rq)) * (p * q)
      ≡⟨ cong (λ z → z * (p * q)) (*-comm rpq (rp * rq)) ⟩
    ((rp * rq) * rpq) * (p * q)
      ≡⟨ *-assoc (rp * rq) rpq (p * q) ⟩
    (rp * rq) * (rpq * (p * q))
      ≡⟨ cong ((rp * rq) *_) (*-inverseˡ (p * q) {{npq}}) ⟩
    (rp * rq) * 1ℚ
      ≡⟨ *-identityʳ (rp * rq) ⟩
    rp * rq
      ∎)
  where
  rp  = 1/ p
  rq  = 1/ q
  rpq = 1/ (p * q)
  prod≡1 : (rp * rq) * (p * q) ≡ 1ℚ
  prod≡1 =
    begin
      (rp * rq) * (p * q)
        ≡⟨ sym (*-assoc (rp * rq) p q) ⟩
      ((rp * rq) * p) * q
        ≡⟨ cong (λ z → z * q)
               (begin
                  (rp * rq) * p
                    ≡⟨ *-assoc rp rq p ⟩
                  rp * (rq * p)
                    ≡⟨ cong (rp *_) (*-comm rq p) ⟩
                  rp * (p * rq)
                    ≡⟨ sym (*-assoc rp p rq) ⟩
                  (rp * p) * rq
                    ∎) ⟩
      ((rp * p) * rq) * q
        ≡⟨ *-assoc (rp * p) rq q ⟩
      (rp * p) * (rq * q)
        ≡⟨ cong₂ _*_ (*-inverseˡ p) (*-inverseˡ q) ⟩
      1ℚ * 1ℚ
        ≡⟨ *-identityˡ 1ℚ ⟩
      1ℚ
        ∎

------------------------------------------------------------------------
-- Dyadic half-powers
--
-- 二进半幂

private
  1≤2^j : ∀ j → 1 ≤N 2 ^ j
  1≤2^j = 0<2^t

  nz2^j : ∀ j → NonZero (embed (2 ^ j))
  nz2^j j =
    subst (λ n → NonZero (embed n)) (m+[n∸m]≡n (1≤2^j j))
      (embed-suc-nonZero {2 ^ j ∸ 1})

hp : ℕ → ℚ
hp j = 1/ embed (2 ^ j)
  where instance nz = nz2^j j

private pow2-suc : ∀ j → (2 ^ j) *N 2 ≡ 2 ^ (suc j)
pow2-suc j = *-commN (2 ^ j) 2

hp-step : ∀ j → hp j * half ≡ hp (suc j)
hp-step j =
  begin
    hp j * half
      ≡⟨ recip-mul (embed (2 ^ j)) (embed 2)
           {{np = nz2^j j}}
           {{nq = embed-suc-nonZero {1}}}
           {{npq = subst NonZero (sym prod≡) (nz2^j (suc j))}} ⟩
    1/_ (embed (2 ^ j) * embed 2) {{subst NonZero (sym prod≡) (nz2^j (suc j))}}
      ≡⟨ reciprocal-cong (embed (2 ^ j) * embed 2) (embed (2 ^ (suc j)))
           {{na = subst NonZero (sym prod≡) (nz2^j (suc j))}}
           {{nb = nz2^j (suc j)}}
           prod≡ ⟩
    1/_ (embed (2 ^ (suc j))) {{nz2^j (suc j)}}
  ∎
  where
  prod≡ : embed (2 ^ j) * embed 2 ≡ embed (2 ^ (suc j))
  prod≡ =
    begin
      embed (2 ^ j) * embed 2
        ≡⟨ sym (embed-*-hom (2 ^ j) 2) ⟩
      embed ((2 ^ j) *N 2)
        ≡⟨ cong embed (pow2-suc j) ⟩
      embed (2 ^ (suc j))
        ∎
