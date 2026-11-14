------------------------------------------------------------------------
-- Quota and accounting: scale, closing, mid, total, accounting, minimum, picking
--
-- 额度与核算：尺度、闭合、中层、总额、记账、最小值与选取
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module Real.Interval.ContinuityRecipQuota where

open import Data.Nat using (ℕ; suc)
open import Data.Product using (Σ; _,_; _×_)
open import Data.Rational using (ℚ; 0ℚ; 1ℚ; _+_; _*_; _<_; _≤_; _-_; _⊓_; -_)
open import Data.Rational.Base using (NonZero; positive; nonNegative; 1/_)
open import Data.Rational.Properties using
  (*-identityˡ; *-assoc; *-comm; *-distribʳ-+; +-mono-<; +-mono-≤-<; ≤-refl
  ; p⊓q≤p; p⊓q≤q; *-monoʳ-≤-nonNeg; +-assoc; +-inverseʳ; +-identityʳ; <⇒≤
  ; pos⇒nonZero; pos*pos⇒pos; +-comm; *-inverseʳ; *-identityʳ)
open import Relation.Binary.PropositionalEquality using
  (_≡_; sym; cong; trans; subst; module ≡-Reasoning)
open ≡-Reasoning

open import Base.RationalRing using (+interchange)
open import Real using (half; ε; embed; 0<ε; embed-+-hom)
open import Real.Interval using (δ)
open import Real.Interval.ContinuityRecipBudget using
  (d-eight; 0<mul; 0<inv; coef2; coef4; 0<embed-suc; coef3; 0<3; 0<6; budget-eq
  ; budget-split)
open import Real.Interval.ContinuityRecipBasic using (pos-meet)
open import Real.Interval.Kit using (two-half; 0<half)

------------------------------------------------------------------------
-- Scaling the closed constant by the level precision leaves the precision
--
-- 用层精度缩放闭合常数，仍得该精度

budget-scale :
  (k : ℕ) →
  (embed 8 * ε 9 + (ε 9 + ε 9)) * ε k ≡ ε k
budget-scale k = begin
    (embed 8 * ε 9 + (ε 9 + ε 9)) * ε k
      ≡⟨ cong (λ z → z * ε k) budget-eq ⟩
    1ℚ * ε k
      ≡⟨ *-identityˡ (ε k) ⟩
    ε k
  ∎

------------------------------------------------------------------------
-- Distributing the level precision across the constant sum
--
-- 把层精度分配到常数和式的各项

e-scale :
  (k : ℕ) →
  (embed 8 * ε 9 + (ε 9 + ε 9)) * ε k
  ≡ embed 8 * (ε k * ε 9) + (ε k * ε 9 + ε k * ε 9)
e-scale k = let q = ε k in begin
    (embed 8 * ε 9 + (ε 9 + ε 9)) * q
      ≡⟨ *-distribʳ-+ q (embed 8 * ε 9) (ε 9 + ε 9) ⟩
    (embed 8 * ε 9) * q + (ε 9 + ε 9) * q
      ≡⟨ cong (λ z → z + (ε 9 + ε 9) * q)
           (trans (*-assoc (embed 8) (ε 9) q)
                  (cong (λ w → embed 8 * w) (*-comm (ε 9) q))) ⟩
    embed 8 * (q * ε 9) + (ε 9 + ε 9) * q
      ≡⟨ cong (λ z → embed 8 * (q * ε 9) + z)
           (*-distribʳ-+ q (ε 9) (ε 9)) ⟩
    embed 8 * (q * ε 9) + (ε 9 * q + ε 9 * q)
      ≡⟨ cong (λ z → embed 8 * (q * ε 9) + (z + ε 9 * q)) (*-comm (ε 9) q) ⟩
    embed 8 * (q * ε 9) + (q * ε 9 + ε 9 * q)
      ≡⟨ cong (λ z → embed 8 * (q * ε 9) + (q * ε 9 + z)) (*-comm (ε 9) q) ⟩
    embed 8 * (q * ε 9) + (q * ε 9 + q * ε 9)
  ∎

------------------------------------------------------------------------
-- Eight copies plus two slack copies equal the level precision
--
-- 八份加两份余量恰为层精度

quota-eq :
  (k : ℕ) →
  embed 8 * (ε k * ε 9) + (ε k * ε 9 + ε k * ε 9) ≡ ε k
quota-eq k = trans (sym (e-scale k)) (budget-scale k)

------------------------------------------------------------------------
-- Closing the quota from two strict allowance bounds
--
-- 由两个严格额度界闭合总额度

budget-core :
  (k : ℕ) (A B : ℚ) →
  A < ε k * ε 9 →
  B < ε k * ε 9 →
  embed 8 * (ε k * ε 9) + (A + B) < ε k
budget-core k A B A< B< =
  let u = ε k * ε 9
      h : A + B < u + u
      h = +-mono-< A< B<
      h' : embed 8 * u + (A + B) < embed 8 * u + (u + u)
      h' = +-mono-≤-< (≤-refl {embed 8 * u}) h
  in subst (λ z → embed 8 * u + (A + B) < z) (quota-eq k) h'

------------------------------------------------------------------------
-- Splitting the accounted total into a width part and an eightfold part
--
-- 把记账总量拆成宽度部分与八倍部分

budget-mid :
  (c W e : ℚ) {{nz : NonZero (c * c)}} →
  (embed 6 * W + embed 8 * ((c * c) * e)) * (1/_ (c * c))
    ≡ (embed 6 * W) * (1/_ (c * c)) + embed 8 * e
budget-mid c W e =
  trans
    (budget-split (embed 6 * W) (embed 8 * ((c * c) * e)) (1/_ (c * c)))
    (cong (λ z → (embed 6 * W) * (1/_ (c * c)) + z) (d-eight c e))

------------------------------------------------------------------------
-- Rearranging the total so that the eightfold constant comes first
--
-- 重排总量，使八倍常数排在前面

budget-total :
  (k : ℕ) (c W : ℚ) {{nz : NonZero (c * c)}} →
  (embed 6 * W + embed 8 * ((c * c) * (ε k * ε 9))) * (1/_ (c * c))
    ≡ embed 8 * (ε k * ε 9) + (embed 6 * W) * (1/_ (c * c))
budget-total k c W =
  trans (budget-mid c W (ε k * ε 9))
    (+-comm ((embed 6 * W) * (1/_ (c * c)))
            (embed 8 * (ε k * ε 9)))

------------------------------------------------------------------------
-- The reciprocal budget, closed inside one module
--
-- 倒数预算的收口（单模块内联）

-- The scalar total of the reciprocal error is E + 3 delta, with
-- E = (6 W + 8 ((c*c) * u)) * inv (c*c) and u = eps k * eps 9. Since
-- 8 u + (u + u) = eps k by quota-eq, it suffices that the width
-- allowance and the three radii are each strictly below u. The chain
-- is kept here in one piece so that the occurrence of u rewritten by
-- quota-eq is the very one built by budget-split and d-eight.
--
-- 倒数误差的标量总量为 E + 3δ，其中 E = (6W + 8((c*c)·u))·inv(c*c)，
-- u = εk·ε9。由 quota-eq 得 8u + (u + u) = εk，故只需宽度额度与三层
-- 半径各自严格低于 u。整条链放在同一模块内，使 quota-eq 改写的那一次
-- u 正是 budget-split 与 d-eight 生成的那一次。
budget :
  (k : ℕ) (c W : ℚ) {{nz : NonZero (c * c)}} (n : ℕ) →
  (embed 6 * W) * (1/_ (c * c)) < ε k * ε 9 →
  ((δ n + δ n) + δ n) < ε k * ε 9 →
  ((embed 6 * W + embed 8 * ((c * c) * (ε k * ε 9))) * (1/_ (c * c))
    + ((δ n + δ n) + δ n)) < ε k
budget k c W n A< B< =
  let u = ε k * ε 9
      inv = 1/_ (c * c)
      A = (embed 6 * W) * inv
      B = (δ n + δ n) + δ n

      h₁ : (embed 6 * W + embed 8 * ((c * c) * u)) * inv ≡ A + embed 8 * u
      h₁ = trans (budget-split (embed 6 * W) (embed 8 * ((c * c) * u)) inv)
                 (cong (λ z → A + z) (d-eight c u))

      h₂ : A + embed 8 * u ≡ embed 8 * u + A
      h₂ = +-comm A (embed 8 * u)

      h₃ : (embed 8 * u + A) + B ≡ embed 8 * u + (A + B)
      h₃ = +-assoc (embed 8 * u) A B

      hE : ((embed 6 * W + embed 8 * ((c * c) * u)) * inv + B)
             ≡ embed 8 * u + (A + B)
      hE = trans (cong (λ z → z + B) h₁)
                 (trans (cong (λ z → z + B) h₂) h₃)

      h' : embed 8 * u + (A + B) < embed 8 * u + (u + u)
      h' = +-mono-≤-< (≤-refl {embed 8 * u}) (+-mono-< A< B<)

      hℓ : embed 8 * u + (A + B) < ε k
      hℓ = subst (λ z → embed 8 * u + (A + B) < z) (quota-eq k) h'
  in subst (λ z → z < ε k) (sym hE) hℓ

------------------------------------------------------------------------
-- The first block merges into two widths plus two gaps
--
-- 第一块合并成两个宽度加两个间隙

block1 : (W d : ℚ) → (W + (d + d)) + W ≡ embed 2 * W + embed 2 * d
block1 W d = begin
    (W + (d + d)) + W
      ≡⟨ +-assoc W (d + d) W ⟩
    W + ((d + d) + W)
      ≡⟨ cong (λ z → W + z) (+-comm (d + d) W) ⟩
    W + (W + (d + d))
      ≡⟨ sym (+-assoc W W (d + d)) ⟩
    (W + W) + (d + d)
      ≡⟨ cong (λ z → z + (d + d)) (sym (coef2 W)) ⟩
    embed 2 * W + (d + d)
      ≡⟨ cong (λ z → embed 2 * W + z) (sym (coef2 d)) ⟩
    embed 2 * W + embed 2 * d
  ∎

------------------------------------------------------------------------
-- The second block merges into two widths plus four gaps
--
-- 第二块合并成两个宽度加四个间隙

block2 :
  (W d : ℚ) →
  (((W + (d + d)) + d) + (W + d)) ≡ embed 2 * W + embed 4 * d
block2 W d = begin
    (((W + (d + d)) + d) + (W + d))
      ≡⟨ cong (λ z → z + (W + d)) (+-assoc W (d + d) d) ⟩
    (W + ((d + d) + d)) + (W + d)
      ≡⟨ +interchange W ((d + d) + d) W d ⟩
    (W + W) + (((d + d) + d) + d)
      ≡⟨ cong (λ z → z + (((d + d) + d) + d)) (sym (coef2 W)) ⟩
    embed 2 * W + (((d + d) + d) + d)
      ≡⟨ cong (λ z → embed 2 * W + z) (sym (coef4 d)) ⟩
    embed 2 * W + embed 4 * d
  ∎

------------------------------------------------------------------------
-- The third block merges into two widths plus two gaps
--
-- 第三块合并成两个宽度加两个间隙

block3 : (W d : ℚ) → W + (W + (d + d)) ≡ embed 2 * W + embed 2 * d
block3 W d = begin
    W + (W + (d + d))
      ≡⟨ sym (+-assoc W W (d + d)) ⟩
    (W + W) + (d + d)
      ≡⟨ cong (λ z → z + (d + d)) (sym (coef2 W)) ⟩
    embed 2 * W + (d + d)
      ≡⟨ cong (λ z → embed 2 * W + z) (sym (coef2 d)) ⟩
    embed 2 * W + embed 2 * d
  ∎

------------------------------------------------------------------------
-- Three copies of a doubled coefficient collapse to six
--
-- 三份二倍系数并成六倍

mergeA : (q : ℚ) → (embed 2 * q + embed 2 * q) + embed 2 * q ≡ embed 6 * q
mergeA q = begin
    (embed 2 * q + embed 2 * q) + embed 2 * q
      ≡⟨ cong (λ z → z + embed 2 * q) (sym (*-distribʳ-+ q (embed 2) (embed 2))) ⟩
    (embed 2 + embed 2) * q + embed 2 * q
      ≡⟨ sym (*-distribʳ-+ q (embed 2 + embed 2) (embed 2)) ⟩
    ((embed 2 + embed 2) + embed 2) * q
      ≡⟨ cong (λ z → z * q)
           (trans (cong (λ z → z + embed 2) (sym (embed-+-hom 2 2)))
                  (sym (embed-+-hom 4 2))) ⟩
    embed 6 * q
  ∎

------------------------------------------------------------------------
-- Two, four and two copies of a coefficient collapse to eight
--
-- 二、四、二份系数并成八倍

mergeB : (q : ℚ) → embed 2 * q + (embed 4 * q + embed 2 * q) ≡ embed 8 * q
mergeB q = begin
    embed 2 * q + (embed 4 * q + embed 2 * q)
      ≡⟨ cong (λ z → embed 2 * q + z) (sym (*-distribʳ-+ q (embed 4) (embed 2))) ⟩
    embed 2 * q + (embed 4 + embed 2) * q
      ≡⟨ cong (λ z → embed 2 * q + z) (cong (λ w → w * q) (sym (embed-+-hom 4 2))) ⟩
    embed 2 * q + embed 6 * q
      ≡⟨ sym (*-distribʳ-+ q (embed 2) (embed 6)) ⟩
    (embed 2 + embed 6) * q
      ≡⟨ cong (λ z → z * q) (sym (embed-+-hom 2 6)) ⟩
    embed 8 * q
  ∎

------------------------------------------------------------------------
-- The three blocks merge into six widths plus eight gaps
--
-- 三块并成六个宽度加八个间隙

merge3 :
  (W d : ℚ) →
  (embed 2 * W + embed 2 * d) + ((embed 2 * W + embed 4 * d) + (embed 2 * W + embed 2 * d))
  ≡ embed 6 * W + embed 8 * d
merge3 W d = let
    a = embed 2 * W
    b = embed 2 * d
    c = embed 4 * d
  in begin
    (a + b) + ((a + c) + (a + b))
      ≡⟨ cong (λ z → (a + b) + z) (+interchange a c a b) ⟩
    (a + b) + ((a + a) + (c + b))
      ≡⟨ +interchange a b (a + a) (c + b) ⟩
    (a + (a + a)) + (b + (c + b))
      ≡⟨ cong (λ z → z + (b + (c + b))) (sym (+-assoc a a a)) ⟩
    ((a + a) + a) + (b + (c + b))
      ≡⟨ cong (λ z → z + (b + (c + b))) (mergeA W) ⟩
    embed 6 * W + (b + (c + b))
      ≡⟨ cong (λ z → embed 6 * W + z) (mergeB d) ⟩
    embed 6 * W + embed 8 * d
  ∎

------------------------------------------------------------------------
-- The accounting identity for the reciprocal budget
--
-- 倒数预算的记账恒等式

acct :
  (W d : ℚ) →
  ((W + (d + d)) + (((W + (d + d)) + d) + W)) + (W + ((W + d) + (W + (d + d))))
  ≡ embed 6 * W + embed 8 * d
acct W d = let
    X = W + (d + d)
    Y = (X + d) + W
    P = W
    Qq = (W + d) + X
  in begin
    (X + Y) + (P + Qq)
      ≡⟨ +interchange X Y P Qq ⟩
    (X + P) + (Y + Qq)
      ≡⟨ cong (λ z → z + (Y + Qq)) (block1 W d) ⟩
    (embed 2 * W + embed 2 * d) + (Y + Qq)
      ≡⟨ cong (λ z → (embed 2 * W + embed 2 * d) + z) (+interchange (X + d) W (W + d) X) ⟩
    (embed 2 * W + embed 2 * d) + (((X + d) + (W + d)) + (W + X))
      ≡⟨ cong (λ z → (embed 2 * W + embed 2 * d) + (z + (W + X))) (block2 W d) ⟩
    (embed 2 * W + embed 2 * d) + ((embed 2 * W + embed 4 * d) + (W + X))
      ≡⟨ cong (λ z → (embed 2 * W + embed 2 * d) + ((embed 2 * W + embed 4 * d) + z)) (block3 W d) ⟩
    (embed 2 * W + embed 2 * d) + ((embed 2 * W + embed 4 * d) + (embed 2 * W + embed 2 * d))
      ≡⟨ merge3 W d ⟩
    embed 6 * W + embed 8 * d
  ∎

------------------------------------------------------------------------
-- Subtracting a summand gives back the other summand
--
-- 减掉一个加项还回另一个

add-sub-self : (a b : ℚ) → (a + b) - b ≡ a
add-sub-self a b =
  trans (+-assoc a b (- b))
        (trans (cong (λ z → a + z) (+-inverseʳ b))
               (+-identityʳ a))

------------------------------------------------------------------------
-- Subtracting half gives back half
--
-- 减去一半还回一半

half-sub : (p : ℚ) → p - p * half ≡ p * half
half-sub p =
  trans (cong (λ z → z - p * half) (sym (two-half p)))
        (add-sub-self (p * half) (p * half))

------------------------------------------------------------------------
-- The meet of the two allowances
--
-- 两个额度的 meet

d-min :
  (c u : ℚ) → 0ℚ < c → 0ℚ < u →
  Σ ℚ (λ d → (0ℚ < d) ×
    (d ≤ (c * half) * (c * half) * u × d ≤ c * half))
d-min c u 0c 0u =
  let c2 = c * half
      0c2 : 0ℚ < c2
      0c2 = 0<mul c half 0c 0<half
      dd = (c2 * c2) * u
      0dd : 0ℚ < dd
      0dd = 0<mul (c2 * c2) u (0<mul c2 c2 0c2 0c2) 0u
      d = dd ⊓ c2
      0d : 0ℚ < d
      0d = pos-meet dd c2 0dd 0c2
  in d , 0d , (p⊓q≤p dd c2 , p⊓q≤q dd c2)

------------------------------------------------------------------------
-- The quadratic allowance charges at most 8u
--
-- 二次额度至多记 8u

d-eight-le :
  (d c u : ℚ) (0c : 0ℚ < c) (0u : 0ℚ < u) →
  d ≤ (c * half) * (c * half) * u →
  (d * embed 8) * (1/_ ((c * half) * (c * half))
    {{pos⇒nonZero ((c * half) * (c * half))
        {{pos*pos⇒pos (c * half)
            {{positive (0<mul c half 0c 0<half)}}
            (c * half)
            {{positive (0<mul c half 0c 0<half)}}}}}})
  ≤ embed 8 * u
d-eight-le d c u 0c 0u d≤ =
  let c2 = c * half
      cc = c2 * c2
      0c2 : 0ℚ < c2
      0c2 = 0<mul c half 0c 0<half
      0cc : 0ℚ < cc
      0cc = 0<mul c2 c2 0c2 0c2
      nzcc = pos⇒nonZero cc {{positive 0cc}}
      invcc = 1/_ cc {{nzcc}}
      0≤8 : 0ℚ ≤ embed 8
      0≤8 = <⇒≤ (0<embed-suc 7)
      0≤inv : 0ℚ ≤ invcc
      0≤inv = <⇒≤ (0<inv cc 0cc)
      step1 : d * embed 8 ≤ (cc * u) * embed 8
      step1 = *-monoʳ-≤-nonNeg (embed 8) {{nonNegative 0≤8}} d≤
      step2 : (d * embed 8) * invcc ≤ ((cc * u) * embed 8) * invcc
      step2 = *-monoʳ-≤-nonNeg invcc {{nonNegative 0≤inv}} step1
      eq : ((cc * u) * embed 8) * invcc ≡ embed 8 * u
      eq = trans (cong (λ z → z * invcc)
                       (*-comm (cc * u) (embed 8)))
                 (d-eight c2 u {{nzcc}})
  in subst (λ z → (d * embed 8) * invcc ≤ z) eq step2

------------------------------------------------------------------------
-- Multiplying by one half strictly shrinks a positive quantity
--
-- 正量乘二分之一严格变小

half-mul-< : (u : ℚ) → 0ℚ < u → u * half < u
half-mul-< u 0u =
  let 0uh : 0ℚ < u * half
      0uh = 0<mul u half 0u 0<half

      s : u * half + 0ℚ < u * half + (u * half)
      s = +-mono-≤-< (≤-refl {u * half}) 0uh

      s' : u * half < u * half + u * half
      s' = subst (λ z → z < u * half + u * half)
                 (+-identityʳ (u * half)) s

      h : u * half + u * half ≡ u
      h = two-half u
  in subst (λ z → u * half < z) h s'

------------------------------------------------------------------------
-- The inverse of the embedded three
--
-- 嵌入三的倒数

i3 : ℚ
i3 = 1/_ (embed 3) {{pos⇒nonZero (embed 3) {{positive 0<3}}}}

------------------------------------------------------------------------
-- The inverse of the embedded three is positive
--
-- 嵌入三的倒数为正

0i3 : 0ℚ < i3
0i3 = 0<inv (embed 3) 0<3

------------------------------------------------------------------------
-- The radius quota: three copies stay below one tenth of eps k
--
-- 半径额度：三份仍低于 εk 的十分之一

-- The quota is (u * inv 3) * half; three copies add up to u * half,
-- which is strictly below u. coef3 turns the triple sum into the
-- coefficient form and the inverse of 3 cancels against that
-- coefficient.
--
-- 额度取 (u·inv3)·half，三份加起来等于 u·half，严格小于 u。coef3 把
-- 三重和化成系数形式，3 的倒数与系数相消。
δ-quota : (k : ℕ) → Σ ℚ (λ q → (0ℚ < q) × (((q + q) + q) < ε k * ε 9))
δ-quota k =
  let u = ε k * ε 9
      0u : 0ℚ < u
      0u = 0<mul (ε k) (ε 9) (0<ε k) (0<ε 9)

      q = (u * i3) * half

      0q : 0ℚ < q
      0q = 0<mul (u * i3) half (0<mul u i3 0u 0i3) 0<half

      triple : ((q + q) + q) ≡ u * half
      triple = begin
          (q + q) + q
            ≡⟨ sym (coef3 q) ⟩
          embed 3 * ((u * i3) * half)
            ≡⟨ sym (*-assoc (embed 3) (u * i3) half) ⟩
          (embed 3 * (u * i3)) * half
            ≡⟨ cong (_* half) (sym (*-assoc (embed 3) u i3)) ⟩
          ((embed 3 * u) * i3) * half
            ≡⟨ cong (_* half) (cong (_* i3) (*-comm (embed 3) u)) ⟩
          ((u * embed 3) * i3) * half
            ≡⟨ cong (_* half) (*-assoc u (embed 3) i3) ⟩
          (u * (embed 3 * i3)) * half
            ≡⟨ cong (_* half)
                 (cong (u *_) (*-inverseʳ (embed 3)
                   {{pos⇒nonZero (embed 3) {{positive 0<3}}}})) ⟩
          (u * 1ℚ) * half
            ≡⟨ cong (_* half) (*-identityʳ u) ⟩
          u * half
        ∎

      lt : u * half < u
      lt = half-mul-< u 0u
  in q , 0q , subst (λ z → z < u) (sym triple) lt

------------------------------------------------------------------------
-- The width quota: scaled by the coefficient it stays below one tenth
--
-- 宽度额度：乘以系数后仍低于 εk 的十分之一

-- The width allowance is W = embed (suc N) * q, and the quantity to be
-- controlled is 6W * inv (c*c). Taking q as (u * half) times the
-- inverse of P := embed (suc N) * (6 * inv (c*c)) makes that product
-- exactly u * half, which is strictly below u.
--
-- 宽度额度为 W = embed (suc N)·q，要控制的是 6W·inv(c*c)。取
-- q := (u·half)·inv P，其中 P := embed (suc N)·(6·inv(c*c))，则该乘积
-- 恰为 u·half，严格小于 u。
pick-q :
  (k : ℕ) (c : ℚ) (N : ℕ) (0c : 0ℚ < c) →
  Σ ℚ (λ q → (0ℚ < q) ×
    (embed 6 * (embed (suc N) * q))
      * (1/_ (c * c)
          {{pos⇒nonZero (c * c)
              {{pos*pos⇒pos c {{positive 0c}} c {{positive 0c}}}}}})
      < ε k * ε 9)
pick-q k c N 0c =
  let u = ε k * ε 9
      0u : 0ℚ < u
      0u = 0<mul (ε k) (ε 9) (0<ε k) (0<ε 9)

      iC = 1/_ (c * c)
             {{pos⇒nonZero (c * c)
                 {{pos*pos⇒pos c {{positive 0c}} c {{positive 0c}}}}}}

      0iC : 0ℚ < iC
      0iC = 0<inv (c * c) (0<mul c c 0c 0c)

      P = embed (suc N) * (embed 6 * iC)

      0P : 0ℚ < P
      0P = 0<mul (embed (suc N)) (embed 6 * iC) (0<embed-suc N)
             (0<mul (embed 6) iC 0<6 0iC)

      iP = 1/_ P {{pos⇒nonZero P {{positive 0P}}}}

      q = (u * half) * iP

      0q : 0ℚ < q
      0q = 0<mul (u * half) iP (0<mul u half 0u 0<half) (0<inv P 0P)

      reorder : (embed 6 * (embed (suc N) * q)) * iC ≡ P * q
      reorder = begin
          (embed 6 * (embed (suc N) * q)) * iC
            ≡⟨ *-assoc (embed 6) (embed (suc N) * q) iC ⟩
          embed 6 * ((embed (suc N) * q) * iC)
            ≡⟨ cong (embed 6 *_) (*-assoc (embed (suc N)) q iC) ⟩
          embed 6 * (embed (suc N) * (q * iC))
            ≡⟨ cong (embed 6 *_) (cong (embed (suc N) *_) (*-comm q iC)) ⟩
          embed 6 * (embed (suc N) * (iC * q))
            ≡⟨ cong (embed 6 *_) (sym (*-assoc (embed (suc N)) iC q)) ⟩
          embed 6 * ((embed (suc N) * iC) * q)
            ≡⟨ sym (*-assoc (embed 6) (embed (suc N) * iC) q) ⟩
          (embed 6 * (embed (suc N) * iC)) * q
            ≡⟨ cong (_* q) (cong (embed 6 *_) (*-comm (embed (suc N)) iC)) ⟩
          (embed 6 * (iC * embed (suc N))) * q
            ≡⟨ cong (_* q) (sym (*-assoc (embed 6) iC (embed (suc N)))) ⟩
          ((embed 6 * iC) * embed (suc N)) * q
            ≡⟨ cong (_* q) (*-comm (embed 6 * iC) (embed (suc N))) ⟩
          (embed (suc N) * (embed 6 * iC)) * q
        ∎

      cancel : P * q ≡ u * half
      cancel = begin
          P * ((u * half) * iP)
            ≡⟨ sym (*-assoc P (u * half) iP) ⟩
          (P * (u * half)) * iP
            ≡⟨ cong (_* iP) (*-comm P (u * half)) ⟩
          ((u * half) * P) * iP
            ≡⟨ *-assoc (u * half) P iP ⟩
          (u * half) * (P * iP)
            ≡⟨ cong ((u * half) *_) (*-inverseʳ P {{pos⇒nonZero P {{positive 0P}}}}) ⟩
          (u * half) * 1ℚ
            ≡⟨ *-identityʳ (u * half) ⟩
          u * half
        ∎

      lt : u * half < u
      lt = half-mul-< u 0u
  in q , 0q , subst (λ z → z < u) (sym (trans reorder cancel)) lt
