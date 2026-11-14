------------------------------------------------------------------------
-- Low-level lemmas for multiplication and endpoint bounds of products
--
-- 乘法连续性的底层引理与乘积端点界
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module Real.Interval.ContinuityMul where

open import Data.Nat using (ℕ) renaming (_≤_ to _≤ℕ_; _+_ to _+ℕ_)
open import Data.Nat.Properties using (m≤m+n) renaming (+-comm to +-commℕ)
open import Data.Product using (Σ; _,_; _×_)
open import Data.Rational using
  (ℚ; 0ℚ; _+_; _-_; _<_; _≤_; _⊓_; _⊔_; _*_; ∣_∣; nonNegative)
  renaming (-_ to neg)
open import Data.Rational.Properties using
  (+-assoc; +-comm; +-identityʳ; +-inverseʳ ; +-monoˡ-<; +-mono-≤; ≤-refl
  ; ≤-trans; <⇒≤; ≤-<-trans; <-≤-trans ; neg-antimono-≤; neg-distrib-+; ⊓-glb
  ; ⊔-lub; p⊓q≤p; p⊓q≤q ; p≤p⊔q; p≤q⊔p; ∣p*q∣≡∣p∣*∣q∣; *-monoʳ-≤-nonNeg
  ; *-monoˡ-≤-nonNeg ; 0≤∣p∣; *-comm)
open import Relation.Binary.PropositionalEquality using
  (_≡_; cong; sym; trans; subst; module ≡-Reasoning)
open ≡-Reasoning

open import Base.RationalRing using (neg-involutive; neg-0)
open import Real.IntervalEquiv using (l; u; l-mono; u-mono)
open import Real.Interval using (RealI; embedℚ; δ; δ-pos)
open import Real.Interval.Arith using (_+ℝ_; _-ℝ_; negℝ)
open import Real.Interval.Continuity using (Close; sub-add-cancel)
open import Real.Interval.Mul using (split-prod)
open import Real.Interval.Mul.Core using (abs-≤)
open import Real.Interval.Node using (u-hom; u-neg; l-hom; l-dyadic)
open import Real.Interval.OrderLe using (sub-mono)
open import Real.Interval.Rational using (r≤|r|; negsub)

------------------------------------------------------------------------
-- Rational bookkeeping
--
-- 有理数记账

-- Adding then subtracting the same term yields the original.
--
-- 加上 b 后再减去 b，结果归约为原值。
add-sub-cancel : (a b : ℚ) → (a + b) + neg b ≡ a
add-sub-cancel a b = begin
  (a + b) + neg b
    ≡⟨ +-assoc a b (neg b) ⟩
  a + (b + neg b)
    ≡⟨ cong (a +_) (+-inverseʳ b) ⟩
  a + 0ℚ
    ≡⟨ +-identityʳ a ⟩
  a
    ∎

-- Adding then subtracting the leading term yields the trailing term.
--
-- 由 b + c 减去首项 b，结果归约为 c。
sandwich-right : (b c : ℚ) → (b + c) + neg b ≡ c
sandwich-right b c = begin
  (b + c) + neg b
    ≡⟨ cong (_+ neg b) (+-comm b c) ⟩
  (c + b) + neg b
    ≡⟨ +-assoc c b (neg b) ⟩
  c + (b + neg b)
    ≡⟨ cong (c +_) (+-inverseʳ b) ⟩
  c + 0ℚ
    ≡⟨ +-identityʳ c ⟩
  c
    ∎

-- Swapping associativity to move the middle term to the end.
--
-- 交换结合次序，把中间项移位到末尾。
shift-inside : (b d e : ℚ) → (b + neg e) + d ≡ (b + d) + neg e
shift-inside b d e = begin
  (b + neg e) + d
    ≡⟨ +-assoc b (neg e) d ⟩
  b + (neg e + d)
    ≡⟨ cong (b +_) (+-comm (neg e) d) ⟩
  b + (d + neg e)
    ≡⟨ sym (+-assoc b d (neg e)) ⟩
  (b + d) + neg e
    ∎

-- Moving a subtraction out of a strict bound.
--
-- 由左侧已减去 c 的严格界，得到右侧加上 c 的严格界。
sub-cancel-< : (a b c : ℚ) → a - c < b → a < b + c
sub-cancel-< a b c h =
  subst (λ z → z < b + c) (sub-add-cancel a c) (+-monoˡ-< c h)

-- Moving a subtraction out of a strict bound (additive form).
--
-- 由右侧已减去 c 的严格界，得到左侧加上 c 的严格界。
addle-cancel-< : (a b c : ℚ) → a < b - c → a + c < b
addle-cancel-< a b c h =
  subst (λ z → a + c < z) (sub-add-cancel b c) (+-monoˡ-< c h)

-- Moving an addition across a strict bound.
--
-- 把左侧的加项移到右侧并变号。
cancel-add-< : (a b c : ℚ) → a + c < b → a < b - c
cancel-add-< a b c h =
  subst (λ z → z < b + neg c) (add-sub-cancel a c) (+-monoˡ-< (neg c) h)

-- Moving a subtraction across a strict bound.
--
-- 把左侧的减项移到不等式另一侧。
sub-left-< : (a b c : ℚ) → a < b + c → a - b < c
sub-left-< a b c h =
  subst (λ z → a + neg b < z) (sandwich-right b c) (+-monoˡ-< (neg b) h)

-- Budget rule: flip the addends across a strict bound.
--
-- 预算律：两侧同时减去 b 与 e。
budget-< : (a b d e : ℚ) → a + e < b + d → a - b < d - e
budget-< a b d e p =
  let q : a < b + (d - e)
      q = subst (λ z → a < z) (+-assoc b d (neg e)) (cancel-add-< a (b + d) e p)
  in sub-left-< a b (d - e) q

-- Weakening: subtracting a nonnegative amount makes the result smaller.
--
-- 当 e 非负时，减去 e 只会让结果变小。
weaken : (d e : ℚ) → 0ℚ ≤ e → d - e ≤ d
weaken d e 0≤e =
  let s : d + neg e ≤ d + 0ℚ
      s = subst (λ z → d + neg e ≤ d + z) neg-0
            (+-mono-≤ (≤-refl {d}) (neg-antimono-≤ 0≤e))
  in subst (λ z → d + neg e ≤ z) (+-identityʳ d) s

------------------------------------------------------------------------
-- Endpoint equations for the two shifted neighbourhoods
--
-- 两个平移邻域的端点等式

-- Every level expresses the shifted upper endpoint via the original
-- upper endpoint plus tolerance minus radius.
--
-- 每层上，平移区间的上端点等于原上端点加容差再减半径。
u-sub-emb : (x : RealI) (d : ℚ) (n : ℕ) → u (x -ℝ embedℚ d) n ≡ u x n + δ n - d
u-sub-emb x d n = begin
  u (x -ℝ embedℚ d) n
    ≡⟨ u-hom x (negℝ (embedℚ d)) n ⟩
  u x n + u (negℝ (embedℚ d)) n
    ≡⟨ cong (u x n +_) (u-neg (embedℚ d) n) ⟩
  u x n + neg (l (embedℚ d) n)
    ≡⟨ cong (u x n +_) (cong neg (l-dyadic d n)) ⟩
  u x n + neg (neg (δ n) + d)
    ≡⟨ cong (u x n +_) (neg-distrib-+ (neg (δ n)) d) ⟩
  u x n + (neg (neg (δ n)) + neg d)
    ≡⟨ cong (λ z → u x n + (z + neg d)) (neg-involutive (δ n)) ⟩
  u x n + (δ n + neg d)
    ≡⟨ sym (+-assoc (u x n) (δ n) (neg d)) ⟩
  (u x n + δ n) + neg d
    ∎

-- Every level expresses the shifted lower endpoint via the original
-- lower endpoint minus tolerance plus radius.
--
-- 每层上，平移区间的下端点等于原下端点减容差再加半径。
l-add-emb : (x : RealI) (d : ℚ) (n : ℕ) → l (x +ℝ embedℚ d) n ≡ l x n - δ n + d
l-add-emb x d n = begin
  l (x +ℝ embedℚ d) n
    ≡⟨ l-hom x (embedℚ d) n ⟩
  l x n + l (embedℚ d) n
    ≡⟨ cong (l x n +_) (l-dyadic d n) ⟩
  l x n + (neg (δ n) + d)
    ≡⟨ sym (+-assoc (l x n) (neg (δ n)) d) ⟩
  (l x n + neg (δ n)) + d
    ∎

------------------------------------------------------------------------
-- Difference bounds from one side of a neighbourhood
--
-- 由邻域单侧给出的差值界

-- If the shifted upper endpoint already lies below another interval's
-- lower endpoint at some level, then on every deeper level every pair
-- of endpoints differs by less than the radius.
--
-- 若平移后的上端点在某一层已经低于另一区间的下端点，则比这更深的所有层
-- 上端点差都小于半径。
node-diff-up : (d : ℚ) (x x' : RealI) (m : ℕ) →
  u (x -ℝ embedℚ d) m < l x' m →
  (k : ℕ) → m ≤ℕ k → (a a' : ℚ) →
  l x k ≤ a → a ≤ u x k → l x' k ≤ a' → a' ≤ u x' k →
  a - a' < d
node-diff-up d x x' m h k p a a' lx≤a a≤ux lx'≤a' a'≤ux' =
  let h' : (u x m + δ m) - d < l x' m
      h' = subst (λ z → z < l x' m) (u-sub-emb x d m) h

      s₁ : u x m + δ m < l x' m + d
      s₁ = sub-cancel-< (u x m + δ m) (l x' m) d h'

      s₂ : u x m - l x' m < d - δ m
      s₂ = budget-< (u x m) (l x' m) d (δ m) s₁

      s₃ : u x k - l x' k ≤ u x m - l x' m
      s₃ = sub-mono (u-mono x {n = m} {m = k} p)
                    (l-mono x' {n = m} {m = k} p)

      s₄ : a - a' ≤ u x k - l x' k
      s₄ = sub-mono a≤ux lx'≤a'

      s₅ : a - a' < d - δ m
      s₅ = ≤-<-trans (≤-trans s₄ s₃) s₂

      s₆ : d - δ m ≤ d
      s₆ = weaken d (δ m) (<⇒≤ (δ-pos m))
  in <-≤-trans s₅ s₆

-- If another interval's upper endpoint already lies below the shifted
-- lower endpoint at some level, then on every deeper level every
-- reversed pair of endpoints differs by less than the radius.
--
-- 若另一区间的上端点在某一层已经低于平移后的下端点，则比这更深的所有层
-- 上反向端点差都小于半径。
node-diff-down : (d : ℚ) (x x' : RealI) (m : ℕ) →
  u x' m < l (x +ℝ embedℚ d) m →
  (k : ℕ) → m ≤ℕ k → (a a' : ℚ) →
  l x k ≤ a → a ≤ u x k → l x' k ≤ a' → a' ≤ u x' k →
  a' - a < d
node-diff-down d x x' m h k p a a' lx≤a a≤ux lx'≤a' a'≤ux' =
  let h' : u x' m < (l x m + d) - δ m
      h' = subst (λ z → u x' m < z)
             (trans (l-add-emb x d m) (shift-inside (l x m) d (δ m))) h

      s₁ : u x' m + δ m < l x m + d
      s₁ = addle-cancel-< (u x' m) (l x m + d) (δ m) h'

      s₂ : u x' m - l x m < d - δ m
      s₂ = budget-< (u x' m) (l x m) d (δ m) s₁

      s₃ : u x' k - l x k ≤ u x' m - l x m
      s₃ = sub-mono (u-mono x' {n = m} {m = k} p)
                    (l-mono x {n = m} {m = k} p)

      s₄ : a' - a ≤ u x' k - l x k
      s₄ = sub-mono a'≤ux' lx≤a

      s₅ : a' - a < d - δ m
      s₅ = ≤-<-trans (≤-trans s₄ s₃) s₂

      s₆ : d - δ m ≤ d
      s₆ = weaken d (δ m) (<⇒≤ (δ-pos m))
  in <-≤-trans s₅ s₆

------------------------------------------------------------------------
-- A common level for both sides of a neighbourhood
--
-- 邻域两侧的共同层级

-- A single level carries both strict witnesses of a neighbourhood.
--
-- 单层同时承载邻域的两个严格见证。
close-levels : (d : ℚ) (x x' : RealI) → Close d x x' →
  Σ ℕ (λ m → (u (x -ℝ embedℚ d) m < l x' m) ×
             (u x' m < l (x +ℝ embedℚ d) m))
close-levels d x x' ((m₁ , w₁) , (m₂ , w₂)) =
  let m = m₁ +ℕ m₂

      p₁ : m₁ ≤ℕ m
      p₁ = m≤m+n m₁ m₂

      p₂ : m₂ ≤ℕ m
      p₂ = subst (λ z → m₂ ≤ℕ z) (+-commℕ m₂ m₁) (m≤m+n m₂ m₁)

      v₁ : u (x -ℝ embedℚ d) m < l x' m
      v₁ = <-≤-trans (≤-<-trans (u-mono (x -ℝ embedℚ d) {n = m₁} {m = m} p₁) w₁)
                     (l-mono x' {n = m₁} {m = m} p₁)

      v₂ : u x' m < l (x +ℝ embedℚ d) m
      v₂ = <-≤-trans (≤-<-trans (u-mono x' {n = m₂} {m = m} p₂) w₂)
                     (l-mono (x +ℝ embedℚ d) {n = m₂} {m = m} p₂)
  in m , v₁ , v₂

------------------------------------------------------------------------
-- Small rearrangements
--
-- 小的重排

-- Moving a leading addition to the other side (≤ form).
--
-- 把左侧的加项 e 移到右侧变成减项。
minus-shift : (a b e : ℚ) → a ≤ b + e → a - e ≤ b
minus-shift a b e h =
  let step : (b + e) + neg e ≤ b
      step = subst (λ z → z ≤ b)
               (sym (trans (cong (_+ neg e) (+-comm b e)) (sandwich-right e b)))
               (≤-refl {b})
  in ≤-trans (+-mono-≤ h (≤-refl {neg e})) step

-- Moving a leading subtraction to the other side (≤ form).
--
-- 把左侧的减项 b 移到右侧变成加项。
sub-right-≤ : (a b e : ℚ) → a - b ≤ e → a ≤ e + b
sub-right-≤ a b e h =
  subst (λ z → z ≤ e + b) (sub-add-cancel a b)
    (+-mono-≤ h (≤-refl {b}))

-- Moving a leading subtraction to the other side, with addends ordered.
--
-- 把左侧的减项 b 移到右侧变成加项，并交换加序。
sub-left-≤ : (a b e : ℚ) → a - b ≤ e → a ≤ b + e
sub-left-≤ a b e h = subst (λ z → a ≤ z) (+-comm e b) (sub-right-≤ a b e h)

-- Moving a leading subtraction to the other side and swapping roles.
--
-- 把左侧的减项 b 与右侧的项 e 互换位置。
shift-bound : (a b e : ℚ) → a - b ≤ e → a - e ≤ b
shift-bound a b e h = minus-shift a b e (sub-left-≤ a b e h)

-- Moving a trailing addition to the other side.
--
-- 把右侧的加项 e 移到左侧变成减项。
le-shift-sub : (a b e : ℚ) → a ≤ b + e → a - b ≤ e
le-shift-sub a b e h =
  subst (λ z → a - b ≤ z) (sandwich-right b e)
    (sub-mono {a = a} {a' = b + e} {b = b} {b' = b} h (≤-refl {b}))

------------------------------------------------------------------------
-- One-sided product difference
--
-- 单向乘积之差

-- Bounding a product difference from two closeness estimates. Only one
-- direction is needed: the same statement serves both as the gap between
-- two products and as the width of a single product.
--
-- 由两个接近性估计给出乘积之差的单向界。只需一个方向：同一陈述既用于
-- 两个乘积之间的间隙，也用于单个乘积的宽度。
prod-diff-one : (a a' b b' Mx My d e : ℚ) →
  0ℚ ≤ Mx → 0ℚ ≤ My →
  ∣ a ∣ ≤ Mx → ∣ b' ∣ ≤ My →
  ∣ a - a' ∣ ≤ d → ∣ b - b' ∣ ≤ e →
  a * b - a' * b' ≤ Mx * e + d * My
prod-diff-one a a' b b' Mx My d e Mx≥0 My≥0 |a|≤Mx |b'|≤My |a-a'|≤d |b-b'|≤e =
  let s : a * b - a' * b' ≡ a * (b - b') + (a - a') * b'
      s = split-prod a a' b b'

      t₁a : a * (b - b') ≤ ∣ a ∣ * ∣ b - b' ∣
      t₁a = subst (λ z → a * (b - b') ≤ z)
              (∣p*q∣≡∣p∣*∣q∣ a (b - b'))
              (r≤|r| (a * (b - b')))

      t₁b : ∣ a ∣ * ∣ b - b' ∣ ≤ Mx * ∣ b - b' ∣
      t₁b = *-monoʳ-≤-nonNeg ∣ b - b' ∣
              {{nonNegative (0≤∣p∣ (b - b'))}} |a|≤Mx

      t₁c : Mx * ∣ b - b' ∣ ≤ Mx * e
      t₁c = *-monoˡ-≤-nonNeg Mx {{nonNegative Mx≥0}} |b-b'|≤e

      t₁ : a * (b - b') ≤ Mx * e
      t₁ = ≤-trans t₁a (≤-trans t₁b t₁c)

      t₂a : (a - a') * b' ≤ ∣ a - a' ∣ * ∣ b' ∣
      t₂a = subst (λ z → (a - a') * b' ≤ z)
              (∣p*q∣≡∣p∣*∣q∣ (a - a') b')
              (r≤|r| ((a - a') * b'))

      t₂b : ∣ a - a' ∣ * ∣ b' ∣ ≤ d * ∣ b' ∣
      t₂b = *-monoʳ-≤-nonNeg ∣ b' ∣
              {{nonNegative (0≤∣p∣ b')}} |a-a'|≤d

      t₂c : d * ∣ b' ∣ ≤ d * My
      t₂c = *-monoˡ-≤-nonNeg d
              {{nonNegative (≤-trans (0≤∣p∣ (a - a')) |a-a'|≤d)}} |b'|≤My

      t₂ : (a - a') * b' ≤ d * My
      t₂ = ≤-trans t₂a (≤-trans t₂b t₂c)

      out : a * (b - b') + (a - a') * b' ≤ Mx * e + d * My
      out = +-mono-≤ t₁ t₂
  in subst (λ z → z ≤ Mx * e + d * My) (sym s) out

------------------------------------------------------------------------
-- Extreme corners
--
-- 四角的极值

-- Iterated minimum of four rationals.
--
-- 四个有理数的迭代最小值。
min4 : ℚ → ℚ → ℚ → ℚ → ℚ
min4 p q r s = (p ⊓ q) ⊓ (r ⊓ s)

-- Iterated maximum of four rationals.
--
-- 四个有理数的迭代最大值。
max4 : ℚ → ℚ → ℚ → ℚ → ℚ
max4 p q r s = (p ⊔ q) ⊔ (r ⊔ s)

-- A corner-wise gap moves the minimum upwards.
--
-- 逐角的间隙把最小值整体上移。
min4-shift : (p q r s p' q' r' s' K : ℚ) →
  p ≤ p' + K → q ≤ q' + K → r ≤ r' + K → s ≤ s' + K →
  min4 p q r s ≤ min4 p' q' r' s' + K
min4-shift p q r s p' q' r' s' K hp hq hr hs =
  let L = min4 p q r s
      M = min4 p' q' r' s'

      L≤p : L ≤ p
      L≤p = ≤-trans (p⊓q≤p (p ⊓ q) (r ⊓ s)) (p⊓q≤p p q)

      L≤q : L ≤ q
      L≤q = ≤-trans (p⊓q≤p (p ⊓ q) (r ⊓ s)) (p⊓q≤q p q)

      L≤r : L ≤ r
      L≤r = ≤-trans (p⊓q≤q (p ⊓ q) (r ⊓ s)) (p⊓q≤p r s)

      L≤s : L ≤ s
      L≤s = ≤-trans (p⊓q≤q (p ⊓ q) (r ⊓ s)) (p⊓q≤q r s)

      h₁ : L - K ≤ p'
      h₁ = minus-shift L p' K (≤-trans L≤p hp)

      h₂ : L - K ≤ q'
      h₂ = minus-shift L q' K (≤-trans L≤q hq)

      h₃ : L - K ≤ r'
      h₃ = minus-shift L r' K (≤-trans L≤r hr)

      h₄ : L - K ≤ s'
      h₄ = minus-shift L s' K (≤-trans L≤s hs)

      g₁ : L - K ≤ p' ⊓ q'
      g₁ = ⊓-glb h₁ h₂

      g₂ : L - K ≤ r' ⊓ s'
      g₂ = ⊓-glb h₃ h₄

      g : L - K ≤ M
      g = ⊓-glb g₁ g₂
  in subst (λ z → L ≤ z) (+-comm K M) (sub-left-≤ L K M g)

-- A corner-wise gap moves the maximum downwards.
--
-- 逐角的间隙把最大值整体下移。
max4-shift : (p q r s p' q' r' s' K : ℚ) →
  p' ≤ p + K → q' ≤ q + K → r' ≤ r + K → s' ≤ s + K →
  max4 p' q' r' s' ≤ max4 p q r s + K
max4-shift p q r s p' q' r' s' K hp hq hr hs =
  let N = max4 p q r s

      p≤N : p ≤ N
      p≤N = ≤-trans (p≤p⊔q p q) (p≤p⊔q (p ⊔ q) (r ⊔ s))

      q≤N : q ≤ N
      q≤N = ≤-trans (p≤q⊔p p q) (p≤p⊔q (p ⊔ q) (r ⊔ s))

      r≤N : r ≤ N
      r≤N = ≤-trans (p≤p⊔q r s) (p≤q⊔p (p ⊔ q) (r ⊔ s))

      s≤N : s ≤ N
      s≤N = ≤-trans (p≤q⊔p r s) (p≤q⊔p (p ⊔ q) (r ⊔ s))

      h₁ : p' ≤ N + K
      h₁ = ≤-trans hp (+-mono-≤ p≤N (≤-refl {K}))

      h₂ : q' ≤ N + K
      h₂ = ≤-trans hq (+-mono-≤ q≤N (≤-refl {K}))

      h₃ : r' ≤ N + K
      h₃ = ≤-trans hr (+-mono-≤ r≤N (≤-refl {K}))

      h₄ : s' ≤ N + K
      h₄ = ≤-trans hs (+-mono-≤ s≤N (≤-refl {K}))

      g₁ : p' ⊔ q' ≤ N + K
      g₁ = ⊔-lub h₁ h₂

      g₂ : r' ⊔ s' ≤ N + K
      g₂ = ⊔-lub h₃ h₄

      g : max4 p' q' r' s' ≤ N + K
      g = ⊔-lub g₁ g₂
  in g

-- Combine a gap and a width into a gap against the other minimum.
--
-- 把间隙与宽度合成为对另一侧最小值的界。
max-gap : (p q r s p' q' r' s' K B : ℚ) →
  min4 p q r s ≤ min4 p' q' r' s' + K →
  max4 p q r s - min4 p q r s ≤ B →
  max4 p q r s ≤ min4 p' q' r' s' + (K + B)
max-gap p q r s p' q' r' s' K B hK hB =
  let h₁ : max4 p q r s ≤ min4 p q r s + B
      h₁ = sub-left-≤ (max4 p q r s) (min4 p q r s) B hB

      h₂ : min4 p q r s + B ≤ (min4 p' q' r' s' + K) + B
      h₂ = +-mono-≤ hK (≤-refl {B})
  in subst (λ z → max4 p q r s ≤ z) (+-assoc (min4 p' q' r' s') K B)
       (≤-trans h₁ h₂)

------------------------------------------------------------------------
-- Width of a four-corner product at one level
--
-- 单层上四角乘积的宽度

-- On a single level, the four corner products differ pairwise by a
-- uniform bound; hence the maximum and minimum also differ by that
-- bound.
--
-- 同一层上乘积四角两两之差有统一上界；据此最大值与最小值之差也不超过
-- 该上界。
width4 : (Mx My lx ux ly uy : ℚ) →
  0ℚ ≤ Mx → 0ℚ ≤ My →
  neg Mx ≤ lx → ux ≤ Mx → neg My ≤ ly → uy ≤ My →
  lx ≤ ux → ly ≤ uy →
  max4 (lx * ly) (lx * uy) (ux * ly) (ux * uy)
    - min4 (lx * ly) (lx * uy) (ux * ly) (ux * uy)
  ≤ Mx * (uy - ly) + My * (ux - lx)
width4 Mx My lx ux ly uy Mx≥0 My≥0 lx≥-Mx ux≤Mx ly≥-My uy≤My lx≤ux ly≤uy =
  let Δx = ux - lx
      Δy = uy - ly
      B = Mx * Δy + My * Δx

      c11 = lx * ly
      c12 = lx * uy
      c21 = ux * ly
      c22 = ux * uy

      ab : (a : ℚ) → lx ≤ a → a ≤ ux → ∣ a ∣ ≤ Mx
      ab a lxa aux = abs-≤ (≤-trans lx≥-Mx lxa) (≤-trans aux ux≤Mx)

      bb : (b : ℚ) → ly ≤ b → b ≤ uy → ∣ b ∣ ≤ My
      bb b lyb buy = abs-≤ (≤-trans ly≥-My lyb) (≤-trans buy uy≤My)


      ad : (a a' : ℚ) → lx ≤ a → a ≤ ux → lx ≤ a' → a' ≤ ux → ∣ a - a' ∣ ≤ Δx
      ad a a' la ua la' ua' =
        abs-≤
          (subst (λ z → z ≤ a - a') (sym (negsub ux lx))
                 (sub-mono {a = lx} {a' = a} {b = ux} {b' = a'} la ua'))
          (sub-mono {a = a} {a' = ux} {b = a'} {b' = lx} ua la')

      bd : (b b' : ℚ) → ly ≤ b → b ≤ uy → ly ≤ b' → b' ≤ uy → ∣ b - b' ∣ ≤ Δy
      bd b b' lb ub lb' ub' =
        abs-≤
          (subst (λ z → z ≤ b - b') (sym (negsub uy ly))
                 (sub-mono {a = ly} {a' = b} {b = uy} {b' = b'} lb ub'))
          (sub-mono {a = b} {a' = uy} {b = b'} {b' = ly} ub lb')

      pair : (a a' b b' : ℚ) →
             lx ≤ a → a ≤ ux → lx ≤ a' → a' ≤ ux →
             ly ≤ b → b ≤ uy → ly ≤ b' → b' ≤ uy →
             a * b - a' * b' ≤ B
      pair a a' b b' la ua la' ua' lb ub lb' ub' =
        subst (λ z → a * b - a' * b' ≤ z) (cong (λ w → Mx * Δy + w) (*-comm Δx My))
          (prod-diff-one a a' b b' Mx My Δx Δy Mx≥0 My≥0
            (ab a la ua) (bb b' lb' ub') (ad a a' la ua la' ua')
            (bd b b' lb ub lb' ub'))

      -- Corner c11: c11 - B is below all four corners.
      --
      -- 角 c11：c11 - B 低于全部四角。
      a1 : c11 - B ≤ c11
      a1 = shift-bound c11 c11 B
             (pair lx lx ly ly (≤-refl {lx}) lx≤ux (≤-refl {lx}) lx≤ux
                   (≤-refl {ly}) ly≤uy (≤-refl {ly}) ly≤uy)

      a2 : c11 - B ≤ c12
      a2 = shift-bound c11 c12 B
             (pair lx lx ly uy (≤-refl {lx}) lx≤ux (≤-refl {lx}) lx≤ux
                   (≤-refl {ly}) ly≤uy ly≤uy (≤-refl {uy}))

      a3 : c11 - B ≤ c21
      a3 = shift-bound c11 c21 B
             (pair lx ux ly ly (≤-refl {lx}) lx≤ux lx≤ux (≤-refl {ux})
                   (≤-refl {ly}) ly≤uy (≤-refl {ly}) ly≤uy)

      a4 : c11 - B ≤ c22
      a4 = shift-bound c11 c22 B
             (pair lx ux ly uy (≤-refl {lx}) lx≤ux lx≤ux (≤-refl {ux})
                   (≤-refl {ly}) ly≤uy ly≤uy (≤-refl {uy}))

      -- Corner c12.
      --
      -- 角 c12。
      b1 : c12 - B ≤ c11
      b1 = shift-bound c12 c11 B
             (pair lx lx uy ly (≤-refl {lx}) lx≤ux (≤-refl {lx}) lx≤ux
                   ly≤uy (≤-refl {uy}) (≤-refl {ly}) ly≤uy)

      b2 : c12 - B ≤ c12
      b2 = shift-bound c12 c12 B
             (pair lx lx uy uy (≤-refl {lx}) lx≤ux (≤-refl {lx}) lx≤ux
                   ly≤uy (≤-refl {uy}) ly≤uy (≤-refl {uy}))

      b3 : c12 - B ≤ c21
      b3 = shift-bound c12 c21 B
             (pair lx ux uy ly (≤-refl {lx}) lx≤ux lx≤ux (≤-refl {ux})
                   ly≤uy (≤-refl {uy}) (≤-refl {ly}) ly≤uy)

      b4 : c12 - B ≤ c22
      b4 = shift-bound c12 c22 B
             (pair lx ux uy uy (≤-refl {lx}) lx≤ux lx≤ux (≤-refl {ux})
                   ly≤uy (≤-refl {uy}) ly≤uy (≤-refl {uy}))

      -- Corner c21.
      --
      -- 角 c21。
      c1 : c21 - B ≤ c11
      c1 = shift-bound c21 c11 B
             (pair ux lx ly ly lx≤ux (≤-refl {ux}) (≤-refl {lx}) lx≤ux
                   (≤-refl {ly}) ly≤uy (≤-refl {ly}) ly≤uy)

      c2 : c21 - B ≤ c12
      c2 = shift-bound c21 c12 B
             (pair ux lx ly uy lx≤ux (≤-refl {ux}) (≤-refl {lx}) lx≤ux
                   (≤-refl {ly}) ly≤uy ly≤uy (≤-refl {uy}))

      c3 : c21 - B ≤ c21
      c3 = shift-bound c21 c21 B
             (pair ux ux ly ly lx≤ux (≤-refl {ux}) lx≤ux (≤-refl {ux})
                   (≤-refl {ly}) ly≤uy (≤-refl {ly}) ly≤uy)

      c4 : c21 - B ≤ c22
      c4 = shift-bound c21 c22 B
             (pair ux ux ly uy lx≤ux (≤-refl {ux}) lx≤ux (≤-refl {ux})
                   (≤-refl {ly}) ly≤uy ly≤uy (≤-refl {uy}))

      -- Corner c22.
      --
      -- 角 c22。
      d1 : c22 - B ≤ c11
      d1 = shift-bound c22 c11 B
             (pair ux lx uy ly lx≤ux (≤-refl {ux}) (≤-refl {lx}) lx≤ux
                   ly≤uy (≤-refl {uy}) (≤-refl {ly}) ly≤uy)

      d2 : c22 - B ≤ c12
      d2 = shift-bound c22 c12 B
             (pair ux lx uy uy lx≤ux (≤-refl {ux}) (≤-refl {lx}) lx≤ux
                   ly≤uy (≤-refl {uy}) ly≤uy (≤-refl {uy}))

      d3 : c22 - B ≤ c21
      d3 = shift-bound c22 c21 B
             (pair ux ux uy ly lx≤ux (≤-refl {ux}) lx≤ux (≤-refl {ux})
                   ly≤uy (≤-refl {uy}) (≤-refl {ly}) ly≤uy)

      d4 : c22 - B ≤ c22
      d4 = shift-bound c22 c22 B
             (pair ux ux uy uy lx≤ux (≤-refl {ux}) lx≤ux (≤-refl {ux})
                   ly≤uy (≤-refl {uy}) ly≤uy (≤-refl {uy}))

      -- Each corner minus B is below the minimum.
      --
      -- 每个角减去 B 都低于最小值。
      m1 : c11 - B ≤ min4 c11 c12 c21 c22
      m1 = ⊓-glb (⊓-glb a1 a2) (⊓-glb a3 a4)

      m2 : c12 - B ≤ min4 c11 c12 c21 c22
      m2 = ⊓-glb (⊓-glb b1 b2) (⊓-glb b3 b4)

      m3 : c21 - B ≤ min4 c11 c12 c21 c22
      m3 = ⊓-glb (⊓-glb c1 c2) (⊓-glb c3 c4)

      m4 : c22 - B ≤ min4 c11 c12 c21 c22
      m4 = ⊓-glb (⊓-glb d1 d2) (⊓-glb d3 d4)

      -- Hence each corner is below the minimum plus B.
      --
      -- 于是每个角都在最小值加上 B 之下。
      s1 : c11 ≤ min4 c11 c12 c21 c22 + B
      s1 = sub-right-≤ c11 B (min4 c11 c12 c21 c22) m1

      s2 : c12 ≤ min4 c11 c12 c21 c22 + B
      s2 = sub-right-≤ c12 B (min4 c11 c12 c21 c22) m2

      s3 : c21 ≤ min4 c11 c12 c21 c22 + B
      s3 = sub-right-≤ c21 B (min4 c11 c12 c21 c22) m3

      s4 : c22 ≤ min4 c11 c12 c21 c22 + B
      s4 = sub-right-≤ c22 B (min4 c11 c12 c21 c22) m4

      j1 : c11 ⊔ c12 ≤ min4 c11 c12 c21 c22 + B
      j1 = ⊔-lub s1 s2

      j2 : c21 ⊔ c22 ≤ min4 c11 c12 c21 c22 + B
      j2 = ⊔-lub s3 s4

      top : max4 c11 c12 c21 c22 ≤ min4 c11 c12 c21 c22 + B
      top = ⊔-lub j1 j2
  in le-shift-sub (max4 c11 c12 c21 c22) (min4 c11 c12 c21 c22) B top
