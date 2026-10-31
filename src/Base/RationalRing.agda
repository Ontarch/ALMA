------------------------------------------------------------------------
-- Shared ring-rearrangement lemmas over ℚ
--
-- ℚ 上的共享环重排引理
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module Base.RationalRing where

open import Data.Rational using (0ℚ; 1ℚ; _+_; _*_; _-_; -_; _<_; _≤_)
open import Data.Rational.Properties using
  (+-assoc; +-comm; +-identityˡ; +-identityʳ; +-inverseˡ; *-assoc; *-comm
  ; *-identityˡ; *-zeroˡ; *-distribˡ-+; *-distribʳ-+; neg-distrib-+
  ; neg-distribˡ-*; neg-distribʳ-*; <⇒≤; positive⁻¹)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; sym; trans; cong; cong₂; module ≡-Reasoning)
open ≡-Reasoning

------------------------------------------------------------------------
-- Unit and zero constants
--
-- 单位与零常量

-- The rational unit is positive.
--
-- 有理数单位为正。
0<1 : 0ℚ < 1ℚ
0<1 = positive⁻¹ 1ℚ

-- The rational unit is nonnegative.
--
-- 有理数单位非负。
0≤1 : 0ℚ ≤ 1ℚ
0≤1 = <⇒≤ 0<1

------------------------------------------------------------------------
-- Negation
--
-- 取负

-- Double negation is the identity.
--
-- 双重取负为恒等。
neg-involutive : ∀ x → - (- x) ≡ x
neg-involutive x = begin
  - (- x)
  ≡⟨ sym (+-identityʳ (- (- x))) ⟩
  - (- x) + 0ℚ
  ≡⟨ cong (- (- x) +_) (sym (+-inverseˡ x)) ⟩
  - (- x) + (- x + x)
  ≡⟨ sym (+-assoc (- (- x)) (- x) x) ⟩
  (- (- x) + - x) + x
  ≡⟨ cong (_+ x) (+-inverseˡ (- x)) ⟩
  0ℚ + x
  ≡⟨ +-identityˡ x ⟩
  x ∎

-- The product of two negations is the original product.
--
-- 两个取负相乘得到原乘积。
neg-neg-mul : ∀ x y → (- x) * (- y) ≡ x * y
neg-neg-mul x y = begin
  (- x) * (- y)
  ≡⟨ sym (neg-distribˡ-* x (- y)) ⟩
  - (x * (- y))
  ≡⟨ cong -_ (sym (neg-distribʳ-* x y)) ⟩
  - (- (x * y))
  ≡⟨ neg-involutive (x * y) ⟩
  x * y ∎

-- Negation does not change the square.
--
-- 取负不改变平方。
neg-neg-square : ∀ x → (- x) * (- x) ≡ x * x
neg-neg-square x = neg-neg-mul x x

------------------------------------------------------------------------
-- Additive rearrangement
--
-- 加法重排

-- Swapping the inner two summands leaves a four-term sum unchanged.
--
-- 交换内层两个加项后四项和不变。
+interchange : ∀ a b c d → (a + b) + (c + d) ≡ (a + c) + (b + d)
+interchange a b c d = begin
  (a + b) + (c + d)
  ≡⟨ +-assoc a b (c + d) ⟩
  a + (b + (c + d))
  ≡⟨ cong (a +_) (sym (+-assoc b c d)) ⟩
  a + ((b + c) + d)
  ≡⟨ cong (a +_) (cong (_+ d) (+-comm b c)) ⟩
  a + ((c + b) + d)
  ≡⟨ cong (a +_) (+-assoc c b d) ⟩
  a + (c + (b + d))
  ≡⟨ sym (+-assoc a c (b + d)) ⟩
  (a + c) + (b + d) ∎

-- Reassociate a left-leaning four-term sum into right-nested form.
--
-- 将左倾的四项和重组为右结合。
flat4 : ∀ p q r s → ((p + q) + r) + s ≡ p + (q + (r + s))
flat4 p q r s = begin
  ((p + q) + r) + s
  ≡⟨ +-assoc (p + q) r s ⟩
  (p + q) + (r + s)
  ≡⟨ +-assoc p q (r + s) ⟩
  p + (q + (r + s)) ∎

-- A negated pair cancels against the corresponding positive pair.
--
-- 取负对与正对相消。
cancel-pair : ∀ t → (- t + - t) + (t + t) ≡ 0ℚ
cancel-pair t = begin
  (- t + - t) + (t + t)
  ≡⟨ cong (_+ (t + t)) (sym (neg-distrib-+ t t)) ⟩
  (- (t + t)) + (t + t)
  ≡⟨ +-inverseˡ (t + t) ⟩
  0ℚ ∎

-- Two adjacent differences combine into a single difference, with the
-- middle term cancelling.
--
-- 相邻差合并：中间项抵消。
telescope : ∀ a b c → (a + (- b)) + (b + (- c)) ≡ a + (- c)
telescope a b c = begin
  (a + (- b)) + (b + (- c))
  ≡⟨ +-assoc a (- b) (b + (- c)) ⟩
  a + ((- b) + (b + (- c)))
  ≡⟨ cong (a +_) (sym (+-assoc (- b) b (- c))) ⟩
  a + (((- b) + b) + (- c))
  ≡⟨ cong (a +_) (cong (_+ (- c)) (+-inverseˡ b)) ⟩
  a + (0ℚ + (- c))
  ≡⟨ cong (a +_) (+-identityˡ (- c)) ⟩
  a + (- c) ∎

------------------------------------------------------------------------
-- Squares
--
-- 平方

-- Square of a sum: two squares plus two cross terms.
--
-- 和之平方展开：拆成两个平方加上两个交叉项。
sq+ : ∀ x y → (x + y) * (x + y) ≡
              x * x + (y * y + (x * y + x * y))
sq+ x y = begin
  (x + y) * (x + y)
  ≡⟨ *-distribʳ-+ (x + y) x y ⟩
  x * (x + y) + y * (x + y)
  ≡⟨ cong₂ _+_ (*-distribˡ-+ x x y) (*-distribˡ-+ y x y) ⟩
  (x * x + x * y) + (y * x + y * y)
  ≡⟨ cong (λ t → (x * x + x * y) + (t + y * y)) (*-comm y x) ⟩
  (x * x + x * y) + (x * y + y * y)
  ≡⟨ +-assoc (x * x) (x * y) (x * y + y * y) ⟩
  x * x + (x * y + (x * y + y * y))
  ≡⟨ cong (x * x +_) (sym (+-assoc (x * y) (x * y) (y * y))) ⟩
  x * x + ((x * y + x * y) + y * y)
  ≡⟨ cong (x * x +_) (+-comm (x * y + x * y) (y * y)) ⟩
  x * x + (y * y + (x * y + x * y)) ∎

-- Square of a difference: as for sums, but the cross terms are negated.
--
-- 差之平方展开：与和的情形相同，交叉项取负。
sq- : ∀ x y → (x - y) * (x - y) ≡
              x * x + (y * y + (- (x * y) + - (x * y)))
sq- x y = begin
  (x - y) * (x - y)
  ≡⟨ refl ⟩
  (x + (- y)) * (x + (- y))
  ≡⟨ sq+ x (- y) ⟩
  x * x + ((- y) * (- y) + (x * (- y) + x * (- y)))
  ≡⟨ cong (x * x +_)
          (cong₂ _+_ (neg-neg-square y)
                     (cong₂ _+_ (sym (neg-distribʳ-* x y))
                                (sym (neg-distribʳ-* x y)))) ⟩
  x * x + (y * y + (- (x * y) + - (x * y))) ∎

-- The square of a product is the product of the squares.
--
-- 乘积的平方等于平方的乘积。
sq-comm : ∀ x y → (x * y) * (x * y) ≡ (x * x) * (y * y)
sq-comm x y = begin
  (x * y) * (x * y)
  ≡⟨ *-assoc x y (x * y) ⟩
  x * (y * (x * y))
  ≡⟨ cong (x *_) (sym (*-assoc y x y)) ⟩
  x * ((y * x) * y)
  ≡⟨ cong (λ z → x * (z * y)) (*-comm y x) ⟩
  x * ((x * y) * y)
  ≡⟨ cong (x *_) (*-assoc x y y) ⟩
  x * (x * (y * y))
  ≡⟨ sym (*-assoc x x (y * y)) ⟩
  (x * x) * (y * y) ∎

-- By rearranging the four factors, the two cross products are equal.
--
-- 通过重排四个因子，两个交叉乘积相等。
cross-eq : ∀ a b c d → (a * c) * (b * d) ≡ (a * d) * (b * c)
cross-eq a b c d = trans canon₁ (sym canon₂)
  where
  canon₁ : (a * c) * (b * d) ≡ (a * b) * (c * d)
  canon₁ = begin
    (a * c) * (b * d)
    ≡⟨ *-assoc a c (b * d) ⟩
    a * (c * (b * d))
    ≡⟨ cong (a *_) (sym (*-assoc c b d)) ⟩
    a * ((c * b) * d)
    ≡⟨ cong (λ z → a * (z * d)) (*-comm c b) ⟩
    a * ((b * c) * d)
    ≡⟨ cong (a *_) (*-assoc b c d) ⟩
    a * (b * (c * d))
    ≡⟨ sym (*-assoc a b (c * d)) ⟩
    (a * b) * (c * d) ∎
  canon₂ : (a * d) * (b * c) ≡ (a * b) * (c * d)
  canon₂ = begin
    (a * d) * (b * c)
    ≡⟨ *-assoc a d (b * c) ⟩
    a * (d * (b * c))
    ≡⟨ cong (a *_) (sym (*-assoc d b c)) ⟩
    a * ((d * b) * c)
    ≡⟨ cong (λ z → a * (z * c)) (*-comm d b) ⟩
    a * ((b * d) * c)
    ≡⟨ cong (a *_) (*-assoc b d c) ⟩
    a * (b * (d * c))
    ≡⟨ cong (λ z → a * (b * z)) (*-comm d c) ⟩
    a * (b * (c * d))
    ≡⟨ sym (*-assoc a b (c * d)) ⟩
    (a * b) * (c * d) ∎

-- Mixed product law used by Rotation / Gaussian.
--
-- 供 Rotation / Gaussian 使用的混合积律。
swap-mid : ∀ x y z w → (x * y) * (z * w) ≡ (x * z) * (y * w)
swap-mid x y z w = begin
  (x * y) * (z * w)
  ≡⟨ *-assoc x y (z * w) ⟩
  x * (y * (z * w))
  ≡⟨ cong (x *_) (sym (*-assoc y z w)) ⟩
  x * ((y * z) * w)
  ≡⟨ cong (x *_) (cong (_* w) (*-comm y z)) ⟩
  x * ((z * y) * w)
  ≡⟨ cong (x *_) (*-assoc z y w) ⟩
  x * (z * (y * w))
  ≡⟨ sym (*-assoc x z (y * w)) ⟩
  (x * z) * (y * w) ∎

-- Swap the last two factors of a left-associated triple product.
--
-- 翻转左结合三元乘积的后两个因子。
flip3 : ∀ s x y → (s * x) * y ≡ (s * y) * x
flip3 s x y = begin
  (s * x) * y
  ≡⟨ *-assoc s x y ⟩
  s * (x * y)
  ≡⟨ cong (s *_) (*-comm x y) ⟩
  s * (y * x)
  ≡⟨ sym (*-assoc s y x) ⟩
  (s * y) * x ∎

------------------------------------------------------------------------
-- Mixed sign and subtraction
--
-- 混合符号与减法

-- Right distributivity of multiplication over subtraction.
--
-- 右乘减法的分配。
*ʳ-sub : ∀ x y z → (x - y) * z ≡ x * z - y * z
*ʳ-sub x y z = begin
  (x - y) * z
  ≡⟨ *-distribʳ-+ z x (- y) ⟩
  x * z + (- y) * z
  ≡⟨ cong (x * z +_) (sym (neg-distribˡ-* y z)) ⟩
  x * z - y * z ∎

-- Left distributivity of multiplication over subtraction.
--
-- 左乘减法的分配。
*ˡ-sub : ∀ x y z → x * (y - z) ≡ x * y - x * z
*ˡ-sub x y z = begin
  x * (y - z)
  ≡⟨ *-distribˡ-+ x y (- z) ⟩
  x * y + x * (- z)
  ≡⟨ cong (x * y +_) (sym (neg-distribʳ-* x z)) ⟩
  x * y - x * z ∎

-- Subtracting a sum is iterated subtraction.
--
-- 嵌套减法：减去和即反复减法。
sub-+-assoc : ∀ X Y Z → X - (Y + Z) ≡ (X - Y) - Z
sub-+-assoc X Y Z = begin
  X - (Y + Z)
  ≡⟨ cong (X +_) (neg-distrib-+ Y Z) ⟩
  X + (- Y + - Z)
  ≡⟨ sym (+-assoc X (- Y) (- Z)) ⟩
  (X - Y) - Z ∎

------------------------------------------------------------------------
-- Four-term regrouping
--
-- 四项归组

-- Interleave-regroup two groups of four terms.
--
-- 两组四项交错归组。
pairs4 : ∀ x₁ x₂ x₃ x₄ y₁ y₂ y₃ y₄ →
         (((x₁ + y₁) + (x₂ + y₂)) + ((x₃ + y₃) + (x₄ + y₄)))
         ≡ ((((x₁ + x₂) + x₃) + x₄) + (((y₁ + y₂) + y₃) + y₄))
pairs4 x₁ x₂ x₃ x₄ y₁ y₂ y₃ y₄ = begin
    (((x₁ + y₁) + (x₂ + y₂)) + ((x₃ + y₃) + (x₄ + y₄)))
  ≡⟨ cong₂ _+_ (+interchange x₁ y₁ x₂ y₂)
               (+interchange x₃ y₃ x₄ y₄) ⟩
    (((x₁ + x₂) + (y₁ + y₂)) + ((x₃ + x₄) + (y₃ + y₄)))
  ≡⟨ +interchange (x₁ + x₂) (y₁ + y₂) (x₃ + x₄) (y₃ + y₄) ⟩
    (((x₁ + x₂) + (x₃ + x₄)) + ((y₁ + y₂) + (y₃ + y₄)))
  ≡⟨ cong₂ _+_ (sym (+-assoc (x₁ + x₂) x₃ x₄))
               (sym (+-assoc (y₁ + y₂) y₃ y₄)) ⟩
    ((((x₁ + x₂) + x₃) + x₄) + (((y₁ + y₂) + y₃) + y₄)) ∎

-- Rotate the first two summands to the end.
--
-- 前两个加项旋到末尾。
rot4 : ∀ X Y U V → ((X + Y) + U) + V ≡ ((U + V) + X) + Y
rot4 X Y U V = begin
  ((X + Y) + U) + V
  ≡⟨ +-assoc (X + Y) U V ⟩
  (X + Y) + (U + V)
  ≡⟨ +-comm (X + Y) (U + V) ⟩
  (U + V) + (X + Y)
  ≡⟨ sym (+-assoc (U + V) X Y) ⟩
  ((U + V) + X) + Y ∎

-- Reverse all four summands.
--
-- 四个加项整体反转。
rev4 : ∀ X Y U V → ((X + Y) + U) + V ≡ ((V + U) + Y) + X
rev4 X Y U V = begin
  ((X + Y) + U) + V
  ≡⟨ +-assoc (X + Y) U V ⟩
  (X + Y) + (U + V)
  ≡⟨ +-comm (X + Y) (U + V) ⟩
  (U + V) + (X + Y)
  ≡⟨ cong₂ _+_ (+-comm U V) (+-comm X Y) ⟩
  (V + U) + (Y + X)
  ≡⟨ sym (+-assoc (V + U) Y X) ⟩
  ((V + U) + Y) + X ∎

-- Negating a signed four-term sum flips all signs.
--
-- 对带符号的四项和整体取负会将所有符号翻转。
neg4 : ∀ a b c d →
       - (((a + b) + - c) + - d) ≡ ((- a + - b) + c) + d
neg4 a b c d = begin
    - (((a + b) + - c) + - d)
  ≡⟨ neg-distrib-+ ((a + b) + - c) (- d) ⟩
    - ((a + b) + - c) + - (- d)
  ≡⟨ cong₂ _+_ (inner a b c) (neg-involutive d) ⟩
    ((- a + - b) + c) + d ∎
  where
  inner : ∀ a b c → - ((a + b) + - c) ≡ (- a + - b) + c
  inner a b c = begin
    - ((a + b) + - c)
    ≡⟨ neg-distrib-+ (a + b) (- c) ⟩
    - (a + b) + - (- c)
    ≡⟨ cong (λ t → - (a + b) + t) (neg-involutive c) ⟩
    - (a + b) + c
    ≡⟨ cong (λ t → t + c) (neg-distrib-+ a b) ⟩
    (- a + - b) + c ∎

-- Negate the expansion of a two-term signed sum.
--
-- 对两项带符号和的展开取负。
foldNeg : ∀ x y → - (x + - y) ≡ - x + y
foldNeg x y = begin
  - (x + - y)
  ≡⟨ neg-distrib-+ x (- y) ⟩
  - x + - (- y)
  ≡⟨ cong (- x +_) (neg-involutive y) ⟩
  - x + y ∎

------------------------------------------------------------------------
-- Scalar rearrangement
--
-- 数乘重排

-- Scalar factors can be reordered.
--
-- 数乘因子之间可交换顺序。
swap-scalar : ∀ {r} s x → (s * (r * x)) ≡ r * (s * x)
swap-scalar {r} s x = begin
  s * (r * x)
  ≡⟨ sym (*-assoc s r x) ⟩
  (s * r) * x
  ≡⟨ cong (λ z → z * x) (*-comm s r) ⟩
  (r * s) * x
  ≡⟨ *-assoc r s x ⟩
  r * (s * x) ∎

-- Exchange the outer and inner scalar factors inside a product.
--
-- 在乘积内交换外层与内层数乘因子。
frontS : ∀ {r} s z x → (s * (r * x)) * z ≡ r * ((s * x) * z)
frontS {r} s z x = begin
  (s * (r * x)) * z
  ≡⟨ cong (λ t → t * z) (swap-scalar {r} s x) ⟩
  (r * (s * x)) * z
  ≡⟨ *-assoc r (s * x) z ⟩
  r * ((s * x) * z) ∎

-- Negation through a product of two scalar factors and an extra factor.
--
-- 通过两个数乘因子与一个因子的乘积进行取负。
front-negS : ∀ {r} s z x →
             - ((s * (r * x)) * z) ≡ r * (- ((s * x) * z))
front-negS {r} s z x = begin
  - ((s * (r * x)) * z)
  ≡⟨ cong -_ (frontS {r} s z x) ⟩
  - (r * ((s * x) * z))
  ≡⟨ neg-distribʳ-* r ((s * x) * z) ⟩
  r * (- ((s * x) * z)) ∎

-- Factor r out of a four-term signed sum.
--
-- 从四项带符号和里提出 r。
factor4 : ∀ {r} x y z w →
          (((r * x + r * y) + r * (- z)) + r * (- w))
          ≡ r * (((x + y) + - z) + - w)
factor4 {r} x y z w = begin
    (((r * x + r * y) + r * (- z)) + r * (- w))
  ≡⟨ cong (λ t → (t + r * (- z)) + r * (- w))
          (sym (*-distribˡ-+ r x y)) ⟩
    ((r * (x + y) + r * (- z)) + r * (- w))
  ≡⟨ cong (λ t → t + r * (- w))
          (sym (*-distribˡ-+ r (x + y) (- z))) ⟩
    r * ((x + y) + - z) + r * (- w)
  ≡⟨ sym (*-distribˡ-+ r ((x + y) + - z) (- w)) ⟩
    r * (((x + y) + - z) + - w) ∎

------------------------------------------------------------------------
-- Unit / zero normalisation
--
-- 单位/零规范化

-- Multiplying by one and subtracting zero leaves the value unchanged.
--
-- 乘以一减去乘以零仍为原值。
norm1 : ∀ k → 1ℚ * k + - (0ℚ * k) ≡ k
norm1 k = begin
  1ℚ * k + - (0ℚ * k)
  ≡⟨ cong (λ x → 1ℚ * k + - x) (*-zeroˡ k) ⟩
  1ℚ * k + - 0ℚ
  ≡⟨ cong (λ x → x + - 0ℚ) (*-identityˡ k) ⟩
  k + - 0ℚ
  ≡⟨ +-identityʳ k ⟩
  k ∎

-- Three layers of zero leave the value unchanged.
--
-- 三层零相加仍为原值。
norm-tail : ∀ k → 0ℚ + (0ℚ + (0ℚ + k)) ≡ k
norm-tail k = begin
  0ℚ + (0ℚ + (0ℚ + k))
  ≡⟨ +-identityˡ (0ℚ + (0ℚ + k)) ⟩
  0ℚ + (0ℚ + k)
  ≡⟨ +-identityˡ (0ℚ + k) ⟩
  0ℚ + k
  ≡⟨ +-identityˡ k ⟩
  k ∎
