------------------------------------------------------------------------
-- Shared ring-rearrangement lemmas over ℚ
--
-- ℚ 上的共享环重排引理
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module Base.RationalRing where

open import Data.Rational using (0ℚ; 1ℚ; _+_; _*_; _-_; -_)
open import Data.Rational.Properties using
  (+-assoc; +-comm; +-identityˡ; +-identityʳ; +-inverseˡ; *-assoc; *-comm; *-identityˡ
  ; *-zeroˡ; *-distribˡ-+; *-distribʳ-+; neg-distrib-+; neg-distribˡ-*; neg-distribʳ-*)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; sym; trans; cong; cong₂; module ≡-Reasoning)

------------------------------------------------------------------------
-- Negation
--
-- 取负

-- -(-x) = x.
neg-involutive : ∀ x → - (- x) ≡ x
neg-involutive x = let open ≡-Reasoning in begin
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

-- (-x)(-y) = xy.
neg-neg-mul : ∀ x y → (- x) * (- y) ≡ x * y
neg-neg-mul x y = let open ≡-Reasoning in begin
  (- x) * (- y)
  ≡⟨ sym (neg-distribˡ-* x (- y)) ⟩
  - (x * (- y))
  ≡⟨ cong -_ (sym (neg-distribʳ-* x y)) ⟩
  - (- (x * y))
  ≡⟨ neg-involutive (x * y) ⟩
  x * y ∎

-- (-x)(-x) = x*x.
neg-neg-square : ∀ x → (- x) * (- x) ≡ x * x
neg-neg-square x = neg-neg-mul x x

-- x * (-y) = -(x*y). The direction is opposite to stdlib's
-- neg-distribʳ-*.
--
-- x * (-y) = -(x*y)。方向与 stdlib 的 neg-distribʳ-* 相反。
n*ʳ : ∀ x y → x * (- y) ≡ - (x * y)
n*ʳ x y = sym (neg-distribʳ-* x y)

-- (-x) * y = -(x*y). The direction is opposite to stdlib's
-- neg-distribˡ-*, hence sym.
--
-- (-x) * y = -(x*y)。方向与 stdlib 的 neg-distribˡ-* 相反，故需要 sym。
n*ˡ : ∀ x y → (- x) * y ≡ - (x * y)
n*ˡ x y = sym (neg-distribˡ-* x y)

------------------------------------------------------------------------
-- Additive rearrangement
--
-- 加法重排

-- (a + b) + (c + d) = (a + c) + (b + d).
+interchange : ∀ a b c d → (a + b) + (c + d) ≡ (a + c) + (b + d)
+interchange a b c d = let open ≡-Reasoning in begin
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

-- ((p + q) + r) + s = p + (q + (r + s)).
flat4 : ∀ p q r s → ((p + q) + r) + s ≡ p + (q + (r + s))
flat4 p q r s = let open ≡-Reasoning in begin
  ((p + q) + r) + s
  ≡⟨ +-assoc (p + q) r s ⟩
  (p + q) + (r + s)
  ≡⟨ +-assoc p q (r + s) ⟩
  p + (q + (r + s)) ∎

-- (-t + -t) + (t + t) = 0.
cancel-pair : ∀ t → (- t + - t) + (t + t) ≡ 0ℚ
cancel-pair t = let open ≡-Reasoning in begin
  (- t + - t) + (t + t)
  ≡⟨ +-assoc (- t) (- t) (t + t) ⟩
  - t + ((- t) + (t + t))
  ≡⟨ cong (- t +_) (sym (+-assoc (- t) t t)) ⟩
  - t + (((- t) + t) + t)
  ≡⟨ cong (- t +_) (cong₂ _+_ (+-inverseˡ t) refl) ⟩
  - t + (0ℚ + t)
  ≡⟨ cong (- t +_) (+-identityˡ t) ⟩
  - t + t
  ≡⟨ +-inverseˡ t ⟩
  0ℚ ∎

------------------------------------------------------------------------
-- Squares
--
-- 平方

-- (x + y)² = x² + y² + (x*y + x*y).
sq+ : ∀ x y → (x + y) * (x + y) ≡
              x * x + (y * y + (x * y + x * y))
sq+ x y = let open ≡-Reasoning in begin
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

-- (x - y)² = x² + y² - (x*y + x*y).
sq- : ∀ x y → (x - y) * (x - y) ≡
              x * x + (y * y + (- (x * y) + - (x * y)))
sq- x y = let open ≡-Reasoning in begin
  (x - y) * (x - y)
  ≡⟨ refl ⟩
  (x + (- y)) * (x + (- y))
  ≡⟨ sq+ x (- y) ⟩
  x * x + ((- y) * (- y) + (x * (- y) + x * (- y)))
  ≡⟨ cong (x * x +_)
          (cong₂ _+_ (neg-neg-square y)
                     (cong₂ _+_ (n*ʳ x y) (n*ʳ x y))) ⟩
  x * x + (y * y + (- (x * y) + - (x * y))) ∎

-- (xy)² = x²y².
sq-comm : ∀ x y → (x * y) * (x * y) ≡ (x * x) * (y * y)
sq-comm x y = let open ≡-Reasoning in begin
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

-- (ac)(bd) = (ad)(bc).
cross-eq : ∀ a b c d → (a * c) * (b * d) ≡ (a * d) * (b * c)
cross-eq a b c d = trans canon₁ (sym canon₂)
  where
  canon₁ : (a * c) * (b * d) ≡ (a * b) * (c * d)
  canon₁ = let open ≡-Reasoning in begin
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
  canon₂ = let open ≡-Reasoning in begin
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
swap-mid x y z w = let open ≡-Reasoning in begin
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
flip3 s x y = let open ≡-Reasoning in begin
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

-- (x - y) * z = x*z - y*z.
*ʳ-sub : ∀ x y z → (x - y) * z ≡ x * z - y * z
*ʳ-sub x y z = let open ≡-Reasoning in begin
  (x - y) * z
  ≡⟨ *-distribʳ-+ z x (- y) ⟩
  x * z + (- y) * z
  ≡⟨ cong (x * z +_) (n*ˡ y z) ⟩
  x * z - y * z ∎

-- x * (y - z) = x*y - x*z.
*ˡ-sub : ∀ x y z → x * (y - z) ≡ x * y - x * z
*ˡ-sub x y z = let open ≡-Reasoning in begin
  x * (y - z)
  ≡⟨ *-distribˡ-+ x y (- z) ⟩
  x * y + x * (- z)
  ≡⟨ cong (x * y +_) (n*ʳ x z) ⟩
  x * y - x * z ∎

-- X - (Y + Z) = (X - Y) - Z.
sub-+-assoc : ∀ X Y Z → X - (Y + Z) ≡ (X - Y) - Z
sub-+-assoc X Y Z = let open ≡-Reasoning in begin
  X - (Y + Z)
  ≡⟨ cong (X +_) (neg-distrib-+ Y Z) ⟩
  X + (- Y + - Z)
  ≡⟨ sym (+-assoc X (- Y) (- Z)) ⟩
  (X - Y) - Z ∎

------------------------------------------------------------------------
-- Four-term regrouping
--
-- 四项归组

-- (x₁ + y₁) + (x₂ + y₂) = (x₁ + x₂) + (y₁ + y₂).
pairs2 : ∀ x₁ x₂ y₁ y₂ →
         (x₁ + y₁) + (x₂ + y₂) ≡ (x₁ + x₂) + (y₁ + y₂)
pairs2 x₁ x₂ y₁ y₂ = +interchange x₁ y₁ x₂ y₂

-- Interleave-regroup two groups of four terms.
--
-- 两组四项交错归组。
pairs4 : ∀ x₁ x₂ x₃ x₄ y₁ y₂ y₃ y₄ →
         (((x₁ + y₁) + (x₂ + y₂)) + ((x₃ + y₃) + (x₄ + y₄)))
         ≡ ((((x₁ + x₂) + x₃) + x₄) + (((y₁ + y₂) + y₃) + y₄))
pairs4 x₁ x₂ x₃ x₄ y₁ y₂ y₃ y₄ = let open ≡-Reasoning in begin
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
rot4 X Y U V = let open ≡-Reasoning in begin
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
rev4 X Y U V = let open ≡-Reasoning in begin
  ((X + Y) + U) + V
  ≡⟨ +-assoc (X + Y) U V ⟩
  (X + Y) + (U + V)
  ≡⟨ +-comm (X + Y) (U + V) ⟩
  (U + V) + (X + Y)
  ≡⟨ cong₂ _+_ (+-comm U V) (+-comm X Y) ⟩
  (V + U) + (Y + X)
  ≡⟨ sym (+-assoc (V + U) Y X) ⟩
  ((V + U) + Y) + X ∎

-- -(((a + b) + -c) + -d) = ((-a + -b) + c) + d.
neg4 : ∀ a b c d →
       - (((a + b) + - c) + - d) ≡ ((- a + - b) + c) + d
neg4 a b c d = let open ≡-Reasoning in begin
    - (((a + b) + - c) + - d)
  ≡⟨ neg-distrib-+ ((a + b) + - c) (- d) ⟩
    - ((a + b) + - c) + - (- d)
  ≡⟨ cong₂ _+_ (inner a b c) (neg-involutive d) ⟩
    ((- a + - b) + c) + d ∎
  where
  inner : ∀ a b c → - ((a + b) + - c) ≡ (- a + - b) + c
  inner a b c = let open ≡-Reasoning in begin
    - ((a + b) + - c)
    ≡⟨ neg-distrib-+ (a + b) (- c) ⟩
    - (a + b) + - (- c)
    ≡⟨ cong (λ t → - (a + b) + t) (neg-involutive c) ⟩
    - (a + b) + c
    ≡⟨ cong (λ t → t + c) (neg-distrib-+ a b) ⟩
    (- a + - b) + c ∎

-- Negate the expansion of a two-term signed sum.
--
-- 折叠两项带符号和的展开取负。
foldNeg : ∀ x y → - (x + - y) ≡ - x + y
foldNeg x y = let open ≡-Reasoning in begin
  - (x + - y)
  ≡⟨ neg-distrib-+ x (- y) ⟩
  - x + - (- y)
  ≡⟨ cong (- x +_) (neg-involutive y) ⟩
  - x + y ∎

------------------------------------------------------------------------
-- Scalar rearrangement
--
-- 数乘重排

-- s*(r*x) = r*(s*x).
swap-scalar : ∀ {r} s x → (s * (r * x)) ≡ r * (s * x)
swap-scalar {r} s x = let open ≡-Reasoning in begin
  s * (r * x)
  ≡⟨ sym (*-assoc s r x) ⟩
  (s * r) * x
  ≡⟨ cong (λ z → z * x) (*-comm s r) ⟩
  (r * s) * x
  ≡⟨ *-assoc r s x ⟩
  r * (s * x) ∎

-- (r*x)*z = r*(x*z).
front : ∀ {r} z x → (r * x) * z ≡ r * (x * z)
front {r} z x = *-assoc r x z

-- (s*(r*x))*z = r*((s*x)*z).
frontS : ∀ {r} s z x → (s * (r * x)) * z ≡ r * ((s * x) * z)
frontS {r} s z x = let open ≡-Reasoning in begin
  (s * (r * x)) * z
  ≡⟨ cong (λ t → t * z) (swap-scalar {r} s x) ⟩
  (r * (s * x)) * z
  ≡⟨ *-assoc r (s * x) z ⟩
  r * ((s * x) * z) ∎

-- -(r*x) = r*(-x).
front-neg : ∀ {r} x → - (r * x) ≡ r * (- x)
front-neg {r} x = neg-distribʳ-* r x

-- -((s*(r*x))*z) = r*(-((s*x)*z)).
front-negS : ∀ {r} s z x →
             - ((s * (r * x)) * z) ≡ r * (- ((s * x) * z))
front-negS {r} s z x = let open ≡-Reasoning in begin
  - ((s * (r * x)) * z)
  ≡⟨ cong -_ (frontS {r} s z x) ⟩
  - (r * ((s * x) * z))
  ≡⟨ front-neg {r} ((s * x) * z) ⟩
  r * (- ((s * x) * z)) ∎

-- Factor r out of two signed summands.
--
-- 从两个带符号加项中提出 r。
factor2 : ∀ {r} x y → r * x + r * (- y) ≡ r * (x + - y)
factor2 {r} x y = sym (*-distribˡ-+ r x (- y))

factor4 : ∀ {r} x y z w →
          (((r * x + r * y) + r * (- z)) + r * (- w))
          ≡ r * (((x + y) + - z) + - w)
factor4 {r} x y z w = let open ≡-Reasoning in begin
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

-- 1*k - 0*k = k.
norm1 : ∀ k → 1ℚ * k + - (0ℚ * k) ≡ k
norm1 k = let open ≡-Reasoning in begin
  1ℚ * k + - (0ℚ * k)
  ≡⟨ cong (λ x → 1ℚ * k + - x) (*-zeroˡ k) ⟩
  1ℚ * k + - 0ℚ
  ≡⟨ cong (λ x → x + - 0ℚ) (*-identityˡ k) ⟩
  k + - 0ℚ
  ≡⟨ +-identityʳ k ⟩
  k ∎

-- 0 + (0 + (0 + k)) = k.
norm-tail : ∀ k → 0ℚ + (0ℚ + (0ℚ + k)) ≡ k
norm-tail k = let open ≡-Reasoning in begin
  0ℚ + (0ℚ + (0ℚ + k))
  ≡⟨ +-identityˡ (0ℚ + (0ℚ + k)) ⟩
  0ℚ + (0ℚ + k)
  ≡⟨ +-identityˡ (0ℚ + k) ⟩
  0ℚ + k
  ≡⟨ +-identityˡ k ⟩
  k ∎
