------------------------------------------------------------------------
-- Nontrivial rational unitary
--
-- Norm conservation under a real rotation. A 2×2 real rotation
-- [[c, -s], [s, c]] with c² + s² = 1 mixes the two complex coordinates
-- of a two-level state. The total squared norm is conserved: the cross
-- terms from the two rows cancel pairwise because c*s = s*c, and the
-- diagonal terms carry the factor c² + s² = 1.
--
-- The orthogonality c² + s² = 1 is a carried hypothesis, not a logical
-- necessity: it is exactly the extra column-orthogonality that L2
-- amplitude dynamics require (contrast the L1 kernel law in
-- Stochastic). The concrete 3/5–4/5 pair realises it over ℚ.
--
-- 非平凡有理幺正
--
-- 实旋转下的范数守恒。2×2 实旋转 [[c,-s],[s,c]]（c²+s²=1）混合二能
-- 级态的两个复坐标。总平方范数守恒：两行展开的交叉项因 c*s=s*c 成对
-- 抵消，对角项带上因子 c²+s²=1。
--
-- 正交条件 c²+s²=1 是携带假设而非逻辑必然：它正是 L2 振幅动力学所需
-- 的额外列正交（对照 Stochastic 的 L1 核定律）。具体的 3/5–4/5 在 ℚ
-- 上实现它。
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module ALMA.Physics.Quantum.Rotation where

open import Data.Rational using (ℚ; 0ℚ; 1ℚ; _+_; _*_; _-_; -_; _/_)
open import Data.Rational.Properties using
  (+-assoc; +-comm; +-identityʳ; *-comm; *-identityˡ; *-distribʳ-+)
open import Data.Integer.Base using (ℤ; 1ℤ) renaming (_+_ to _ℤ+_)
open import Data.Product.Base using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; sym; cong; cong₂; module ≡-Reasoning)

open import ALMA.Physics.Quantum.Gaussian using (ℂ; re; im; norm²)
open import ALMA.Physics.RationalKit as Kit using
  (+interchange; swap-mid; sq+; sq-; cancel-pair)

------------------------------------------------------------------------
-- Local ring lemmas
--
-- cross-vanish, factor-left, factor-right and cross-eq carry four-term
-- shapes specific to the rotation matrix; they stay local. rot-real is
-- the core real-vector computation.
--
-- 本地环引理
--
-- cross-vanish、factor-left、factor-right、cross-eq 携带专为旋转矩阵
-- 定制的四项形状，留在本地；rot-real 是核心的实向量计算。

private
  -- Given u*v = x*y, the squared sum of a difference and a sum has its
  -- cross terms cancel, leaving the four plain squares.
  --
  -- 给定 u*v = x*y，一差一和平方和的交叉项抵消，只剩四个纯平方。
  cross-vanish : ∀ x y u v → u * v ≡ x * y →
    (x * x + (y * y + (- (x * y) + - (x * y)))) +
    (u * u + (v * v + (u * v + u * v))) ≡
    (x * x + u * u) + (y * y + v * v)
  cross-vanish x y u v eq = let open ≡-Reasoning in begin
    (x² + (y² + (P))) + (u² + (v² + (Q₀)))
    ≡⟨ cong (λ z → (x² + (y² + P)) + (u² + (v² + (z + z)))) eq ⟩
    (x² + (y² + P)) + (u² + (v² + Q))
    ≡⟨ cong₂ _+_ (sym (+-assoc x² y² P)) (sym (+-assoc u² v² Q)) ⟩
    ((x² + y²) + P) + ((u² + v²) + Q)
    ≡⟨ +interchange (x² + y²) P (u² + v²) Q ⟩
    ((x² + y²) + (u² + v²)) + (P + Q)
    ≡⟨ cong (_+ (P + Q)) (+interchange x² y² u² v²) ⟩
    ((x² + u²) + (y² + v²)) + (P + Q)
    ≡⟨ cong (((x² + u²) + (y² + v²)) +_) (cancel-pair t) ⟩
    ((x² + u²) + (y² + v²)) + 0ℚ
    ≡⟨ +-identityʳ ((x² + u²) + (y² + v²)) ⟩
    (x² + u²) + (y² + v²) ∎
    where
    x² = x * x ; y² = y * y ; u² = u * u ; v² = v * v
    t  = x * y
    P  = - t + - t
    Q₀ = u * v + u * v
    Q  = t + t

  -- (c*a)² + (s*a)² = (c² + s²)*a².
  --
  -- (c*a)² + (s*a)² = (c² + s²)*a²。
  factor-left : ∀ c s a →
    (c * a) * (c * a) + (s * a) * (s * a) ≡ (c * c + s * s) * (a * a)
  factor-left c s a = let open ≡-Reasoning in begin
    (c * a) * (c * a) + (s * a) * (s * a)
    ≡⟨ cong₂ _+_ (swap-mid c a c a) (swap-mid s a s a) ⟩
    (c * c) * (a * a) + (s * s) * (a * a)
    ≡⟨ sym (*-distribʳ-+ (a * a) (c * c) (s * s)) ⟩
    (c * c + s * s) * (a * a) ∎

  -- (s*d)² + (c*d)² = (c² + s²)*d².
  --
  -- (s*d)² + (c*d)² = (c² + s²)*d²。
  factor-right : ∀ c s d →
    (s * d) * (s * d) + (c * d) * (c * d) ≡ (c * c + s * s) * (d * d)
  factor-right c s d = let open ≡-Reasoning in begin
    (s * d) * (s * d) + (c * d) * (c * d)
    ≡⟨ cong₂ _+_ (swap-mid s d s d) (swap-mid c d c d) ⟩
    (s * s) * (d * d) + (c * c) * (d * d)
    ≡⟨ +-comm ((s * s) * (d * d)) ((c * c) * (d * d)) ⟩
    (c * c) * (d * d) + (s * s) * (d * d)
    ≡⟨ sym (*-distribʳ-+ (d * d) (c * c) (s * s)) ⟩
    (c * c + s * s) * (d * d) ∎

  -- The two cross products agree: (s*a)*(c*d) = (c*a)*(s*d).
  --
  -- 两个交叉积相等（仅用乘法交换/结合）。
  cross-eq : ∀ c s a d → (s * a) * (c * d) ≡ (c * a) * (s * d)
  cross-eq c s a d = let open ≡-Reasoning in begin
    (s * a) * (c * d)
    ≡⟨ swap-mid s a c d ⟩
    (s * c) * (a * d)
    ≡⟨ cong (_* (a * d)) (*-comm s c) ⟩
    (c * s) * (a * d)
    ≡⟨ sym (swap-mid c a s d) ⟩
    (c * a) * (s * d) ∎

  -- Real core: a real rotation preserves the squared Euclidean norm of
  -- a real 2-vector. Cross terms cancel; c² + s² = 1 closes the
  -- diagonals.
  --
  -- 实核心：实旋转保持实 2-向量的平方欧氏范数；交叉项抵消，
  -- c²+s²=1 收口。
  rot-real : ∀ c s a d → c * c + s * s ≡ 1ℚ →
    (c * a - s * d) * (c * a - s * d) +
    (s * a + c * d) * (s * a + c * d) ≡ a * a + d * d
  rot-real c s a d h = let open ≡-Reasoning in begin
    (x - y) * (x - y) + (u + v) * (u + v)
    ≡⟨ cong₂ _+_ (sq- x y) (sq+ u v) ⟩
    (x² + (y² + (- (x * y) + - (x * y)))) +
    (u² + (v² + (u * v + u * v)))
    ≡⟨ cross-vanish x y u v (cross-eq c s a d) ⟩
    (x² + u²) + (y² + v²)
    ≡⟨ cong₂ _+_ (factor-left c s a) (factor-right c s d) ⟩
    (c * c + s * s) * (a * a) + (c * c + s * s) * (d * d)
    ≡⟨ cong₂ _+_ (cong (_* (a * a)) h) (cong (_* (d * d)) h) ⟩
    1ℚ * (a * a) + 1ℚ * (d * d)
    ≡⟨ cong₂ _+_ (*-identityˡ (a * a)) (*-identityˡ (d * d)) ⟩
    a * a + d * d ∎
    where
    x = c * a ; y = s * d ; u = s * a ; v = c * d
    x² = x * x ; y² = y * y ; u² = u * u ; v² = v * v

------------------------------------------------------------------------
-- Rotation on a pair of complex coordinates
--
-- The rotation acts on a pair of complex coordinates (a two-level
-- state), mixing both real and imaginary parts by the same real matrix.
--
-- 作用在一对复坐标上的旋转
--
-- 旋转作用于一对复坐标（二能级态），实部与虚部按同一实矩阵混合。

rot0 rot1 : ℚ → ℚ → ℂ → ℂ → ℂ
rot0 c s z w = (c * re z - s * re w , c * im z - s * im w)
rot1 c s z w = (s * re z + c * re w , s * im z + c * im w)

rot : ℚ → ℚ → ℂ → ℂ → ℂ × ℂ
rot c s z w = (rot0 c s z w , rot1 c s z w)

-- Complex conservation: the total squared norm of the two coordinates
-- is unchanged. Each component (real/imaginary) is a real rotated
-- 2-vector, so rot-real applies twice and the four squares regroup.
--
-- 复守恒：两坐标总平方范数不变。实部、虚部分别是被旋转的实 2-向量，
-- 故 rot-real 各用一次，四个平方重新归组。
rot-pres : ∀ c s → c * c + s * s ≡ 1ℚ → ∀ z w →
  let (φ₀ , φ₁) = rot c s z w in
  norm² φ₀ + norm² φ₁ ≡ norm² z + norm² w
rot-pres c s h (a , b) (d , e) = let open ≡-Reasoning in begin
  (sq (c * a - s * d) + sq (c * b - s * e)) +
  (sq (s * a + c * d) + sq (s * b + c * e))
  ≡⟨ +interchange (sq (c * a - s * d)) (sq (c * b - s * e))
                   (sq (s * a + c * d)) (sq (s * b + c * e)) ⟩
  (sq (c * a - s * d) + sq (s * a + c * d)) +
  (sq (c * b - s * e) + sq (s * b + c * e))
  ≡⟨ cong₂ _+_ (rot-real c s a d h) (rot-real c s b e h) ⟩
  (a * a + d * d) + (b * b + e * e)
  ≡⟨ +interchange (a * a) (d * d) (b * b) (e * e) ⟩
  (a * a + b * b) + (d * d + e * e) ∎
  where
  sq : ℚ → ℚ
  sq x = x * x

------------------------------------------------------------------------
-- Concrete rational realisation
--
-- c = 3/5, s = 4/5, with c² + s² = 1. ℚ carries this Pythagorean pair,
-- so no square roots are needed.
--
-- 具体有理实现
--
-- c = 3/5、s = 4/5，c²+s²=1；ℚ 承载该勾股对，无需平方根。

i3 i4 : ℤ
i3 = (1ℤ ℤ+ 1ℤ) ℤ+ 1ℤ
i4 = i3 ℤ+ 1ℤ

c₃₄₅ s₃₄₅ : ℚ
c₃₄₅ = i3 / 5
s₃₄₅ = i4 / 5

-- Closed rational arithmetic normalises 9/25 + 16/25 to 1.
--
-- 闭项有理算术把 9/25 + 16/25 规范化为 1。
pythagoras-345 : c₃₄₅ * c₃₄₅ + s₃₄₅ * s₃₄₅ ≡ 1ℚ
pythagoras-345 = refl

-- The 3/5–4/5 rotation conserves total squared norm.
--
-- 3/5–4/5 旋转保持总平方范数。
rotation-345 : ∀ z w →
  let (φ₀ , φ₁) = rot c₃₄₅ s₃₄₅ z w in
  norm² φ₀ + norm² φ₁ ≡ norm² z + norm² w
rotation-345 = rot-pres c₃₄₅ s₃₄₅ pythagoras-345
