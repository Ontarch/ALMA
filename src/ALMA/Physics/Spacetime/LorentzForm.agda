------------------------------------------------------------------------
-- The Lorentz quadratic form on a four-dimensional rational vector space
--
-- A four-vector is a record of four rational components (t, x, y, z).
-- The Lorentz bilinear form g has signature (+---):
--
--   g(v, w) = t·t' − x·x' − y·y' − z·z' ,
--
-- with associated quadratic form η(v) = g(v, v). The form is symmetric
-- and ℚ-bilinear: linearity in the first argument is discharged by the
-- rational ring solver, and linearity in the second argument follows
-- from symmetry. The standard basis has η(e₀) = 1 and η(e₁..₃) = −1,
-- which fixes the causal character (timelike / spacelike / null).
--
-- Nothing here is analytic: every quantity and proof is exact and
-- algebraic over ℚ. This is the single-point algebraic skeleton of a
-- Lorentzian spacetime, sitting at the same level as Newton.Quadratic.
--
-- 四维有理向量空间上的洛伦兹二次型
--
-- 四向量是四个有理分量 (t, x, y, z) 的记录。洛伦兹双线性型 g 取号差
-- (+---)：
--
--   g(v, w) = t·t' − x·x' − y·y' − z·z' ，
--
-- 相应二次型为 η(v) = g(v, v)。该型对称且 ℚ-双线性：第一参数的线性
-- 由有理数环求解器直接给出，第二参数的线性由对称性推出。标准基满足
-- η(e₀) = 1、η(e₁..₃) = −1，由此确定因果性质（类时 / 类空 / 类光）。
--
-- 此处不含任何分析，所有量与证明皆为 ℚ 上精确、代数的内容。这是洛伦
-- 兹时空的单点代数骨架，与 Newton.Quadratic 同层。
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module ALMA.Physics.Spacetime.LorentzForm where

open import Data.Rational using
  (ℚ; 0ℚ; 1ℚ; _+_; _*_; _-_; _<_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Data.List using (_∷_; [])
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; cong; cong₂; module ≡-Reasoning)

------------------------------------------------------------------------
-- Four-vectors and their vector-space operations
--
-- 四向量及其向量空间运算

record FourVec : Set where
  constructor mk4
  field t x y z : ℚ
open FourVec

zero4 : FourVec
zero4 = mk4 0ℚ 0ℚ 0ℚ 0ℚ

add4 : FourVec → FourVec → FourVec
add4 u v = mk4 (t u + t v) (x u + x v) (y u + y v) (z u + z v)

scale4 : ℚ → FourVec → FourVec
scale4 s v = mk4 (s * t v) (s * x v) (s * y v) (s * z v)

------------------------------------------------------------------------
-- The Lorentz bilinear form and quadratic form
--
-- The component-level form g4 is inlined in the linearity lemmas so the
-- ring solver sees only bare ring expressions rather than an applied
-- function it would treat as a constant.
--
-- 洛伦兹双线性型与二次型
--
-- 分量级形式 g4 在线性引理中被内联，使环求解器只看到裸环表达式，而不
-- 会把被应用的函数误当作常量。

g4 : ℚ → ℚ → ℚ → ℚ → ℚ → ℚ → ℚ → ℚ → ℚ
g4 a b c d e f g h = a * e - b * f - c * g - d * h

g : FourVec → FourVec → ℚ
g v w = g4 (t v) (x v) (y v) (z v) (t w) (x w) (y w) (z w)

η : FourVec → ℚ
η v = g v v

------------------------------------------------------------------------
-- Symmetry and bilinearity
--
-- 对称性与双线性

g-sym′ : ∀ a b c d e f k l →
  (a * e - b * f - c * k - d * l)
  ≡ (e * a - f * b - k * c - l * d)
g-sym′ a b c d e f k l =
  solve (a ∷ b ∷ c ∷ d ∷ e ∷ f ∷ k ∷ l ∷ [])

g-sym : ∀ v w → g v w ≡ g w v
g-sym v w =
  g-sym′ (t v) (x v) (y v) (z v) (t w) (x w) (y w) (z w)

-- Linearity in the first argument.
-- 第一参数的线性。
g-addˡ′ : ∀ i j k l a b c d e f g h →
  ((i + a) * e - (j + b) * f - (k + c) * g - (l + d) * h)
  ≡ (i * e - j * f - k * g - l * h)
    + (a * e - b * f - c * g - d * h)
g-addˡ′ i j k l a b c d e f g h =
  solve (i ∷ j ∷ k ∷ l ∷ a ∷ b ∷ c ∷ d ∷ e ∷ f ∷ g ∷ h ∷ [])

g-addˡ : ∀ u v w → g (add4 u v) w ≡ g u w + g v w
g-addˡ u v w =
  g-addˡ′ (t u) (x u) (y u) (z u) (t v) (x v) (y v) (z v)
           (t w) (x w) (y w) (z w)

g-scaleˡ′ : ∀ s a b c d e f g h →
  ((s * a) * e - (s * b) * f - (s * c) * g - (s * d) * h)
  ≡ s * (a * e - b * f - c * g - d * h)
g-scaleˡ′ s a b c d e f g h =
  solve (s ∷ a ∷ b ∷ c ∷ d ∷ e ∷ f ∷ g ∷ h ∷ [])

g-scaleˡ : ∀ s v w → g (scale4 s v) w ≡ s * g v w
g-scaleˡ s v w =
  g-scaleˡ′ s (t v) (x v) (y v) (z v) (t w) (x w) (y w) (z w)

-- Linearity in the second argument, obtained from symmetry.
-- 第二参数的线性，由对称性推出。
g-addʳ : ∀ v u w → g v (add4 u w) ≡ g v u + g v w
g-addʳ v u w =
  let open ≡-Reasoning in begin
    g v (add4 u w)
    ≡⟨ g-sym v (add4 u w) ⟩
    g (add4 u w) v
    ≡⟨ g-addˡ u w v ⟩
    g u v + g w v
    ≡⟨ cong₂ _+_ (g-sym u v) (g-sym w v) ⟩
    g v u + g v w ∎

g-scaleʳ : ∀ s v w → g v (scale4 s w) ≡ s * g v w
g-scaleʳ s v w =
  let open ≡-Reasoning in begin
    g v (scale4 s w)
    ≡⟨ g-sym v (scale4 s w) ⟩
    g (scale4 s w) v
    ≡⟨ g-scaleˡ s w v ⟩
    s * g w v
    ≡⟨ cong (s *_) (g-sym w v) ⟩
    s * g v w ∎

------------------------------------------------------------------------
-- The standard basis
--
-- 标准基

e₀ e₁ e₂ e₃ : FourVec
e₀ = mk4 1ℚ 0ℚ 0ℚ 0ℚ
e₁ = mk4 0ℚ 1ℚ 0ℚ 0ℚ
e₂ = mk4 0ℚ 0ℚ 1ℚ 0ℚ
e₃ = mk4 0ℚ 0ℚ 0ℚ 1ℚ

η-e₀ : η e₀ ≡ 1ℚ
η-e₀ = refl

η-e₁ : η e₁ ≡ 0ℚ - 1ℚ
η-e₁ = refl

η-e₂ : η e₂ ≡ 0ℚ - 1ℚ
η-e₂ = refl

η-e₃ : η e₃ ≡ 0ℚ - 1ℚ
η-e₃ = refl

g-e₀₀ : g e₀ e₀ ≡ 1ℚ
g-e₀₀ = refl

g-e₁₁ : g e₁ e₁ ≡ 0ℚ - 1ℚ
g-e₁₁ = refl

g-e₀₁ : g e₀ e₁ ≡ 0ℚ
g-e₀₁ = refl

------------------------------------------------------------------------
-- Causal character
--
-- Under (+---) a vector is timelike when η(v) > 0, spacelike when
-- η(v) < 0 and null (lightlike) when η(v) = 0.
--
-- 因果性质
--
-- 在 (+---) 下，η(v) > 0 为类时，η(v) < 0 为类空，η(v) = 0 为类光。

Timelike : FourVec → Set
Timelike v = 0ℚ < η v

Spacelike : FourVec → Set
Spacelike v = η v < 0ℚ

Null : FourVec → Set
Null v = η v ≡ 0ℚ

null-zero : Null zero4
null-zero = refl

------------------------------------------------------------------------
-- Polarisation identity
--
-- η(v + w) − η(v) − η(w) = g(v, w) + g(w, v).
--
-- The factor 1/2 is omitted so the whole identity stays in the ring
-- language; over a field of characteristic zero the two sides equal
-- 2·g(v, w) by symmetry.
--
-- 极化恒等式
--
-- η(v + w) − η(v) − η(w) = g(v, w) + g(w, v)。
--
-- 此处省略因子 1/2，使整条恒等式保持在环语言内；在特征零的域上，由
-- 对称性两边等于 2·g(v, w)。

polarisation′ : ∀ a b c d e f g h →
  ((a + e) * (a + e) - (b + f) * (b + f)
    - (c + g) * (c + g) - (d + h) * (d + h))
  - (a * a - b * b - c * c - d * d)
  - (e * e - f * f - g * g - h * h)
  ≡ (a * e - b * f - c * g - d * h)
    + (e * a - f * b - g * c - h * d)
polarisation′ a b c d e f g h =
  solve (a ∷ b ∷ c ∷ d ∷ e ∷ f ∷ g ∷ h ∷ [])
