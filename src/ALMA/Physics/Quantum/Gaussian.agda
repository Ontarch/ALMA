------------------------------------------------------------------------
-- Quantitative scalar fiber: Gaussian rationals as exact amplitudes
--
-- The carried setoid equipment (FiberAdjˢ) moves equivalences between
-- fibers; it cannot carry a number. Quantum amplitudes and Born
-- probabilities are quantitative, so the fiber must be extended with a
-- scalar carrying conjugation and a squared norm. This module fixes an
-- exact, constructive scalar -- Gaussian rationals ℚ[i] = ℚ × ℚ with
-- i² = -1 -- on which the structural identities hold by ring algebra:
-- conj is complex conjugation; norm² z = (re z)² + (im z)² is the real
-- squared modulus (the Born weight of z); norm²-mul : |uv|² = |u|²|v|²
-- is multiplicativity of the modulus, the identity behind probability
-- conservation under unitaries; norm²-conj says conjugation preserves
-- the modulus; and Unit, unit-norm-mul say unit-modulus phases
-- (norm² = 1) are closed under multiplication, the phase group used by
-- diagonal unitaries.
--
-- 定量标量纤维：高斯有理数作为精确振幅
--
-- 携带式 setoid 装备（FiberAdjˢ）只在纤维间搬运等价，携带不了数。量子
-- 振幅与 Born 概率是定量的，故纤维必须扩展为携带共轭与平方范数的标量。
-- 本模块取精确、构造性的标量——高斯有理数 ℚ[i] = ℚ × ℚ，i² = -1——
-- 结构恒等式由环代数成立：conj 为复共轭；norm² z = (re z)² + (im z)²
-- 为实平方模（z 的 Born 权重）；norm²-mul：|uv|² = |u|²|v|² 是模的
-- 乘法性，幺正下概率守恒背后的恒等式；norm²-conj 说共轭保模；Unit、
-- unit-norm-mul 说单位模相位（norm² = 1）对乘法封闭，即对角幺正所用的
-- 相位群。
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module ALMA.Physics.Quantum.Gaussian where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Product.Base using (_×_; _,_)
open import Data.Rational using (ℚ; 0ℚ; 1ℚ; _+_; _*_; _-_; -_)
open import Data.Rational.Properties using
  (+-assoc; +-comm; +-identityʳ; +-inverseˡ; *-distribˡ-+; *-distribʳ-+; neg-distrib-+)
open import Relation.Binary.PropositionalEquality using
  (trans; sym; cong; cong₂; module ≡-Reasoning)
open ≡-Reasoning

open import ALMA.Physics.RationalKit using (neg-neg-mul; sq+; sq-; sq-comm; cross-eq)

------------------------------------------------------------------------
-- Gaussian rationals in rectangular form
--
-- Real part and imaginary part.
--
-- 矩形形式的高斯有理数
--
-- 实部与虚部。

ℂ : Set
ℂ = ℚ × ℚ

re im : ℂ → ℚ
re (a , _) = a
im (_ , b) = b

infixl 6 _+ᶜ_
infixl 7 _*ᶜ_

_+ᶜ_ : ℂ → ℂ → ℂ
(a , b) +ᶜ (c , d) = (a + c , b + d)

-- (a + bi)(c + di) = (ac - bd) + (ad + bc)i
--
-- (a + bi)(c + di) = (ac - bd) + (ad + bc)i
_*ᶜ_ : ℂ → ℂ → ℂ
(a , b) *ᶜ (c , d) = (a * c - b * d , a * d + b * c)

0ᶜ 1ᶜ : ℂ
0ᶜ = (0ℚ , 0ℚ)
1ᶜ = (1ℚ , 0ℚ)

conj : ℂ → ℂ
conj (a , b) = (a , - b)

-- Squared modulus; real on ℚ (a² + b²).
--
-- 平方模；在 ℚ 上为实（a² + b²）。
norm² : ℂ → ℚ
norm² z = re z * re z + im z * im z

norm²-0ᶜ : norm² 0ᶜ ≡ 0ℚ
norm²-0ᶜ = refl

norm²-1ᶜ : norm² 1ᶜ ≡ 1ℚ
norm²-1ᶜ = refl

------------------------------------------------------------------------
-- Rational ring algebra kit
--
-- Short ring-algebra chains used by the structural identities below.
--
-- 有理数环代数工具
--
-- 下面结构恒等式所用的简短环等式链。

private
  -- A paired positive and negative copy of t cancels additively.
  --
  -- 一正一负两份 t 在加法下相消。
  kill : ∀ U V t →
         (U - (t + t)) + (V + (t + t)) ≡ U + V
  kill U V t = begin
    (U - (t + t)) + (V + (t + t))
    ≡⟨ sym (+-assoc (U - (t + t)) V (t + t)) ⟩
    ((U - (t + t)) + V) + (t + t)
    ≡⟨ cong (λ z → z + (t + t)) (+-comm (U - (t + t)) V) ⟩
    (V + (U - (t + t))) + (t + t)
    ≡⟨ +-assoc V (U - (t + t)) (t + t) ⟩
    V + ((U - (t + t)) + (t + t))
    ≡⟨ cong (V +_) (+-assoc U (- (t + t)) (t + t)) ⟩
    V + (U + ((- (t + t)) + (t + t)))
    ≡⟨ cong (λ z → V + (U + z)) (+-inverseˡ (t + t)) ⟩
    V + (U + 0ℚ)
    ≡⟨ cong (V +_) (+-identityʳ U) ⟩
    V + U
    ≡⟨ +-comm V U ⟩
    U + V ∎

  -- Reorder the four collected monomials to match the distributive
  -- expansion (wy + wz) + (xy + xz).
  --
  -- 将四个单项式重排以匹配分配展开 (wy + wz) + (xy + xz)。
  gather : ∀ w x y z →
           (w * y + x * z) + (w * z + x * y)
         ≡ (w * y + w * z) + (x * y + x * z)
  gather w x y z = begin
    (w * y + x * z) + (w * z + x * y)
    ≡⟨ +-assoc (w * y) (x * z) (w * z + x * y) ⟩
    w * y + (x * z + (w * z + x * y))
    ≡⟨ cong (w * y +_) move ⟩
    w * y + (w * z + (x * z + x * y))
    ≡⟨ cong (λ r → w * y + (w * z + r)) (+-comm (x * z) (x * y)) ⟩
    w * y + (w * z + (x * y + x * z))
    ≡⟨ sym (+-assoc (w * y) (w * z) (x * y + x * z)) ⟩
    (w * y + w * z) + (x * y + x * z) ∎
    where
    move : x * z + (w * z + x * y) ≡ w * z + (x * z + x * y)
    move = begin
      x * z + (w * z + x * y)
      ≡⟨ sym (+-assoc (x * z) (w * z) (x * y)) ⟩
      (x * z + w * z) + x * y
      ≡⟨ cong (λ r → r + x * y) (+-comm (x * z) (w * z)) ⟩
      (w * z + x * z) + x * y
      ≡⟨ +-assoc (w * z) (x * z) (x * y) ⟩
      w * z + (x * z + x * y) ∎

------------------------------------------------------------------------
-- Structural identities of the scalar
--
-- 标量的结构恒等式

-- Conjugation preserves the squared modulus.
--
-- 共轭保持平方模。
norm²-conj : ∀ (u : ℂ) → norm² (conj u) ≡ norm² u
norm²-conj (a , b) = cong (a * a +_) (neg-neg-mul b b)

-- Multiplicativity of the squared modulus: |uv|² = |u|²|v|².
--
-- 平方模的乘法性：|uv|² = |u|²|v|²。
norm²-mul : ∀ (u v : ℂ) → norm² (u *ᶜ v) ≡ norm² u * norm² v
norm²-mul (a , b) (c , d) = begin
  (ac - bd) * (ac - bd) + (ad + bc) * (ad + bc)
  ≡⟨ cong₂ _+_ real-part imag-part ⟩
  (U - (P + P)) + (V + (Q + Q))
  ≡⟨ cong ((U - (P + P)) +_) (cong (V +_) (cong₂ _+_ (sym (cross-eq a b c d))
                                                         (sym (cross-eq a b c d)))) ⟩
  (U - (P + P)) + (V + (P + P))
  ≡⟨ kill U V P ⟩
  U + V
  ≡⟨ cong₂ _+_ U-eq V-eq ⟩
  (a²c² + b²d²) + (a²d² + b²c²)
  ≡⟨ gather (a * a) (b * b) (c * c) (d * d) ⟩
  (a²c² + a²d²) + (b²c² + b²d²)
  ≡⟨ sym expand ⟩
  (a * a + b * b) * (c * c + d * d) ∎
  where
  ac = a * c ; bd = b * d ; ad = a * d ; bc = b * c
  P  = ac * bd ; Q = ad * bc
  U  = ac * ac + bd * bd
  V  = ad * ad + bc * bc
  a²c² = (a * a) * (c * c) ; b²d² = (b * b) * (d * d)
  a²d² = (a * a) * (d * d) ; b²c² = (b * b) * (c * c)

  -- (x - y)² = x² + y² - 2xy, regrouped so that the pair of negative
  -- cross terms is a single `- (P + P)`, matching kill's shape.
  --
  -- (x - y)² = x² + y² - 2xy，重排使成对的负交叉项合并为一个
  -- `- (P + P)`，以匹配 kill 的形状。
  real-part : (ac - bd) * (ac - bd) ≡ U - (P + P)
  real-part = begin
    (ac - bd) * (ac - bd)
      ≡⟨ sq- ac bd ⟩
    ac * ac + (bd * bd + (- (ac * bd) + - (ac * bd)))
      ≡⟨ cong (ac * ac +_)
           (cong (bd * bd +_)
             (sym (neg-distrib-+ (ac * bd) (ac * bd)))) ⟩
    ac * ac + (bd * bd + - (P + P))
      ≡⟨ sym (+-assoc (ac * ac) (bd * bd) (- (P + P))) ⟩
    (ac * ac + bd * bd) + - (P + P) ∎

  imag-part : (ad + bc) * (ad + bc) ≡ V + (Q + Q)
  imag-part = trans (sq+ ad bc)
                     (sym (+-assoc (ad * ad) (bc * bc) (Q + Q)))

  U-eq : U ≡ a²c² + b²d²
  U-eq = cong₂ _+_ (sq-comm a c) (sq-comm b d)

  V-eq : V ≡ a²d² + b²c²
  V-eq = cong₂ _+_ (sq-comm a d) (sq-comm b c)

  expand : (a * a + b * b) * (c * c + d * d)
         ≡ (a²c² + a²d²) + (b²c² + b²d²)
  expand = begin
    (a * a + b * b) * (c * c + d * d)
    ≡⟨ *-distribʳ-+ (c * c + d * d) (a * a) (b * b) ⟩
    a * a * (c * c + d * d) + b * b * (c * c + d * d)
    ≡⟨ cong₂ _+_ (*-distribˡ-+ (a * a) (c * c) (d * d))
                  (*-distribˡ-+ (b * b) (c * c) (d * d)) ⟩
    (a²c² + a²d²) + (b²c² + b²d²) ∎

-- Unit-modulus complex numbers are the phases.
--
-- 单位模复数即相位。
Unit : ℂ → Set
Unit z = norm² z ≡ 1ℚ

-- Phases are closed under multiplication: |uv| = |u||v| = 1.
--
-- 相位对乘法封闭：|uv| = |u||v| = 1。
unit-norm-mul : ∀ u v → Unit u → Unit v → Unit (u *ᶜ v)
unit-norm-mul u v hu hv
  rewrite norm²-mul u v | hu | hv = refl
