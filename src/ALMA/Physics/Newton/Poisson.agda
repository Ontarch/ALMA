------------------------------------------------------------------------
-- The affine canonical Poisson algebra (the Heisenberg algebra)
--
-- Observables affine in canonical coordinates, f = c + a q + b p over
-- ℚ. The canonical bracket
--
--   {f, g} = ∂q f · ∂p g − ∂p f · ∂q g = a b' − b a'
--
-- is constant in q, p, so every bracket is central and the algebra is
-- the two-step nilpotent Heisenberg algebra. We verify the Poisson
-- axioms (ℚ-bilinearity, antisymmetry, Jacobi) and the canonical
-- relations {q,p}=1. The Hamiltonian vector field X_H f = {f,H} gives
-- Newton's equations at constant force: q̇ = b_H, ṗ = −a_H, and energy
-- is conserved, {H,H}=0. Everything is exact over ℚ; no analysis
-- enters.
--
-- 仿射典范 Poisson 代数（Heisenberg 代数）
--
-- 典范坐标上的仿射观测量 f = c + a q + b p（ℚ 系数），典范括号
--
--   {f, g} = ∂q f · ∂p g − ∂p f · ∂q g = a b' − b a'
--
-- 与 q、p 无关，故每个括号都在中心，代数为二步幂零的 Heisenberg 代数。
-- 此处验证 Poisson 公理（ℚ 双线性、反对称、Jacobi）与正则关系
-- {q,p}=1。哈密顿向量场 X_H f = {f,H} 给出常力情形的牛顿方程
-- q̇=b_H、ṗ=−a_H，且能量守恒 {H,H}=0。全部在 ℚ 上精确，不含任何分析。
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module ALMA.Physics.Newton.Poisson where

open import Data.Rational using (ℚ; 0ℚ; 1ℚ; _+_; _*_; -_)
open import Data.Rational.Properties using
  (+-assoc; +-identityˡ; +-identityʳ; +-inverseʳ; +-comm; *-assoc
  ; *-comm; *-zeroˡ; *-zeroʳ; *-identityˡ; *-distribˡ-+; *-distribʳ-+
  ; neg-distrib-+; neg-distribʳ-*)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; sym; cong; cong₂; module ≡-Reasoning)

open import ALMA.Physics.RationalKit using (neg-involutive)

------------------------------------------------------------------------
-- Affine observables and the canonical bracket
--
-- 仿射观测量与典范括号

-- An observable c + a q + b p.
--
-- 观测量 c + a q + b p。
record Obs : Set where
  constructor obs
  field
    c : ℚ   -- constant / 常数项
    a : ℚ   -- coefficient of q / q 的系数
    b : ℚ   -- coefficient of p / p 的系数
open Obs

-- Pointwise addition and scalar multiplication.
--
-- 逐点加法与数乘。
add : Obs → Obs → Obs
add (obs c a b) (obs c' a' b') = obs (c + c') (a + a') (b + b')

scale : ℚ → Obs → Obs
scale r (obs c a b) = obs (r * c) (r * a) (r * b)

neg : Obs → Obs
neg (obs c a b) = obs (- c) (- a) (- b)

zero : Obs
zero = obs 0ℚ 0ℚ 0ℚ

-- The unit constant, and the canonical coordinates.
--
-- 单位常数与典范坐标。
one : Obs
one = obs 1ℚ 0ℚ 0ℚ

qO : Obs
qO = obs 0ℚ 1ℚ 0ℚ

pO : Obs
pO = obs 0ℚ 0ℚ 1ℚ

-- Canonical Poisson bracket; the constant term of each argument drops.
--
-- 典范 Poisson 括号；两自变量的常数项不出现。
bracket : Obs → Obs → Obs
bracket (obs _ a b) (obs _ a' b') = obs (a * b' + - (b * a')) 0ℚ 0ℚ

infix 6 bracket

------------------------------------------------------------------------
-- Antisymmetry and the canonical relations
--
-- 反对称性与正则关系

-- {f, f} = 0 since a b − b a = 0.
--
-- 因 a b − b a = 0，有 {f, f} = 0。
bracket-self : ∀ f → bracket f f ≡ zero
bracket-self (obs _ a b) =
  cong (λ x → obs x 0ℚ 0ℚ) lemma
  where
  lemma : a * b + - (b * a) ≡ 0ℚ
  lemma = let open ≡-Reasoning in begin
    a * b + - (b * a)
    ≡⟨ cong (λ x → a * b + - x) (*-comm b a) ⟩
    a * b + - (a * b)
    ≡⟨ +-inverseʳ (a * b) ⟩
    0ℚ ∎

-- Antisymmetry: {g, f} = −{f, g}.
--
-- 反对称：{g, f} = −{f, g}。
bracket-skew : ∀ f g → bracket g f ≡ neg (bracket f g)
bracket-skew (obs _ a b) (obs _ a' b') =
  cong (λ x → obs x 0ℚ 0ℚ) lemma
  where
  lemma : a' * b + - (b' * a) ≡ - (a * b' + - (b * a'))
  lemma = let open ≡-Reasoning in begin
    a' * b + - (b' * a)
    ≡⟨ cong₂ (λ x y → x + - y) (*-comm a' b) (*-comm b' a) ⟩
    b * a' + - (a * b')
    ≡⟨ +-comm (b * a') (- (a * b')) ⟩
    - (a * b') + b * a'
    ≡⟨ cong (λ x → - (a * b') + x) (sym (neg-involutive (b * a'))) ⟩
    - (a * b') + - (- (b * a'))
    ≡⟨ sym (neg-distrib-+ (a * b') (- (b * a'))) ⟩
    - (a * b' + - (b * a')) ∎

-- Canonical (Heisenberg) relations.
--
-- 正则（Heisenberg）关系。
bracket-qp : bracket qO pO ≡ one
bracket-qp = refl

bracket-qq : bracket qO qO ≡ zero
bracket-qq = bracket-self qO

bracket-pp : bracket pO pO ≡ zero
bracket-pp = bracket-self pO

------------------------------------------------------------------------
-- Bilinearity
--
-- 双线性

-- Bilinearity in the first argument
--
-- Write ω(u,v) for the constant value of {u,v}, and distribute over
-- addition and scaling.
--
-- 第一自变量的双线性
--
-- 记 ω(u,v) 为 {u,v} 的常数值，对加法与数乘分配。
bracket-addˡ : ∀ f g h →
               bracket (add f g) h ≡ add (bracket f h) (bracket g h)
bracket-addˡ (obs _ af bf) (obs _ ag bg) (obs _ ah bh) =
  cong (λ x → obs x 0ℚ 0ℚ) lemma
  where
  lemma : (af + ag) * bh + - ((bf + bg) * ah)
        ≡ (af * bh + - (bf * ah)) + (ag * bh + - (bg * ah))
  lemma = let open ≡-Reasoning in begin
    (af + ag) * bh + - ((bf + bg) * ah)
    ≡⟨ cong₂ (λ x y → x + - y) (*-distribʳ-+ bh af ag)
                             (*-distribʳ-+ ah bf bg) ⟩
    (af * bh + ag * bh) + - (bf * ah + bg * ah)
    ≡⟨ cong ((af * bh + ag * bh) +_)
            (neg-distrib-+ (bf * ah) (bg * ah)) ⟩
    (af * bh + ag * bh) + (- (bf * ah) + - (bg * ah))
    ≡⟨ swap4 (af * bh) (ag * bh) (- (bf * ah)) (- (bg * ah)) ⟩
    (af * bh + - (bf * ah)) + (ag * bh + - (bg * ah)) ∎
    where
    swap4 : ∀ w x y z → (w + x) + (y + z) ≡ (w + y) + (x + z)
    swap4 w x y z = let open ≡-Reasoning in begin
      (w + x) + (y + z)
      ≡⟨ +-assoc w x (y + z) ⟩
      w + (x + (y + z))
      ≡⟨ cong (w +_) (sym (+-assoc x y z)) ⟩
      w + ((x + y) + z)
      ≡⟨ cong (λ t → w + (t + z)) (+-comm x y) ⟩
      w + ((y + x) + z)
      ≡⟨ cong (w +_) (+-assoc y x z) ⟩
      w + (y + (x + z))
      ≡⟨ sym (+-assoc w y (x + z)) ⟩
      (w + y) + (x + z) ∎

-- Bilinearity in the second argument follows by antisymmetry.
--
-- 第二自变量的双线性由反对称推出。
bracket-addʳ : ∀ f g h →
               bracket f (add g h) ≡ add (bracket f g) (bracket f h)
bracket-addʳ f g h = let open ≡-Reasoning in begin
  bracket f (add g h)
  ≡⟨ bracket-skew (add g h) f ⟩
  neg (bracket (add g h) f)
  ≡⟨ cong neg (bracket-addˡ g h f) ⟩
  neg (add (bracket g f) (bracket h f))
  ≡⟨ neg-add (bracket g f) (bracket h f) ⟩
  add (neg (bracket g f)) (neg (bracket h f))
  ≡⟨ cong₂ add (sym (bracket-skew g f)) (sym (bracket-skew h f)) ⟩
  add (bracket f g) (bracket f h) ∎
  where
  neg-add : ∀ u v → neg (add u v) ≡ add (neg u) (neg v)
  neg-add (obs c a b) (obs c' a' b') = let open ≡-Reasoning in begin
    obs (- (c + c')) (- (a + a')) (- (b + b'))
    ≡⟨ cong (λ x → obs x (- (a + a')) (- (b + b')))
           (neg-distrib-+ c c') ⟩
    obs (- c + - c') (- (a + a')) (- (b + b'))
    ≡⟨ cong₂ (obs (- c + - c'))
            (neg-distrib-+ a a') (neg-distrib-+ b b') ⟩
    obs (- c + - c') (- a + - a') (- b + - b') ∎

-- Scalar linearity in each argument.
--
-- 每个自变量上的数乘线性。
bracket-scaleˡ : ∀ r f g →
                 bracket (scale r f) g ≡ scale r (bracket f g)
bracket-scaleˡ r f@(obs _ a b) g@(obs _ a' b') =
  let open ≡-Reasoning in begin
    bracket (scale r f) g
  ≡⟨ cong (λ x → obs x 0ℚ 0ℚ) lemma ⟩
    obs (r * (a * b' + - (b * a'))) 0ℚ 0ℚ
  ≡⟨ cong₂ (obs (r * (a * b' + - (b * a'))))
          (sym (*-zeroʳ r)) (sym (*-zeroʳ r)) ⟩
    obs (r * (a * b' + - (b * a'))) (r * 0ℚ) (r * 0ℚ) ∎
  where
  lemma : (r * a) * b' + - ((r * b) * a')
        ≡ r * (a * b' + - (b * a'))
  lemma = let open ≡-Reasoning in begin
    (r * a) * b' + - ((r * b) * a')
    ≡⟨ cong₂ (λ x y → x + - y) (*-assoc r a b') (*-assoc r b a') ⟩
    r * (a * b') + - (r * (b * a'))
    ≡⟨ cong (r * (a * b') +_) (neg-distribʳ-* r (b * a')) ⟩
    r * (a * b') + r * (- (b * a'))
    ≡⟨ sym (*-distribˡ-+ r (a * b') (- (b * a'))) ⟩
    r * (a * b' + - (b * a')) ∎

bracket-scaleʳ : ∀ r f g →
                 bracket f (scale r g) ≡ scale r (bracket f g)
bracket-scaleʳ r f g = let open ≡-Reasoning in begin
  bracket f (scale r g)
  ≡⟨ bracket-skew (scale r g) f ⟩
  neg (bracket (scale r g) f)
  ≡⟨ cong neg (bracket-scaleˡ r g f) ⟩
  neg (scale r (bracket g f))
  ≡⟨ neg-scale r (bracket g f) ⟩
  scale r (neg (bracket g f))
  ≡⟨ cong (scale r) (sym (bracket-skew g f)) ⟩
  scale r (bracket f g) ∎
  where
  neg-scale : ∀ r u → neg (scale r u) ≡ scale r (neg u)
  neg-scale r (obs c a b) = let open ≡-Reasoning in begin
    obs (- (r * c)) (- (r * a)) (- (r * b))
    ≡⟨ cong (λ x → obs x (- (r * a)) (- (r * b)))
           (neg-distribʳ-* r c) ⟩
    obs (r * - c) (- (r * a)) (- (r * b))
    ≡⟨ cong₂ (obs (r * - c))
            (neg-distribʳ-* r a) (neg-distribʳ-* r b) ⟩
    obs (r * - c) (r * - a) (r * - b) ∎

------------------------------------------------------------------------
-- Centrality and the Jacobi identity
--
-- 中心性与 Jacobi 恒等式

-- Every bracket has zero q- and p-coefficients, hence is central
--
-- A central observable brackets to zero with anything.
--
-- 每个括号的 q、p 系数皆零，故在中心
--
-- 中心观测量与任何观测量括号为零。
central-kill : ∀ k h → bracket (obs k 0ℚ 0ℚ) h ≡ zero
central-kill k (obs _ a b) = cong (λ x → obs x 0ℚ 0ℚ) lemma
  where
  lemma : 0ℚ * b + - (0ℚ * a) ≡ 0ℚ
  lemma = let open ≡-Reasoning in begin
    0ℚ * b + - (0ℚ * a)
    ≡⟨ cong₂ (λ x y → x + - y) (*-zeroˡ b) (*-zeroˡ a) ⟩
    0ℚ + - 0ℚ
    ≡⟨ +-inverseʳ 0ℚ ⟩
    0ℚ ∎

-- A nested bracket is zero on the left
--
-- { {f,g}, h } = 0, since the inner bracket is definitionally central
-- (obs k 0 0).
--
-- 左嵌套括号为零
--
-- { {f,g}, h } = 0，因内括号按定义即在中心（obs k 0 0）。
nested-zero : ∀ f g h → bracket (bracket f g) h ≡ zero
nested-zero (obs _ af bf) (obs _ ag bg) h =
  central-kill (af * bg + - (bf * ag)) h

-- zero is the additive unit on the left.
--
-- zero 是左加法单位。
add-zeroˡ : ∀ u → add zero u ≡ u
add-zeroˡ (obs c a b) = let open ≡-Reasoning in begin
  obs (0ℚ + c) (0ℚ + a) (0ℚ + b)
  ≡⟨ cong (λ x → obs x (0ℚ + a) (0ℚ + b)) (+-identityˡ c) ⟩
  obs c (0ℚ + a) (0ℚ + b)
  ≡⟨ cong₂ (obs c) (+-identityˡ a) (+-identityˡ b) ⟩
  obs c a b ∎

-- Jacobi
--
-- Every nested bracket vanishes, so the cyclic sum is zero.
--
-- Jacobi
--
-- 每个嵌套括号皆零，故循环和为零。
jacobi : ∀ f g h →
         add (add (bracket (bracket f g) h)
                  (bracket (bracket g h) f))
             (bracket (bracket h f) g) ≡ zero
jacobi f g h = let open ≡-Reasoning in begin
  add (add (bracket (bracket f g) h)
           (bracket (bracket g h) f))
      (bracket (bracket h f) g)
  ≡⟨ cong₂ (λ x y → add (add x (bracket (bracket g h) f)) y)
           (nested-zero f g h) (nested-zero h f g) ⟩
  add (add zero (bracket (bracket g h) f)) zero
  ≡⟨ cong (λ x → add (add zero x) zero) (nested-zero g h f) ⟩
  add (add zero zero) zero
  ≡⟨ cong (λ x → add x zero) (add-zeroˡ zero) ⟩
  add zero zero
  ≡⟨ add-zeroˡ zero ⟩
  zero ∎

------------------------------------------------------------------------
-- Hamiltonian dynamics: Newton's equations and energy conservation
--
-- 哈密顿动力学：牛顿方程与能量守恒

-- Hamiltonian vector field X_H f = {f, H}.
--
-- 哈密顿向量场 X_H f = {f, H}。
X : Obs → Obs → Obs
X H f = bracket f H

-- q̇ = {q,H} = b_H: the constant coefficient equals H's p-coefficient.
--
-- q̇ = {q,H} = b_H：常数值等于 H 的 p 系数。
eom-q : ∀ H → X H qO ≡ obs (b H) 0ℚ 0ℚ
eom-q (obs _ a b) = let open ≡-Reasoning in begin
  obs (1ℚ * b + - (0ℚ * a)) 0ℚ 0ℚ
  ≡⟨ cong (λ x → obs x 0ℚ 0ℚ) lemma ⟩
  obs b 0ℚ 0ℚ ∎
  where
  lemma : 1ℚ * b + - (0ℚ * a) ≡ b
  lemma = let open ≡-Reasoning in begin
    1ℚ * b + - (0ℚ * a)
    ≡⟨ cong (λ x → 1ℚ * b + - x) (*-zeroˡ a) ⟩
    1ℚ * b + - 0ℚ
    ≡⟨ cong (λ x → x + - 0ℚ) (*-identityˡ b) ⟩
    b + - 0ℚ
    ≡⟨ +-identityʳ b ⟩
    b ∎

-- ṗ = {p,H} = −a_H: the constant coefficient is minus H's q-coefficient.
--
-- ṗ = {p,H} = −a_H：常数值为 H 的 q 系数取负。
eom-p : ∀ H → X H pO ≡ obs (- a H) 0ℚ 0ℚ
eom-p (obs _ a b) = let open ≡-Reasoning in begin
  obs (0ℚ * b + - (1ℚ * a)) 0ℚ 0ℚ
  ≡⟨ cong (λ x → obs x 0ℚ 0ℚ) lemma ⟩
  obs (- a) 0ℚ 0ℚ ∎
  where
  lemma : 0ℚ * b + - (1ℚ * a) ≡ - a
  lemma = let open ≡-Reasoning in begin
    0ℚ * b + - (1ℚ * a)
    ≡⟨ cong (λ x → 0ℚ * b + - x) (*-identityˡ a) ⟩
    0ℚ * b + - a
    ≡⟨ cong (λ x → x + - a) (*-zeroˡ b) ⟩
    0ℚ + - a
    ≡⟨ +-identityˡ (- a) ⟩
    - a ∎

-- Energy is conserved along its own flow: {H,H} = 0.
--
-- 能量沿自身流守恒：{H,H} = 0。
energy-conserved : ∀ H → X H H ≡ zero
energy-conserved H = bracket-self H

------------------------------------------------------------------------
-- Constant-force instance
--
-- H = −F q + v₀ p gives q̇ = v₀, ṗ = F.
--
-- 常力实例
--
-- H = −F q + v₀ p 给出 q̇ = v₀、ṗ = F。

-- Force F = 2, initial velocity parameter v₀ = 1; H = −2 q + p.
--
-- 力 F = 2，速度参数 v₀ = 1；H = −2 q + p。
H-const-force : Obs
H-const-force = obs 0ℚ (- (1ℚ + 1ℚ)) 1ℚ

-- q̇ = 1.
--
-- q̇ = 1。
const-force-qdot : X H-const-force qO ≡ one
const-force-qdot = refl

-- ṗ = 2 (the force).
--
-- ṗ = 2（即力）。
const-force-pdot : X H-const-force pO ≡ obs (1ℚ + 1ℚ) 0ℚ 0ℚ
const-force-pdot = refl

-- The constant-force Hamiltonian conserves its own energy.
--
-- 常力哈密顿量的能量守恒。
const-force-energy : X H-const-force H-const-force ≡ zero
const-force-energy = energy-conserved H-const-force
