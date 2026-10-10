------------------------------------------------------------------------
-- Algebraic Newtonian mechanics: quadratic Poisson algebra over ℚ.
--
-- Observables are polynomials of degree at most two in the canonical
-- coordinates q, p:
--
--   c + a q + b p + d q² + e qp + f p².
--
-- They carry the canonical Poisson bracket {q,p} = 1.  The bracket of
-- two quadratics is again at most quadratic, so the space closes.  This
-- slice fixes the bracket on the basis monomials; bilinearity,
-- antisymmetry, the Jacobi identity and the harmonic oscillator follow
-- in later slices.
--
-- 代数版牛顿力学：ℚ 上的二次 Poisson 代数。
--
-- 观测量是典范坐标 q、p 上次数不超过二的多项式：
--
--   c + a q + b p + d q² + e qp + f p²。
--
-- 其上承载典范 Poisson 括号 {q,p} = 1。两个二次观测量的括号仍不超过
-- 二次，故该空间对括号闭合。本切片确立括号在基单项式上的取值；双线性、
-- 反对称、Jacobi 与谐振子在后续切片给出。
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module ALMA.Physics.Newton.Quadratic where

open import Data.Rational using (ℚ; 0ℚ; 1ℚ; _+_; _*_; -_)
open import Data.Rational.Properties using
  ( +-identityˡ; +-identityʳ
  ; *-identityˡ; *-identityʳ
  ; *-zeroˡ; *-zeroʳ )
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; sym; trans; cong; cong₂; module ≡-Reasoning)

------------------------------------------------------------------------
-- Quadratic observables
-- 二次观测量
------------------------------------------------------------------------

record Obs : Set where
  constructor obs
  field
    c : ℚ   -- constant / 常数
    a : ℚ   -- coefficient of q / q 的系数
    b : ℚ   -- coefficient of p / p 的系数
    d : ℚ   -- coefficient of q² / q² 的系数
    e : ℚ   -- coefficient of qp / qp 的系数
    f : ℚ   -- coefficient of p² / p² 的系数
open Obs public

-- Addition and ℚ-scaling are componentwise.
-- 加法与 ℚ-数乘按分量定义。
add : Obs → Obs → Obs
add (obs c a b d e f) (obs c' a' b' d' e' f') =
  obs (c + c') (a + a') (b + b') (d + d') (e + e') (f + f')

scale : ℚ → Obs → Obs
scale r (obs c a b d e f) =
  obs (r * c) (r * a) (r * b) (r * d) (r * e) (r * f)

neg : Obs → Obs
neg (obs c a b d e f) = obs (- c) (- a) (- b) (- d) (- e) (- f)

-- Basis observables.
-- 基观测量。
zero : Obs
zero = obs 0ℚ 0ℚ 0ℚ 0ℚ 0ℚ 0ℚ

one : Obs
one = obs 1ℚ 0ℚ 0ℚ 0ℚ 0ℚ 0ℚ

qO pO q²O qpO p²O : Obs
qO   = obs 0ℚ 1ℚ 0ℚ 0ℚ 0ℚ 0ℚ
pO   = obs 0ℚ 0ℚ 1ℚ 0ℚ 0ℚ 0ℚ
q²O  = obs 0ℚ 0ℚ 0ℚ 1ℚ 0ℚ 0ℚ
qpO  = obs 0ℚ 0ℚ 0ℚ 0ℚ 1ℚ 0ℚ
p²O  = obs 0ℚ 0ℚ 0ℚ 0ℚ 0ℚ 1ℚ

-- Small integer constants inside ℚ.
-- ℚ 中的小整数常量。
twoℚ fourℚ : ℚ
twoℚ  = 1ℚ + 1ℚ
fourℚ = twoℚ + twoℚ

------------------------------------------------------------------------
-- Canonical Poisson bracket
--
-- For f = Σ cᵢ mᵢ over the basis, {f,g} = f_q g_p − f_p g_q.  Reading
-- the elementary brackets {q,p} = 1 and the Leibniz rule off the basis
-- gives the coefficients below.  Each output coefficient is manifestly
-- antisymmetric: swapping the two arguments negates it.
--
-- 典范 Poisson 括号
--
-- 对 f = Σ cᵢ mᵢ，{f,g} = f_q g_p − f_p g_q。由基本括号 {q,p} = 1 与
-- Leibniz 法则在基上读出下列系数。每个输出系数均显式反对称：交换两个
-- 参数即取负。
------------------------------------------------------------------------

bracket : Obs → Obs → Obs
bracket (obs _ a b d e f) (obs _ a' b' d' e' f') =
  obs
    -- {q,p} = 1
    (a * b' + - (b * a'))
    -- q: {q,qp}=q, {q²,p}=2q, {qp,q}=-q, {p,q²}=-2q
    (a * e' + twoℚ * d * b' + - (e * a') + - (twoℚ * b * d'))
    -- p: {q,p²}=2p, {qp,p}=p, {p,qp}=-p, {p²,q}=-2p
    (twoℚ * a * f' + e * b' + - (b * e') + - (twoℚ * f * a'))
    -- q²: {q²,qp}=2q², {qp,q²}=-2q²
    (twoℚ * d * e' + - (twoℚ * e * d'))
    -- qp: {q²,p²}=4qp, {p²,q²}=-4qp
    (fourℚ * d * f' + - (fourℚ * f * d'))
    -- p²: {qp,p²}=2p², {p²,qp}=-2p²
    (twoℚ * e * f' + - (twoℚ * f * e'))

infix 6 bracket

------------------------------------------------------------------------
-- Elementary bracket table
--
-- Each entry normalises the unit/zero factors (k*1 = k, k*0 = 0 and
-- 0 + k = k) and then matches the displayed basis observable.
--
-- 基本括号乘法表
--
-- 每条先化简单位/零因子（k*1 = k、k*0 = 0、0 + k = k），再与所示基
-- 观测量匹配。
------------------------------------------------------------------------

private
  -- Normalise a coefficient built from unit and zero factors.
  -- 化简由单位与零因子构成的系数。
  norm1 : ∀ k → 1ℚ * k + - (0ℚ * k) ≡ k
  norm1 k = let open ≡-Reasoning in begin
    1ℚ * k + - (0ℚ * k)
    ≡⟨ cong (λ x → 1ℚ * k + - x) (*-zeroˡ k) ⟩
    1ℚ * k + - 0ℚ
    ≡⟨ cong (λ x → x + - 0ℚ) (*-identityˡ k) ⟩
    k + - 0ℚ
    ≡⟨ +-identityʳ k ⟩
    k ∎

  -- Strip three leading zero summands of a four-term coefficient.
  -- 消去四项系数开头的三个零加项。
  norm-tail : ∀ k → 0ℚ + (0ℚ + (0ℚ + k)) ≡ k
  norm-tail k = let open ≡-Reasoning in begin
    0ℚ + (0ℚ + (0ℚ + k))
    ≡⟨ +-identityˡ (0ℚ + (0ℚ + k)) ⟩
    0ℚ + (0ℚ + k)
    ≡⟨ +-identityˡ (0ℚ + k) ⟩
    0ℚ + k
    ≡⟨ +-identityˡ k ⟩
    k ∎

-- {q,p} = 1.
-- {q,p} = 1。
bracket-qp : bracket qO pO ≡ one
bracket-qp = cong (λ x → obs x 0ℚ 0ℚ 0ℚ 0ℚ 0ℚ) (norm1 1ℚ)

-- {q²,p} = 2q.
-- {q²,p} = 2q。
bracket-q²p : bracket q²O pO ≡ scale twoℚ qO
bracket-q²p =
  cong (λ x → obs 0ℚ x 0ℚ 0ℚ 0ℚ 0ℚ) (norm-tail twoℚ)

-- {q,p²} = 2p.
-- {q,p²} = 2p。
bracket-qp² : bracket qO p²O ≡ scale twoℚ pO
bracket-qp² =
  cong (λ x → obs 0ℚ 0ℚ x 0ℚ 0ℚ 0ℚ) (norm-tail twoℚ)

-- {q²,qp} = 2q².
-- {q²,qp} = 2q²。
bracket-q²qp : bracket q²O qpO ≡ scale twoℚ q²O
bracket-q²qp =
  cong (λ x → obs 0ℚ 0ℚ 0ℚ x 0ℚ 0ℚ) (norm-tail twoℚ)

-- {qp,p²} = 2p².
-- {qp,p²} = 2p²。
bracket-qpp² : bracket qpO p²O ≡ scale twoℚ p²O
bracket-qpp² =
  cong (λ x → obs 0ℚ 0ℚ 0ℚ 0ℚ 0ℚ x) (norm-tail twoℚ)

-- {q²,p²} = 4qp.
-- {q²,p²} = 4qp。
bracket-q²p² : bracket q²O p²O ≡ scale fourℚ qpO
bracket-q²p² =
  cong (λ x → obs 0ℚ 0ℚ 0ℚ 0ℚ x 0ℚ) (norm-tail fourℚ)
