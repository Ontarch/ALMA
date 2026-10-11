------------------------------------------------------------------------
-- Algebraic Newtonian mechanics: Jacobi identity and the harmonic
-- oscillator
--
-- Continuing from the preceding slices (QuadraticBilinear,
-- QuadraticSkew), which gave ℚ-bilinearity and skew-symmetry, this
-- slice closes the Lie-algebra axiomatics with the Jacobi identity and
-- then instantiates the algebraic dynamics on the harmonic oscillator,
-- whose velocities leave the constant (central) sector and rotate
-- within h₃. Everything is exact over ℚ. Every coefficient is a universal polynomial over ℚ,
-- so the standard-library ℚ ring solver discharges it.
--
-- 代数版牛顿力学：Jacobi 恒等式与谐振子
--
-- 承接前序切片（QuadraticBilinear、QuadraticSkew）已给的 ℚ-双线性与
-- 反对称性，本切片以 Jacobi 恒等式闭合其 Lie 代数公理，继而把代数动力学
-- 实例化为谐振子——其速度离开常数（中心）截段、在 h₃ 内部旋转。全部结论
-- 在 ℚ 上精确成立。每个系数都是 ℚ 上的
-- 全称多项式，故由标准库 ℚ 环求解器消去。
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module ALMA.Physics.Newton.QuadraticJacobi where

open import Data.Rational using (ℚ; 0ℚ; 1ℚ; _*_; _/_)
open import Data.Integer using (1ℤ)
open import Data.List.Base using (_∷_; [])
open import Data.Unit.Base using (⊤)
open import Data.Rational.Tactic.RingSolver as RationalRing
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Reflection
open import Tactic.RingSolver using (solve-macro)

open import ALMA.Physics.Newton.Quadratic using
  (Obs; obs; bracket; add; neg; zero; qO; pO; twoℚ; mkObs)

------------------------------------------------------------------------
-- Normalising ring-solver entry
--
-- The standard reflective solver only weak-head-reduces the goal, so a
-- coefficient hidden behind a nested bracket, a componentwise add or a
-- record projection is seen as an opaque constant. We normalise the
-- equation fully, open a fresh metavariable of that normalised type and
-- hand it to the ℚ ring solver. No type transport is ever used.
--
-- 范式化环求解入口
--
-- 标准反射求解器只对目标做弱头范式化，因而藏在嵌套括号、逐分量加法或
-- 记录投影之后的系数会被视作不透明常量。此处先把等式完全范式化，再以
-- 该范式化类型开一个新的元变量，交给 ℚ 环求解器。全程不使用任何类型
-- 传输。

macro
  solveℚ : Term → Term → TC ⊤
  solveℚ vars hole = do
    normalised-goal ← inferType hole >>= normalise
    solver-hole ← newMeta normalised-goal
    solve-macro vars (quote RationalRing.ring) solver-hole
    commitTC
    unify hole solver-hole

------------------------------------------------------------------------
-- Self-bracket
--
-- {f, f} = 0. Each coefficient is a ring expression that is its own
-- negative and hence zero over ℚ (characteristic zero); the ring solver
-- discharges all six fields uniformly.
--
-- 自括号
--
-- {f, f} = 0。每个系数都是与其负值相等的环表达式，在 ℚ（特征零）上为
-- 零；环求解器统一消去全部六个字段。

bracket-self : ∀ f → bracket f f ≡ zero
bracket-self (obs _ a b d e f) =
  mkObs
    (solveℚ (a ∷ b ∷ d ∷ e ∷ f ∷ []))
    (solveℚ (a ∷ b ∷ d ∷ e ∷ f ∷ []))
    (solveℚ (a ∷ b ∷ d ∷ e ∷ f ∷ []))
    (solveℚ (a ∷ b ∷ d ∷ e ∷ f ∷ []))
    (solveℚ (a ∷ b ∷ d ∷ e ∷ f ∷ []))
    (solveℚ (a ∷ b ∷ d ∷ e ∷ f ∷ []))

------------------------------------------------------------------------
-- The Jacobi identity
--
-- The cyclic sum of the double brackets vanishes, coefficient by
-- coefficient. This is the remaining Lie-algebra axiom; together with
-- ℚ-bilinearity and skew-symmetry the quadratic observables form a Lie
-- algebra over ℚ. Each of the six fields is a universal polynomial in
-- the fifteen non-constant coordinates, closed by the ring solver.
--
-- Jacobi 恒等式
--
-- 双重括号的循环和逐系数为零。这是最后一条 Lie 代数公理；与 ℚ-双线性
-- 及反对称性合起来，二次观测量在 ℚ 上构成 Lie 代数。六个字段各是十五
-- 个非常数坐标上的全称多项式，由环求解器闭合。

jacobi : ∀ f g h →
         add (add (bracket (bracket f g) h)
                  (bracket (bracket g h) f))
             (bracket (bracket h f) g) ≡ zero
jacobi (obs _ a b d e f)
       (obs _ a' b' d' e' f')
       (obs _ a″ b″ d″ e″ f″) =
  mkObs
    (solveℚ vars) (solveℚ vars) (solveℚ vars)
    (solveℚ vars) (solveℚ vars) (solveℚ vars)
  where
  -- The fifteen non-constant coordinates of f, g, h. The list is built
  -- inline in the where clause so the reflective solver receives the
  -- de Bruijn variable terms rather than an opaque list name.
  --
  -- f、g、h 的十五个非常数坐标。列表在 where 中就地构造，使反射求解器
  -- 收到 de Bruijn 变量项，而非不透明的列表名。
  vars = a ∷ b ∷ d ∷ e ∷ f
       ∷ a' ∷ b' ∷ d' ∷ e' ∷ f'
       ∷ a″ ∷ b″ ∷ d″ ∷ e″ ∷ f″ ∷ []

------------------------------------------------------------------------
-- The harmonic oscillator over ℚ
--
-- H = (q² + p²)/2 uses the rational coefficient 1/2 for both quadratic
-- terms. The factor two produced by differentiating a square cancels the
-- 1/2, so 2 · (1/2) = 1 and the equations of motion are exact.
--
-- ℚ 上的谐振子
--
-- H = (q² + p²)/2 的两个二次项系数均取有理数 1/2。对平方求导产生的因子
-- 2 与 1/2 相消，即 2·(1/2) = 1，故运动方程精确成立。

halfℚ : ℚ
halfℚ = 1ℤ / 2

-- 2 · (1/2) = 1; the square derivative factor cancels the denominator.
--
-- 2·(1/2) = 1；平方求导的因子与分母相消。
double-half : twoℚ * halfℚ ≡ 1ℚ
double-half = refl

-- H = (q² + p²) / 2: d = f = 1/2, all other coordinates zero.
--
-- H = (q² + p²)/2：取 d = f = 1/2，其余坐标为零。
H-harmonic : Obs
H-harmonic = obs 0ℚ 0ℚ 0ℚ halfℚ 0ℚ halfℚ

-- Hamiltonian vector field X_H u = {u, H}.
--
-- 哈密顿向量场 X_H u = {u, H}。
X : Obs → Obs → Obs
X H u = bracket u H

-- q̇ = {q, H} = p.
harmonic-qdot : X H-harmonic qO ≡ pO
harmonic-qdot = refl

-- ṗ = {p, H} = −q.
harmonic-pdot : X H-harmonic pO ≡ neg qO
harmonic-pdot = refl

-- Energy is conserved along its own flow: {H, H} = 0.
--
-- 能量沿自身流守恒：{H, H} = 0。
harmonic-energy : X H-harmonic H-harmonic ≡ zero
harmonic-energy = bracket-self H-harmonic
