------------------------------------------------------------------------
-- Algebraic Newtonian mechanics: Jacobi identity and the harmonic
-- oscillator
--
-- The quadratic Poisson bracket of the preceding slices is ℚ-bilinear
-- (QuadraticBilinear, QuadraticSkew) and skew-symmetric (QuadraticSkew).
-- This slice closes the Lie-algebra axiomatics with the Jacobi identity
--
--   { {f, g}, h } + { {g, h}, f } + { {h, f}, g } = 0,
--
-- then instantiates the algebraic dynamics on the harmonic oscillator
--
--   H = (q² + p²) / 2,   d = f = 1/2 over ℚ,
--
-- for which the Hamiltonian vector field X_H u = {u, H} gives
--
--   q̇ = {q, H} = p,   ṗ = {p, H} = −q,   {H, H} = 0.
--
-- The equations of motion are linear and stay in the degree≤1 sector:
-- the affine Heisenberg–Poisson algebra of the Poisson slice is exactly
-- the deg≤1 truncation of this quadratic algebra, so the oscillator is
-- the first dynamics whose velocities leave the constant (central)
-- sector and rotate within h₃. Everything is exact over ℚ; no analysis,
-- limits or real numbers enter.
--
-- Proof method. Every Jacobi coefficient is a universal polynomial in
-- the rational coordinates of f, g, h, hence a ring identity over ℚ.
-- The standard-library ℚ ring decision procedure discharges each of the
-- six coefficients. A thin reflection wrapper fully normalises the goal
-- first so that the nested bracket, the componentwise addition and the
-- record projections unfold to raw ring operations. This introduces no
-- transport, no cast and no subst: reflection only reconstructs a proof
-- of propositional equality from the ring homomorphism.
--
-- 代数版牛顿力学：Jacobi 恒等式与谐振子
--
-- 前序切片中的二次 Poisson 括号已具备 ℚ-双线性（QuadraticBilinear、
-- QuadraticSkew）与反对称性（QuadraticSkew）。本切片以 Jacobi 恒等式
--
--   { {f, g}, h } + { {g, h}, f } + { {h, f}, g } = 0
--
-- 闭合其 Lie 代数公理，继而把代数动力学实例化为谐振子
--
--   H = (q² + p²) / 2，  即在 ℚ 上取 d = f = 1/2，
--
-- 其哈密顿向量场 X_H u = {u, H} 给出
--
--   q̇ = {q, H} = p，   ṗ = {p, H} = −q，   {H, H} = 0。
--
-- 运动方程是线性的，且始终停留在次数≤1 的截段：Poisson 切片中的仿射
-- Heisenberg–Poisson 代数正是本二次代数的 deg≤1 截断。因此谐振子是
-- 首个速度离开常数（中心）截段、在 h₃ 内部旋转的动力学系统。全部结论
-- 在 ℚ 上精确成立，不涉及任何分析、极限或实数。
--
-- 证明方法。Jacobi 的每个系数都是 f、g、h 的 ℚ 坐标上的全称多项式，
-- 因而是 ℚ 上的环恒等式。标准库的 ℚ 环判定过程逐一消去六个系数。一层
-- 轻量反射包装先对目标做完全范式化，使嵌套括号、逐分量加法与记录投影
-- 全部展开为裸环运算。此处不引入任何 transport、cast 或 subst：反射仅
-- 经由环同态重写出命题相等的证明项。
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module ALMA.Physics.Newton.QuadraticJacobi where

open import Data.Rational using (ℚ; 0ℚ; 1ℚ; _*_; _/_)
open import Data.Integer using (1ℤ)
open import Data.List.Base using (_∷_; [])
open import Data.Unit.Base using (⊤)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; cong; module ≡-Reasoning)

open import Reflection
open import Reflection.TCM
open import Tactic.RingSolver as RingSolver using (solve-macro)
open import Data.Rational.Tactic.RingSolver as RationalRing

open import ALMA.Physics.Newton.Quadratic as Q using
  (Obs; obs; bracket; add; neg; zero; qO; pO; twoℚ)

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
-- Field-wise record assembly
--
-- Six coefficient equalities assemble into an equality of observables;
-- copied in the same cong-chaining style as the preceding slices.
--
-- 逐字段记录组装
--
-- 六个系数等式组装为一条观测量相等；沿用前序切片的 cong 链式风格。

private
  mkObs : ∀ {lc la lb ld le lf rc ra rb rd re rf}
        → lc ≡ rc → la ≡ ra → lb ≡ rb
        → ld ≡ rd → le ≡ re → lf ≡ rf
        → obs lc la lb ld le lf ≡ obs rc ra rb rd re rf
  mkObs pc pa pb pd pe pf = let open ≡-Reasoning in begin
    obs _ _ _ _ _ _
    ≡⟨ cong (λ x → obs x _ _ _ _ _) pc ⟩
    obs _ _ _ _ _ _
    ≡⟨ cong (λ x → obs _ x _ _ _ _) pa ⟩
    obs _ _ _ _ _ _
    ≡⟨ cong (λ x → obs _ _ x _ _ _) pb ⟩
    obs _ _ _ _ _ _
    ≡⟨ cong (λ x → obs _ _ _ x _ _) pd ⟩
    obs _ _ _ _ _ _
    ≡⟨ cong (λ x → obs _ _ _ _ x _) pe ⟩
    obs _ _ _ _ _ _
    ≡⟨ cong (obs _ _ _ _ _) pf ⟩
    obs _ _ _ _ _ _ ∎

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

-- One half in ℚ, written as the fraction 1 / 2.
--
-- ℚ 中的二分之一，写成分数 1 / 2。
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
--
-- q̇ = {q, H} = p。
harmonic-qdot : X H-harmonic qO ≡ pO
harmonic-qdot = refl

-- ṗ = {p, H} = −q.
--
-- ṗ = {p, H} = −q。
harmonic-pdot : X H-harmonic pO ≡ neg qO
harmonic-pdot = refl

-- Energy is conserved along its own flow: {H, H} = 0.
--
-- 能量沿自身流守恒：{H, H} = 0。
harmonic-energy : X H-harmonic H-harmonic ≡ zero
harmonic-energy = bracket-self H-harmonic
