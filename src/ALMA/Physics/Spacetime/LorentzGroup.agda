------------------------------------------------------------------------
-- The Lorentz group O(V, g) as g-preserving transformations
--
-- A transformation of the rational four-vector space is Lorentz when
-- it preserves the Lorentz bilinear form:
--
--   IsLorentz A ⇔ ∀ v w → g(A v, A w) ≡ g(v, w) .
--
-- Such transformations form the monoid skeleton of O(3,1). The boost
-- along x is parametrised directly by its matrix entries (a, b)
-- subject to a² − b² = 1, which avoids the factor γ = 1/√(1−v²) that
-- is not rational; the ring solver first establishes
--
--   g(boost v, boost w) = (a² − b²)·g(v, w) ,
--
-- and the constraint makes the boost Lorentz. A rational example is
-- (a, b) = (5/4, 3/4).
--
-- 以保持 g 的变换刻画洛伦兹群 O(V, g)
--
-- 有理四向量空间上的变换为洛伦兹变换，当且仅当它保持洛伦兹双线性型：
--
--   IsLorentz A ⇔ ∀ v w → g(A v, A w) ≡ g(v, w) 。
--
-- 此类变换构成 O(3,1) 的幺半群骨架。沿 x 方向的推动直接以矩阵元
-- (a, b) 参数化，并要求 a² − b² = 1，从而避开非有理的因子
-- γ = 1/√(1−v²)；环求解器首先建立
--
--   g(boost v, boost w) = (a² − b²)·g(v, w) ，
--
-- 再由约束使该推动成为洛伦兹变换。一个有理例为 (a, b) = (5/4, 3/4)。
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module ALMA.Physics.Spacetime.LorentzGroup where

open import Data.Rational using
  (ℚ; 0ℚ; 1ℚ; _+_; _*_; _-_; _/_; -_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Data.Rational.Properties using (*-identityˡ)
open import Data.Integer using (+_)
open import Data.List using (_∷_; [])
open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; cong; trans; module ≡-Reasoning)

open import ALMA.Physics.Spacetime.LorentzForm using (FourVec; mk4; g)
open FourVec using (t; x; y; z)

------------------------------------------------------------------------
-- The g-preservation predicate
--
-- Defines the predicate whose monoid closure is established below.
--
-- 保持 g 的谓词
--
-- 定义下面将要建立幺半群封闭性的谓词。

IsLorentz : (FourVec → FourVec) → Set
IsLorentz A = ∀ v w → g (A v) (A w) ≡ g v w

------------------------------------------------------------------------
-- Identity and composition
--
-- Establishes that IsLorentz is closed under identity and composition.
--
-- 恒等与合成
--
-- 建立 IsLorentz 在恒等与合成下的封闭性。

id4 : FourVec → FourVec
id4 v = v

id-lorentz : IsLorentz id4
id-lorentz v w = refl

comp-lorentz : ∀ A B → IsLorentz A → IsLorentz B →
  IsLorentz (A ∘ B)
comp-lorentz A B pA pB v w =
  trans (pA (B v) (B w)) (pB v w)

------------------------------------------------------------------------
-- The x-boost
--
-- Evaluates g on a pair of boosted vectors, inlined so the ring solver
-- sees only ring expressions.
--
-- x-推动
--
-- 计算一对推动后向量的 g 值，内联以便环求解器只看到环表达式。

boost : ℚ → ℚ → FourVec → FourVec
boost a b v =
  mk4 (a * t v + b * x v)
      (b * t v + a * x v)
      (y v) (z v)

-- g(boost v, boost w) = (a² − b²)·g(v, w), fully inlined.
--
-- g(boost v, boost w) = (a² − b²)·g(v, w)，全内联。
g-boost-raw : ∀ a b tv xv yv zv tw xw yw zw →
  ((a * tv + b * xv) * (a * tw + b * xw)
    - (b * tv + a * xv) * (b * tw + a * xw)
    - yv * yw - zv * zw)
  ≡ (a * a - b * b) * (tv * tw - xv * xw) - yv * yw - zv * zw
g-boost-raw a b tv xv yv zv tw xw yw zw =
  solve ( a ∷ b ∷ tv ∷ xv ∷ yv ∷ zv ∷ tw ∷ xw ∷ yw ∷ zw ∷ [])

-- A boost with a² − b² = 1 preserves g.
--
-- 满足 a² − b² = 1 的推动保持 g。
boost-lorentz : ∀ a b → a * a - b * b ≡ 1ℚ → IsLorentz (boost a b)
boost-lorentz a b eq v w =
  let open ≡-Reasoning
      tx = t v * t w - x v * x w
  in begin
    g (boost a b v) (boost a b w)
    ≡⟨ g-boost-raw a b (t v) (x v) (y v) (z v) (t w) (x w) (y w) (z w) ⟩
    (a * a - b * b) * tx - y v * y w - z v * z w
    ≡⟨ cong (λ c → c * tx - y v * y w - z v * z w) eq ⟩
    1ℚ * tx - y v * y w - z v * z w
    ≡⟨ cong (λ c → c - y v * y w - z v * z w) (*-identityˡ tx) ⟩
    tx - y v * y w - z v * z w ∎

------------------------------------------------------------------------
-- The inverse boost
--
-- Shows that the boost with entries (a, −b) is Lorentz whenever the
-- forward boost is, so it acts as the group inverse.
--
-- 逆推动
--
-- 证明矩阵元为 (a, −b) 的推动在前向推动为洛伦兹时也为洛伦兹，从而
-- 充当群逆元。

-- (−b)² = b².
--
-- (−b)² = b²。
neg-square : ∀ b → (0ℚ - b) * (0ℚ - b) ≡ b * b
neg-square b = solve (b ∷ [])

boost-inv-lorentz : ∀ a b → a * a - b * b ≡ 1ℚ →
  IsLorentz (boost a (0ℚ - b))
boost-inv-lorentz a b eq =
  boost-lorentz a (0ℚ - b)
    (trans (cong (λ c → a * a - c) (neg-square b)) eq)

------------------------------------------------------------------------
-- Rational example
--
-- Instantiates the boost at (a, b) = (5/4, 3/4).
--
-- 有理例
--
-- 在 (a, b) = (5/4, 3/4) 处实例化推动。

fifth : ℚ
fifth = + 5 / 4

threeq : ℚ
threeq = + 3 / 4

point-eq : fifth * fifth - threeq * threeq ≡ 1ℚ
point-eq = refl

boost5-lorentz : IsLorentz (boost fifth threeq)
boost5-lorentz = boost-lorentz fifth threeq point-eq
