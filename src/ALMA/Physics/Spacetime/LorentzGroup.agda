------------------------------------------------------------------------
-- The Lorentz group O(V, g) as g-preserving transformations
--
-- A transformation of the rational four-vector space is Lorentz when it
-- preserves the Lorentz bilinear form:
--
--   IsLorentz A ⇔ ∀ v w → g(A v, A w) ≡ g(v, w) .
--
-- The identity is Lorentz and Lorentz transformations close under
-- composition, giving the monoid skeleton of O(3,1). The boost along x
-- is parametrised directly by its matrix entries (a, b) subject to
-- a² − b² = 1, which avoids the factor γ = 1/√(1−v²) that is not
-- rational. The ring solver first establishes
--
--   g(boost v, boost w) = (a² − b²)·g(v, w) ,
--
-- and the constraint a² − b² = 1 makes the boost Lorentz. The reverse
-- boost with entries (a, −b) is Lorentz as well and is the group
-- inverse. A concrete rational point is (a, b) = (5/4, 3/4).
--
-- Everything is exact and algebraic over ℚ; no analysis and no choice
-- principles are used.
--
-- 以保持 g 的变换刻画洛伦兹群 O(V, g)
--
-- 有理四向量空间上的变换为洛伦兹变换，当且仅当它保持洛伦兹双线性型：
--
--   IsLorentz A ⇔ ∀ v w → g(A v, A w) ≡ g(v, w) 。
--
-- 恒等变换是洛伦兹变换，且洛伦兹变换在合成下封闭，给出 O(3,1) 的幺
-- 半群骨架。沿 x 方向的推动（boost）直接以矩阵元 (a, b) 参数化，并要求
-- a² − b² = 1，从而避开非有理的因子 γ = 1/√(1−v²)。环求解器首先建立
--
--   g(boost v, boost w) = (a² − b²)·g(v, w) ，
--
-- 再由约束 a² − b² = 1 使该推动成为洛伦兹变换。以 (a, −b) 为矩阵元的
-- 反向推动同样是洛伦兹变换，即群逆元。具体有理点为 (a, b) = (5/4, 3/4)。
--
-- 全部内容皆为 ℚ 上精确、代数的，不使用分析，也不使用选择原理。
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module ALMA.Physics.Spacetime.LorentzGroup where

open import Data.Rational using
  (ℚ; 0ℚ; 1ℚ; _+_; _*_; _-_; _/_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Data.Rational.Properties using (*-identityˡ)
open import Data.Integer using (+_)
open import Data.List using (_∷_; [])
open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; cong; trans; module ≡-Reasoning)

open import ALMA.Physics.Spacetime.LorentzForm using
  (FourVec; mk4; g)
open FourVec using (t; x; y; z)

------------------------------------------------------------------------
-- The g-preservation predicate
--
-- 保持 g 的谓词

IsLorentz : (FourVec → FourVec) → Set
IsLorentz A = ∀ v w → g (A v) (A w) ≡ g v w

------------------------------------------------------------------------
-- Identity and composition
--
-- 恒等与合成

id4 : FourVec → FourVec
id4 v = v

id-lorentz : IsLorentz id4
id-lorentz v w = refl

comp-lorentz : ∀ A B → IsLorentz A → IsLorentz B →
  IsLorentz (A ∘ B)
comp-lorentz A B pA pB v w =
  trans (pA (B v) (B w)) (pB v w)

------------------------------------------------------------------------
-- The boost along x, parametrised by matrix entries (a, b)
--
-- 沿 x 方向的推动，以矩阵元 (a, b) 参数化

boost : ℚ → ℚ → FourVec → FourVec
boost a b v =
  mk4 (a * t v + b * x v)
      (b * t v + a * x v)
      (y v) (z v)

-- g(boost v, boost w) = (a² − b²)·g(v, w), fully inlined.
g-boost-raw : ∀ a b tv xv yv zv tw xw yw zw →
  ((a * tv + b * xv) * (a * tw + b * xw)
    - (b * tv + a * xv) * (b * tw + a * xw)
    - yv * yw - zv * zw)
  ≡ (a * a - b * b) * (tv * tw - xv * xw) - yv * yw - zv * zw
g-boost-raw a b tv xv yv zv tw xw yw zw =
  solve ( a ∷ b ∷ tv ∷ xv ∷ yv ∷ zv ∷ tw ∷ xw ∷ yw ∷ zw ∷ [])

-- A boost with a² − b² = 1 preserves g.
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
-- The reverse boost is the group inverse
--
-- 反向推动即群逆元

-- (−b)² = b².
neg-square : ∀ b → (0ℚ - b) * (0ℚ - b) ≡ b * b
neg-square b = solve (b ∷ [])

boost-inv-lorentz : ∀ a b → a * a - b * b ≡ 1ℚ →
  IsLorentz (boost a (0ℚ - b))
boost-inv-lorentz a b eq =
  boost-lorentz a (0ℚ - b)
    (trans (cong (λ c → a * a - c) (neg-square b)) eq)

------------------------------------------------------------------------
-- A concrete rational point (a, b) = (5/4, 3/4)
--
-- 具体有理点 (a, b) = (5/4, 3/4)

fifth : ℚ
fifth = + 5 / 4

threeq : ℚ
threeq = + 3 / 4

point-eq : fifth * fifth - threeq * threeq ≡ 1ℚ
point-eq = refl

boost5-lorentz : IsLorentz (boost fifth threeq)
boost5-lorentz = boost-lorentz fifth threeq point-eq
