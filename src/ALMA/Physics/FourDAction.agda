------------------------------------------------------------------------
-- Four-dimensional Benincasa–Dowker action: the integer chain core
--
-- In four spacetime dimensions the discrete scalar curvature at an
-- event x is
--
--   R(x) = (4 / √6) · (1 / l²) · [ 1 − N₀(x) + 9 N₁(x)
--                                   − 16 N₂(x) + 8 N₃(x) ] ,
--
-- and the action, summing over a finite causal set C with n events, is
--
--   S(C) / ℏ = (4 / √6) · (l / l_p)² · [ n − N₀ + 9 N₁
--                                          − 16 N₂ + 8 N₃ ] .
--
-- The k-abundance N_k is the number of strictly ordered pairs (x, y)
-- whose inclusive order interval has cardinality exactly k + 2:
--
--   N_k = |{ (x, y) : x ≺ y, |I[x, y]| = k + 2 }| .
--
-- The bracketed expression is an exact integer computed purely from
-- the causal order; this module delivers that integer core as bd4. The
-- overall physical factor (4 / √6)(l / l_p)² contains the irrational
-- √6 and is not formalized over ℚ: it is an external calibration, as is
-- the factor 1/l² in R(x). No ℝ and no analysis enter the core.
--
-- The four-point diamond is checked: N₀ = 4, N₁ = 0, N₂ = 1, N₃ = 0,
-- and bd4 = −16. The diamond is a 1+1 poset rather than a four-dim
-- sprinkling, so a non-zero four-dimensional action is the expected
-- result; the theorem validates the exact counting and weighting, not a
-- physical zero.
--
-- 四维 Benincasa–Dowker 作用量：整数链核
--
-- 四维时空下，事件 x 处的离散标量曲率为
--
--   R(x) = (4 / √6) · (1 / l²) · [ 1 − N₀(x) + 9 N₁(x)
--                                   − 16 N₂(x) + 8 N₃(x) ] ，
--
-- 对含 n 事件的有限因果集 C 求和，作用量为
--
--   S(C) / ℏ = (4 / √6) · (l / l_p)² · [ n − N₀ + 9 N₁
--                                          − 16 N₂ + 8 N₃ ] 。
--
-- k-丰度 N_k 是包含序区间基数恰为 k + 2 的严格可比对 (x, y) 数：
--
--   N_k = |{ (x, y)：x ≺ y，|I[x, y]| = k + 2 }| 。
--
-- 方括号内为纯由因果序计算的精确整数；本模块将该整数核交付为 bd4。整
-- 体物理因子 (4 / √6)(l / l_p)² 含无理数 √6，不在 ℚ 上形式化，它是外部
-- 标定，R(x) 中的 1/l² 亦然。核内无需 ℝ、无需分析。
--
-- 四点菱形检验：N₀ = 4，N₁ = 0，N₂ = 1，N₃ = 0，bd4 = −16。菱形是
-- 1+1 偏序而非四维 sprinkling，故四维作用量非零是预期结果；定理验证的是
-- 精确计数与加权，而非物理零值。
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module ALMA.Physics.FourDAction where

open import Data.Nat using (ℕ; zero; suc)
  renaming (_+_ to _+ℕ_; _≡ᵇ_ to _≡ℕᵇ_)
open import Data.Fin using (Fin)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Integer using (ℤ; _+_; _-_; _*_; +_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import ALMA.Physics.CausalSet using (diamond; boolFilter; sumOver)
open ALMA.Physics.CausalSet.Core
  using (events; interval-volume)

------------------------------------------------------------------------
-- k-abundance: strictly ordered pairs with inclusive volume k + 2
--
-- k-丰度：包含体积为 k + 2 的严格可比对

abundance : ∀ n (o : Fin n → Fin n → Bool) → ℕ → ℕ
abundance n o k =
  sumOver (events n o) λ x →
  sumOver (boolFilter (λ y → o x y) (events n o)) λ y →
  if interval-volume n o x y ≡ℕᵇ (k +ℕ 2) then 1 else 0

N0 : ∀ n (o : Fin n → Fin n → Bool) → ℕ
N0 n o = abundance n o 0
N1 : ∀ n (o : Fin n → Fin n → Bool) → ℕ
N1 n o = abundance n o 1
N2 : ∀ n (o : Fin n → Fin n → Bool) → ℕ
N2 n o = abundance n o 2
N3 : ∀ n (o : Fin n → Fin n → Bool) → ℕ
N3 n o = abundance n o 3

------------------------------------------------------------------------
-- Integer four-dimensional BD core: n − N0 + 9 N1 − 16 N2 + 8 N3
--
-- 四维 BD 整数核：n − N0 + 9 N1 − 16 N2 + 8 N3

bd4 : ∀ n (o : Fin n → Fin n → Bool) → ℤ
bd4 n o =
  + n
  - + (N0 n o)
  + + 9 * + (N1 n o)
  - + 16 * + (N2 n o)
  + + 8 * + (N3 n o)

------------------------------------------------------------------------
-- Diamond reference
--
-- 菱形参考

diamond-N0 : N0 4 diamond ≡ 4
diamond-N0 = refl
diamond-N1 : N1 4 diamond ≡ 0
diamond-N1 = refl
diamond-N2 : N2 4 diamond ≡ 1
diamond-N2 = refl
diamond-N3 : N3 4 diamond ≡ 0
diamond-N3 = refl

diamond-bd4 : bd4 4 diamond ≡ + 0 - + 16
diamond-bd4 = refl
