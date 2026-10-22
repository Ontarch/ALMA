------------------------------------------------------------------------
-- Exact finite-dimensional quantum amplitudes over Gaussian rationals
--
-- A state is a finite family of Gaussian amplitudes Fin n → ℂ. Its
-- total squared norm is the (rational) mass of the state; a diagonal
-- (coordinate-wise) unit-modulus phase preserves that mass, and each
-- computational-basis Born weight is nonnegative. No analysis enters:
-- every quantity and proof here is exact and algebraic.
--
-- 高斯有理数上的精确有限维量子振幅
--
-- 态是有限振幅族 Fin n → ℂ；总平方范数即态的（有理）质量。坐标逐点
-- 作用的单位模相位保持该质量，且每个计算基 Born 权重非负。此处不含
-- 任何分析，所有量与证明皆精确、代数。
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module Physics.Quantum.FiniteVec where

open import Data.Nat.Base using (zero; suc)
open import Data.Fin.Base using (Fin; zero; suc)
open import Data.Product.Base using (_,_)
open import Data.Rational using (ℚ; 0ℚ; 1ℚ; _+_; _*_; _≤_)
open import Data.Rational.Base using (mkℚ; ∣_∣)
open import Data.Integer.Base using (+[1+_]; -[1+_]; +0)
open import Data.Rational.Properties using
  (+-identityˡ; +-mono-≤; *-zeroˡ; *-identityˡ; 0≤∣p∣; ∣-∣-nonNeg
  ; *-monoʳ-≤-nonNeg; ≤-reflexive; module ≤-Reasoning)
open import Function.Base using (_∘_)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; sym; cong₂; module ≡-Reasoning)

open import Physics.Quantum.Gaussian using (ℂ; _*ᶜ_; norm²; norm²-mul; Unit)
open import Base.RationalRing using (neg-neg-square)

------------------------------------------------------------------------
-- Rational squares are nonnegative
--
-- Double negation, sign-product and square laws on ℚ, needed below to
-- show each Born weight is nonnegative.
--
-- 有理平方非负
--
-- ℚ 上的双重否定、符号乘积与平方律，用于下面证明每个 Born 权重非负。

private
  -- |x|² = x² by sign cases on the normalised numerator.
  --
  -- 按规范化分子的符号分情形：|x|² = x²。
  abs²≡² : ∀ x → ∣ x ∣ * ∣ x ∣ ≡ x * x
  abs²≡² (mkℚ +[1+ _ ] _ _) = refl
  abs²≡² (mkℚ +0       _ _) = refl
  abs²≡² x@(mkℚ -[1+ _ ] _ _) = let open ≡-Reasoning in begin
    ∣ x ∣ * ∣ x ∣
    ≡⟨ neg-neg-square x ⟩
    x * x ∎

  -- Every rational square is nonnegative, via |x| ≥ 0.
  --
  -- 由 |x| ≥ 0 得每个有理平方非负。
  0≤sq : ∀ x → 0ℚ ≤ x * x
  0≤sq x = begin
    0ℚ
    ≤⟨ ≤-reflexive (sym (*-zeroˡ (∣ x ∣))) ⟩
    0ℚ * ∣ x ∣
    ≤⟨ *-monoʳ-≤-nonNeg (∣ x ∣) {{∣-∣-nonNeg x}} (0≤∣p∣ x) ⟩
    ∣ x ∣ * ∣ x ∣
    ≡⟨ abs²≡² x ⟩
    x * x ∎
    where open ≤-Reasoning

------------------------------------------------------------------------
-- Finite sums and total squared norm
--
-- Sum over Fin n, peeling off the zero index.
--
-- 有限求和与总平方范数
--
-- 对 Fin n 求和，剥出零号指标。
sumFin : ∀ {n} → (Fin n → ℚ) → ℚ
sumFin {zero}  f = 0ℚ
sumFin {suc n} f = f zero + sumFin (f ∘ suc)

-- Pointwise equal families have equal sums.
--
-- 逐点相等的族求和相等。
sumFin-cong : ∀ {n} {f g : Fin n → ℚ} →
              (∀ i → f i ≡ g i) → sumFin f ≡ sumFin g
sumFin-cong {zero}  h = refl
sumFin-cong {suc n} h =
  cong₂ _+_ (h zero) (sumFin-cong (h ∘ suc))

-- Total squared norm (total mass) of a finite state.
--
-- 有限态的总平方范数（总质量）。
total : ∀ {n} → (Fin n → ℂ) → ℚ
total ψ = sumFin (λ k → norm² (ψ k))

------------------------------------------------------------------------
-- Diagonal phases preserve total mass
--
-- Coordinate-wise multiplication by a family of phases.
--
-- 对角相位保持总质量
--
-- 逐点乘以一族相位。
phase : ∀ {n} → (u : Fin n → ℂ) → (Fin n → ℂ) → (Fin n → ℂ)
phase u ψ k = u k *ᶜ ψ k

-- At a single coordinate a unit phase leaves the squared norm fixed.
--
-- 单位相位在单个坐标上保持平方范数。
norm²-phase : ∀ {n} (u ψ : Fin n → ℂ) →
              (∀ k → Unit (u k)) →
              ∀ k → norm² (phase u ψ k) ≡ norm² (ψ k)
norm²-phase u ψ hu k
  rewrite norm²-mul (u k) (ψ k) | hu k = *-identityˡ (norm² (ψ k))

-- A diagonal unit-modulus transformation preserves total mass.
--
-- 对角单位模变换保持总质量。
total-phase : ∀ {n} (u ψ : Fin n → ℂ) →
              (∀ k → Unit (u k)) →
              total (phase u ψ) ≡ total ψ
total-phase u ψ hu = sumFin-cong (norm²-phase u ψ hu)

------------------------------------------------------------------------
-- Computational-basis Born weights
--
-- Born weight of outcome k: the squared amplitude at k.
--
-- 计算基 Born 权重
--
-- 结果 k 的 Born 权重：k 处振幅的平方范数。
prob : ∀ {n} (ψ : Fin n → ℂ) (k : Fin n) → ℚ
prob ψ k = norm² (ψ k)

-- A state is normalised when its total mass is one.
--
-- 总质量为一的态称为归一化态。
Normalized : ∀ {n} (ψ : Fin n → ℂ) → Set
Normalized ψ = total ψ ≡ 1ℚ

-- A squared norm is a sum of two squares, hence nonnegative.
--
-- 平方范数是两个平方之和，故非负。
norm²-nonNeg : ∀ (z : ℂ) → 0ℚ ≤ norm² z
norm²-nonNeg (a , b) = begin
  0ℚ
  ≤⟨ ≤-reflexive (sym (+-identityˡ 0ℚ)) ⟩
  0ℚ + 0ℚ
  ≤⟨ +-mono-≤ (0≤sq a) (0≤sq b) ⟩
  a * a + b * b ∎
  where open ≤-Reasoning

-- Every Born weight is nonnegative.
--
-- 每个 Born 权重非负。
prob-nonNeg : ∀ {n} (ψ : Fin n → ℂ) (k : Fin n) → 0ℚ ≤ prob ψ k
prob-nonNeg ψ k = norm²-nonNeg (ψ k)

-- For a normalised state the Born weights sum to one.
--
-- 归一化态的 Born 权重之和为一。
probs-sum-to-one : ∀ {n} (ψ : Fin n → ℂ) →
                   Normalized ψ → sumFin (prob ψ) ≡ 1ℚ
probs-sum-to-one ψ norm = norm
