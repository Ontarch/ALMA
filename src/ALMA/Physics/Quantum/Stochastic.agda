------------------------------------------------------------------------
-- Classical weighted edge families: stochastic kernels and composition
--
-- A Kernel m n maps each input to every outcome carrying a rational
-- weight, with each column summing to one. Composition is the classical
-- (L1) rule: along a two-step path the weights multiply, and the
-- intermediate outcomes are summed. Normalisation is preserved, proved
-- by finite-sum interchange and distributivity alone.
--
-- This is the probability equipment, distinct from the amplitude
-- equipment in Measurement: quantum (L2) amplitudes compose with
-- interference, whose norm preservation additionally requires
-- orthogonality of columns. That hypothesis is not assumed here; the
-- classical law below needs no such assumption.
--
-- 经典带权边族：随机核及其复合
--
-- Kernel m n 把每个输入送到所有结果并携带有理权重，每列权重和为一。
-- 复合遵循经典（L1）规则：两步路径上权重相乘，对中间结果求和。仅用
-- 有限和交换律与分配律即可证明归一化在复合下保持。
--
-- 这是概率装备，与 Measurement 的振幅装备不同：量子（L2）振幅复合带
-- 干涉，其范数保持还需列正交假设；此处不引入该假设，经典定律不需要。
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module ALMA.Physics.Quantum.Stochastic where

open import Data.Nat.Base as Nat using (ℕ)
open import Data.Fin.Base using (Fin; zero; suc)
open import Data.Rational using (ℚ; 0ℚ; 1ℚ; _+_; _*_)
open import Data.Rational.Properties using
  (+-identityˡ; *-comm; *-zeroʳ; *-identityʳ; *-distribˡ-+)
open import Function.Base using (_∘_)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; sym; trans; cong; cong₂; module ≡-Reasoning)

open import ALMA.Physics.Quantum.FiniteVec using (sumFin; sumFin-cong)
open import ALMA.Physics.RationalKit as Kit using (+interchange)

------------------------------------------------------------------------
-- Finite-sum algebra over ℚ
--
-- ℚ 上的有限和代数

private
  -- The sum of the constant-zero family is zero.
  --
  -- 常零族之和为零。
  sumFin-zero : ∀ n → sumFin {n} (λ (_ : Fin n) → 0ℚ) ≡ 0ℚ
  sumFin-zero Nat.zero    = refl
  sumFin-zero (Nat.suc n) = let open ≡-Reasoning in begin
    0ℚ + sumFin {n} (λ _ → 0ℚ)
    ≡⟨ +-identityˡ _ ⟩
    sumFin {n} (λ _ → 0ℚ)
    ≡⟨ sumFin-zero n ⟩
    0ℚ ∎

  -- Pointwise addition lifts to sums.
  --
  -- 逐点加法提升至求和。
  sumFin-+ : ∀ {n} (g h : Fin n → ℚ) →
             sumFin (λ i → g i + h i) ≡ sumFin g + sumFin h
  sumFin-+ {Nat.zero} g h = sym (+-identityˡ 0ℚ)
  sumFin-+ {Nat.suc n} g h = let open ≡-Reasoning in begin
    (g zero + h zero) + sumFin (λ i → g (suc i) + h (suc i))
    ≡⟨ cong ((g zero + h zero) +_)
            (sumFin-+ (g ∘ suc) (h ∘ suc)) ⟩
    (g zero + h zero) + (sumFin (g ∘ suc) + sumFin (h ∘ suc))
    ≡⟨ +interchange (g zero) (h zero)
                     (sumFin (g ∘ suc)) (sumFin (h ∘ suc)) ⟩
    (g zero + sumFin (g ∘ suc)) + (h zero + sumFin (h ∘ suc)) ∎

  -- A constant factor pulls out of a sum.
  --
  -- 常数因子提出求和号。
  sumFin-*ˡ : ∀ {n} (c : ℚ) (f : Fin n → ℚ) →
              sumFin (λ i → c * f i) ≡ c * sumFin f
  sumFin-*ˡ {Nat.zero} c f = sym (*-zeroʳ c)
  sumFin-*ˡ {Nat.suc n} c f = let open ≡-Reasoning in begin
    c * f zero + sumFin (λ i → c * f (suc i))
    ≡⟨ cong (c * f zero +_) (sumFin-*ˡ c (f ∘ suc)) ⟩
    c * f zero + c * sumFin (f ∘ suc)
    ≡⟨ sym (*-distribˡ-+ c (f zero) (sumFin (f ∘ suc))) ⟩
    c * (f zero + sumFin (f ∘ suc)) ∎

  -- Finite double sums interchange: Σ_i Σ_k a i k = Σ_k Σ_i a i k.
  --
  -- 有限双重求和可交换：Σ_i Σ_k a i k = Σ_k Σ_i a i k。
  sumFin-comm : ∀ {m p} (a : Fin m → Fin p → ℚ) →
                sumFin (λ i → sumFin (λ k → a i k)) ≡
                sumFin (λ k → sumFin (λ i → a i k))
  sumFin-comm {Nat.zero} {p} a = sym (sumFin-zero p)
  sumFin-comm {Nat.suc m} {p} a = let open ≡-Reasoning in begin
    sumFin (a zero) + sumFin (λ i → sumFin (λ k → a (suc i) k))
    ≡⟨ cong (sumFin (a zero) +_) (sumFin-comm (a ∘ suc)) ⟩
    sumFin (a zero) +
      sumFin (λ k → sumFin (λ i → a (suc i) k))
    ≡⟨ sym (sumFin-+ (a zero) (λ k → sumFin (λ i → a (suc i) k))) ⟩
    sumFin (λ k → a zero k + sumFin (λ i → a (suc i) k)) ∎

------------------------------------------------------------------------
-- Stochastic kernels
--
-- 随机核

-- A kernel from n inputs to m outcomes
--
-- cell i j is the weight of outcome i for input j, and every column sums
-- to one.
--
-- 从 n 个输入到 m 个结果的随机核
--
-- cell i j 是输入 j 得结果 i 的权重，每列和为一。
record Kernel (m n : ℕ) : Set where
  field
    cell   : Fin m → Fin n → ℚ
    totals : (j : Fin n) → sumFin (λ i → cell i j) ≡ 1ℚ
open Kernel

-- Kernel composition
--
-- V (n→p) followed by U (p→m) yields a kernel n→m whose cell sums over
-- the shared intermediate index k.
--
-- 随机核复合
--
-- V（n→p）后接 U（p→m）得 n→m 的核，其格子对共享中间指标 k 求和。
comp : ∀ {m p n} → Kernel p n → Kernel m p → Kernel m n
comp {m} {p} {n} V U = record
  { cell   = λ i j → sumFin (λ k → cell U i k * cell V k j)
  ; totals = totals-comp
  }
  where
  open ≡-Reasoning

  -- For a fixed intermediate k, pull the V-weight out of the sum over
  -- outcomes and use that column k of U sums to one.
  --
  -- 固定中间结果 k，把 V 的权重提出对结果的求和，并用 U 的第 k 列和为一。
  inner : ∀ (j : Fin n) (k : Fin p) →
          sumFin (λ i → cell U i k * cell V k j) ≡ cell V k j
  inner j k = begin
    sumFin (λ i → cell U i k * cell V k j)
    ≡⟨ sumFin-cong (λ i → *-comm (cell U i k) (cell V k j)) ⟩
    sumFin (λ i → cell V k j * cell U i k)
    ≡⟨ sumFin-*ˡ (cell V k j) (λ i → cell U i k) ⟩
    cell V k j * sumFin (λ i → cell U i k)
    ≡⟨ cong (cell V k j *_) (totals U k) ⟩
    cell V k j * 1ℚ
    ≡⟨ *-identityʳ (cell V k j) ⟩
    cell V k j ∎

  totals-comp : ∀ (j : Fin n) →
                sumFin (λ i → sumFin
                  (λ k → cell U i k * cell V k j)) ≡ 1ℚ
  totals-comp j = begin
    sumFin (λ i → sumFin (λ k → cell U i k * cell V k j))
    ≡⟨ sumFin-comm (λ i k → cell U i k * cell V k j) ⟩
    sumFin (λ k → sumFin (λ i → cell U i k * cell V k j))
    ≡⟨ sumFin-cong (inner j) ⟩
    sumFin (λ k → cell V k j)
    ≡⟨ totals V j ⟩
    1ℚ ∎
