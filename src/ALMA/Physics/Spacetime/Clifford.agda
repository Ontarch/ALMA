------------------------------------------------------------------------
-- The Clifford algebra Cl(3, 1) on its orthonormal basis
--
-- A blade is a subset of the four orthonormal generators, represented
-- directly by four booleans; there are sixteen blades, which are the
-- rational basis of Cl(3, 1). The generators obey the Clifford
-- relation eᵢ·eⱼ + eⱼ·eᵢ = 2·g(eᵢ, eⱼ). Left multiplication of a blade
-- P by a generator eᵢ is computed algebraically: if i ∉ P, eᵢ·P is the
-- blade P ∪ {i}, with sign (−1) raised to the number of generators in
-- P strictly before i; if i ∈ P, eᵢ·P contracts to P \\ {i}, with the
-- same positional sign multiplied by η(i) = eᵢ². The main theorem
-- clifford-rel checks, for all sixteen pairs (i, j), that the two
-- products coincide as blades and their coefficients sum to
-- 2·g(eᵢ, eⱼ).
--
-- 正交基上的克利福德代数 Cl(3, 1)
--
-- Blade（刃）是四个正交生成元的子集，直接用四个布尔值表示；共有
-- 十六个 blade，构成 Cl(3, 1) 的有理基。生成元满足克利福德关系
-- eᵢ·eⱼ + eⱼ·eᵢ = 2·g(eᵢ, eⱼ)。生成元 eᵢ 左乘 blade P 的代数计算：
-- 若 i ∉ P，eᵢ·P 为 blade P ∪ {i}，符号为 (−1) 的「P 中严格先于 i
-- 的生成元个数」次方；若 i ∈ P，eᵢ·P 收缩为 P \\ {i}，位置符号再乘
-- η(i) = eᵢ²。主定理 clifford-rel 对全部十六对 (i, j) 验证：两个乘
-- 积作为 blade 相同，且系数之和为 2·g(eᵢ, eⱼ)。
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module ALMA.Physics.Spacetime.Clifford where

open import Data.Nat using (ℕ; zero; suc) renaming (_+_ to _+ℕ_)
open import Data.Bool using (Bool; true; false)
open import Data.Rational using (ℚ; 0ℚ; 1ℚ; _+_; _*_; _-_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

------------------------------------------------------------------------
-- Basis labels and blades
--
-- 基标签与 blade

data Basis : Set where
  e0 e1 e2 e3 : Basis

record Blade : Set where
  constructor blade
  field b0 b1 b2 b3 : Bool
open Blade

bit : Bool → ℕ
bit true = 1
bit false = 0

------------------------------------------------------------------------
-- Signs and the squared-length of each generator
--
-- 符号与各生成元的平方长度

parity : ℕ → ℚ
parity zero = 1ℚ
parity (suc n) = 0ℚ - parity n

η : Basis → ℚ
η e0 = 1ℚ
η e1 = 0ℚ - 1ℚ
η e2 = 0ℚ - 1ℚ
η e3 = 0ℚ - 1ℚ

single : Basis → Blade
single e0 = blade true false false false
single e1 = blade false true false false
single e2 = blade false false true false
single e3 = blade false false false true

countBefore : Blade → Basis → ℕ
countBefore b e0 = 0
countBefore b e1 = bit (b0 b)
countBefore b e2 = bit (b0 b) +ℕ bit (b1 b)
countBefore b e3 =
  bit (b0 b) +ℕ bit (b1 b) +ℕ bit (b2 b)

member : Basis → Blade → Bool
member e0 = b0
member e1 = b1
member e2 = b2
member e3 = b3

insert : Basis → Blade → Blade
insert e0 b = blade true (b1 b) (b2 b) (b3 b)
insert e1 b = blade (b0 b) true (b2 b) (b3 b)
insert e2 b = blade (b0 b) (b1 b) true (b3 b)
insert e3 b = blade (b0 b) (b1 b) (b2 b) true

remove : Basis → Blade → Blade
remove e0 b = blade false (b1 b) (b2 b) (b3 b)
remove e1 b = blade (b0 b) false (b2 b) (b3 b)
remove e2 b = blade (b0 b) (b1 b) false (b3 b)
remove e3 b = blade (b0 b) (b1 b) (b2 b) false

------------------------------------------------------------------------
-- Left multiplication by a generator
--
-- 生成元左乘

leftMul : Basis → Blade → ℚ × Blade
leftMul i p with member i p
... | true  = (η i * parity (countBefore p i) , remove i p)
... | false = (parity (countBefore p i) , insert i p)

------------------------------------------------------------------------
-- g on the orthonormal basis
--
-- 正交基上的 g

gB : Basis → Basis → ℚ
gB e0 e0 = 1ℚ
gB e1 e1 = 0ℚ - 1ℚ
gB e2 e2 = 0ℚ - 1ℚ
gB e3 e3 = 0ℚ - 1ℚ
gB e0 e1 = 0ℚ; gB e0 e2 = 0ℚ; gB e0 e3 = 0ℚ
gB e1 e0 = 0ℚ; gB e1 e2 = 0ℚ; gB e1 e3 = 0ℚ
gB e2 e0 = 0ℚ; gB e2 e1 = 0ℚ; gB e2 e3 = 0ℚ
gB e3 e0 = 0ℚ; gB e3 e1 = 0ℚ; gB e3 e2 = 0ℚ

twoℚ : ℚ
twoℚ = 1ℚ + 1ℚ

------------------------------------------------------------------------
-- The Clifford relation on generators
--
-- 生成元上的克利福德关系

clifford-rel : ∀ i j →
  let s1 = proj₁ (leftMul i (single j))
      b1 = proj₂ (leftMul i (single j))
      s2 = proj₁ (leftMul j (single i))
      b2 = proj₂ (leftMul j (single i))
  in (b1 ≡ b2) × (s1 + s2 ≡ twoℚ * gB i j)

clifford-rel e0 e0 = refl , refl
clifford-rel e0 e1 = refl , refl
clifford-rel e0 e2 = refl , refl
clifford-rel e0 e3 = refl , refl
clifford-rel e1 e0 = refl , refl
clifford-rel e1 e1 = refl , refl
clifford-rel e1 e2 = refl , refl
clifford-rel e1 e3 = refl , refl
clifford-rel e2 e0 = refl , refl
clifford-rel e2 e1 = refl , refl
clifford-rel e2 e2 = refl , refl
clifford-rel e2 e3 = refl , refl
clifford-rel e3 e0 = refl , refl
clifford-rel e3 e1 = refl , refl
clifford-rel e3 e2 = refl , refl
clifford-rel e3 e3 = refl , refl

------------------------------------------------------------------------
-- Grade (the ℤ-grading skeleton)
--
-- 阶数（ℤ-分级骨架）

grade : Blade → ℕ
grade b =
  bit (b0 b) +ℕ bit (b1 b) +ℕ bit (b2 b) +ℕ bit (b3 b)

grade-single : ∀ i → grade (single i) ≡ 1
grade-single e0 = refl
grade-single e1 = refl
grade-single e2 = refl
grade-single e3 = refl
