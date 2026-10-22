------------------------------------------------------------------------
-- Boundedness of rational intervals
--
-- 有理区间的有界性
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module Real.Interval.Bounded where

open import Data.Nat using (ℕ; z≤n; s≤s)
open import Data.Integer using (+<+)
open import Data.Rational using (ℚ; 0ℚ; 1ℚ; _+_; ∣_∣; _≤_; _<_; -_)
open import Data.Rational.Base using (*<*)
open import Data.Rational.Properties using
  (+-mono-≤; +-identityˡ; +-identityʳ; +-comm; ≤-refl; ≤-trans; ≤-reflexive
  ; <⇒≤; 0≤∣p∣; ∣p∣≡p∨∣p∣≡-p; neg-antimono-≤; module ≤-Reasoning)
open ≤-Reasoning
open import Data.Product using (Σ; _,_; _×_)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (sym)

open import Real.Interval using (RealI)
open import Real.Interval.Order using (l; u; l-mono'; u-mono')
open import Real.Interval.Rational using (r≤|r|; -r≤|r|)

------------------------------------------------------------------------
-- Numerical constants and monotonicity helpers
--
-- 数值常量与单调性助手

0<1 : 0ℚ < 1ℚ
0<1 = *<* (+<+ (s≤s z≤n))

0≤1 : 0ℚ ≤ 1ℚ
0≤1 = <⇒≤ 0<1

m≤m+nℚ : ∀ m n → 0ℚ ≤ n → m ≤ m + n
m≤m+nℚ m n 0≤n = begin
  m
    ≤⟨ ≤-reflexive (sym (+-identityʳ m)) ⟩
  m + 0ℚ
    ≤⟨ +-mono-≤ (≤-refl {m}) 0≤n ⟩
  m + n
  ∎

------------------------------------------------------------------------
-- The uniform bound
--
-- M = |l x| + |u x| + 1, uniform in n.
--
-- 一致界
--
-- M = |l x| + |u x| + 1，对 n 一致。

bound : (x : RealI) → ℚ
bound x = ∣ RealI.l x ∣ + ∣ RealI.u x ∣ + 1ℚ

0≤A+B : (x : RealI) → 0ℚ ≤ ∣ RealI.l x ∣ + ∣ RealI.u x ∣
0≤A+B x = begin
  0ℚ
    ≤⟨ ≤-reflexive (sym (+-identityˡ 0ℚ)) ⟩
  0ℚ + 0ℚ
    ≤⟨ +-mono-≤ (0≤∣p∣ (RealI.l x)) (0≤∣p∣ (RealI.u x)) ⟩
  ∣ RealI.l x ∣ + ∣ RealI.u x ∣
  ∎

A+B≤bound : (x : RealI) →
  ∣ RealI.l x ∣ + ∣ RealI.u x ∣ ≤ bound x
A+B≤bound x = begin
  ∣ RealI.l x ∣ + ∣ RealI.u x ∣
    ≤⟨ ≤-reflexive (sym (+-identityʳ (∣ RealI.l x ∣ + ∣ RealI.u x ∣))) ⟩
  (∣ RealI.l x ∣ + ∣ RealI.u x ∣) + 0ℚ
    ≤⟨ +-mono-≤ (≤-refl {∣ RealI.l x ∣ + ∣ RealI.u x ∣}) 0≤1 ⟩
  (∣ RealI.l x ∣ + ∣ RealI.u x ∣) + 1ℚ
  ∎

0≤bound : (x : RealI) → 0ℚ ≤ bound x
0≤bound x = begin
  0ℚ
    ≤⟨ 0≤A+B x ⟩
  ∣ RealI.l x ∣ + ∣ RealI.u x ∣
    ≤⟨ A+B≤bound x ⟩
  bound x
  ∎

------------------------------------------------------------------------
-- Monotonicity of the endpoints at level 0
--
-- 端点在 0 层的单调性

l0≤ln : (x : RealI) (n : ℕ) → l x 0 ≤ l x n
l0≤ln x n = l-mono' x {n = 0} {m = n} z≤n

un≤u0 : (x : RealI) (n : ℕ) → u x n ≤ u x 0
un≤u0 x n = u-mono' x {n = 0} {m = n} z≤n

------------------------------------------------------------------------
-- The two sign cases of the membership bound
--
-- 成员界的两符号情形

a≤ux0 : (x : RealI) (n : ℕ) (a : ℚ) → a ≤ u x n → a ≤ u x 0
a≤ux0 x n a a≤uxn = ≤-trans a≤uxn (un≤u0 x n)

a≤A+B : (x : RealI) (a : ℚ) → a ≤ u x 0 →
  a ≤ ∣ RealI.l x ∣ + ∣ RealI.u x ∣
a≤A+B x a a≤ux0 = begin
  a
    ≤⟨ a≤ux0 ⟩
  u x 0
    ≤⟨ r≤|r| (RealI.u x) ⟩
  ∣ RealI.u x ∣
    ≤⟨ m≤m+nℚ ∣ RealI.u x ∣ ∣ RealI.l x ∣ (0≤∣p∣ (RealI.l x)) ⟩
  ∣ RealI.u x ∣ + ∣ RealI.l x ∣
    ≤⟨ ≤-reflexive (+-comm ∣ RealI.u x ∣ ∣ RealI.l x ∣) ⟩
  ∣ RealI.l x ∣ + ∣ RealI.u x ∣
  ∎

l0≤a : (x : RealI) (n : ℕ) (a : ℚ) → l x n ≤ a → l x 0 ≤ a
l0≤a x n a lxn≤a = ≤-trans (l0≤ln x n) lxn≤a

-a≤A+B : (x : RealI) (a : ℚ) → l x 0 ≤ a →
  - a ≤ ∣ RealI.l x ∣ + ∣ RealI.u x ∣
-a≤A+B x a l0≤a = begin
  - a
    ≤⟨ neg-antimono-≤ l0≤a ⟩
  - (l x 0)
    ≤⟨ -r≤|r| (RealI.l x) ⟩
  ∣ RealI.l x ∣
    ≤⟨ m≤m+nℚ ∣ RealI.l x ∣ ∣ RealI.u x ∣ (0≤∣p∣ (RealI.u x)) ⟩
  ∣ RealI.l x ∣ + ∣ RealI.u x ∣
  ∎

------------------------------------------------------------------------
-- The membership bound
--
-- 成员界

inside : (x : RealI) (n : ℕ) (a : ℚ) →
  l x n ≤ a → a ≤ u x n → ∣ a ∣ ≤ bound x
inside x n a lxn≤a a≤uxn with ∣p∣≡p∨∣p∣≡-p a
... | inj₁ |a|≡a = begin
  ∣ a ∣
    ≤⟨ ≤-reflexive |a|≡a ⟩
  a
    ≤⟨ a≤A+B x a (a≤ux0 x n a a≤uxn) ⟩
  ∣ RealI.l x ∣ + ∣ RealI.u x ∣
    ≤⟨ A+B≤bound x ⟩
  bound x
  ∎
... | inj₂ |a|≡-a = begin
  ∣ a ∣
    ≤⟨ ≤-reflexive |a|≡-a ⟩
  - a
    ≤⟨ -a≤A+B x a (l0≤a x n a lxn≤a) ⟩
  ∣ RealI.l x ∣ + ∣ RealI.u x ∣
    ≤⟨ A+B≤bound x ⟩
  bound x
  ∎

------------------------------------------------------------------------
-- Boundedness
--
-- 有界性

bounded : (x : RealI) → Σ ℚ λ M →
          0ℚ ≤ M ×
          (∀ n a → l x n ≤ a → a ≤ u x n → ∣ a ∣ ≤ M)
bounded x = bound x , 0≤bound x , inside x
