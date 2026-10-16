------------------------------------------------------------------------
-- Boundedness of rational intervals
--
-- Every rational interval is bounded: there is a rational M ≥ 0 such
-- that any a lying in the n-th approximant of x satisfies |a| ≤ M.
-- The bound is M = |l x| + |u x| + 1, uniform in n.
--
-- 有理区间的有界性
--
-- 每个有理区间都有界：存在有理数 M ≥ 0，使落在 x 第 n 层近似中的
-- 任意 a 满足 |a| ≤ M。界为 M = |l x| + |u x| + 1，对 n 一致。
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module ALMA.Base.Real.Interval.Bounded where

open import Data.Nat using (ℕ; z≤n; s≤s)
open import Data.Integer using (+<+)
open import Data.Rational using (ℚ; 0ℚ; 1ℚ; _+_; ∣_∣; _≤_; _<_)
open import Data.Rational.Base using (*<*) renaming (-_ to neg)
open import Data.Rational.Properties using
  (+-mono-≤; +-identityˡ; +-identityʳ; +-comm; ≤-refl; ≤-trans; ≤-reflexive
  ; <⇒≤; 0≤∣p∣; ∣p∣≡p∨∣p∣≡-p; neg-antimono-≤; module ≤-Reasoning)
open ≤-Reasoning
open import Data.Product using (Σ; _,_; _×_)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; sym)

open import ALMA.Base.Real.Interval using (RealI)
open import ALMA.Base.Real.Interval.Order using (l; u; l-mono'; u-mono')
open import ALMA.Base.Real.Interval.Rational using (r≤|r|; -r≤|r|)

------------------------------------------------------------------------
-- Boundedness
--
-- 有界性

bounded : (x : RealI) → Σ ℚ λ M →
          0ℚ ≤ M ×
          (∀ n a → l x n ≤ a → a ≤ u x n → ∣ a ∣ ≤ M)
bounded x = M , 0≤M , inside
  where
    M : ℚ
    M = ∣ RealI.l x ∣ + ∣ RealI.u x ∣ + 1ℚ

    0<1 : 0ℚ < 1ℚ
    0<1 = *<* (+<+ (s≤s z≤n))

    0≤1 : 0ℚ ≤ 1ℚ
    0≤1 = <⇒≤ 0<1

    0≤M : 0ℚ ≤ M
    0≤M = begin
      0ℚ
        ≤⟨ step1 ⟩
      A + B
        ≤⟨ step2 ⟩
      (A + B) + 1ℚ
      ∎
      where
        A = ∣ RealI.l x ∣
        B = ∣ RealI.u x ∣

        step1 : 0ℚ ≤ A + B
        step1 = begin
          0ℚ
            ≤⟨ ≤-reflexive (sym (+-identityˡ 0ℚ)) ⟩
          0ℚ + 0ℚ
            ≤⟨ +-mono-≤ (0≤∣p∣ (RealI.l x)) (0≤∣p∣ (RealI.u x)) ⟩
          A + B
          ∎

        step2 : A + B ≤ (A + B) + 1ℚ
        step2 = begin
          A + B
            ≤⟨ ≤-reflexive (sym (+-identityʳ (A + B))) ⟩
          (A + B) + 0ℚ
            ≤⟨ +-mono-≤ (≤-refl {A + B}) 0≤1 ⟩
          (A + B) + 1ℚ
          ∎

    l0≤ln : ∀ n → l x 0 ≤ l x n
    l0≤ln n = l-mono' x {n = 0} {m = n} z≤n

    un≤u0 : ∀ n → u x n ≤ u x 0
    un≤u0 n = u-mono' x {n = 0} {m = n} z≤n

    m≤m+nℚ : ∀ m n → 0ℚ ≤ n → m ≤ m + n
    m≤m+nℚ m n 0≤n = begin
      m
        ≤⟨ ≤-reflexive (sym (+-identityʳ m)) ⟩
      m + 0ℚ
        ≤⟨ +-mono-≤ (≤-refl {m}) 0≤n ⟩
      m + n
      ∎

    bound-M : ∣ RealI.l x ∣ + ∣ RealI.u x ∣ ≤ M
    bound-M = m≤m+nℚ (∣ RealI.l x ∣ + ∣ RealI.u x ∣) 1ℚ 0≤1

    inside : ∀ n a → l x n ≤ a → a ≤ u x n → ∣ a ∣ ≤ M
    inside n a lxn≤a a≤uxn with ∣p∣≡p∨∣p∣≡-p a
    ... | inj₁ |a|≡a = begin
      ∣ a ∣
        ≤⟨ ≤-reflexive |a|≡a ⟩
      a
        ≤⟨ a≤sum ⟩
      ∣ RealI.l x ∣ + ∣ RealI.u x ∣
        ≤⟨ bound-M ⟩
      M
      ∎
      where
        a≤ux0 : a ≤ u x 0
        a≤ux0 = ≤-trans a≤uxn (un≤u0 n)

        a≤sum : a ≤ ∣ RealI.l x ∣ + ∣ RealI.u x ∣
        a≤sum = begin
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

    ... | inj₂ |a|≡-a = begin
      ∣ a ∣
        ≤⟨ ≤-reflexive |a|≡-a ⟩
      neg a
        ≤⟨ -a≤sum ⟩
      ∣ RealI.l x ∣ + ∣ RealI.u x ∣
        ≤⟨ bound-M ⟩
      M
      ∎
      where
        l0≤a : l x 0 ≤ a
        l0≤a = ≤-trans (l0≤ln n) lxn≤a

        -a≤sum : neg a ≤ ∣ RealI.l x ∣ + ∣ RealI.u x ∣
        -a≤sum = begin
          neg a
            ≤⟨ neg-antimono-≤ l0≤a ⟩
          neg (l x 0)
            ≤⟨ -r≤|r| (RealI.l x) ⟩
          ∣ RealI.l x ∣
            ≤⟨ m≤m+nℚ ∣ RealI.l x ∣ ∣ RealI.u x ∣ (0≤∣p∣ (RealI.u x)) ⟩
          ∣ RealI.l x ∣ + ∣ RealI.u x ∣
          ∎
