------------------------------------------------------------------------
-- Arithmetic on rational intervals
--
-- Defines 0, 1, addition, negation and subtraction on RealI. Each
-- operation is defined componentwise on the endpoints and next, with
-- nest assembled from the corresponding pointwise inequalities.
--
-- 有理区间上的算术
--
-- 定义 RealI 上的 0、1、加法、取负与减法。每个运算逐分量定义于端点
-- 与 next 上，nest 由相应的逐点不等式组装。
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module ALMA.Base.Real.Interval.Arith where

open import Data.Rational using (ℚ; 0ℚ; 1ℚ; _+_; _-_; _≤_)
open import Data.Rational.Base using (_÷_; 1/_) renaming (-_ to neg)
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.Rational.Properties using
  (+-mono-<; +-mono-≤; neg-antimono-<; neg-antimono-≤; *-distribʳ-+; ≤-reflexive; ≤-trans)
open import Relation.Binary.PropositionalEquality using
  (_≡_; cong; sym; subst; module ≡-Reasoning)
open ≡-Reasoning

open import ALMA.Base.Real using (embed)
open import ALMA.Base.Real.Interval using (RealI; dyadic)
open import ALMA.Base.Real.Interval.Rational using (sub-add; neg-sub)

------------------------------------------------------------------------
-- Division distributes over addition
--
-- Requires the NonZero instance for embed 2.
--
-- 除法对加法分配
--
-- 需要 embed 2 的 NonZero 实例。

div-add : (a b : ℚ) → (a + b) ÷ embed 2 ≡ (a ÷ embed 2) + (b ÷ embed 2)
div-add a b = begin
    (a + b) ÷ embed 2
  ≡⟨ *-distribʳ-+ (1/ embed 2) a b ⟩
    (a ÷ embed 2) + (b ÷ embed 2)
  ∎

------------------------------------------------------------------------
-- Zero and one
--
-- 零与一

0ℝ : RealI
0ℝ = dyadic 0ℚ 0

1ℝ : RealI
1ℝ = dyadic 1ℚ 0

------------------------------------------------------------------------
-- Addition
--
-- 加法

infixl 6 _+ℝ_

_+ℝ_ : RealI → RealI → RealI
RealI.l (x +ℝ y)    = RealI.l x + RealI.l y
RealI.u (x +ℝ y)    = RealI.u x + RealI.u y
RealI.lo (x +ℝ y)   = +-mono-< (RealI.lo x) (RealI.lo y)
RealI.next (x +ℝ y) = RealI.next x +ℝ RealI.next y
RealI.nest (x +ℝ y) = nest1 , nest2 , nest3
  where
    nest1 : RealI.l x + RealI.l y
          ≤ RealI.l (RealI.next x) + RealI.l (RealI.next y)
    nest1 = +-mono-≤ (proj₁ (RealI.nest x)) (proj₁ (RealI.nest y))

    nest2 : RealI.u (RealI.next x) + RealI.u (RealI.next y)
          ≤ RealI.u x + RealI.u y
    nest2 = +-mono-≤ (proj₁ (proj₂ (RealI.nest x)))
                     (proj₁ (proj₂ (RealI.nest y)))

    nest3 : (RealI.u (RealI.next x) + RealI.u (RealI.next y))
            - (RealI.l (RealI.next x) + RealI.l (RealI.next y))
          ≤ ((RealI.u x + RealI.u y) - (RealI.l x + RealI.l y)) ÷ embed 2
    nest3 =
      let
        ux  = RealI.u x;  uy  = RealI.u y
        lx  = RealI.l x;  ly  = RealI.l y
        ux' = RealI.u (RealI.next x); uy' = RealI.u (RealI.next y)
        lx' = RealI.l (RealI.next x); ly' = RealI.l (RealI.next y)
        wx  = ux - lx;  wy  = uy - ly
        wx' = ux' - lx'; wy' = uy' - ly'

        step-x : wx' ≤ wx ÷ embed 2
        step-x = proj₂ (proj₂ (RealI.nest x))

        step-y : wy' ≤ wy ÷ embed 2
        step-y = proj₂ (proj₂ (RealI.nest y))

        step1 : wx' + wy' ≤ (wx ÷ embed 2) + (wy ÷ embed 2)
        step1 = +-mono-≤ step-x step-y

        step2 : (wx ÷ embed 2) + (wy ÷ embed 2) ≡ (wx + wy) ÷ embed 2
        step2 = begin
            (wx ÷ embed 2) + (wy ÷ embed 2)
          ≡⟨ sym (div-add wx wy) ⟩
            (wx + wy) ÷ embed 2
          ∎

        r-eq : (wx + wy) ÷ embed 2
             ≡ ((ux + uy) - (lx + ly)) ÷ embed 2
        r-eq = begin
            (wx + wy) ÷ embed 2
          ≡⟨ cong (λ z → z ÷ embed 2) (sym (sub-add ux uy lx ly)) ⟩
            ((ux + uy) - (lx + ly)) ÷ embed 2
          ∎

        T : ℚ
        T = ((ux + uy) - (lx + ly)) ÷ embed 2

        core : wx' + wy' ≤ T
        core = ≤-trans step1 (≤-trans (≤-reflexive step2) (≤-reflexive r-eq))

        l-eq : wx' + wy' ≡ (ux' + uy') - (lx' + ly')
        l-eq = begin
            wx' + wy'
          ≡⟨ sym (sub-add ux' uy' lx' ly') ⟩
            (ux' + uy') - (lx' + ly')
          ∎
      in
        subst (λ z → z ≤ T) l-eq core

------------------------------------------------------------------------
-- Negation
--
-- 取负

negℝ : RealI → RealI
RealI.l (negℝ x)    = neg (RealI.u x)
RealI.u (negℝ x)    = neg (RealI.l x)
RealI.lo (negℝ x)   = neg-antimono-< (RealI.lo x)
RealI.next (negℝ x) = negℝ (RealI.next x)
RealI.nest (negℝ x) = nest1 , nest2 , nest3
  where
    nest1 : neg (RealI.u x) ≤ neg (RealI.u (RealI.next x))
    nest1 = neg-antimono-≤ (proj₁ (proj₂ (RealI.nest x)))

    nest2 : neg (RealI.l (RealI.next x)) ≤ neg (RealI.l x)
    nest2 = neg-antimono-≤ (proj₁ (RealI.nest x))

    nest3 : neg (RealI.l (RealI.next x)) - neg (RealI.u (RealI.next x))
          ≤ (neg (RealI.l x) - neg (RealI.u x)) ÷ embed 2
    nest3 =
      let
        a  = RealI.l x;  b  = RealI.u x
        a' = RealI.l (RealI.next x); b' = RealI.u (RealI.next x)

        w-eq  : neg a  - neg b  ≡ b  - a
        w-eq  = neg-sub a b

        w'-eq : neg a' - neg b' ≡ b' - a'
        w'-eq = neg-sub a' b'

        inner : b' - a' ≤ (b - a) ÷ embed 2
        inner = proj₂ (proj₂ (RealI.nest x))

        target-eq : (neg a - neg b) ÷ embed 2 ≡ (b - a) ÷ embed 2
        target-eq = begin
            (neg a - neg b) ÷ embed 2
          ≡⟨ cong (λ z → z ÷ embed 2) w-eq ⟩
            (b - a) ÷ embed 2
          ∎
      in
        ≤-trans
          (≤-reflexive w'-eq)
          (≤-trans
            inner
            (≤-reflexive (sym target-eq)))

------------------------------------------------------------------------
-- Subtraction
--
-- 减法

infixl 6 _-ℝ_

_-ℝ_ : RealI → RealI → RealI
x -ℝ y = x +ℝ negℝ y
