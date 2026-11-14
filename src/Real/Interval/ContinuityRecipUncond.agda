------------------------------------------------------------------------
-- Unconditional continuity of the reciprocal at a positive point
--
-- 正点处倒数连续性的无条件版
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module Real.Interval.ContinuityRecipUncond where

open import Data.Nat using (ℕ) renaming (_+_ to _+ℕ_; _≤_ to _≤ℕ_)
open import Data.Nat.Properties using (m≤m+n; m≤n+m)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Rational using (ℚ; 0ℚ; _+_; _-_; -_; _*_; _⊓_; _<_; _≤_)
open import Data.Rational.Base using (NonNegative; nonNegative)
open import Data.Rational.Properties using
  (≤-trans; ≤-refl; <⇒≤; <-≤-trans; ≤-<-trans; +-comm; *-monoʳ-≤-nonNeg; p⊓q≤p
  ; p⊓q≤q)
open import Relation.Binary.PropositionalEquality using (sym; subst)

open import Real using (ε; half)
open import Real.IntervalEquiv using (l; l-mono)
open import Real.Interval using (RealI; δ)
open import Real.Interval.Arith using (0ℝ)
open import Real.Interval.Continuity using (Close; Close-self; close-mono)
open import Real.Interval.ContinuityClose using (close-endpoint-bounds)
open import Real.Interval.ContinuityMul using (addle-cancel-<; cancel-add-<)
open import Real.Interval.ContinuityRecipBasic using (l-near-lower; pos-meet)
open import Real.Interval.ContinuityRecipQuota using (half-mul-<)
open import Real.Interval.OrderLe using (sub-mono)
open import Real.Interval.ContinuityRecipBudget using (0<mul)
open import Real.Interval.ContinuityRecipDeep using (δ-add)
open import Real.Interval.ContinuityRecipAt using (recip-close-at)
open import Real.Interval.Kit using (0<half)
open import Real.Interval.Mul.Order using (u-dyadic-0)
open import Real.Interval.Order using (_<ℝ_)
open import Real.Interval.Rational using (pos-diff)
open import Real.Interval.Recip using (recipℝ)

------------------------------------------------------------------------
-- Choosing the working radius
--
-- 选取工作半径

-- The radius must be positive, strictly below the modulus of the
-- landed theorem (so that widening applies), and strictly below the
-- positivity margin (so that positivity transfers). Halving the
-- minimum of the two achieves all three at once.
--
-- 半径须为正、严格小于落点定理的模数（以便放宽），并严格小于正性
-- 余量（以便传递正性）。取二者下确界的一半即可同时满足。
pick-mod :
  (d₀ m : ℚ) (0d : 0ℚ < d₀) (0m : 0ℚ < m) →
  Σ ℚ (λ r → (0ℚ < r) × (r < d₀) × (r < m))
pick-mod d₀ m 0d 0m =
  let z = d₀ ⊓ m
      0z : 0ℚ < z
      0z = pos-meet d₀ m 0d 0m

      z≤d₀ : z ≤ d₀
      z≤d₀ = p⊓q≤p d₀ m

      z≤m : z ≤ m
      z≤m = p⊓q≤q d₀ m

      0half : NonNegative half
      0half = nonNegative (<⇒≤ 0<half)
  in z * half
   , 0<mul z half 0z 0<half
   , ≤-<-trans (*-monoʳ-≤-nonNeg half {{0half}} z≤d₀) (half-mul-< d₀ 0d)
   , ≤-<-trans (*-monoʳ-≤-nonNeg half {{0half}} z≤m) (half-mul-< m 0m)

------------------------------------------------------------------------
-- Positivity of a neighbour inside a small enough neighbourhood
--
-- 足够小的邻域内邻点的正性

-- At the level where the endpoint gaps hold and x already has passed
-- n₀, the lower endpoint of x' stays within r of the lower endpoint of
-- x, hence above c - r, while delta at that level is at most delta n₀.
-- A radius below c - delta n₀ closes the chain.
--
-- 在端点差成立且 x 已越过 n₀ 的层级上，x' 的下端点与 x 的下端点相距
-- 不超过 r，故高于 c - r；该层的 δ 不超过 δ n₀。半径小于 c - δ n₀
-- 即可合上这条链。
pos-of-close :
  (r : ℚ) (x x' : RealI) (0<x : 0ℝ <ℝ x) →
  r < l x (proj₁ 0<x) - δ (proj₁ 0<x) →
  Close r x x' → 0ℝ <ℝ x'
pos-of-close r x x' 0<x r<m cl =
  let n₀ = proj₁ 0<x
      c  = l x n₀

      δr<c : δ n₀ + r < c
      δr<c = subst (λ w → w < c) (+-comm r (δ n₀))
                     (addle-cancel-< r c (δ n₀) r<m)

      δ<c-r : δ n₀ < c - r
      δ<c-r = cancel-add-< (δ n₀) c r δr<c

      bd = close-endpoint-bounds r x x' cl
      q  = proj₁ bd
      hb = proj₂ bd
      k  = n₀ +ℕ q

      n₀k : n₀ ≤ℕ k
      n₀k = m≤m+n n₀ q

      qk : q ≤ℕ k
      qk = m≤n+m q n₀

      c≤lxk : c ≤ l x k
      c≤lxk = l-mono x n₀k

      lxk-r≤lx'k : l x k - r ≤ l x' k
      lxk-r≤lx'k = l-near-lower r x x' q (λ t qt → proj₁ (hb t qt)) k qk

      δk≤δn₀ : δ k ≤ δ n₀
      δk≤δn₀ = δ-add n₀ q

      δk<c-r : δ k < c - r
      δk<c-r = ≤-<-trans δk≤δn₀ δ<c-r

      c-r≤lxk-r : c - r ≤ l x k - r
      c-r≤lxk-r = sub-mono {a = c} {a' = l x k} {b = r} {b' = r} c≤lxk ≤-refl

      δk<lx'k : δ k < l x' k
      δk<lx'k = <-≤-trans δk<c-r (≤-trans c-r≤lxk-r lxk-r≤lx'k)
  in k , subst (λ z → z < l x' k) (sym (u-dyadic-0 k)) δk<lx'k

------------------------------------------------------------------------
-- The unconditional landing theorem
--
-- 无条件落点定理

-- The modulus is the working radius from pick-mod: it widens to the
-- modulus of recip-close-at and stays below the positivity margin.
--
-- 模数取 pick-mod 给出的工作半径：它可放宽到 recip-close-at 的模数，
-- 且保持在正性余量之下。
recip-close-at-uncond :
  (x : RealI) (0<x : 0ℝ <ℝ x) (k : ℕ) →
  Σ ℚ (λ d → (0ℚ < d) ×
    ∀ x' → Close d x x' →
      Σ (0ℝ <ℝ x') (λ 0<x' → Close (ε k) (recipℝ x 0<x) (recipℝ x' 0<x')))
recip-close-at-uncond x 0<x k =
  let at    = recip-close-at x 0<x k
      d₀    = proj₁ at
      0d₀   = proj₁ (proj₂ at)
      mod   = proj₂ (proj₂ at)

      n₀    = proj₁ 0<x
      c     = l x n₀
      δ<c   = subst (λ z → z < l x n₀) (u-dyadic-0 n₀) (proj₂ 0<x)
      margin = c - δ n₀
      0margin = pos-diff (δ n₀) c δ<c

      pick  = pick-mod d₀ margin 0d₀ 0margin
      r     = proj₁ pick
      0r    = proj₁ (proj₂ pick)
      r<d₀  = proj₁ (proj₂ (proj₂ pick))
      r<margin = proj₂ (proj₂ (proj₂ pick))
  in r , 0r , λ x' cl →
       let 0<x' = pos-of-close r x x' 0<x r<margin cl
           out  = mod x' 0<x' (close-mono r d₀ x x' r<d₀ cl)
       in 0<x' , out

------------------------------------------------------------------------
-- Sanity check: the neighbour may be the point itself
--
-- 自洽性检验：邻点可取原点自身

uncond-recover-pos :
  (x : RealI) (0<x : 0ℝ <ℝ x) (k : ℕ) → 0ℝ <ℝ x
uncond-recover-pos x 0<x k =
  let (d , 0d , f) = recip-close-at-uncond x 0<x k
      cl = Close-self d 0d x
  in proj₁ (f x cl)
