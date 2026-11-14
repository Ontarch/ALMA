------------------------------------------------------------------------
-- Node bounds, gap terms, and Close splitting for products
--
-- 乘积的节点界、间隙项与 Close 分解
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module Real.Interval.ContinuityProdGap where

open import Data.Nat using (ℕ) renaming (_+_ to _+ℕ_; _*_ to _*ℕ_; _≤_ to _≤ℕ_)
import Data.Nat.Properties as ℕP
open import Data.Product using (Σ; _,_; _×_; proj₁; proj₂)
open import Data.Rational using (ℚ; 0ℚ; _+_; _-_; _<_; _≤_; _*_; ∣_∣)
  renaming (-_ to neg)
open import Data.Rational.Properties using
  (≤-refl; ≤-trans; <⇒≤; neg-antimono-≤; +-mono-≤; +-monoʳ-<; +-assoc; +-comm
  ; ≤-<-trans)
open import Relation.Binary.PropositionalEquality using (_≡_; sym; cong; subst)

open import Base.RationalRing using (neg-involutive)
open import Real using (ε)
open import Real.IntervalEquiv using (node; l; u)
open import Real.Interval using (RealI; embedℚ; δ)
open import Real.Interval.Arith using (_+ℝ_; _-ℝ_)
open import Real.Interval.Continuity using (Close)
open import Real.Interval.ContinuityMul using
  (u-sub-emb; l-add-emb; shift-inside; cancel-add-<; sub-left-<; min4; max4
  ; width4; min4-shift; max-gap; sub-left-≤; prod-diff-one)
open import Real.Interval.ContinuityClose using (close-endpoint-bounds)
open import Real.Interval.Kit using (n≤2n)
open import Real.Interval.Mul using (_*ℝ_)
open import Real.Interval.Mul.Core using (abs-≤)
open import Real.Interval.Node using (node-*ℝ)
open import Real.Interval.Rational using (r≤|r|; -r≤|r|)

------------------------------------------------------------------------
-- The four corners at level n are the corners at level 2n
--
-- 第 n 层的四角就是第 2n 层的四角

-- The lower endpoint of a product at level n is the minimum of the
-- four corner products at level 2n.
--
-- 第 n 层乘积的下端点是第 2n 层四角乘积的最小值。
l-corners : (x y : RealI) (n : ℕ) →
  l (x *ℝ y) n
    ≡ min4 (l x (2 *ℕ n) * l y (2 *ℕ n))
           (l x (2 *ℕ n) * u y (2 *ℕ n))
           (u x (2 *ℕ n) * l y (2 *ℕ n))
           (u x (2 *ℕ n) * u y (2 *ℕ n))
l-corners x y n = cong RealI.l (node-*ℝ x y n)

-- The upper endpoint of a product at level n is the maximum of the
-- four corner products at level 2n.
--
-- 第 n 层乘积的上端点是第 2n 层四角乘积的最大值。
u-corners : (x y : RealI) (n : ℕ) →
  u (x *ℝ y) n
    ≡ max4 (l x (2 *ℕ n) * l y (2 *ℕ n))
           (l x (2 *ℕ n) * u y (2 *ℕ n))
           (u x (2 *ℕ n) * l y (2 *ℕ n))
           (u x (2 *ℕ n) * u y (2 *ℕ n))
u-corners x y n = cong RealI.u (node-*ℝ x y n)

------------------------------------------------------------------------
-- Product node gap
--
-- 乘积的节点间隙

-- At level n the gap between the products is controlled by the endpoint
-- gaps at level 2n plus the current widths at level 2n. No interior
-- comparison is needed: the corners only use endpoints.
--
-- 第 n 层的乘积间隙由第 2n 层的端点间隙与第 2n 层的宽度控制。不需要区间
-- 内部的比较：四角只涉及端点。
prod-node-bound :
  (x x' y y' : RealI) (n : ℕ) (Mx My d e : ℚ) →
  0ℚ ≤ Mx → 0ℚ ≤ My →
  neg Mx ≤ l x (2 *ℕ n) → u x (2 *ℕ n) ≤ Mx →
  neg My ≤ l y (2 *ℕ n) → u y (2 *ℕ n) ≤ My →
  neg Mx ≤ l x' (2 *ℕ n) → u x' (2 *ℕ n) ≤ Mx →
  neg My ≤ l y' (2 *ℕ n) → u y' (2 *ℕ n) ≤ My →
  l x (2 *ℕ n) ≤ u x (2 *ℕ n) → l y (2 *ℕ n) ≤ u y (2 *ℕ n) →
  l x' (2 *ℕ n) ≤ u x' (2 *ℕ n) → l y' (2 *ℕ n) ≤ u y' (2 *ℕ n) →
  ∣ l x (2 *ℕ n) - l x' (2 *ℕ n) ∣ ≤ d →
  ∣ u x (2 *ℕ n) - u x' (2 *ℕ n) ∣ ≤ d →
  ∣ l y (2 *ℕ n) - l y' (2 *ℕ n) ∣ ≤ e →
  ∣ u y (2 *ℕ n) - u y' (2 *ℕ n) ∣ ≤ e →
  u (x *ℝ y) n ≤ l (x' *ℝ y') n +
    ((Mx * e + d * My)
     + (Mx * (u y (2 *ℕ n) - l y (2 *ℕ n))
        + My * (u x (2 *ℕ n) - l x (2 *ℕ n))))
prod-node-bound x x' y y' n Mx My d e Mx≥0 My≥0
  lx≥ ux≤ ly≥ uy≤ lx'≥ ux'≤ ly'≥ uy'≤
  lx≤ux ly≤uy lx'≤ux' ly'≤uy'
  |lx-lx'|≤d |ux-ux'|≤d |ly-ly'|≤e |uy-uy'|≤e =
  let lx = l x (2 *ℕ n)
      ux = u x (2 *ℕ n)
      ly = l y (2 *ℕ n)
      uy = u y (2 *ℕ n)
      lx' = l x' (2 *ℕ n)
      ux' = u x' (2 *ℕ n)
      ly' = l y' (2 *ℕ n)
      uy' = u y' (2 *ℕ n)

      K = Mx * e + d * My
      B = Mx * (uy - ly) + My * (ux - lx)

      |lx|≤Mx : ∣ lx ∣ ≤ Mx
      |lx|≤Mx = abs-≤ lx≥ (≤-trans lx≤ux ux≤)

      |ux|≤Mx : ∣ ux ∣ ≤ Mx
      |ux|≤Mx = abs-≤ (≤-trans lx≥ lx≤ux) ux≤

      |ly'|≤My : ∣ ly' ∣ ≤ My
      |ly'|≤My = abs-≤ ly'≥ (≤-trans ly'≤uy' uy'≤)

      |uy'|≤My : ∣ uy' ∣ ≤ My
      |uy'|≤My = abs-≤ (≤-trans ly'≥ ly'≤uy') uy'≤

      pair : (a a' b b' : ℚ) → ∣ a ∣ ≤ Mx → ∣ b' ∣ ≤ My →
             ∣ a - a' ∣ ≤ d → ∣ b - b' ∣ ≤ e → a * b - a' * b' ≤ K
      pair a a' b b' |a|≤ |b'|≤ |a-a'|≤d' |b-b'|≤e' =
        prod-diff-one a a' b b' Mx My d e Mx≥0 My≥0
          |a|≤ |b'|≤ |a-a'|≤d' |b-b'|≤e'

      g11 : lx * ly - lx' * ly' ≤ K
      g11 = pair lx lx' ly ly' |lx|≤Mx |ly'|≤My |lx-lx'|≤d |ly-ly'|≤e

      g12 : lx * uy - lx' * uy' ≤ K
      g12 = pair lx lx' uy uy' |lx|≤Mx |uy'|≤My |lx-lx'|≤d |uy-uy'|≤e

      g21 : ux * ly - ux' * ly' ≤ K
      g21 = pair ux ux' ly ly' |ux|≤Mx |ly'|≤My |ux-ux'|≤d |ly-ly'|≤e

      g22 : ux * uy - ux' * uy' ≤ K
      g22 = pair ux ux' uy uy' |ux|≤Mx |uy'|≤My |ux-ux'|≤d |uy-uy'|≤e

      hK : min4 (lx * ly) (lx * uy) (ux * ly) (ux * uy)
             ≤ min4 (lx' * ly') (lx' * uy') (ux' * ly') (ux' * uy') + K
      hK = min4-shift (lx * ly) (lx * uy) (ux * ly) (ux * uy)
             (lx' * ly') (lx' * uy') (ux' * ly') (ux' * uy') K
             (sub-left-≤ (lx * ly) (lx' * ly') K g11)
             (sub-left-≤ (lx * uy) (lx' * uy') K g12)
             (sub-left-≤ (ux * ly) (ux' * ly') K g21)
             (sub-left-≤ (ux * uy) (ux' * uy') K g22)

      hB : max4 (lx * ly) (lx * uy) (ux * ly) (ux * uy)
             - min4 (lx * ly) (lx * uy) (ux * ly) (ux * uy) ≤ B
      hB = width4 Mx My lx ux ly uy Mx≥0 My≥0
             lx≥ ux≤ ly≥ uy≤ lx≤ux ly≤uy

      hmax : max4 (lx * ly) (lx * uy) (ux * ly) (ux * uy)
               ≤ min4 (lx' * ly') (lx' * uy') (ux' * ly') (ux' * uy') + (K + B)
      hmax = max-gap (lx * ly) (lx * uy) (ux * ly) (ux * uy)
               (lx' * ly') (lx' * uy') (ux' * ly') (ux' * uy') K B hK hB

      target = l (x' *ℝ y') n + ((Mx * e + d * My) + B)

      htarget : max4 (lx * ly) (lx * uy) (ux * ly) (ux * uy) ≤ target
      htarget = subst (λ z → max4 (lx * ly) (lx * uy) (ux * ly) (ux * uy) ≤ z)
                  (sym (cong (λ w → w + ((Mx * e + d * My) + B))
                             (l-corners x' y' n)))
                  hmax
  in subst (λ z → z ≤ target) (sym (u-corners x y n)) htarget

------------------------------------------------------------------------
-- Absolute bounds give two one-sided bounds
--
-- 绝对值界给出两个单侧界

-- A bound on the absolute value yields both one-sided bounds.
--
-- 绝对值界同时给出两个单侧界。
within : (a C : ℚ) → ∣ a ∣ ≤ C → (neg C ≤ a) × (a ≤ C)
within a C h =
  let lo0 : neg ∣ a ∣ ≤ a
      lo0 = subst (λ z → neg ∣ a ∣ ≤ z) (neg-involutive a)
              (neg-antimono-≤ (-r≤|r| a))
      lo : neg C ≤ a
      lo = ≤-trans (neg-antimono-≤ h) lo0
      hi : a ≤ C
      hi = ≤-trans (r≤|r| a) h
  in lo , hi

------------------------------------------------------------------------
-- The gap term
--
-- 间隙项

-- The gap term at level n: the endpoint-gap contribution K plus the
-- width contribution B taken at level 2n.
--
-- 第 n 层的间隙项：端点间隙贡献 K 加上第 2n 层的宽度贡献 B。
prod-gap-term : (Mx My d : ℚ) (x y : RealI) (n : ℕ) → ℚ
prod-gap-term Mx My d x y n =
  (Mx * d + d * My)
    + (Mx * (u y (2 *ℕ n) - l y (2 *ℕ n))
       + My * (u x (2 *ℕ n) - l x (2 *ℕ n)))

------------------------------------------------------------------------
-- The node gap with the endpoint data supplied by Close
--
-- 由 Close 提供端点数据的节点间隙

-- Choosing one node level n = mx + my makes the doubling harmless: the
-- endpoint bounds hold at level 2n because they hold at every level from
-- mx + my onwards.
--
-- 取节点层 n = mx + my，翻倍便无碍：端点界在 2n 层成立，因为它在
-- mx + my 之后的每一层都成立。
prod-node-gap-close :
  (x x' y y' : RealI) (d Mx My : ℚ) →
  0ℚ ≤ Mx → 0ℚ ≤ My →
  (∀ m a → l x m ≤ a → a ≤ u x m → ∣ a ∣ ≤ Mx) →
  (∀ m a → l x' m ≤ a → a ≤ u x' m → ∣ a ∣ ≤ Mx) →
  (∀ m a → l y m ≤ a → a ≤ u y m → ∣ a ∣ ≤ My) →
  (∀ m a → l y' m ≤ a → a ≤ u y' m → ∣ a ∣ ≤ My) →
  Close d x x' → Close d y y' →
  Σ ℕ (λ n → u (x *ℝ y) n ≤ l (x' *ℝ y') n + prod-gap-term Mx My d x y n)
prod-node-gap-close x x' y y' d Mx My Mx≥0 My≥0
  bx bx' by by' hx hy =
  let (mx , gx) = close-endpoint-bounds d x x' hx
      (my , gy) = close-endpoint-bounds d y y' hy
      n = mx +ℕ my

      mx≤n : mx ≤ℕ n
      mx≤n = ℕP.m≤m+n mx my

      my≤n : my ≤ℕ n
      my≤n = subst (λ z → my ≤ℕ z) (ℕP.+-comm my mx) (ℕP.m≤m+n my mx)

      mx≤2n : mx ≤ℕ 2 *ℕ n
      mx≤2n = ℕP.≤-trans mx≤n (n≤2n n)

      my≤2n : my ≤ℕ 2 *ℕ n
      my≤2n = ℕP.≤-trans my≤n (n≤2n n)

      lx≤ux : l x (2 *ℕ n) ≤ u x (2 *ℕ n)
      lx≤ux = <⇒≤ (RealI.lo (node x (2 *ℕ n)))

      lx'≤ux' : l x' (2 *ℕ n) ≤ u x' (2 *ℕ n)
      lx'≤ux' = <⇒≤ (RealI.lo (node x' (2 *ℕ n)))

      ly≤uy : l y (2 *ℕ n) ≤ u y (2 *ℕ n)
      ly≤uy = <⇒≤ (RealI.lo (node y (2 *ℕ n)))

      ly'≤uy' : l y' (2 *ℕ n) ≤ u y' (2 *ℕ n)
      ly'≤uy' = <⇒≤ (RealI.lo (node y' (2 *ℕ n)))

      lx≥ : neg Mx ≤ l x (2 *ℕ n)
      lx≥ = proj₁ (within (l x (2 *ℕ n)) Mx
                (bx (2 *ℕ n) (l x (2 *ℕ n)) (≤-refl {l x (2 *ℕ n)}) lx≤ux))

      ux≤ : u x (2 *ℕ n) ≤ Mx
      ux≤ = proj₂ (within (u x (2 *ℕ n)) Mx
                (bx (2 *ℕ n) (u x (2 *ℕ n)) lx≤ux (≤-refl {u x (2 *ℕ n)})))

      ly≥ : neg My ≤ l y (2 *ℕ n)
      ly≥ = proj₁ (within (l y (2 *ℕ n)) My
                (by (2 *ℕ n) (l y (2 *ℕ n)) (≤-refl {l y (2 *ℕ n)}) ly≤uy))

      uy≤ : u y (2 *ℕ n) ≤ My
      uy≤ = proj₂ (within (u y (2 *ℕ n)) My
                (by (2 *ℕ n) (u y (2 *ℕ n)) ly≤uy (≤-refl {u y (2 *ℕ n)})))

      lx'≥ : neg Mx ≤ l x' (2 *ℕ n)
      lx'≥ = proj₁ (within (l x' (2 *ℕ n)) Mx
                (bx' (2 *ℕ n) (l x' (2 *ℕ n)) (≤-refl {l x' (2 *ℕ n)}) lx'≤ux'))

      ux'≤ : u x' (2 *ℕ n) ≤ Mx
      ux'≤ = proj₂ (within (u x' (2 *ℕ n)) Mx
                (bx' (2 *ℕ n) (u x' (2 *ℕ n)) lx'≤ux' (≤-refl {u x' (2 *ℕ n)})))

      ly'≥ : neg My ≤ l y' (2 *ℕ n)
      ly'≥ = proj₁ (within (l y' (2 *ℕ n)) My
                (by' (2 *ℕ n) (l y' (2 *ℕ n)) (≤-refl {l y' (2 *ℕ n)}) ly'≤uy'))

      uy'≤ : u y' (2 *ℕ n) ≤ My
      uy'≤ = proj₂ (within (u y' (2 *ℕ n)) My
                (by' (2 *ℕ n) (u y' (2 *ℕ n)) ly'≤uy' (≤-refl {u y' (2 *ℕ n)})))

      dlx : ∣ l x (2 *ℕ n) - l x' (2 *ℕ n) ∣ ≤ d
      dlx = proj₁ (gx (2 *ℕ n) mx≤2n)

      dux : ∣ u x (2 *ℕ n) - u x' (2 *ℕ n) ∣ ≤ d
      dux = proj₂ (gx (2 *ℕ n) mx≤2n)

      dly : ∣ l y (2 *ℕ n) - l y' (2 *ℕ n) ∣ ≤ d
      dly = proj₁ (gy (2 *ℕ n) my≤2n)

      duy : ∣ u y (2 *ℕ n) - u y' (2 *ℕ n) ∣ ≤ d
      duy = proj₂ (gy (2 *ℕ n) my≤2n)

      body = prod-node-bound x x' y y' n Mx My d d Mx≥0 My≥0
               lx≥ ux≤ ly≥ uy≤ lx'≥ ux'≤ ly'≥ uy'≤
               lx≤ux ly≤uy lx'≤ux' ly'≤uy'
               dlx dux dly duy
  in n , body

------------------------------------------------------------------------
-- The same gap with a freely chosen node level
--
-- 同上，但节点层可自由选择

-- The same gap bound, with the node level supplied by the caller.
--
-- 同上间隙界，但节点层由调用者给出。
prod-node-gap-at :
  (x x' y y' : RealI) (d Mx My : ℚ) (n : ℕ) →
  0ℚ ≤ Mx → 0ℚ ≤ My →
  (∀ m a → l x m ≤ a → a ≤ u x m → ∣ a ∣ ≤ Mx) →
  (∀ m a → l x' m ≤ a → a ≤ u x' m → ∣ a ∣ ≤ Mx) →
  (∀ m a → l y m ≤ a → a ≤ u y m → ∣ a ∣ ≤ My) →
  (∀ m a → l y' m ≤ a → a ≤ u y' m → ∣ a ∣ ≤ My) →
  ∣ l x (2 *ℕ n) - l x' (2 *ℕ n) ∣ ≤ d →
  ∣ u x (2 *ℕ n) - u x' (2 *ℕ n) ∣ ≤ d →
  ∣ l y (2 *ℕ n) - l y' (2 *ℕ n) ∣ ≤ d →
  ∣ u y (2 *ℕ n) - u y' (2 *ℕ n) ∣ ≤ d →
  u (x *ℝ y) n ≤ l (x' *ℝ y') n + prod-gap-term Mx My d x y n
prod-node-gap-at x x' y y' d Mx My n Mx≥0 My≥0 bx bx' by by'
  dlx dux dly duy =
  let M = 2 *ℕ n
      lx≤ux : l x M ≤ u x M
      lx≤ux = <⇒≤ (RealI.lo (node x M))
      lx'≤ux' : l x' M ≤ u x' M
      lx'≤ux' = <⇒≤ (RealI.lo (node x' M))
      ly≤uy : l y M ≤ u y M
      ly≤uy = <⇒≤ (RealI.lo (node y M))
      ly'≤uy' : l y' M ≤ u y' M
      ly'≤uy' = <⇒≤ (RealI.lo (node y' M))
      lx≥ = proj₁ (within (l x M) Mx
             (bx M (l x M) (≤-refl {l x M}) lx≤ux))
      ux≤ = proj₂ (within (u x M) Mx
             (bx M (u x M) lx≤ux (≤-refl {u x M})))
      ly≥ = proj₁ (within (l y M) My
             (by M (l y M) (≤-refl {l y M}) ly≤uy))
      uy≤ = proj₂ (within (u y M) My
             (by M (u y M) ly≤uy (≤-refl {u y M})))
      lx'≥ = proj₁ (within (l x' M) Mx
              (bx' M (l x' M) (≤-refl {l x' M}) lx'≤ux'))
      ux'≤ = proj₂ (within (u x' M) Mx
              (bx' M (u x' M) lx'≤ux' (≤-refl {u x' M})))
      ly'≥ = proj₁ (within (l y' M) My
              (by' M (l y' M) (≤-refl {l y' M}) ly'≤uy'))
      uy'≤ = proj₂ (within (u y' M) My
              (by' M (u y' M) ly'≤uy' (≤-refl {u y' M})))
  in prod-node-bound x x' y y' n Mx My d d Mx≥0 My≥0
       lx≥ ux≤ ly≥ uy≤ lx'≥ ux'≤ ly'≥ uy'≤
       lx≤ux ly≤uy lx'≤ux' ly'≤uy'
       dlx dux dly duy

------------------------------------------------------------------------
-- Left half: the product minus the radius stays below
--
-- 左半：乘积减去半径仍在其下

-- Left half of the neighbourhood: subtracting the radius from the
-- product keeps it below the other product.
--
-- 邻域的左半：从乘积减去半径后仍落在另一乘积之下。
left-gap :
  (x x' y y' : RealI) (k n : ℕ) (G : ℚ) →
  G + δ n < ε k →
  u (x *ℝ y) n ≤ l (x' *ℝ y') n + G →
  u ((x *ℝ y) -ℝ embedℚ (ε k)) n < l (x' *ℝ y') n
left-gap x x' y y' k n G hg hgap =
  let uA = u (x *ℝ y) n
      lB = l (x' *ℝ y') n
      d = ε k
      dn = δ n

      add : uA + dn ≤ (lB + G) + dn
      add = +-mono-≤ hgap (≤-refl {dn})

      reassoc : (lB + G) + dn ≡ lB + (G + dn)
      reassoc = +-assoc lB G dn

      big : uA + dn < lB + d
      big = ≤-<-trans
              (subst (λ z → uA + dn ≤ z) reassoc add)
              (+-monoʳ-< lB hg)

      shifted : uA + dn < d + lB
      shifted = subst (λ z → uA + dn < z) (+-comm lB d) big

      body : (uA + dn) - d < lB
      body = sub-left-< (uA + dn) d lB shifted
  in subst (λ z → z < lB) (sym (u-sub-emb (x *ℝ y) (ε k) n)) body

------------------------------------------------------------------------
-- Right half: the perturbed product plus the radius stays below
--
-- 右半：扰动后的乘积加上半径仍在其下

-- Right half of the neighbourhood: adding the radius to the perturbed
-- product keeps it below the enlarged reference.
--
-- 邻域的右半：给扰动后的乘积加上半径后仍落在放大后的参照之下。
right-gap :
  (x x' y y' : RealI) (k n : ℕ) (G' : ℚ) →
  G' + δ n < ε k →
  u (x' *ℝ y') n ≤ l (x *ℝ y) n + G' →
  u (x' *ℝ y') n < l ((x *ℝ y) +ℝ embedℚ (ε k)) n
right-gap x x' y y' k n G' hg hgap =
  let uB = u (x' *ℝ y') n
      lA = l (x *ℝ y) n
      d = ε k
      dn = δ n

      add : uB + dn ≤ (lA + G') + dn
      add = +-mono-≤ hgap (≤-refl {dn})

      reassoc : (lA + G') + dn ≡ lA + (G' + dn)
      reassoc = +-assoc lA G' dn

      big : uB + dn < lA + d
      big = ≤-<-trans
              (subst (λ z → uB + dn ≤ z) reassoc add)
              (+-monoʳ-< lA hg)

      body : uB < (lA + d) - dn
      body = cancel-add-< uB (lA + d) dn big

      goal : uB < lA - dn + d
      goal = subst (λ z → uB < z) (sym (shift-inside lA d dn)) body
  in subst (λ z → uB < z) (sym (l-add-emb (x *ℝ y) (ε k) n)) goal
