------------------------------------------------------------------------
-- Continuity of multiplication on the interval reals
--
-- 区间实数上乘法的连续性
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module Real.Interval.ContinuityProd where

open import Data.Nat hiding (∣_-_∣)
  renaming (_+_ to _+ℕ_; _*_ to _*ℕ_; _≤_ to _≤ℕ_; _<_ to _<N_; _⊔_ to _⊔ℕ_)
open import Data.Nat.Properties as ℕP using
  (m≤m⊔n; m≤n⊔m; m≤n⇒m≤1+n; <-≤-trans; ^-monoʳ-≤)
  renaming (≤-trans to ≤ℕ-trans; ≤-refl to ≤ℕ-refl)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Rational using
  (ℚ; 0ℚ; 1ℚ; _+_; _-_; _*_; _≤_; _<_; ∣_∣; _⊔_) renaming (-_ to neg)
open import Data.Rational.Properties using
  (≤-trans; ≤-refl; ≤-reflexive; +-mono-≤; +-identityʳ; p≤p⊔q; p≤q⊔p; <⇒≤
  ; ∣-p∣≡∣p∣; *-distribʳ-+)
  renaming (<-≤-trans to <-≤ℚ-trans)
open import Relation.Binary.PropositionalEquality using
  (_≡_; sym; trans; cong; subst)

open import Base.RationalRing using (0≤1)
open import Real using (ε; ε-half; embed; embed-+-hom; embed-mono-≤; 0≤embed; 0<ε)
open import Real.IntervalEquiv using
  (l; u; width; node; recip2^t; bound-w; n<2^n; 1≤embed-suc)
open import Real.Interval using (RealI; δ)
open import Real.Interval.Continuity using (Close; ContinuousAt₂; Continuous₂)
open import Real.Interval.ContinuityMul using (sub-right-≤)
open import Real.Interval.ContinuityClose using
  (bounded; shift-abs; abs-diff-bounds; close-endpoint-bounds)
open import Real.Interval.ContinuityProdGap using
  (prod-node-bound; within; prod-gap-term; left-gap; right-gap)
open import Real.Interval.ContinuityProdBudget using
  (width-deep; 0<recip2^t; gap-budget; width-pos; term-width-le; gap-budget-rev
  ; recip2^t≤1; width-shift; mul-left-≤)
open import Real.Interval.Kit using (n≤2n)
open import Real.Interval.Mul using (_*ℝ_)
open import Real.Interval.Mul.Cong using (≤+1)
open import Real.Interval.Rational using (negsub)

------------------------------------------------------------------------
-- Symmetry of the absolute difference
--
-- 差的绝对值对称

-- The absolute difference is symmetric in its two arguments.
--
-- 差的绝对值关于两个参数对称。
abs-diff-sym : (p q : ℚ) → ∣ p - q ∣ ≡ ∣ q - p ∣
abs-diff-sym p q =
  let e : q - p ≡ neg (p - q)
      e = sym (negsub p q)
      h : ∣ q - p ∣ ≡ ∣ neg (p - q) ∣
      h = cong ∣_∣ e
      h2 : ∣ neg (p - q) ∣ ≡ ∣ p - q ∣
      h2 = ∣-p∣≡∣p∣ (p - q)
  in sym (trans h h2)

------------------------------------------------------------------------
-- The reversed orientation of the same identity
--
-- 同一恒等式的反向定向

-- The reversed orientation of the same identity.
--
-- 同一恒等式的反向定向。
abs-diff-flip : (p q : ℚ) → ∣ q - p ∣ ≡ ∣ p - q ∣
abs-diff-flip p q =
  let e1 : q - p ≡ neg (p - q)
      e1 = sym (negsub p q)
      e2 : ∣ q - p ∣ ≡ ∣ neg (p - q) ∣
      e2 = cong ∣_∣ e1
      e3 : ∣ neg (p - q) ∣ ≡ ∣ p - q ∣
      e3 = ∣-p∣≡∣p∣ (p - q)
  in trans e2 e3

------------------------------------------------------------------------
-- Pointwise absolute bound for the perturbed interval
--
-- 被扰动区间的逐点绝对界

-- A bound valid on one interval transfers to a nearby interval once
-- the endpoints are within d, at the price of one extra unit.
--
-- 一个区间上的界，在端点相差不超过 d 时，可转移到邻近区间，代价是
-- 多出一个单位。
abs-next :
  (x x' : RealI) (L : ℕ) (M₀ d : ℚ) →
  0ℚ ≤ M₀ → d ≤ 1ℚ →
  (∀ a → l x L ≤ a → a ≤ u x L → ∣ a ∣ ≤ M₀) →
  ∣ l x L - l x' L ∣ ≤ d →
  ∣ u x L - u x' L ∣ ≤ d →
  (∀ a → l x' L ≤ a → a ≤ u x' L → ∣ a ∣ ≤ M₀ + 1ℚ)
abs-next x x' L M₀ d 0≤M₀ d≤1 bx dlx dux a la au =
  let lx≤ux : l x L ≤ u x L
      lx≤ux = <⇒≤ (RealI.lo (node x L))

      bxl : ∣ l x L ∣ ≤ M₀
      bxl = bx (l x L) (≤-refl {l x L}) lx≤ux

      bxu : ∣ u x L ∣ ≤ M₀
      bxu = bx (u x L) lx≤ux (≤-refl {u x L})

      ll : l x L - d ≤ l x' L
      ll = proj₁ (abs-diff-bounds (l x L) (l x' L) d dlx)

      uu : u x' L ≤ u x L + d
      uu = proj₂ (abs-diff-bounds (u x L) (u x' L) d dux)

      h : ∣ a ∣ ≤ M₀ + d
      h = shift-abs M₀ d (l x L) (u x L) (l x' L) (u x' L) a bxl bxu ll uu la au

      h' : M₀ + d ≤ M₀ + 1ℚ
      h' = +-mono-≤ (≤-refl {M₀}) d≤1
  in ≤-trans h h'

------------------------------------------------------------------------
-- The node gap from absolute bounds at a single level
--
-- 单层绝对界给出的节点间隙

-- The node gap derived from pointwise absolute bounds at a single
-- level.
--
-- 单层上逐点绝对界给出的节点间隙。
prod-gap-abs :
  (x x' y y' : RealI) (d Mx My : ℚ) (n : ℕ) →
  0ℚ ≤ Mx → 0ℚ ≤ My →
  (∀ a → l x (2 *ℕ n) ≤ a → a ≤ u x (2 *ℕ n) → ∣ a ∣ ≤ Mx) →
  (∀ a → l x' (2 *ℕ n) ≤ a → a ≤ u x' (2 *ℕ n) → ∣ a ∣ ≤ Mx) →
  (∀ a → l y (2 *ℕ n) ≤ a → a ≤ u y (2 *ℕ n) → ∣ a ∣ ≤ My) →
  (∀ a → l y' (2 *ℕ n) ≤ a → a ≤ u y' (2 *ℕ n) → ∣ a ∣ ≤ My) →
  ∣ l x (2 *ℕ n) - l x' (2 *ℕ n) ∣ ≤ d →
  ∣ u x (2 *ℕ n) - u x' (2 *ℕ n) ∣ ≤ d →
  ∣ l y (2 *ℕ n) - l y' (2 *ℕ n) ∣ ≤ d →
  ∣ u y (2 *ℕ n) - u y' (2 *ℕ n) ∣ ≤ d →
  u (x *ℝ y) n ≤ l (x' *ℝ y') n + prod-gap-term Mx My d x y n
prod-gap-abs x x' y y' d Mx My n 0≤Mx 0≤My
  bx bx' by by' dlx dux dly duy =
  let lx≤ux : l x (2 *ℕ n) ≤ u x (2 *ℕ n)
      lx≤ux = <⇒≤ (RealI.lo (node x (2 *ℕ n)))
      lx'≤ux' : l x' (2 *ℕ n) ≤ u x' (2 *ℕ n)
      lx'≤ux' = <⇒≤ (RealI.lo (node x' (2 *ℕ n)))
      ly≤uy : l y (2 *ℕ n) ≤ u y (2 *ℕ n)
      ly≤uy = <⇒≤ (RealI.lo (node y (2 *ℕ n)))
      ly'≤uy' : l y' (2 *ℕ n) ≤ u y' (2 *ℕ n)
      ly'≤uy' = <⇒≤ (RealI.lo (node y' (2 *ℕ n)))

      lx≥ : neg Mx ≤ l x (2 *ℕ n)
      lx≥ = proj₁ (within (l x (2 *ℕ n)) Mx
              (bx (l x (2 *ℕ n)) (≤-refl {l x (2 *ℕ n)}) lx≤ux))
      ux≤ : u x (2 *ℕ n) ≤ Mx
      ux≤ = proj₂ (within (u x (2 *ℕ n)) Mx
              (bx (u x (2 *ℕ n)) lx≤ux (≤-refl {u x (2 *ℕ n)})))
      ly≥ : neg My ≤ l y (2 *ℕ n)
      ly≥ = proj₁ (within (l y (2 *ℕ n)) My
              (by (l y (2 *ℕ n)) (≤-refl {l y (2 *ℕ n)}) ly≤uy))
      uy≤ : u y (2 *ℕ n) ≤ My
      uy≤ = proj₂ (within (u y (2 *ℕ n)) My
              (by (u y (2 *ℕ n)) ly≤uy (≤-refl {u y (2 *ℕ n)})))
      lx'≥ : neg Mx ≤ l x' (2 *ℕ n)
      lx'≥ = proj₁ (within (l x' (2 *ℕ n)) Mx
               (bx' (l x' (2 *ℕ n)) (≤-refl {l x' (2 *ℕ n)}) lx'≤ux'))
      ux'≤ : u x' (2 *ℕ n) ≤ Mx
      ux'≤ = proj₂ (within (u x' (2 *ℕ n)) Mx
               (bx' (u x' (2 *ℕ n)) lx'≤ux' (≤-refl {u x' (2 *ℕ n)})))
      ly'≥ : neg My ≤ l y' (2 *ℕ n)
      ly'≥ = proj₁ (within (l y' (2 *ℕ n)) My
               (by' (l y' (2 *ℕ n)) (≤-refl {l y' (2 *ℕ n)}) ly'≤uy'))
      uy'≤ : u y' (2 *ℕ n) ≤ My
      uy'≤ = proj₂ (within (u y' (2 *ℕ n)) My
               (by' (u y' (2 *ℕ n)) ly'≤uy' (≤-refl {u y' (2 *ℕ n)})))
  in prod-node-bound x x' y y' n Mx My d d 0≤Mx 0≤My
       lx≥ ux≤ ly≥ uy≤ lx'≥ ux'≤ ly'≥ uy'≤
       lx≤ux ly≤uy lx'≤ux' ly'≤uy'
       dlx dux dly duy

------------------------------------------------------------------------
-- The two-variable modulus of multiplication
--
-- 乘法的二元模数

-- The reference modulus M and the dyadic scale N absorb both the
-- pointwise bounds and the initial widths of x and y. The ladder
-- k < j₀ < j₁ < j₂ halves three times, so ε k = 8 * ε j₂, which is
-- enough for the forward gap, the two copied shifts of the reversed
-- gap, and the dyadic correction δ n.
--
-- 参照模数 M 与二进尺度 N 同时吸收 x、y 的逐点界与初始宽度。连折
-- 三次的阶梯足以容纳正向间隙、反向间隙的两份平移与二进修正。
module MultiplicationModulus (x y : RealI) (k : ℕ) where

  -- Three-step ladder: each step halves the dyadic scale.
  --
  -- 三级阶梯：每一步把二进尺度折半。
  j₀ : ℕ
  j₀ = suc (2 *ℕ k)

  j₁ : ℕ
  j₁ = suc (2 *ℕ j₀)

  j₂ : ℕ
  j₂ = suc (2 *ℕ j₁)

  hk : ε j₀ + ε j₀ ≡ ε k
  hk = ε-half k

  h₀₁ : ε j₁ + ε j₁ ≡ ε j₀
  h₀₁ = ε-half j₀

  h₁₂ : ε j₂ + ε j₂ ≡ ε j₁
  h₁₂ = ε-half j₁

  -- The shallowest bound on x from `bounded`.
  --
  -- 由 `bounded` 得到的最浅层 x 界。
  Mx₀ : ℚ
  Mx₀ = proj₁ (bounded x)

  0≤Mx₀ : 0ℚ ≤ Mx₀
  0≤Mx₀ = proj₁ (proj₂ (bounded x))

  -- Every endpoint of x is bounded in absolute value by Mx₀.
  --
  -- x 的每个端点都被 Mx₀ 界住绝对值。
  bx : ∀ m a → l x m ≤ a → a ≤ u x m → ∣ a ∣ ≤ Mx₀
  bx = proj₂ (proj₂ (bounded x))

  -- The shallowest bound on y from `bounded`.
  --
  -- 由 `bounded` 得到的最浅层 y 界。
  My₀ : ℚ
  My₀ = proj₁ (bounded y)

  0≤My₀ : 0ℚ ≤ My₀
  0≤My₀ = proj₁ (proj₂ (bounded y))

  -- Every endpoint of y is bounded in absolute value by My₀.
  --
  -- y 的每个端点都被 My₀ 界住绝对值。
  by : ∀ m a → l y m ≤ a → a ≤ u y m → ∣ a ∣ ≤ My₀
  by = proj₂ (proj₂ (bounded y))

  -- The relaxed endpoint bound for x, after the d-shift.
  --
  -- x 在 d 平移后放宽的端点界。
  Mx : ℚ
  Mx = Mx₀ + 1ℚ

  0≤Mx : 0ℚ ≤ Mx
  0≤Mx = +-mono-≤ 0≤Mx₀ 0≤1

  -- The relaxed endpoint bound for y, after the d-shift.
  --
  -- y 在 d 平移后放宽的端点界。
  My : ℚ
  My = My₀ + 1ℚ

  0≤My : 0ℚ ≤ My
  0≤My = +-mono-≤ 0≤My₀ 0≤1

  -- The joint reference modulus.
  --
  -- 联合参照模数。
  A : ℚ
  A = Mx ⊔ My

  Mx≤A : Mx ≤ A
  Mx≤A = p≤p⊔q Mx My

  My≤A : My ≤ A
  My≤A = p≤q⊔p Mx My

  0≤A : 0ℚ ≤ A
  0≤A = ≤-trans 0≤Mx Mx≤A

  -- The initial width of x.
  --
  -- x 的初始宽度。
  Wx : ℚ
  Wx = width x 0

  -- The initial width of y.
  --
  -- y 的初始宽度。
  Wy : ℚ
  Wy = width y 0

  0≤Wx : 0ℚ ≤ Wx
  0≤Wx = <⇒≤ (width-pos x 0)

  0≤Wy : 0ℚ ≤ Wy
  0≤Wy = <⇒≤ (width-pos y 0)

  -- The initial width of x, with one extra unit.
  --
  -- x 的初始宽度加一。
  Rx : ℚ
  Rx = Wx + 1ℚ

  -- The initial width of y, with one extra unit.
  --
  -- y 的初始宽度加一。
  Ry : ℚ
  Ry = Wy + 1ℚ

  0≤Rx : 0ℚ ≤ Rx
  0≤Rx = +-mono-≤ 0≤Wx 0≤1

  0≤Ry : 0ℚ ≤ Ry
  0≤Ry = +-mono-≤ 0≤Wy 0≤1

  -- The joint reference width.
  --
  -- 联合参照宽度。
  R : ℚ
  R = Rx ⊔ Ry

  0≤R : 0ℚ ≤ R
  0≤R = ≤-trans 0≤Rx (p≤p⊔q Rx Ry)

  -- The consolidated reference bound.
  --
  -- 综合参照界。
  C : ℚ
  C = (A ⊔ R) ⊔ embed 4

  0≤C : 0ℚ ≤ C
  0≤C = ≤-trans (≤-trans 0≤A (p≤p⊔q A R)) (p≤p⊔q (A ⊔ R) (embed 4))

  mb : ℕ
  mb = proj₁ (bound-w C 0≤C)

  C≤emb : C ≤ embed mb
  C≤emb = proj₂ (bound-w C 0≤C)

  -- The smallest embed level dominating C.
  --
  -- 支配 C 的最小 embed 层级。
  N₀ : ℕ
  N₀ = suc mb

  C≤N₀ : C ≤ embed N₀
  C≤N₀ = ≤-trans C≤emb (embed-mono-≤ (m≤n⇒m≤1+n (≤ℕ-refl {mb})))

  A≤C : A ≤ C
  A≤C = ≤-trans (p≤p⊔q A R) (p≤p⊔q (A ⊔ R) (embed 4))

  R≤C : R ≤ C
  R≤C = ≤-trans (p≤q⊔p A R) (p≤p⊔q (A ⊔ R) (embed 4))

  A≤e : A ≤ embed N₀
  A≤e = ≤-trans A≤C C≤N₀

  Mx≤e : Mx ≤ embed N₀
  Mx≤e = ≤-trans Mx≤A A≤e

  My≤e : My ≤ embed N₀
  My≤e = ≤-trans My≤A A≤e

  Rx≤C : Rx ≤ C
  Rx≤C = ≤-trans (p≤p⊔q Rx Ry) R≤C

  Ry≤C : Ry ≤ C
  Ry≤C = ≤-trans (p≤q⊔p Rx Ry) R≤C

  Wx≤e : Wx ≤ embed N₀
  Wx≤e = ≤-trans (≤-trans (≤+1 Wx) Rx≤C) C≤N₀

  Wy≤e : Wy ≤ embed N₀
  Wy≤e = ≤-trans (≤-trans (≤+1 Wy) Ry≤C) C≤N₀

  -- The embed of N₀, used as the reference modulus in bounds.
  --
  -- N₀ 的 embed，用作界中的参照模数。
  e : ℚ
  e = embed N₀

  1≤e : 1ℚ ≤ e
  1≤e = 1≤embed-suc mb

  -- The triple level, absorbing both the modulus and the widths.
  --
  -- 吸收模数与宽度的三倍层级。
  N : ℕ
  N = (N₀ +ℕ N₀) +ℕ N₀

  embN : embed N ≡ (e + e) + e
  embN = trans (embed-+-hom (N₀ +ℕ N₀) N₀)
           (cong (_+ e) (embed-+-hom N₀ N₀))

  e≤ee : e ≤ e + e
  e≤ee = ≤-trans (≤-reflexive (sym (+-identityʳ e)))
           (+-mono-≤ (≤-refl {e}) (0≤embed N₀))

  ee≤eee : e + e ≤ (e + e) + e
  ee≤eee = ≤-trans (≤-reflexive (sym (+-identityʳ (e + e))))
             (+-mono-≤ (≤-refl {e + e}) (0≤embed N₀))

  ee≤eN : e + e ≤ embed N
  ee≤eN = ≤-trans ee≤eee (≤-reflexive (sym embN))

  e≤eN : e ≤ embed N
  e≤eN = ≤-trans e≤ee ee≤eN

  Mx≤eN : Mx ≤ embed N
  Mx≤eN = ≤-trans Mx≤e e≤eN

  My≤eN : My ≤ embed N
  My≤eN = ≤-trans My≤e e≤eN

  AA≤ee : A + A ≤ e + e
  AA≤ee = +-mono-≤ A≤e A≤e

  MxMy≤ee : Mx + My ≤ e + e
  MxMy≤ee = ≤-trans (+-mono-≤ Mx≤A My≤A) AA≤ee

  MxMy≤eN : Mx + My ≤ embed N
  MxMy≤eN = ≤-trans MxMy≤ee ee≤eN

  -- The final dyadic depth, chosen so that its reciprocal dominates
  -- every product-gap term.
  --
  -- 最终的二进深度，其倒数支配所有乘积间隙项。
  T : ℕ
  T = suc (N *ℕ suc j₂)

  -- The final radius.
  --
  -- 最终半径。
  d : ℚ
  d = recip2^t T

  0<d : 0ℚ < d
  0<d = 0<recip2^t T

  0≤d : 0ℚ ≤ d
  0≤d = <⇒≤ 0<d

  d≤1 : d ≤ 1ℚ
  d≤1 = recip2^t≤1 T

  Pb : ℕ
  Pb = N *ℕ suc j₂

  hT : Pb <N 2 ^ T
  hT = <-≤-trans (n<2^n Pb) (^-monoʳ-≤ 2 (m≤n⇒m≤1+n (≤ℕ-refl {Pb})))

  ----------------------------------------------------------------------
  -- Index bookkeeping
  --
  -- 索引簿记

  -- Given the two witness lower bounds from the Close hypotheses, pick
  -- a single node n that dominates both and the Cauchy budget Q.
  --
  -- 给定两条 Close 假设提供的见证下界，选一个同时支配二者与柯西预算
  -- Q 的节点 n。
  module ProdIndex (mₓ m_y : ℕ) where

    Q : ℕ
    Q = ((N *ℕ N) +ℕ (N *ℕ N)) *ℕ suc j₂

    Sb : ℕ
    Sb = Q ⊔ℕ (j₁ ⊔ℕ (mₓ ⊔ℕ m_y))

    n : ℕ
    n = suc Sb

    L : ℕ
    L = 2 *ℕ n

    Q≤Sb : Q ≤ℕ Sb
    Q≤Sb = m≤m⊔n Q (j₁ ⊔ℕ (mₓ ⊔ℕ m_y))

    Sb≤n : Sb ≤ℕ n
    Sb≤n = m≤n⇒m≤1+n (≤ℕ-refl {Sb})

    Q≤n : Q ≤ℕ n
    Q≤n = ≤ℕ-trans Q≤Sb Sb≤n

    j₁≤⊔ : j₁ ≤ℕ j₁ ⊔ℕ (mₓ ⊔ℕ m_y)
    j₁≤⊔ = m≤m⊔n j₁ (mₓ ⊔ℕ m_y)

    ⊔≤Sb : j₁ ⊔ℕ (mₓ ⊔ℕ m_y) ≤ℕ Sb
    ⊔≤Sb = m≤n⊔m Q (j₁ ⊔ℕ (mₓ ⊔ℕ m_y))

    j₁≤n : j₁ ≤ℕ n
    j₁≤n = ≤ℕ-trans (≤ℕ-trans j₁≤⊔ ⊔≤Sb) Sb≤n

    mₓ≤⊔ : mₓ ≤ℕ mₓ ⊔ℕ m_y
    mₓ≤⊔ = m≤m⊔n mₓ m_y

    ⊔≤j₁⊔ : mₓ ⊔ℕ m_y ≤ℕ j₁ ⊔ℕ (mₓ ⊔ℕ m_y)
    ⊔≤j₁⊔ = m≤n⊔m j₁ (mₓ ⊔ℕ m_y)

    mₓ≤Sb : mₓ ≤ℕ Sb
    mₓ≤Sb = ≤ℕ-trans (≤ℕ-trans mₓ≤⊔ ⊔≤j₁⊔) ⊔≤Sb

    mₓ≤n : mₓ ≤ℕ n
    mₓ≤n = ≤ℕ-trans mₓ≤Sb Sb≤n

    m_y≤⊔ : m_y ≤ℕ mₓ ⊔ℕ m_y
    m_y≤⊔ = m≤n⊔m mₓ m_y

    m_y≤Sb : m_y ≤ℕ Sb
    m_y≤Sb = ≤ℕ-trans (≤ℕ-trans m_y≤⊔ ⊔≤j₁⊔) ⊔≤Sb

    m_y≤n : m_y ≤ℕ n
    m_y≤n = ≤ℕ-trans m_y≤Sb Sb≤n

    n≤L : n ≤ℕ L
    n≤L = n≤2n n

    mₓ≤L : mₓ ≤ℕ L
    mₓ≤L = ≤ℕ-trans mₓ≤n n≤L

    m_y≤L : m_y ≤ℕ L
    m_y≤L = ≤ℕ-trans m_y≤n n≤L

    hW : Q <N 2 ^ L
    hW = <-≤-trans (n<2^n Q) (^-monoʳ-≤ 2 (≤ℕ-trans Q≤n n≤L))

  ----------------------------------------------------------------------
  -- The step function
  --
  -- step 函数

  -- For a pair (x', y') in the two Close neighbourhoods, the product
  -- gap is pushed below ε k.
  --
  -- 对两个 Close 邻域内的一对 (x', y')，乘积间隙被压到 ε k 之下。
  step : ∀ x' y' → Close d x x' → Close d y y' →
         Close (ε k) (x *ℝ y) (x' *ℝ y')
  step x' y' cx cy =
    ( (n , left-gap x x' y y' k n Gf bf fwd)
    , (n , right-gap x x' y y' k n G' bg₀ revGap) )
    where

      cxr : Σ ℕ (λ m → ∀ j → m ≤ℕ j →
        ∣ l x j - l x' j ∣ ≤ d × ∣ u x j - u x' j ∣ ≤ d)
      cxr = close-endpoint-bounds d x x' cx

      mₓ : ℕ
      mₓ = proj₁ cxr

      gₓ : ∀ j → mₓ ≤ℕ j →
        ∣ l x j - l x' j ∣ ≤ d × ∣ u x j - u x' j ∣ ≤ d
      gₓ = proj₂ cxr

      cyr : Σ ℕ (λ m → ∀ j → m ≤ℕ j →
        ∣ l y j - l y' j ∣ ≤ d × ∣ u y j - u y' j ∣ ≤ d)
      cyr = close-endpoint-bounds d y y' cy

      m_y : ℕ
      m_y = proj₁ cyr

      g_y : ∀ j → m_y ≤ℕ j →
        ∣ l y j - l y' j ∣ ≤ d × ∣ u y j - u y' j ∣ ≤ d
      g_y = proj₂ cyr

      open ProdIndex mₓ m_y

      0≤rL : 0ℚ ≤ recip2^t L
      0≤rL = <⇒≤ (0<recip2^t L)

      wxL : width x L ≤ embed N * recip2^t L
      wxL = ≤-trans (width-deep x N₀ L Wx≤e)
              (mul-left-≤ (recip2^t L) 0≤rL e≤eN)

      wyL : width y L ≤ embed N * recip2^t L
      wyL = ≤-trans (width-deep y N₀ L Wy≤e)
              (mul-left-≤ (recip2^t L) 0≤rL e≤eN)

      dlx : ∣ l x L - l x' L ∣ ≤ d
      dlx = proj₁ (gₓ L mₓ≤L)

      dux : ∣ u x L - u x' L ∣ ≤ d
      dux = proj₂ (gₓ L mₓ≤L)

      dly : ∣ l y L - l y' L ∣ ≤ d
      dly = proj₁ (g_y L m_y≤L)

      duy : ∣ u y L - u y' L ∣ ≤ d
      duy = proj₂ (g_y L m_y≤L)

      bxL : ∀ a → l x L ≤ a → a ≤ u x L → ∣ a ∣ ≤ Mx
      bxL = λ a la au → ≤-trans (bx L a la au) (≤+1 Mx₀)

      bxL' : ∀ a → l x' L ≤ a → a ≤ u x' L → ∣ a ∣ ≤ Mx
      bxL' = abs-next x x' L Mx₀ d 0≤Mx₀ d≤1 (bx L) dlx dux

      byL : ∀ a → l y L ≤ a → a ≤ u y L → ∣ a ∣ ≤ My
      byL = λ a la au → ≤-trans (by L a la au) (≤+1 My₀)

      byL' : ∀ a → l y' L ≤ a → a ≤ u y' L → ∣ a ∣ ≤ My
      byL' = abs-next y y' L My₀ d 0≤My₀ d≤1 (by L) dly duy

      Gf : ℚ
      Gf = prod-gap-term Mx My d x y n

      fwd : u (x *ℝ y) n ≤ l (x' *ℝ y') n + Gf
      fwd = prod-gap-abs x x' y y' d Mx My n 0≤Mx 0≤My
              bxL bxL' byL byL' dlx dux dly duy

      bf₀ : Gf + δ n < ε j₀
      bf₀ = gap-budget x y Mx My d N j₀ j₁ j₂ T n
              0≤d (≤-refl {d}) Mx≤eN My≤eN MxMy≤eN hT hW
              j₁≤n h₁₂ h₀₁ wyL wxL

      e₀≤ek : ε j₀ ≤ ε k
      e₀≤ek = ≤-trans (≤-reflexive (sym (+-identityʳ (ε j₀))))
                (≤-trans (+-mono-≤ (≤-refl {ε j₀}) (<⇒≤ (0<ε j₀)))
                  (≤-reflexive hk))

      bf : Gf + δ n < ε k
      bf = <-≤ℚ-trans bf₀ e₀≤ek

      E : ℚ
      E = (Mx + My) * (d + d)

      G' : ℚ
      G' = Gf + E

      bg₀ : G' + δ n < ε k
      bg₀ = gap-budget-rev x y Mx My d N k j₀ j₁ j₂ T n
              0≤d (≤-refl {d}) Mx≤eN My≤eN MxMy≤eN hT hW
              j₁≤n h₁₂ h₀₁ hk wyL wxL

      dlx' : ∣ l x' L - l x L ∣ ≤ d
      dlx' = subst (λ z → z ≤ d) (sym (abs-diff-flip (l x L) (l x' L))) dlx

      dux' : ∣ u x' L - u x L ∣ ≤ d
      dux' = subst (λ z → z ≤ d) (sym (abs-diff-flip (u x L) (u x' L))) dux

      dly' : ∣ l y' L - l y L ∣ ≤ d
      dly' = subst (λ z → z ≤ d) (sym (abs-diff-flip (l y L) (l y' L))) dly

      duy' : ∣ u y' L - u y L ∣ ≤ d
      duy' = subst (λ z → z ≤ d) (sym (abs-diff-flip (u y L) (u y' L))) duy

      rev₀ : u (x' *ℝ y') n ≤ l (x *ℝ y) n + prod-gap-term Mx My d x' y' n
      rev₀ = prod-gap-abs x' x y' y d Mx My n 0≤Mx 0≤My
               bxL' bxL byL' byL
               dlx' dux' dly' duy'

      shx : u x' L ≤ u x L + d
      shx = proj₂ (abs-diff-bounds (u x L) (u x' L) d dux)

      slx : l x L ≤ l x' L + d
      slx = sub-right-≤ (l x L) d (l x' L)
              (proj₁ (abs-diff-bounds (l x L) (l x' L) d dlx))

      wx' : u x' L - l x' L ≤ (u x L - l x L) + (d + d)
      wx' = width-shift (l x L) (u x L) (l x' L) (u x' L) d shx slx

      shy : u y' L ≤ u y L + d
      shy = proj₂ (abs-diff-bounds (u y L) (u y' L) d duy)

      sly : l y L ≤ l y' L + d
      sly = sub-right-≤ (l y L) d (l y' L)
              (proj₁ (abs-diff-bounds (l y L) (l y' L) d dly))

      wy' : u y' L - l y' L ≤ (u y L - l y L) + (d + d)
      wy' = width-shift (l y L) (u y L) (l y' L) (u y' L) d shy sly

      termLe : prod-gap-term Mx My d x' y' n
                 ≤ Gf + (Mx * (d + d) + My * (d + d))
      termLe = term-width-le Mx My d
                 (u x L - l x L) (u y L - l y L)
                 (u x' L - l x' L) (u y' L - l y' L)
                 0≤Mx 0≤My wx' wy'

      splitE : Gf + (Mx * (d + d) + My * (d + d)) ≡ G'
      splitE = cong (Gf +_) (sym (*-distribʳ-+ (d + d) Mx My))

      termLe' : prod-gap-term Mx My d x' y' n ≤ G'
      termLe' = ≤-trans termLe (≤-reflexive splitE)

      revGap : u (x' *ℝ y') n ≤ l (x *ℝ y) n + G'
      revGap = ≤-trans rev₀ (+-mono-≤ (≤-refl {l (x *ℝ y) n}) termLe')

------------------------------------------------------------------------
-- Pointwise joint continuity of multiplication
--
-- 乘法的逐点联合连续

-- Multiplication is jointly continuous at every pair of points.
--
-- 乘法在每个点对处联合连续。
continuous-*-at : (x y : RealI) → ContinuousAt₂ (λ a b → a *ℝ b) x y
continuous-*-at x y k = d , (0<d , step)
  where
    open MultiplicationModulus x y k

------------------------------------------------------------------------
-- Multiplication is continuous
--
-- 乘法连续

-- Multiplication is continuous on the interval reals.
--
-- 区间实数上乘法连续。
continuous-* : Continuous₂ (λ a b → a *ℝ b)
continuous-* x y = continuous-*-at x y
