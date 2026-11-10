------------------------------------------------------------------------
-- Countermodel against the sum law under the per-layer _⟶_ definition
--
-- 逐 centre 层 _⟶_ 定义下加法运算律的反模型
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module Real.Interval.Countermodel where

open import Data.Nat using (ℕ; zero; suc; z≤n)
open import Data.Product using (_,_)
open import Data.Rational using (ℚ; 0ℚ; _+_; _-_; _*_; _<_; _≤_; ∣_∣)
  renaming (-_ to neg)
open import Data.Rational.Base using (positive; _÷_; 1/_)
open import Data.Rational.Properties using
  (≤-refl; ≤-reflexive; ≤-trans; ≤-<-trans; <-trans; <-irrefl; +-mono-<
  ; +-mono-<-≤; +-inverseˡ; +-inverseʳ; +-identityˡ; +-identityʳ; +-assoc; +-comm
  ; neg-distrib-+; neg-antimono-<; 0≤p⇒∣p∣≡p; <⇒≤; positive⁻¹; pos*pos⇒pos
  ; +-mono-≤; *-assoc; *-comm; *-identityˡ; *-inverseʳ; pos⇒nonZero; *-zeroˡ)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; sym; trans; cong; cong₂; subst; subst₂)
open import Base.RationalRing using (neg-involutive; +interchange)
open import Relation.Nullary using (¬_)

open import Real using (ε; 0<ε; half; embed; 2ℚ)
open import Real.Interval using (RealI; Nest; pos-pow)
open import Real.IntervalEquiv using
  (centre; l; u; width; node; 0<width; centre-l; centre-u; l-mono; u-mono; width-step)
open import Real.Interval.Arith using (_+ℝ_)
open import Real.Interval.Complete using (_⟶_)
open import Real.Interval.Node using (centre-add)
open import Real.Interval.Rational using (cancel-plus)
open import Real.Interval.Kit using (two-half; 0≤half; add-self; *-mono-≤-nonNeg)
open import Real.Interval.Mul using (cancelʳ; cancel-z)

------------------------------------------------------------------------
-- This module constructs, for any RealI L and positive d, a sequence
-- converging to L whose layer-0 centre is shifted by d while every
-- deeper layer is unchanged. Taking d = ε 0 * half then refutes the
-- literal sum-limit goal at precision 0.
--
-- 本模块对任意 RealI L 与正的 d，构造一个收敛到 L 的序列，其第 0 层
-- 中心偏移 d，而所有更深层保持不变。取 d = ε 0 * half 即否证精度 0
-- 处字面的加法极限目标。

-- Prepending a wider root interval to an existing RealI tail.
--
-- 在已有 RealI 尾部之前前置一个更宽的根区间。
prepend :
  (l0 u0 : ℚ) (l0<u0 : l0 < u0) (tail : RealI) → Nest l0 u0 tail → RealI
prepend l0 u0 l0<u0 tail nest = record
  { l = l0; u = u0; lo = l0<u0; next = tail; nest = nest }

-- (c + d) - (w + d) ≡ c - w.
--
-- 共同的偏移 d 在差中抵消。
shift-cancel : ∀ c d w → (c + d) - (w + d) ≡ c - w
shift-cancel c d w =
  trans (cong₂ _-_ (+-comm c d) (+-comm w d))
        (cancel-plus d c w)

-- (q + W) - (q - W) ≡ W + W.
--
-- 对称展开后差为两份 W。
diff-double : ∀ q W → (q + W) - (q - W) ≡ W + W
diff-double q W =
  let step1 : neg (q - W) ≡ neg q + W
      step1 =
        trans (neg-distrib-+ q (neg W))
          (cong (neg q +_) (neg-involutive W))
      step2 : (q + W) - (q - W) ≡ (q + W) + (neg q + W)
      step2 = cong ((q + W) +_) step1
      inner : neg q + (q + W) ≡ W
      inner =
        trans (sym (+-assoc (neg q) q W))
          (trans (cong (λ z → z + W) (+-inverseˡ q))
            (+-identityˡ W))
      step3 : (q + W) + (neg q + W) ≡ W + W
      step3 =
        trans (sym (+-assoc (q + W) (neg q) W))
          (trans (cong (λ z → z + W) (+-comm (q + W) (neg q)))
            (cong (λ z → z + W) inner))
  in trans step2 step3

-- (W + W) ÷ embed 2 ≡ W.
--
-- 两份 W 除以 2 回到 W。
double-div2 : ∀ W → (W + W) ÷ embed 2 ≡ W
double-div2 W =
  let h = (1/ embed 2) {{pos⇒nonZero (embed 2) {{pos-pow 0}}}}
  in trans (cong (_÷ embed 2) (add-self W))
    (trans (*-assoc 2ℚ W h)
      (trans (cong (2ℚ *_) (*-comm W h))
        (trans (sym (*-assoc 2ℚ h W))
          (trans (cong (λ z → z * W)
                   (*-inverseʳ (embed 2) {{pos⇒nonZero (embed 2) {{pos-pow 0}}}}))
            (*-identityˡ W)))))

-- A RealI whose root is widened and whose centre at layer 0 is moved
-- to q; all deeper layers are exactly those of L.
--
-- 根区间加宽、第 0 层中心移到 q 的 RealI；所有更深层与 L 完全相同。
shifted : (L : RealI) (d : ℚ) → 0ℚ < d → RealI
shifted L d 0<d = prepend l0 u0 l0<u0 (node L 1) (n1 , n2 , n3)
  where
    q = centre L 0 + d
    W = width L 0 + d
    l0 = q - W
    u0 = q + W

    l0<u0 : l0 < u0
    l0<u0 =
      let w = width L 0
          raw : 0ℚ + w < d + w
          raw = +-mono-<-≤ 0<d ≤-refl
          step1 = subst (λ z → z < d + w) (+-identityˡ w) raw
          w<W : w < W
          w<W = subst (λ z → w < z) (+-comm d w) step1
          0<W : 0ℚ < W
          0<W = <-trans (0<width L) w<W
          negW<0 : neg W < 0ℚ
          negW<0 = neg-antimono-< 0<W
          negW<W : neg W < W
          negW<W = <-trans negW<0 0<W
          raw2 : neg W + q < W + q
          raw2 = +-mono-<-≤ negW<W ≤-refl
      in subst₂ (λ a b → a < b) (+-comm (neg W) q) (+-comm W q) raw2

    a = l L 0
    b = u L 0
    c = centre L 0
    w = width L 0

    a+w≡b : a + w ≡ b
    a+w≡b = trans (+-comm a w) (cancelʳ b a)

    n1old : l0 ≤ a
    n1old =
      let test : l0 ≡ (c + d) - (w + d)
          test = refl
          l0≡ : l0 ≡ c - w
          l0≡ = trans test (shift-cancel c d w)
          c≤a+w : c ≤ a + w
          c≤a+w = subst (λ z → c ≤ z) (sym a+w≡b) (centre-u L 0)
          step : c - w ≤ (a + w) - w
          step = +-mono-≤ c≤a+w (≤-refl {neg w})
          back : (a + w) - w ≡ a
          back = trans (cong (λ z → z - w) (+-comm a w)) (cancel-z w a)
          p1 : l0 ≤ c - w
          p1 = ≤-reflexive l0≡
          p2 : c - w ≤ a
          p2 = subst (λ z → c - w ≤ z) back step
      in ≤-trans p1 p2

    n1 : l0 ≤ l (node L 1) 0
    n1 = ≤-trans n1old (l-mono L {n = 0} {m = 1} (z≤n {1}))

    n2old : b ≤ u0
    n2old =
      let a≤c : a ≤ c
          a≤c = centre-l L 0
          bw≤cw : a + w ≤ c + w
          bw≤cw = +-mono-≤ a≤c (≤-refl {w})
          bw≤cw' : b ≤ c + w
          bw≤cw' = subst (λ z → z ≤ c + w) a+w≡b bw≤cw
          s2raw : (c + w) + 0ℚ ≤ (c + w) + d
          s2raw = +-mono-≤ (≤-refl {c + w}) (<⇒≤ 0<d)
          s2 : c + w ≤ c + (w + d)
          s2 = subst₂ (λ a b → a ≤ b) (+-identityʳ (c + w))
                       (+-assoc c w d) s2raw
          c<cd : 0ℚ + c < d + c
          c<cd = +-mono-<-≤ 0<d (≤-refl {c})
          c≤c+d : c ≤ c + d
          c≤c+d = <⇒≤ (subst₂ (λ a b → a < b) (+-identityˡ c) (+-comm d c) c<cd)
          s3 : c + (w + d) ≤ (c + d) + (w + d)
          s3 = +-mono-≤ c≤c+d (≤-refl {w + d})
          core2 : b ≤ u0
          core2 = ≤-trans bw≤cw' (≤-trans s2 s3)
      in core2

    n2 : u (node L 1) 0 ≤ u0
    n2 = ≤-trans (u-mono L {n = 0} {m = 1} (z≤n {1})) n2old

    n3old : w ≤ (u0 - l0) ÷ embed 2
    n3old =
      let diff≡ : u0 - l0 ≡ W + W
          diff≡ = diff-double q W
          div≡ : (W + W) ÷ embed 2 ≡ W
          div≡ = double-div2 W
          raw≤ : 0ℚ + w < d + w
          raw≤ = +-mono-<-≤ 0<d (≤-refl {w})
          s1 = subst (λ z → z < d + w) (+-identityˡ w) raw≤
          w≤W : w ≤ W
          w≤W = <⇒≤ (subst (λ z → w < z) (+-comm d w) s1)
          bridge : u0 - l0 ≡ (q + W) - (q - W)
          bridge = refl
          e : (u0 - l0) ÷ embed 2 ≡ W
          e = trans (cong (_÷ embed 2) (trans bridge diff≡)) div≡
          e' : W ≡ (u0 - l0) ÷ embed 2
          e' = sym e
      in subst (λ z → w ≤ z) e' w≤W

    half≤ : ∀ x → 0ℚ ≤ x → x ÷ embed 2 ≤ x
    half≤ x 0≤x =
      let
        0≤xh : 0ℚ ≤ x * half
        0≤xh = subst (λ z → z ≤ x * half) (*-zeroˡ half)
                (*-mono-≤-nonNeg (≤-refl {0ℚ}) 0≤x 0≤half (≤-refl {half}))
        p : x * half ≤ x * half + x * half
        p = ≤-trans (≤-reflexive (sym (+-identityʳ (x * half))))
                    (+-mono-≤ (≤-refl {x * half}) 0≤xh)
        q : x * half + x * half ≡ x
        q = two-half x
      in subst (λ z → x * half ≤ z) q p

    n3 : width (node L 1) 0 ≤ (u0 - l0) ÷ embed 2
    n3 =
      let w1≤w0 : width L 1 ≤ width L 0
          w1≤w0 = ≤-trans (width-step L)
                    (half≤ (width L 0) (<⇒≤ (0<width L)))
      in ≤-trans w1≤w0 n3old

-- The average of two symmetric endpoints equals the centre.
--
-- 两个对称端点的平均值等于中心。
avg-sym : ∀ q W → ((q - W) + (q + W)) ÷ embed 2 ≡ q
avg-sym q W =
  let s : (q - W) + (q + W) ≡ q + q
      s =
        trans (+interchange q (neg W) q W)
          (trans (cong ((q + q) +_) (+-inverseˡ W))
            (+-identityʳ (q + q)))
  in trans (cong (_÷ embed 2) s) (double-div2 q)

-- The layer-0 centre of the shifted RealI is the shifted value.
--
-- 偏移后 RealI 的第 0 层中心恰为偏移值。
shifted-centre0 :
  ∀ L d (0<d : 0ℚ < d) → centre (shifted L d 0<d) 0 ≡ centre L 0 + d
shifted-centre0 L d 0<d = avg-sym (centre L 0 + d) (width L 0 + d)

-- From layer 1 onward the shifted RealI coincides with the tail of L.
--
-- 从第 1 层起，偏移 RealI 与 L 的尾部重合。
shifted-tail :
  ∀ L d (0<d : 0ℚ < d) → node (shifted L d 0<d) 1 ≡ RealI.next L
shifted-tail L d 0<d = refl

-- The constant sequence of shifted RealIs converges to L, provided
-- the shift stays below the layer-0 tolerance.
--
-- 只要偏移小于第 0 层容差，偏移 RealI 的常序列收敛到 L。
shifted-converges :
  ∀ L d (0<d : 0ℚ < d) (d<ε0 : d < ε 0) →
  (λ (_ : ℕ) → shifted L d 0<d) ⟶ L
shifted-converges L d 0<d d<ε0 k = 0 , λ n _ → goal k
  where
  s = shifted L d 0<d

  node-shift : (k' : ℕ) → node s (suc k') ≡ node L (suc k')
  node-shift zero    = shifted-tail L d 0<d
  node-shift (suc k') = cong RealI.next (node-shift k')

  -- The centre error at precision 0 is exactly d.
  --
  -- 精度 0 处中心误差恰为 d。
  goal0 : ∣ centre s 0 - centre L 0 ∣ < ε 0
  goal0 =
    let e0 : centre s 0 ≡ centre L 0 + d
        e0 = shifted-centre0 L d 0<d
        step1 : centre s 0 - centre L 0 ≡ (centre L 0 + d) - centre L 0
        step1 = cong (λ z → z - centre L 0) e0
        step2 : (centre L 0 + d) - centre L 0 ≡ d
        step2 = cancel-z (centre L 0) d
        diff : centre s 0 - centre L 0 ≡ d
        diff = trans step1 step2
        full : ∣ centre s 0 - centre L 0 ∣ ≡ d
        full = trans (cong ∣_∣ diff) (0≤p⇒∣p∣≡p (<⇒≤ 0<d))
    in ≤-<-trans (≤-reflexive full) d<ε0

  -- At positive depths the shifted and original tails agree, so the
  -- error is zero.
  --
  -- 正精度处尾部重合，误差为 0。
  goal+ : ∀ k' → ∣ centre s (suc k') - centre L (suc k') ∣ < ε (suc k')
  goal+ k' =
    let ce : centre s (suc k') ≡ centre L (suc k')
        ce = cong (λ r → (RealI.l r + RealI.u r) ÷ embed 2) (node-shift k')
        diff0 : centre s (suc k') - centre L (suc k') ≡ 0ℚ
        diff0 = trans (cong (λ z → z - centre L (suc k')) ce)
                      (+-inverseʳ (centre L (suc k')))
        abs0 : ∣ centre s (suc k') - centre L (suc k') ∣ ≡ 0ℚ
        abs0 = trans (cong ∣_∣ diff0) (0≤p⇒∣p∣≡p (≤-refl {0ℚ}))
    in subst (λ z → z < ε (suc k')) (sym abs0) (0<ε (suc k'))

  goal : ∀ k → ∣ centre s k - centre L k ∣ < ε k
  goal zero    = goal0
  goal (suc k') = goal+ k'

------------------------------------------------------------------------
-- The sum-limit goal at precision 0 fails: with the shift set to
-- ε 0 * half, the centre error of the sum equals ε 0, which is not
-- strictly below it.
--
-- 精度 0 处的加法极限目标失败：取 `ε 0 * half` 作为偏移时，和的
-- 中心误差恰等于该层容差，不严格小于它。

-- The shift amount: half of the layer-0 tolerance.
--
-- 偏移量：第 0 层容差的一半。
d0 : ℚ
d0 = ε 0 * half

-- The shift amount is positive.
--
-- 偏移量为正。
d0-pos : 0ℚ < d0
d0-pos = positive⁻¹ d0
  ⦃ pos*pos⇒pos (ε 0) half ⦃ positive (0<ε 0) ⦄ ⦄

sum-goal-fails :
  ∀ L → let f = shifted L d0 d0-pos
        in ¬ (∣ centre (f +ℝ f) 0 - centre (L +ℝ L) 0 ∣ < ε 0)
sum-goal-fails L lt =
  <-irrefl refl (subst (λ z → z < ε 0) final-eq lt)
  where
  f = shifted L d0 d0-pos
  c = centre L 0

  cf≡ : centre f 0 ≡ c + d0
  cf≡ = shifted-centre0 L d0 d0-pos

  eq1 : centre (f +ℝ f) 0 ≡ (c + d0) + (c + d0)
  eq1 = trans (centre-add f f 0) (cong₂ _+_ cf≡ cf≡)

  eq2 : centre (L +ℝ L) 0 ≡ c + c
  eq2 = centre-add L L 0

  expand-eq : (c + d0) + (c + d0) ≡ (c + c) + (d0 + d0)
  expand-eq = +interchange c d0 c d0

  step1 : (c + d0) + (c + d0) - (c + c) ≡
          (c + c) + (d0 + d0) - (c + c)
  step1 = cong (λ z → z - (c + c)) expand-eq

  step2 : (c + c) + (d0 + d0) - (c + c) ≡ d0 + d0
  step2 = cancel-z (c + c) (d0 + d0)

  diff-eq : (c + d0) + (c + d0) - (c + c) ≡ d0 + d0
  diff-eq = trans step1 step2

  diff : centre (f +ℝ f) 0 - centre (L +ℝ L) 0 ≡ d0 + d0
  diff = trans (cong₂ _-_ eq1 eq2) diff-eq

  0<d0d0 : 0ℚ < d0 + d0
  0<d0d0 =
    subst (λ z → z < d0 + d0) (sym (+-identityʳ 0ℚ))
          (+-mono-< d0-pos d0-pos)

  d0+d0-pos : 0ℚ ≤ d0 + d0
  d0+d0-pos = <⇒≤ 0<d0d0

  abs-d0d0 : ∣ d0 + d0 ∣ ≡ d0 + d0
  abs-d0d0 = 0≤p⇒∣p∣≡p d0+d0-pos

  d0+d0≡ε0 : d0 + d0 ≡ ε 0
  d0+d0≡ε0 = two-half (ε 0)

  final-eq :
    ∣ centre (f +ℝ f) 0 - centre (L +ℝ L) 0 ∣ ≡ ε 0
  final-eq = trans (cong ∣_∣ diff) (trans abs-d0d0 d0+d0≡ε0)
