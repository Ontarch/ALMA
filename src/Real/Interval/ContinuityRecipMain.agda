------------------------------------------------------------------------
-- Assembly layer: samples, gaps, levels and close-recip
--
-- 装配层：采样、间隙、层级与 close-recip
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module Real.Interval.ContinuityRecipMain where

open import Data.Nat using (ℕ)
  renaming (_+_ to _+ℕ_; _*_ to _*ℕ_; _≥_ to _≥ℕ_; _≤_ to _≤ℕ_)
open import Data.Nat.Properties using (m≤m+n; m≤n+m)
  renaming (≤-trans to ≤ℕ-trans)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Rational using (ℚ; 0ℚ; 1ℚ; ∣_∣; _≤_; _<_; _-_; _+_; -_; _*_)
open import Data.Rational.Base using (NonZero; positive; nonNegative; 1/_; _÷_)
open import Data.Rational.Properties using
  (+-assoc; +-identityˡ; +-inverseʳ; +-mono-≤-<; <-dense; ∣p∣≡p∨∣p∣≡-p
  ; 0≤∣p∣; neg-distrib-+; <⇒≤; ≤-refl; ≤-trans; ≤-<-trans; +-mono-≤
  ; +-identityʳ; neg-antimono-≤; <-≤-trans; pos⇒nonZero; pos*pos⇒pos
  ; *-monoˡ-≤-nonNeg; *-identityʳ)
  renaming (+-comm to +ℚ-comm)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; sym; subst; cong; trans)

open import Base.RationalRing using (neg-involutive; neg-0)
open import Real using (CauchySeq; ε; half; embed)
open import Real.CauchyToInterval using
  (M; K; K≥k; μ≤M; centre-cauchy→realI; node-go)
open import Real.IntervalEquiv using
  (centre; u; l; node; width; centre-l; centre-u; realI→cauchy; μx-dom)
open import Real.Interval using (RealI; δ; δ-pos)
open import Real.Interval.Arith using (0ℝ)
open import Real.Interval.Continuity using (Close; sub-add-cancel)
open import Real.Interval.ContinuityMul using
  (u-sub-emb; l-add-emb; close-levels; sub-cancel-<; sub-left-<; cancel-add-<
  ; sub-left-≤)
open import Real.Interval.ContinuityClose using (close-endpoint-bounds)
open import Real.Interval.ContinuityProdGap using (within)
open import Real.Interval.ContinuityRecipBasic using
  (Bsq-index; recip-modulus-grow; gap-c; neg-sub; sub-add-right; add-left
  ; centre-gap-upper; centre-gap-lower; centre-cross-upper; centre-cross-lower
  ; width-near; u-shift-upper)
open import Real.Interval.ContinuityProdBudget using (width-pos)
open import Real.Interval.Kit using (half≤1)
open import Real.Interval.Mul using (sub-monoˡ)
open import Real.Interval.Order using (_<ℝ_)
open import Real.Interval.OrderLe using (sub-mono)
open import Real.Interval.OrderLaws using (width-dec)
open import Real.Interval.Recip using
  (recipCauchy; realI→posCauchy; recip-modulus; recipℝ; PosCauchy; recipcauchy-μ)

------------------------------------------------------------------------
-- Assembly of the reciprocal's continuity: first wiring
--
-- 倒数连续性的装配：第一批接线

-- The sampled reciprocal is Cauchy with an explicit modulus, so two
-- samples beyond μ k differ by less than ε k.
--
-- 采样倒数是柯西序列且有显式模数，故 μ k 之后的两点相差小于 ε k。
sample-close :
  (x : RealI) (0<x : 0ℝ <ℝ x) (k : ℕ) →
  ∀ t s →
  t ≥ℕ CauchySeq.μ (recipCauchy (realI→posCauchy x 0<x)) k →
  s ≥ℕ CauchySeq.μ (recipCauchy (realI→posCauchy x 0<x)) k →
  ∣ CauchySeq.f (recipCauchy (realI→posCauchy x 0<x)) t
  - CauchySeq.f (recipCauchy (realI→posCauchy x 0<x)) s ∣ < ε k
sample-close x 0<x k t s t≥ s≥ =
  CauchySeq.cauchy (recipCauchy (realI→posCauchy x 0<x)) k t s t≥ s≥

-- The centre of the reciprocal at level n is the sampled value at the
-- level M chooses. This is exported as an equality, which sidesteps
-- the unexported NonZero instance of the endpoint form.
--
-- 倒数第 n 层的中心就是 M 所选层上的采样值；这条以等式导出，绕开了
-- 端点形式里未导出的 NonZero 实例。
centre-recip :
  (x : RealI) (0<x : 0ℝ <ℝ x) (n : ℕ) →
  centre (recipℝ x 0<x) n
    ≡ CauchySeq.f (recipCauchy (realI→posCauchy x 0<x))
                  (M (recipCauchy (realI→posCauchy x 0<x)) n)
centre-recip x 0<x n = centre-cauchy→realI (recipCauchy (realI→posCauchy x 0<x)) n

------------------------------------------------------------------------
-- One level suffices once both endpoints are shifted correctly
--
-- 端点按正确形式平移后，单层即可给出邻域

-- The two hypotheses are exactly the right-hand sides of u-sub-emb and
-- l-add-emb, so the neighbourhood follows by rewriting alone: no
-- arithmetic and no reference to the internal NonZero instance is
-- involved. This is the geometric bridge from endpoint data to Close.
--
-- 两条前提正好是 u-sub-emb 与 l-add-emb 的右端，故邻域只需改写即可
-- 得到：既不涉及算术，也不涉及内部 NonZero 实例。这是从端点数据到
-- Close 的几何桥。
close-of-shifted :
  (e : ℚ) (A B : RealI) (m : ℕ) →
  u A m + δ m - e < l B m →
  u B m < l A m - δ m + e →
  Close e A B
close-of-shifted e A B m h₁ h₂ =
  ( m , subst (λ z → z < l B m) (sym (u-sub-emb A e m)) h₁ )
  , ( m , subst (λ z → u B m < z) (sym (l-add-emb A e m)) h₂ )

------------------------------------------------------------------------
-- Endpoint order at any level
--
-- 任意层上的端点次序

l≤u : (r : RealI) (n : ℕ) → l r n ≤ u r n
l≤u r n = <⇒≤ (RealI.lo (node r n))

------------------------------------------------------------------------
-- Adding a nonnegative term on the right never decreases the value
--
-- 右加非负数不减小原值

le-plus : (a c : ℚ) → 0ℚ ≤ c → a ≤ a + c
le-plus a c 0≤c =
  let h : 0ℚ + a ≤ c + a
      h = add-left 0ℚ c a 0≤c
      h' : a ≤ c + a
      h' = subst (λ z → z ≤ c + a) (+-identityˡ a) h
  in subst (λ z → a ≤ z) (+ℚ-comm c a) h'

------------------------------------------------------------------------
-- A neighbourhood moves the upper endpoints
--
-- 邻域给出上端点的一次迁移

u-move-of-close :
  (d : ℚ) (x x' : RealI) → Close d x x' →
  Σ ℕ (λ m → u x m ≤ u x' m + d)
u-move-of-close d x x' h =
  let m , w₁ , w₂ = close-levels d x x' h
      s₁ : u x m + δ m < l x' m + d
      s₁ = sub-cancel-< (u x m + δ m) (l x' m) d
             (subst (λ z → z < l x' m) (u-sub-emb x d m) w₁)
      c₁ : u x m < l x' m + d
      c₁ = ≤-<-trans (le-plus (u x m) (δ m) (<⇒≤ (δ-pos m))) s₁
      c₂ : l x' m + d ≤ u x' m + d
      c₂ = +-mono-≤ {x = l x' m} {y = u x' m} {u = d} {v = d} (l≤u x' m) ≤-refl
  in m , ≤-trans (<⇒≤ c₁) c₂

------------------------------------------------------------------------
-- Negation of a non-negative rational is non-positive
--
-- 非负有理数的相反数非正

neg-nonneg : (q : ℚ) → 0ℚ ≤ q → - q ≤ 0ℚ
neg-nonneg q 0≤q = subst (λ z → - q ≤ z) (sym neg-0) (neg-antimono-≤ 0≤q)

------------------------------------------------------------------------
-- The other side of the neighbourhood
--
-- 邻域另一侧

-- Here l-add-emb is used in the reverse direction: the right half of
-- Close puts u x' below l (x + emb d), whose value is l x - δ + d.
-- Since -δ ≤ 0, that is at most l x + d, and l x ≤ u x closes the step.
--
-- 此处 l-add-emb 反向使用：Close 的右半把 u x' 压到 l (x + emb d) 之
-- 下，其值为 l x - δ + d。因 -δ ≤ 0，它不超过 l x + d，再由 l x ≤ u x
-- 收口。
u-move-of-close' :
  (d : ℚ) (x x' : RealI) → Close d x x' →
  Σ ℕ (λ m → u x' m ≤ u x m + d)
u-move-of-close' d x x' h =
  let m , w₁ , w₂ = close-levels d x x' h
      H : u x' m < l x m + (- δ m) + d
      H = subst (λ z → u x' m < z) (l-add-emb x d m) w₂
      s : u x' m ≤ l x m + (- δ m) + d
      s = <⇒≤ H
      n₁ : l x m + (- δ m) ≤ l x m + 0ℚ
      n₁ = +-mono-≤ {x = l x m} {y = l x m} {u = - δ m} {v = 0ℚ}
              ≤-refl (neg-nonneg (δ m) (<⇒≤ (δ-pos m)))
      n₂ : l x m + (- δ m) ≤ l x m
      n₂ = subst (λ z → l x m + (- δ m) ≤ z) (+-identityʳ (l x m)) n₁
      t : l x m + (- δ m) + d ≤ l x m + d
      t = +-mono-≤ {x = l x m + (- δ m)} {y = l x m} {u = d} {v = d} n₂ ≤-refl
      u₀ : l x m + d ≤ u x m + d
      u₀ = +-mono-≤ {x = l x m} {y = u x m} {u = d} {v = d} (l≤u x m) ≤-refl
  in m , ≤-trans s (≤-trans t u₀)

------------------------------------------------------------------------
-- Upper endpoints are within d at every level past the witness
--
-- 越过见证层之后，每一层上上端点都相差不超过 d

u-gap-deep :
  (d : ℚ) (x x' : RealI) → Close d x x' →
  Σ ℕ (λ m → ∀ k → m ≤ℕ k →
    (u x k ≤ u x' k + d) × (u x' k ≤ u x k + d))
u-gap-deep d x x' h =
  let m , g = close-endpoint-bounds d x x' h
      b : ∀ k → m ≤ℕ k →
          (u x k ≤ u x' k + d) × (u x' k ≤ u x k + d)
      b k hk =
        let p = proj₂ (g k hk)
            w = within (u x k - u x' k) d p
            up : u x k ≤ u x' k + d
            up = sub-left-≤ (u x k) (u x' k) d (proj₂ w)
            dn₀ : u x' k - d ≤ u x k
            dn₀ = neg-sub (u x k) (u x' k) d (proj₁ w)
            dn₁ : (u x' k - d) + d ≤ u x k + d
            dn₁ = +-mono-≤ {x = u x' k - d} {y = u x k} {u = d} {v = d} dn₀ ≤-refl
            dn : u x' k ≤ u x k + d
            dn = subst (λ z → z ≤ u x k + d) (sub-add-cancel (u x' k) d) dn₁
        in up , dn
  in m , b

------------------------------------------------------------------------
-- The centres of two neighbouring reals are within W + d
--
-- 相邻两实数的中心相距不超过 W + d

centre-gap-of-close :
  (d W : ℚ) (x x' : RealI) → Close d x x' →
  Σ ℕ (λ m → ∀ n → m ≤ℕ n → width x n ≤ W → width x' n ≤ W →
    (centre x n ≤ centre x' n + (W + d)) ×
    (centre x' n ≤ centre x n + (W + d)))
centre-gap-of-close d W x x' h =
  let m , g = u-gap-deep d x x' h
      b : ∀ n → m ≤ℕ n → width x n ≤ W → width x' n ≤ W →
          (centre x n ≤ centre x' n + (W + d)) ×
          (centre x' n ≤ centre x n + (W + d))
      b n hn wx wx' =
        centre-gap-upper d W x x' n (proj₁ (g n hn)) wx'
        , centre-gap-lower d W x x' n (proj₂ (g n hn)) wx
  in m , b

------------------------------------------------------------------------
-- The centre sits between the endpoints
--
-- 中心夹在两端之间

-- Two exported facts from IntervalEquiv, packaged as one pair so that
-- later endpoint estimates can charge one half-width per side.
--
-- IntervalEquiv 的两条导出事实，打包成一对，方便后续端点估计每侧记
-- 半宽。
centre-between : (r : RealI) (n : ℕ) →
  (l r n ≤ centre r n) × (centre r n ≤ u r n)
centre-between r n = centre-l r n , centre-u r n

------------------------------------------------------------------------
-- The sampled reciprocal is a literal 1/ term
--
-- 采样倒数是字面意义上的 1/ 项

-- The sampled value of the underlying positive sequence is positive.
--
-- 底层正序列在采样点的值为正。
pos-of-sample :
  (pc : PosCauchy) (t : ℕ) →
  0ℚ < CauchySeq.f (PosCauchy.seq pc) (PosCauchy.N₀ pc +ℕ t)
pos-of-sample pc t =
  <-≤-trans (PosCauchy.0<b pc)
            (PosCauchy.lower pc (PosCauchy.N₀ pc +ℕ t)
                             (m≤m+n (PosCauchy.N₀ pc) t))

-- The library writes the reciprocal as 1/ A with a dot-prefixed
-- instance, which cannot be passed explicitly. Going through inv makes
-- the NonZero argument an ordinary instance argument, so an explicit
-- proof can be handed over while the term stays the library's 1/ A.
--
-- 库中把倒数写成 1/ A，其实例参数带点号，无法显式传入。经 inv 转一
-- 道，非零参数变成普通实例参数，可显式交出一个证明，而项仍是库的
-- 1/ A。
inv : (A : ℚ) {{_ : NonZero A}} → ℚ
inv A = 1/ A

-- recipCauchy builds its sequence as h n = 1/ (g n), where g n reads
-- the sample of x at N₀ + n. Naming the sample therefore pins the
-- reciprocal's value as 1/ A with A a concrete rational, which is what
-- the gap estimate consumes.
--
-- recipCauchy 把序列建成 h n = 1/ (g n)，而 g n 读的是 x 在 N₀ + n 处
-- 的采样。故把采样写出来即可把倒数值钉成 1/ A，A 是具体有理数，正是
-- 差界估计所需的形状。
sample-form :
  (pc : PosCauchy) (t : ℕ) →
  CauchySeq.f (recipCauchy pc) t
    ≡ inv (CauchySeq.f (PosCauchy.seq pc) (PosCauchy.N₀ pc +ℕ t))
          {{pos⇒nonZero
              (CauchySeq.f (PosCauchy.seq pc) (PosCauchy.N₀ pc +ℕ t))
              {{positive (pos-of-sample pc t)}}}}
sample-form pc t = refl

------------------------------------------------------------------------
-- The reciprocal samples differ by the reduced gap estimate
--
-- 两个倒数采样值之差由降分母后的估计控制

-- The sampled value of a positive Cauchy sequence.
--
-- 正柯西序列的采样值。
sample-of : (pc : PosCauchy) (t : ℕ) → ℚ
sample-of pc t = CauchySeq.f (PosCauchy.seq pc) (PosCauchy.N₀ pc +ℕ t)

-- gap-c asks for the two values, a common positive lower bound c, the
-- positivity of both, and a bound W on the difference read as B + -A.
-- Here the values are the samples of the two reciprocals, written
-- through inv so the NonZero proofs can be handed over; A * B is then
-- charged against c * c, and the whole estimate is monotone in W.
--
-- gap-c 需要两个值、一个公共正下界 c、两者正性，以及把差写成
-- B + -A 后的界 W。此处两个值即两个倒数的采样，经 inv 写出以便交出
-- 非零证明；乘积 A * B 再由 c * c 承担，整个估计对 W 单调。
sample-gap :
  (pcx pcx' : PosCauchy) (t s : ℕ) (c W : ℚ) (0c : 0ℚ < c)
  (0A : 0ℚ < sample-of pcx t) (0B : 0ℚ < sample-of pcx' s) →
  c ≤ sample-of pcx t → c ≤ sample-of pcx' s →
  ∣ sample-of pcx' s + (- sample-of pcx t) ∣ ≤ W →
  ∣ inv (sample-of pcx t) {{pos⇒nonZero (sample-of pcx t) {{positive 0A}}}}
  - inv (sample-of pcx' s) {{pos⇒nonZero (sample-of pcx' s) {{positive 0B}}}} ∣
    ≤ W * inv (c * c)
            {{pos⇒nonZero (c * c)
                {{pos*pos⇒pos c {{positive 0c}} c {{positive 0c}}}}}}
sample-gap pcx pcx' t s c W 0c 0A 0B c≤A c≤B hW =
  gap-c (sample-of pcx t) (sample-of pcx' s) c W 0A 0B 0c c≤A c≤B hW

------------------------------------------------------------------------
-- Endpoints of the reciprocal are the sampled value plus or minus δ
--
-- 倒数的端点等于采样值加减 δ

-- The sampled value that appears in the reciprocal's endpoint.
--
-- 倒数端点中出现的采样值。
sample-deep : (x : RealI) (0<x : 0ℝ <ℝ x) (n : ℕ) → ℚ
sample-deep x 0<x n =
  sample-of (realI→posCauchy x 0<x)
            (M (recipCauchy (realI→posCauchy x 0<x)) n)

-- The sampled value is positive.
--
-- 该采样值为正。
pos-deep : (x : RealI) (0<x : 0ℝ <ℝ x) (n : ℕ) →
  0ℚ < sample-deep x 0<x n
pos-deep x 0<x n =
  pos-of-sample (realI→posCauchy x 0<x)
                (M (recipCauchy (realI→posCauchy x 0<x)) n)

-- cauchy→realI x is definitionally go x 0 (the first step of
-- centre-cauchy→realI is ≡⟨⟩), and u (go x n) is definitionally
-- seq-f x (M x n) + δ n. Composing node-go with sample-form therefore
-- reads the endpoint as the library's 1/ term plus δ.
--
-- cauchy→realI x 在定义上就是 go x 0（centre-cauchy→realI 的首步即
-- ≡⟨⟩），而 u (go x n) 在定义上就是 seq-f x (M x n) + δ n。把 node-go
-- 与 sample-form 串起来，端点即库中 1/ 项加 δ。
u-recip :
  (x : RealI) (0<x : 0ℝ <ℝ x) (n : ℕ) →
  u (recipℝ x 0<x) n
    ≡ inv (sample-deep x 0<x n)
          {{pos⇒nonZero (sample-deep x 0<x n)
              {{positive (pos-deep x 0<x n)}}}}
      + δ n
u-recip x 0<x n =
  let pc = realI→posCauchy x 0<x
      t = M (recipCauchy pc) n
  in trans (cong RealI.u (node-go (recipCauchy pc) n))
           (cong (λ z → z + δ n) (sample-form pc t))

-- The negative side is identical with a minus sign.
--
-- 负侧同形换减号。
l-recip :
  (x : RealI) (0<x : 0ℝ <ℝ x) (n : ℕ) →
  l (recipℝ x 0<x) n
    ≡ inv (sample-deep x 0<x n)
          {{pos⇒nonZero (sample-deep x 0<x n)
              {{positive (pos-deep x 0<x n)}}}}
      - δ n
l-recip x 0<x n =
  let pc = realI→posCauchy x 0<x
      t = M (recipCauchy pc) n
  in trans (cong RealI.l (node-go (recipCauchy pc) n))
           (cong (λ z → z - δ n) (sample-form pc t))

------------------------------------------------------------------------
-- Dividing by two never widens
--
-- 除以二不放大

width÷2≤ : (w : ℚ) → 0ℚ ≤ w → w ÷ embed 2 ≤ w
width÷2≤ w 0≤w =
  let m : w * half ≤ w * 1ℚ
      m = *-monoˡ-≤-nonNeg w {{nonNegative 0≤w}} half≤1

      m₂ : w * half ≤ w
      m₂ = subst (λ z → w * half ≤ z) (*-identityʳ w) m
  in m₂

------------------------------------------------------------------------
-- The sampled level of the reciprocal lies past x's own modulus
--
-- 倒数的采样层已越过 x 自身的模数

sample-past :
  (x : RealI) (0<x : 0ℝ <ℝ x) (n : ℕ) →
  CauchySeq.μ (realI→cauchy x)
      (recip-modulus (l x (proj₁ 0<x))
                     (PosCauchy.0<b (realI→posCauchy x 0<x)) (K n))
    ≤ℕ proj₁ 0<x +ℕ M (recipCauchy (realI→posCauchy x 0<x)) n
sample-past x 0<x n =
  let pc = realI→posCauchy x 0<x
      n₀ = proj₁ 0<x
      h₁ : CauchySeq.μ (recipCauchy pc) (K n) ≤ℕ M (recipCauchy pc) n
      h₁ = μ≤M (recipCauchy pc) n

      h₂ : CauchySeq.μ (realI→cauchy x)
             (recip-modulus (l x n₀) (PosCauchy.0<b pc) (K n))
           ≤ℕ M (recipCauchy pc) n
      h₂ = subst (λ z → z ≤ℕ M (recipCauchy pc) n)
                 (recipcauchy-μ pc (K n)) h₁

      h₃ : M (recipCauchy pc) n ≤ℕ n₀ +ℕ M (recipCauchy pc) n
      h₃ = m≤n+m (M (recipCauchy pc) n) n₀
  in ≤ℕ-trans h₂ h₃

------------------------------------------------------------------------
-- The sampled value is within the precision it was sampled at
--
-- 采样值落在它被采样时的精度之内

sample-near :
  (x : RealI) (0<x : 0ℝ <ℝ x) (n k : ℕ) →
  CauchySeq.μ (realI→cauchy x)
      (recip-modulus (l x (proj₁ 0<x))
                     (PosCauchy.0<b (realI→posCauchy x 0<x)) (K n))
    ≤ℕ k →
  ∣ CauchySeq.f (realI→cauchy x)
      (proj₁ 0<x +ℕ M (recipCauchy (realI→posCauchy x 0<x)) n)
    - CauchySeq.f (realI→cauchy x) k ∣
    < ε (recip-modulus (l x (proj₁ 0<x))
                       (PosCauchy.0<b (realI→posCauchy x 0<x)) (K n))
sample-near x 0<x n k k≥μ =
  let pc = realI→posCauchy x 0<x
      η  = recip-modulus (l x (proj₁ 0<x)) (PosCauchy.0<b pc) (K n)
      j  = proj₁ 0<x +ℕ M (recipCauchy pc) n
      j≥μ : CauchySeq.μ (realI→cauchy x) η ≤ℕ j
      j≥μ = sample-past x 0<x n
  in CauchySeq.cauchy (realI→cauchy x) η j k j≥μ k≥μ

------------------------------------------------------------------------
-- Two sum-shaped endpoint gaps give the reciprocal neighbourhood
--
-- 两条和式端点间隙给出倒数的邻域

-- u-recip and l-recip read the endpoints of a reciprocal as inv A + δ
-- and inv B - δ. The hypotheses are stated in sum form ("left bracket
-- below right bracket plus e"), because the budget lemma produces
-- exactly that shape; sub-left-< moves the e back across the bracket
-- in one step, so no associativity chain is needed here.
--
-- u-recip 与 l-recip 把倒数端点读成 inv A + δ 与 inv B - δ。前提写成
-- 和式（"左括号低于右括号加 e"），因为预算引理正是产出该形状；
-- sub-left-< 一步把 e 挪回括号另一侧，故此处不需要结合律链。
close-recip :
  (x : RealI) (0<x : 0ℝ <ℝ x) (x' : RealI) (0<x' : 0ℝ <ℝ x') →
  (n : ℕ) (e : ℚ) →
  ( ( inv (sample-deep x 0<x n)
          {{pos⇒nonZero (sample-deep x 0<x n)
              {{positive (pos-deep x 0<x n)}}}}
      + δ n ) + δ n
    < ( inv (sample-deep x' 0<x' n)
          {{pos⇒nonZero (sample-deep x' 0<x' n)
              {{positive (pos-deep x' 0<x' n)}}}} - δ n ) + e ) →
  ( inv (sample-deep x' 0<x' n)
        {{pos⇒nonZero (sample-deep x' 0<x' n)
            {{positive (pos-deep x' 0<x' n)}}}}
      + δ n
    < ( inv (sample-deep x 0<x n)
          {{pos⇒nonZero (sample-deep x 0<x n)
              {{positive (pos-deep x 0<x n)}}}} - δ n ) - δ n + e ) →
  Close e (recipℝ x 0<x) (recipℝ x' 0<x')
close-recip x 0<x x' 0<x' n e h₁ h₂ =
  let A = recipℝ x 0<x
      B = recipℝ x' 0<x'
      s = δ n
      a = inv (sample-deep x 0<x n)
            {{pos⇒nonZero (sample-deep x 0<x n)
                {{positive (pos-deep x 0<x n)}}}}
      b = inv (sample-deep x' 0<x' n)
            {{pos⇒nonZero (sample-deep x' 0<x' n)
                {{positive (pos-deep x' 0<x' n)}}}}

      e₁ : u A n + s - e ≡ (a + s) + s - e
      e₁ = cong (λ z → z + s - e) (u-recip x 0<x n)

      e₂ : (a - s) - s + e ≡ l A n - s + e
      e₂ = cong (λ z → z - s + e) (sym (l-recip x 0<x n))

      g₁ : u A n + s - e < l B n
      g₁ = subst (λ z → z < l B n) (sym e₁)
                 (subst (λ z → (a + s) + s - e < z)
                        (sym (l-recip x' 0<x' n))
                        (sub-left-< ((a + s) + s) e (b - s)
                              (subst (λ z → (a + s) + s < z) (+ℚ-comm (b - s) e) h₁)))

      g₂ : u B n < l A n - s + e
      g₂ = subst (λ z → u B n < z) e₂
                 (subst (λ z → z < (a - s) - s + e)
                        (sym (u-recip x' 0<x' n)) h₂)
  in close-of-shifted e A B n g₁ g₂

------------------------------------------------------------------------
-- Scalar budget: a difference bound below e - 3δ yields the sum shape
--
-- 标量预算：差值界低于 e - 3δ 即给出和式形状

-- Swap the last two summands of a triple sum.
--
-- 交换三项之和的后两个加项。
swap : (p q r : ℚ) → (p + q) + r ≡ (p + r) + q
swap p q r = trans (+-assoc p q r)
                   (trans (cong (p +_) (+ℚ-comm q r)) (sym (+-assoc p r q)))

-- The forward direction of the sum-shaped gap.
--
-- 和式间隙的正方向。
gap-sum-left : (a b s e E : ℚ) → a - b ≤ E → E + ((s + s) + s) < e →
               (a + s) + s < (b - s) + e
gap-sum-left a b s e E le gap =
  let h1 : a ≤ b + E
      h1 = sub-left-≤ a b E le
      h2 : a + ((s + s) + s) ≤ (b + E) + ((s + s) + s)
      h2 = +-mono-≤ {a} {b + E} {((s + s) + s)} {((s + s) + s)} h1 ≤-refl
      h3 : (b + E) + ((s + s) + s) ≡ b + (E + ((s + s) + s))
      h3 = +-assoc b E ((s + s) + s)
      h4 : a + ((s + s) + s) ≤ b + (E + ((s + s) + s))
      h4 = subst (λ z → a + ((s + s) + s) ≤ z) h3 h2
      h5 : b + (E + ((s + s) + s)) < b + e
      h5 = +-mono-≤-< {b} {b} {E + ((s + s) + s)} {e} ≤-refl gap
      h6 : a + ((s + s) + s) < b + e
      h6 = ≤-<-trans h4 h5
      h7 : (a + (s + s)) + s < b + e
      h7 = subst (λ z → z < b + e) (sym (+-assoc a (s + s) s)) h6
      h8 : a + (s + s) < (b + e) - s
      h8 = cancel-add-< (a + (s + s)) (b + e) s h7
  in subst (λ z → z < (b - s) + e) (sym (+-assoc a s s))
           (subst (λ z → a + (s + s) < z) (sym (swap b (- s) e)) h8)

-- The backward direction of the sum-shaped gap.
--
-- 和式间隙的反方向。
gap-sum-right : (a b s e E : ℚ) → b - a ≤ E → E + ((s + s) + s) < e →
                b + s < ((a - s) - s) + e
gap-sum-right a b s e E le gap =
  let h1 : b ≤ a + E
      h1 = sub-left-≤ b a E le
      h2 : b + ((s + s) + s) ≤ (a + E) + ((s + s) + s)
      h2 = +-mono-≤ {b} {a + E} {((s + s) + s)} {((s + s) + s)} h1 ≤-refl
      h3 : (a + E) + ((s + s) + s) ≡ a + (E + ((s + s) + s))
      h3 = +-assoc a E ((s + s) + s)
      h4 : b + ((s + s) + s) ≤ a + (E + ((s + s) + s))
      h4 = subst (λ z → b + ((s + s) + s) ≤ z) h3 h2
      h5 : a + (E + ((s + s) + s)) < a + e
      h5 = +-mono-≤-< {a} {a} {E + ((s + s) + s)} {e} ≤-refl gap
      h6 : b + ((s + s) + s) < a + e
      h6 = ≤-<-trans h4 h5
      h7 : (b + (s + s)) + s < a + e
      h7 = subst (λ z → z < a + e) (sym (+-assoc b (s + s) s)) h6
      h8 : b + (s + s) < (a + e) - s
      h8 = cancel-add-< (b + (s + s)) (a + e) s h7
      h9 : (b + s) + s < (a + e) - s
      h9 = subst (λ z → z < (a + e) - s) (sym (+-assoc b s s)) h8
      h10 : b + s < ((a + e) - s) - s
      h10 = cancel-add-< (b + s) ((a + e) - s) s h9
      eqA : ((a + (- s)) + (- s)) + e ≡ ((a + (- s)) + e) + (- s)
      eqA = swap (a + (- s)) (- s) e
      eqB : ((a + (- s)) + e) + (- s) ≡ ((a + e) + (- s)) + (- s)
      eqB = cong (λ z → z + (- s)) (swap a (- s) e)
      eq : ((a + e) - s) - s ≡ ((a - s) - s) + e
      eq = sym (trans eqA eqB)
  in subst (λ z → b + s < z) eq h10

------------------------------------------------------------------------
-- The budget slack: pick e strictly between the gap and ε k
--
-- 预算余量：在间隙与 ε k 之间取 e

e-sel : (lo hi : ℚ) → lo < hi → Σ ℚ (λ e → lo < e × e < hi)
e-sel lo hi = <-dense {lo} {hi}

------------------------------------------------------------------------
-- A rational lies on both sides of its absolute value
--
-- 有理数落在自身绝对值的两侧

p≤∣p∣ : (p : ℚ) → p ≤ ∣ p ∣
p≤∣p∣ p with ∣p∣≡p∨∣p∣≡-p p
... | inj₁ eq = subst (λ z → p ≤ z) (sym eq) ≤-refl
... | inj₂ eq =
  let 0≤-p : 0ℚ ≤ - p
      0≤-p = subst (λ z → 0ℚ ≤ z) eq (0≤∣p∣ p)
      step : 0ℚ + p ≤ (- p) + p
      step = add-left 0ℚ (- p) p 0≤-p
      step' : p ≤ (- p) + p
      step' = subst (λ z → z ≤ (- p) + p) (+-identityˡ p) step
      q : (- p) + p ≡ 0ℚ
      q = trans (+ℚ-comm (- p) p) (+-inverseʳ p)
      p≤0 : p ≤ 0ℚ
      p≤0 = subst (λ z → p ≤ z) q step'
  in subst (λ z → p ≤ z) (sym eq) (≤-trans p≤0 0≤-p)

-p≤∣p∣ : (p : ℚ) → - p ≤ ∣ p ∣
-p≤∣p∣ p with ∣p∣≡p∨∣p∣≡-p p
... | inj₁ eq =
  let 0≤p : 0ℚ ≤ p
      0≤p = subst (λ z → 0ℚ ≤ z) eq (0≤∣p∣ p)
      step : 0ℚ + (- p) ≤ p + (- p)
      step = add-left 0ℚ p (- p) 0≤p
      step' : - p ≤ p + (- p)
      step' = subst (λ z → z ≤ p + (- p)) (+-identityˡ (- p)) step
      -p≤0 : - p ≤ 0ℚ
      -p≤0 = subst (λ z → - p ≤ z) (+-inverseʳ p) step'
  in subst (λ z → - p ≤ z) (sym eq) (≤-trans -p≤0 0≤p)
... | inj₂ eq = subst (λ z → - p ≤ z) (sym eq) ≤-refl

------------------------------------------------------------------------
-- The layer at which a reciprocal sample sits
--
-- 倒数采样所在的层

sample-level : (x : RealI) (0<x : 0ℝ <ℝ x) (n : ℕ) → ℕ
sample-level x 0<x n =
  proj₁ 0<x +ℕ M (recipCauchy (realI→posCauchy x 0<x)) n

-- The sampled value is the centre at that layer.
--
-- 采样值就是该层上的中心。
sample-deep-centre :
  (x : RealI) (0<x : 0ℝ <ℝ x) (n : ℕ) →
  sample-deep x 0<x n ≡ centre x (sample-level x 0<x n)
sample-deep-centre x 0<x n = refl

------------------------------------------------------------------------
-- The sampled level never falls below x's first positive level
--
-- 采样层不低于 x 的初始正层

sample-level-low :
  (x : RealI) (0<x : 0ℝ <ℝ x) (n : ℕ) →
  proj₁ 0<x ≤ℕ sample-level x 0<x n
sample-level-low x 0<x n =
  m≤m+n (proj₁ 0<x) (M (recipCauchy (realI→posCauchy x 0<x)) n)

------------------------------------------------------------------------
-- The sampled level is unbounded in the layer index
--
-- 采样层随层号无界

-- The recursion picks n := L * Bsq-index b 0<b, so that recip-modulus b
-- is at least L at precision K n (recip-modulus-grow), the sequence
-- modulus at that precision dominates the precision (μx-dom), and the
-- reciprocal's own M dominates that modulus (μ≤M) and hence the sample
-- level (sample-past).
--
-- 取 n := L * Bsq-index b 0<b，使得 recip-modulus b 在精度 K n 处至少
-- 达到 L（recip-modulus-grow），该精度下序列模数支配精度（μx-dom），
-- 而倒数自身的 M 支配该模数（μ≤M），从而支配采样层（sample-past）。
sample-level-unbounded :
  (x : RealI) (0<x : 0ℝ <ℝ x) (L : ℕ) →
  Σ ℕ (λ n → L ≤ℕ sample-level x 0<x n)
sample-level-unbounded x 0<x L =
  let pc = realI→posCauchy x 0<x
      b = l x (proj₁ 0<x)
      0b = PosCauchy.0<b pc
      n = L *ℕ Bsq-index b 0b

      h₁ : L ≤ℕ recip-modulus b 0b (K n)
      h₁ = recip-modulus-grow b 0b L (K n) (K≥k n)

      h₂ : recip-modulus b 0b (K n) ≤ℕ sample-level x 0<x n
      h₂ = ≤ℕ-trans (μx-dom x (recip-modulus b 0b (K n)))
                    (sample-past x 0<x n)
  in (n , ≤ℕ-trans h₁ h₂)

------------------------------------------------------------------------
-- Elementary order arithmetic for the two-sided estimate
--
-- 双侧估计所需的初等序算术

-- A sum of two nonnegatives is nonnegative.
--
-- 两个非负数之和非负。
0≤sum : (a b : ℚ) → 0ℚ ≤ a → 0ℚ ≤ b → 0ℚ ≤ a + b
0≤sum a b 0≤a 0≤b = ≤-trans 0≤a (le-plus a b 0≤b)

-- A two-sided bound gives an absolute bound.
--
-- 双侧界给出绝对值界。
abs-bound : (p W : ℚ) → - W ≤ p → p ≤ W → ∣ p ∣ ≤ W
abs-bound p W lo hi with ∣p∣≡p∨∣p∣≡-p p
... | inj₁ eq = subst (λ z → z ≤ W) (sym eq) hi
... | inj₂ eq =
  subst (λ z → z ≤ W) (sym eq)
        (subst (λ z → - p ≤ z) (neg-involutive W) (neg-antimono-≤ lo))

------------------------------------------------------------------------
-- The centre sampled at the reciprocal's layer moves by a bounded gap
--
-- 倒数层上的中心位移有明确上界

-- The sampled value of a reciprocal at layer n is the centre of x at
-- the level n₀ + M n (sample-deep-centre), so the cross level centre
-- estimate applies verbatim. The common level q is j + j', which is
-- past both sampled levels; x's width is bounded from level 0 (width
-- shrinks with depth), while x' must be past the level m at which the
-- close pair yields endpoint bounds, hence the hypothesis on j'. Each
-- side is stated separately: the two bounds have different shapes
-- (3W + 5d above, 3W + 3d below), and both are kept as the exact
-- expressions the cross level lemmas produce, so no distributivity is
-- needed here.
--
-- 倒数在 n 层上的采样值就是 x 在 n₀ + M n 层上的中心
-- （sample-deep-centre），故跨层中心估计可直接套用。公共层 q 取
-- j + j'，已越过两个采样层；x 的宽度由第 0 层控制（宽度随深度收缩），
-- 而 x' 需越过 close 对给出端点界的层 m，故对 j' 的假设。两侧分别
-- 陈述：两条界形状不同（上方 3W + 5d，下方 3W + 3d），都保留跨层引理
-- 所产生的精确表达式，故此处不需要分配律。
sample-sides :
  (d W : ℚ) (x : RealI) (0<x : 0ℝ <ℝ x) (x' : RealI) (0<x' : 0ℝ <ℝ x')
  (m n : ℕ) →
  (∀ t → m ≤ℕ t → ∣ l x t - l x' t ∣ ≤ d × ∣ u x t - u x' t ∣ ≤ d) →
  width x (sample-level x 0<x n) ≤ W →
  width x (sample-level x' 0<x' n) ≤ W →
  width x (sample-level x 0<x n +ℕ sample-level x' 0<x' n) ≤ W →
  0ℚ ≤ W → 0ℚ ≤ d →
  m ≤ℕ sample-level x' 0<x' n →
  ( centre x (sample-level x 0<x n)
      ≤ centre x' (sample-level x' 0<x' n)
        + ((W + (d + d)) + (((W + (d + d)) + d) + W)) )
  ×
  ( centre x' (sample-level x' 0<x' n)
      ≤ centre x (sample-level x 0<x n)
        + (W + ((W + d) + (W + (d + d)))) )
sample-sides d W x 0<x x' 0<x' m n hm hwj hwj' hwq 0≤W 0≤d mn =
  let j = sample-level x 0<x n
      j' = sample-level x' 0<x' n
      q = j +ℕ j'
      dd = d + d
      Wx' = W + dd

      j≤q : j ≤ℕ q
      j≤q = m≤m+n j j'

      j'≤q : j' ≤ℕ q
      j'≤q = m≤n+m j' j

      mq : m ≤ℕ q
      mq = ≤ℕ-trans mn j'≤q

      hxq : width x q ≤ W
      hxq = hwq

      hxj : width x j ≤ W
      hxj = hwj

      hx'q : width x' q ≤ Wx'
      hx'q = ≤-trans (width-near d x x' m hm q mq) (add-left (width x q) W dd hxq)

      hxj' : width x j' ≤ W
      hxj' = hwj'

      hx'j : width x' j' ≤ Wx'
      hx'j = ≤-trans (width-near d x x' m hm j' mn) (add-left (width x j') W dd hxj')

      hu : u x q ≤ u x' q + d
      hu = sub-left-≤ (u x q) (u x' q) d
             (proj₂ (within (u x q - u x' q) d (proj₂ (hm q mq))))

      hu' : u x' q ≤ u x q + d
      hu' = u-shift-upper d x x' m (λ t mt → proj₂ (hm t mt)) q mq
  in centre-cross-upper d W Wx' x x' j j' q j≤q j'≤q hxj hx'q hx'j hu
     , centre-cross-lower d W Wx' x x' j j' q j≤q j'≤q hxq hxj hx'j hu'

------------------------------------------------------------------------
-- Subtraction identities and the bounded gap of the sampled centres
--
-- 减法恒等式与采样中心的有界位移

sub-cancel-right : (a c : ℚ) → (a + c) - a ≡ c
sub-cancel-right a c =
  trans (sub-add-right a a c)
        (trans (cong (λ z → z + c) (+-inverseʳ a)) (+-identityˡ c))

neg-sub-eq : (a b : ℚ) → - (a - b) ≡ b - a
neg-sub-eq a b =
  trans (neg-distrib-+ a (- b))
        (trans (cong (λ z → (- a) + z) (neg-involutive b)) (+ℚ-comm (- a) b))

------------------------------------------------------------------------
-- The two one-sided bounds of sample-sides combine into one radius
--
-- sample-sides 的两条单侧界合成一个半径

-- The radius is taken as U + L, the sum of the two raw bound
-- expressions, so both sides are pushed into it by le-plus alone; no
-- distribution over W and d is needed at this stage. The lower bound
-- turns into the negative side through neg-sub-eq.
--
-- 半径取为 U + L，即两条原始界表达式之和，故只需 le-plus 即可把两侧
-- 都推入半径；此处尚不需要对 W 与 d 做分配。下界经 neg-sub-eq 转成
-- 负侧。
sample-gap-W :
  (d W : ℚ) (x : RealI) (0<x : 0ℝ <ℝ x) (x' : RealI) (0<x' : 0ℝ <ℝ x')
  (m n : ℕ) →
  (∀ t → m ≤ℕ t → ∣ l x t - l x' t ∣ ≤ d × ∣ u x t - u x' t ∣ ≤ d) →
  width x (sample-level x 0<x n) ≤ W →
  width x (sample-level x' 0<x' n) ≤ W →
  width x (sample-level x 0<x n +ℕ sample-level x' 0<x' n) ≤ W →
  0ℚ ≤ W → 0ℚ ≤ d →
  m ≤ℕ sample-level x' 0<x' n →
  ∣ centre x' (sample-level x' 0<x' n) + (- centre x (sample-level x 0<x n)) ∣
    ≤ ((W + (d + d)) + (((W + (d + d)) + d) + W))
      + (W + ((W + d) + (W + (d + d))))
sample-gap-W d W x 0<x x' 0<x' m n hm hwj hwj' hwq 0≤W 0≤d mn =
  let j = sample-level x 0<x n
      j' = sample-level x' 0<x' n
      dd = d + d
      Wx' = W + dd
      U = Wx' + ((Wx' + d) + W)
      Lb = W + ((W + d) + Wx')
      A = centre x j
      B = centre x' j'
      pp = B + (- A)

      0≤dd : 0ℚ ≤ dd
      0≤dd = 0≤sum d d 0≤d 0≤d

      0≤Wx' : 0ℚ ≤ Wx'
      0≤Wx' = 0≤sum W dd 0≤W 0≤dd

      0≤Wd : 0ℚ ≤ W + d
      0≤Wd = 0≤sum W d 0≤W 0≤d

      0≤Wx'd : 0ℚ ≤ Wx' + d
      0≤Wx'd = 0≤sum Wx' d 0≤Wx' 0≤d

      0≤Uw : 0ℚ ≤ (Wx' + d) + W
      0≤Uw = 0≤sum (Wx' + d) W 0≤Wx'd 0≤W

      0≤U : 0ℚ ≤ U
      0≤U = 0≤sum Wx' ((Wx' + d) + W) 0≤Wx' 0≤Uw

      0≤WdW : 0ℚ ≤ (W + d) + Wx'
      0≤WdW = 0≤sum (W + d) Wx' 0≤Wd 0≤Wx'

      0≤Lb : 0ℚ ≤ Lb
      0≤Lb = 0≤sum W ((W + d) + Wx') 0≤W 0≤WdW

      sides = sample-sides d W x 0<x x' 0<x' m n hm hwj hwj' hwq 0≤W 0≤d mn

      up : A ≤ B + U
      up = proj₁ sides

      lo : B ≤ A + Lb
      lo = proj₂ sides

      hAB : A + (- B) ≤ U
      hAB = subst (λ z → A + (- B) ≤ z) (sub-cancel-right B U)
                  (sub-mono {a = A} {a' = B + U} {b = B} {b' = B} up ≤-refl)

      hBA : B + (- A) ≤ Lb
      hBA = subst (λ z → B + (- A) ≤ z) (sub-cancel-right A Lb)
                  (sub-monoˡ {a = B} {b = A + Lb} {c = A} lo)

      hneg : - U ≤ B + (- A)
      hneg = subst (λ z → - U ≤ z) (neg-sub-eq A B) (neg-antimono-≤ hAB)

      hM : Lb ≤ U + Lb
      hM = subst (λ z → Lb ≤ z) (+ℚ-comm Lb U) (le-plus Lb U 0≤U)

      hUM : U ≤ U + Lb
      hUM = le-plus U Lb 0≤Lb

      hnegM : - (U + Lb) ≤ pp
      hnegM = ≤-trans (neg-antimono-≤ hUM) hneg

      hposM : pp ≤ U + Lb
      hposM = ≤-trans hBA hM
  in abs-bound pp (U + Lb) hnegM hposM

------------------------------------------------------------------------
-- The gap in the form gap-c consumes
--
-- gap-c 所需形式的位移界

-- sample-of pc t and sample-deep agree by definition: both unfold to
-- CauchySeq.f (PosCauchy.seq pc) (PosCauchy.N₀ pc + t), and for x the
-- sequence is centre x, so the sampled value is the centre at the
-- level n₀ + M n, exactly the level sample-level names.
--
-- sample-of pc t 与 sample-deep 定义一致：都展开成
-- CauchySeq.f (PosCauchy.seq pc) (PosCauchy.N₀ pc + t)，而对 x 序列即
-- centre x，故采样值即 n₀ + M n 层上的中心，正是 sample-level 所指的层。
sample-gap-deep :
  (d W : ℚ) (x : RealI) (0<x : 0ℝ <ℝ x) (x' : RealI) (0<x' : 0ℝ <ℝ x')
  (m n : ℕ) →
  (∀ t → m ≤ℕ t → ∣ l x t - l x' t ∣ ≤ d × ∣ u x t - u x' t ∣ ≤ d) →
  width x (sample-level x 0<x n) ≤ W →
  width x (sample-level x' 0<x' n) ≤ W →
  width x (sample-level x 0<x n +ℕ sample-level x' 0<x' n) ≤ W →
  0ℚ ≤ W → 0ℚ ≤ d →
  m ≤ℕ sample-level x' 0<x' n →
  ∣ sample-deep x' 0<x' n + (- sample-deep x 0<x n) ∣
    ≤ ((W + (d + d)) + (((W + (d + d)) + d) + W))
      + (W + ((W + d) + (W + (d + d))))
sample-gap-deep d W x 0<x x' 0<x' m n hm hwj hwj' hwq 0≤W 0≤d mn =
  sample-gap-W d W x 0<x x' 0<x' m n hm hwj hwj' hwq 0≤W 0≤d mn

------------------------------------------------------------------------
-- Opening one absolute bound into its two directions
--
-- 把一个绝对值界拆成两个方向

-- gap-c yields a single absolute bound on the difference of the two
-- reciprocals; gap-sum-left and gap-sum-right each want one direction,
-- and the reverse direction is the same bound with the sign flipped.
--
-- gap-c 给出两条倒数之差的绝对值界，而 gap-sum-left / gap-sum-right
-- 各要一个方向；反方向就是同一个界翻符号。
abs-two-sides : (a b E : ℚ) → ∣ a - b ∣ ≤ E → (a - b ≤ E) × (b - a ≤ E)
abs-two-sides a b E h =
  proj₂ (within (a - b) E h)
  , subst (λ z → z ≤ E) (neg-sub-eq a b)
          (subst (λ z → - (a - b) ≤ z) (neg-involutive E)
                 (neg-antimono-≤ (proj₁ (within (a - b) E h))))

------------------------------------------------------------------------
-- A radius that dominates all three sampled widths
--
-- 支配三条采样宽度的一个半径

-- The radius is the sum of the two deep widths. Both terms are
-- positive, so each summand dominates itself, and the common level
-- j + j' is deeper than j, hence its width is smaller by width-dec.
-- Since both sample levels grow with n, this radius tends to zero as
-- n grows: it is the only usable radius for the budget.
--
-- 半径取为两个深层宽度之和。两项均正，故各加项自己支配自己，公共层
-- j + j' 比 j 更深，故其宽度由 width-dec 更小。由于两个采样层都随 n
-- 增长，该半径随 n 趋于零：这是预算唯一可用的半径。
sample-radius :
  (x : RealI) (0<x : 0ℝ <ℝ x) (x' : RealI) (0<x' : 0ℝ <ℝ x') (n : ℕ) →
  ( width x (sample-level x 0<x n)
      ≤ width x (sample-level x 0<x n) + width x (sample-level x' 0<x' n) )
  ×
  ( width x (sample-level x' 0<x' n)
      ≤ width x (sample-level x 0<x n) + width x (sample-level x' 0<x' n) )
  ×
  ( width x (sample-level x 0<x n +ℕ sample-level x' 0<x' n)
      ≤ width x (sample-level x 0<x n) + width x (sample-level x' 0<x' n) )
sample-radius x 0<x x' 0<x' n =
  let j = sample-level x 0<x n
      j' = sample-level x' 0<x' n
      q = j +ℕ j'

      0≤wj : 0ℚ ≤ width x j
      0≤wj = <⇒≤ (width-pos x j)

      0≤wj' : 0ℚ ≤ width x j'
      0≤wj' = <⇒≤ (width-pos x j')

      h1 : width x j ≤ width x j + width x j'
      h1 = le-plus (width x j) (width x j') 0≤wj'

      h2 : width x j' ≤ width x j + width x j'
      h2 = subst (λ z → width x j' ≤ z) (+ℚ-comm (width x j') (width x j))
                 (le-plus (width x j') (width x j) 0≤wj)

      h3 : width x q ≤ width x j + width x j'
      h3 = ≤-trans (width-dec x {j} {q} (m≤m+n j j')) h1
  in h1 , h2 , h3
