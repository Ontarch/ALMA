------------------------------------------------------------------------
-- The landing theorem: from a gap bound to the two strict inequalities of close-recip
--
-- 落点定理：从间隙界落到 close-recip 的两条严格不等式
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module Real.Interval.ContinuityRecipAt where

open import Data.Nat using (ℕ; suc; zero; _∸_)
  renaming (_+_ to _+ℕ_; _≤_ to _≤ℕ_)
open import Data.Nat.Properties using (m≤m+n; m≤n+m; m≤n⇒m≤1+n)
  renaming (+-comm to +ℕ-comm; +-identityʳ to +ℕ-identityʳ; +-suc to +ℕ-suc
  ; ≤-trans to ≤ℕ-trans; ≤-refl to ≤ℕ-refl ; +-mono-≤ to +ℕ-mono-≤
  ; m∸n+n≡m to ∸-plus)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Rational using (ℚ; 0ℚ; ∣_∣; _≤_; _<_; _+_; _-_; _*_; -_)
open import Data.Rational.Base using (NonZero; Positive; positive; 1/_; nonNegative)
open import Data.Rational.Properties using
  (+-mono-<-≤; +-mono-≤; +-comm; ≤-refl; ≤-<-trans; ≤-trans; <⇒≤; <-trans
  ; +-mono-<; *-assoc; *-comm; *-identityʳ; *-inverseʳ ; *-monoˡ-≤-nonNeg
  ; *-monoʳ-≤-nonNeg ; pos⇒nonZero; pos*pos⇒pos; positive⁻¹)
open import Data.Rational.Solver using (module +-*-Solver)
open +-*-Solver
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; sym; trans; cong; subst)

open import Real using
  (ε; embed; half; CauchySeq; 0<ε; 0<embed; embed-suc-pos ; embed-mono-≤)
open import Real.CauchyToInterval using (M; M-mono)
open import Real.IntervalEquiv using
  (l; width; centre-l; l-mono; bound-w; 0<width; recip2^t)
open import Real.Interval using (RealI; δ; δ-pos)
open import Real.Interval.Arith using (0ℝ)
open import Real.Interval.Continuity using (Close)
open import Real.Interval.ContinuityMul using (sub-cancel-<)
open import Real.Interval.ContinuityProd using (abs-diff-flip)
open import Real.Interval.ContinuityProdGap using (within)
open import Real.Interval.ContinuityRecipBasic using
  (gap-c; close-abs; l-near-lower)
open import Real.Interval.ContinuityRecipBudget using
  (0<3; 0<inv; 0<mul; coef3; width-small)
open import Real.Interval.ContinuityRecipDeep using (deep-both)
open import Real.Interval.ContinuityRecipMain using
  (inv; sample-deep; pos-deep; sample-level; sample-level-low; close-recip
  ; sample-level-unbounded; sample-gap-deep)
open import Real.Interval.ContinuityRecipQuota using
  (acct; budget; d-min; half-sub; pick-q)
open import Real.Interval.Kit using (0<half; half≤1)
open import Real.Interval.Mul.Order using (u-dyadic-0)
open import Real.Interval.Order using (_<ℝ_)
open import Real.Interval.OrderLe using (sub-mono)
open import Real.Interval.OrderLaws using (width-dec)
open import Real.Interval.Recip using (recipℝ; recipCauchy; realI→posCauchy)

------------------------------------------------------------------------
-- Regrouping the subtracted side
--
-- 重排被减一侧

-- The regrouped form with the subtracted side exposed.
--
-- 把被减一侧展开后的重排形式。
group3 : (a b s : ℚ) →
  ((a + s) + s) - (b - s) ≡ (a - b) + ((s + s) + s)
group3 a b s =
  solve 3 (λ a b s → ((a :+ s) :+ s) :- (b :- s)
                    := (a :- b) :+ ((s :+ s) :+ s))
    refl a b s

-- The same regrouping with the roles of a and b exchanged.
--
-- 交换 a 与 b 的角色后的同一重排。
group3' : (a b s : ℚ) →
  (b + s) - ((a - s) - s) ≡ (b - a) + ((s + s) + s)
group3' a b s =
  solve 3 (λ a b s → (b :+ s) :- ((a :- s) :- s)
                    := (b :- a) :+ ((s :+ s) :+ s))
    refl a b s

------------------------------------------------------------------------
-- The two hypotheses of close-recip
--
-- close-recip 的两条前提

-- One gap bound feeds both sides: the upper half a - b <= r gives the
-- first hypothesis, the lower half read backwards as b - a <= r gives
-- the second.
--
-- 一个差界同时供给两侧：上半不等式给出第一条前提，下半反向即得第二条。
at-hyp :
  (a b s e r : ℚ) → ∣ a - b ∣ ≤ r → r + ((s + s) + s) < e →
  (((a + s) + s) < ((b - s) + e))
  × ((b + s) < (((a - s) - s) + e))
at-hyp a b s e r ab≤r r3<e =
  let ab≤ : a - b ≤ r
      ab≤ = proj₂ (within (a - b) r ab≤r)
      ba≤ : b - a ≤ r
      ba≤ = proj₂ (within (b - a) r
             (subst (λ z → z ≤ r) (sym (abs-diff-flip a b)) ab≤r))
      m1 : (a - b) + ((s + s) + s) ≤ r + ((s + s) + s)
      m1 = +-mono-≤ ab≤ ≤-refl
      l1 : (a - b) + ((s + s) + s) < e
      l1 = ≤-<-trans m1 r3<e
      s1 : ((a + s) + s) - (b - s) < e
      s1 = subst (λ z → z < e) (sym (group3 a b s)) l1
      h1 : (a + s) + s < (b - s) + e
      h1 = subst (λ z → (a + s) + s < z) (+-comm e (b - s))
             (sub-cancel-< ((a + s) + s) e (b - s) s1)
      m2 : (b - a) + ((s + s) + s) ≤ r + ((s + s) + s)
      m2 = +-mono-≤ ba≤ ≤-refl
      l2 : (b - a) + ((s + s) + s) < e
      l2 = ≤-<-trans m2 r3<e
      s2 : (b + s) - ((a - s) - s) < e
      s2 = subst (λ z → z < e) (sym (group3' a b s)) l2
      h2 : (b + s) < ((a - s) - s) + e
      h2 = subst (λ z → b + s < z) (+-comm e ((a - s) - s))
             (sub-cancel-< (b + s) e ((a - s) - s) s2)
  in h1 , h2

------------------------------------------------------------------------
-- Deepening a modulus never lowers it
--
-- 加深模数不会降低它

-- Adding any number of steps to the modulus argument never lowers the
-- result: M s n ≤ M s (n + k).
--
-- 在模数的参数上增加任意多步都不会降低结果：M s n ≤ M s (n + k)。
M-add : (s : CauchySeq) (n k : ℕ) → M s n ≤ℕ M s (n +ℕ k)
M-add s n zero =
  subst (λ z → M s n ≤ℕ M s z) (sym (+ℕ-identityʳ n)) ≤ℕ-refl
M-add s n (suc k) =
  ≤ℕ-trans (M-add s n k)
    (subst (λ z → M s (n +ℕ k) ≤ℕ M s z) (sym (+ℕ-suc n k)) (M-mono s (n +ℕ k)))

------------------------------------------------------------------------
-- The sampled level grows with the layer index
--
-- 采样层随层号增长

-- The sample level is monotone in the layer index.
--
-- 采样层关于层号单调。
sample-level-mono :
  (x : RealI) (0<x : 0ℝ <ℝ x) {n m : ℕ} → n ≤ℕ m →
  sample-level x 0<x n ≤ℕ sample-level x 0<x m
sample-level-mono x 0<x {n} {m} n≤m =
  let s = recipCauchy (realI→posCauchy x 0<x)
      h : M s n ≤ℕ M s m
      h = subst (λ z → M s n ≤ℕ M s z)
                (trans (+ℕ-comm n (m ∸ n)) (∸-plus n≤m))
                (M-add s n (m ∸ n))
  in +ℕ-mono-≤ ≤ℕ-refl h

------------------------------------------------------------------------
-- The eightfold coefficient is nonnegative
--
-- 八倍系数非负

-- The embedded 8 is nonnegative.
--
-- 嵌入的 8 非负。
0≤8 : 0ℚ ≤ embed 8
0≤8 = <⇒≤ (0<embed 7)

------------------------------------------------------------------------
-- The modulus of continuity of the reciprocal at a positive point
--
-- 正点处倒数的连续模数

-- At every positive point, the reciprocal carries a modulus of
-- continuity mapping Close d into Close (ε k).
--
-- 在每个正点处，倒数携带一个连续模数，把 Close d 映为 Close (ε k)。
recip-close-at :
  (x : RealI) (0<x : 0ℝ <ℝ x) (k : ℕ) →
  Σ ℚ (λ d → (0ℚ < d) ×
    ∀ x' → ∀ (0<x' : 0ℝ <ℝ x') → Close d x x' →
      Close (ε k) (recipℝ x 0<x) (recipℝ x' 0<x'))
recip-close-at x 0<x k =
  let n₀ = proj₁ 0<x
      c = l x n₀

      -- x is positive at level n₀, so its lower bound there is positive
      --
      -- x 在 n₀ 层已为正，故该层的下界为正
      δ<c : δ n₀ < c
      δ<c = subst (λ z → z < l x n₀) (u-dyadic-0 n₀) (proj₂ 0<x)
      0c : 0ℚ < c
      0c = <-trans (δ-pos n₀) δ<c
      0≤c : 0ℚ ≤ c
      0≤c = <⇒≤ 0c

      -- the retained lower bound and its half
      --
      -- 保留的下界与它的半
      c2 = c * half
      0c2 : 0ℚ < c2
      0c2 = 0<mul c half 0c 0<half
      cc = c2 * c2
      cc-pos : Positive cc
      cc-pos = pos*pos⇒pos c2 {{positive 0c2}} c2 {{positive 0c2}}
      nzcc : NonZero cc
      nzcc = pos⇒nonZero cc {{cc-pos}}
      0cc : 0ℚ < cc
      0cc = positive⁻¹ cc {{cc-pos}}
      invcc = 1/_ cc {{nzcc}}
      0≤inv : 0ℚ ≤ invcc
      0≤inv = <⇒≤ (0<inv cc 0cc)

      -- the quarter quota u
      --
      -- 三层额度：εk·ε9
      u = ε k * ε 9
      0u : 0ℚ < u
      0u = 0<mul (ε k) (ε 9) (0<ε k) (0<ε 9)

      -- the modulus, bounded by both c2²u and c2
      --
      -- 模数：同时受 c2²u 与 c2 约束
      dmed = d-min c u 0c 0u
      d₀ = proj₁ dmed
      0<d₀ = proj₁ (proj₂ dmed)
      d≤c2u = proj₁ (proj₂ (proj₂ dmed))
      d≤c2 = proj₂ (proj₂ (proj₂ dmed))

      -- a fixed natural bound for width x 0, raised twice
      --
      -- 宽度的固定界：width x 0 的自然上界再抬两层
      0≤width0 = <⇒≤ (0<width x)
      bw = bound-w (width x 0) 0≤width0
      M₀ = proj₁ bw
      w0≤ = proj₂ bw
      B = suc (suc M₀)
      w0≤B : width x 0 ≤ embed B
      w0≤B = ≤-trans w0≤ (embed-mono-≤ {M₀} {B}
                             (≤ℕ-trans (m≤n⇒m≤1+n (≤ℕ-refl {M₀}))
                                       (m≤n⇒m≤1+n (≤ℕ-refl {suc M₀}))))
      0≤B : 0ℚ ≤ embed B
      0≤B = <⇒≤ (positive⁻¹ (embed B) {{embed-suc-pos {suc M₀}}})

      -- the width quota W with N = suc M₀
      --
      -- 宽度额度 W = embed (suc N)·q，N = suc M₀
      pick = pick-q k c2 (suc M₀) 0c2
      q = proj₁ pick
      0<q = proj₁ (proj₂ pick)
      6W<u = proj₂ (proj₂ pick)
      W = embed (suc (suc M₀)) * q
      0<W : 0ℚ < W
      0<W = 0<mul (embed (suc (suc M₀))) q
              (positive⁻¹ (embed (suc (suc M₀))) {{embed-suc-pos {suc M₀}}}) 0<q

      -- the three-radius quota: u divided by the embedded three
      --
      -- 三层半径的额度：u 除以嵌入的三
      i3 = 1/_ (embed 3) {{pos⇒nonZero (embed 3) {{positive 0<3}}}}
      qδ = u * i3
      0qδ : 0ℚ < qδ
      0qδ = 0<mul u i3 0u (0<inv (embed 3) 0<3)
      e3q : embed 3 * qδ ≡ u
      e3q = trans (sym (*-assoc (embed 3) u i3))
              (trans (cong (_* i3) (*-comm (embed 3) u))
                (trans (*-assoc u (embed 3) i3)
                  (trans (cong (u *_) (*-inverseʳ (embed 3)
                                   {{pos⇒nonZero (embed 3) {{positive 0<3}}}}))
                         (*-identityʳ u))))

      -- one depth serving both smallness requirements
      --
      -- 同时满足尺度小与半径小的层
      deep = deep-both q qδ 0<q 0qδ
      tδ = proj₁ deep
      db = proj₂ deep
  in d₀ , 0<d₀ , (λ x' 0<x' cl →
    let cab = close-abs d₀ x x' cl
        m = proj₁ cab
        hb = proj₂ cab

        -- the sampled level must pass the close threshold, the dyadic
        -- threshold and the level needed by c2
        --
        -- 采样层要同时越过：close 的阈值、尺度阈值、c2 所需的层
        K₀ = n₀ +ℕ m
        L = tδ +ℕ (K₀ +ℕ m)
        n₁ = proj₁ (sample-level-unbounded x 0<x L)
        n₂ = proj₁ (sample-level-unbounded x' 0<x' L)
        nn = n₁ +ℕ n₂
        n = nn +ℕ tδ
        j = sample-level x 0<x n
        j' = sample-level x' 0<x' n

        m≤L : m ≤ℕ L
        m≤L = ≤ℕ-trans (m≤n+m m K₀) (m≤n+m (K₀ +ℕ m) tδ)
        K₀≤L : K₀ ≤ℕ L
        K₀≤L = ≤ℕ-trans (m≤m+n K₀ m) (m≤n+m (K₀ +ℕ m) tδ)
        tδ≤L : tδ ≤ℕ L
        tδ≤L = m≤m+n tδ (K₀ +ℕ m)
        n₀≤K₀ : n₀ ≤ℕ K₀
        n₀≤K₀ = m≤m+n n₀ m

        L≤j₁ : L ≤ℕ sample-level x 0<x n₁
        L≤j₁ = proj₂ (sample-level-unbounded x 0<x L)
        n₁≤n : n₁ ≤ℕ n
        n₁≤n = ≤ℕ-trans (m≤m+n n₁ n₂) (m≤m+n nn tδ)
        n₂≤n : n₂ ≤ℕ n
        n₂≤n = ≤ℕ-trans (m≤n+m n₂ n₁) (m≤m+n nn tδ)
        tδ≤n : tδ ≤ℕ n
        tδ≤n = m≤n+m tδ nn

        L≤j : L ≤ℕ j
        L≤j = ≤ℕ-trans L≤j₁ (sample-level-mono x 0<x n₁≤n)
        L≤j₂ : L ≤ℕ sample-level x' 0<x' n₂
        L≤j₂ = proj₂ (sample-level-unbounded x' 0<x' L)
        L≤j' : L ≤ℕ j'
        L≤j' = ≤ℕ-trans L≤j₂ (sample-level-mono x' 0<x' n₂≤n)

        m≤j' : m ≤ℕ j'
        m≤j' = ≤ℕ-trans m≤L L≤j'
        K₀≤j' : K₀ ≤ℕ j'
        K₀≤j' = ≤ℕ-trans K₀≤L L≤j'

        -- the three width premises
        --
        -- 三个宽度前提
        smallL : recip2^t L < q
        smallL = proj₁ (db L tδ≤L)
        widthL : width x L ≤ W
        widthL = width-small x B L q w0≤B 0≤B smallL
        hwj : width x j ≤ W
        hwj = ≤-trans (width-dec x L≤j) widthL
        hwj' : width x j' ≤ W
        hwj' = ≤-trans (width-dec x L≤j') widthL
        hwq : width x (j +ℕ j') ≤ W
        hwq = ≤-trans (width-dec x (≤ℕ-trans L≤j (m≤m+n j j'))) widthL

        -- the gap of the sampled centres, accounted into 6W + 8d
        --
        -- 两个采样中心之差，经 acct 记账成 6W + 8d
        A = sample-deep x 0<x n
        B' = sample-deep x' 0<x' n
        gap0 = sample-gap-deep d₀ W x 0<x x' 0<x' m n hb hwj hwj' hwq
                 (<⇒≤ 0<W) (<⇒≤ 0<d₀) m≤j'
        gapB : ∣ B' - A ∣ ≤ embed 6 * W + embed 8 * d₀
        gapB = subst (λ z → ∣ B' - A ∣ ≤ z) (acct W d₀) gap0

        -- c2 bounds both samples from below
        --
        -- c2 压住两个采样
        c≤A : c ≤ A
        c≤A = ≤-trans (l-mono x (sample-level-low x 0<x n)) (centre-l x j)
        c2≤c : c2 ≤ c
        c2≤c = subst (λ z → c2 ≤ z) (*-identityʳ c)
                 (*-monoˡ-≤-nonNeg c {{nonNegative 0≤c}} half≤1)
        c2≤A : c2 ≤ A
        c2≤A = ≤-trans c2≤c c≤A

        t = K₀
        lx≥c : c ≤ l x t
        lx≥c = l-mono x n₀≤K₀
        lx'lb : l x t - d₀ ≤ l x' t
        lx'lb = l-near-lower d₀ x x' m (λ s ms → proj₁ (hb s ms)) t
                  (m≤n+m m n₀)
        sub1 : c - d₀ ≤ l x t - d₀
        sub1 = sub-mono {a = c} {a' = l x t} {b = d₀} {b' = d₀} lx≥c (≤-refl {d₀})
        sub2 : c - c2 ≤ c - d₀
        sub2 = sub-mono {a = c} {a' = c} {b = c2} {b' = d₀} (≤-refl {c}) d≤c2
        cc≡c2 : c - c2 ≡ c2
        cc≡c2 = half-sub c
        c2≤lx' : c2 ≤ l x' t
        c2≤lx' = subst (λ z → z ≤ l x' t) cc≡c2
                   (≤-trans sub2 (≤-trans sub1 lx'lb))
        c2≤B : c2 ≤ B'
        c2≤B = ≤-trans c2≤lx'
                 (≤-trans (l-mono x' K₀≤j') (centre-l x' j'))

        -- the gap of the two reciprocals
        --
        -- 两个倒数之差的界
        0A = pos-deep x 0<x n
        0B = pos-deep x' 0<x' n
        gapR : ∣ inv A {{pos⇒nonZero A {{positive 0A}}}}
                 - inv B' {{pos⇒nonZero B' {{positive 0B}}}} ∣
                 ≤ (embed 6 * W + embed 8 * d₀) * invcc
        gapR = gap-c A B' c2 (embed 6 * W + embed 8 * d₀) 0A 0B 0c2 c2≤A c2≤B gapB

        -- the three radii are each below u
        --
        -- 三层半径各自低于 u
        3δ<u : ((δ n + δ n) + δ n) < u
        3δ<u = let dδ : δ n < qδ
                   dδ = proj₂ (db n tδ≤n)
                   s1 : δ n + δ n < qδ + qδ
                   s1 = +-mono-< dδ dδ
                   s2 : (δ n + δ n) + δ n < (qδ + qδ) + qδ
                   s2 = +-mono-<-≤ s1 (<⇒≤ dδ)
                   s3 : (qδ + qδ) + qδ ≡ u
                   s3 = trans (sym (coef3 qδ)) e3q
               in subst (λ z → ((δ n + δ n) + δ n) < z) s3 s2

        -- the modulus side: 8d is dominated by 8(c2²u)
        --
        -- 模数侧的记账：8d 被 8(c2²u) 压住
        d8 : embed 8 * d₀ ≤ embed 8 * (cc * u)
        d8 = *-monoˡ-≤-nonNeg (embed 8) {{nonNegative 0≤8}} d≤c2u
        body : embed 6 * W + embed 8 * d₀ ≤ embed 6 * W + embed 8 * (cc * u)
        body = +-mono-≤ (≤-refl {embed 6 * W}) d8
        r≤R : (embed 6 * W + embed 8 * d₀) * invcc
                ≤ (embed 6 * W + embed 8 * (cc * u)) * invcc
        r≤R = *-monoʳ-≤-nonNeg invcc {{nonNegative 0≤inv}} body

        -- closing the budget
        --
        -- 预算收口
        budgetOut = budget k c2 W ⦃ nzcc ⦄ n 6W<u 3δ<u
        total< : ((embed 6 * W + embed 8 * d₀) * invcc
                    + ((δ n + δ n) + δ n)) < ε k
        total< = ≤-<-trans (+-mono-≤ r≤R (≤-refl {((δ n + δ n) + δ n)}))
                   budgetOut

        -- at-hyp yields the two hypotheses of close-recip
        --
        -- at-hyp 给出 close-recip 的两条前提
        hth = at-hyp (inv A {{pos⇒nonZero A {{positive 0A}}}})
                     (inv B' {{pos⇒nonZero B' {{positive 0B}}}})
                     (δ n) (ε k) ((embed 6 * W + embed 8 * d₀) * invcc)
                     gapR total<
    in close-recip x 0<x x' 0<x' n (ε k) (proj₁ hth) (proj₂ hth))
