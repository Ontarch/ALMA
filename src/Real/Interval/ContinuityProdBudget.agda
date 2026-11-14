------------------------------------------------------------------------
-- The product budget: scaling, width, level depth, and the forward and reverse accounting
--
-- 乘积预算：尺度、宽度、层级深度与正反两个方向的记账
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module Real.Interval.ContinuityProdBudget where

open import Data.Nat using (ℕ; suc; _^_; _∸_; s≤s; z≤n)
  renaming (_+_ to _+ℕ_; _*_ to _*ℕ_; _≤_ to _≤ℕ_; _<_ to _<N_)
open import Data.Rational using (ℚ; 0ℚ; 1ℚ; _+_; _-_; _*_; _≤_; _<_; nonNegative)
  renaming (-_ to neg)
open import Data.Rational.Properties using
  (≤-trans; ≤-refl; ≤-<-trans; +-mono-≤; +-monoʳ-<; +-monoˡ-<; <-trans; <-≤-trans
  ; <⇒≤; *-monoʳ-≤-nonNeg; 1/pos⇒pos; positive⁻¹; ≤-reflexive; *-monoˡ-≤-nonNeg
  ; *-assoc; *-distribʳ-+; *-comm; *-identityˡ; +-assoc; +-comm; +-identityʳ
  ; *-distribˡ-+)
open import Relation.Binary.PropositionalEquality using
  (_≡_; sym; trans; cong; cong₂; subst)

open import Base.RationalRing using (0<1; +interchange)
open import Real using
  (ε; embed; 0<ε; embed-+-hom; embed-*-hom; embed-mono-≤; embed-suc-pos; 0≤embed)
open import Real.IntervalEquiv using
  (l; u; width; width-n; 0<width; node; recip2^t; frac-strict)
open import Real.Interval using (RealI; δ)
open import Real.Interval.ContinuityMul using (minus-shift)
open import Real.Interval.ContinuityProdGap using (prod-gap-term)
open import Real.Interval.Kit using (recip-antitone)
open import Real.Interval.LimitLaws using (ε-mono)
open import Real.Interval.Mul.Order using (δ≤ε)
open import Real.Interval.OrderLe using (sub-mono)
open import Real.Interval.Rational using (negsub)

------------------------------------------------------------------------
-- Bounding a sum of two values by one embedded natural
--
-- 用同一个自然数的嵌入上界两个值之和

-- A sum of two values bounded by embedded naturals is bounded by their
-- embedded sum.
--
-- 被两个嵌入自然数分别界住的两值之和，被它们的嵌入和界住。
prod-value-bound :
  (Mx My : ℚ) (Nx Ny : ℕ) →
  Mx ≤ embed Nx → My ≤ embed Ny → Mx + My ≤ embed (Nx +ℕ Ny)
prod-value-bound Mx My Nx Ny hx hy =
  ≤-trans (+-mono-≤ hx hy) (≤-reflexive (sym (embed-+-hom Nx Ny)))

------------------------------------------------------------------------
-- The gap term is a product of a sum
--
-- 间隙项是一个和与 d 的乘积

-- The gap term factors as a product of the magnitude sum and d.
--
-- 间隙项可分解为量值和与 d 的乘积。
prod-gap-eq : (Mx My d : ℚ) → Mx * d + d * My ≡ (Mx + My) * d
prod-gap-eq Mx My d =
  trans (cong (λ z → Mx * d + z) (*-comm d My))
        (sym (*-distribʳ-+ d Mx My))

------------------------------------------------------------------------
-- Multiplicative budget
--
-- 乘性预算

-- If the sum of the two magnitudes is at most embed N, and d is at most
-- the dyadic recip2^t T, then the whole product term is strictly below
-- ε k, provided N(k+1) < 2^T.
--
-- 若两个量值之和不超过某个嵌入自然数，且 d 不超过对应的二进量，则在
-- 相应指数比较条件成立时，整个乘积项严格小于目标精度。
prod-budget :
  (Mx My d : ℚ) (N k T : ℕ) →
  0ℚ ≤ d → d ≤ recip2^t T →
  Mx + My ≤ embed N →
  (N *ℕ suc k) <N 2 ^ T →
  (Mx + My) * d < ε k
prod-budget Mx My d N k T 0≤d d≤r M≤e h =
  ≤-<-trans
    (≤-trans
      (*-monoʳ-≤-nonNeg d {{nonNegative 0≤d}} M≤e)
      (*-monoˡ-≤-nonNeg (embed N) {{nonNegative (0≤embed N)}} d≤r))
    (frac-strict N k T h)

------------------------------------------------------------------------
-- One width term folded into a single embedding
--
-- 单项宽度折成单个嵌入

-- Folding one magnitude bound and one width bound into a single
-- embedded-natural budget.
--
-- 把一个量值界与一个宽度界折成单个嵌入自然数的预算。
width-one :
  (Mx : ℚ) (N : ℕ) (wy r : ℚ) →
  0ℚ ≤ wy → Mx ≤ embed N → wy ≤ embed N * r →
  Mx * wy ≤ embed (N *ℕ N) * r
width-one Mx N wy r 0≤wy Mx≤N wy≤ =
  ≤-trans
    (≤-trans
      (*-monoʳ-≤-nonNeg wy {{nonNegative 0≤wy}} Mx≤N)
      (*-monoˡ-≤-nonNeg (embed N) {{nonNegative (0≤embed N)}} wy≤))
    (≤-reflexive one)
  where
  one : embed N * (embed N * r) ≡ embed (N *ℕ N) * r
  one = trans (sym (*-assoc (embed N) (embed N) r))
              (cong (λ z → z * r) (sym (embed-*-hom N N)))

------------------------------------------------------------------------
-- Two width terms in one budget
--
-- 两项宽度合成一个预算

-- Two width terms together fit into the doubled embedding budget.
--
-- 两个宽度项合起来落在加倍的嵌入预算内。
width-budget :
  (Mx My : ℚ) (N : ℕ) (wy wx r : ℚ) →
  0ℚ ≤ wy → 0ℚ ≤ wx → 0ℚ ≤ r →
  Mx ≤ embed N → My ≤ embed N →
  wy ≤ embed N * r → wx ≤ embed N * r →
  Mx * wy + My * wx ≤ embed ((N *ℕ N) +ℕ (N *ℕ N)) * r
width-budget Mx My N wy wx r 0≤wy 0≤wx 0≤r Mx≤N My≤N wy≤ wx≤ =
  let t1 : Mx * wy ≤ embed (N *ℕ N) * r
      t1 = width-one Mx N wy r 0≤wy Mx≤N wy≤
      t2 : My * wx ≤ embed (N *ℕ N) * r
      t2 = width-one My N wx r 0≤wx My≤N wx≤
      fold : embed (N *ℕ N) * r + embed (N *ℕ N) * r
             ≡ embed ((N *ℕ N) +ℕ (N *ℕ N)) * r
      fold = trans (sym (*-distribʳ-+ r (embed (N *ℕ N)) (embed (N *ℕ N))))
                   (cong (λ z → z * r)
                     (sym (embed-+-hom (N *ℕ N) (N *ℕ N))))
      fold≤ : embed (N *ℕ N) * r + embed (N *ℕ N) * r ≤ embed ((N *ℕ N) +ℕ (N *ℕ N)) * r
      fold≤ = subst (λ z → embed (N *ℕ N) * r + embed (N *ℕ N) * r ≤ z) fold
                   (≤-refl {embed (N *ℕ N) * r + embed (N *ℕ N) * r})
  in ≤-trans (+-mono-≤ t1 t2) fold≤

------------------------------------------------------------------------
-- The dyadic scale is positive
--
-- 二进量是正的

-- The dyadic reciprocal is strictly positive at every depth.
--
-- 二进倒数在每一深度严格为正。
0<recip2^t : (t : ℕ) → 0ℚ < recip2^t t
0<recip2^t t =
  let d = 2 ^ t ∸ 1
      p = 1/pos⇒pos (embed (suc d)) {{embed-suc-pos {d}}}
  in positive⁻¹ (recip2^t t) {{p}}

-- The dyadic scale is nonnegative.
--
-- 二进量非负。
0≤recip2^t : (t : ℕ) → 0ℚ ≤ recip2^t t
0≤recip2^t t = <⇒≤ (0<recip2^t t)

------------------------------------------------------------------------
-- Deep width is bounded by a fixed natural scaled dyadically
--
-- 深层宽度被固定自然数的二进尺度控制

-- The width at a deep level is bounded by the shallowest width scaled
-- dyadically.
--
-- 深层宽度被最浅层宽度按二进尺度控制。
width-deep :
  (r : RealI) (N n : ℕ) →
  width r 0 ≤ embed N →
  width r n ≤ embed N * recip2^t n
width-deep r N n w0≤ =
  ≤-trans (width-n r n)
    (*-monoʳ-≤-nonNeg (recip2^t n) {{nonNegative (0≤recip2^t n)}} w0≤)

------------------------------------------------------------------------
-- Width is positive at every level
--
-- 每一层的宽度都是正的

-- Width is strictly positive at every level.
--
-- 每一层的宽度严格为正。
width-pos : (r : RealI) (n : ℕ) → 0ℚ < width r n
width-pos r n = 0<width (node r n)

------------------------------------------------------------------------
-- Adding a strict pair to a bounded third term
--
-- 严格的两项加上有界的第三项

-- Two terms below e₂ plus a third below e₁ fall below eₖ, given the
-- doubling chain.
--
-- 两个低于 e₂ 的项加上一个不超过 e₁ 的项，在倍增链下低于 eₖ。
sum-budget :
  (a b c e₂ e₁ eₖ : ℚ) →
  a < e₂ → b < e₂ → c ≤ e₁ →
  e₂ + e₂ ≡ e₁ → e₁ + e₁ ≡ eₖ →
  (a + b) + c < eₖ
sum-budget a b c e₂ e₁ eₖ a< b< c≤ h₂ h₁ =
  let ab : a + b < e₂ + e₂
      ab = <-trans (+-monoˡ-< b a<) (+-monoʳ-< e₂ b<)

      ab' : a + b < e₁
      ab' = subst (λ z → a + b < z) h₂ ab

      step : (a + b) + c < e₁ + e₁
      step = <-≤-trans (+-monoˡ-< c ab')
               (+-mono-≤ (≤-refl {e₁}) c≤)
  in subst (λ z → (a + b) + c < z) h₁ step

------------------------------------------------------------------------
-- The whole gap term plus the dyadic correction
--
-- 整个间隙项加上二进修正

-- The forward product gap plus the dyadic correction stays below ε k.
--
-- 正向乘积间隙加上二进修正严格低于 ε k。
gap-budget :
  (x y : RealI) (Mx My d : ℚ) (N k j₁ j₂ T n : ℕ) →
  0ℚ ≤ d → d ≤ recip2^t T →
  Mx ≤ embed N →
  My ≤ embed N →
  Mx + My ≤ embed N →
  (N *ℕ suc j₂) <N 2 ^ T →
  ((N *ℕ N) +ℕ (N *ℕ N)) *ℕ suc j₂ <N 2 ^ (2 *ℕ n) →
  j₁ ≤ℕ n →
  ε j₂ + ε j₂ ≡ ε j₁ →
  ε j₁ + ε j₁ ≡ ε k →
  u y (2 *ℕ n) - l y (2 *ℕ n) ≤ embed N * recip2^t (2 *ℕ n) →
  u x (2 *ℕ n) - l x (2 *ℕ n) ≤ embed N * recip2^t (2 *ℕ n) →
  prod-gap-term Mx My d x y n + δ n < ε k
gap-budget x y Mx My d N k j₁ j₂ T n
  0≤d d≤r Mx≤N My≤N M≤e hT hW j₁≤n h₂ h₁ wy≤ wx≤ =
  let wy = u y (2 *ℕ n) - l y (2 *ℕ n)
      wx = u x (2 *ℕ n) - l x (2 *ℕ n)
      r = recip2^t (2 *ℕ n)
      Mw = (N *ℕ N) +ℕ (N *ℕ N)

      0≤r : 0ℚ ≤ r
      0≤r = <⇒≤ (0<recip2^t (2 *ℕ n))

      0≤wy : 0ℚ ≤ wy
      0≤wy = <⇒≤ (width-pos y (2 *ℕ n))

      0≤wx : 0ℚ ≤ wx
      0≤wx = <⇒≤ (width-pos x (2 *ℕ n))

      K : (Mx + My) * d < ε j₂
      K = prod-budget Mx My d N j₂ T 0≤d d≤r M≤e hT

      A : ℚ
      A = Mx * d + d * My

      A< : A < ε j₂
      A< = subst (λ z → z < ε j₂) (sym (prod-gap-eq Mx My d)) K

      Bv : ℚ
      Bv = Mx * wy + My * wx

      B≤ : Bv ≤ embed Mw * r
      B≤ = width-budget Mx My N wy wx r 0≤wy 0≤wx 0≤r Mx≤N My≤N wy≤ wx≤

      B< : Bv < ε j₂
      B< = ≤-<-trans B≤ (frac-strict Mw j₂ (2 *ℕ n) hW)

      δn≤ : δ n ≤ ε j₁
      δn≤ = ≤-trans (δ≤ε n) (ε-mono j₁≤n)
  in sum-budget A Bv (δ n) (ε j₂) (ε j₁) (ε k) A< B< δn≤ h₂ h₁

------------------------------------------------------------------------
-- Gap term after shifting the two widths back
--
-- 把两份宽度搬回之后的间隙项

-- If the widths of the perturbed pair exceed the reference widths by at
-- most (d + d), the gap term grows by at most Mx * (d + d) + My * (d + d)
-- on top of the reference gap term.
--
-- 若扰动那一对的宽度最多比参照宽度多出两倍 d，则间隙项最多比参照
-- 间隙项多出对应的交叉项。
term-width-le :
  (Mx My d wx wy wx' wy' : ℚ) →
  0ℚ ≤ Mx → 0ℚ ≤ My →
  wx' ≤ wx + (d + d) → wy' ≤ wy + (d + d) →
  (Mx * d + d * My) + (Mx * wy' + My * wx')
    ≤ ((Mx * d + d * My) + (Mx * wy + My * wx))
        + (Mx * (d + d) + My * (d + d))
term-width-le Mx My d wx wy wx' wy' 0≤Mx 0≤My hx' hy' =
  let P = Mx * wy
      Q = My * wx
      R = Mx * (d + d)
      S = My * (d + d)
      Ax = Mx * d + d * My
      E' = d + d

      uy : Mx * wy' ≤ Mx * (wy + E')
      uy = *-monoˡ-≤-nonNeg Mx {{nonNegative 0≤Mx}} hy'

      ux : My * wx' ≤ My * (wx + E')
      ux = *-monoˡ-≤-nonNeg My {{nonNegative 0≤My}} hx'

      ey : Mx * (wy + E') ≡ P + R
      ey = *-distribˡ-+ Mx wy E'

      ex : My * (wx + E') ≡ Q + S
      ex = *-distribˡ-+ My wx E'

      step1 : Mx * wy' + My * wx' ≤ (P + R) + (Q + S)
      step1 =
        ≤-trans (+-mono-≤ uy ux)
          (≤-reflexive (cong₂ _+_ ey ex))

      perm : Ax + ((P + R) + (Q + S)) ≡ (Ax + (P + Q)) + (R + S)
      perm =
        let l1 : Ax + ((P + R) + (Q + S)) ≡ Ax + (P + (R + (Q + S)))
            l1 = cong (Ax +_) (+-assoc P R (Q + S))

            l2 : Ax + (P + (R + (Q + S))) ≡ Ax + (P + (Q + (R + S)))
            l2 = cong (Ax +_) (cong (P +_)
                   (trans (sym (+-assoc R Q S))
                     (trans (cong (_+ S) (+-comm R Q)) (+-assoc Q R S))))

            l3 : Ax + (P + (Q + (R + S))) ≡ (Ax + (P + Q)) + (R + S)
            l3 = trans (sym (+-assoc Ax P (Q + (R + S))))
                   (trans (sym (+-assoc (Ax + P) Q (R + S)))
                     (cong (_+ (R + S)) (+-assoc Ax P Q)))
        in trans l1 (trans l2 l3)

      step2 : Ax + ((P + R) + (Q + S)) ≤ (Ax + (P + Q)) + (R + S)
      step2 = ≤-reflexive perm
  in ≤-trans (+-mono-≤ (≤-refl {Ax}) step1) step2

------------------------------------------------------------------------
-- The reversed budget with the two copied shifts
--
-- 带两份平移的反向预算

-- The ladder is three and a half halvings deep, so there is room for two
-- strict copies of the reference bound, the width part, and the dyadic
-- correction.
--
-- 阶梯深三级半，因而容得下两份严格的参照界、宽度部分与二进修正。
gap-budget-rev :
  (x y : RealI) (Mx My d : ℚ) (N k j₀ j₁ j₂ T n : ℕ) →
  0ℚ ≤ d → d ≤ recip2^t T →
  Mx ≤ embed N → My ≤ embed N → Mx + My ≤ embed N →
  (N *ℕ suc j₂) <N 2 ^ T →
  ((N *ℕ N) +ℕ (N *ℕ N)) *ℕ suc j₂ <N 2 ^ (2 *ℕ n) →
  j₁ ≤ℕ n →
  ε j₂ + ε j₂ ≡ ε j₁ →
  ε j₁ + ε j₁ ≡ ε j₀ →
  ε j₀ + ε j₀ ≡ ε k →
  u y (2 *ℕ n) - l y (2 *ℕ n) ≤ embed N * recip2^t (2 *ℕ n) →
  u x (2 *ℕ n) - l x (2 *ℕ n) ≤ embed N * recip2^t (2 *ℕ n) →
  (prod-gap-term Mx My d x y n + (Mx + My) * (d + d)) + δ n < ε k
gap-budget-rev x y Mx My d N k j₀ j₁ j₂ T n
  0≤d d≤r Mx≤N My≤N M≤e hT hW j₁≤n h₂₁ h₁₀ h₀k wy≤ wx≤ =
  let wy = u y (2 *ℕ n) - l y (2 *ℕ n)
      wx = u x (2 *ℕ n) - l x (2 *ℕ n)
      r = recip2^t (2 *ℕ n)
      Mw = (N *ℕ N) +ℕ (N *ℕ N)
      Kd = (Mx + My) * d
      Gd = (Mx + My) * (d + d)

      0≤r : 0ℚ ≤ r
      0≤r = <⇒≤ (0<recip2^t (2 *ℕ n))

      0≤wy : 0ℚ ≤ wy
      0≤wy = <⇒≤ (width-pos y (2 *ℕ n))

      0≤wx : 0ℚ ≤ wx
      0≤wx = <⇒≤ (width-pos x (2 *ℕ n))

      K : Kd < ε j₂
      K = prod-budget Mx My d N j₂ T 0≤d d≤r M≤e hT

      K2 : Gd < ε j₁
      K2 =
        let e : Gd ≡ Kd + Kd
            e = *-distribˡ-+ (Mx + My) d d

            s : Kd + Kd < ε j₂ + ε j₂
            s = <-trans (+-monoˡ-< Kd K) (+-monoʳ-< (ε j₂) K)
        in subst (λ z → z < ε j₁) (sym e)
             (subst (λ z → Kd + Kd < z) h₂₁ s)

      A : ℚ
      A = Mx * d + d * My

      A< : A < ε j₂
      A< = subst (λ z → z < ε j₂) (sym (prod-gap-eq Mx My d)) K

      Bv : ℚ
      Bv = Mx * wy + My * wx

      B≤ : Bv ≤ embed Mw * r
      B≤ = width-budget Mx My N wy wx r 0≤wy 0≤wx 0≤r Mx≤N My≤N wy≤ wx≤

      B< : Bv < ε j₂
      B< = ≤-<-trans B≤ (frac-strict Mw j₂ (2 *ℕ n) hW)

      ab : A + Bv < ε j₂ + ε j₂
      ab = <-trans (+-monoˡ-< Bv A<) (+-monoʳ-< (ε j₂) B<)

      ab₁ : A + Bv < ε j₁
      ab₁ = subst (λ z → A + Bv < z) h₂₁ ab

      abE : (A + Bv) + Gd < ε j₁ + ε j₁
      abE = <-trans (+-monoˡ-< Gd ab₁) (+-monoʳ-< (ε j₁) K2)

      abE₀ : (A + Bv) + Gd < ε j₀
      abE₀ = subst (λ z → (A + Bv) + Gd < z) h₁₀ abE

      δn≤ : δ n ≤ ε j₁
      δn≤ = ≤-trans (δ≤ε n) (ε-mono j₁≤n)

      abEδ : ((A + Bv) + Gd) + δ n < ε j₀ + ε j₁
      abEδ = <-≤-trans (+-monoˡ-< (δ n) abE₀)
               (+-mono-≤ (≤-refl {ε j₀}) δn≤)

      0≤e₁ : 0ℚ ≤ ε j₁
      0≤e₁ = <⇒≤ (0<ε j₁)

      e₁≤e₀ : ε j₁ ≤ ε j₀
      e₁≤e₀ = ≤-trans (≤-reflexive (sym (+-identityʳ (ε j₁))))
                (≤-trans (+-mono-≤ (≤-refl {ε j₁}) 0≤e₁)
                  (≤-reflexive h₁₀))

      slack : ε j₀ + ε j₁ ≤ ε j₀ + ε j₀
      slack = +-mono-≤ (≤-refl {ε j₀}) e₁≤e₀

      final : ((A + Bv) + Gd) + δ n < ε j₀ + ε j₀
      final = <-≤-trans abEδ slack
  in subst (λ z → ((A + Bv) + Gd) + δ n < z) h₀k final

------------------------------------------------------------------------
-- The dyadic reciprocal is at most one
--
-- 二进倒数不超过一

-- The dyadic reciprocal never exceeds one.
--
-- 二进倒数不超过一。
recip2^t≤1 : (t : ℕ) → recip2^t t ≤ 1ℚ
recip2^t≤1 t =
  let d = 2 ^ t ∸ 1
      A = embed (suc d)
      1≤A : 1ℚ ≤ A
      1≤A = embed-mono-≤ {1} {suc d} (s≤s z≤n)
  in recip-antitone {a = 1ℚ} {b = A} 0<1 1≤A

------------------------------------------------------------------------
-- Width under endpoint movement
--
-- 端点移动下的宽度

-- The width grows by at most twice the endpoint displacement.
--
-- 宽度最多增加端点位移的两倍。
width-shift :
  (lo hi lo' hi' d : ℚ) →
  hi' ≤ hi + d →
  lo ≤ lo' + d →
  hi' - lo' ≤ (hi - lo) + (d + d)
width-shift lo hi lo' hi' d hhi hlo =
  let s1 : hi' - lo' ≤ (hi + d) - lo'
      s1 = sub-mono {a = hi'} {a' = hi + d} {b = lo'} {b' = lo'} hhi (≤-refl {lo'})

      s2 : (hi + d) - lo' ≤ (hi + d) - (lo - d)
      s2 = sub-mono {a = hi + d} {a' = hi + d} {b = lo'} {b' = lo - d}
             (≤-refl {hi + d}) (minus-shift lo lo' d hlo)

      s3 : (hi + d) - (lo - d) ≡ (hi - lo) + (d + d)
      s3 = trans (cong ((hi + d) +_) (negsub lo d))
             (trans (cong ((hi + d) +_) (+-comm d (neg lo)))
               (+interchange hi d (neg lo) d))
  in ≤-trans s1 (≤-trans s2 (≤-reflexive s3))

------------------------------------------------------------------------
-- Multiplication is monotone in the first factor for a nonnegative
-- second factor
--
-- 第二个因子非负时，乘法对第一个因子单调

-- Multiplication by a nonnegative scalar preserves ≤.
--
-- 乘以非负标量保持 ≤ 关系。
mul-left-≤ : (r : ℚ) → 0ℚ ≤ r → {p q : ℚ} → p ≤ q → p * r ≤ q * r
mul-left-≤ r 0≤r {p} {q} h = *-monoʳ-≤-nonNeg r {{nonNegative 0≤r}} h

------------------------------------------------------------------------
-- Width bound transfer
--
-- 宽度界搬运

-- A width bound is preserved up to the factor (A + A) + A after an
-- endpoint shift by at most r.
--
-- 在端点位移不超过 r 时，宽度界以 (A + A) + A 的因子保持。
width-close-le :
  (lo hi lo' hi' A r : ℚ) →
  1ℚ ≤ A → 0ℚ ≤ r →
  hi - lo ≤ A * r →
  hi' ≤ hi + r → lo ≤ lo' + r →
  hi' - lo' ≤ ((A + A) + A) * r
width-close-le lo hi lo' hi' A r 1≤A 0≤r hw hhi hlo =
  let w1 : hi' - lo' ≤ (hi - lo) + (r + r)
      w1 = width-shift lo hi lo' hi' r hhi hlo

      r≤Ar : r ≤ A * r
      r≤Ar = ≤-trans (≤-reflexive (sym (*-identityˡ r))) (mul-left-≤ r 0≤r 1≤A)

      rr : r + r ≤ A * r + A * r
      rr = +-mono-≤ r≤Ar r≤Ar

      w2 : (hi - lo) + (r + r) ≤ A * r + (A * r + A * r)
      w2 = +-mono-≤ hw rr

      a1 : ((A + A) + A) * r ≡ (A + A) * r + A * r
      a1 = *-distribʳ-+ r (A + A) A

      a2 : (A + A) * r ≡ A * r + A * r
      a2 = *-distribʳ-+ r A A

      a3 : (A + A) * r + A * r ≡ (A * r + A * r) + A * r
      a3 = cong (_+ A * r) a2

      a4 : A * r + (A * r + A * r) ≡ (A * r + A * r) + A * r
      a4 = sym (+-assoc (A * r) (A * r) (A * r))

      w3 : A * r + (A * r + A * r) ≡ ((A + A) + A) * r
      w3 = trans a4 (trans (sym a3) (sym a1))
  in ≤-trans w1 (≤-trans w2 (≤-reflexive w3))
