------------------------------------------------------------------------
-- Endpoint expansion, boundedness, and Lipschitz estimates for Close
--
-- Close 邻域的端点展开、有界性与 Lipschitz 估计
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module Real.Interval.ContinuityClose where

open import Data.Nat using (ℕ; zero; z≤n) renaming (_+_ to _+ℕ_; _≤_ to _≤ℕ_)
import Data.Nat.Properties as ℕP
open import Data.Product using (Σ; _,_; _×_; proj₁; proj₂)
open import Data.Rational using (_⊔_; ℚ; 0ℚ; _+_; _-_; _<_; _≤_; ∣_∣)
open import Data.Rational.Base using () renaming (-_ to neg)
open import Data.Rational.Properties using
  (<⇒≤; ≤-refl; ≤-trans; +-comm; +-monoˡ-<; +-mono-≤; neg-distrib-+; p≤p⊔q
  ; p≤q⊔p; 0≤∣p∣; ∣p∣≡p∨∣p∣≡-p; neg-antimono-≤)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using
  (_≡_; cong; sym; trans; subst; subst₂)

open import Base.RationalRing using (neg-involutive)
open import Real.IntervalEquiv using (node; l; u; l-mono; u-mono)
open import Real.Interval using (δ; RealI; embedℚ)
open import Real.Interval.Arith using (_-ℝ_; negℝ)
open import Real.Interval.Continuity using (Close; sub-add-cancel)
open import Real.Interval.ContinuityMul using
  (u-sub-emb; l-add-emb; budget-<; sub-cancel-<; shift-inside; shift-bound
  ; sub-left-≤; node-diff-up; node-diff-down)
open import Real.Interval.OrderLe using (sub-mono)
open import Real.Interval.Mul.Core using (abs-≤)
open import Real.Interval.Node using (u-hom; u-neg; l-dyadic)
open import Real.Interval.Order using (_<ℝ_)
open import Real.Interval.Rational using (-r≤|r|; r≤|r|; negsub)

------------------------------------------------------------------------
-- Absolute value from two one-sided bounds
--
-- 由两侧单边界给出绝对值界

-- Two one-sided rational bounds yield an absolute-value bound.
--
-- 两个单向有理界给出绝对值界。
abs-from :
  (a C : ℚ) → neg C ≤ a → a ≤ C → ∣ a ∣ ≤ C
abs-from a C lo hi with ∣p∣≡p∨∣p∣≡-p a
... | inj₁ eq = subst (λ z → z ≤ C) (sym eq) hi
... | inj₂ eq = subst (λ z → z ≤ C) (sym eq)
                (subst (λ z → neg a ≤ z) (neg-involutive C) (neg-antimono-≤ lo))

------------------------------------------------------------------------
-- The shallowest interval bounds every deeper endpoint
--
-- 最浅层区间界住所有更深层的端点

-- Every endpoint of x is bounded in absolute value by the shallowest
-- bound.
--
-- x 的每个端点都被最浅层的界界住绝对值。
bounded :
  (x : RealI) →
  Σ ℚ (λ M → 0ℚ ≤ M ×
    (∀ m a → l x m ≤ a → a ≤ u x m → ∣ a ∣ ≤ M))
bounded x =
  let L = l x 0
      U = u x 0
      M = ∣ L ∣ ⊔ ∣ U ∣

      0≤M : 0ℚ ≤ M
      0≤M = ≤-trans (0≤∣p∣ L) (p≤p⊔q ∣ L ∣ ∣ U ∣)

      L≥ : neg M ≤ L
      L≥ = subst (λ z → neg M ≤ z) (neg-involutive L)
             (neg-antimono-≤
               (≤-trans (-r≤|r| L) (p≤p⊔q ∣ L ∣ ∣ U ∣)))

      U≤ : U ≤ M
      U≤ = ≤-trans (r≤|r| U) (p≤q⊔p ∣ L ∣ ∣ U ∣)

      inside : ∀ m a → l x m ≤ a → a ≤ u x m → ∣ a ∣ ≤ M
      inside m a la au =
        let lo : neg M ≤ a
            lo = ≤-trans L≥ (≤-trans (l-mono x {n = zero} {m = m} z≤n) la)

            hi : a ≤ M
            hi = ≤-trans au (≤-trans (u-mono x {n = zero} {m = m} z≤n) U≤)
        in abs-from a M lo hi
  in M , 0≤M , inside

------------------------------------------------------------------------
-- From a neighbourhood to order information
--
-- 由邻域得到序信息

-- The leftward difference is below the radius. A difference uses the
-- level once, so the same level as the order statement suffices.
--
-- 左向差分低于半径。减法只用一次层级，故与序陈述同层即可。
close-left : (d : ℚ) (x x' : RealI) → Close d x x' → x -ℝ x' <ℝ embedℚ d
close-left d x x' h =
  let n , w = proj₁ h

      h₁ : u x n + δ n < l x' n + d
      h₁ = sub-cancel-< (u x n + δ n) (l x' n) d
             (subst (λ z → z < l x' n) (u-sub-emb x d n) w)

      s : u x n + neg (l x' n) < d + neg (δ n)
      s = budget-< (u x n) (l x' n) d (δ n) h₁

      s' : u x n + neg (l x' n) < neg (δ n) + d
      s' = subst (λ z → u x n + neg (l x' n) < z) (+-comm d (neg (δ n))) s

      lhs : u (x -ℝ x') n ≡ u x n + neg (l x' n)
      lhs = trans (u-hom x (negℝ x') n) (cong (u x n +_) (u-neg x' n))

      rhs : l (embedℚ d) n ≡ neg (δ n) + d
      rhs = l-dyadic d n
  in n , subst₂ (λ p q → p < q) (sym lhs) (sym rhs) s'

-- The rightward difference is below the radius.
--
-- 右向差分低于半径。
close-right : (d : ℚ) (x x' : RealI) → Close d x x' → x' -ℝ x <ℝ embedℚ d
close-right d x x' h =
  let n , w = proj₂ h

      h₂ : u x' n < (l x n + neg (δ n)) + d
      h₂ = subst (λ z → u x' n < z) (l-add-emb x d n) w

      shift : ((l x n + neg (δ n)) + d) + δ n ≡ l x n + d
      shift = trans (cong (_+ δ n) (shift-inside (l x n) d (δ n)))
                    (sub-add-cancel (l x n + d) (δ n))

      h₃ : u x' n + δ n < l x n + d
      h₃ = subst (λ z → u x' n + δ n < z) shift
             (+-monoˡ-< (δ n) h₂)

      s : u x' n + neg (l x n) < d + neg (δ n)
      s = budget-< (u x' n) (l x n) d (δ n) h₃

      s' : u x' n + neg (l x n) < neg (δ n) + d
      s' = subst (λ z → u x' n + neg (l x n) < z) (+-comm d (neg (δ n))) s

      lhs : u (x' -ℝ x) n ≡ u x' n + neg (l x n)
      lhs = trans (u-hom x' (negℝ x) n) (cong (u x' n +_) (u-neg x n))

      rhs : l (embedℚ d) n ≡ neg (δ n) + d
      rhs = l-dyadic d n
  in n , subst₂ (λ p q → p < q) (sym lhs) (sym rhs) s'

------------------------------------------------------------------------
-- Negated absolute value lies below the number
--
-- 负的绝对值落在数之下

-- The negated absolute value of p lies below p.
--
-- p 的负绝对值落在 p 之下。
neg-abs≤ : (p : ℚ) → neg ∣ p ∣ ≤ p
neg-abs≤ p =
  subst (λ z → neg ∣ p ∣ ≤ z) (neg-involutive p)
    (neg-antimono-≤ (-r≤|r| p))

-- A dominating absolute bound gives a negated lower bound.
--
-- 占优的绝对值界给出取负后的下界。
neg≤-of-abs : (p C : ℚ) → ∣ p ∣ ≤ C → neg C ≤ p
neg≤-of-abs p C h =
  ≤-trans (neg-antimono-≤ h) (neg-abs≤ p)

------------------------------------------------------------------------
-- An absolute difference gives a two-sided bracket
--
-- 绝对差给出双侧夹逼

-- An absolute difference yields a two-sided bracket.
--
-- 绝对差给出双侧夹逼。
abs-diff-bounds :
  (p q d : ℚ) → ∣ p - q ∣ ≤ d → (p - d ≤ q) × (q ≤ p + d)
abs-diff-bounds p q d h =
  let h1 : p - q ≤ d
      h1 = ≤-trans (r≤|r| (p - q)) h

      h2 : neg d ≤ p - q
      h2 = ≤-trans (neg-antimono-≤ h) (neg-abs≤ (p - q))

      lo : p - d ≤ q
      lo = shift-bound p q d h1

      qp : q - p ≤ d
      qp = subst (λ z → z ≤ d) (negsub p q)
             (subst (λ z → neg (p - q) ≤ z) (neg-involutive d)
               (neg-antimono-≤ h2))

      hi : q ≤ p + d
      hi = sub-left-≤ q p d qp
  in lo , hi

------------------------------------------------------------------------
-- A shifted endpoint stays inside the enlarged bound
--
-- 平移后的端点仍落在放大的界内

-- A shifted endpoint stays inside the enlarged bound.
--
-- 平移后的端点仍落在放大的界内。
shift-abs :
  (M d lx ux lx' ux' a : ℚ) →
  ∣ lx ∣ ≤ M → ∣ ux ∣ ≤ M →
  lx - d ≤ lx' → ux' ≤ ux + d →
  lx' ≤ a → a ≤ ux' →
  ∣ a ∣ ≤ M + d
shift-abs M d lx ux lx' ux' a
  lx≤M ux≤M ll uu la au =
  let lx≥ : neg M ≤ lx
      lx≥ = neg≤-of-abs lx M lx≤M

      ux≤ : ux ≤ M
      ux≤ = ≤-trans (r≤|r| ux) ux≤M

      p1 : neg M + neg d ≤ lx + neg d
      p1 = +-mono-≤ lx≥ (≤-refl {neg d})

      p2 : neg (M + d) ≤ lx + neg d
      p2 = subst (λ z → z ≤ lx + neg d)
             (sym (neg-distrib-+ M d)) p1

      lo : neg (M + d) ≤ a
      lo = ≤-trans p2 (≤-trans ll la)

      hi1 : ux + d ≤ M + d
      hi1 = +-mono-≤ ux≤ (≤-refl {d})

      hi : a ≤ M + d
      hi = ≤-trans au (≤-trans uu hi1)
  in abs-from a (M + d) lo hi

------------------------------------------------------------------------
-- The two one-sided endpoint gaps
--
-- 两侧的端点间隙

-- On every level deeper than the neighbourhood's own witnesses, the
-- upper endpoint of x lies below the lower endpoint of x' plus the
-- radius, and vice versa.
--
-- 在比该邻域自身见证更深的每一层上，原区间的上端点低于邻近区间的下端点
-- 加半径，反向亦然。
close-endpoint-gaps :
  (d : ℚ) (x x' : RealI) → Close d x x' →
  Σ ℕ (λ m → ∀ k → m ≤ℕ k →
    (u x k - l x' k < d) × (u x' k - l x k < d))
close-endpoint-gaps d x x' h =
  let (m₁ , w₁) = proj₁ h
      (m₂ , w₂) = proj₂ h
      m = m₁ +ℕ m₂

      p₁ : (k : ℕ) → m ≤ℕ k → m₁ ≤ℕ k
      p₁ k hk = ℕP.≤-trans (ℕP.m≤m+n m₁ m₂) hk

      p₂ : (k : ℕ) → m ≤ℕ k → m₂ ≤ℕ k
      p₂ k hk = ℕP.≤-trans (subst (λ z → m₂ ≤ℕ z) (ℕP.+-comm m₂ m₁) (ℕP.m≤m+n m₂ m₁)) hk

      lx≤ux : (k : ℕ) → l x k ≤ u x k
      lx≤ux k = <⇒≤ (RealI.lo (node x k))

      lx'≤ux' : (k : ℕ) → l x' k ≤ u x' k
      lx'≤ux' k = <⇒≤ (RealI.lo (node x' k))

      up : (k : ℕ) → m ≤ℕ k → u x k - l x' k < d
      up k hk =
        node-diff-up d x x' m₁ w₁ k (p₁ k hk)
          (u x k) (l x' k) (lx≤ux k) (≤-refl {u x k})
          (≤-refl {l x' k}) (lx'≤ux' k)

      dn : (k : ℕ) → m ≤ℕ k → u x' k - l x k < d
      dn k hk =
        node-diff-down d x x' m₂ w₂ k (p₂ k hk)
          (l x k) (u x' k) (≤-refl {l x k}) (lx≤ux k)
          (lx'≤ux' k) (≤-refl {u x' k})
  in m , λ k hk → up k hk , dn k hk

------------------------------------------------------------------------
-- Absolute endpoint differences
--
-- 端点差的绝对值界

-- The same information as absolute values, which is the form the
-- product estimate consumes.
--
-- 同一信息写成绝对值形式，这正是乘积估计所需的形状。
close-endpoint-bounds :
  (d : ℚ) (x x' : RealI) → Close d x x' →
  Σ ℕ (λ m → ∀ k → m ≤ℕ k →
    ∣ l x k - l x' k ∣ ≤ d × ∣ u x k - u x' k ∣ ≤ d)
close-endpoint-bounds d x x' h =
  let (m , g) = close-endpoint-gaps d x x' h

      bound : (k : ℕ) → m ≤ℕ k →
        ∣ l x k - l x' k ∣ ≤ d × ∣ u x k - u x' k ∣ ≤ d
      bound k hk =
        let p = proj₁ (g k hk)
            q = proj₂ (g k hk)

            lx≤ux = <⇒≤ (RealI.lo (node x k))
            lx'≤ux' = <⇒≤ (RealI.lo (node x' k))

            u1 : u x k - u x' k ≤ u x k - l x' k
            u1 = sub-mono {a = u x k} {a' = u x k} {b = u x' k} {b' = l x' k}
                   (≤-refl {u x k}) lx'≤ux'

            u2 : u x k - u x' k ≤ d
            u2 = ≤-trans u1 (<⇒≤ p)

            v1 : u x' k - u x k ≤ u x' k - l x k
            v1 = sub-mono {a = u x' k} {a' = u x' k} {b = u x k} {b' = l x k}
                   (≤-refl {u x' k}) lx≤ux

            v2 : u x' k - u x k ≤ d
            v2 = ≤-trans v1 (<⇒≤ q)

            v3 : neg d ≤ neg (u x' k - u x k)
            v3 = neg-antimono-≤ v2

            v4 : neg d ≤ u x k - u x' k
            v4 = subst (λ z → neg d ≤ z) (negsub (u x' k) (u x k)) v3

            uAbs : ∣ u x k - u x' k ∣ ≤ d
            uAbs = abs-≤ v4 u2

            l1 : l x k - l x' k ≤ u x k - l x' k
            l1 = sub-mono {a = l x k} {a' = u x k} {b = l x' k} {b' = l x' k}
                   lx≤ux (≤-refl {l x' k})

            l2 : l x k - l x' k ≤ d
            l2 = ≤-trans l1 (<⇒≤ p)

            m1 : l x' k - l x k ≤ u x' k - l x k
            m1 = sub-mono {a = l x' k} {a' = u x' k} {b = l x k} {b' = l x k}
                   lx'≤ux' (≤-refl {l x k})

            m2 : l x' k - l x k ≤ d
            m2 = ≤-trans m1 (<⇒≤ q)

            m3 : neg d ≤ neg (l x' k - l x k)
            m3 = neg-antimono-≤ m2

            m4 : neg d ≤ l x k - l x' k
            m4 = subst (λ z → neg d ≤ z) (negsub (l x' k) (l x k)) m3

            lAbs : ∣ l x k - l x' k ∣ ≤ d
            lAbs = abs-≤ m4 l2
        in lAbs , uAbs
  in m , bound
