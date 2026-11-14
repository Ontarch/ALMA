------------------------------------------------------------------------
-- Base layer of the reciprocal chain
--
-- 倒数链的底座
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module Real.Interval.ContinuityRecipBasic where

open import Data.Empty using (⊥-elim)
open import Data.Nat using (ℕ; suc) renaming (_*_ to _*ℕ_; _≤_ to _≤ℕ_)
open import Data.Nat.Properties as ℕP using (n≤1+n)
  renaming (≤-trans to ≤ℕ-trans; <⇒≤ to <⇒≤ℕ)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Rational using
  (ℚ; 0ℚ; 1ℚ; _+_; _-_; -_; _*_; _≤_; _<_; ∣_∣; NonZero; Positive; positive
  ; _⊓_)
open import Data.Rational.Base using (1/_; nonNegative)
open import Data.Rational.Properties using
  (neg-antimono-≤; pos⇒nonZero; positive⁻¹; 1/pos⇒pos; pos*pos⇒pos; <⇒≤
  ; ≤-trans; ≤-refl; ≤-reflexive; *-comm; *-identityˡ; *-identityʳ
  ; *-distribʳ-+; +-assoc; +-comm; +-inverseʳ; +-identityʳ; +-mono-≤
  ; *-monoˡ-≤-nonNeg; *-monoʳ-≤-nonNeg; ⊓-sel; p⊓q≤p; p⊓q≤q; ≤-<-trans
  ; <-trans; <-irrefl; *-cancelˡ-<-nonNeg; ∣p*q∣≡∣p∣*∣q∣; 0≤p⇒∣p∣≡p
  ; 0≤∣p∣)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.Definitions using (tri<; tri≈; tri>)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; sym; trans; cong; subst; module ≡-Reasoning)
open ≡-Reasoning

open import Base.RationalRing using (0<1)
open import Real using
  (ε; 0<ε; CauchySeq; half; embed; 0≤embed; embed-mono-≤; embed-*-hom)
open CauchySeq renaming (f to seq-f; μ to seq-μ)
open import Real.CauchyToInterval using (M; K; K≥k; μ≤M; node-go; cauchy→realI)
open import Real.IntervalEquiv using
  (l; u; width; 1≤embed-suc; centre; centre-l; centre-u; centre-diff; bound-w
  ; realI→cauchy; μx-dom)
open import Real.Interval using (RealI; δ; δ-pos; double-half)
open import Real.Interval.Arith using (0ℝ)
open import Real.Interval.Continuity using (Close; sub-add-cancel)
open import Real.Interval.ContinuityClose using (close-endpoint-bounds)
open import Real.Interval.ContinuityProdGap using (within)
open import Real.Interval.ContinuityProdBudget using (width-shift)
open import Real.Interval.ContinuityMul using (shift-bound; sub-left-≤)
open import Real.Interval.Kit using (recip-antitone; 0<embed2)
open import Real.Interval.Mul using (sub-monoˡ)
open import Real.Interval.Mul.Order using (u-dyadic-0)
open import Real.Interval.Order using (_<ℝ_)
open import Real.Interval.OrderLe using (sub-mono)
open import Real.Interval.Recip using
  (inv-sub; recip-modulus; recip-modulus-lower ; realI→posCauchy; recipCauchy)
open import Real.Interval.Reasoning using (begin≤_; _≈⟨_⟩_; _≤⟨_⟩_; _≤∎)

------------------------------------------------------------------------
-- Elementary subtraction moves
--
-- 初等减法变形

-- Moving a negated subtraction to the other side.
--
-- 把取负后的减项移到另一侧。
neg-sub : (a b d : ℚ) → - d ≤ a - b → b - d ≤ a
neg-sub a b d h =
  let s1 : - d + b ≤ (a - b) + b
      s1 = +-mono-≤ h ≤-refl
      s2 : - d + b ≤ a
      s2 = subst (λ z → - d + b ≤ z) (sub-add-cancel a b) s1
  in subst (λ z → z ≤ a) (+-comm (- d) b) s2

------------------------------------------------------------------------
-- The absolute endpoint bounds, inherited from the close pair
--
-- 端点绝对界，直接取自 close 对

-- Endpoint bounds from the two sides of a Close pair.
--
-- 由 Close 对两侧给出的端点绝对界。
close-abs :
  (d : ℚ) (x x' : RealI) → Close d x x' →
  Σ ℕ (λ m → ∀ t → m ≤ℕ t →
    ∣ l x t - l x' t ∣ ≤ d × ∣ u x t - u x' t ∣ ≤ d)
close-abs = close-endpoint-bounds

------------------------------------------------------------------------
-- Upper shifts of the two endpoints
--
-- 两对端点的上移界

-- The lower endpoint of the original interval is at most the nearby one
-- plus the radius.
--
-- 原区间的下端点不超过邻近区间的下端点加半径。
l-shift-upper :
  (d : ℚ) (x x' : RealI) (m : ℕ) →
  (∀ t → m ≤ℕ t → ∣ l x t - l x' t ∣ ≤ d) →
  ∀ t → m ≤ℕ t → l x t ≤ l x' t + d
l-shift-upper d x x' m hl t mt =
  let a = l x t; b = l x' t
      hi = proj₂ (within (a - b) d (hl t mt))
  in sub-left-≤ a b d hi

-- The upper endpoint of the nearby interval is at most the original one
-- plus the radius.
--
-- 邻近区间的上端点不超过原区间的上端点加半径。
u-shift-upper :
  (d : ℚ) (x x' : RealI) (m : ℕ) →
  (∀ t → m ≤ℕ t → ∣ u x t - u x' t ∣ ≤ d) →
  ∀ t → m ≤ℕ t → u x' t ≤ u x t + d
u-shift-upper d x x' m hu t mt =
  let a = u x t; b = u x' t
      lo = proj₁ (within (a - b) d (hu t mt))
      h1 = neg-sub a b d lo
      h2 : (b - d) + d ≤ a + d
      h2 = +-mono-≤ h1 ≤-refl
  in subst (λ z → z ≤ a + d) (sub-add-cancel b d) h2

------------------------------------------------------------------------
-- Width transfer under a close pair
--
-- close 对之下的宽度传递

-- The width of the nearby interval exceeds the original width by at
-- most twice the radius.
--
-- 邻近区间的宽度最多比原宽度多出两倍半径。
width-near :
  (d : ℚ) (x x' : RealI) (m : ℕ) →
  (∀ t → m ≤ℕ t → ∣ l x t - l x' t ∣ ≤ d × ∣ u x t - u x' t ∣ ≤ d) →
  ∀ t → m ≤ℕ t → width x' t ≤ width x t + (d + d)
width-near d x x' m h t mt =
  let hi : u x' t ≤ u x t + d
      hi = u-shift-upper d x x' m (λ s ms → proj₂ (h s ms)) t mt
      lo : l x t ≤ l x' t + d
      lo = l-shift-upper d x x' m (λ s ms → proj₁ (h s ms)) t mt
  in width-shift (l x t) (u x t) (l x' t) (u x' t) d hi lo

------------------------------------------------------------------------
-- Lower endpoint of the second interval, shifted down by d
--
-- 第二个区间下端点的下移界

-- The lower endpoint of the original interval, shifted down by the
-- radius, stays below the nearby lower endpoint.
--
-- 原区间的下端点下移半径后仍不超过邻近的下端点。
l-near-lower :
  (d : ℚ) (x x' : RealI) (m : ℕ) →
  (∀ t → m ≤ℕ t → ∣ l x t - l x' t ∣ ≤ d) →
  ∀ t → m ≤ℕ t → l x t - d ≤ l x' t
l-near-lower d x x' m hl t mt =
  let a = l x t; b = l x' t
      hi = proj₂ (within (a - b) d (hl t mt))
  in shift-bound a b d hi

------------------------------------------------------------------------
-- Adding a fixed rational on one side
--
-- 单侧同加一个固定有理数

-- Adding the same rational on the right preserves order.
--
-- 右侧同加一个有理数保持序。
add-right : (a c d : ℚ) → c ≤ d → a + c ≤ a + d
add-right a c d h = +-mono-≤ {x = a} {y = a} {u = c} {v = d} ≤-refl h

-- Adding the same rational on the left preserves order.
--
-- 左侧同加一个有理数保持序。
add-left : (a b c : ℚ) → a ≤ b → a + c ≤ b + c
add-left a b c h = +-mono-≤ {x = a} {y = b} {u = c} {v = c} h ≤-refl

------------------------------------------------------------------------
-- Monotonicity of subtraction
--
-- 减法的单调性

-- Subtracting a larger term on the right makes the result smaller.
--
-- 右侧减去更大的项会使结果更小。
sub-le-right : (a c d : ℚ) → d ≤ c → a - c ≤ a - d
sub-le-right a c d h = add-right a (- c) (- d) (neg-antimono-≤ h)

-- Regrouping an addition on the left of a subtraction.
--
-- 减法左侧的加法重排。
sub-add-right : (a b d : ℚ) → (a + d) - b ≡ (a - b) + d
sub-add-right a b d = begin
  (a + d) - b
    ≡⟨ +-assoc a d (- b) ⟩
  a + (d + (- b))
    ≡⟨ cong (a +_) (+-comm d (- b)) ⟩
  a + (- b + d)
    ≡⟨ sym (+-assoc a (- b) d) ⟩
  (a - b) + d
  ∎

------------------------------------------------------------------------
-- Same level: the centre of x moves by at most width x' + d
--
-- 同层：x 的中心移动不超过 width x' + d

-- Upper bound for the centre shift at a single level.
--
-- 同层中心移动的上界。
centre-gap-upper :
  (d W : ℚ) (x x' : RealI) (m : ℕ) →
  u x m ≤ u x' m + d → width x' m ≤ W →
  centre x m ≤ centre x' m + (W + d)
centre-gap-upper d W x x' m hu hW =
  let step1 : centre x m - centre x' m ≤ u x m - l x' m
      step1 = sub-mono {a = centre x m} {a' = u x m} {b = centre x' m} {b' = l x' m}
                (centre-u x m) (centre-l x' m)
      step2 : u x m - l x' m ≤ (u x' m + d) - l x' m
      step2 = sub-monoˡ {a = u x m} {b = u x' m + d} {c = l x' m} hu
      step3 : (u x' m + d) - l x' m ≡ width x' m + d
      step3 = sub-add-right (u x' m) (l x' m) d
      step4 : width x' m + d ≤ W + d
      step4 = add-left (width x' m) W d hW
      chain : centre x m - centre x' m ≤ W + d
      chain = ≤-trans step1 (≤-trans step2 (≤-trans (≤-reflexive step3) step4))
  in sub-left-≤ (centre x m) (centre x' m) (W + d) chain

-- Lower bound for the centre shift at a single level.
--
-- 同层中心移动的下界。
centre-gap-lower :
  (d W : ℚ) (x x' : RealI) (m : ℕ) →
  u x' m ≤ u x m + d → width x m ≤ W →
  centre x' m ≤ centre x m + (W + d)
centre-gap-lower d W x x' m hu hW =
  let step1 : centre x' m - centre x m ≤ u x' m - l x m
      step1 = sub-mono {a = centre x' m} {a' = u x' m} {b = centre x m} {b' = l x m}
                (centre-u x' m) (centre-l x m)
      step2 : u x' m - l x m ≤ (u x m + d) - l x m
      step2 = sub-monoˡ {a = u x' m} {b = u x m + d} {c = l x m} hu
      step3 : (u x m + d) - l x m ≡ width x m + d
      step3 = sub-add-right (u x m) (l x m) d
      step4 : width x m + d ≤ W + d
      step4 = add-left (width x m) W d hW
      chain : centre x' m - centre x m ≤ W + d
      chain = ≤-trans step1 (≤-trans step2 (≤-trans (≤-reflexive step3) step4))
  in sub-left-≤ (centre x' m) (centre x m) (W + d) chain

------------------------------------------------------------------------
-- Cross level: centres sampled at different levels
--
-- 跨层：两个中心在不同层上采样

-- Upper bound for cross-level centre shifts.
--
-- 跨层中心移动的上界。
centre-cross-upper :
  (d Wx Wx' : ℚ) (x x' : RealI) (nu nu' q : ℕ) →
  nu ≤ℕ q → nu' ≤ℕ q →
  width x nu ≤ Wx → width x' q ≤ Wx' → width x' nu' ≤ Wx' →
  u x q ≤ u x' q + d →
  centre x nu ≤ centre x' nu' + (Wx' + ((Wx' + d) + Wx))
centre-cross-upper d Wx Wx' x x' nu nu' q nu≤q nu'≤q hx hxq hxu hu =
  let hA1 : centre x nu ≤ centre x q + width x nu
      hA1 = sub-left-≤ (centre x nu) (centre x q) (width x nu)
              (proj₂ (within (centre x nu - centre x q) (width x nu)
                        (centre-diff x nu nu q ℕP.≤-refl nu≤q)))
      hA2 : centre x q + width x nu ≤ centre x q + Wx
      hA2 = add-right (centre x q) (width x nu) Wx hx
      hA : centre x nu ≤ centre x q + Wx
      hA = ≤-trans hA1 hA2
      hB : centre x q ≤ centre x' q + (Wx' + d)
      hB = centre-gap-upper d Wx' x x' q hu hxq
      hC1 : centre x' q ≤ centre x' nu' + width x' nu'
      hC1 = sub-left-≤ (centre x' q) (centre x' nu') (width x' nu')
              (proj₂ (within (centre x' q - centre x' nu') (width x' nu')
                        (centre-diff x' nu' q nu' nu'≤q ℕP.≤-refl)))
      hC2 : centre x' nu' + width x' nu' ≤ centre x' nu' + Wx'
      hC2 = add-right (centre x' nu') (width x' nu') Wx' hxu
      hC : centre x' q ≤ centre x' nu' + Wx'
      hC = ≤-trans hC1 hC2
      hC' : centre x' q + (Wx' + d) ≤ (centre x' nu' + Wx') + (Wx' + d)
      hC' = add-left (centre x' q) (centre x' nu' + Wx') (Wx' + d) hC
  in begin≤ centre x nu
       ≤⟨ hA ⟩
         centre x q + Wx
       ≤⟨ add-left (centre x q) (centre x' q + (Wx' + d)) Wx hB ⟩
         (centre x' q + (Wx' + d)) + Wx
       ≤⟨ add-left (centre x' q + (Wx' + d)) ((centre x' nu' + Wx') + (Wx' + d)) Wx hC' ⟩
         ((centre x' nu' + Wx') + (Wx' + d)) + Wx
       ≈⟨ +-assoc (centre x' nu' + Wx') (Wx' + d) Wx ⟩
         (centre x' nu' + Wx') + ((Wx' + d) + Wx)
       ≈⟨ +-assoc (centre x' nu') Wx' ((Wx' + d) + Wx) ⟩
         centre x' nu' + (Wx' + ((Wx' + d) + Wx))
       ≤∎

-- Lower bound for cross-level centre shifts.
--
-- 跨层中心移动的下界。
centre-cross-lower :
  (d Wx Wx' : ℚ) (x x' : RealI) (nu nu' q : ℕ) →
  nu ≤ℕ q → nu' ≤ℕ q →
  width x q ≤ Wx → width x nu ≤ Wx → width x' nu' ≤ Wx' →
  u x' q ≤ u x q + d →
  centre x' nu' ≤ centre x nu + (Wx + ((Wx + d) + Wx'))
centre-cross-lower d Wx Wx' x x' nu nu' q nu≤q nu'≤q hxq hx hxu hu =
  let hA1 : centre x' nu' ≤ centre x' q + width x' nu'
      hA1 = sub-left-≤ (centre x' nu') (centre x' q) (width x' nu')
              (proj₂ (within (centre x' nu' - centre x' q) (width x' nu')
                        (centre-diff x' nu' nu' q ℕP.≤-refl nu'≤q)))
      hA2 : centre x' q + width x' nu' ≤ centre x' q + Wx'
      hA2 = add-right (centre x' q) (width x' nu') Wx' hxu
      hA : centre x' nu' ≤ centre x' q + Wx'
      hA = ≤-trans hA1 hA2
      hB : centre x' q ≤ centre x q + (Wx + d)
      hB = centre-gap-lower d Wx x x' q hu hxq
      hC1 : centre x q ≤ centre x nu + width x nu
      hC1 = sub-left-≤ (centre x q) (centre x nu) (width x nu)
              (proj₂ (within (centre x q - centre x nu) (width x nu)
                        (centre-diff x nu q nu nu≤q ℕP.≤-refl)))
      hC2 : centre x nu + width x nu ≤ centre x nu + Wx
      hC2 = add-right (centre x nu) (width x nu) Wx hx
      hC : centre x q ≤ centre x nu + Wx
      hC = ≤-trans hC1 hC2
      hC' : centre x q + (Wx + d) ≤ (centre x nu + Wx) + (Wx + d)
      hC' = add-left (centre x q) (centre x nu + Wx) (Wx + d) hC
  in begin≤ centre x' nu'
       ≤⟨ hA ⟩
         centre x' q + Wx'
       ≤⟨ add-left (centre x' q) (centre x q + (Wx + d)) Wx' hB ⟩
         (centre x q + (Wx + d)) + Wx'
       ≤⟨ add-left (centre x q + (Wx + d)) ((centre x nu + Wx) + (Wx + d)) Wx' hC' ⟩
         ((centre x nu + Wx) + (Wx + d)) + Wx'
       ≈⟨ +-assoc (centre x nu + Wx) (Wx + d) Wx' ⟩
         (centre x nu + Wx) + ((Wx + d) + Wx')
       ≈⟨ +-assoc (centre x nu) Wx ((Wx + d) + Wx') ⟩
         centre x nu + (Wx + ((Wx + d) + Wx'))
       ≤∎

------------------------------------------------------------------------
-- half is positive
--
-- half 为正

-- The embedding of two is positive.
--
-- 嵌入的二为正。
pos-embed2 : Positive (embed 2)
pos-embed2 = positive 0<embed2

-- The half is positive.
--
-- 半为正。
half-pos : Positive half
half-pos = 1/pos⇒pos (embed 2) {{pos-embed2}}

------------------------------------------------------------------------
-- The retained lower bound: the smaller of b / 2 and 1
--
-- 保留下来的下界：b / 2 与 1 中较小者

-- The retained lower bound.
--
-- 保留下来的下界。
c : ℚ → ℚ
c b = (b * half) ⊓ 1ℚ

-- A meet of two positive rationals is positive. The case analysis goes
-- through ⊓-sel, consumed by [_,_] so that Agda does not abstract the
-- goal (which would erase the very equation we need).
--
-- 两个正有理数的交为正。分情况走 ⊓-sel，并用 [_,_] 消去，避免 Agda
-- 抽象目标而把所需的等式抹掉。
pos-meet : (p q : ℚ) → 0ℚ < p → 0ℚ < q → 0ℚ < p ⊓ q
pos-meet p q 0p 0q = h (⊓-sel p q)
  where
    h : p ⊓ q ≡ p ⊎ p ⊓ q ≡ q → 0ℚ < p ⊓ q
    h (inj₁ e) = subst (λ z → 0ℚ < z) (sym e) 0p
    h (inj₂ e) = subst (λ z → 0ℚ < z) (sym e) 0q

-- The retained lower bound is positive.
--
-- 保留下来的下界为正。
0<c : (b : ℚ) → 0ℚ < b → 0ℚ < c b
0<c b 0<b = pos-meet (b * half) 1ℚ hb 0<1
  where
    hb : 0ℚ < b * half
    hb = positive⁻¹ (b * half)
           {{pos*pos⇒pos b {{positive 0<b}} half {{half-pos}}}}

-- The retained lower bound is nonnegative.
--
-- 保留下来的下界非负。
0≤c : (b : ℚ) → 0ℚ < b → 0ℚ ≤ c b
0≤c b 0<b = <⇒≤ (0<c b 0<b)

-- The retained lower bound is at most b * half.
--
-- 保留下来的下界不超过 b * half。
c≤bhalf : (b : ℚ) → c b ≤ b * half
c≤bhalf b = p⊓q≤p (b * half) 1ℚ

-- The retained lower bound is at most one.
--
-- 保留下来的下界不超过一。
c≤1 : (b : ℚ) → c b ≤ 1ℚ
c≤1 b = p⊓q≤q (b * half) 1ℚ

-- The retained bound plus itself is at most the original bound.
--
-- 保留下来的下界加上自己，仍不超过原下界。
c+c≤b : (b : ℚ) → c b + c b ≤ b
c+c≤b b =
  let h1 : c b + c b ≤ b * half + b * half
      h1 = +-mono-≤ {x = c b} {y = b * half} {u = c b} {v = b * half}
             (c≤bhalf b) (c≤bhalf b)
      h2 : b * half + b * half ≡ b
      h2 = begin
        b * half + b * half
          ≡⟨ sym (*-distribʳ-+ half b b) ⟩
        (b + b) * half
          ≡⟨ double-half b ⟩
        b
        ∎
  in ≤-trans h1 (≤-reflexive h2)

-- c is still below b minus c.
--
-- c 仍不超过 b 减 c。
c≤b-c : (b : ℚ) → c b ≤ b - c b
c≤b-c b =
  let step1 : (c b + c b) - c b ≤ b - c b
      step1 = sub-monoˡ {a = c b + c b} {b = b} {c = c b} (c+c≤b b)
      step2 : (c b + c b) - c b ≡ c b
      step2 = begin
        (c b + c b) - c b
          ≡⟨ refl ⟩
        (c b + c b) + (- c b)
          ≡⟨ +-assoc (c b) (c b) (- c b) ⟩
        c b + (c b + (- c b))
          ≡⟨ cong (c b +_) (+-inverseʳ (c b)) ⟩
        c b + 0ℚ
          ≡⟨ +-identityʳ (c b) ⟩
        c b
        ∎
  in ≤-trans (≤-reflexive (sym step2)) step1

------------------------------------------------------------------------
-- The k-th precision is at most one
--
-- 第 k 层精度不超过一

-- One divided by one is one.
--
-- 一除以一等于一。
1/1≡1 : 1/ 1ℚ ≡ 1ℚ
1/1≡1 = refl

-- The k-th precision is at most one.
--
-- 第 k 层精度不超过一。
ε≤1 : (k : ℕ) → ε k ≤ 1ℚ
ε≤1 k =
  subst (λ z → ε k ≤ z) (sym 1/1≡1)
        (recip-antitone {a = 1ℚ} {b = embed (suc k)} 0<1 (1≤embed-suc k))

------------------------------------------------------------------------
-- Slack: proportional to c squared, at most c
--
-- 松弛量：与 c 的平方成正比，且不超过 c

-- The product of two precisions is at most one.
--
-- 两个精度之积不超过一。
εk*ε9≤1 : (k : ℕ) → ε k * ε 9 ≤ 1ℚ
εk*ε9≤1 k =
  let q : ε k * ε 9 ≤ 1ℚ * ε 9
      q = *-monoʳ-≤-nonNeg (ε 9) {{nonNegative (<⇒≤ (0<ε 9))}} (ε≤1 k)
      q' : ε k * ε 9 ≤ ε 9
      q' = subst (λ z → ε k * ε 9 ≤ z) (*-identityˡ (ε 9)) q
  in ≤-trans q' (ε≤1 9)

-- The slack for the retained bound.
--
-- 保留下界的松弛量。
slack : (b : ℚ) → ℕ → ℚ
slack b k = ((c b) * (c b)) * (ε k * ε 9)

-- The square of the retained bound is positive.
--
-- 保留下界的平方为正。
0<c*c : (b : ℚ) → 0ℚ < b → 0ℚ < c b * c b
0<c*c b 0<b =
  positive⁻¹ (c b * c b)
    {{pos*pos⇒pos (c b) {{positive (0<c b 0<b)}} (c b) {{positive (0<c b 0<b)}}}}

-- The slack is positive.
--
-- 松弛量为正。
0<slack : (b : ℚ) (k : ℕ) → 0ℚ < b → 0ℚ < slack b k
0<slack b k 0<b =
  positive⁻¹ ((c b * c b) * (ε k * ε 9))
    {{pos*pos⇒pos (c b * c b) {{positive (0<c*c b 0<b)}}
                   (ε k * ε 9)
                   {{pos*pos⇒pos (ε k) {{positive (0<ε k)}}
                                  (ε 9) {{positive (0<ε 9)}}}}}}

-- The slack is at most the retained bound.
--
-- 松弛量不超过保留下界。
slack≤c : (b : ℚ) (k : ℕ) → 0ℚ < b → slack b k ≤ c b
slack≤c b k 0<b =
  let h1 : (c b * c b) * (ε k * ε 9) ≤ (c b * c b) * 1ℚ
      h1 = *-monoˡ-≤-nonNeg (c b * c b)
             {{nonNegative (<⇒≤ (0<c*c b 0<b))}} (εk*ε9≤1 k)
      h2 : (c b * c b) * 1ℚ ≤ c b * c b
      h2 = ≤-reflexive (*-identityʳ (c b * c b))
      h3 : c b * c b ≤ c b * 1ℚ
      h3 = *-monoˡ-≤-nonNeg (c b) {{nonNegative (<⇒≤ (0<c b 0<b))}} (c≤1 b)
      h4 : c b * 1ℚ ≤ c b
      h4 = ≤-reflexive (*-identityʳ (c b))
  in ≤-trans h1 (≤-trans h2 (≤-trans h3 h4))

------------------------------------------------------------------------
-- A close x' keeps its lower bound above c
--
-- 邻近的 x' 下界仍高于 c

-- c is still below b minus the slack.
--
-- c 仍不超过 b 减去松弛量。
c≤b-slack : (b : ℚ) (k : ℕ) → 0ℚ < b → c b ≤ b - slack b k
c≤b-slack b k 0<b =
  let step1 : b - c b ≤ b - slack b k
      step1 = sub-le-right b (c b) (slack b k) (slack≤c b k 0<b)
  in ≤-trans (c≤b-c b) step1

------------------------------------------------------------------------
-- The gap, with the denominator kept as a product
--
-- 差界，分母保留为乘积形式

-- Bound on the difference of two reciprocals.
--
-- 两个倒数之差的界。
gap-abs :
  (A B W : ℚ) (0A : 0ℚ < A) (0B : 0ℚ < B) →
  ∣ B + - A ∣ ≤ W →
  ∣ (1/ A) {{pos⇒nonZero A {{positive 0A}}}}
    - (1/ B) {{pos⇒nonZero B {{positive 0B}}}} ∣
    ≤ W * (1/ (A * B))
        {{pos⇒nonZero (A * B)
            {{pos*pos⇒pos A {{positive 0A}} B {{positive 0B}}}}}}
gap-abs A B W 0A 0B hW =
  let nzA : NonZero A
      nzA = pos⇒nonZero A {{positive 0A}}
      nzB : NonZero B
      nzB = pos⇒nonZero B {{positive 0B}}
      AB-pos : Positive (A * B)
      AB-pos = pos*pos⇒pos A {{positive 0A}} B {{positive 0B}}
      nzAB : NonZero (A * B)
      nzAB = pos⇒nonZero (A * B) {{AB-pos}}
      iP : ℚ
      iP = (1/ (A * B)) {{nzAB}}
      iP-pos : Positive iP
      iP-pos = 1/pos⇒pos (A * B) {{AB-pos}}
      0≤iP : 0ℚ ≤ iP
      0≤iP = <⇒≤ (positive⁻¹ iP {{iP-pos}})
      e1 : (1/ A) {{nzA}} - (1/ B) {{nzB}} ≡ (B + - A) * iP
      e1 = inv-sub A B {{nzA}} {{nzB}} {{nzAB}}
      e2 : ∣ (1/ A) {{nzA}} - (1/ B) {{nzB}} ∣ ≡ ∣ B + - A ∣ * ∣ iP ∣
      e2 = trans (cong ∣_∣ e1) (∣p*q∣≡∣p∣*∣q∣ (B + - A) iP)
      e3 : ∣ B + - A ∣ * ∣ iP ∣ ≡ ∣ B + - A ∣ * iP
      e3 = cong (∣ B + - A ∣ *_) (0≤p⇒∣p∣≡p 0≤iP)
      e4 : ∣ B + - A ∣ * iP ≤ W * iP
      e4 = *-monoʳ-≤-nonNeg iP {{nonNegative 0≤iP}} hW
  in subst (λ z → z ≤ W * iP) (sym (trans e2 e3)) e4

------------------------------------------------------------------------
-- The gap, with the denominator reduced to a square
--
-- 差界，把分母降到平方形式

-- Bound on the difference of two reciprocals, with a smaller
-- denominator.
--
-- 用更小分母给出的倒数差界。
gap-c :
  (A B c W : ℚ) (0A : 0ℚ < A) (0B : 0ℚ < B) (0c : 0ℚ < c) →
  c ≤ A → c ≤ B → ∣ B + - A ∣ ≤ W →
  ∣ (1/ A) {{pos⇒nonZero A {{positive 0A}}}}
    - (1/ B) {{pos⇒nonZero B {{positive 0B}}}} ∣
    ≤ W * (1/ (c * c))
        {{pos⇒nonZero (c * c)
            {{pos*pos⇒pos c {{positive 0c}} c {{positive 0c}}}}}}
gap-c A B c W 0A 0B 0c c≤A c≤B hW =
  let AB-pos : Positive (A * B)
      AB-pos = pos*pos⇒pos A {{positive 0A}} B {{positive 0B}}
      nzAB : NonZero (A * B)
      nzAB = pos⇒nonZero (A * B) {{AB-pos}}
      cc-pos : Positive (c * c)
      cc-pos = pos*pos⇒pos c {{positive 0c}} c {{positive 0c}}
      nzcc : NonZero (c * c)
      nzcc = pos⇒nonZero (c * c) {{cc-pos}}
      iP : ℚ
      iP = (1/ (A * B)) {{nzAB}}
      iC : ℚ
      iC = (1/ (c * c)) {{nzcc}}
      s1 : c * c ≤ c * B
      s1 = *-monoˡ-≤-nonNeg c {{nonNegative (<⇒≤ 0c)}} c≤B
      s2 : c * B ≤ A * B
      s2 = *-monoʳ-≤-nonNeg B {{nonNegative (<⇒≤ 0B)}} c≤A
      cc≤AB : c * c ≤ A * B
      cc≤AB = ≤-trans s1 s2
      mono : iP ≤ iC
      mono = recip-antitone {a = c * c} {b = A * B}
               (positive⁻¹ (c * c) {{cc-pos}}) cc≤AB
      W-nn : 0ℚ ≤ W
      W-nn = ≤-trans (0≤∣p∣ (B + - A)) hW
  in ≤-trans (gap-abs A B W 0A 0B hW)
       (*-monoˡ-≤-nonNeg W {{nonNegative W-nn}} mono)

------------------------------------------------------------------------
-- Node formulas
--
-- 节点公式

-- Lower endpoint formula.
--
-- 下端点公式。
l-cauchy→realI : (cs : CauchySeq) (n : ℕ) →
  l (cauchy→realI cs) n ≡ seq-f cs (M cs n) - δ n
l-cauchy→realI cs n = cong RealI.l (node-go cs n)

-- Upper endpoint formula.
--
-- 上端点公式。
u-cauchy→realI : (cs : CauchySeq) (n : ℕ) →
  u (cauchy→realI cs) n ≡ seq-f cs (M cs n) + δ n
u-cauchy→realI cs n = cong RealI.u (node-go cs n)

------------------------------------------------------------------------
-- Squares of positive rationals are positive
--
-- 正有理数的平方为正

-- The square of a positive rational is positive.
--
-- 正有理数的平方为正。
0<b*b : (b : ℚ) → 0ℚ < b → 0ℚ < b * b
0<b*b b b>0 =
  positive⁻¹ (b * b) {{pos*pos⇒pos b {{positive b>0}} b {{positive b>0}}}}

------------------------------------------------------------------------
-- A natural index above the square
--
-- 一个不小于平方的自然数下标

-- A natural number bounding the square from above.
--
-- 从上方界住平方的自然数。
Bsq-index : (b : ℚ) → 0ℚ < b → ℕ
Bsq-index b 0<b = proj₁ (bound-w (b * b) (<⇒≤ (0<b*b b 0<b)))

------------------------------------------------------------------------
-- Reflecting a strict embedding inequality at successor
--
-- 严格嵌入不等式反向给出自然数不等式

-- embed N < embed (suc M) gives N ≤ M.
--
-- 严格嵌入不等式反向给出自然数不等式。
≤-from-embed-< : (N M : ℕ) → embed N < embed (suc M) → N ≤ℕ M
≤-from-embed-< N M h with ℕP.<-cmp N M
... | tri< N<M _ _ = <⇒≤ℕ N<M
... | tri≈ p q r = ℕP.≤-reflexive q
... | tri> _ _ M<N =
      ⊥-elim (<-irrefl refl (≤-<-trans (embed-mono-≤ M<N) h))

------------------------------------------------------------------------
-- Growth of the reciprocal modulus
--
-- 倒数模数的增长

-- If i is past the threshold, then the reciprocal modulus at i is at
-- least the prescribed natural number.
--
-- 越过相应阈值后，倒数模数至少达到指定自然数。
recip-modulus-grow :
  (b : ℚ) (0<b : 0ℚ < b) (N i : ℕ) →
  (N *ℕ Bsq-index b 0<b) ≤ℕ i →
  N ≤ℕ recip-modulus b 0<b i
recip-modulus-grow b 0<b N i thresh =
  let bsq = b * b
      B = Bsq-index b 0<b
      bsq≤eB : bsq ≤ embed B
      bsq≤eB = proj₂ (bound-w bsq (<⇒≤ (0<b*b b 0<b)))
      h1 : embed N * bsq ≤ embed N * embed B
      h1 = *-monoˡ-≤-nonNeg (embed N) {{nonNegative (0≤embed N)}} bsq≤eB
      h2 : embed N * bsq ≤ embed (N *ℕ B)
      h2 = ≤-trans h1 (≤-reflexive (sym (embed-*-hom N B)))
      h3 : embed (N *ℕ B) ≤ embed i
      h3 = embed-mono-≤ thresh
      h4 : embed i ≤ embed (suc i)
      h4 = embed-mono-≤ (n≤1+n i)
      lo : embed N * bsq ≤ embed (suc i)
      lo = ≤-trans h2 (≤-trans h3 h4)
      M' = recip-modulus b 0<b i
      hi : embed (suc i) < bsq * embed (suc M')
      hi = recip-modulus-lower b 0<b i
      mid : embed N * bsq < bsq * embed (suc M')
      mid = ≤-<-trans lo hi
      comm : bsq * embed N < bsq * embed (suc M')
      comm = subst (λ z → z < bsq * embed (suc M')) (*-comm (embed N) bsq) mid
      cancel : embed N < embed (suc M')
      cancel = *-cancelˡ-<-nonNeg bsq {{nonNegative (<⇒≤ (0<b*b b 0<b))}} comm
      N≤M' : N ≤ℕ M'
      N≤M' = ≤-from-embed-< N M' cancel
  in N≤M'

------------------------------------------------------------------------
-- Deep sampling index for the reciprocal sequence
--
-- 倒数序列的深采样下标

-- The sampling index of the reciprocal sequence can be made arbitrarily
-- large, which is what the endpoint estimates need.
--
-- 倒数序列的采样下标可以任意大，这正是端点估计所需。
M-recip-grow :
  (x : RealI) (0<x : 0ℝ <ℝ x) (N : ℕ) →
  Σ ℕ (λ n → N ≤ℕ M (recipCauchy (realI→posCauchy x 0<x)) n)
M-recip-grow x 0<x N =
  let n₀ = proj₁ 0<x
      b = l x n₀
      0<b : 0ℚ < l x n₀
      0<b = <-trans (δ-pos n₀)
              (subst (λ z → z < l x n₀) (u-dyadic-0 n₀) (proj₂ 0<x))
      cs = recipCauchy (realI→posCauchy x 0<x)
      n = N *ℕ Bsq-index b 0<b
      Kn≥ : (N *ℕ Bsq-index b 0<b) ≤ℕ K n
      Kn≥ = K≥k n
      g1 : N ≤ℕ recip-modulus b 0<b (K n)
      g1 = recip-modulus-grow b 0<b N (K n) Kn≥
      g2 : recip-modulus b 0<b (K n) ≤ℕ seq-μ (realI→cauchy x) (recip-modulus b 0<b (K n))
      g2 = μx-dom x (recip-modulus b 0<b (K n))
      g3 : seq-μ cs (K n) ≤ℕ M cs n
      g3 = μ≤M cs n
  in n , ≤ℕ-trans g1 (≤ℕ-trans g2 g3)
