------------------------------------------------------------------------
-- Infimum (greatest lower bound)
--
-- 下确界（最大下界）
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module Real.Interval.Infimum where

open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Rational using (ℚ; _-_; _<_; ∣_∣) renaming (-_ to neg)
open import Data.Rational.Properties using
  (neg-antimono-<; neg-distrib-+; ∣-p∣≡∣p∣)
open import Relation.Binary.PropositionalEquality using
  (_≡_; cong; cong₂; sym; subst; module ≡-Reasoning)
open ≡-Reasoning
open import Function.Base using (case_of_)

open import Real.Interval using (RealI; embedℚ)
open import Real.Interval.Arith using (negℝ)
open import Real.Interval.Equiv using (_≈ℝ_; ≈ℝ-sym; ≈ℝ-refl; ≈ℝ-trans)
open import Real.Interval.Order using (_<ℝ_)
open import Real.Interval.OrderComplete.Base using
  (Subset; Located; Upper; Occupied; _≤ℝ_)
open import Real.Interval.OrderComplete using (order-complete)
open import Real.Interval.OrderLaws using (≈-<-resp; <-neg)
open import Real.Interval.Mul.Order using (≈-<-respʳ)
open import Real.Interval.OrderLe using (≤ℝ-trans; ≈⇒≤ℝ; ≤ℝ-resp-≈)
open import Real.Interval.ArithLaws using (negℝ-negℝ)
open import Real.Interval.Embed using (embedℚ-neg)
open import Real.IntervalEquiv using (centre)
open import Real.Interval.Node using (centre-neg)
open import Real using (ε)

------------------------------------------------------------------------
-- Reflected subset
--
-- 反射子集

reflect : Subset → Subset
reflect P y = Σ RealI λ x → P x × (y ≈ℝ negℝ x)

-- A member x of P gives the member neg x of reflect P.
--
-- P 的成员经取负成为反射集的成员。
reflect-member : {P : Subset} {x : RealI} → P x → reflect P (negℝ x)
reflect-member {P} {x} px = x , px , ≈ℝ-refl

------------------------------------------------------------------------
-- Negation respects equivalence
--
-- 取负尊重等价

-- Rational helper: the difference of two negations is the negation of
-- the difference.
--
-- 有理辅助：两个取负之差等于差的取负。
neg-diff : (p q : ℚ) → neg p - neg q ≡ neg (p - q)
neg-diff p q = sym (neg-distrib-+ p (neg q))

-- Negation respects _≈ℝ_: the centres are negated, and the absolute
-- difference is unchanged, so the same witness from a ≈ b applies.
--
-- 取负尊重 _≈ℝ_：中心被取负，而绝对差不变，故同一见证仍然成立。
negℝ-cong : {a b : RealI} → a ≈ℝ b → negℝ a ≈ℝ negℝ b
negℝ-cong {a} {b} a≈b k =
  let N , h = a≈b k
  in N , λ n n≥N →
    let eq : ∣ centre (negℝ a) n - centre (negℝ b) n ∣
             ≡ ∣ centre a n - centre b n ∣
        eq =
          begin
            ∣ centre (negℝ a) n - centre (negℝ b) n ∣
              ≡⟨ cong₂ (λ p q → ∣ p - q ∣)
                       (centre-neg a n) (centre-neg b n) ⟩
            ∣ neg (centre a n) - neg (centre b n) ∣
              ≡⟨ cong ∣_∣ (neg-diff (centre a n) (centre b n)) ⟩
            ∣ neg (centre a n - centre b n) ∣
              ≡⟨ ∣-p∣≡∣p∣ (centre a n - centre b n) ⟩
            ∣ centre a n - centre b n ∣ ∎
    in subst (λ z → z < ε k) (sym eq) (h n n≥N)

------------------------------------------------------------------------
-- Lower locatedness
--
-- Lower P a          every member lies strictly above embed a
-- OccupiedBelow P b  some member lies strictly below embed b
-- LocatedBelow P     at each gap (p,q), either all members are above p
--                    or some member is below q
--
-- 下定位性
--
-- Lower          所有成员严格位于给定嵌入之上
-- OccupiedBelow  某个成员严格位于给定嵌入之下
-- LocatedBelow   在每个间隙处，要么所有成员位于左端之上，要么某个
--                成员位于右端之下

Lower : Subset → ℚ → Set
Lower P a = (x : RealI) → P x → embedℚ a <ℝ x

OccupiedBelow : Subset → ℚ → Set
OccupiedBelow P b = Σ RealI λ x → P x × (x <ℝ embedℚ b)

LocatedBelow : Subset → Set
LocatedBelow P = ∀ (p q : ℚ) → p < q → Lower P p ⊎ OccupiedBelow P q

------------------------------------------------------------------------
-- Order-reversing lemma for non-strict order
--
-- Negation reverses the non-strict order.
--
-- 非严格序的反序引理
--
-- 取负反转非严格序。

≤ℝ-neg : {x y : RealI} → x ≤ℝ y → negℝ y ≤ℝ negℝ x
≤ℝ-neg {x} {y} x≤y negx<negy =
  let step : negℝ (negℝ y) <ℝ negℝ (negℝ x)
      step = <-neg (negℝ x) (negℝ y) negx<negy
      y<x : y <ℝ x
      y<x =
        let a : y <ℝ negℝ (negℝ x)
            a = ≈-<-resp (negℝ-negℝ y) step
        in ≈-<-respʳ (negℝ-negℝ x) a
  in x≤y y<x

------------------------------------------------------------------------
-- Transfer of lower locatedness to the reflected set
--
-- 下定位性向反射集的转移

-- The double-negated rational embedding recovers the original
-- embedding.
--
-- 有理嵌入两次取负后回到原嵌入。
neg-emb-neg : (q : ℚ) → negℝ (embedℚ (neg q)) ≈ℝ embedℚ q
neg-emb-neg q = ≈ℝ-trans (negℝ-cong (embedℚ-neg q)) (negℝ-negℝ (embedℚ q))

-- A lower bound on the reflected side yields an upper bound on the
-- original side.
--
-- 下界条件在反射集上给出上界条件。
lower→upper : {P : Subset} {q : ℚ} →
  Lower P (neg q) → Upper (reflect P) q
lower→upper {P} {q} lw y (x , px , y≈negx) =
  let base : embedℚ (neg q) <ℝ x
      base = lw x px
      flipped : negℝ x <ℝ negℝ (embedℚ (neg q))
      flipped = <-neg (embedℚ (neg q)) x base
      negx<embq : negℝ x <ℝ embedℚ q
      negx<embq = ≈-<-respʳ (neg-emb-neg q) flipped
      y<embq : y <ℝ embedℚ q
      y<embq = ≈-<-resp (≈ℝ-sym y≈negx) negx<embq
  in y<embq

-- An occupied point below the reflected set yields an occupied point
-- above the reflected set.
--
-- 反射集下方的占据性对应反射集上方的占据性。
occbelow→occ : {P : Subset} {p : ℚ} →
  OccupiedBelow P (neg p) → Occupied (reflect P) p
occbelow→occ {P} {p} (x , px , x<enegp) =
  let y = negℝ x
      py : reflect P y
      py = reflect-member px
      flipped : negℝ (embedℚ (neg p)) <ℝ negℝ x
      flipped = <-neg x (embedℚ (neg p)) x<enegp
      embp<y : embedℚ p <ℝ y
      embp<y = ≈-<-resp (neg-emb-neg p) flipped
  in y , py , embp<y

-- Lower locatedness of the original set yields locatedness of the
-- reflected set.
--
-- 下定位性经反射后给出上定位性。
located-below→located : {P : Subset} →
  LocatedBelow P → Located (reflect P)
located-below→located {P} locb p q p<q =
  let s = locb (neg q) (neg p) (neg-antimono-< p<q)
  in case s of λ
       { (inj₁ lw) → inj₂ (lower→upper lw)
       ; (inj₂ ob) → inj₁ (occbelow→occ ob) }

------------------------------------------------------------------------
-- Infimum
--
-- 下确界

module _ {P : Subset} (locb : LocatedBelow P)
         {x₀ : RealI} (px₀ : P x₀)
         {l₀ : RealI} (isLower : (x : RealI) → P x → l₀ ≤ℝ x) where

  Q : Subset
  Q = reflect P

  locQ : Located Q
  locQ = located-below→located locb

  y₀ : RealI
  y₀ = negℝ x₀

  qy₀ : Q y₀
  qy₀ = reflect-member px₀

  u₀ : RealI
  u₀ = negℝ l₀

  -- The negated lower bound is an upper bound of the reflected set.
  --
  -- 取负后的下界是反射集的上界。
  upperQ : (y : RealI) → Q y → y ≤ℝ u₀
  upperQ y (x , px , y≈negx) =
    let l₀≤x : l₀ ≤ℝ x
        l₀≤x = isLower x px
        negx≤negl₀ : negℝ x ≤ℝ negℝ l₀
        negx≤negl₀ = ≤ℝ-neg l₀≤x
        y≤negx : y ≤ℝ negℝ x
        y≤negx = ≈⇒≤ℝ y≈negx
    in ≤ℝ-trans y≤negx negx≤negl₀

  -- Supremum of the reflected set.
  --
  -- 反射集的上确界。
  oc = order-complete {P = Q} locQ {y₀} qy₀ {u₀} upperQ

  s : RealI
  s = proj₁ oc

  s-upper : (y : RealI) → Q y → y ≤ℝ s
  s-upper = proj₁ (proj₂ oc)

  s-least : (y : RealI) → ((z : RealI) → Q z → z ≤ℝ y) → s ≤ℝ y
  s-least = proj₂ (proj₂ oc)

  inf : RealI
  inf = negℝ s

  -- The infimum is a lower bound: every member is at or above it.
  --
  -- 下确是下界：每个成员都不小于它。
  inf-lower : (x : RealI) → P x → inf ≤ℝ x
  inf-lower x px =
    let negx≤s : negℝ x ≤ℝ s
        negx≤s = s-upper (negℝ x) (reflect-member px)
        negs≤negnegx : negℝ s ≤ℝ negℝ (negℝ x)
        negs≤negnegx = ≤ℝ-neg negx≤s
    in ≤ℝ-resp-≈ (≈ℝ-refl) (negℝ-negℝ x) negs≤negnegx

  -- The infimum is greatest: any lower bound is at or below it.
  --
  -- 下确界最大：任意下界都不大于它。
  inf-greatest : (y : RealI) →
    ((x : RealI) → P x → y ≤ℝ x) → y ≤ℝ inf
  inf-greatest y lb =
    let upper-negy : (z : RealI) → Q z → z ≤ℝ negℝ y
        upper-negy z (x , px , z≈negx) =
          let y≤x : y ≤ℝ x
              y≤x = lb x px
              negx≤negy : negℝ x ≤ℝ negℝ y
              negx≤negy = ≤ℝ-neg y≤x
              z≤negx : z ≤ℝ negℝ x
              z≤negx = ≈⇒≤ℝ z≈negx
          in ≤ℝ-trans z≤negx negx≤negy
        s≤negy : s ≤ℝ negℝ y
        s≤negy = s-least (negℝ y) upper-negy
        negnegy≤negs : negℝ (negℝ y) ≤ℝ negℝ s
        negnegy≤negs = ≤ℝ-neg s≤negy
    in ≤ℝ-resp-≈ (negℝ-negℝ y) (≈ℝ-refl) negnegy≤negs

  ----------------------------------------------------------------------
  -- Infimum completeness
  --
  -- 下确界完备性

  inf-complete : Σ RealI λ i →
    (∀ x → P x → i ≤ℝ x)
    × (∀ y → ((x : RealI) → P x → y ≤ℝ x) → y ≤ℝ i)
  inf-complete = inf , inf-lower , inf-greatest
