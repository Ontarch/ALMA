------------------------------------------------------------------------
-- Order completeness of real intervals
--
-- 实数区间的序完备性
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module Real.Interval.OrderComplete where

open import Data.Nat using (ℕ; zero; suc; _⊔_) renaming (_≥_ to _≥N_)
open import Data.Nat.Properties using (m≤m⊔n; m≤n⊔m) renaming (≤-trans to ≤N-trans)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Data.Rational using
  (ℚ; 0ℚ; 1ℚ; _+_; _-_; _*_; _<_; _≤_; Positive; positive)
open import Data.Rational.Base using (-_)
open import Data.Rational.Properties using
  (≤-<-trans; <⇒≤; +-comm; +-assoc; +-monoˡ-<; *-comm; *-identityʳ; *-distribˡ-+
  ; +-identityʳ; *-monoˡ-<-pos; *-monoʳ-<-pos; *-zeroˡ)
  renaming (+-inverseʳ to +-invʳ)
import Data.Rational.Properties
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; cong; cong₂; sym; subst; subst₂; module ≡-Reasoning)
open ≡-Reasoning
open Data.Rational.Properties.≤-Reasoning public
  renaming (_∎ to _∎≤; begin_ to begin≤_) hiding (step-≡-⟩; step-≡-⟨; step-≡-∣)

open import Base.RationalRing using (neg-involutive)
open import Real using (half)
open import Real.Interval.Rational using (pos-diff)
open import Real.Interval.OrderLaws using (width-below-strict; width-dec)
open import Real.Interval.Node using (node-dyadic; l-dyadic; u-dyadic)
open import Real.Interval.Kit using (0<half; half+half≡1)
open import Real.Interval using (RealI; embedℚ; δ; dyadic; sub-cancel)
import Real.Interval as RealI
open import Real.IntervalEquiv using (l; u; node; width; u-mono; l-mono)
open import Real.Interval.Order using (_<ℝ_; <-irrefl) renaming (<-trans to <-transR)
open import Real.Interval.OrderComplete.Base using
  (_≤ℝ_; gapLemma; Subset; Located; Bracket)
open import Real.Interval.OrderComplete.Bisect using
  (bw; step₃-a≤a; step₃-b≤b; step₃-shrink; cbr-seq; initBracket; widenBracket)

------------------------------------------------------------------------
-- Pure rational lemmas
--
-- 纯有理引理

half-pos : Positive half
half-pos = positive 0<half

-- δ n < g/2 whenever δ n + δ n < g.
--
-- 若 δ n + δ n < g，则 δ n < g/2。
δ-half< : ∀ (n : ℕ) (g : ℚ) → δ n + δ n < g → δ n < g * half
δ-half< n g d<n =
  let e1 : half * (δ n + δ n) < half * g
      e1 = *-monoʳ-<-pos half {{half-pos}} d<n
      e2 : half * (δ n + δ n) ≡ δ n
      e2 =
        begin
          half * (δ n + δ n)
            ≡⟨ *-distribˡ-+ half (δ n) (δ n) ⟩
          half * δ n + half * δ n
            ≡⟨ cong₂ _+_ (*-comm half (δ n)) (*-comm half (δ n)) ⟩
          δ n * half + δ n * half
            ≡⟨ sym (*-distribˡ-+ (δ n) half half) ⟩
          δ n * (half + half)
            ≡⟨ cong (δ n *_) half+half≡1 ⟩
          δ n * 1ℚ
            ≡⟨ *-identityʳ (δ n) ⟩
          δ n
            ∎
      e3 : half * g ≡ g * half
      e3 = *-comm half g
  in subst₂ _<_ e2 e3 e1

------------------------------------------------------------------------
-- Supremum
--
-- 上确界

module _ {P : Subset} (loc : Located P)
         {x₀ : RealI} (px₀ : P x₀)
         {u₀ : RealI} (isUpper : (x : RealI) → P x → x ≤ℝ u₀) where

  br0 : Bracket P
  br0 = widenBracket (initBracket x₀ px₀ u₀ isUpper)

  d0 = bw br0

  d0>0 : 0ℚ < d0
  d0>0 = pos-diff (Bracket.a br0) (Bracket.b br0) (Bracket.a<b br0)

  0≤d0 : 0ℚ ≤ d0
  0≤d0 = <⇒≤ d0>0

  br-seq : ℕ → Bracket P
  br-seq = cbr-seq loc br0

  supI : (j : ℕ) → RealI
  supI j .RealI.l    = Bracket.a (br-seq j)
  supI j .RealI.u    = Bracket.b (br-seq j)
  supI j .RealI.lo   = Bracket.a<b (br-seq j)
  supI j .RealI.next = supI (suc j)
  supI j .RealI.nest = step₃-a≤a loc (br-seq j)
                     , step₃-b≤b loc (br-seq j)
                     , step₃-shrink loc (br-seq j)

  sup : RealI
  sup = supI 0

  node-sup : ∀ n → node sup n ≡ supI n
  node-sup zero    = refl
  node-sup (suc n) = cong RealI.next (node-sup n)

  l-sup : ∀ n → l sup n ≡ Bracket.a (br-seq n)
  l-sup n = cong RealI.l (node-sup n)
  u-sup : ∀ n → u sup n ≡ Bracket.b (br-seq n)
  u-sup n = cong RealI.u (node-sup n)

  ----------------------------------------------------------------------
  -- width (embedℚ 0) n ≡ δ n + δ n  (top-level within the module)
  --
  -- embedℚ 0 在层级 n 的宽度（模块内顶层陈述）。

  w0-embed0 : ∀ n → width (embedℚ 0ℚ) n ≡ δ n + δ n
  w0-embed0 n =
    begin
      width (embedℚ 0ℚ) n
        ≡⟨ cong (λ r → RealI.u r - RealI.l r) (node-dyadic 0ℚ n) ⟩
      RealI.u (dyadic 0ℚ n) - RealI.l (dyadic 0ℚ n)
        ≡⟨ sub-cancel (δ n) (- δ n) 0ℚ ⟩
      δ n + (- (- δ n))
        ≡⟨ cong (δ n +_) (neg-involutive (δ n)) ⟩
      δ n + δ n
        ∎

  ----------------------------------------------------------------------
  -- smallNode: a level where both width sup and δ are below g/2.
  --
  -- smallNode：使上确界宽度与 δ 均低于 g/2 的层级。

  smallNode : (k : ℕ) (g : ℚ) → 0ℚ < g →
    Σ ℕ λ n → n ≥N k × width sup n < g * half × δ n < g * half
  smallNode k g 0<g =
    let ghalf>0 : 0ℚ < g * half
        ghalf>0 = subst (λ z → z < g * half) (*-zeroˡ half)
                    (*-monoˡ-<-pos half {{half-pos}} 0<g)
        s1 = width-below-strict sup (g * half) k ghalf>0
        n1 = proj₁ s1
        n1≥k = proj₁ (proj₂ s1)
        w1 = proj₂ (proj₂ s1)
        s2 = width-below-strict (embedℚ 0ℚ) g k 0<g
        n2 = proj₁ s2
        w2 = proj₂ (proj₂ s2)
        n = n1 ⊔ n2
        n≥k = ≤N-trans n1≥k (m≤m⊔n n1 n2)
        n1≤n = m≤m⊔n n1 n2
        n2≤n = m≤n⊔m n1 n2
        w< = ≤-<-trans (width-dec sup n1≤n) w1
        d2< = ≤-<-trans (width-dec (embedℚ 0ℚ) n2≤n) w2
        two*δn<g = subst (λ z → z < g) (w0-embed0 n) d2<
        d< = δ-half< n g two*δn<g
    in n , n≥k , w< , d<

  ----------------------------------------------------------------------
  -- sup-upper-witness: a strict-order witness embedℚ (u sup n) <ℝ z
  -- given u sup k < l z k.
  --
  -- sup-upper-witness：由 u sup k < l z k 给出严格序见证
  -- embedℚ (u sup n) <ℝ z。

  sup-upper-witness : (z : RealI) (k : ℕ) (g : ℚ)
      → g ≡ l z k - u sup k
      → 0ℚ < g
      → Σ ℕ λ n → n ≥N k × (embedℚ (u sup n) <ℝ z)
  sup-upper-witness z k g refl 0<g =
    let sn = smallNode k g 0<g
        n = proj₁ sn
        n≥k = proj₁ (proj₂ sn)
        d< = proj₂ (proj₂ (proj₂ sn))
        bn+δn<lzn : u sup n + δ n < l z n
        bn+δn<lzn = gapLemma (δ n) 0<g (u-mono sup n≥k) (l-mono z n≥k) d<
        reordered : δ n + u sup n < l z n
        reordered = subst (λ z₁ → z₁ < l z n)
                      (+-comm (u sup n) (δ n)) bn+δn<lzn
        eb<z : embedℚ (u sup n) <ℝ z
        eb<z = n , subst (λ z₁ → z₁ < l z n)
                  (sym (u-dyadic (u sup n) n)) reordered
    in n , n≥k , eb<z

  ----------------------------------------------------------------------
  -- sup-least-witness: a strict-order witness y <ℝ embedℚ (l sup n)
  -- given u y k < l sup k.
  --
  -- sup-least-witness：由 u y k < l sup k 给出严格序见证
  -- y <ℝ embedℚ (l sup n)。

  sup-least-witness : (y : RealI) (k : ℕ) (g : ℚ)
      → g ≡ l sup k - u y k
      → 0ℚ < g
      → Σ ℕ λ n → n ≥N k × (y <ℝ embedℚ (l sup n))
  sup-least-witness y k g refl 0<g =
    let sn = smallNode k g 0<g
        n = proj₁ sn
        n≥k = proj₁ (proj₂ sn)
        d< = proj₂ (proj₂ (proj₂ sn))
        q = l sup n
        uy+δ<an : u y n + δ n < q
        uy+δ<an = gapLemma (δ n) 0<g (u-mono y n≥k) (l-mono sup n≥k) d<
        shifted : (u y n + δ n) + (- δ n) < q + (- δ n)
        shifted = +-monoˡ-< (- δ n) uy+δ<an
        lhs≡ : (u y n + δ n) + (- δ n) ≡ u y n
        lhs≡ =
          begin
            (u y n + δ n) + (- δ n)
              ≡⟨ +-assoc (u y n) (δ n) (- δ n) ⟩
            u y n + (δ n + (- δ n))
              ≡⟨ cong (u y n +_) (+-invʳ (δ n)) ⟩
            u y n + 0ℚ
              ≡⟨ +-identityʳ (u y n) ⟩
            u y n
              ∎
        uy<q-δn : u y n < q - δ n
        uy<q-δn = subst (λ z → z < q + (- δ n)) lhs≡ shifted
        reordered : u y n < (- δ n) + l sup n
        reordered = subst (λ z₁ → u y n < z₁)
                      (+-comm (l sup n) (- δ n)) uy<q-δn
        y<ea : y <ℝ embedℚ (l sup n)
        y<ea = n , subst (λ z₁ → u y n < z₁)
                  (sym (l-dyadic (l sup n) n)) reordered
    in n , n≥k , y<ea

  ----------------------------------------------------------------------
  -- sup is an upper bound: every member z satisfies z ≤ℝ sup.
  --
  -- sup 是上界：每个成员 z 满足 z ≤ℝ sup。

  sup-upper : ∀ z → P z → z ≤ℝ sup
  sup-upper z pz sup<z =
    let k = proj₁ sup<z
        gap0 = proj₂ sup<z
        g = l z k - u sup k
        0<g = pos-diff (u sup k) (l z k) gap0
        sn = sup-upper-witness z k g refl 0<g
        n = proj₁ sn
        eb<z = proj₂ (proj₂ sn)
        z<eb0 = Bracket.upper (br-seq n) z pz
        z<eb = subst (λ q → z <ℝ embedℚ q) (sym (u-sup n)) z<eb0
        absurd = <-transR eb<z z<eb
    in <-irrefl (embedℚ (u sup n)) absurd

  ----------------------------------------------------------------------
  -- sup is least: any upper bound y satisfies sup ≤ℝ y.
  --
  -- sup 是最小上界：任意上界 y 满足 sup ≤ℝ y。

  sup-least : ∀ y → ((z : RealI) → P z → z ≤ℝ y) → sup ≤ℝ y
  sup-least y bound y<sup =
    let k = proj₁ y<sup
        gap0 = proj₂ y<sup
        g = l sup k - u y k
        0<g = pos-diff (u y k) (l sup k) gap0
        sn = sup-least-witness y k g refl 0<g
        n = proj₁ sn
        y<ea = proj₂ (proj₂ sn)
        occn = Bracket.occ (br-seq n)
        x = proj₁ occn
        px = proj₁ (proj₂ occn)
        a0<x = proj₂ (proj₂ occn)
        an<x = subst (λ q → embedℚ q <ℝ x) (sym (l-sup n)) a0<x
        y<x = <-transR y<ea an<x
        x≤y = bound x px
    in x≤y y<x

  ----------------------------------------------------------------------
  -- Order completeness
  --
  -- 序完备性

  order-complete : Σ RealI λ s →
    (∀ z → P z → z ≤ℝ s) × (∀ y → ((z : RealI) → P z → z ≤ℝ y) → s ≤ℝ y)
  order-complete = sup , sup-upper , sup-least
