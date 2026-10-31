------------------------------------------------------------------------
-- Bisection steps and carried bracket stream
--
-- 二分步骤与携带式括号流
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module Real.Interval.OrderComplete.Bisect where

open import Data.Nat using (ℕ; zero; suc; z≤n)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Function using (_∘_)
open import Data.Rational using
  (ℚ; 0ℚ; 1ℚ; _+_; _-_; _*_; _<_; _≤_; NonNegative; positive)
open import Data.Rational.Base using (-_; nonNegative)
open import Data.Rational.Properties using
  (≤-refl; ≤-reflexive; ≤-trans; ≤-<-trans; <-≤-trans; <-trans; <⇒≤; +-mono-≤
  ; +-monoʳ-<; +-comm; +-assoc; *-assoc; *-identityʳ; *-distribˡ-+; +-identityˡ
  ; +-identityʳ; pos⇒nonNeg; *-monoˡ-<-pos; neg-distrib-+; *-monoʳ-≤-nonNeg
  ; *-monoˡ-≤-nonNeg; +-monoˡ-≤; +-monoʳ-≤; ≮⇒≥)
  renaming (+-inverseʳ to +-invʳ)
open import Relation.Binary.PropositionalEquality using
  (_≡_; cong; cong₂; sym; trans; subst; module ≡-Reasoning)
open ≡-Reasoning

open import Real using (embed; half; 0<embed)
open import Real.Interval using (RealI; δ; δ-half; δ-pos; sub-cancel)
open import Real.IntervalEquiv using (l; u; u-mono; width)
open import Real.Interval.OrderLaws using (width-below-strict)
open import Real.Interval.Node using (u-dyadic; l-dyadic)
open import Real.Interval.Kit using (0<half; 0≤half; half+half≡1)
open import Real.Interval.Order renaming (<-trans to <-transR)
open import Real.Interval.Rational using (pos-diff)
open import Real.Interval.OrderComplete.Base using
  (_≤ℝ_; a+d≡b; x<x+; emb<; δ-dec; Subset; Upper; Occupied; Located; Bracket
  ; mkB; quarter; 0<quarter; qq≡h; 3/4; cube≤half; hp; hp-step)
open import Real.Interval.Reasoning using (begin≤_; _≈⟨_⟩_; _≤⟨_⟩_; _≤∎)

------------------------------------------------------------------------
-- NonNegative half instance
--
-- NonNegative half 的实例

private
  instance
    half-nn : NonNegative half
    half-nn = nonNegative 0≤half

------------------------------------------------------------------------
-- Dyadic half/quarter algebra, independent of a and b
--
-- 二进半/四分之一代数，独立于 a、b

d-half-pair : ∀ (d : ℚ) → d * half + d * half ≡ d
d-half-pair d =
  begin
    d * half + d * half
      ≡⟨ sym (*-distribˡ-+ d half half) ⟩
    d * (half + half)
      ≡⟨ cong (d *_) half+half≡1 ⟩
    d * 1ℚ
      ≡⟨ *-identityʳ d ⟩
    d
      ∎

d-quarter-pair : ∀ (d : ℚ) → d * quarter + d * quarter ≡ d * half
d-quarter-pair d =
  begin
    d * quarter + d * quarter
      ≡⟨ sym (*-distribˡ-+ d quarter quarter) ⟩
    d * (quarter + quarter)
      ≡⟨ cong (d *_) qq≡h ⟩
    d * half
      ∎

d-3/4 : ∀ (d : ℚ) → d * 3/4 ≡ d * half + d * quarter
d-3/4 d = *-distribˡ-+ d half quarter

d-minus-half : ∀ (d : ℚ) → d - d * half ≡ d * half
d-minus-half d =
  begin
    d - d * half
      ≡⟨ cong (_- d * half) (sym (d-half-pair d)) ⟩
    (d * half + d * half) - d * half
      ≡⟨ +-assoc (d * half) (d * half) (- (d * half)) ⟩
    d * half + (d * half - d * half)
      ≡⟨ cong (d * half +_) (+-invʳ (d * half)) ⟩
    d * half + 0ℚ
      ≡⟨ +-identityʳ (d * half) ⟩
    d * half
      ∎

d-half-pos : ∀ (d : ℚ) → 0ℚ < d → 0ℚ < d * half
d-half-pos d 0<d = *-monoˡ-<-pos half {{positive 0<half}} 0<d

d-quarter-pos : ∀ (d : ℚ) → 0ℚ < d → 0ℚ < d * quarter
d-quarter-pos d 0<d = *-monoˡ-<-pos quarter {{positive 0<quarter}} 0<d

------------------------------------------------------------------------
-- Bracket rearrangement, with d = b - a left unexpanded
--
-- 括号重排；d = b - a 保持不展开

bracket-b-eq : ∀ (a b : ℚ) →
  b ≡ ((a + (b - a) * half) + (b - a) * quarter) + (b - a) * quarter
bracket-b-eq a b =
  begin
    b
      ≡⟨ sym (a+d≡b a b) ⟩
    a + (b - a)
      ≡⟨ cong (a +_) (sym (d-half-pair (b - a))) ⟩
    a + ((b - a) * half + (b - a) * half)
      ≡⟨ sym (+-assoc a ((b - a) * half) ((b - a) * half)) ⟩
    (a + (b - a) * half) + (b - a) * half
      ≡⟨ cong ((a + (b - a) * half) +_) (sym (d-quarter-pair (b - a))) ⟩
    (a + (b - a) * half) + ((b - a) * quarter + (b - a) * quarter)
      ≡⟨ sym (+-assoc (a + (b - a) * half)
                     ((b - a) * quarter) ((b - a) * quarter)) ⟩
    ((a + (b - a) * half) + (b - a) * quarter) + (b - a) * quarter
      ∎

bracket-bm-eq : ∀ (a b : ℚ) →
  b - (a + (b - a) * half) ≡ (b - a) * half
bracket-bm-eq a b =
  begin
    b - (a + (b - a) * half)
      ≡⟨ cong (λ z → z - (a + (b - a) * half)) (sym (a+d≡b a b)) ⟩
    (a + (b - a)) - (a + (b - a) * half)
      ≡⟨ cong₂ _-_ (+-comm a (b - a)) (+-comm a ((b - a) * half)) ⟩
    ((b - a) + a) - ((b - a) * half + a)
      ≡⟨ sub-cancel (b - a) ((b - a) * half) a ⟩
    (b - a) - (b - a) * half
      ≡⟨ d-minus-half (b - a) ⟩
    (b - a) * half
      ∎

bracket-ra-eq : ∀ (a b : ℚ) →
  ((a + (b - a) * half) + (b - a) * quarter) - a ≡
  (b - a) * half + (b - a) * quarter
bracket-ra-eq a b =
  begin
    ((a + (b - a) * half) + (b - a) * quarter) - a
      ≡⟨ cong (_- a) (+-assoc a ((b - a) * half) ((b - a) * quarter)) ⟩
    (a + ((b - a) * half + (b - a) * quarter)) - a
      ≡⟨ +-assoc a (((b - a) * half) + ((b - a) * quarter)) (- a) ⟩
    a + (((b - a) * half + (b - a) * quarter) - a)
      ≡⟨ a+d≡b a ((b - a) * half + (b - a) * quarter) ⟩
    (b - a) * half + (b - a) * quarter
      ∎

bracket-case1 : ∀ (a b : ℚ) → a < b →
  b - (a + (b - a) * half) ≤ (b - a) * 3/4
bracket-case1 a b a<b =
  subst (λ z → z ≤ (b - a) * 3/4) (sym (bracket-bm-eq a b))
    (subst (λ z → (b - a) * half ≤ z) (sym (d-3/4 (b - a)))
      (<⇒≤ (x<x+ ((b - a) * half)
              (d-quarter-pos (b - a) (pos-diff a b a<b)))))

bracket-case2 : ∀ (a b : ℚ) → a < b →
  ((a + (b - a) * half) + (b - a) * quarter) - a ≤ (b - a) * 3/4
bracket-case2 a b a<b =
  subst (λ z → z ≤ (b - a) * 3/4) (sym (bracket-ra-eq a b))
    (≤-reflexive (sym (d-3/4 (b - a))))

------------------------------------------------------------------------
-- d-only algebra for step₃-shrink
--
-- step₃-shrink 的 d 代数（独立于 br）

d-cube-assoc : ∀ (d : ℚ) →
  (((d * 3/4) * 3/4) * 3/4) ≡ d * ((3/4 * 3/4) * 3/4)
d-cube-assoc d =
  begin
    (((d * 3/4) * 3/4) * 3/4)
      ≡⟨ *-assoc (d * 3/4) 3/4 3/4 ⟩
    (d * 3/4) * (3/4 * 3/4)
      ≡⟨ *-assoc d 3/4 (3/4 * 3/4) ⟩
    d * (3/4 * (3/4 * 3/4))
      ≡⟨ cong (λ x → d * x) (sym (*-assoc 3/4 3/4 3/4)) ⟩
    d * ((3/4 * 3/4) * 3/4)
      ∎

d-cube≤half : ∀ (d : ℚ) → 0ℚ ≤ d →
  d * ((3/4 * 3/4) * 3/4) ≤ d * half
d-cube≤half d 0≤d =
  *-monoˡ-≤-nonNeg d {{nonNegative 0≤d}} cube≤half

------------------------------------------------------------------------
-- Bracket width and case split, independent of locatedness
--
-- 括号宽度与 case split，独立于定位性

module _ {P : Subset} where

  bw : Bracket P → ℚ
  bw (mkB a b _ _ _) = b - a

  bw-pos : ∀ (br : Bracket P) → 0ℚ < bw br
  bw-pos br = pos-diff (Bracket.a br) (Bracket.b br) (Bracket.a<b br)

  bw-nn : ∀ (br : Bracket P) → 0ℚ ≤ bw br
  bw-nn br = <⇒≤ (bw-pos br)

  -- Case split on the locatedness verdict. The two width bounds are
  -- passed in explicitly, because b - m and r - a depend on how m and r
  -- were chosen (the caller knows m = a + (b-a)/2 and r = a + 3(b-a)/4).
  --
  -- 按定位裁决分情况。两条宽度界显式传入，因为 b - m 与 r - a 依赖
  -- m、r 的构造方式（调用方知道 m = a + (b-a)/2，r = a + 3(b-a)/4）。
  step₁-case :
      (a b : ℚ) (a<b : a < b)
      (m r : ℚ) (a<m : a < m) (m<r : m < r) (r<b : r < b)
      (occ : Occupied P a) (upper : Upper P b)
      (b-m-bound : b - m ≤ (b - a) * 3/4)
      (r-a-bound : r - a ≤ (b - a) * 3/4)
      (s : Occupied P m ⊎ Upper P r) →
      Σ (Bracket P) λ br' →
        (bw br' ≤ (b - a) * 3/4)
        × (a ≤ Bracket.a br')
        × (Bracket.b br' ≤ b)
  step₁-case a b a<b m r a<m m<r r<b occ upper b-m-bound r-a-bound
      (inj₁ (x , px , m<x)) =
    (mkB m b (<-trans m<r r<b) (x , px , m<x) upper)
      , b-m-bound
      , <⇒≤ a<m
      , ≤-refl
  step₁-case a b a<b m r a<m m<r r<b occ upper b-m-bound r-a-bound
      (inj₂ all<r) =
    (mkB a r (<-trans a<m m<r) occ all<r)
      , r-a-bound
      , ≤-refl
      , <⇒≤ r<b

------------------------------------------------------------------------
-- Bisection under a locatedness witness
--
-- 定位见证下的二分

module _ {P : Subset} (loc : Located P) where

  step₁-core : (br : Bracket P) →
    Σ (Bracket P) λ br' →
      (bw br' ≤ bw br * 3/4)
      × (Bracket.a br ≤ Bracket.a br')
      × (Bracket.b br' ≤ Bracket.b br)
  step₁-core (mkB a b a<b occ upper) =
    let
      d   = b - a
      d>0 = pos-diff a b a<b
      hd  = d * half
      qd  = d * quarter
      hd>0 = d-half-pos d d>0
      qd>0 = d-quarter-pos d d>0
      m = a + hd
      r = m + qd
      a<m = x<x+ a hd>0
      m<r = x<x+ m qd>0
      r<b = subst (λ z → r < z) (sym (bracket-b-eq a b)) (x<x+ r qd>0)
    in
      step₁-case a b a<b m r a<m m<r r<b occ upper
        (bracket-case1 a b a<b)
        (bracket-case2 a b a<b)
        (loc m r m<r)

  step₁ : Bracket P → Bracket P
  step₁ br = proj₁ (step₁-core br)

  step₁-shrink : (br : Bracket P) → bw (step₁ br) ≤ bw br * 3/4
  step₁-shrink = proj₁ ∘ proj₂ ∘ step₁-core

  step₁-a≤a : (br : Bracket P) → Bracket.a br ≤ Bracket.a (step₁ br)
  step₁-a≤a = proj₁ ∘ proj₂ ∘ proj₂ ∘ step₁-core

  step₁-b≤b : (br : Bracket P) → Bracket.b (step₁ br) ≤ Bracket.b br
  step₁-b≤b = proj₂ ∘ proj₂ ∘ proj₂ ∘ step₁-core

  step₂ : Bracket P → Bracket P
  step₂ br = step₁ (step₁ br)

  0<3/4 : 0ℚ < 3/4
  0<3/4 = <-trans 0<half (x<x+ half 0<quarter)

  private
    instance nn3/4 : NonNegative 3/4
    nn3/4 = pos⇒nonNeg 3/4 {{positive 0<3/4}}

  mul3/4 : ∀ {x y} → x ≤ y → x * 3/4 ≤ y * 3/4
  mul3/4 = *-monoʳ-≤-nonNeg 3/4

  abstract
    step₃ : Bracket P → Bracket P
    step₃ br = step₁ (step₁ (step₁ br))

    step₃-a≤a : (br : Bracket P) → Bracket.a br ≤ Bracket.a (step₃ br)
    step₃-a≤a br =
      begin≤
        Bracket.a br
          ≤⟨ step₁-a≤a br ⟩
        Bracket.a (step₁ br)
          ≤⟨ step₁-a≤a (step₁ br) ⟩
        Bracket.a (step₁ (step₁ br))
          ≤⟨ step₁-a≤a (step₁ (step₁ br)) ⟩
        Bracket.a (step₁ (step₁ (step₁ br)))
      ≤∎

    step₃-b≤b : (br : Bracket P) → Bracket.b (step₃ br) ≤ Bracket.b br
    step₃-b≤b br =
      begin≤
        Bracket.b (step₁ (step₁ (step₁ br)))
          ≤⟨ step₁-b≤b (step₁ (step₁ br)) ⟩
        Bracket.b (step₁ (step₁ br))
          ≤⟨ step₁-b≤b (step₁ br) ⟩
        Bracket.b (step₁ br)
          ≤⟨ step₁-b≤b br ⟩
        Bracket.b br
      ≤∎

    step₃-shrink : (br : Bracket P) → bw (step₃ br) ≤ bw br * half
    step₃-shrink br =
      begin≤
        bw (step₁ (step₁ (step₁ br)))
          ≤⟨ step₁-shrink (step₁ (step₁ br)) ⟩
        bw (step₁ (step₁ br)) * 3/4
          ≤⟨ mul3/4 (step₁-shrink (step₁ br)) ⟩
        (bw (step₁ br) * 3/4) * 3/4
          ≤⟨ mul3/4 (mul3/4 (step₁-shrink br)) ⟩
        ((bw br * 3/4) * 3/4) * 3/4
          ≈⟨ d-cube-assoc (bw br) ⟩
        bw br * ((3/4 * 3/4) * 3/4)
          ≤⟨ d-cube≤half (bw br) (bw-nn br) ⟩
        bw br * half
      ≤∎

  record CStep (br0 : Bracket P) (j : ℕ) : Set where
    field
      cbr : Bracket P
      cw≤ : bw cbr ≤ bw br0 * hp j

  cstep : ∀ {br0 j} (s : CStep br0 j) → CStep br0 (suc j)
  cstep {br0} {j} (record { cbr = br ; cw≤ = w≤ }) =
    record
      { cbr = step₃ br
      ; cw≤ = begin≤
          bw (step₃ br)
            ≤⟨ step₃-shrink br ⟩
          bw br * half
            ≤⟨ *-monoʳ-≤-nonNeg half w≤ ⟩
          (bw br0 * hp j) * half
            ≈⟨ *-assoc (bw br0) (hp j) half ⟩
          bw br0 * (hp j * half)
            ≈⟨ cong ((bw br0) *_) (hp-step j) ⟩
          bw br0 * hp (suc j)
        ≤∎
      }

  csteps : (br0 : Bracket P) (j : ℕ) → CStep br0 j
  csteps br0 zero    = record { cbr = br0
                              ; cw≤ = ≤-reflexive (sym (*-identityʳ (bw br0))) }
  csteps br0 (suc j) = cstep (csteps br0 j)

  cbr-seq : (br0 : Bracket P) (j : ℕ) → Bracket P
  cbr-seq br0 j = CStep.cbr (csteps br0 j)

  cwb : ∀ br0 j → bw (cbr-seq br0 j) ≤ bw br0 * hp j
  cwb br0 j = CStep.cw≤ (csteps br0 j)

------------------------------------------------------------------------
-- Initial and widened brackets
--
-- 初始括号与加宽括号

module _ {P : Subset} where

  initBracket : (x₀ : RealI) → P x₀
              → (u₀ : RealI) → ((x : RealI) → P x → x ≤ℝ u₀)
              → Bracket P
  initBracket x₀ px₀ u₀ isUpper =
    let
      0<1ℚ = 0<embed 0
      lx   = l x₀ 0
      uu   = u u₀ 0

      not-u0<x0 = isUpper x₀ px₀
      lx≤uu     = ≮⇒≥ (λ uu<lx → not-u0<x0 (0 , uu<lx))

      a = lx - 1ℚ
      b = uu + 1ℚ

      a+1≡lx = begin
        a + 1ℚ
          ≡⟨ +-comm a 1ℚ ⟩
        1ℚ + a
          ≡⟨ a+d≡b 1ℚ lx ⟩
        lx
          ∎

      a<lx = subst (a <_) a+1≡lx (x<x+ a 0<1ℚ)
      uu<b = x<x+ uu 0<1ℚ
      a<b  = <-trans a<lx (≤-<-trans lx≤uu uu<b)

      uEa≡ = trans (u-dyadic a 0) (+-comm (δ 0) a)

      a+half+half≡lx = begin
        a + half + half
          ≡⟨ +-assoc a half half ⟩
        a + (half + half)
          ≡⟨ cong (a +_) half+half≡1 ⟩
        a + 1ℚ
          ≡⟨ a+1≡lx ⟩
        lx
          ∎

      a+half<lx = subst (λ z → a + half < z) a+half+half≡lx
                    (x<x+ (a + half) 0<half)

      occ = x₀ , px₀ , (0 , subst (λ z → z < lx) (sym uEa≡) a+half<lx)

      upper = λ x px →
        let
          sel = width-below-strict x half 1 (0<half)
          n      = proj₁ sel
          n≥1    = proj₁ (proj₂ sel)
          w<half = proj₂ (proj₂ sel)

          δ1≤half = subst (δ 1 ≤_) (δ-half 0)
                      (<⇒≤ (x<x+ (δ 1) (δ-pos 1)))
          δn≤half = ≤-trans (δ-dec 1 n n≥1) δ1≤half

          lxn = l x n

          ¬uun<lxn = λ uun<lxn → isUpper x px (n , uun<lxn)
          lxn≤uun  = ≮⇒≥ ¬uun<lxn
          uun≤uu   = u-mono u₀ {0} {n} z≤n

          ux≡ = sym (a+d≡b lxn (u x n))

          half+δn≤1 = subst (λ z → half + δ n ≤ z) half+half≡1
                        (+-monoʳ-≤ half δn≤half)

          simpl = begin
            (half + δ n) + (- δ n)
              ≡⟨ +-assoc half (δ n) (- δ n) ⟩
            half + (δ n + (- δ n))
              ≡⟨ cong (half +_) (+-invʳ (δ n)) ⟩
            half + 0ℚ
              ≡⟨ +-identityʳ half ⟩
            half
              ∎

          half≤1-δn = subst (λ z → z ≤ 1ℚ - δ n) simpl
                        (+-mono-≤ half+δn≤1 (≤-refl {(- δ n)}))

          ux≤ = subst (λ z → z ≤ uu + width x n) (sym ux≡)
                  (≤-trans (+-monoˡ-≤ (width x n) lxn≤uun)
                     (+-monoˡ-≤ (width x n) uun≤uu))

          w-strict = +-monoʳ-< uu (<-≤-trans w<half half≤1-δn)

          lEb≡ = trans (l-dyadic b n) (+-comm (- δ n) b)

          b-δ≡ = +-assoc uu 1ℚ (- δ n)

          final = subst (λ z → u x n < z) (sym lEb≡)
                    (≤-<-trans ux≤
                      (subst (λ z → uu + width x n < z) (sym b-δ≡) w-strict))
        in
          n , final
    in
      mkB a b a<b occ upper

  widenBracket : Bracket P → Bracket P
  widenBracket br =
    let open Bracket br
        two = embed 2
        a' = a - two
        b' = b + two
        0<two = 0<embed 1

        negA' = begin
          (- a')
            ≡⟨⟩
          - (a - two)
            ≡⟨ neg-distrib-+ a (- two) ⟩
          (- a) + two
            ∎

        diff≡ = begin
          a + (- a')
            ≡⟨ cong (a +_) negA' ⟩
          a + ((- a) + two)
            ≡⟨ sym (+-assoc a (- a) two) ⟩
          (a + (- a)) + two
            ≡⟨ cong (_+ two) (+-invʳ a) ⟩
          0ℚ + two
            ≡⟨ +-identityˡ two ⟩
          two
            ∎

        a'<a = subst (λ z → a' < z) (a+d≡b a' a)
                 (subst (λ z → a' < a' + z) (sym diff≡) (x<x+ a' 0<two))
        b<b' = x<x+ b 0<two
        a'<b' = <-trans a'<a (≤-<-trans (<⇒≤ a<b) b<b')

        x  = proj₁ occ
        px = proj₁ (proj₂ occ)
        a<x = proj₂ (proj₂ occ)

        a'<x = <-transR (emb< a'<a) a<x
        occ' = x , px , a'<x

        x<b = upper
        b<b'R = emb< b<b'
        upper' = λ y py → <-transR (x<b y py) b<b'R
    in mkB a' b' a'<b' occ' upper'
