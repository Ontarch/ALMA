------------------------------------------------------------------------
-- Core lemmas for multiplication laws of RealI
--
-- RealI 乘法律的核心引理
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module Real.Interval.Mul.Core where

open import Data.Nat using (ℕ) renaming (_*_ to _ℕ*_)
import Data.Nat.Properties as ℕP
open import Data.Product using (_,_; Σ; _×_)
open import Data.Rational using
  (ℚ; 0ℚ; 1ℚ; _+_; _-_; _*_; _≤_; ∣_∣; nonNegative)
open import Data.Rational.Base using (_÷_) renaming (-_ to neg)
open import Data.Rational.Properties using
  (+-identityˡ; +-identityʳ; +-inverseʳ; +-comm; *-identityˡ; *-identityʳ
  ; *-assoc; *-comm; *-distribʳ-+; *-distribˡ-+; neg-distribˡ-*; neg-distribʳ-*
  ; ≤-refl; <⇒≤; +-mono-≤; neg-antimono-≤; *-monoˡ-≤-nonNeg; *-monoʳ-≤-nonNeg
  ; ∣p+q∣≤∣p∣+∣q∣; ∣p∣≡p∨∣p∣≡-p; ∣p*q∣≡∣p∣*∣q∣; 0≤p⇒∣p∣≡p)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; cong; cong₂; trans; sym; subst; module ≡-Reasoning)
open ≡-Reasoning

open import Base.RationalRing using (neg-involutive)
open import Real using (embed; half; 2ℚ; telescope)
open import Real.Interval using (RealI)
open import Real.Interval.Mul using
  (_*ℝ_; 0≤diff; cancelʳ; sub-mono)
import Real.Interval.Mul as MUL
open import Real.Interval.Bounded using (bounded)
open import Real.IntervalEquiv using
  (node; centre; width; centre-l; centre-u; recipPow2)
open import Real.Interval.Rational using
  (min; max; max-eq; min-eq; sub-add; negsub)
open import Real.Interval.Kit using
  (*-mono-≤-nonNeg; add-self; 2ℚ*half≡1; 0≤half; half≤1; 0≤recipPow2)
open import Real.Interval.Node using
  (node-*ℝ; width-rec; mul-pair; mul-nonNeg; 0≤width-n; recipPow2≤1; rr≤r)
open import Base.RationalRing using (*ʳ-sub; +interchange)
open import Real.Interval.Reasoning

------------------------------------------------------------------------
-- Absolute-value bound
--
-- |t| ≤ C whenever −C ≤ t ≤ C.
--
-- 绝对值界
--
-- 若 −C ≤ t ≤ C 则 |t| ≤ C。

abs-≤ : ∀ {t C : ℚ} → neg C ≤ t → t ≤ C → ∣ t ∣ ≤ C
abs-≤ {t} {C} h1 h2 with ∣p∣≡p∨∣p∣≡-p t
... | inj₁ e = begin≤
      ∣ t ∣
        ≈⟨ e ⟩
      t
        ≤⟨ h2 ⟩
      C
      ≤∎
... | inj₂ e = begin≤
      ∣ t ∣
        ≈⟨ e ⟩
      neg t
        ≤⟨ subst (λ z → neg t ≤ z) (neg-involutive C) (neg-antimono-≤ h1) ⟩
      C
      ≤∎

------------------------------------------------------------------------
-- Additive rearrangement
--
-- 加法重排

add-diff : ∀ a b → a + (b - a) ≡ b
add-diff a b = begin
  a + (b - a)
    ≡⟨ +-comm a (b - a) ⟩
  (b - a) + a
    ≡⟨ cancelʳ b a ⟩
  b
  ∎

le-of-diff : ∀ {a b : ℚ} → 0ℚ ≤ b - a → a ≤ b
le-of-diff {a} {b} 0≤ = begin≤
      a
        ≈⟨ sym (+-identityʳ a) ⟩
      a + 0ℚ
        ≤⟨ +-mono-≤ (≤-refl {a}) 0≤ ⟩
      a + (b - a)
        ≈⟨ add-diff a b ⟩
      b
      ≤∎

------------------------------------------------------------------------
-- Half-scale estimates
--
-- 半尺度估计

half*half≤half : half * half ≤ half
half*half≤half = begin≤
      half * half
        ≤⟨ *-monoˡ-≤-nonNeg half {{nonNegative 0≤half}} half≤1 ⟩
      half * 1ℚ
        ≈⟨ *-identityʳ half ⟩
      half
      ≤∎

double-sub : ∀ a c → (a + a) - (a + c) ≡ a - c
double-sub a c = begin
  (a + a) - (a + c)
    ≡⟨ sub-add a a a c ⟩
  (a - a) + (a - c)
    ≡⟨ cong (λ z → z + (a - c)) (+-inverseʳ a) ⟩
  0ℚ + (a - c)
    ≡⟨ +-identityˡ (a - c) ⟩
  a - c
  ∎

half-scale : ∀ a → a * half ≡ (a + a) * (half * half)
half-scale a = sym (begin
  (a + a) * (half * half)
    ≡⟨ cong (_* (half * half)) (add-self a) ⟩
  (2ℚ * a) * (half * half)
    ≡⟨ *-assoc 2ℚ a (half * half) ⟩
  2ℚ * (a * (half * half))
    ≡⟨ cong (2ℚ *_) (sym (*-assoc a half half)) ⟩
  2ℚ * ((a * half) * half)
    ≡⟨ cong (2ℚ *_) (*-comm (a * half) half) ⟩
  2ℚ * (half * (a * half))
    ≡⟨ sym (*-assoc 2ℚ half (a * half)) ⟩
  (2ℚ * half) * (a * half)
    ≡⟨ cong (_* (a * half)) 2ℚ*half≡1 ⟩
  1ℚ * (a * half)
    ≡⟨ *-identityˡ (a * half) ⟩
  a * half
  ∎)

final-alg : ∀ S D E → S * half - (D + E) * (half * half)
                      ≡ ((S + S) - (D + E)) * (half * half)
final-alg S D E = begin
  S * half - (D + E) * (half * half)
    ≡⟨ cong (λ z → z - (D + E) * (half * half)) (half-scale S) ⟩
  ((S + S) * (half * half)) - (D + E) * (half * half)
    ≡⟨ sym (*ʳ-sub (S + S) (D + E) (half * half)) ⟩
  ((S + S) - (D + E)) * (half * half)
  ∎

------------------------------------------------------------------------
-- Centre core
--
-- Helpers for centre-*ℝ≤.
--
-- 中心核心
--
-- centre-*ℝ≤ 的辅助引理。

module CentreCore (x y : RealI) (n : ℕ) where
  X : RealI
  X = node x (2 ℕ* n)

  Y : RealI
  Y = node y (2 ℕ* n)

  lx ux ly uy : ℚ
  lx = RealI.l X
  ux = RealI.u X
  ly = RealI.l Y
  uy = RealI.u Y

  lx≤ux : lx ≤ ux
  lx≤ux = <⇒≤ (RealI.lo X)
  ly≤uy : ly ≤ uy
  ly≤uy = <⇒≤ (RealI.lo Y)

  module C = MUL.Corner lx ux ly uy lx≤ux ly≤uy

  P1 P2 P3 P4 : ℚ
  P1 = C.c1
  P2 = C.c2
  P3 = C.c3
  P4 = C.c4

  lo4 hi4 : ℚ
  lo4 = C.lo4
  hi4 = C.hi4

  D E S : ℚ
  D = P1 + P4
  E = P2 + P3
  S = lo4 + hi4

  w w' : ℚ
  w = ux - lx
  w' = uy - ly

  0≤w : 0ℚ ≤ w
  0≤w = 0≤diff lx≤ux
  0≤w' : 0ℚ ≤ w'
  0≤w' = 0≤diff ly≤uy

  c-xy : centre (x *ℝ y) n ≡ S * half
  c-xy = cong₂ (λ a b → (a + b) * half)
                (cong RealI.l (node-*ℝ x y n))
                (cong RealI.u (node-*ℝ x y n))

  expand : (lx + ux) * (ly + uy) ≡ D + E
  expand = begin
    (lx + ux) * (ly + uy)
      ≡⟨ *-distribʳ-+ (ly + uy) lx ux ⟩
    lx * (ly + uy) + ux * (ly + uy)
      ≡⟨ cong₂ _+_ (*-distribˡ-+ lx ly uy) (*-distribˡ-+ ux ly uy) ⟩
    (lx * ly + lx * uy) + (ux * ly + ux * uy)
      ≡⟨ cong ((P1 + P2) +_) (+-comm P3 P4) ⟩
    (P1 + P2) + (P4 + P3)
      ≡⟨ +interchange P1 P2 P4 P3 ⟩
    D + E
    ∎

  c-cc : centre x (2 ℕ* n) * centre y (2 ℕ* n)
        ≡ (D + E) * (half * half)
  c-cc = begin
    centre x (2 ℕ* n) * centre y (2 ℕ* n)
      ≡⟨ mul-pair (lx + ux) (ly + uy) half ⟩
    ((lx + ux) * (ly + uy)) * (half * half)
      ≡⟨ cong (_* (half * half)) expand ⟩
    (D + E) * (half * half)
    ∎

  hi4-fromL : max (max P1 P2) (max P3 P4) ≡ max P1 P2 →
              max P1 P2 ≡ P1 ⊎ max P1 P2 ≡ P2 →
              hi4 ≡ P1 ⊎ hi4 ≡ P2 ⊎ hi4 ≡ P3 ⊎ hi4 ≡ P4
  hi4-fromL e (inj₁ e2) = inj₁ (trans e e2)
  hi4-fromL e (inj₂ e2) = inj₂ (inj₁ (trans e e2))

  hi4-fromR : max (max P1 P2) (max P3 P4) ≡ max P3 P4 →
              max P3 P4 ≡ P3 ⊎ max P3 P4 ≡ P4 →
              hi4 ≡ P1 ⊎ hi4 ≡ P2 ⊎ hi4 ≡ P3 ⊎ hi4 ≡ P4
  hi4-fromR e (inj₁ e2) = inj₂ (inj₂ (inj₁ (trans e e2)))
  hi4-fromR e (inj₂ e2) = inj₂ (inj₂ (inj₂ (trans e e2)))

  hi4-combine : (max (max P1 P2) (max P3 P4) ≡ max P1 P2)
              ⊎ (max (max P1 P2) (max P3 P4) ≡ max P3 P4) →
                hi4 ≡ P1 ⊎ hi4 ≡ P2 ⊎ hi4 ≡ P3 ⊎ hi4 ≡ P4
  hi4-combine (inj₁ e) = hi4-fromL e (max-eq P1 P2)
  hi4-combine (inj₂ e) = hi4-fromR e (max-eq P3 P4)

  hi4-cases : hi4 ≡ P1 ⊎ hi4 ≡ P2 ⊎ hi4 ≡ P3 ⊎ hi4 ≡ P4
  hi4-cases = hi4-combine (max-eq (max P1 P2) (max P3 P4))

  lo4-fromL : min (min P1 P2) (min P3 P4) ≡ min P1 P2 →
              min P1 P2 ≡ P1 ⊎ min P1 P2 ≡ P2 →
              lo4 ≡ P1 ⊎ lo4 ≡ P2 ⊎ lo4 ≡ P3 ⊎ lo4 ≡ P4
  lo4-fromL e (inj₁ e2) = inj₁ (trans e e2)
  lo4-fromL e (inj₂ e2) = inj₂ (inj₁ (trans e e2))

  lo4-fromR : min (min P1 P2) (min P3 P4) ≡ min P3 P4 →
              min P3 P4 ≡ P3 ⊎ min P3 P4 ≡ P4 →
              lo4 ≡ P1 ⊎ lo4 ≡ P2 ⊎ lo4 ≡ P3 ⊎ lo4 ≡ P4
  lo4-fromR e (inj₁ e2) = inj₂ (inj₂ (inj₁ (trans e e2)))
  lo4-fromR e (inj₂ e2) = inj₂ (inj₂ (inj₂ (trans e e2)))

  lo4-combine : (min (min P1 P2) (min P3 P4) ≡ min P1 P2)
              ⊎ (min (min P1 P2) (min P3 P4) ≡ min P3 P4) →
                lo4 ≡ P1 ⊎ lo4 ≡ P2 ⊎ lo4 ≡ P3 ⊎ lo4 ≡ P4
  lo4-combine (inj₁ e) = lo4-fromL e (min-eq P1 P2)
  lo4-combine (inj₂ e) = lo4-fromR e (min-eq P3 P4)

  lo4-cases : lo4 ≡ P1 ⊎ lo4 ≡ P2 ⊎ lo4 ≡ P3 ⊎ lo4 ≡ P4
  lo4-cases = lo4-combine (min-eq (min P1 P2) (min P3 P4))

  c4-c3≡ : P4 - P3 ≡ ux * (uy - ly)
  c4-c3≡ = begin
    P4 - P3
      ≡⟨ sym (negsub P3 P4) ⟩
    neg (P3 - P4)
      ≡⟨ cong neg C.c3-c4≡ ⟩
    neg (ux * (ly - uy))
      ≡⟨ neg-distribʳ-* ux (ly - uy) ⟩
    ux * neg (ly - uy)
      ≡⟨ cong (ux *_) (negsub ly uy) ⟩
    ux * (uy - ly)
    ∎

  key-neg-step : lx * (ly - uy) ≡ (neg lx) * (uy - ly)
  key-neg-step = begin
    lx * (ly - uy)
      ≡⟨ cong (lx *_) (sym (negsub uy ly)) ⟩
    lx * neg (uy - ly)
      ≡⟨ sym (neg-distribʳ-* lx (uy - ly)) ⟩
    neg (lx * (uy - ly))
      ≡⟨ neg-distribˡ-* lx (uy - ly) ⟩
    (neg lx) * (uy - ly)
    ∎

  key : D - E ≡ w * w'
  key = begin
    D - E
      ≡⟨ sub-add P1 P4 P2 P3 ⟩
    (P1 - P2) + (P4 - P3)
      ≡⟨ cong₂ _+_ C.c1-c2≡ c4-c3≡ ⟩
    (lx * (ly - uy)) + (ux * (uy - ly))
      ≡⟨ cong (λ z → z + ux * (uy - ly)) key-neg-step ⟩
    ((neg lx) * (uy - ly)) + (ux * (uy - ly))
      ≡⟨ sym (*-distribʳ-+ (uy - ly) (neg lx) ux) ⟩
    ((neg lx) + ux) * (uy - ly)
      ≡⟨ cong (λ z → z * (uy - ly)) (+-comm (neg lx) ux) ⟩
    (ux + neg lx) * (uy - ly)
      ≡⟨ refl ⟩
    (ux - lx) * (uy - ly)
    ∎

  E≤D : E ≤ D
  E≤D = le-of-diff (begin≤
        0ℚ
          ≤⟨ mul-nonNeg 0≤w 0≤w' ⟩
        w * w'
          ≈⟨ sym key ⟩
        D - E
        ≤∎)

  S≤D-go : hi4 ≡ P1 ⊎ hi4 ≡ P2 ⊎ hi4 ≡ P3 ⊎ hi4 ≡ P4 → S ≤ D
  S≤D-go (inj₁ e) = begin≤
        lo4 + hi4
          ≈⟨ cong (lo4 +_) e ⟩
        lo4 + P1
          ≤⟨ +-mono-≤ C.lo4≤c4 (≤-refl {P1}) ⟩
        P4 + P1
          ≈⟨ +-comm P4 P1 ⟩
        D
        ≤∎
  S≤D-go (inj₂ (inj₁ e)) = begin≤
        lo4 + hi4
          ≈⟨ cong (lo4 +_) e ⟩
        lo4 + P2
          ≤⟨ +-mono-≤ C.lo4≤c3 (≤-refl {P2}) ⟩
        P3 + P2
          ≈⟨ +-comm P3 P2 ⟩
        E
          ≤⟨ E≤D ⟩
        D
        ≤∎
  S≤D-go (inj₂ (inj₂ (inj₁ e))) = begin≤
        lo4 + hi4
          ≈⟨ cong (lo4 +_) e ⟩
        lo4 + P3
          ≤⟨ +-mono-≤ C.lo4≤c2 (≤-refl {P3}) ⟩
        E
          ≤⟨ E≤D ⟩
        D
        ≤∎
  S≤D-go (inj₂ (inj₂ (inj₂ e))) = begin≤
        lo4 + hi4
          ≈⟨ cong (lo4 +_) e ⟩
        lo4 + P4
          ≤⟨ +-mono-≤ C.lo4≤c1 (≤-refl {P4}) ⟩
        D
        ≤∎

  S≤D : S ≤ D
  S≤D = S≤D-go hi4-cases

  E≤S-go : lo4 ≡ P1 ⊎ lo4 ≡ P2 ⊎ lo4 ≡ P3 ⊎ lo4 ≡ P4 → E ≤ S
  E≤S-go (inj₁ e) = begin≤
        E
          ≤⟨ E≤D ⟩
        D
          ≤⟨ +-mono-≤ (≤-refl {P1}) C.c4≤hi4 ⟩
        P1 + hi4
          ≈⟨ cong (λ z → z + hi4) (sym e) ⟩
        lo4 + hi4
        ≤∎
  E≤S-go (inj₂ (inj₁ e)) = begin≤
        E
          ≤⟨ +-mono-≤ (≤-refl {P2}) C.c3≤hi4 ⟩
        P2 + hi4
          ≈⟨ cong (λ z → z + hi4) (sym e) ⟩
        lo4 + hi4
        ≤∎
  E≤S-go (inj₂ (inj₂ (inj₁ e))) = begin≤
        E
          ≤⟨ +-mono-≤ C.c2≤hi4 (≤-refl {P3}) ⟩
        hi4 + P3
          ≈⟨ +-comm hi4 P3 ⟩
        P3 + hi4
          ≈⟨ cong (λ z → z + hi4) (sym e) ⟩
        lo4 + hi4
        ≤∎
  E≤S-go (inj₂ (inj₂ (inj₂ e))) = begin≤
        E
          ≤⟨ E≤D ⟩
        D
          ≤⟨ +-mono-≤ C.c1≤hi4 (≤-refl {P4}) ⟩
        hi4 + P4
          ≈⟨ +-comm hi4 P4 ⟩
        P4 + hi4
          ≈⟨ cong (λ z → z + hi4) (sym e) ⟩
        lo4 + hi4
        ≤∎

  E≤S : E ≤ S
  E≤S = E≤S-go lo4-cases

  abs-key-double-sub-comm : ∀ a c → (a + a) - (c + a) ≡ a - c
  abs-key-double-sub-comm a c = begin
    (a + a) - (c + a)
      ≡⟨ cong (λ z → (a + a) - z) (+-comm c a) ⟩
    (a + a) - (a + c)
      ≡⟨ double-sub a c ⟩
    a - c
    ∎

  abs-key-upper : (S + S) - (D + E) ≤ w * w'
  abs-key-upper = begin≤
        (S + S) - (D + E)
          ≤⟨ sub-mono {a = S + S} {b = D + D} {c = D + E}
                      (+-mono-≤ S≤D S≤D) ⟩
        (D + D) - (D + E)
          ≈⟨ double-sub D E ⟩
        D - E
          ≈⟨ key ⟩
        w * w'
        ≤∎

  abs-key-lower : neg (w * w') ≤ (S + S) - (D + E)
  abs-key-lower = begin≤
        neg (w * w')
          ≈⟨ cong neg (sym key) ⟩
        neg (D - E)
          ≈⟨ negsub D E ⟩
        E - D
          ≈⟨ sym (abs-key-double-sub-comm E D) ⟩
        (E + E) - (D + E)
          ≤⟨ sub-mono {a = E + E} {b = S + S} {c = D + E}
                      (+-mono-≤ E≤S E≤S) ⟩
        (S + S) - (D + E)
        ≤∎

  abs-key : ∣ (S + S) - (D + E) ∣ ≤ w * w'
  abs-key = abs-≤ abs-key-lower abs-key-upper

  0≤hh : 0ℚ ≤ half * half
  0≤hh = mul-nonNeg 0≤half 0≤half

  step1 : S * half - (D + E) * (half * half)
        ≡ ((S + S) - (D + E)) * (half * half)
  step1 = final-alg S D E

  step2 : ∣ ((S + S) - (D + E)) * (half * half) ∣
        ≤ (w * w') * (half * half)
  step2 = begin≤
        ∣ ((S + S) - (D + E)) * (half * half) ∣
          ≈⟨ ∣p*q∣≡∣p∣*∣q∣ ((S + S) - (D + E)) (half * half) ⟩
        ∣ (S + S) - (D + E) ∣ * ∣ half * half ∣
          ≈⟨ cong (λ z → ∣ (S + S) - (D + E) ∣ * z)
                  (0≤p⇒∣p∣≡p {half * half} 0≤hh) ⟩
        ∣ (S + S) - (D + E) ∣ * (half * half)
          ≤⟨ *-monoʳ-≤-nonNeg (half * half) {{nonNegative 0≤hh}} abs-key ⟩
        (w * w') * (half * half)
        ≤∎

  step3 : (w * w') * (half * half) ≤ (w * w') * half
  step3 = *-monoˡ-≤-nonNeg (w * w')
            {{nonNegative (mul-nonNeg 0≤w 0≤w')}} half*half≤half

  proof : ∣ centre (x *ℝ y) n - centre x (2 ℕ* n) * centre y (2 ℕ* n) ∣
            ≤ (width x (2 ℕ* n) * width y (2 ℕ* n)) ÷ embed 2
  proof = begin≤
        ∣ centre (x *ℝ y) n - centre x (2 ℕ* n) * centre y (2 ℕ* n) ∣
          ≈⟨ cong (λ z → ∣ z - centre x (2 ℕ* n) * centre y (2 ℕ* n) ∣)
                  c-xy ⟩
        ∣ S * half - centre x (2 ℕ* n) * centre y (2 ℕ* n) ∣
          ≈⟨ cong (λ z → ∣ S * half - z ∣) c-cc ⟩
        ∣ S * half - (D + E) * (half * half) ∣
          ≈⟨ cong ∣_∣ step1 ⟩
        ∣ ((S + S) - (D + E)) * (half * half) ∣
          ≤⟨ step2 ⟩
        (w * w') * (half * half)
          ≤⟨ step3 ⟩
        (w * w') * half
        ≤∎

------------------------------------------------------------------------
-- Centre of product vs product of centres
--
-- 乘积的中心与中心之积

centre-*ℝ≤ : (x y : RealI) (n : ℕ) →
  ∣ centre (x *ℝ y) n - centre x (2 ℕ* n) * centre y (2 ℕ* n) ∣
    ≤ (width x (2 ℕ* n) * width y (2 ℕ* n)) ÷ embed 2
centre-*ℝ≤ x y n = CentreCore.proof x y n

------------------------------------------------------------------------
-- Generic convergence helpers
--
-- 通用收敛辅助引理

centre-mag : (x : RealI) →
  Σ ℚ (λ M → 0ℚ ≤ M × (∀ n → ∣ centre x n ∣ ≤ M))
centre-mag x =
  let M , 0≤M , inside = bounded x
  in M , 0≤M , λ n → inside n (centre x n) (centre-l x n) (centre-u x n)

tri-add : ∀ p q P Q → ∣ (p + q) - (P + Q) ∣ ≤ ∣ p - P ∣ + ∣ q - Q ∣
tri-add p q P Q = begin≤
      ∣ (p + q) - (P + Q) ∣
        ≈⟨ cong ∣_∣ (sub-add p q P Q) ⟩
      ∣ (p - P) + (q - Q) ∣
        ≤⟨ ∣p+q∣≤∣p∣+∣q∣ (p - P) (q - Q) ⟩
      ∣ p - P ∣ + ∣ q - Q ∣
      ≤∎

add3-eq : ∀ A B C r → A * r + (B * r + C * r) ≡ (A + (B + C)) * r
add3-eq A B C r = begin
  A * r + (B * r + C * r)
    ≡⟨ cong (A * r +_) (sym (*-distribʳ-+ r B C)) ⟩
  A * r + (B + C) * r
    ≡⟨ sym (*-distribʳ-+ r A (B + C)) ⟩
  (A + (B + C)) * r
  ∎

mul-shift : ∀ {a b M : ℚ} → 0ℚ ≤ M → a ≤ b → M * a ≤ M * b
mul-shift {a} {b} {M} 0≤M = *-monoˡ-≤-nonNeg M {{nonNegative 0≤M}}

sub-distribˡ : ∀ a b c → a * (b - c) ≡ a * b - a * c
sub-distribˡ a b c = begin
  a * (b - c)
    ≡⟨ *-distribˡ-+ a b (neg c) ⟩
  a * b + a * neg c
    ≡⟨ cong (a * b +_) (sym (neg-distribʳ-* a c)) ⟩
  a * b + neg (a * c)
  ∎

telesc2 : ∀ p p' q q' → p * q - p' * q' ≡ q * (p - p') + p' * (q - q')
telesc2 p p' q q' = sym (begin
  q * (p - p') + p' * (q - q')
    ≡⟨ cong₂ _+_ (sub-distribˡ q p p') (sub-distribˡ p' q q') ⟩
  (q * p - q * p') + (p' * q - p' * q')
    ≡⟨ cong (_+ (p' * q - p' * q'))
            (cong₂ _-_ (*-comm q p) (*-comm q p')) ⟩
  (p * q - p' * q) + (p' * q - p' * q')
    ≡⟨ telescope (p * q) (p' * q) (p' * q') ⟩
  p * q - p' * q'
  ∎)

------------------------------------------------------------------------
-- Closed-form bound on the centre error of multiplication
--
-- 乘法中心误差的闭式界

term1-raw-eq : (w0 wR0 r : ℚ) →
  (w0 * r) * (wR0 * r) ≡ w0 * wR0 * (r * r)
term1-raw-eq w0 wR0 r = begin
  (w0 * r) * (wR0 * r)
    ≡⟨ sym (*-assoc (w0 * r) wR0 r) ⟩
  ((w0 * r) * wR0) * r
    ≡⟨ cong (_* r) (*-comm (w0 * r) wR0) ⟩
  (wR0 * (w0 * r)) * r
    ≡⟨ cong (_* r) (sym (*-assoc wR0 w0 r)) ⟩
  ((wR0 * w0) * r) * r
    ≡⟨ *-assoc (wR0 * w0) r r ⟩
  (wR0 * w0) * (r * r)
    ≡⟨ cong (λ z → z * (r * r)) (*-comm wR0 w0) ⟩
  (w0 * wR0) * (r * r)
  ∎

term1-prod : (x R : RealI) (n : ℕ) →
  width x (2 ℕ* n) * width R (2 ℕ* n)
    ≤ width x 0 * width R 0 * recipPow2 n
term1-prod x R n = begin≤
      width x (2 ℕ* n) * width R (2 ℕ* n)
        ≤⟨ *-mono-≤-nonNeg
            (0≤width-n x (2 ℕ* n)) (width-rec x n)
            (0≤width-n R (2 ℕ* n)) (width-rec R n) ⟩
      (width x 0 * recipPow2 n) * (width R 0 * recipPow2 n)
        ≈⟨ term1-raw-eq (width x 0) (width R 0) (recipPow2 n) ⟩
      width x 0 * width R 0 * (recipPow2 n * recipPow2 n)
        ≤⟨ *-monoˡ-≤-nonNeg (width x 0 * width R 0)
            {{nonNegative (mul-nonNeg (0≤width-n x 0)
                                      (0≤width-n R 0))}}
            (rr≤r {r = recipPow2 n} (0≤recipPow2 n) (recipPow2≤1 n)) ⟩
      width x 0 * width R 0 * recipPow2 n
      ≤∎

term1-final-eq : (w0 wR0 : ℚ) (n : ℕ) →
  (w0 * wR0 * recipPow2 n) * half ≡ (w0 * wR0 * half) * recipPow2 n
term1-final-eq w0 wR0 n = begin
  (w0 * wR0 * recipPow2 n) * half
    ≡⟨ *-assoc (w0 * wR0) (recipPow2 n) half ⟩
  w0 * wR0 * (recipPow2 n * half)
    ≡⟨ cong (w0 * wR0 *_) (*-comm (recipPow2 n) half) ⟩
  w0 * wR0 * (half * recipPow2 n)
    ≡⟨ sym (*-assoc (w0 * wR0) half (recipPow2 n)) ⟩
  (w0 * wR0 * half) * recipPow2 n
  ∎

term1-step : (x R : RealI) (n : ℕ) →
  (width x (2 ℕ* n) * width R (2 ℕ* n)) * half
    ≤ (width x 0 * width R 0 * half) * recipPow2 n
term1-step x R n = begin≤
      (width x (2 ℕ* n) * width R (2 ℕ* n)) * half
        ≤⟨ *-monoʳ-≤-nonNeg half {{nonNegative 0≤half}} (term1-prod x R n) ⟩
      (width x 0 * width R 0 * recipPow2 n) * half
        ≈⟨ term1-final-eq (width x 0) (width R 0) n ⟩
      (width x 0 * width R 0 * half) * recipPow2 n
      ≤∎

term1 :
    (x R : RealI) (n : ℕ) →
    ∣ centre (x *ℝ R) n - centre x (2 ℕ* n) * centre R (2 ℕ* n) ∣
      ≤ (width x 0 * width R 0 * half) * recipPow2 n
term1 x R n = begin≤
      ∣ centre (x *ℝ R) n - centre x (2 ℕ* n) * centre R (2 ℕ* n) ∣
        ≤⟨ centre-*ℝ≤ x R n ⟩
      (width x (2 ℕ* n) * width R (2 ℕ* n)) * half
        ≤⟨ term1-step x R n ⟩
      (width x 0 * width R 0 * half) * recipPow2 n
      ≤∎
