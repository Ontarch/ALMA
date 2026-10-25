------------------------------------------------------------------------
-- CauchyI is a special case of WeakCauchy
--
-- CauchyI 是 WeakCauchy 的特例
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module Real.Interval.WeakCompleteFromCauchyI where

open import Data.Nat using (suc; _∸_; _^_; s≤s; z≤n)
  renaming (_≤_ to _≤N_; _≥_ to _≥N_; _+_ to _+ℕ_; _*_ to _*ℕ_; _<_ to _<N_)
open import Data.Nat.Properties using (m+[n∸m]≡n; +-suc; ^-monoʳ-≤)
  renaming (≤-trans to ≤N-trans; ≤-refl to ≤N-refl; +-comm to +-commℕ
  ; *-identityˡ to *-identityˡℕ; +-identityʳ to +-identityʳℕ; +-mono-≤ to +-mono-≤N)
open import Data.Product using (proj₁; proj₂; _,_)
open import Data.Rational using
  (0ℚ; _+_; _-_; _*_; _<_; _≤_; ∣_∣; positive; Positive; NonZero)
open import Data.Rational.Base using (1/_; -_)
open import Data.Rational.Properties using
  (≤-refl; ≤-trans; ≤-reflexive; ≤-<-trans; +-mono-<; +-mono-≤; +-assoc; +-comm
  ; pos⇒nonZero; pos*pos⇒pos; positive⁻¹; <⇒≤; *-monoˡ-<-pos)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; cong; cong₂; sym; trans; subst; module ≡-Reasoning)
open ≡-Reasoning

open import Real using
  (ε; embed; 2ℚ; 2*embed; halve; reciprocal-cong; 0<embed; embed-mono-<)
open import Real.IntervalEquiv using
  (centre; width; width-n; recipPow2; centre-diff)
open import Real.Interval.Kit using (0<recipPow2; tri-diff)
open import Real.Interval.RegularRep using (i; reg; fold≥k+4)
open import Real.Interval.WeakArith using
  (half; half*recipPow2; 2ss; 2ss-eq; εs-half; strict-recip; 4k+8<2^k+4
  ; 4k+8<4k+10; H+H≡budget)
open import Real.Interval.Complete using (CauchyI)
open import Real.Interval.WeakComplete using (WeakCauchy)

CauchyI→WeakCauchy : ∀ {f} → CauchyI f → WeakCauchy f
CauchyI→WeakCauchy {f} cf k = N , step
  where
  μI = proj₁ cf
  μI≥ = proj₁ (proj₂ cf)
  μI-mono = proj₁ (proj₂ (proj₂ cf))
  cond = proj₂ (proj₂ (proj₂ cf))
  width-cond : ∀ i n → n ≥N μI i → width (f n) i < ε i * half
  width-cond i = proj₁ (cond i)
  centre-cond : ∀ i n m → n ≥N μI i → m ≥N μI i →
                  ∣ centre (f n) n - centre (f m) m ∣ < ε i * half
  centre-cond i = proj₂ (cond i)

  t = suc(suc(suc(suc k)))
  q1 = suc(suc k) +ℕ suc(suc k)

  N = μI q1

  width-t< : ∀ n → n ≥N μI 0 → width (f n) t < recipPow2 (suc t)
  width-t< n n≥μ0 =
    ≤-<-trans (width-n (f n) t)
      (subst (λ z → width (f n) 0 * recipPow2 t < z) (half*recipPow2 t)
        (*-monoˡ-<-pos (recipPow2 t)
           {{positive (0<recipPow2 t)}}
           (width-cond 0 n n≥μ0)))

  step : ∀ n m → n ≥N N → m ≥N N →
    ∣ reg (f n) (suc k) - reg (f m) (suc k) ∣ < ε (suc k) * half
  step n m n≥N m≥N =
    let
      n≥μ0 = ≤N-trans (μI-mono 0 q1 z≤n) n≥N
      m≥μ0 = ≤N-trans (μI-mono 0 q1 z≤n) m≥N
      2≤k+2 : 2 ≤N suc(suc k)
      2≤k+2 = s≤s (s≤s (z≤n {k}))
      t≤q1 : t ≤N q1
      t≤q1 = +-mono-≤N 2≤k+2 (≤N-refl {suc(suc k)})
      n≥t = ≤N-trans t≤q1 (≤N-trans (μI≥ q1) n≥N)
      m≥t = ≤N-trans t≤q1 (≤N-trans (μI≥ q1) m≥N)

      A = reg (f n) (suc k)
      B = centre (f n) n
      C = centre (f m) m
      D = reg (f m) (suc k)

      gap1 : ∣ A - B ∣ < recipPow2 (suc t)
      gap1 = ≤-<-trans (centre-diff (f n) t (i (f n) (suc k)) n
                                   (fold≥k+4 (f n) k) n≥t)
                       (width-t< n n≥μ0)
      gap2 : ∣ C - D ∣ < recipPow2 (suc t)
      gap2 = ≤-<-trans (centre-diff (f m) t m (i (f m) (suc k))
                                   m≥t (fold≥k+4 (f m) k))
                       (width-t< m m≥μ0)

      gapM : ∣ B - C ∣ < ε q1 * half
      gapM = centre-cond q1 n m n≥N m≥N

      tri≤ : ∣ A - D ∣ ≤ ∣ A - B ∣ + (∣ B - C ∣ + ∣ C - D ∣)
      tri≤ = ≤-trans (tri-diff A B D)
              (+-mono-≤ (≤-refl {x = ∣ A - B ∣}) (tri-diff B C D))

      X = recipPow2 (suc t)
      Y = ε q1 * half
      H = 1/ embed (4 *ℕ suc(suc k))

      ab = ∣ A - B ∣
      bc = ∣ B - C ∣
      cd = ∣ C - D ∣
      reorder : ab + (bc + cd) ≡ (ab + cd) + bc
      reorder =
        begin
          ab + (bc + cd)
            ≡⟨ cong (ab +_) (+-comm bc cd) ⟩
          ab + (cd + bc)
            ≡⟨ sym (+-assoc ab cd bc) ⟩
          (ab + cd) + bc
          ∎

      pair< : ∣ A - B ∣ + ∣ C - D ∣ < X + X
      pair< = +-mono-< gap1 gap2
      dT = suc (2 ^ t ∸ 1)
      dT≡2^t : dT ≡ 2 ^ t
      dT≡2^t = m+[n∸m]≡n {1} {2 ^ t} (^-monoʳ-≤ 2 (z≤n {t}))
      dA = suc (2 ^ suc t ∸ 1)
      dA≡ : dA ≡ 2 *ℕ dT
      dA≡ =
        begin
          dA
            ≡⟨ m+[n∸m]≡n {1} {2 ^ suc t} (^-monoʳ-≤ 2 (z≤n {suc t})) ⟩
          2 ^ suc t
            ≡⟨⟩
          2 *ℕ (2 ^ t)
            ≡⟨ cong (2 *ℕ_) (sym (m+[n∸m]≡n {1} {2 ^ t} (^-monoʳ-≤ 2 (z≤n {t})))) ⟩
          2 *ℕ dT
          ∎
      0<dT : 0ℚ < embed dT
      0<dT = 0<embed (2 ^ t ∸ 1)
      pos-dT : Positive (embed dT)
      pos-dT = positive 0<dT
      one-dT = 1/ (embed dT)
      instance
        nz-2dT : NonZero (2ℚ * embed dT)
        nz-2dT = pos⇒nonZero (2ℚ * embed dT)
                  {{pos*pos⇒pos 2ℚ (embed dT) {{pos-dT}}}}
      a≡b : embed dA ≡ 2ℚ * embed dT
      a≡b =
        trans (cong embed dA≡) (sym (2*embed dT))
      X≡ : X ≡ 1/ (2ℚ * embed dT)
      X≡ = reciprocal-cong (embed dA) (2ℚ * embed dT) a≡b
      eq : X + X ≡ 1/ embed dT
      eq =
        begin
          X + X
            ≡⟨ cong₂ _+_ X≡ X≡ ⟩
          1/ (2ℚ * embed dT) + 1/ (2ℚ * embed dT)
            ≡⟨ halve (embed dT) {{pos⇒nonZero (embed dT) {{pos-dT}}}}
                            {{nz-2dT}} ⟩
          one-dT
          ∎
      4a<dT : 4 *ℕ suc(suc k) <N dT
      4a<dT = subst (λ z → 4 *ℕ suc(suc k) <N z) (sym dT≡2^t)
                     (4k+8<2^k+4 k)
      recipPow2t<H : 1/ embed dT < H
      recipPow2t<H =
        strict-recip (embed (4 *ℕ suc(suc k))) (embed dT)
          (positive⁻¹ (embed (4 *ℕ suc(suc k))))
          (embed-mono-< 4a<dT)
      foldSum< : X + X < H
      foldSum< =
        subst (λ z → z < H) (sym eq) recipPow2t<H

      x = k +ℕ k
      y = suc(suc(suc(suc x)))
      cA = 4 *ℕ suc(suc k)
      cB = 2 *ℕ suc y
      k+k≡2k : k +ℕ k ≡ 2 *ℕ k
      k+k≡2k =
        cong (k +ℕ_) (sym (*-identityˡℕ k))
      cB-old = 2 *ℕ (2 *ℕ k +ℕ 5)
      x+4≡y : x +ℕ 4 ≡ y
      x+4≡y =
        begin
          x +ℕ 4
            ≡⟨ +-suc x 3 ⟩
          suc (x +ℕ 3)
            ≡⟨ cong suc (+-suc x 2) ⟩
          suc (suc (x +ℕ 2))
            ≡⟨ cong (λ z → suc(suc z)) (+-suc x 1) ⟩
          suc (suc (suc (x +ℕ 1)))
            ≡⟨ cong (λ z → suc(suc(suc z)))
                  (trans (+-suc x 0) (cong suc (+-identityʳℕ x))) ⟩
          y
          ∎
      y≡x+4 : y ≡ x +ℕ 4
      y≡x+4 = sym x+4≡y
      suc-y≡x+5 : suc y ≡ x +ℕ 5
      suc-y≡x+5 =
        begin
          suc y
            ≡⟨ cong suc y≡x+4 ⟩
          suc (x +ℕ 4)
            ≡⟨ sym (+-suc x 4) ⟩
          x +ℕ 5
          ∎
      cB≡old : cB ≡ cB-old
      cB≡old =
        begin
          cB
            ≡⟨ cong (2 *ℕ_) suc-y≡x+5 ⟩
          2 *ℕ (x +ℕ 5)
            ≡⟨ cong (2 *ℕ_) (cong (λ z → z +ℕ 5) k+k≡2k) ⟩
          cB-old
          ∎
      cA<cB : cA <N cB
      cA<cB = subst (λ z → cA <N z) (sym cB≡old)
                      (4k+8<4k+10 k)
      s : 1/ embed cB < 1/ embed cA
      s = strict-recip (embed cA) (embed cB)
            (positive⁻¹ (embed cA))
            (embed-mono-< cA<cB)
      q1m = suc(suc(suc (k +ℕ k)))
      q1≡ : q1 ≡ suc q1m
      q1≡ =
        begin
          q1
            ≡⟨ +-suc (suc(suc k)) (suc k) ⟩
          suc (suc(suc k) +ℕ suc k)
            ≡⟨ cong suc (+-suc (suc(suc k)) k) ⟩
          suc (suc (suc(suc k) +ℕ k))
            ≡⟨ cong (λ x → suc(suc x)) (+-commℕ (suc(suc k)) k) ⟩
          suc (suc (k +ℕ suc(suc k)))
            ≡⟨ cong (λ x → suc(suc x)) (+-suc k (suc k)) ⟩
          suc (suc (suc (k +ℕ suc k)))
            ≡⟨ cong (λ x → suc(suc(suc x))) (+-suc k k) ⟩
          suc q1m
          ∎
      2ssq1m≡ : 2ss q1m ≡ cB
      2ssq1m≡ =
        trans (2ss-eq q1m) refl
      Y≡ : Y ≡ 1/ embed cB
      Y≡ =
        begin
          Y
            ≡⟨ cong (λ z → ε z * half) q1≡ ⟩
          ε (suc q1m) * half
            ≡⟨ εs-half q1m ⟩
          1/ embed (2ss q1m)
            ≡⟨ reciprocal-cong (embed (2ss q1m)) (embed cB) (cong embed 2ssq1m≡) ⟩
          1/ embed cB
          ∎
      Y<H : Y < H
      Y<H = subst (λ z → z < H) (sym Y≡) s
      bc<H : bc < H
      bc<H = ≤-<-trans (<⇒≤ gapM) Y<H
      foldPair<H : ab + cd < H
      foldPair<H = ≤-<-trans (<⇒≤ pair<) foldSum<

      total< : (ab + cd) + bc < ε (suc k) * half
      total< =
        subst (λ z → (ab + cd) + bc < z)
              (H+H≡budget k)
              (+-mono-< foldPair<H bc<H)
    in ≤-<-trans (≤-trans tri≤ (≤-reflexive reorder)) total<
