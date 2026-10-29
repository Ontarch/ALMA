------------------------------------------------------------------------
-- Absolute value: nonnegativity, triangle inequality, evenness
--
-- 绝对值：非负性、三角不等式、偶性
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module Real.Interval.AbsTriangle where

open import Data.Product using (_,_; proj₁; proj₂)
open import Data.Sum.Base using (inj₁; inj₂)
open import Data.Nat using (ℕ; suc; _⊔_) renaming (_+_ to _+N_; _≤_ to _≤N_)
open import Data.Nat.Properties using (m≤n⊔m; m≤m⊔n; +-suc; +-identityʳ)
open import Data.Rational using
  (ℚ; 0ℚ; 1ℚ; _+_; _-_; _*_; _≤_; _<_; _≥_; ∣_∣; positive) renaming (-_ to neg)
open import Data.Rational.Base using (nonNegative)
open import Data.Rational.Properties as QP using
  (≤-refl; ≤-reflexive; ≤-trans; <⇒≤; +-mono-≤; +-mono-<-≤; +-comm; +-assoc
  ; +-identityˡ; +-inverseʳ; +-inverseˡ; *-assoc; *-identityˡ; *-identityʳ
  ; *-distribʳ-+; *-distribˡ-+; pos⇒nonNeg; ∣p+q∣≤∣p∣+∣q∣; ∣p-q∣≤∣p∣+∣q∣
  ; 0≤∣p∣; 0≤p⇒∣p∣≡p; ∣-p∣≡∣p∣; *-monoˡ-≤-nonNeg; ≤-total; neg-distrib-+
  ; neg-antimono-≤; neg-antimono-<; ∣p*q∣≡∣p∣*∣q∣)
open import Function.Base using (case_of_)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; cong; cong₂; sym; trans; subst; module ≡-Reasoning)
open ≡-Reasoning

open import Base.RationalRing using (+interchange)
open import Real using (embed; half; 2ℚ≡1+1)
open import Real.Interval using (RealI; δ; δ-pos; dyadic)
open import Real.Interval.Arith using (0ℝ; _+ℝ_; negℝ)
open import Real.Interval.Equiv using (_≈ℝ_)
open import Real.IntervalEquiv using
  (l; u; centre; width; width-n; centre-l; centre-u; l-mono; u-mono; node
  ; recipPow2; node-suc)
open import Real.Interval.Node using
  (centre-add; 0≤width-n; l-hom; u-hom; l-neg; u-neg)
open import Real.Interval.Abs using
  (∣_∣ℝ; absLo; absHi; lo-pos; hi-pos; lo-neg; hi-neg; lo-mid)
open import Real.Interval.Rational using (max; ≤maxʳ; max≤)
open import Real.Interval.Kit using
  (≈ℝ-of-rec; half+half≡1; 0≤recipPow2; recipPow2-mul; recipPow2-n≤1
  ; recipPow2-≤; halveQ; half≥0'; halveQ-mono; 0≤halveQ; halveQ-distrib
  ; halveQ-neg; x≤∣x∣; same⇒diff0; 0≤diff; move-≤; move-≤-back; neg-of-nonpos
  ; npos⇒∣p∣≡neg; tail-bound; neg-neg; 0<embed2)
open import Real.Interval.OrderComplete.Base using (_≤ℝ_)
open import Real.Interval.Reasoning using (begin≤_; _≤⟨_⟩_; _≤∎)

------------------------------------------------------------------------
-- The absolute value of [l, u] versus the absolute value of its centre
--
-- ∣[l,u]∣ 的中心与 [l,u] 中心的绝对值之差不超过区间宽度。

abs-centre-≤ : (l u : ℚ) (l≤u : l ≤ u) →
  ∣ halveQ (absLo l u + absHi l u) - ∣ halveQ (l + u) ∣ ∣ ≤ u - l
abs-centre-≤ l u l≤u with ≤-total l 0ℚ | ≤-total u 0ℚ
... | inj₂ 0≤l | _ =
      let 0≤u = ≤-trans 0≤l l≤u
          lp = lo-pos 0≤l 0≤u
          hp = hi-pos 0≤l 0≤u
          A≡ : halveQ (absLo l u + absHi l u) ≡ halveQ (l + u)
          A≡ = trans (cong halveQ (cong₂ _+_ lp hp)) refl
          0≤c : 0ℚ ≤ halveQ (l + u)
          0≤c =
            let 0≤sum : 0ℚ ≤ l + u
                0≤sum = +-mono-≤ 0≤l 0≤u
                h : halveQ 0ℚ ≤ halveQ (l + u)
                h = halveQ-mono 0≤sum
                h0 : halveQ 0ℚ ≡ 0ℚ
                h0 = QP.*-zeroˡ half
            in subst (λ z → z ≤ halveQ (l + u)) (sym h0) h
          B≡ : ∣ halveQ (l + u) ∣ ≡ halveQ (l + u)
          B≡ = 0≤p⇒∣p∣≡p 0≤c
          eq : halveQ (absLo l u + absHi l u) ≡ ∣ halveQ (l + u) ∣
          eq = trans A≡ (sym B≡)
      in subst (λ z → z ≤ u - l) (sym (same⇒diff0 eq))
           (0≤diff l≤u)
... | inj₁ l≤0 | inj₁ u≤0 =
      let l≤u' = l≤u
          lp = lo-neg l≤u' u≤0
          hp = hi-neg l≤u' u≤0
          A≡ : halveQ (absLo l u + absHi l u) ≡ neg (halveQ (l + u))
          A≡ = begin
            halveQ (absLo l u + absHi l u)
              ≡⟨ cong halveQ (cong₂ _+_ lp hp) ⟩
            halveQ (neg u + neg l)
              ≡⟨ halveQ-distrib (neg u) (neg l) ⟩
            halveQ (neg u) + halveQ (neg l)
              ≡⟨ cong₂ _+_ (halveQ-neg u) (halveQ-neg l) ⟩
            neg (halveQ u) + neg (halveQ l)
              ≡⟨ QP.+-comm (neg (halveQ u)) (neg (halveQ l)) ⟩
            neg (halveQ l) + neg (halveQ u)
              ≡⟨ sym (neg-distrib-+ (halveQ l) (halveQ u)) ⟩
            neg (halveQ l + halveQ u)
              ≡⟨ cong neg (sym (halveQ-distrib l u)) ⟩
            neg (halveQ (l + u)) ∎
          su≤0 : l + u ≤ 0ℚ
          su≤0 = begin≤ l + u
            ≤⟨ +-mono-≤ l≤0 u≤0 ⟩ 0ℚ + 0ℚ
            ≤⟨ ≤-reflexive (+-identityˡ 0ℚ) ⟩ 0ℚ ≤∎
          c≤0 : halveQ (l + u) ≤ 0ℚ
          c≤0 =
            let h : halveQ (l + u) ≤ halveQ 0ℚ
                h = halveQ-mono su≤0
                h0 : halveQ 0ℚ ≡ 0ℚ
                h0 = QP.*-zeroˡ half
            in subst (λ z → halveQ (l + u) ≤ z) h0 h
          B≡ : ∣ halveQ (l + u) ∣ ≡ neg (halveQ (l + u))
          B≡ = npos⇒∣p∣≡neg c≤0
          eq : halveQ (absLo l u + absHi l u) ≡ ∣ halveQ (l + u) ∣
          eq = trans A≡ (sym B≡)
      in subst (λ z → z ≤ u - l) (sym (same⇒diff0 eq))
           (0≤diff l≤u)
... | inj₁ l≤0 | inj₂ 0≤u =
      let p = u
          q = neg l
          p≥0 = 0≤u
          q≥0 = neg-of-nonpos l≤0
          lp = lo-mid l≤0 p≥0
          A≡ : halveQ (absLo l u + absHi l u) ≡ halveQ (max p q)
          A≡ = begin
            halveQ (absLo l u + absHi l u)
              ≡⟨ cong (λ z → halveQ (z + absHi l u)) lp ⟩
            halveQ (0ℚ + absHi l u)
              ≡⟨ cong halveQ (+-identityˡ (absHi l u)) ⟩
            halveQ (max p q) ∎
          s≡ : l + u ≡ p - q
          s≡ = begin l + u
            ≡⟨ +-comm l u ⟩ u + l
            ≡⟨ cong (u +_) (sym (neg-neg l)) ⟩ u + neg (neg l)
            ≡⟨ refl ⟩ p - q ∎
          B≡ : ∣ halveQ (l + u) ∣ ≡ halveQ ∣ p - q ∣
          B≡ = begin
            ∣ halveQ (l + u) ∣
              ≡⟨ cong ∣_∣ (cong halveQ s≡) ⟩
            ∣ halveQ (p - q) ∣
              ≡⟨ ∣p*q∣≡∣p∣*∣q∣ (p - q) half ⟩
            ∣ p - q ∣ * ∣ half ∣
              ≡⟨ cong (∣ p - q ∣ *_) (0≤p⇒∣p∣≡p half≥0') ⟩
            ∣ p - q ∣ * half
              ≡⟨ refl ⟩
            halveQ ∣ p - q ∣ ∎
          max≤pq : max p q ≤ p + q
          max≤pq = max≤ (begin≤ p
                          ≤⟨ ≤-reflexive (sym (QP.+-identityʳ p)) ⟩ p + 0ℚ
                          ≤⟨ +-mono-≤ (≤-refl {p}) q≥0 ⟩ p + q ≤∎)
                        (begin≤ q
                          ≤⟨ ≤-reflexive (sym (QP.+-identityʳ q)) ⟩ q + 0ℚ
                          ≤⟨ +-mono-≤ (≤-refl {q}) p≥0 ⟩ q + p
                          ≤⟨ ≤-reflexive (+-comm q p) ⟩ p + q ≤∎)
          diff≤pq : ∣ p - q ∣ ≤ p + q
          diff≤pq = begin≤ ∣ p - q ∣
            ≤⟨ ∣p-q∣≤∣p∣+∣q∣ p q ⟩ ∣ p ∣ + ∣ q ∣
            ≤⟨ ≤-reflexive (cong₂ _+_ (0≤p⇒∣p∣≡p p≥0) (0≤p⇒∣p∣≡p q≥0)) ⟩
            p + q ≤∎
          0≤max : 0ℚ ≤ max p q
          0≤max = begin≤ 0ℚ
            ≤⟨ q≥0 ⟩ q
            ≤⟨ ≤maxʳ p q ⟩ max p q ≤∎
          bound : ∣ halveQ (max p q) - halveQ ∣ p - q ∣ ∣ ≤ p + q
          bound =
            let a = halveQ (max p q)
                b = halveQ ∣ p - q ∣
                s1 : ∣ a ∣ + ∣ b ∣ ≤ a + b
                s1 = ≤-reflexive
                       (cong₂ _+_ (0≤p⇒∣p∣≡p (0≤halveQ 0≤max))
                                 (0≤p⇒∣p∣≡p (0≤halveQ (0≤∣p∣ (p - q)))))
                s2 : a + b ≤ halveQ (p + q) + halveQ (p + q)
                s2 = +-mono-≤ (halveQ-mono max≤pq) (halveQ-mono diff≤pq)
                s3 : halveQ (p + q) + halveQ (p + q) ≤ p + q
                s3 = ≤-reflexive
                  let x = p + q
                  in begin x * half + x * half
                       ≡⟨ sym (*-distribˡ-+ x half half) ⟩ x * (half + half)
                       ≡⟨ cong (x *_) half+half≡1 ⟩ x * 1ℚ
                       ≡⟨ *-identityʳ x ⟩ x ∎
            in ≤-trans (∣p-q∣≤∣p∣+∣q∣ a b)
                       (≤-trans s1 (≤-trans s2 s3))
          eq : halveQ (absLo l u + absHi l u) ≡ halveQ (max p q)
          eq = A≡
          X = halveQ (absLo l u + absHi l u)
          Y = halveQ (max p q)
          Z = ∣ halveQ (l + u) ∣
          W = halveQ ∣ p - q ∣
          diff-eq : ∣ X - Z ∣ ≡ ∣ Y - W ∣
          diff-eq = cong₂ (λ a b → ∣ a - b ∣) eq B≡
      in subst (λ t → t ≤ p + q) (sym diff-eq) bound

------------------------------------------------------------------------
-- Triangle inequality at the centre level
--
-- The centre of the absolute value of a sum interval is bounded by the
-- sum of the summands' absolute-value centres plus twice the sum of the
-- widths.
--
-- 中心层的三角不等式
--
-- 和区间绝对值的中心，被各加子绝对值中心之和加上两倍宽度和界住。

abs-centre-triangle :
  (l1 u1 l2 u2 : ℚ) (l1≤u1 : l1 ≤ u1) (l2≤u2 : l2 ≤ u2) →
  let w1 = u1 - l1
      w2 = u2 - l2
      A = halveQ (absLo (l1 + l2) (u1 + u2) + absHi (l1 + l2) (u1 + u2))
      B = halveQ (absLo l1 u1 + absHi l1 u1)
      C = halveQ (absLo l2 u2 + absHi l2 u2)
  in A - (B + C) ≤ embed 2 * (w1 + w2)
abs-centre-triangle l1 u1 l2 u2 l1≤u1 l2≤u2 =
  let w1 = u1 - l1
      w2 = u2 - l2
      sum≤ : l1 + l2 ≤ u1 + u2
      sum≤ = +-mono-≤ l1≤u1 l2≤u2
      A = halveQ (absLo (l1 + l2) (u1 + u2) + absHi (l1 + l2) (u1 + u2))
      B = halveQ (absLo l1 u1 + absHi l1 u1)
      C = halveQ (absLo l2 u2 + absHi l2 u2)
      p = halveQ (l1 + u1)
      q = halveQ (l2 + u2)
      centreSum : halveQ ((l1 + l2) + (u1 + u2)) ≡ p + q
      centreSum =
        let a = halveQ l1
            b = halveQ l2
            c = halveQ u1
            d = halveQ u2
            regroup : (a + b) + (c + d) ≡ (a + c) + (b + d)
            regroup =
              begin (a + b) + (c + d)
                ≡⟨ sym (+-assoc (a + b) c d) ⟩
              ((a + b) + c) + d
                ≡⟨ cong (_+ d) (+-assoc a b c) ⟩
              (a + (b + c)) + d
                ≡⟨ cong (λ z → (a + z) + d) (+-comm b c) ⟩
              (a + (c + b)) + d
                ≡⟨ cong (_+ d) (sym (+-assoc a c b)) ⟩
              ((a + c) + b) + d
                ≡⟨ +-assoc (a + c) b d ⟩
              (a + c) + (b + d) ∎
        in
        begin halveQ ((l1 + l2) + (u1 + u2))
          ≡⟨ halveQ-distrib (l1 + l2) (u1 + u2) ⟩
        halveQ (l1 + l2) + halveQ (u1 + u2)
          ≡⟨ cong₂ _+_ (halveQ-distrib l1 l2) (halveQ-distrib u1 u2) ⟩
        (a + b) + (c + d)
          ≡⟨ regroup ⟩
        (a + c) + (b + d)
          ≡⟨ cong₂ _+_ (sym (halveQ-distrib l1 u1)) (sym (halveQ-distrib l2 u2)) ⟩
        p + q ∎
      h1raw = abs-centre-≤ (l1 + l2) (u1 + u2) sum≤
      boundEq : (u1 + u2) - (l1 + l2) ≡ w1 + w2
      boundEq =
        begin (u1 + u2) - (l1 + l2)
          ≡⟨ cong ((u1 + u2) +_) (neg-distrib-+ l1 l2) ⟩
        (u1 + u2) + (neg l1 + neg l2)
          ≡⟨ +interchange u1 u2 (neg l1) (neg l2) ⟩
        (u1 + neg l1) + (u2 + neg l2)
          ≡⟨ refl ⟩
        w1 + w2 ∎
      h1 : ∣ A - ∣ halveQ ((l1 + l2) + (u1 + u2)) ∣ ∣ ≤ w1 + w2
      h1 = subst (λ z → ∣ A - ∣ halveQ ((l1 + l2) + (u1 + u2)) ∣ ∣ ≤ z)
             boundEq h1raw
      h1' : ∣ A - ∣ p + q ∣ ∣ ≤ w1 + w2
      h1' = subst (λ z → ∣ A - ∣ z ∣ ∣ ≤ w1 + w2) centreSum h1
      h2 = abs-centre-≤ l1 u1 l1≤u1
      h3 = abs-centre-≤ l2 u2 l2≤u2
      abs-neg : {X w : ℚ} → ∣ X ∣ ≤ w → neg X ≤ w
      abs-neg {X} {w} h =
        let k : neg X ≤ ∣ neg X ∣
            k = x≤∣x∣ (neg X)
            e : ∣ neg X ∣ ≡ ∣ X ∣
            e = ∣-p∣≡∣p∣ X
        in ≤-trans k (≤-trans (≤-reflexive e) h)
      s1 : A - ∣ p + q ∣ ≤ w1 + w2
      s1 = ≤-trans (x≤∣x∣ (A - ∣ p + q ∣)) h1'
      s2 : ∣ p + q ∣ ≤ ∣ p ∣ + ∣ q ∣
      s2 = ∣p+q∣≤∣p∣+∣q∣ p q
      s3 : ∣ p ∣ - B ≤ w1
      s3 =
        let e : neg (B - ∣ p ∣) ≡ ∣ p ∣ - B
            e =
              begin neg (B - ∣ p ∣)
                ≡⟨ neg-distrib-+ B (neg ∣ p ∣) ⟩
              neg B + neg (neg ∣ p ∣)
                ≡⟨ cong (neg B +_) (neg-neg ∣ p ∣) ⟩
              neg B + ∣ p ∣
                ≡⟨ +-comm (neg B) ∣ p ∣ ⟩
              ∣ p ∣ + neg B
                ≡⟨ refl ⟩
              ∣ p ∣ - B ∎
        in subst (λ z → z ≤ w1) e (abs-neg h2)
      s4 : ∣ q ∣ - C ≤ w2
      s4 =
        let e : neg (C - ∣ q ∣) ≡ ∣ q ∣ - C
            e =
              begin neg (C - ∣ q ∣)
                ≡⟨ neg-distrib-+ C (neg ∣ q ∣) ⟩
              neg C + neg (neg ∣ q ∣)
                ≡⟨ cong (neg C +_) (neg-neg ∣ q ∣) ⟩
              neg C + ∣ q ∣
                ≡⟨ +-comm (neg C) ∣ q ∣ ⟩
              ∣ q ∣ + neg C
                ≡⟨ refl ⟩
              ∣ q ∣ - C ∎
        in subst (λ z → z ≤ w2) e (abs-neg h3)
      t1 : A ≤ ∣ p + q ∣ + (w1 + w2)
      t1 = move-≤ s1
      t3 : ∣ p ∣ ≤ B + w1
      t3 = move-≤ s3
      t4 : ∣ q ∣ ≤ C + w2
      t4 = move-≤ s4
      rearrange : (B + w1) + (C + w2) ≡ B + C + (w1 + w2)
      rearrange =
        begin (B + w1) + (C + w2)
          ≡⟨ sym (+-assoc (B + w1) C w2) ⟩
        B + w1 + C + w2
          ≡⟨ cong (λ z → z + w2)
                  (begin (B + w1) + C
                    ≡⟨ +-assoc B w1 C ⟩
                  B + (w1 + C)
                    ≡⟨ cong (B +_) (+-comm w1 C) ⟩
                  B + (C + w1) ∎) ⟩
        (B + (C + w1)) + w2
          ≡⟨ +-assoc B (C + w1) w2 ⟩
        B + ((C + w1) + w2)
          ≡⟨ cong (B +_) (+-assoc C w1 w2) ⟩
        B + (C + (w1 + w2))
          ≡⟨ sym (+-assoc B C (w1 + w2)) ⟩
        B + C + (w1 + w2) ∎
      t5 : ∣ p ∣ + ∣ q ∣ ≤ B + C + (w1 + w2)
      t5 =
        subst (λ z → ∣ p ∣ + ∣ q ∣ ≤ z) rearrange
          (+-mono-≤ t3 t4)
      t2 : ∣ p + q ∣ + (w1 + w2) ≤
             (∣ p ∣ + ∣ q ∣) + (w1 + w2)
      t2 = +-mono-≤ s2 (≤-refl {w1 + w2})
      t6 : A ≤ B + C + embed 2 * (w1 + w2)
      t6 =
        let up : (∣ p ∣ + ∣ q ∣) + (w1 + w2) ≤
                   (B + C + (w1 + w2)) + (w1 + w2)
            up = +-mono-≤ t5 (≤-refl {w1 + w2})
            chain : A ≤ (B + C + (w1 + w2)) + (w1 + w2)
            chain = ≤-trans (≤-trans t1 t2) up
            double : embed 2 * (w1 + w2) ≡ (w1 + w2) + (w1 + w2)
            double =
              begin embed 2 * (w1 + w2)
                ≡⟨ cong (λ z → z * (w1 + w2)) 2ℚ≡1+1 ⟩
              (1ℚ + 1ℚ) * (w1 + w2)
                ≡⟨ *-distribʳ-+ (w1 + w2) 1ℚ 1ℚ ⟩
              (1ℚ * (w1 + w2)) + (1ℚ * (w1 + w2))
                ≡⟨ cong₂ _+_ (*-identityˡ (w1 + w2)) (*-identityˡ (w1 + w2)) ⟩
              (w1 + w2) + (w1 + w2) ∎
            merge :
              (B + C + (w1 + w2)) + (w1 + w2) ≡
              B + C + embed 2 * (w1 + w2)
            merge =
              let w = w1 + w2
              in
              begin (B + C + w) + w
                ≡⟨ +-assoc (B + C) w w ⟩
              (B + C) + (w + w)
                ≡⟨ cong ((B + C) +_) (sym double) ⟩
              (B + C) + embed 2 * w ∎
        in subst (λ z → A ≤ z) merge chain
  in let t6' : A ≤ (B + C) + embed 2 * (w1 + w2)
         t6' =
           let t6right : B + C + embed 2 * (w1 + w2) ≡
                          (B + C) + embed 2 * (w1 + w2)
               t6right = refl
           in subst (λ z → A ≤ z) (sym t6right) t6
     in move-≤-back t6'

-- Non-strict order from a recursive centre bound.
--
-- If the centre gap is bounded by a decaying geometric series at every
-- level, then A ≤ℝ B.  Contrapositively, B < A gives a fixed positive
-- gap between A's lower endpoint and B's upper endpoint at some level,
-- which the decaying bound cannot match.
--
-- 由递归中心界得到非严格序
--
-- 若中心差在每一层都被同一个几何衰减界控制，则该非严格序成立。
-- 反证：B < A 会在某一层给出 A 的下端点与 B 的上端点之间固定的
-- 正间隙，而衰减界无法与之匹配。
≤ℝ-of-rec : (A B : RealI) (C : ℚ) → 0ℚ ≤ C →
  (h : ∀ n → centre A n - centre B n ≤ C * recipPow2 n) →
  A ≤ℝ B
≤ℝ-of-rec A B C 0≤C h (n0 , gap) =
  let d = l A n0 - u B n0
      0<d : 0ℚ < d
      0<d =
        let raw : u B n0 + neg (u B n0) < l A n0 + neg (u B n0)
            raw = +-mono-<-≤ gap (≤-refl {neg (u B n0)})
            zeroeq : u B n0 + neg (u B n0) ≡ 0ℚ
            zeroeq = +-inverseʳ (u B n0)
        in subst (λ z → z < l A n0 + neg (u B n0)) zeroeq raw
      tb = tail-bound C 0≤C d 0<d
      m0 = proj₁ tb
      h2 = proj₂ tb
      m = n0 ⊔ m0
      m0≤m : m0 ≤N m
      m0≤m = m≤n⊔m n0 m0
      m≥n0 : n0 ≤N m
      m≥n0 = m≤m⊔n n0 m0
      cA≥l0 : centre A m ≥ l A n0
      cA≥l0 =
        let p : l A n0 ≤ l A m
            p = l-mono A m≥n0
            q : l A m ≤ centre A m
            q = centre-l A m
        in ≤-trans p q
      cB≤u0 : centre B m ≤ u B n0
      cB≤u0 =
        let p : centre B m ≤ u B m
            p = centre-u B m
            q : u B m ≤ u B n0
            q = u-mono B m≥n0
        in ≤-trans p q
      diff≥d : centre A m - centre B m ≥ d
      diff≥d = +-mono-≤ cA≥l0 (neg-antimono-≤ cB≤u0)
      upper : centre A m - centre B m < d
      upper = QP.≤-<-trans (h m) (h2 m m0≤m)
  in let dd : d < d
         dd = QP.≤-<-trans diff≥d upper
     in QP.<-irrefl refl dd

-- Nesting a dyadic interval n times yields the dyadic at depth k + n.
--
-- 嵌套 dyadic n 次后得到深度为 k + n 的 dyadic。
node-dyadic : (q : ℚ) (k n : ℕ) → node (dyadic q k) n ≡ dyadic q (k +N n)
node-dyadic q k 0 =
  begin node (dyadic q k) 0
    ≡⟨ refl ⟩
  dyadic q k
    ≡⟨ cong (dyadic q) (sym (+-identityʳ k)) ⟩
  dyadic q (k +N 0) ∎
node-dyadic q k (suc n) =
  begin node (dyadic q k) (suc n)
    ≡⟨ node-suc (dyadic q k) n ⟩
  node (RealI.next (dyadic q k)) n
    ≡⟨ cong (λ z → node z n) refl ⟩
  node (dyadic q (suc k)) n
    ≡⟨ node-dyadic q (suc k) n ⟩
  dyadic q (suc k +N n)
    ≡⟨ cong (dyadic q) (sym (+-suc k n)) ⟩
  dyadic q (k +N suc n) ∎

-- The lower endpoint of 0ℝ at level n is the negated dyadic tolerance.
--
-- 0ℝ 在第 n 层的下端点是取负的二进容差。
l0ℝ : (n : ℕ) → l 0ℝ n ≡ neg (δ n)
l0ℝ n =
  let eq : node 0ℝ n ≡ dyadic 0ℚ n
      eq = node-dyadic 0ℚ 0 n
  in subst (λ z → RealI.l z ≡ neg (δ n)) (sym eq)
       (let e : RealI.l (dyadic 0ℚ n) ≡ neg (δ n)
            e =
              begin RealI.l (dyadic 0ℚ n)
                ≡⟨ refl ⟩
              neg (δ n) + 0ℚ
                ≡⟨ QP.+-identityʳ (neg (δ n)) ⟩
              neg (δ n) ∎
        in e)

labs-nonneg : (x : RealI) (n : ℕ) → 0ℚ ≤ RealI.l (node ∣ x ∣ℝ n)
labs-nonneg x 0 = ≤maxʳ (max (RealI.l x) (neg (RealI.u x))) 0ℚ
labs-nonneg x (suc n) =
  let nx = RealI.next (RealI.next x)
      eq : node ∣ x ∣ℝ (suc n) ≡ node ∣ nx ∣ℝ n
      eq =
        begin node ∣ x ∣ℝ (suc n)
          ≡⟨ node-suc ∣ x ∣ℝ n ⟩
        node (RealI.next ∣ x ∣ℝ) n
          ≡⟨ cong (λ z → node z n) refl ⟩
        node ∣ nx ∣ℝ n ∎
  in subst (λ z → 0ℚ ≤ RealI.l z) (sym eq) (labs-nonneg nx n)

------------------------------------------------------------------------
-- Nonnegativity
--
-- The lower endpoint of the absolute value is a max with 0, hence at
-- least 0.  If the absolute value were below 0ℝ, its upper endpoint
-- would be below the (negative) lower endpoint of 0ℝ, contradicting
-- the nonnegativity of its endpoints.
--
-- 非负性
--
-- 绝对值的下端点是 absLo，它是与 0 的 max，故不小于 0。若绝对值
-- 小于 0ℝ，其上端点会小于 0ℝ 的下端点（为负），与其端点的非负性
-- 矛盾。

abs-nonneg : (x : RealI) → 0ℝ ≤ℝ ∣ x ∣ℝ
abs-nonneg x (n , h) =
  let l0≤0 : 0ℚ ≤ l ∣ x ∣ℝ n
      l0≤0 = labs-nonneg x n
      u≥l : l ∣ x ∣ℝ n ≤ u ∣ x ∣ℝ n
      u≥l = <⇒≤ (RealI.lo (node ∣ x ∣ℝ n))
      u≥0 : u ∣ x ∣ℝ n ≥ 0ℚ
      u≥0 = ≤-trans l0≤0 u≥l
      l0ℝ≡ : l 0ℝ n ≡ neg (δ n)
      l0ℝ≡ = l0ℝ n
      negδ<0 : neg (δ n) < 0ℚ
      negδ<0 = subst (λ z → neg (δ n) < z) (sym (QP.+-identityʳ 0ℚ))
                 (neg-antimono-< (δ-pos n))
      h' : u ∣ x ∣ℝ n < neg (δ n)
      h' = subst (λ z → u ∣ x ∣ℝ n < z) l0ℝ≡ h
      u<0 : u ∣ x ∣ℝ n < 0ℚ
      u<0 = QP.<-trans h' negδ<0
  in let dd : 0ℚ < 0ℚ
         dd = QP.≤-<-trans u≥0 u<0
     in QP.<-irrefl refl dd

------------------------------------------------------------------------
-- Toolkit lemmas for the norm development
--
-- 范数开发所需的工具引理

-- The absolute value walks two interval layers per step.
--
-- 绝对值每走一步，底层区间走两步。
node-abs : (x : RealI) (n : ℕ) → node ∣ x ∣ℝ n ≡ ∣ node x (n +N n) ∣ℝ
node-abs x 0 =
  begin node ∣ x ∣ℝ 0
    ≡⟨ refl ⟩
  ∣ x ∣ℝ
    ≡⟨ refl ⟩
  ∣ node x 0 ∣ℝ
    ≡⟨ cong ∣_∣ℝ (cong (node x) (sym (+-identityʳ 0))) ⟩
  ∣ node x (0 +N 0) ∣ℝ ∎
node-abs x (suc n) =
  begin node ∣ x ∣ℝ (suc n)
    ≡⟨ node-suc ∣ x ∣ℝ n ⟩
  node (RealI.next ∣ x ∣ℝ) n
    ≡⟨ cong (λ z → node z n) refl ⟩
  node ∣ RealI.next (RealI.next x) ∣ℝ n
    ≡⟨ node-abs (RealI.next (RealI.next x)) n ⟩
  ∣ node (RealI.next (RealI.next x)) (n +N n) ∣ℝ
    ≡⟨ cong ∣_∣ℝ
       (begin node (RealI.next (RealI.next x)) (n +N n)
         ≡⟨ sym (node-suc (RealI.next x) (n +N n)) ⟩
       node (RealI.next x) (suc (n +N n))
         ≡⟨ sym (node-suc x (suc (n +N n))) ⟩
       node x (suc (suc (n +N n)))
         ≡⟨ cong (node x) (sym (cong suc (+-suc n n))) ⟩
       node x ((suc n) +N (suc n)) ∎) ⟩
  ∣ node x ((suc n) +N (suc n)) ∣ℝ ∎

l-abs-node : (x : RealI) (n : ℕ) →
  RealI.l (node ∣ x ∣ℝ n) ≡
  absLo (l x (n +N n)) (u x (n +N n))
l-abs-node x n =
  let e : node ∣ x ∣ℝ n ≡ ∣ node x (n +N n) ∣ℝ
      e = node-abs x n
  in subst (λ z → RealI.l z ≡ absLo (l x (n +N n)) (u x (n +N n))) (sym e) refl

u-abs-node : (x : RealI) (n : ℕ) →
  RealI.u (node ∣ x ∣ℝ n) ≡
  absHi (l x (n +N n)) (u x (n +N n))
u-abs-node x n =
  let e : node ∣ x ∣ℝ n ≡ ∣ node x (n +N n) ∣ℝ
      e = node-abs x n
  in subst (λ z → RealI.u z ≡ absHi (l x (n +N n)) (u x (n +N n))) (sym e) refl

-- The centre of the n-th absolute-value layer is determined by the
-- endpoints of the 2n-th interval layer.
--
-- 第 n 层绝对值的中心，由第 2n 层区间的端点决定。
centre-abs-node : (x : RealI) (n : ℕ) →
  centre ∣ x ∣ℝ n ≡
  halveQ (absLo (l x (n +N n)) (u x (n +N n)) +
         absHi (l x (n +N n)) (u x (n +N n)))
centre-abs-node x n =
  begin centre ∣ x ∣ℝ n
    ≡⟨ refl ⟩
  halveQ (RealI.l (node ∣ x ∣ℝ n) + RealI.u (node ∣ x ∣ℝ n))
    ≡⟨ cong₂ (λ a b → halveQ (a + b)) (l-abs-node x n) (u-abs-node x n) ⟩
  halveQ (absLo (l x (n +N n)) (u x (n +N n)) +
         absHi (l x (n +N n)) (u x (n +N n))) ∎

------------------------------------------------------------------------
-- Triangle inequality: ∣ x + y ∣ ≤ℝ ∣ x ∣ + ∣ y ∣
--
-- At level n the centre gap is bounded by twice the sum of the widths,
-- which decays geometrically.  The bound is fed to ≤ℝ-of-rec.
--
-- 三角不等式
--
-- 在第 n 层，中心差被宽度之和的两倍界住，该界几何衰减，交给
-- ≤ℝ-of-rec。

abs-triangle : (x y : RealI) →
  ∣ x +ℝ y ∣ℝ ≤ℝ ∣ x ∣ℝ +ℝ ∣ y ∣ℝ
abs-triangle x y =
  let s0 = width x 0 + width y 0
      C = embed 2 * s0
      s0≥0 : 0ℚ ≤ s0
      s0≥0 = +-mono-≤ (0≤width-n x 0) (0≤width-n y 0)
      0≤C : 0ℚ ≤ C
      0≤C =
        let p : embed 2 * 0ℚ ≤ embed 2 * s0
            p = *-monoˡ-≤-nonNeg (embed 2)
                  {{pos⇒nonNeg (embed 2) {{positive 0<embed2}}}} s0≥0
            z : embed 2 * 0ℚ ≡ 0ℚ
            z = QP.*-zeroʳ (embed 2)
        in subst (λ z → z ≤ C) z p
      h : ∀ n →
        centre ∣ x +ℝ y ∣ℝ n - centre (∣ x ∣ℝ +ℝ ∣ y ∣ℝ) n
        ≤ C * recipPow2 n
      h n =
        let nn = n +N n
            l1d = l x nn
            u1d = u x nn
            l2d = l y nn
            u2d = u y nn
            l1d≤u1d : l1d ≤ u1d
            l1d≤u1d = <⇒≤ (RealI.lo (node x nn))
            l2d≤u2d : l2d ≤ u2d
            l2d≤u2d = <⇒≤ (RealI.lo (node y nn))
            main = abs-centre-triangle l1d u1d l2d u2d l1d≤u1d l2d≤u2d
            A = halveQ (absLo (l1d + l2d) (u1d + u2d) +
                       absHi (l1d + l2d) (u1d + u2d))
            Bd = halveQ (absLo l1d u1d + absHi l1d u1d)
            Cd = halveQ (absLo l2d u2d + absHi l2d u2d)
            Bn = centre ∣ x ∣ℝ n
            Cn = centre ∣ y ∣ℝ n
            Aeq : centre ∣ x +ℝ y ∣ℝ n ≡ A
            Aeq =
              let pl : l (x +ℝ y) nn ≡ l1d + l2d
                  pl = l-hom x y nn
                  pu : u (x +ℝ y) nn ≡ u1d + u2d
                  pu = u-hom x y nn
              in
              begin centre ∣ x +ℝ y ∣ℝ n
                ≡⟨ refl ⟩
              halveQ (RealI.l (node ∣ x +ℝ y ∣ℝ n) +
                     RealI.u (node ∣ x +ℝ y ∣ℝ n))
                ≡⟨ cong₂ (λ a b → halveQ (a + b))
                       (l-abs-node (x +ℝ y) n) (u-abs-node (x +ℝ y) n) ⟩
              halveQ (absLo (l (x +ℝ y) nn) (u (x +ℝ y) nn) +
                     absHi (l (x +ℝ y) nn) (u (x +ℝ y) nn))
                ≡⟨ cong₂ (λ a b → halveQ (absLo a b + absHi a b)) pl pu ⟩
              A ∎
            Beq : centre (∣ x ∣ℝ +ℝ ∣ y ∣ℝ) n ≡ Bn + Cn
            Beq = centre-add ∣ x ∣ℝ ∣ y ∣ℝ n
            s1 : A - (Bd + Cd) ≤ embed 2 * ((u1d - l1d) + (u2d - l2d))
            s1 = main
            eq : Bn + Cn ≡ Bd + Cd
            eq =
              begin Bn + Cn
                ≡⟨ cong₂ _+_ (centre-abs-node x n) (centre-abs-node y n) ⟩
              Bd + Cd ∎
            s2 : A - (Bn + Cn) ≤ embed 2 * ((u1d - l1d) + (u2d - l2d))
            s2 = subst (λ z → A - z ≤ embed 2 * ((u1d - l1d) + (u2d - l2d)))
                   (sym eq) s1
            w1d≤ : width x nn ≤ width x 0 * recipPow2 n
            w1d≤ =
              let p : width x nn ≤ width x 0 * recipPow2 nn
                  p = width-n x nn
                  r = recipPow2 n
                  0≤r : 0ℚ ≤ r
                  0≤r = 0≤recipPow2 n
                  q : recipPow2 nn ≤ r
                  q =
                    let e : recipPow2 nn ≡ r * r
                        e = recipPow2-mul n n
                        s : r * r ≤ r
                        s =
                          subst (λ z → r * r ≤ z) (*-identityʳ r)
                            (*-monoˡ-≤-nonNeg r {{nonNegative 0≤r}}
                              (recipPow2-n≤1 n))
                    in QP.≤-trans (≤-reflexive e) s
                in ≤-trans p (*-monoˡ-≤-nonNeg (width x 0)
                                {{nonNegative (0≤width-n x 0)}} q)
            w2d≤ : width y nn ≤ width y 0 * recipPow2 n
            w2d≤ =
              let p : width y nn ≤ width y 0 * recipPow2 nn
                  p = width-n y nn
                  r = recipPow2 n
                  0≤r : 0ℚ ≤ r
                  0≤r = 0≤recipPow2 n
                  q : recipPow2 nn ≤ r
                  q =
                    let e : recipPow2 nn ≡ r * r
                        e = recipPow2-mul n n
                        s : r * r ≤ r
                        s =
                          subst (λ z → r * r ≤ z) (*-identityʳ r)
                            (*-monoˡ-≤-nonNeg r {{nonNegative 0≤r}}
                              (recipPow2-n≤1 n))
                    in QP.≤-trans (≤-reflexive e) s
              in ≤-trans p (*-monoˡ-≤-nonNeg (width y 0)
                              {{nonNegative (0≤width-n y 0)}} q)
            wsum≤ : (u1d - l1d) + (u2d - l2d) ≤ s0 * recipPow2 n
            wsum≤ =
              let p : width x nn + width y nn ≤
                        (width x 0 * recipPow2 n) + (width y 0 * recipPow2 n)
                  p = +-mono-≤ w1d≤ w2d≤
                  dist :
                    (width x 0 * recipPow2 n) + (width y 0 * recipPow2 n)
                    ≡ s0 * recipPow2 n
                  dist = sym (*-distribʳ-+ (recipPow2 n) (width x 0) (width y 0))
              in subst (λ z → width x nn + width y nn ≤ z) dist p
            double≤ : embed 2 * ((u1d - l1d) + (u2d - l2d)) ≤
                      embed 2 * (s0 * recipPow2 n)
            double≤ = *-monoˡ-≤-nonNeg (embed 2)
                        {{pos⇒nonNeg (embed 2) {{positive 0<embed2}}}} wsum≤
            last : embed 2 * (s0 * recipPow2 n) ≡ C * recipPow2 n
            last =
              begin embed 2 * (s0 * recipPow2 n)
                ≡⟨ sym (*-assoc (embed 2) s0 (recipPow2 n)) ⟩
              (embed 2 * s0) * recipPow2 n
                ≡⟨ refl ⟩
              C * recipPow2 n ∎
        in ≤-trans
             (subst (λ z → centre ∣ x +ℝ y ∣ℝ n - z ≤
                           embed 2 * (s0 * recipPow2 n))
               (sym Beq)
               (subst (λ z → z - (Bn + Cn) ≤
                             embed 2 * (s0 * recipPow2 n))
                 (sym Aeq)
                 (≤-trans s2 double≤)))
             (≤-reflexive last)
  in ≤ℝ-of-rec ∣ x +ℝ y ∣ℝ (∣ x ∣ℝ +ℝ ∣ y ∣ℝ) C 0≤C h

-- Algebraic identity: A - B = (A - C) + (C - B).
--
-- 代数恒等式：A - B = (A - C) + (C - B)。
abs-centre-even-helper : (A B C : ℚ) →
  A - B ≤ (A - C) + (C - B)
abs-centre-even-helper A B C =
  let e : (A - C) + (C - B) ≡ A - B
      e =
        begin (A + neg C) + (C + neg B)
          ≡⟨ sym (+-assoc (A + neg C) C (neg B)) ⟩
        A + neg C + C + neg B
          ≡⟨ cong (λ z → z + neg B)
                  (begin (A + neg C) + C
                    ≡⟨ +-assoc A (neg C) C ⟩
                  A + (neg C + C)
                    ≡⟨ cong (A +_) (+-inverseˡ C) ⟩
                  A + 0ℚ
                    ≡⟨ QP.+-identityʳ A ⟩ A ∎) ⟩
        A + neg B ∎
  in ≤-reflexive (sym e)

------------------------------------------------------------------------
-- Evenness at the centre level
--
-- The centres of the absolute values of a negated interval and the
-- original interval differ by at most twice the width.
--
-- 中心层的偶性
--
-- 取负区间绝对值的中心与原区间绝对值的中心之差至多为宽度的两倍。

abs-centre-even : (l u : ℚ) (l≤u : l ≤ u) →
  let A = halveQ (absLo (neg u) (neg l) + absHi (neg u) (neg l))
      B = halveQ (absLo l u + absHi l u)
  in ∣ A - B ∣ ≤ embed 2 * (u - l)
abs-centre-even l u l≤u =
  let w = u - l
      neg≤ : neg u ≤ neg l
      neg≤ =
        let p : l ≤ u
            p = l≤u
        in neg-antimono-≤ p
      A = halveQ (absLo (neg u) (neg l) + absHi (neg u) (neg l))
      B = halveQ (absLo l u + absHi l u)
      c = halveQ (l + u)
      pneg = halveQ (neg u + neg l)
      pneg≡ : pneg ≡ neg c
      pneg≡ =
        begin pneg
          ≡⟨ halveQ-distrib (neg u) (neg l) ⟩
        halveQ (neg u) + halveQ (neg l)
          ≡⟨ cong (_+ halveQ (neg l)) (halveQ-neg u) ⟩
        neg (halveQ u) + halveQ (neg l)
          ≡⟨ cong (neg (halveQ u) +_) (halveQ-neg l) ⟩
        neg (halveQ u) + neg (halveQ l)
          ≡⟨ sym (neg-distrib-+ (halveQ u) (halveQ l)) ⟩
        neg (halveQ u + halveQ l)
          ≡⟨ cong neg (+-comm (halveQ u) (halveQ l)) ⟩
        neg (halveQ l + halveQ u)
          ≡⟨ cong neg (sym (halveQ-distrib l u)) ⟩
        neg (halveQ (l + u)) ∎
      h1 = abs-centre-≤ (neg u) (neg l) neg≤
      h2 = abs-centre-≤ l u l≤u
      neg-eq : (neg l) - (neg u) ≡ w
      neg-eq =
        begin (neg l) - (neg u)
          ≡⟨ cong (neg l +_) (neg-neg u) ⟩
        neg l + u
          ≡⟨ +-comm (neg l) u ⟩
        u + neg l
          ≡⟨ refl ⟩
        u - l
          ≡⟨ refl ⟩
        w ∎

      h1' : ∣ A - ∣ pneg ∣ ∣ ≤ w
      h1' = subst (λ z → ∣ A - ∣ pneg ∣ ∣ ≤ z) neg-eq h1
      h2' : ∣ B - ∣ c ∣ ∣ ≤ w
      h2' = h2
      abs≡ : ∣ pneg ∣ ≡ ∣ c ∣
      abs≡ =
        begin ∣ pneg ∣
          ≡⟨ cong ∣_∣ pneg≡ ⟩
        ∣ neg c ∣
          ≡⟨ ∣-p∣≡∣p∣ c ⟩
        ∣ c ∣ ∎
      main : ∣ A - B ∣ ≤ embed 2 * w
      main =
        let e1 : ∣ A - ∣ c ∣ ∣ ≤ w
            e1 = subst (λ z → ∣ A - z ∣ ≤ w) abs≡ h1'
            t1 : A - ∣ c ∣ ≤ w
            t1 = ≤-trans (x≤∣x∣ (A - ∣ c ∣)) e1
            a-aux : ∣ c ∣ - B ≡ neg (B - ∣ c ∣)
            a-aux = begin
              ∣ c ∣ - B
                ≡⟨⟩
              ∣ c ∣ + neg B
                ≡⟨ +-comm ∣ c ∣ (neg B) ⟩
              neg B + ∣ c ∣
                ≡⟨ cong (neg B +_) (sym (neg-neg ∣ c ∣)) ⟩
              neg B + neg (neg ∣ c ∣)
                ≡⟨ sym (neg-distrib-+ B (neg ∣ c ∣)) ⟩
              neg (B + neg ∣ c ∣)
                ≡⟨⟩
              neg (B - ∣ c ∣) ∎

            t2 : ∣ c ∣ - B ≤ w
            t2 = subst (λ z → z ≤ w) (sym a-aux)
                   (≤-trans (x≤∣x∣ (neg (B - ∣ c ∣)))
                            (≤-trans (≤-reflexive (∣-p∣≡∣p∣ (B - ∣ c ∣))) h2'))
            s : A - B ≤ w + w
            s =
              let k : A - B ≤ (A - ∣ c ∣) + (∣ c ∣ - B)
                  k = abs-centre-even-helper A B ∣ c ∣
                  d : (A - ∣ c ∣) + (∣ c ∣ - B) ≤ w + w
                  d = +-mono-≤ t1 t2
              in ≤-trans k d
            t1' : B - ∣ c ∣ ≤ w
            t1' = ≤-trans (x≤∣x∣ (B - ∣ c ∣)) h2'

            a-aux' : ∣ c ∣ - A ≡ neg (A - ∣ c ∣)
            a-aux' = begin
              ∣ c ∣ - A
                ≡⟨⟩
              ∣ c ∣ + neg A
                ≡⟨ +-comm ∣ c ∣ (neg A) ⟩
              neg A + ∣ c ∣
                ≡⟨ cong (neg A +_) (sym (neg-neg ∣ c ∣)) ⟩
              neg A + neg (neg ∣ c ∣)
                ≡⟨ sym (neg-distrib-+ A (neg ∣ c ∣)) ⟩
              neg (A + neg ∣ c ∣)
                ≡⟨⟩
              neg (A - ∣ c ∣) ∎

            t2' : ∣ c ∣ - A ≤ w
            t2' = subst (λ z → z ≤ w) (sym a-aux')
                    (≤-trans (x≤∣x∣ (neg (A - ∣ c ∣)))
                             (≤-trans (≤-reflexive (∣-p∣≡∣p∣ (A - ∣ c ∣))) e1))

            s' : B - A ≤ w + w
            s' =
              let k' : B - A ≤ (B - ∣ c ∣) + (∣ c ∣ - A)
                  k' = abs-centre-even-helper B A ∣ c ∣
                  d' : (B - ∣ c ∣) + (∣ c ∣ - A) ≤ w + w
                  d' = +-mono-≤ t1' t2'
              in ≤-trans k' d'

            neg-sub : (a b : ℚ) → neg (a - b) ≡ b - a
            neg-sub a b =
              begin
                neg (a - b)
                  ≡⟨ neg-distrib-+ a (neg b) ⟩
                neg a + neg (neg b)
                  ≡⟨ cong (neg a +_) (neg-neg b) ⟩
                neg a + b
                  ≡⟨ +-comm (neg a) b ⟩
                b + neg a
                  ∎

            sAbs : ∣ A - B ∣ ≤ w + w
            sAbs = case_of_ {B = ∣ A - B ∣ ≤ w + w}
                     (QP.∣p∣≡p∨∣p∣≡-p (A - B))
                     λ { (inj₁ abs≡') →
                           subst (λ z → z ≤ w + w) (sym abs≡') s
                       ; (inj₂ abs≡') →
                           subst (λ z → z ≤ w + w)
                                  (sym (trans abs≡' (neg-sub A B))) s'
                       }
            double : w + w ≡ embed 2 * w
            double =
              begin w + w
                ≡⟨ cong₂ _+_ (sym (*-identityˡ w)) (sym (*-identityˡ w)) ⟩
              1ℚ * w + 1ℚ * w
                ≡⟨ sym (*-distribʳ-+ w 1ℚ 1ℚ) ⟩
              (1ℚ + 1ℚ) * w
                ≡⟨ cong (_* w) (sym 2ℚ≡1+1) ⟩
              embed 2 * w ∎
        in subst (λ z → ∣ A - B ∣ ≤ z) double sAbs
  in main

------------------------------------------------------------------------
-- Evenness
--
-- 偶性

abs-even : (x : RealI) → ∣ negℝ x ∣ℝ ≈ℝ ∣ x ∣ℝ
abs-even x =
  let C = embed 2 * width x 0
      C≥0 : 0ℚ ≤ C
      C≥0 =
        let w≥0 : 0ℚ ≤ width x 0
            w≥0 = 0≤width-n x 0
            p : embed 2 * 0ℚ ≤ embed 2 * width x 0
            p = *-monoˡ-≤-nonNeg (embed 2)
                  {{pos⇒nonNeg (embed 2) {{positive 0<embed2}}}} w≥0
            z : embed 2 * 0ℚ ≡ 0ℚ
            z = QP.*-zeroʳ (embed 2)
        in subst (λ z → z ≤ C) z p
      h : ∀ n →
        ∣ centre ∣ negℝ x ∣ℝ n - centre ∣ x ∣ℝ n ∣ ≤ C * recipPow2 n
      h n =
        let l0 = l x (n +N n)
            u0 = u x (n +N n)
            l0≤u0 : l0 ≤ u0
            l0≤u0 = <⇒≤ (RealI.lo (node x (n +N n)))
            main = abs-centre-even l0 u0 l0≤u0
            Aeq : centre ∣ negℝ x ∣ℝ n ≡
                  halveQ (absLo (neg u0) (neg l0) + absHi (neg u0) (neg l0))
            Aeq =
              let e = centre-abs-node (negℝ x) n
                  pl : l (negℝ x) (n +N n) ≡ neg u0
                  pl = l-neg x (n +N n)
                  pu : u (negℝ x) (n +N n) ≡ neg l0
                  pu = u-neg x (n +N n)
              in trans e
                   (cong₂ (λ a b → halveQ (absLo a b + absHi a b)) pl pu)
            main' :
              ∣ centre ∣ negℝ x ∣ℝ n - centre ∣ x ∣ℝ n ∣ ≤
              embed 2 * (u0 - l0)
            main' =
              let A = halveQ (absLo (neg u0) (neg l0) + absHi (neg u0) (neg l0))
                  B = halveQ (absLo l0 u0 + absHi l0 u0)
                  Beq : centre ∣ x ∣ℝ n ≡ B
                  Beq = centre-abs-node x n
                  eq : centre ∣ negℝ x ∣ℝ n - centre ∣ x ∣ℝ n ≡ A - B
                  eq = cong₂ _-_ Aeq Beq
              in subst (λ z → ∣ z ∣ ≤ embed 2 * (u0 - l0)) (sym eq) main
            w≤ : width x (n +N n) ≤ width x 0 * recipPow2 n
            w≤ =
              let p : width x (n +N n) ≤ width x 0 * recipPow2 (n +N n)
                  p = width-n x (n +N n)
                  q : recipPow2 (n +N n) ≤ recipPow2 n
                  q = recipPow2-≤ n
              in ≤-trans p
                   (*-monoˡ-≤-nonNeg (width x 0)
                      {{nonNegative (0≤width-n x 0)}} q)
            double≤ : embed 2 * (u0 - l0) ≤
                      embed 2 * (width x 0 * recipPow2 n)
            double≤ = *-monoˡ-≤-nonNeg (embed 2)
                        {{pos⇒nonNeg (embed 2) {{positive 0<embed2}}}} w≤
            last : embed 2 * (width x 0 * recipPow2 n) ≡ C * recipPow2 n
            last =
              begin
                embed 2 * (width x 0 * recipPow2 n)
                  ≡⟨ sym (*-assoc (embed 2) (width x 0) (recipPow2 n)) ⟩
                (embed 2 * width x 0) * recipPow2 n
                  ≡⟨ refl ⟩
                C * recipPow2 n ∎
        in ≤-trans main' (≤-trans double≤ (≤-reflexive last))
  in ≈ℝ-of-rec ∣ negℝ x ∣ℝ ∣ x ∣ℝ C C≥0 h
