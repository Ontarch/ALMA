------------------------------------------------------------------------
-- Multiplicative and distributive laws for RealI
--
-- Multiplication uses a two-level jump: node (x *ℝ y) n =
-- node x (2n) *ℝ node y (2n). The core lemma centre-*ℝ≈ therefore
-- compares the centre of the product interval with the product of the
-- centres at level 2n, and bounds the error by width·width·half. All
-- algebraic laws reduce to this bound plus the convergence engine
-- ≈ℝ-of-rec.
--
-- RealI 的乘法与分配律
--
-- 乘法采用两级跳跃：node (x *ℝ y) n = node x (2n) *ℝ node y (2n)。
-- 核心引理 centre-*ℝ≈ 因此比较乘积区间的中心与第 2n 层中心之积，
-- 并用 width·width·half 界定误差。所有代数律都归约到该界加上
-- 收敛引擎 ≈ℝ-of-rec。
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module ALMA.Base.Real.Interval.MulLaws where

open import Data.Nat using (ℕ; suc; s≤s; z≤n) renaming (_*_ to _ℕ*_)
import Data.Nat.Properties as ℕP
open import Data.Rational using
  (ℚ; 0ℚ; 1ℚ; _+_; _-_; _*_; _≤_; ∣_∣; nonNegative)
open import Data.Rational.Base using (_÷_) renaming (-_ to neg)
open import Data.Rational.Properties using
  (+-identityˡ; +-identityʳ; +-inverseʳ; +-assoc; +-comm; *-identityˡ; *-identityʳ
  ; *-zeroˡ; *-assoc; *-comm; *-distribʳ-+; *-distribˡ-+; neg-distribˡ-*
  ; neg-distribʳ-*; ≤-refl; ≤-reflexive; ≤-trans; <⇒≤; +-mono-≤; neg-antimono-≤
  ; *-monoˡ-≤-nonNeg; *-monoʳ-≤-nonNeg; ∣p+q∣≤∣p∣+∣q∣; ∣p∣≡p∨∣p∣≡-p
  ; 0≤∣p∣; ∣p*q∣≡∣p∣*∣q∣; 0≤p⇒∣p∣≡p)
open import Data.Product using (_,_; Σ; _×_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; cong; cong₂; trans; sym; subst)

open import ALMA.Base.Real using (embed; 2ℚ; 2ℚ≡1+1; telescope)
open import ALMA.Base.Real.Interval using (RealI; neg-invol)
open import ALMA.Base.Real.Interval.Arith using (0ℝ; 1ℝ; _+ℝ_)
open import ALMA.Base.Real.Interval.Mul using
  (_*ℝ_; 0≤diff; nn; cancelʳ; sub-mono; le-addˡ; le-addʳ)
import ALMA.Base.Real.Interval.Mul as MUL
open import ALMA.Base.Real.Interval.Bounded using (bounded)
open import ALMA.Base.Real.IntervalEquiv using
  (node; centre; width; width-n; centre-l; centre-u; centre-diff; 0<width; recipPow2)
open import ALMA.Base.Real.Interval.Equiv using (_≈ℝ_; ≈ℝ-trans)
open import ALMA.Base.Real.Interval.Rational using
  (min; max; max-eq; min-eq; sub-add; negsub)
open import ALMA.Base.Real.Interval.Kit using
  (half; ≈ℝ-of-rec; recipPow2-mono; n≤2n; 2n≤4n; *-mono-≤-nonNeg
  ; add-self; 2*2n≡4n; 0≤recipPow2; abs-swap; tri-diff; two-half; 2ℚ*half≡1
  ; 0≤half; half≤1; half-drop)
open import ALMA.Base.Real.Interval.Node using
  (node-*ℝ; centre-add; centre-0ℝ; centre-1ℝ; width-rec; width-rec4; width-prod
  ; width-sum-rec; width-x-sum; prod-rec; mul-pair; mul-nonNeg; add2-nonNeg; 0≤width-n; recipPow2≤1)
open import ALMA.Physics.RationalKit using (*ʳ-sub; +interchange)

------------------------------------------------------------------------
-- Private helpers for centre-*ℝ≈
--
-- centre-*ℝ≈ 的私有助手

private

  abs-≤ : ∀ {t C : ℚ} → neg C ≤ t → t ≤ C → ∣ t ∣ ≤ C
  abs-≤ {t} {C} h1 h2 with ∣p∣≡p∨∣p∣≡-p t
  ... | inj₁ e = ≤-trans (≤-reflexive e) h2
  ... | inj₂ e =
        ≤-trans (≤-reflexive e)
                (subst (λ z → neg t ≤ z) (neg-invol C)
                       (neg-antimono-≤ h1))

  add-diff : ∀ a b → a + (b - a) ≡ b
  add-diff a b = trans (+-comm a (b - a)) (cancelʳ b a)

  le-of-diff : ∀ {a b : ℚ} → 0ℚ ≤ b - a → a ≤ b
  le-of-diff {a} {b} 0≤ =
    subst (λ z → a ≤ z) (add-diff a b)
      (≤-trans (≤-reflexive (sym (+-identityʳ a)))
               (+-mono-≤ (≤-refl {a}) 0≤))

  half*half≤half : half * half ≤ half
  half*half≤half =
    ≤-trans (*-monoˡ-≤-nonNeg half {{nonNegative 0≤half}} half≤1)
            (≤-reflexive (*-identityʳ half))

  double-sub : ∀ a c → (a + a) - (a + c) ≡ a - c
  double-sub a c =
    trans (sub-add a a a c)
    (trans (cong (λ z → z + (a - c)) (+-inverseʳ a))
           (+-identityˡ (a - c)))

  half-scale : ∀ a → a * half ≡ (a + a) * (half * half)
  half-scale a =
    sym (trans (cong (_* (half * half)) (add-self a))
        (trans (*-assoc 2ℚ a (half * half))
        (trans (cong (2ℚ *_) (sym (*-assoc a half half)))
        (trans (cong (2ℚ *_) (*-comm (a * half) half))
        (trans (sym (*-assoc 2ℚ half (a * half)))
        (trans (cong (_* (a * half)) 2ℚ*half≡1)
               (*-identityˡ (a * half))))))))

  final-alg : ∀ S D E → S * half - (D + E) * (half * half)
                        ≡ ((S + S) - (D + E)) * (half * half)
  final-alg S D E =
    trans (cong (λ z → z - (D + E) * (half * half)) (half-scale S))
          (sym (*ʳ-sub (S + S) (D + E) (half * half)))

------------------------------------------------------------------------
-- Core lemma: centre of product vs product of centres
--
-- 核心引理：乘积的中心与中心之积

centre-*ℝ≈ : (x y : RealI) (n : ℕ) →
  ∣ centre (x *ℝ y) n - centre x (2 ℕ* n) * centre y (2 ℕ* n) ∣
    ≤ (width x (2 ℕ* n) * width y (2 ℕ* n)) ÷ embed 2
centre-*ℝ≈ x y n =
  subst (λ z → ∣ z - centre x (2 ℕ* n) * centre y (2 ℕ* n) ∣
                 ≤ (w * w') * half)
        (sym c-xy)
        (subst (λ z → ∣ S * half - z ∣ ≤ (w * w') * half)
               (sym c-cc)
               (≤-trans (≤-reflexive (cong ∣_∣ step1))
               (≤-trans step2 step3)))
  where
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
    expand =
      trans (*-distribʳ-+ (ly + uy) lx ux)
      (trans (cong₂ _+_ (*-distribˡ-+ lx ly uy) (*-distribˡ-+ ux ly uy))
      (trans (cong ((P1 + P2) +_) (+-comm P3 P4))
             (+interchange P1 P2 P4 P3)))

    c-cc : centre x (2 ℕ* n) * centre y (2 ℕ* n)
         ≡ (D + E) * (half * half)
    c-cc = trans (mul-pair (lx + ux) (ly + uy) half)
                 (cong (_* (half * half)) expand)

    hi4-cases : hi4 ≡ P1 ⊎ hi4 ≡ P2 ⊎ hi4 ≡ P3 ⊎ hi4 ≡ P4
    hi4-cases = combine (max-eq (max P1 P2) (max P3 P4))
      where
        fromL : max (max P1 P2) (max P3 P4) ≡ max P1 P2 →
                max P1 P2 ≡ P1 ⊎ max P1 P2 ≡ P2 →
                hi4 ≡ P1 ⊎ hi4 ≡ P2 ⊎ hi4 ≡ P3 ⊎ hi4 ≡ P4
        fromL e (inj₁ e2) = inj₁ (trans e e2)
        fromL e (inj₂ e2) = inj₂ (inj₁ (trans e e2))
        fromR : max (max P1 P2) (max P3 P4) ≡ max P3 P4 →
                max P3 P4 ≡ P3 ⊎ max P3 P4 ≡ P4 →
                hi4 ≡ P1 ⊎ hi4 ≡ P2 ⊎ hi4 ≡ P3 ⊎ hi4 ≡ P4
        fromR e (inj₁ e2) = inj₂ (inj₂ (inj₁ (trans e e2)))
        fromR e (inj₂ e2) = inj₂ (inj₂ (inj₂ (trans e e2)))
        combine : (max (max P1 P2) (max P3 P4) ≡ max P1 P2)
                ⊎ (max (max P1 P2) (max P3 P4) ≡ max P3 P4) →
                  hi4 ≡ P1 ⊎ hi4 ≡ P2 ⊎ hi4 ≡ P3 ⊎ hi4 ≡ P4
        combine (inj₁ e) = fromL e (max-eq P1 P2)
        combine (inj₂ e) = fromR e (max-eq P3 P4)

    lo4-cases : lo4 ≡ P1 ⊎ lo4 ≡ P2 ⊎ lo4 ≡ P3 ⊎ lo4 ≡ P4
    lo4-cases = combine (min-eq (min P1 P2) (min P3 P4))
      where
        fromL : min (min P1 P2) (min P3 P4) ≡ min P1 P2 →
                min P1 P2 ≡ P1 ⊎ min P1 P2 ≡ P2 →
                lo4 ≡ P1 ⊎ lo4 ≡ P2 ⊎ lo4 ≡ P3 ⊎ lo4 ≡ P4
        fromL e (inj₁ e2) = inj₁ (trans e e2)
        fromL e (inj₂ e2) = inj₂ (inj₁ (trans e e2))
        fromR : min (min P1 P2) (min P3 P4) ≡ min P3 P4 →
                min P3 P4 ≡ P3 ⊎ min P3 P4 ≡ P4 →
                lo4 ≡ P1 ⊎ lo4 ≡ P2 ⊎ lo4 ≡ P3 ⊎ lo4 ≡ P4
        fromR e (inj₁ e2) = inj₂ (inj₂ (inj₁ (trans e e2)))
        fromR e (inj₂ e2) = inj₂ (inj₂ (inj₂ (trans e e2)))
        combine : (min (min P1 P2) (min P3 P4) ≡ min P1 P2)
                ⊎ (min (min P1 P2) (min P3 P4) ≡ min P3 P4) →
                  lo4 ≡ P1 ⊎ lo4 ≡ P2 ⊎ lo4 ≡ P3 ⊎ lo4 ≡ P4
        combine (inj₁ e) = fromL e (min-eq P1 P2)
        combine (inj₂ e) = fromR e (min-eq P3 P4)

    c4-c3≡ : P4 - P3 ≡ ux * (uy - ly)
    c4-c3≡ =
      trans (sym (negsub P3 P4))
      (trans (cong neg C.c3-c4≡)
      (trans (neg-distribʳ-* ux (ly - uy))
             (cong (ux *_) (negsub ly uy))))

    key : D - E ≡ w * w'
    key =
      trans (sub-add P1 P4 P2 P3)
      (trans (cong₂ _+_ C.c1-c2≡ c4-c3≡)
      (trans (cong (λ z → z + ux * (uy - ly)) neg-step)
      (trans (sym (*-distribʳ-+ (uy - ly) (neg lx) ux))
      (trans (cong (λ z → z * (uy - ly)) (+-comm (neg lx) ux)) refl))))
      where
        neg-step : lx * (ly - uy) ≡ (neg lx) * (uy - ly)
        neg-step =
          trans (cong (lx *_) (sym (negsub uy ly)))
          (trans (sym (neg-distribʳ-* lx (uy - ly)))
                 (neg-distribˡ-* lx (uy - ly)))

    E≤D : E ≤ D
    E≤D = le-of-diff (≤-trans (mul-nonNeg 0≤w 0≤w') (≤-reflexive (sym key)))

    S≤D : S ≤ D
    S≤D = go hi4-cases
      where
        go : hi4 ≡ P1 ⊎ hi4 ≡ P2 ⊎ hi4 ≡ P3 ⊎ hi4 ≡ P4 → S ≤ D
        go (inj₁ e) =
          subst (λ z → lo4 + z ≤ D) (sym e)
            (≤-trans (+-mono-≤ C.lo4≤c4 (≤-refl {P1}))
                     (≤-reflexive (+-comm P4 P1)))
        go (inj₂ (inj₁ e)) =
          subst (λ z → lo4 + z ≤ D) (sym e)
            (≤-trans (+-mono-≤ C.lo4≤c3 (≤-refl {P2}))
            (≤-trans (≤-reflexive (+-comm P3 P2)) E≤D))
        go (inj₂ (inj₂ (inj₁ e))) =
          subst (λ z → lo4 + z ≤ D) (sym e)
            (≤-trans (+-mono-≤ C.lo4≤c2 (≤-refl {P3})) E≤D)
        go (inj₂ (inj₂ (inj₂ e))) =
          subst (λ z → lo4 + z ≤ D) (sym e)
            (+-mono-≤ C.lo4≤c1 (≤-refl {P4}))

    E≤S : E ≤ S
    E≤S = go lo4-cases
      where
        go : lo4 ≡ P1 ⊎ lo4 ≡ P2 ⊎ lo4 ≡ P3 ⊎ lo4 ≡ P4 → E ≤ S
        go (inj₁ e) =
          subst (λ z → E ≤ z + hi4) (sym e)
            (≤-trans E≤D (+-mono-≤ (≤-refl {P1}) C.c4≤hi4))
        go (inj₂ (inj₁ e)) =
          subst (λ z → E ≤ z + hi4) (sym e)
            (+-mono-≤ (≤-refl {P2}) C.c3≤hi4)
        go (inj₂ (inj₂ (inj₁ e))) =
          subst (λ z → E ≤ z + hi4) (sym e)
            (≤-trans (+-mono-≤ C.c2≤hi4 (≤-refl {P3}))
                     (≤-reflexive (+-comm hi4 P3)))
        go (inj₂ (inj₂ (inj₂ e))) =
          subst (λ z → E ≤ z + hi4) (sym e)
            (≤-trans E≤D
            (≤-trans (+-mono-≤ C.c1≤hi4 (≤-refl {P4}))
                     (≤-reflexive (+-comm hi4 P4))))

    abs-key : ∣ (S + S) - (D + E) ∣ ≤ w * w'
    abs-key = abs-≤ lower upper
      where
        upper : (S + S) - (D + E) ≤ w * w'
        upper =
          ≤-trans (sub-mono {a = S + S} {b = D + D} {c = D + E}
                            (+-mono-≤ S≤D S≤D))
                  (≤-trans (≤-reflexive (double-sub D E))
                           (≤-reflexive key))

        double-sub-comm : ∀ a c → (a + a) - (c + a) ≡ a - c
        double-sub-comm a c =
          trans (cong (λ z → (a + a) - z) (+-comm c a)) (double-sub a c)

        lower : neg (w * w') ≤ (S + S) - (D + E)
        lower =
          ≤-trans (≤-reflexive (trans (sym (cong neg key)) (negsub D E)))
                  (≤-trans (≤-reflexive (sym (double-sub-comm E D)))
                           (sub-mono {a = E + E} {b = S + S} {c = D + E}
                                     (+-mono-≤ E≤S E≤S)))

    0≤hh : 0ℚ ≤ half * half
    0≤hh = mul-nonNeg 0≤half 0≤half

    step1 : S * half - (D + E) * (half * half)
          ≡ ((S + S) - (D + E)) * (half * half)
    step1 = final-alg S D E

    step2 : ∣ ((S + S) - (D + E)) * (half * half) ∣
          ≤ (w * w') * (half * half)
    step2 =
      ≤-trans (≤-reflexive
                (trans (∣p*q∣≡∣p∣*∣q∣ ((S + S) - (D + E)) (half * half))
                       (cong (λ z → ∣ (S + S) - (D + E) ∣ * z)
                             (0≤p⇒∣p∣≡p {half * half} 0≤hh))))
              (*-monoʳ-≤-nonNeg (half * half) {{nonNegative 0≤hh}} abs-key)

    step3 : (w * w') * (half * half) ≤ (w * w') * half
    step3 = *-monoˡ-≤-nonNeg (w * w')
              {{nonNegative (mul-nonNeg 0≤w 0≤w')}} half*half≤half

------------------------------------------------------------------------
-- Private helpers (II)
--
-- 私有助手（II）

private
  recipPow2-0 : recipPow2 0 ≡ 1ℚ
  recipPow2-0 = refl

  centre-mag : (x : RealI) → Σ ℚ (λ M → 0ℚ ≤ M × (∀ n → ∣ centre x n ∣ ≤ M))
  centre-mag x =
    let M , 0≤M , inside = bounded x
    in M , 0≤M , λ n → inside n (centre x n) (centre-l x n) (centre-u x n)

  tri-add : ∀ p q P Q → ∣ (p + q) - (P + Q) ∣ ≤ ∣ p - P ∣ + ∣ q - Q ∣
  tri-add p q P Q =
    subst (λ z → ∣ z ∣ ≤ ∣ p - P ∣ + ∣ q - Q ∣) (sym (sub-add p q P Q))
          (∣p+q∣≤∣p∣+∣q∣ (p - P) (q - Q))

  add3-eq : ∀ A B C r → A * r + (B * r + C * r) ≡ (A + (B + C)) * r
  add3-eq A B C r =
    trans (cong (A * r +_) (sym (*-distribʳ-+ r B C)))
          (sym (*-distribʳ-+ r A (B + C)))

  mul-shift : ∀ {a b M : ℚ} → 0ℚ ≤ M → a ≤ b → M * a ≤ M * b
  mul-shift {a} {b} {M} 0≤M = *-monoˡ-≤-nonNeg M {{nonNegative 0≤M}}

  sub-distribˡ : ∀ a b c → a * (b - c) ≡ a * b - a * c
  sub-distribˡ a b c =
    trans (*-distribˡ-+ a b (neg c))
          (cong (a * b +_) (sym (neg-distribʳ-* a c)))

  telesc2 : ∀ p p' q q' → p * q - p' * q' ≡ q * (p - p') + p' * (q - q')
  telesc2 p p' q q' =
    sym (trans (cong₂ _+_ (sub-distribˡ q p p') (sub-distribˡ p' q q'))
               (trans (cong (_+ (p' * q - p' * q'))
                            (cong₂ _-_ (*-comm q p) (*-comm q p')))
                      (telescope (p * q) (p' * q) (p' * q'))))

------------------------------------------------------------------------
-- Commutativity
--
-- 乘法交换

*ℝ-comm : (x y : RealI) → x *ℝ y ≈ℝ y *ℝ x
*ℝ-comm x y =
  ≈ℝ-of-rec (x *ℝ y) (y *ℝ x) (width x 0 * width y 0)
    (mul-nonNeg (0≤width-n x 0) (0≤width-n y 0))
    (λ n →
      ≤-trans (tri-diff (centre (x *ℝ y) n)
                        (centre x (2 ℕ* n) * centre y (2 ℕ* n))
                        (centre (y *ℝ x) n))
      (≤-trans (+-mono-≤ (centre-*ℝ≈ x y n)
                         (≤-trans (≤-reflexive (swap-rewrite n))
                                  (centre-*ℝ≈ y x n)))
      (≤-trans (≤-reflexive (sum-eq n)) (width-prod x y n))))
  where
    swap-rewrite : ∀ n →
      ∣ centre x (2 ℕ* n) * centre y (2 ℕ* n) - centre (y *ℝ x) n ∣
      ≡ ∣ centre (y *ℝ x) n - centre y (2 ℕ* n) * centre x (2 ℕ* n) ∣
    swap-rewrite n =
      trans (abs-swap (centre x (2 ℕ* n) * centre y (2 ℕ* n))
                      (centre (y *ℝ x) n))
            (cong ∣_∣ (cong (centre (y *ℝ x) n -_)
                            (*-comm (centre x (2 ℕ* n)) (centre y (2 ℕ* n)))))

    sum-eq : ∀ n →
      (width x (2 ℕ* n) * width y (2 ℕ* n)) * half
      + (width y (2 ℕ* n) * width x (2 ℕ* n)) * half
      ≡ width x (2 ℕ* n) * width y (2 ℕ* n)
    sum-eq n =
      trans (cong (λ z → (width x (2 ℕ* n) * width y (2 ℕ* n)) * half + z * half)
                  (*-comm (width y (2 ℕ* n)) (width x (2 ℕ* n))))
            (two-half (width x (2 ℕ* n) * width y (2 ℕ* n)))

------------------------------------------------------------------------
-- Zero laws
--
-- 零元律

*ℝ-zeroˡ : (x : RealI) → 0ℝ *ℝ x ≈ℝ 0ℝ
*ℝ-zeroˡ x =
  ≈ℝ-of-rec (0ℝ *ℝ x) 0ℝ (width 0ℝ 0 * width x 0)
    (mul-nonNeg (0≤width-n 0ℝ 0) (0≤width-n x 0))
    (λ n →
      ≤-trans (≤-reflexive (cong (λ z → ∣ centre (0ℝ *ℝ x) n - z ∣) (centre-0ℝ n)))
      (≤-trans (tri-diff (centre (0ℝ *ℝ x) n)
                         (centre 0ℝ (2 ℕ* n) * centre x (2 ℕ* n)) 0ℚ)
      (≤-trans (+-mono-≤ (centre-*ℝ≈ 0ℝ x n) (zero-term n))
      (≤-trans (≤-reflexive (+-identityʳ
                              ((width 0ℝ (2 ℕ* n) * width x (2 ℕ* n)) * half)))
               (half-drop (mul-nonNeg (0≤width-n 0ℝ (2 ℕ* n))
                                      (0≤width-n x (2 ℕ* n)))
                          (width-prod 0ℝ x n))))))
  where
    zero-term : ∀ n →
      ∣ centre 0ℝ (2 ℕ* n) * centre x (2 ℕ* n) - 0ℚ ∣ ≤ 0ℚ
    zero-term n =
      ≤-reflexive
        (trans (cong (λ z → ∣ z * centre x (2 ℕ* n) - 0ℚ ∣)
                     (centre-0ℝ (2 ℕ* n)))
        (trans (cong (λ z → ∣ z - 0ℚ ∣) (*-zeroˡ (centre x (2 ℕ* n))))
        (trans (cong ∣_∣ (+-inverseʳ 0ℚ))
               (0≤p⇒∣p∣≡p {0ℚ} (≤-refl {0ℚ})))))

*ℝ-zeroʳ : (x : RealI) → x *ℝ 0ℝ ≈ℝ 0ℝ
*ℝ-zeroʳ x = ≈ℝ-trans (*ℝ-comm x 0ℝ) (*ℝ-zeroˡ x)

------------------------------------------------------------------------
-- Identity laws
--
-- 单位元律

*ℝ-identityˡ : (x : RealI) → 1ℝ *ℝ x ≈ℝ x
*ℝ-identityˡ x =
  ≈ℝ-of-rec (1ℝ *ℝ x) x (width 1ℝ 0 * width x 0 + width x 0)
    (≤-trans (mul-nonNeg (0≤width-n 1ℝ 0) (0≤width-n x 0))
             (le-addʳ (≤-refl {width 1ℝ 0 * width x 0}) (0≤width-n x 0)))
    (λ n →
      ≤-trans (tri-diff (centre (1ℝ *ℝ x) n)
                        (centre 1ℝ (2 ℕ* n) * centre x (2 ℕ* n))
                        (centre x n))
      (≤-trans (+-mono-≤ (centre-*ℝ≈ 1ℝ x n) (one-term n))
      (≤-trans (+-mono-≤ (half-drop (mul-nonNeg (0≤width-n 1ℝ (2 ℕ* n))
                                                (0≤width-n x (2 ℕ* n)))
                                  (width-prod 1ℝ x n))
                         (width-n x n))
               (≤-reflexive (sym (*-distribʳ-+ (recipPow2 n)
                                      (width 1ℝ 0 * width x 0) (width x 0)))))))
  where
    one-term : ∀ n →
      ∣ centre 1ℝ (2 ℕ* n) * centre x (2 ℕ* n) - centre x n ∣ ≤ width x n
    one-term n =
      ≤-trans (≤-reflexive (cong (λ z → ∣ z * centre x (2 ℕ* n) - centre x n ∣)
                                 (centre-1ℝ (2 ℕ* n))))
              (≤-trans (≤-reflexive (cong (λ z → ∣ z - centre x n ∣)
                                          (*-identityˡ (centre x (2 ℕ* n)))))
                       (centre-diff x n (2 ℕ* n) n (n≤2n n) (ℕP.≤-refl {n})))

*ℝ-identityʳ : (x : RealI) → x *ℝ 1ℝ ≈ℝ x
*ℝ-identityʳ x = ≈ℝ-trans (*ℝ-comm x 1ℝ) (*ℝ-identityˡ x)

------------------------------------------------------------------------
-- Distributive laws
--
-- 分配律

*ℝ-distribˡ-+ : (x y z : RealI) →
  x *ℝ (y +ℝ z) ≈ℝ (x *ℝ y) +ℝ (x *ℝ z)
*ℝ-distribˡ-+ x y z =
  ≈ℝ-of-rec (x *ℝ (y +ℝ z)) ((x *ℝ y) +ℝ (x *ℝ z))
    (width x 0 * (width y 0 + width z 0)
      + (width x 0 * width y 0 + width x 0 * width z 0))
    (le-addˡ {x = 0ℚ} {y = width x 0 * (width y 0 + width z 0)}
             {z = width x 0 * width y 0 + width x 0 * width z 0}
             (add2-nonNeg (mul-nonNeg (0≤width-n x 0) (0≤width-n y 0))
                          (mul-nonNeg (0≤width-n x 0) (0≤width-n z 0)))
             (mul-nonNeg (0≤width-n x 0)
                         (add2-nonNeg (0≤width-n y 0) (0≤width-n z 0))))
    (λ n →
      ≤-trans (tri-diff (centre (x *ℝ (y +ℝ z)) n)
                        (centre x (2 ℕ* n) * centre (y +ℝ z) (2 ℕ* n))
                        (centre ((x *ℝ y) +ℝ (x *ℝ z)) n))
      (≤-trans (+-mono-≤ (≤-trans (centre-*ℝ≈ x (y +ℝ z) n) (rec1 n))
                         (≤-trans (≤-trans (≤-reflexive (mid-rewrite n))
                                           (mid-split n))
                                  (+-mono-≤ (rec2 n) (rec3 n))))
               (≤-reflexive (add3-eq (width x 0 * (width y 0 + width z 0))
                                     (width x 0 * width y 0)
                                     (width x 0 * width z 0)
                                     (recipPow2 n)))))
  where
    mid-rewrite : ∀ n →
      ∣ centre x (2 ℕ* n) * centre (y +ℝ z) (2 ℕ* n)
        - centre ((x *ℝ y) +ℝ (x *ℝ z)) n ∣
      ≡ ∣ (centre x (2 ℕ* n) * centre y (2 ℕ* n)
           + centre x (2 ℕ* n) * centre z (2 ℕ* n))
          - (centre (x *ℝ y) n + centre (x *ℝ z) n) ∣
    mid-rewrite n =
      cong ∣_∣
        (cong₂ _-_
          (trans (cong (centre x (2 ℕ* n) *_) (centre-add y z (2 ℕ* n)))
                 (*-distribˡ-+ (centre x (2 ℕ* n))
                               (centre y (2 ℕ* n)) (centre z (2 ℕ* n))))
          (centre-add (x *ℝ y) (x *ℝ z) n))

    mid-split : ∀ n →
      ∣ (centre x (2 ℕ* n) * centre y (2 ℕ* n)
         + centre x (2 ℕ* n) * centre z (2 ℕ* n))
        - (centre (x *ℝ y) n + centre (x *ℝ z) n) ∣
      ≤ (width x (2 ℕ* n) * width y (2 ℕ* n)) * half
        + (width x (2 ℕ* n) * width z (2 ℕ* n)) * half
    mid-split n =
      ≤-trans (tri-add (centre x (2 ℕ* n) * centre y (2 ℕ* n))
                       (centre x (2 ℕ* n) * centre z (2 ℕ* n))
                       (centre (x *ℝ y) n) (centre (x *ℝ z) n))
              (+-mono-≤ pair-xy pair-xz)
      where
        pair-xy : ∣ centre x (2 ℕ* n) * centre y (2 ℕ* n) - centre (x *ℝ y) n ∣
                    ≤ (width x (2 ℕ* n) * width y (2 ℕ* n)) * half
        pair-xy = ≤-trans (≤-reflexive
                    (abs-swap (centre x (2 ℕ* n) * centre y (2 ℕ* n))
                              (centre (x *ℝ y) n)))
                  (centre-*ℝ≈ x y n)

        pair-xz : ∣ centre x (2 ℕ* n) * centre z (2 ℕ* n) - centre (x *ℝ z) n ∣
                    ≤ (width x (2 ℕ* n) * width z (2 ℕ* n)) * half
        pair-xz = ≤-trans (≤-reflexive
                    (abs-swap (centre x (2 ℕ* n) * centre z (2 ℕ* n))
                              (centre (x *ℝ z) n)))
                  (centre-*ℝ≈ x z n)

    rec1 : ∀ n → (width x (2 ℕ* n) * width (y +ℝ z) (2 ℕ* n)) * half
            ≤ (width x 0 * (width y 0 + width z 0)) * recipPow2 n
    rec1 = λ n → half-drop (mul-nonNeg (0≤width-n x (2 ℕ* n))
                                       (0≤width-n (y +ℝ z) (2 ℕ* n)))
                           (width-x-sum x y z n)

    rec2 : ∀ n → (width x (2 ℕ* n) * width y (2 ℕ* n)) * half
            ≤ (width x 0 * width y 0) * recipPow2 n
    rec2 = λ n → half-drop (mul-nonNeg (0≤width-n x (2 ℕ* n)) (0≤width-n y (2 ℕ* n)))
                           (width-prod x y n)

    rec3 : ∀ n → (width x (2 ℕ* n) * width z (2 ℕ* n)) * half
            ≤ (width x 0 * width z 0) * recipPow2 n
    rec3 = λ n → half-drop (mul-nonNeg (0≤width-n x (2 ℕ* n)) (0≤width-n z (2 ℕ* n)))
                           (width-prod x z n)

*ℝ-distribʳ-+ : (x y z : RealI) →
  (x +ℝ y) *ℝ z ≈ℝ (x *ℝ z) +ℝ (y *ℝ z)
*ℝ-distribʳ-+ x y z =
  ≈ℝ-of-rec ((x +ℝ y) *ℝ z) ((x *ℝ z) +ℝ (y *ℝ z))
    (width z 0 * (width x 0 + width y 0)
      + (width z 0 * width x 0 + width z 0 * width y 0))
    (le-addˡ {x = 0ℚ} {y = width z 0 * (width x 0 + width y 0)}
             {z = width z 0 * width x 0 + width z 0 * width y 0}
             (add2-nonNeg (mul-nonNeg (0≤width-n z 0) (0≤width-n x 0))
                          (mul-nonNeg (0≤width-n z 0) (0≤width-n y 0)))
             (mul-nonNeg (0≤width-n z 0)
                         (add2-nonNeg (0≤width-n x 0) (0≤width-n y 0))))
    (λ n →
      ≤-trans (tri-diff (centre ((x +ℝ y) *ℝ z) n)
                        (centre (x +ℝ y) (2 ℕ* n) * centre z (2 ℕ* n))
                        (centre ((x *ℝ z) +ℝ (y *ℝ z)) n))
      (≤-trans (+-mono-≤ (≤-trans (centre-*ℝ≈ (x +ℝ y) z n) (rec1 n))
                         (≤-trans (≤-trans (≤-reflexive (mid-rewrite n))
                                           (mid-split n))
                                  (+-mono-≤ (rec2 n) (rec3 n))))
               (≤-reflexive (add3-eq (width z 0 * (width x 0 + width y 0))
                                     (width z 0 * width x 0)
                                     (width z 0 * width y 0)
                                     (recipPow2 n)))))
  where
    mid-rewrite : ∀ n →
      ∣ centre (x +ℝ y) (2 ℕ* n) * centre z (2 ℕ* n)
        - centre ((x *ℝ z) +ℝ (y *ℝ z)) n ∣
      ≡ ∣ (centre x (2 ℕ* n) * centre z (2 ℕ* n)
           + centre y (2 ℕ* n) * centre z (2 ℕ* n))
          - (centre (x *ℝ z) n + centre (y *ℝ z) n) ∣
    mid-rewrite n =
      cong ∣_∣
        (cong₂ _-_
          (trans (cong (_* centre z (2 ℕ* n)) (centre-add x y (2 ℕ* n)))
                 (*-distribʳ-+ (centre z (2 ℕ* n))
                               (centre x (2 ℕ* n)) (centre y (2 ℕ* n))))
          (centre-add (x *ℝ z) (y *ℝ z) n))

    mid-split : ∀ n →
      ∣ (centre x (2 ℕ* n) * centre z (2 ℕ* n)
         + centre y (2 ℕ* n) * centre z (2 ℕ* n))
        - (centre (x *ℝ z) n + centre (y *ℝ z) n) ∣
      ≤ (width x (2 ℕ* n) * width z (2 ℕ* n)) * half
        + (width y (2 ℕ* n) * width z (2 ℕ* n)) * half
    mid-split n =
      ≤-trans (tri-add (centre x (2 ℕ* n) * centre z (2 ℕ* n))
                       (centre y (2 ℕ* n) * centre z (2 ℕ* n))
                       (centre (x *ℝ z) n) (centre (y *ℝ z) n))
              (+-mono-≤ pair-xz pair-yz)
      where
        pair-xz : ∣ centre x (2 ℕ* n) * centre z (2 ℕ* n) - centre (x *ℝ z) n ∣
                    ≤ (width x (2 ℕ* n) * width z (2 ℕ* n)) * half
        pair-xz = ≤-trans (≤-reflexive
                    (abs-swap (centre x (2 ℕ* n) * centre z (2 ℕ* n))
                              (centre (x *ℝ z) n)))
                  (centre-*ℝ≈ x z n)

        pair-yz : ∣ centre y (2 ℕ* n) * centre z (2 ℕ* n) - centre (y *ℝ z) n ∣
                    ≤ (width y (2 ℕ* n) * width z (2 ℕ* n)) * half
        pair-yz = ≤-trans (≤-reflexive
                    (abs-swap (centre y (2 ℕ* n) * centre z (2 ℕ* n))
                              (centre (y *ℝ z) n)))
                  (centre-*ℝ≈ y z n)

    rec1 : ∀ n → (width (x +ℝ y) (2 ℕ* n) * width z (2 ℕ* n)) * half
            ≤ (width z 0 * (width x 0 + width y 0)) * recipPow2 n
    rec1 = λ n →
      half-drop (mul-nonNeg (0≤width-n (x +ℝ y) (2 ℕ* n))
                            (0≤width-n z (2 ℕ* n)))
        (≤-trans (prod-rec {a = width (x +ℝ y) (2 ℕ* n)}
                           {a' = width x 0 + width y 0}
                           {b = width z (2 ℕ* n)}
                           {b' = width z 0}
                           {r = recipPow2 n}
                           (0≤recipPow2 n) (recipPow2≤1 n)
                           (width-sum-rec x y n) (width-rec z n)
                           (0≤width-n (x +ℝ y) (2 ℕ* n)) (0≤width-n z (2 ℕ* n))
                           (add2-nonNeg (0≤width-n x 0) (0≤width-n y 0))
                           (0≤width-n z 0))
                 (≤-reflexive (cong (_* recipPow2 n)
                                    (*-comm (width x 0 + width y 0) (width z 0)))))

    rec2 : ∀ n → (width x (2 ℕ* n) * width z (2 ℕ* n)) * half
            ≤ (width z 0 * width x 0) * recipPow2 n
    rec2 = λ n →
      half-drop (mul-nonNeg (0≤width-n x (2 ℕ* n)) (0≤width-n z (2 ℕ* n)))
        (≤-trans (width-prod x z n)
                 (≤-reflexive (cong (_* recipPow2 n)
                                    (*-comm (width x 0) (width z 0)))))

    rec3 : ∀ n → (width y (2 ℕ* n) * width z (2 ℕ* n)) * half
            ≤ (width z 0 * width y 0) * recipPow2 n
    rec3 = λ n →
      half-drop (mul-nonNeg (0≤width-n y (2 ℕ* n)) (0≤width-n z (2 ℕ* n)))
        (≤-trans (width-prod y z n)
                 (≤-reflexive (cong (_* recipPow2 n)
                                    (*-comm (width y 0) (width z 0)))))

------------------------------------------------------------------------
-- Associativity
--
-- 结合律

*ℝ-assoc : (x y z : RealI) → (x *ℝ y) *ℝ z ≈ℝ x *ℝ (y *ℝ z)
*ℝ-assoc x y z =
  ≈ℝ-of-rec ((x *ℝ y) *ℝ z) (x *ℝ (y *ℝ z)) K K≥0 body
  where
    Mx My Mz : ℚ
    Mx = proj₁ (centre-mag x)
    My = proj₁ (centre-mag y)
    Mz = proj₁ (centre-mag z)

    0≤Mx : 0ℚ ≤ Mx
    0≤Mx = proj₁ (proj₂ (centre-mag x))
    0≤My : 0ℚ ≤ My
    0≤My = proj₁ (proj₂ (centre-mag y))
    0≤Mz : 0ℚ ≤ Mz
    0≤Mz = proj₁ (proj₂ (centre-mag z))

    ≤Mx : ∀ m → ∣ centre x m ∣ ≤ Mx
    ≤Mx m = proj₂ (proj₂ (centre-mag x)) m
    ≤My : ∀ m → ∣ centre y m ∣ ≤ My
    ≤My m = proj₂ (proj₂ (centre-mag y)) m
    ≤Mz : ∀ m → ∣ centre z m ∣ ≤ Mz
    ≤Mz m = proj₂ (proj₂ (centre-mag z)) m

    P1 P2 P3 P4 P5 K : ℚ
    P1 = width (x *ℝ y) 0 * width z 0
    P2 = Mz * (width x 0 * width y 0)
    P3 = My * (Mz * width x 0 + Mx * width z 0)
    P4 = Mx * (width y 0 * width z 0)
    P5 = width x 0 * width (y *ℝ z) 0
    K  = P1 + ((P2 + (P3 + P4)) + P5)

    P1≥0 : 0ℚ ≤ P1
    P1≥0 = mul-nonNeg (0≤width-n (x *ℝ y) 0) (0≤width-n z 0)
    P2≥0 : 0ℚ ≤ P2
    P2≥0 = mul-nonNeg 0≤Mz (mul-nonNeg (0≤width-n x 0) (0≤width-n y 0))
    P3≥0 : 0ℚ ≤ P3
    P3≥0 = mul-nonNeg 0≤My
             (add2-nonNeg (mul-nonNeg 0≤Mz (0≤width-n x 0))
                          (mul-nonNeg 0≤Mx (0≤width-n z 0)))
    P4≥0 : 0ℚ ≤ P4
    P4≥0 = mul-nonNeg 0≤Mx (mul-nonNeg (0≤width-n y 0) (0≤width-n z 0))
    P5≥0 : 0ℚ ≤ P5
    P5≥0 = mul-nonNeg (0≤width-n x 0) (0≤width-n (y *ℝ z) 0)
    P234≥0 : 0ℚ ≤ P2 + (P3 + P4)
    P234≥0 = le-addˡ {x = 0ℚ} {y = P2} {z = P3 + P4}
               (add2-nonNeg P3≥0 P4≥0) P2≥0

    K≥0 : 0ℚ ≤ K
    K≥0 = le-addˡ {x = 0ℚ} {y = P1} {z = (P2 + (P3 + P4)) + P5}
            (add2-nonNeg P234≥0 P5≥0) P1≥0

    cx2 cx4 cy4 cz2 cz4 cyz2 cxy2 : ℕ → ℚ
    cx2 n = centre x (2 ℕ* n)
    cx4 n = centre x (4 ℕ* n)
    cy4 n = centre y (4 ℕ* n)
    cz2 n = centre z (2 ℕ* n)
    cz4 n = centre z (4 ℕ* n)
    cyz2 n = centre (y *ℝ z) (2 ℕ* n)
    cxy2 n = centre (x *ℝ y) (2 ℕ* n)

    Lo Hi : ℕ → ℚ
    Lo n = centre ((x *ℝ y) *ℝ z) n
    Hi n = centre (x *ℝ (y *ℝ z)) n

    A B : ℕ → ℚ
    A n = cxy2 n * cz2 n
    B n = cx2 n * cyz2 n

    X Y : ℕ → ℚ
    X n = cx4 n * cy4 n * cz2 n
    Y n = cx2 n * (cy4 n * cz4 n)

    t1 ta tb tc t5 : ℕ → ℚ
    t1 n = (width (x *ℝ y) (2 ℕ* n) * width z (2 ℕ* n)) * half
    ta n = Mz * ((width x (4 ℕ* n) * width y (4 ℕ* n)) * half)
    tb n = My * (Mz * width x (2 ℕ* n) + Mx * width z (2 ℕ* n))
    tc n = Mx * ((width y (4 ℕ* n) * width z (4 ℕ* n)) * half)
    t5 n = (width x (2 ℕ* n) * width (y *ℝ z) (2 ℕ* n)) * half

    w2 : ∀ (r : RealI) n → width r (2 ℕ* n) ≤ width r 0 * recipPow2 n
    w2 r n = width-rec r n
    w4 : ∀ (r : RealI) n → width r (4 ℕ* n) ≤ width r 0 * recipPow2 n
    w4 r n = width-rec4 r n

    h1 : ∀ n → ∣ Lo n - A n ∣ ≤ t1 n
    h1 n = centre-*ℝ≈ (x *ℝ y) z n

    h5 : ∀ n → ∣ B n - Hi n ∣ ≤ t5 n
    h5 n =
      ≤-trans (≤-reflexive (abs-swap (cx2 n * cyz2 n)
                                     (centre (x *ℝ (y *ℝ z)) n)))
              (centre-*ℝ≈ x (y *ℝ z) n)

    mA : ∀ n → ∣ cxy2 n * cz2 n - cx4 n * cy4 n * cz2 n ∣ ≤ ta n
    mA n =
      ≤-trans (≤-reflexive (cong ∣_∣ eqA))
      (≤-trans (≤-reflexive (trans (∣p*q∣≡∣p∣*∣q∣ (cxy2 n - cx4 n * cy4 n) (cz2 n))
                                   (*-comm (∣ cxy2 n - cx4 n * cy4 n ∣) (∣ cz2 n ∣))))
      (≤-trans (*-mono-≤-nonNeg (0≤∣p∣ (cz2 n)) (≤Mz (2 ℕ* n))
                                (0≤∣p∣ (cxy2 n - cx4 n * cy4 n)) inner)
               (≤-refl {ta n})))
      where
        eqA : cxy2 n * cz2 n - cx4 n * cy4 n * cz2 n
                ≡ (cxy2 n - cx4 n * cy4 n) * cz2 n
        eqA = sym (*ʳ-sub (cxy2 n) (cx4 n * cy4 n) (cz2 n))
        inner : ∣ cxy2 n - cx4 n * cy4 n ∣
                  ≤ (width x (4 ℕ* n) * width y (4 ℕ* n)) * half
        inner = subst (λ m → ∣ cxy2 n - centre x m * centre y m ∣
                               ≤ (width x m * width y m) * half)
                      (2*2n≡4n n) (centre-*ℝ≈ x y (2 ℕ* n))

    mB : ∀ n → ∣ cx4 n * cy4 n * cz2 n - cx2 n * (cy4 n * cz4 n) ∣ ≤ tb n
    mB n =
      ≤-trans (≤-reflexive (cong ∣_∣ eqX))
      (≤-trans (≤-reflexive (∣p*q∣≡∣p∣*∣q∣ (cy4 n) (cx4 n * cz2 n - cx2 n * cz4 n)))
      (≤-trans (*-mono-≤-nonNeg (0≤∣p∣ (cy4 n)) (≤My (4 ℕ* n))
                                (0≤∣p∣ (cx4 n * cz2 n - cx2 n * cz4 n)) inner)
               (≤-refl {tb n})))
      where
        rwY : cx2 n * (cy4 n * cz4 n) ≡ cy4 n * (cx2 n * cz4 n)
        rwY = trans (cong (cx2 n *_) (*-comm (cy4 n) (cz4 n)))
              (trans (sym (*-assoc (cx2 n) (cz4 n) (cy4 n)))
                     (*-comm (cx2 n * cz4 n) (cy4 n)))
        eqX : cx4 n * cy4 n * cz2 n - cx2 n * (cy4 n * cz4 n)
                ≡ cy4 n * (cx4 n * cz2 n - cx2 n * cz4 n)
        eqX = trans (cong (λ w → w * cz2 n - cx2 n * (cy4 n * cz4 n))
                          (*-comm (cx4 n) (cy4 n)))
              (trans (cong (λ w → w - cx2 n * (cy4 n * cz4 n))
                           (*-assoc (cy4 n) (cx4 n) (cz2 n)))
              (trans (cong (cy4 n * (cx4 n * cz2 n) -_) rwY)
                     (sym (sub-distribˡ (cy4 n) (cx4 n * cz2 n) (cx2 n * cz4 n)))))
        inner : ∣ cx4 n * cz2 n - cx2 n * cz4 n ∣
                  ≤ Mz * width x (2 ℕ* n) + Mx * width z (2 ℕ* n)
        inner = inner-step
          where
            l1 : ∣ cx4 n * cz2 n - cx2 n * cz4 n ∣
                   ≤ ∣ cz2 n * (cx4 n - cx2 n) ∣ + ∣ cx2 n * (cz2 n - cz4 n) ∣
            l1 = ≤-trans (≤-reflexive (cong ∣_∣
                            (telesc2 (cx4 n) (cx2 n) (cz2 n) (cz4 n))))
                         (∣p+q∣≤∣p∣+∣q∣ (cz2 n * (cx4 n - cx2 n))
                                          (cx2 n * (cz2 n - cz4 n)))
            l2 : ∣ cz2 n * (cx4 n - cx2 n) ∣ ≤ Mz * width x (2 ℕ* n)
            l2 = ≤-trans (≤-reflexive (∣p*q∣≡∣p∣*∣q∣ (cz2 n) (cx4 n - cx2 n)))
                 (≤-trans (*-mono-≤-nonNeg (0≤∣p∣ (cz2 n)) (≤Mz (2 ℕ* n))
                            (0≤∣p∣ (cx4 n - cx2 n)) d1)
                          (≤-refl {Mz * width x (2 ℕ* n)}))
              where
                d1 : ∣ cx4 n - cx2 n ∣ ≤ width x (2 ℕ* n)
                d1 = ≤-trans (≤-reflexive (abs-swap (cx4 n) (cx2 n)))
                             (centre-diff x (2 ℕ* n) (2 ℕ* n) (4 ℕ* n)
                                          (ℕP.≤-refl {2 ℕ* n}) (2n≤4n n))
            l3 : ∣ cx2 n * (cz2 n - cz4 n) ∣ ≤ Mx * width z (2 ℕ* n)
            l3 = ≤-trans (≤-reflexive (∣p*q∣≡∣p∣*∣q∣ (cx2 n) (cz2 n - cz4 n)))
                 (≤-trans (*-mono-≤-nonNeg (0≤∣p∣ (cx2 n)) (≤Mx (2 ℕ* n))
                            (0≤∣p∣ (cz2 n - cz4 n)) d3)
                          (≤-refl {Mx * width z (2 ℕ* n)}))
              where
                d3 : ∣ cz2 n - cz4 n ∣ ≤ width z (2 ℕ* n)
                d3 = centre-diff z (2 ℕ* n) (2 ℕ* n) (4 ℕ* n)
                             (ℕP.≤-refl {2 ℕ* n}) (2n≤4n n)
            inner-step : ∣ cx4 n * cz2 n - cx2 n * cz4 n ∣
                           ≤ Mz * width x (2 ℕ* n) + Mx * width z (2 ℕ* n)
            inner-step = ≤-trans l1 (+-mono-≤ l2 l3)

    mC : ∀ n → ∣ cx2 n * (cy4 n * cz4 n) - cx2 n * cyz2 n ∣ ≤ tc n
    mC n =
      ≤-trans (≤-reflexive (cong ∣_∣ (sym (sub-distribˡ (cx2 n)
                                     (cy4 n * cz4 n) (cyz2 n)))))
      (≤-trans (≤-reflexive (∣p*q∣≡∣p∣*∣q∣ (cx2 n) (cy4 n * cz4 n - cyz2 n)))
      (≤-trans (*-mono-≤-nonNeg (0≤∣p∣ (cx2 n)) (≤Mx (2 ℕ* n))
                                (0≤∣p∣ (cy4 n * cz4 n - cyz2 n)) inner)
               (≤-refl {tc n})))
      where
        inner : ∣ cy4 n * cz4 n - cyz2 n ∣
                  ≤ (width y (4 ℕ* n) * width z (4 ℕ* n)) * half
        inner = subst (λ m → ∣ centre y m * centre z m - cyz2 n ∣
                               ≤ (width y m * width z m) * half)
                      (2*2n≡4n n)
                      (≤-trans (≤-reflexive (abs-swap (centre y (2 ℕ* (2 ℕ* n)) * centre z (2 ℕ* (2 ℕ* n))) (cyz2 n)))
                               (centre-*ℝ≈ y z (2 ℕ* n)))

    hM : ∀ n → ∣ cxy2 n * cz2 n - cx2 n * cyz2 n ∣ ≤ ta n + (tb n + tc n)
    hM n =
      ≤-trans (tri-diff (cxy2 n * cz2 n) (cx4 n * cy4 n * cz2 n) (cx2 n * cyz2 n))
      (≤-trans (+-mono-≤ (mA n)
                         (≤-trans (tri-diff (cx4 n * cy4 n * cz2 n)
                                            (cx2 n * (cy4 n * cz4 n)) (cx2 n * cyz2 n))
                                  (+-mono-≤ (mB n) (mC n))))
               (≤-refl {ta n + (tb n + tc n)}))

    chain : ∀ n → ∣ Lo n - Hi n ∣ ≤ t1 n + ((ta n + (tb n + tc n)) + t5 n)
    chain n =
      ≤-trans (tri-diff (Lo n) (cxy2 n * cz2 n) (Hi n))
      (≤-trans (+-mono-≤ (h1 n) (≤-refl {∣ cxy2 n * cz2 n - Hi n ∣}))
      (≤-trans (+-mono-≤ (≤-refl {t1 n}) (tri-diff (cxy2 n * cz2 n) (cx2 n * cyz2 n) (Hi n)))
      (≤-trans (+-mono-≤ (≤-refl {t1 n}) (+-mono-≤ (hM n) (≤-refl {∣ cx2 n * cyz2 n - Hi n ∣})))
               (+-mono-≤ (≤-refl {t1 n}) (+-mono-≤ (≤-refl {ta n + (tb n + tc n)})
                                                   (h5 n))))))

    c1 : ∀ n → t1 n ≤ P1 * recipPow2 n
    c1 n =
      half-drop {a = width (x *ℝ y) (2 ℕ* n) * width z (2 ℕ* n)}
                {b = (width (x *ℝ y) 0 * width z 0) * recipPow2 n}
                (mul-nonNeg (0≤width-n (x *ℝ y) (2 ℕ* n)) (0≤width-n z (2 ℕ* n)))
        (prod-rec {a = width (x *ℝ y) (2 ℕ* n)}
                  {a' = width (x *ℝ y) 0}
                  {b = width z (2 ℕ* n)}
                  {b' = width z 0}
                  {r = recipPow2 n}
                  (0≤recipPow2 n) (recipPow2≤1 n)
                  (w2 (x *ℝ y) n) (w2 z n)
                  (0≤width-n (x *ℝ y) (2 ℕ* n)) (0≤width-n z (2 ℕ* n))
                  (0≤width-n (x *ℝ y) 0) (0≤width-n z 0))

    ca : ∀ n → ta n ≤ P2 * recipPow2 n
    ca n =
      ≤-trans (mul-shift 0≤Mz
                (half-drop {a = width x (4 ℕ* n) * width y (4 ℕ* n)}
                           {b = (width x 0 * width y 0) * recipPow2 n}
                           (mul-nonNeg (0≤width-n x (4 ℕ* n)) (0≤width-n y (4 ℕ* n)))
                  (prod-rec {a = width x (4 ℕ* n)}
                            {a' = width x 0}
                            {b = width y (4 ℕ* n)}
                            {b' = width y 0}
                            {r = recipPow2 n}
                            (0≤recipPow2 n) (recipPow2≤1 n)
                            (w4 x n) (w4 y n)
                            (0≤width-n x (4 ℕ* n)) (0≤width-n y (4 ℕ* n))
                            (0≤width-n x 0) (0≤width-n y 0))))
              (≤-reflexive (sym (*-assoc Mz (width x 0 * width y 0) (recipPow2 n))))

    cb : ∀ n → tb n ≤ P3 * recipPow2 n
    cb n =
      ≤-trans (mul-shift 0≤My
                (≤-trans (+-mono-≤
                           (≤-trans (mul-shift 0≤Mz (w2 x n))
                                    (≤-reflexive (sym (*-assoc Mz (width x 0)
                                                               (recipPow2 n)))))
                           (≤-trans (mul-shift 0≤Mx (w2 z n))
                                    (≤-reflexive (sym (*-assoc Mx (width z 0)
                                                               (recipPow2 n))))))
                         (≤-reflexive (sym (*-distribʳ-+ (recipPow2 n)
                                               (Mz * width x 0) (Mx * width z 0))))))
              (≤-reflexive (sym (*-assoc My (Mz * width x 0 + Mx * width z 0)
                                         (recipPow2 n))))

    cc : ∀ n → tc n ≤ P4 * recipPow2 n
    cc n =
      ≤-trans (mul-shift 0≤Mx
                (half-drop {a = width y (4 ℕ* n) * width z (4 ℕ* n)}
                           {b = (width y 0 * width z 0) * recipPow2 n}
                           (mul-nonNeg (0≤width-n y (4 ℕ* n)) (0≤width-n z (4 ℕ* n)))
                  (prod-rec {a = width y (4 ℕ* n)}
                            {a' = width y 0}
                            {b = width z (4 ℕ* n)}
                            {b' = width z 0}
                            {r = recipPow2 n}
                            (0≤recipPow2 n) (recipPow2≤1 n)
                            (w4 y n) (w4 z n)
                            (0≤width-n y (4 ℕ* n)) (0≤width-n z (4 ℕ* n))
                            (0≤width-n y 0) (0≤width-n z 0))))
              (≤-reflexive (sym (*-assoc Mx (width y 0 * width z 0) (recipPow2 n))))

    c5 : ∀ n → t5 n ≤ P5 * recipPow2 n
    c5 n =
      half-drop {a = width x (2 ℕ* n) * width (y *ℝ z) (2 ℕ* n)}
                {b = (width x 0 * width (y *ℝ z) 0) * recipPow2 n}
                (mul-nonNeg (0≤width-n x (2 ℕ* n)) (0≤width-n (y *ℝ z) (2 ℕ* n)))
        (prod-rec {a = width x (2 ℕ* n)}
                  {a' = width x 0}
                  {b = width (y *ℝ z) (2 ℕ* n)}
                  {b' = width (y *ℝ z) 0}
                  {r = recipPow2 n}
                  (0≤recipPow2 n) (recipPow2≤1 n)
                  (w2 x n) (w2 (y *ℝ z) n)
                  (0≤width-n x (2 ℕ* n)) (0≤width-n (y *ℝ z) (2 ℕ* n))
                  (0≤width-n x 0) (0≤width-n (y *ℝ z) 0))

    cM : ∀ n → ta n + (tb n + tc n) ≤ (P2 + (P3 + P4)) * recipPow2 n
    cM n =
      ≤-trans (+-mono-≤ (ca n) (+-mono-≤ (cb n) (cc n)))
              (≤-reflexive (add3-eq P2 P3 P4 (recipPow2 n)))

    body : ∀ n → ∣ Lo n - Hi n ∣ ≤ K * recipPow2 n
    body n =
      ≤-trans (chain n)
      (≤-trans (+-mono-≤ (c1 n) (+-mono-≤ (cM n) (c5 n)))
               (≤-reflexive (add3-eq P1 (P2 + (P3 + P4)) P5 (recipPow2 n))))
