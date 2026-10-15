------------------------------------------------------------------------
-- Order laws for RealI
--
-- Basic order-theoretic facts about _<ℝ_ and _≈ℝ_ on RealI.
--
-- RealI 的序律
--
-- RealI 上 _<ℝ_ 与 _≈ℝ_ 的基本序论事实。
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module ALMA.Base.Real.Interval.OrderLaws where

open import Data.Nat using
  (ℕ; zero; suc; _≥_; _⊔_; _^_; _∸_; s≤s; z≤n) renaming (_≤_ to _≤ℕ_; _+_ to _+ℕ_)
open import Data.Nat.Properties using
  (m≤m⊔n; m≤n⊔m; m∸n+n≡m) renaming (≤-trans to ≤ℕ-trans; +-suc to +-sucℕ
  ; +-comm to +-commℕ; +-identityʳ to +-identityʳℕ)
open import Data.Product using (Σ; _,_; _×_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Rational using
  (ℚ; 0ℚ; 1ℚ; _+_; _-_; _*_; _≤_; _<_; ∣_∣; Positive; NonZero; positive)
open import Data.Rational.Base using (1/_) renaming (-_ to neg)
open import Data.Rational.Properties using
  (≤-refl; ≤-reflexive; ≤-trans; <⇒≤; ≤-<-trans; <-≤-trans; <-trans; +-mono-≤
  ; +-mono-<; +-monoˡ-<; +-monoʳ-<; *-monoˡ-≤-nonNeg; *-monoʳ-<-pos; *-monoˡ-<-pos
  ; pos⇒nonZero; positive⁻¹; 1/pos⇒pos; pos⇒nonNeg; *-inverseʳ; *-inverseˡ
  ; *-comm; *-assoc; *-identityʳ; *-identityˡ; *-zeroˡ; *-zeroʳ; *-distribˡ-+
  ; +-inverseʳ; +-inverseˡ; +-identityʳ; +-identityˡ; +-comm; +-assoc
  ; neg-distrib-+; neg-antimono-≤; neg-antimono-<; ∣-p∣≡∣p∣; 0≤∣p∣
  ;∣p∣≡p∨∣p∣≡-p; *-cancelˡ-<-nonNeg)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; cong; sym; trans; subst)
open import Relation.Binary.PropositionalEquality.Properties using (module ≡-Reasoning)

open import ALMA.Base.Real using (embed; ε; 0<ε; embed-suc-pos)
open import ALMA.Base.Real.Interval using (RealI; neg-invol)
open import ALMA.Base.Real.IntervalEquiv using
  (node; l; u; centre; width; width-n; width-1step; centre-l; centre-u; u-mono
  ; l-mono; recipPow2; bound-w; n<2^n; 0<2^n; embed-mono-<; 0<width)
open import ALMA.Base.Real.Interval.Equiv using (_≈ℝ_)
open import ALMA.Base.Real.Interval.Order using (_<ℝ_)
open import ALMA.Base.Real.Interval.Kit using
  (half; 0<half; 0≤half; half≤1; two-half; half+half≡1; 0<recipPow2; embed-suc∸1)
open import ALMA.Base.Real.Interval.Node using
  (0≤width-n; l-hom; u-hom; l-neg; u-neg)
open import ALMA.Base.Real.Interval.Mul using (le-shift)
open import ALMA.Base.Real.Interval.Arith using (_+ℝ_; _-ℝ_; negℝ)
open import ALMA.Base.Real.Interval.Rational using (r≤|r|)

------------------------------------------------------------------------
-- An ε below any positive rational
--
-- For every b > 0 there is k with ε k < b, since ε k = 1/(k+1) and
-- k+1 > 1/b suffices.
--
-- 任意正有理数下方有 ε
--
-- 对每个 b > 0，存在 k 使 ε k < b；因为 ε k = 1/(k+1)，
-- 取 k+1 > 1/b 即可。

eps-below : (b : ℚ) → 0ℚ < b → Σ ℕ (λ k → ε k < b)
eps-below b 0<b = M , goal
  where
    instance
      b-Positive : Positive b
      b-Positive = positive 0<b

      b-NonZero : NonZero b
      b-NonZero = pos⇒nonZero b

    inv : ℚ
    inv = 1/ b

    0<inv : 0ℚ < inv
    0<inv = positive⁻¹ inv {{1/pos⇒pos b}}

    M : ℕ
    M = proj₁ (bound-w inv (<⇒≤ 0<inv))

    inv≤M : inv ≤ embed M
    inv≤M = proj₂ (bound-w inv (<⇒≤ 0<inv))

    M<sM : embed M < embed (suc M)
    M<sM = embed-mono-< {M} {suc M} (s≤s (Data.Nat.Properties.≤-refl))

    inv<sM : inv < embed (suc M)
    inv<sM = ≤-<-trans inv≤M M<sM

    sM : ℚ
    sM = embed (suc M)

    instance
      sM-Positive : Positive sM
      sM-Positive = embed-suc-pos

      sM-NonZero : NonZero sM
      sM-NonZero = pos⇒nonZero sM

    b-inv<b-sM : b * inv < b * sM
    b-inv<b-sM = *-monoʳ-<-pos b inv<sM

    1<b-sM : 1ℚ < b * sM
    1<b-sM = subst (λ z → z < b * sM) (*-inverseʳ b) b-inv<b-sM

    sM-b : sM * b ≡ b * sM
    sM-b = *-comm sM b

    ε-eq : 1/ sM ≡ ε M
    ε-eq = refl

    goal : ε M < b
    goal =
      subst (λ z → z < b) ε-eq
        (*-cancelˡ-<-nonNeg sM {{pos⇒nonNeg sM}}
          (subst (λ z → z < sM * b) (sym (*-inverseʳ sM))
                 (subst (λ z → 1ℚ < z) (sym sM-b) 1<b-sM)))

------------------------------------------------------------------------
-- A width below any positive rational
--
-- 任意正有理数下方有宽度

width-below : (r : RealI) (b : ℚ) → 0ℚ < b → Σ ℕ (λ m → width r m < b)
width-below r b 0<b = M , result
  where
    w0 : ℚ
    w0 = width r 0

    0<w0 : 0ℚ < w0
    0<w0 = 0<width r

    0≤w0 : 0ℚ ≤ w0
    0≤w0 = <⇒≤ 0<w0

    b-pos : Positive b
    b-pos = positive 0<b

    b-nz : NonZero b
    b-nz = pos⇒nonZero b {{b-pos}}

    inv-b : ℚ
    inv-b = 1/_ b {{b-nz}}

    0<inv-b : 0ℚ < inv-b
    0<inv-b = positive⁻¹ inv-b {{1/pos⇒pos b {{b-pos}}}}

    0≤inv-b : 0ℚ ≤ inv-b
    0≤inv-b = <⇒≤ 0<inv-b

    w0-pos : Positive w0
    w0-pos = positive 0<w0

    q : ℚ
    q = w0 * inv-b

    0≤q : 0ℚ ≤ q
    0≤q = subst (λ z → z ≤ w0 * inv-b) (*-zeroʳ w0)
            (*-monoˡ-≤-nonNeg w0 {{pos⇒nonNeg w0 {{w0-pos}}}} 0≤inv-b)

    M : ℕ
    M = proj₁ (bound-w q 0≤q)

    q≤M : q ≤ embed M
    q≤M = proj₂ (bound-w q 0≤q)

    M<2^m : M Data.Nat.< 2 ^ M
    M<2^m = n<2^n M

    M<2^m' : embed M < embed (2 ^ M)
    M<2^m' = embed-mono-< M<2^m

    q<2^m : q < embed (2 ^ M)
    q<2^m = ≤-<-trans q≤M M<2^m'

    em-pos : Positive (embed (2 ^ M))
    em-pos = positive (embed-mono-< (0<2^n M))

    em-nz : NonZero (embed (2 ^ M))
    em-nz = pos⇒nonZero (embed (2 ^ M)) {{em-pos}}

    em-inv : ℚ
    em-inv = recipPow2 M

    0<em-inv : 0ℚ < em-inv
    0<em-inv = 0<recipPow2 M

    recipPow2-eq : recipPow2 M ≡ em-inv
    recipPow2-eq = refl

    1b-inv-b : inv-b * b ≡ 1ℚ
    1b-inv-b = *-inverseˡ b {{b-nz}}

    step1 : (w0 * inv-b) * b < embed (2 ^ M) * b
    step1 = *-monoˡ-<-pos b {{b-pos}} q<2^m

    lhs≡ : (w0 * inv-b) * b ≡ w0
    lhs≡ = trans (*-assoc w0 inv-b b)
                (trans (cong (w0 *_) 1b-inv-b) (*-identityʳ w0))

    w0<em-b : w0 < embed (2 ^ M) * b
    w0<em-b = subst (λ z → z < embed (2 ^ M) * b) lhs≡ step1

    step2 : w0 * em-inv < (embed (2 ^ M) * b) * em-inv
    step2 = *-monoˡ-<-pos em-inv {{positive 0<em-inv}} w0<em-b

    -- recipPow2 m = 1 / embed (suc (2^m ∸ 1)) and the denominator
    -- equals embed (2^m), so embed (2^m) * em-inv ≡ 1.
    --
    -- recipPow2 m = 1 / embed (suc (2^m ∸ 1))，其分母等于
    -- embed (2^m)，故 embed (2^m) * em-inv ≡ 1。
    s : ℚ
    s = embed (suc (2 ^ M ∸ 1))

    s≡E : s ≡ embed (2 ^ M)
    s≡E = embed-suc∸1 M

    s-nz : NonZero s
    s-nz = pos⇒nonZero s {{embed-suc-pos}}

    E*em-inv≡1 : embed (2 ^ M) * em-inv ≡ 1ℚ
    E*em-inv≡1 =
      trans (cong (λ t → t * em-inv) (sym s≡E))
            (*-inverseʳ s {{s-nz}})

    rhs≡ : (embed (2 ^ M) * b) * em-inv ≡ b
    rhs≡ = trans (*-assoc (embed (2 ^ M)) b em-inv)
                (trans (cong (embed (2 ^ M) *_) (*-comm b em-inv))
                (trans (sym (*-assoc (embed (2 ^ M)) em-inv b))
                (trans (cong (_* b) E*em-inv≡1)
                       (*-identityˡ b))))

    w0-em-inv<b : w0 * em-inv < b
    w0-em-inv<b = subst (λ z → w0 * em-inv < z) rhs≡ step2

    result : width r M < b
    result = ≤-<-trans (width-n r M)
               (≤-<-trans (≤-reflexive (cong (w0 *_) recipPow2-eq))
                          w0-em-inv<b)

------------------------------------------------------------------------
-- Widths decrease with depth
--
-- 宽度随深度递减

width-step-dec : (r : RealI) (n : ℕ) → width r (suc n) ≤ width r n
width-step-dec r n =
  ≤-trans (width-1step r n)
    (≤-trans (*-monoˡ-≤-nonNeg (width r n)
                                {{pos⇒nonNeg (width r n)
                                   {{positive (0<width (node r n))}}}}
                                half≤1)
             (≤-reflexive (*-identityʳ (width r n))))

width-mono-ge : (r : RealI) (n k : ℕ) → width r (n +ℕ k) ≤ width r n
width-mono-ge r n zero =
  ≤-reflexive (cong (width r) (+-identityʳℕ n))
width-mono-ge r n (suc k) =
  ≤-trans (subst (λ j → width r j ≤ width r (n +ℕ k)) (sym (+-sucℕ n k))
                 (width-step-dec r (n +ℕ k)))
          (width-mono-ge r n k)

width-dec : (r : RealI) {n m : ℕ} → n ≤ℕ m → width r m ≤ width r n
width-dec r {n} {m} n≤m =
  subst (λ j → width r j ≤ width r n)
        (trans (+-commℕ n (m ∸ n)) (m∸n+n≡m n≤m))
        (width-mono-ge r n (m ∸ n))

------------------------------------------------------------------------
-- width-below with a lower bound
--
-- 带下界的 width-below

width-below-strict : (r : RealI) (b : ℚ) (M₀ : ℕ) → 0ℚ < b
  → Σ ℕ (λ m → M₀ ≤ℕ m × width r m < b)
width-below-strict r b M₀ 0<b =
  m , m≤m⊔n M₀ M , ≤-<-trans (width-dec r (m≤n⊔m M₀ M)) wb
  where
    w-res : Σ ℕ (λ j → width r j < b)
    w-res = width-below r b 0<b

    M : ℕ
    M = proj₁ w-res

    wb : width r M < b
    wb = proj₂ w-res

    m : ℕ
    m = M₀ ⊔ M

u≤c+w : (r : RealI) (k : ℕ) → u r k ≤ centre r k + width r k
u≤c+w r k =
  le-shift {x = u r k} {y = width r k} {z = centre r k}
    (subst (λ z → z ≤ centre r k)
           (sym (sub-cancel-2 (u r k) (l r k)))
           (centre-l r k))
  where
    sub-cancel-2 : ∀ a b → a - (a - b) ≡ b
    sub-cancel-2 a b = let open ≡-Reasoning in begin
      a - (a - b)
      ≡⟨⟩
      a + neg (a + neg b)
      ≡⟨ cong (a +_) (neg-distrib-+ a (neg b)) ⟩
      a + (neg a + neg (neg b))
      ≡⟨ sym (+-assoc a (neg a) (neg (neg b))) ⟩
      (a + neg a) + neg (neg b)
      ≡⟨ cong (λ z → z + neg (neg b)) (+-inverseʳ a) ⟩
      0ℚ + neg (neg b)
      ≡⟨ +-identityˡ (neg (neg b)) ⟩
      neg (neg b)
      ≡⟨ neg-invol b ⟩
      b ∎

1<2 : 1ℚ < embed 2
1<2 = embed-mono-< {1} {2} (s≤s (s≤s z≤n))

half<1 : half < 1ℚ
half<1 =
  subst (λ z → half < z)
        (*-inverseʳ (embed 2) {{pos⇒nonZero (embed 2) {{embed-suc-pos}}}})
        (*-monoˡ-<-pos half {{positive 0<half}} 1<2)

half+half²<1 : half + half * half < 1ℚ
half+half²<1 =
  let
    step1 : half + half * half ≡ half * (1ℚ + half)
    step1 =
      trans (cong (λ z → z + half * half) (sym (*-identityʳ half)))
            (sym (*-distribˡ-+ half 1ℚ half))
    step2 : half * (1ℚ + half) < half * (1ℚ + 1ℚ)
    step2 = *-monoʳ-<-pos half {{positive 0<half}}
                    (+-monoˡ-< 1ℚ half<1)
    step3 : half * (1ℚ + 1ℚ) ≡ 1ℚ
    step3 =
      trans (sym (*-distribˡ-+ half 1ℚ 1ℚ)) half+half≡1
  in subst (λ z → half + half * half < z) step3
       (subst (λ z → z < half * (1ℚ + 1ℚ)) (sym step1) step2)

3d/4<d : (d : ℚ) → 0ℚ < d → d * half + (d * half) * half < d
3d/4<d d 0<d =
  subst (λ z → z < d)
    (trans (*-distribˡ-+ d half (half * half))
           (cong (d * half +_) (sym (*-assoc d half half))))
    (subst (λ z → d * (half + half * half) < z) (*-identityʳ d)
           (*-monoʳ-<-pos d {{positive 0<d}} half+half²<1))

------------------------------------------------------------------------
-- Compatibility of order with equivalence
--
-- x ≈ y ∧ x < z ⟹ y < z.
--
-- 序与等价的相容性
--
-- x ≈ y ∧ x < z ⟹ y < z。

≈-<-resp : {x y z : RealI} → x ≈ℝ y → x <ℝ z → y <ℝ z
≈-<-resp {x} {y} {z} x≈y (n , uxn<lzn) = m , uym<lzm
  where
    d : ℚ
    d = l z n - u x n

    0<d : 0ℚ < d
    0<d = subst (λ w → w < l z n - u x n) (+-inverseʳ (u x n))
                (+-monoˡ-< (neg (u x n)) uxn<lzn)

    b : ℚ
    b = d * half

    0<b : 0ℚ < b
    0<b = subst (λ w → w < b) (*-zeroˡ half)
                (*-monoˡ-<-pos half {{positive 0<half}} 0<d)

    e-res : Σ ℕ (λ j → ε j < b)
    e-res = eps-below b 0<b

    k : ℕ
    k = proj₁ e-res

    εk<b : ε k < b
    εk<b = proj₂ e-res

    xy-res : Σ ℕ (λ j → ∀ p → p ≥ j → ∣ centre x p - centre y p ∣ < ε k)
    xy-res = x≈y k

    N : ℕ
    N = proj₁ xy-res

    hN : ∀ p → p ≥ N → ∣ centre x p - centre y p ∣ < ε k
    hN = proj₂ xy-res

    ws-res : Σ ℕ (λ j → (n ⊔ N) ≤ℕ j × width y j < b)
    ws-res = width-below-strict y b (n ⊔ N) 0<b

    m : ℕ
    m = proj₁ ws-res

    m≥nN : (n ⊔ N) ≤ℕ m
    m≥nN = proj₁ (proj₂ ws-res)

    wym<b : width y m < b
    wym<b = proj₂ (proj₂ ws-res)

    m≥n : n ≤ℕ m
    m≥n = ≤ℕ-trans (m≤m⊔n n N) m≥nN

    m≥N : N ≤ℕ m
    m≥N = ≤ℕ-trans (m≤n⊔m n N) m≥nN

    neg-diff : centre y m - centre x m ≡ neg (centre x m - centre y m)
    neg-diff = let open ≡-Reasoning in begin
      centre y m - centre x m
      ≡⟨⟩
      centre y m + neg (centre x m)
      ≡⟨ +-comm (centre y m) (neg (centre x m)) ⟩
      neg (centre x m) + centre y m
      ≡⟨ cong (neg (centre x m) +_) (sym (neg-invol (centre y m))) ⟩
      neg (centre x m) + neg (neg (centre y m))
      ≡⟨ sym (neg-distrib-+ (centre x m) (neg (centre y m))) ⟩
      neg (centre x m + neg (centre y m))
      ≡⟨⟩
      neg (centre x m - centre y m) ∎

    swp : ∣ centre y m - centre x m ∣ ≡ ∣ centre x m - centre y m ∣
    swp = trans (cong ∣_∣ neg-diff) (∣-p∣≡∣p∣ _)

    cy-cx<b : ∣ centre y m - centre x m ∣ < b
    cy-cx<b =
      subst (λ z → z < b) (sym swp)
            (<-trans (hN m m≥N) εk<b)

    uxm≤uxn : u x m ≤ u x n
    uxm≤uxn = u-mono x m≥n

    lzn≤lzm : l z n ≤ l z m
    lzn≤lzm = l-mono z m≥n

    uy≤cy+wy : u y m ≤ centre y m + width y m
    uy≤cy+wy = u≤c+w y m

    cx≤uxm : centre x m ≤ u x m
    cx≤uxm = centre-u x m

    uy-ux-le : u y m - u x m ≤ width y m + ∣ centre y m - centre x m ∣
    uy-ux-le =
      let
        a : u y m - u x m ≤ (centre y m + width y m) - centre x m
        a = +-mono-≤ uy≤cy+wy (neg-antimono-≤ cx≤uxm)
        b' : (centre y m + width y m) - centre x m
               ≡ width y m + (centre y m - centre x m)
        b' = let open ≡-Reasoning in begin
          (centre y m + width y m) - centre x m
          ≡⟨⟩
          (centre y m + width y m) + neg (centre x m)
          ≡⟨ +-assoc (centre y m) (width y m) (neg (centre x m)) ⟩
          centre y m + (width y m + neg (centre x m))
          ≡⟨ cong (centre y m +_) (+-comm (width y m) (neg (centre x m))) ⟩
          centre y m + (neg (centre x m) + width y m)
          ≡⟨ sym (+-assoc (centre y m) (neg (centre x m)) (width y m)) ⟩
          (centre y m + neg (centre x m)) + width y m
          ≡⟨ +-comm (centre y m + neg (centre x m)) (width y m) ⟩
          width y m + (centre y m + neg (centre x m))
          ≡⟨⟩
          width y m + (centre y m - centre x m) ∎
        c : centre y m - centre x m ≤ ∣ centre y m - centre x m ∣
        c = r≤|r| (centre y m - centre x m)

        a' : u y m - u x m ≤ width y m + (centre y m - centre x m)
        a' = subst (λ w → u y m - u x m ≤ w) b' a
      in ≤-trans a' (+-mono-≤ (≤-refl {width y m}) c)

    uy-ux<b : u y m - u x m < b + b
    uy-ux<b = ≤-<-trans uy-ux-le (+-mono-< wym<b cy-cx<b)

    b+b≡d : b + b ≡ d
    b+b≡d = two-half d

    uy-ux<d : u y m - u x m < d
    uy-ux<d = subst (λ w → u y m - u x m < w) b+b≡d uy-ux<b

    be≤0 : u x m - u x n ≤ 0ℚ
    be≤0 = subst (λ z → u x m - u x n ≤ z) (+-inverseʳ (u x n))
                 (+-mono-≤ uxm≤uxn (≤-refl {neg (u x n)}))

    cpart : l z n + (u x m - u x n) ≤ l z n
    cpart = subst (λ w → l z n + (u x m - u x n) ≤ w)
                  (+-identityʳ (l z n))
                  (+-mono-≤ (≤-refl {l z n}) be≤0)

    raw : (u y m - u x m) + u x m < (l z n - u x n) + u x m
    raw = +-monoˡ-< (u x m) uy-ux<d

    lhs≡ : (u y m - u x m) + u x m ≡ u y m
    lhs≡ = trans (+-assoc (u y m) (neg (u x m)) (u x m))
             (trans (cong (u y m +_) (+-inverseˡ (u x m)))
                    (+-identityʳ (u y m)))

    rhs≡ : (l z n - u x n) + u x m ≡ l z n + (u x m - u x n)
    rhs≡ = trans (+-assoc (l z n) (neg (u x n)) (u x m))
                 (cong (l z n +_) (+-comm (neg (u x n)) (u x m)))

    a< : u y m < l z n + (u x m - u x n)
    a< = subst (λ w → w < l z n + (u x m - u x n)) lhs≡
           (subst (λ w → (u y m - u x m) + u x m < w) rhs≡ raw)

    uym<lzm : u y m < l z m
    uym<lzm = <-≤-trans (<-≤-trans a< cpart) lzn≤lzm

------------------------------------------------------------------------
-- Monotonicity of order under addition
--
-- 序在加法下的单调性

<-+mono : (x y z : RealI) → x <ℝ y → x +ℝ z <ℝ y +ℝ z
<-+mono x y z (n , p) = k , goal
  where
    g : ℚ
    g = l y n - u x n

    0<g : 0ℚ < g
    0<g = subst (λ w → w < l y n - u x n) (+-inverseʳ (u x n))
             (+-monoˡ-< (neg (u x n)) p)

    k-res : Σ ℕ (λ j → n ≤ℕ j × width z j < g)
    k-res = width-below-strict z g n 0<g

    k : ℕ
    k = proj₁ k-res

    k≥n : n ≤ℕ k
    k≥n = proj₁ (proj₂ k-res)

    wzk<g : width z k < g
    wzk<g = proj₂ (proj₂ k-res)

    uxk≤uxn : u x k ≤ u x n
    uxk≤uxn = u-mono x k≥n

    lyn≤lyk : l y n ≤ l y k
    lyn≤lyk = l-mono y k≥n

    ux+g≡ly : u x n + g ≡ l y n
    ux+g≡ly =
      trans (sym (+-assoc (u x n) (l y n) (neg (u x n))))
      (trans (cong (λ z → z + neg (u x n)) (+-comm (u x n) (l y n)))
      (trans (+-assoc (l y n) (u x n) (neg (u x n)))
      (trans (cong (l y n +_) (+-inverseʳ (u x n)))
             (+-identityʳ (l y n)))))

    l+w≡u : l z k + width z k ≡ u z k
    l+w≡u =
      trans (sym (+-assoc (l z k) (u z k) (neg (l z k))))
      (trans (cong (λ w → w + neg (l z k)) (+-comm (l z k) (u z k)))
      (trans (+-assoc (u z k) (l z k) (neg (l z k)))
      (trans (cong (u z k +_) (+-inverseʳ (l z k)))
             (+-identityʳ (u z k)))))

    first : u x k + width z k ≤ u x n + width z k
    first = +-mono-≤ uxk≤uxn (≤-refl {width z k})

    second : u x n + width z k < u x n + g
    second = +-monoʳ-< (u x n) wzk<g

    mid : u x k + width z k < l y n
    mid = subst (λ w → u x k + width z k < w) ux+g≡ly
            (≤-<-trans first second)

    core : u x k + width z k < l y k
    core = <-≤-trans mid lyn≤lyk

    added : (u x k + width z k) + l z k < l y k + l z k
    added = +-monoˡ-< (l z k) core

    reorder : (u x k + width z k) + l z k
              ≡ u x k + (l z k + width z k)
    reorder =
      trans (+-assoc (u x k) (width z k) (l z k))
            (cong (u x k +_) (+-comm (width z k) (l z k)))

    shifted : u x k + (l z k + width z k) < l y k + l z k
    shifted = subst (λ q → q < l y k + l z k) reorder added

    shifted-final : u x k + u z k < l y k + l z k
    shifted-final =
      subst (λ a → u x k + a < l y k + l z k) l+w≡u shifted

    lhs≡ : u (x +ℝ z) k ≡ u x k + u z k
    lhs≡ = u-hom x z k

    rhs≡ : l (y +ℝ z) k ≡ l y k + l z k
    rhs≡ = l-hom y z k

    goal : u (x +ℝ z) k < l (y +ℝ z) k
    goal = subst (λ a → a < l (y +ℝ z) k) (sym lhs≡)
             (subst (λ b → u x k + u z k < b) (sym rhs≡) shifted-final)

<-neg : (x y : RealI) → x <ℝ y → negℝ y <ℝ negℝ x
<-neg x y (n , p) = n , goal
  where
    raw : neg (l y n) < neg (u x n)
    raw = neg-antimono-< p

    lhs≡ : u (negℝ y) n ≡ neg (l y n)
    lhs≡ = u-neg y n

    rhs≡ : l (negℝ x) n ≡ neg (u x n)
    rhs≡ = l-neg x n

    goal : u (negℝ y) n < l (negℝ x) n
    goal = subst (λ a → a < l (negℝ x) n) (sym lhs≡)
             (subst (λ b → neg (l y n) < b) (sym rhs≡) raw)

<-sub : (x y z : RealI) → x <ℝ y → x -ℝ z <ℝ y -ℝ z
<-sub x y z p = <-+mono x y (negℝ z) p
