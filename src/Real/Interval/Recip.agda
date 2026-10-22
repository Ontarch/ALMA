------------------------------------------------------------------------
-- Reciprocals of interval reals
--
-- 区间实数的倒数
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module Real.Interval.Recip where

open import Data.Empty using (⊥)
open import Data.Nat using
  (ℕ; suc; z≤n; _∸_; _^_; _≥_; s≤s)
  renaming (_≤_ to _≤ℕ_; _+_ to _+ℕ_; _*_ to _ℕ*_; _<_ to _<ℕ_)
open import Data.Nat.Properties using
  (m≤m+n; m≤n+m; +-suc; *-mono-≤; *-suc; ^-distribʳ-*; ^-distribˡ-+-*)
  renaming (≤-trans to ≤ℕ-trans; ≤-refl to ≤ℕ-refl; *-comm to *-commℕ
          ; *-assoc to *-assocℕ; *-identityʳ to *-identityʳℕ)
import Data.Nat.Properties as ℕP
open import Data.Product using (proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Rational using
  (ℚ; 0ℚ; 1ℚ; _+_; _-_; _*_; _<_; _≤_; ∣_∣; Positive; NonZero; positive)
open import Data.Rational.Base using (1/_; NonNegative; nonNegative)
  renaming (-_ to neg)
open import Data.Rational.Properties using
  (pos⇒nonZero; positive⁻¹; 1/pos⇒pos; pos*pos⇒pos; pos⇒nonNeg; <⇒≤
  ; <-trans; ≤-reflexive; ≤-trans; <-irrefl; *-comm; *-assoc; *-identityˡ
  ; *-identityʳ; *-inverseʳ; *-inverseˡ; *-distribʳ-+; neg-distribˡ-*
  ; neg-distrib-+; +-identityʳ; +-comm; <-≤-trans; ≤-<-trans; *-monoˡ-≤-nonNeg
  ; *-monoʳ-≤-nonNeg; *-monoˡ-<-pos; *-cancelˡ-≤-pos; 0≤∣p∣; ∣-p∣≡∣p∣
  ; ∣p*q∣≡∣p∣*∣q∣; 0≤p⇒∣p∣≡p)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; sym; trans; cong; cong₂; subst; subst₂; module ≡-Reasoning)
open ≡-Reasoning

open import Real using
  (CauchySeq; ε; embed; embed-suc-pos; embed-*-hom; 0≤embed)
open CauchySeq renaming (f to seq-f; μ to seq-μ; cauchy to seq-cauchy)
open import Real.Interval using (RealI; δ; δ-pos)
open import Real.IntervalEquiv using
  (l; u; l-mono; centre-l; bound-w; realI→cauchy; embed-mono-<; n<2^n; suc∸1)
open import Real.CauchyToInterval using (cauchy→realI; recip-strict; K)
open import Real.Interval.Order using (_<ℝ_)
open import Real.Interval.Arith using (0ℝ; negℝ)
open import Real.Interval.OrderLaws using (≈-<-resp; <-neg)
open import Real.Interval.ArithLaws using (negℝ-0ℝ)
open import Real.Interval.Kit using
  (*-mono-≤-nonNeg; recip-antitone; n≤2n; embed-mono-≤)
open import Real.Interval.Node using (u-dyadic)
open import Real.Interval.Reasoning using (begin≤_; _≈⟨_⟩_; _≤⟨_⟩_; _≤∎)
open import Base.RationalRing using (neg-involutive)

------------------------------------------------------------------------
-- Common denominator
--
-- The difference of two reciprocals is (B − A) times the reciprocal
-- of A * B.
--
-- 公共分母
--
-- 把两个倒数之差写成 (B − A) 乘以 A * B 的倒数。

inv-sub : (A B : ℚ) {{A-nz : NonZero A}} {{B-nz : NonZero B}}
  {{AB-nz : NonZero (A * B)}} →
  (1/ A) - (1/ B) ≡ (B + neg A) * (1/ (A * B))
inv-sub A B =
  begin
    (1/ A) - (1/ B)
      ≡⟨⟩
    (1/ A) + neg (1/ B)
      ≡⟨ cong₂ (λ x y → x + neg y) iA≡ iB≡ ⟩
    B * iP + neg (A * iP)
      ≡⟨ cong (B * iP +_) (neg-distribˡ-* A iP) ⟩
    B * iP + neg A * iP
      ≡⟨ sym (*-distribʳ-+ iP B (neg A)) ⟩
    (B + neg A) * iP
      ∎
  where
    iP : ℚ
    iP = 1/ (A * B)
    A*B≡ : (1/ A) * (A * B) ≡ B
    A*B≡ =
      trans (sym (*-assoc (1/ A) A B))
      (trans (cong (λ z → z * B) (*-inverseˡ A))
             (*-identityˡ B))
    iA≡ : (1/ A) ≡ B * iP
    iA≡ =
      trans (sym (*-identityʳ (1/ A)))
      (trans (cong ((1/ A) *_) (sym (*-inverseʳ (A * B))))
      (trans (sym (*-assoc (1/ A) (A * B) iP))
             (cong (_* iP) A*B≡)))
    B*A≡ : (1/ B) * (B * A) ≡ A
    B*A≡ =
      trans (sym (*-assoc (1/ B) B A))
      (trans (cong (λ z → z * A) (*-inverseˡ B))
             (*-identityˡ A))
    iB≡ : (1/ B) ≡ A * iP
    iB≡ =
      trans (sym (*-identityʳ (1/ B)))
      (trans (cong ((1/ B) *_) (sym (*-inverseʳ (A * B))))
      (trans (sym (*-assoc (1/ B) (A * B) iP))
             (cong (_* iP)
               (trans (cong ((1/ B) *_) (*-comm A B)) B*A≡))))

-- Upper bound of the zero interval real
--
-- The upper bound of 0ℝ at precision K is exactly δ K.
--
-- 零区间实数的上界
--
-- 在精度 K 下，0ℝ 的上界恰好是 δ K。
u-0ℝ : (K : ℕ) → u 0ℝ K ≡ δ K
u-0ℝ K = trans (u-dyadic 0ℚ K) (+-identityʳ (δ K))

------------------------------------------------------------------------
-- Positive Cauchy sequences
--
-- A Cauchy sequence is positive if it is eventually bounded below by
-- a strictly positive rational number.
--
-- 正 Cauchy 序列
--
-- 一个 Cauchy 序列是正的，如果它最终被一个严格正的有理数作为下界。

record PosCauchy : Set₁ where
  field
    seq   : CauchySeq
    b     : ℚ
    0<b   : 0ℚ < b
    N₀    : ℕ
    lower : ∀ n → n ≥ N₀ → b ≤ seq-f seq n
open PosCauchy

------------------------------------------------------------------------
-- Convergence modulus for the reciprocal
--
-- Computes the modulus of convergence for the reciprocal of a
-- positive Cauchy sequence, ensuring the error bounds are met.
--
-- 倒数的收敛模数
--
-- 计算正 Cauchy 序列倒数的收敛模数，确保满足误差界。

private
  module RecipModAux (b : ℚ) (0<b : 0ℚ < b) (k : ℕ) where
    bsq : ℚ
    bsq = b * b

    bsq-pos : Positive bsq
    bsq-pos = pos*pos⇒pos b {{positive 0<b}} b {{positive 0<b}}

    bsq-nz : NonZero bsq
    bsq-nz = pos⇒nonZero bsq {{bsq-pos}}

    bsq-nn : NonNegative bsq
    bsq-nn = pos⇒nonNeg bsq {{bsq-pos}}

    inv-bsq : ℚ
    inv-bsq = (1/ bsq) {{bsq-nz}}

    inv-bsq-pos : Positive inv-bsq
    inv-bsq-pos = 1/pos⇒pos bsq {{bsq-pos}}

    e-pos : Positive (embed (suc k))
    e-pos = embed-suc-pos

    e-nz : NonZero (embed (suc k))
    e-nz = pos⇒nonZero (embed (suc k)) {{e-pos}}

    w : ℚ
    w = embed (suc k) * inv-bsq

    0<w : 0ℚ < w
    0<w = positive⁻¹ w
            {{pos*pos⇒pos (embed (suc k)) {{e-pos}}
                          inv-bsq {{inv-bsq-pos}}}}

    0≤w : 0ℚ ≤ w
    0≤w = <⇒≤ 0<w

recip-modulus : (b : ℚ) → 0ℚ < b → ℕ → ℕ
recip-modulus b 0<b k = proj₁ (bound-w w 0≤w)
  where
    open RecipModAux b 0<b k

------------------------------------------------------------------------
-- Specification of recip-modulus
--
-- Proves that the chosen modulus M satisfies the required inequality:
-- ε M < b² * ε k.
--
-- recip-modulus 的规格
--
-- 证明所选的模数 M 满足所需的不等式：ε M < b² * ε k。

recip-modulus-spec : (b : ℚ) (0<b : 0ℚ < b) (k : ℕ) →
  ε (recip-modulus b 0<b k) < (b * b) * ε k
recip-modulus-spec b 0<b k = goal
  where
    open RecipModAux b 0<b k

    M : ℕ
    M = recip-modulus b 0<b k

    w≤eM : w ≤ embed M
    w≤eM = proj₂ (bound-w w 0≤w)

    eM>0 : 0ℚ < embed M
    eM>0 = <-≤-trans 0<w w≤eM

    eM-pos : Positive (embed M)
    eM-pos = positive eM>0

    eM-nz : NonZero (embed M)
    eM-nz = pos⇒nonZero (embed M) {{eM-pos}}

    w-bsq-eq : w * bsq ≡ embed (suc k)
    w-bsq-eq = begin
      w * bsq
        ≡⟨ refl ⟩
      (embed (suc k) * inv-bsq) * bsq
        ≡⟨ *-assoc (embed (suc k)) inv-bsq bsq ⟩
      embed (suc k) * (inv-bsq * bsq)
        ≡⟨ cong (embed (suc k) *_) (*-comm inv-bsq bsq) ⟩
      embed (suc k) * (bsq * inv-bsq)
        ≡⟨ cong (embed (suc k) *_) (*-inverseʳ bsq {{bsq-nz}}) ⟩
      embed (suc k) * 1ℚ
        ≡⟨ *-identityʳ (embed (suc k)) ⟩
      embed (suc k)
      ∎

    key1 : embed (suc k) ≤ embed M * bsq
    key1 = subst (λ z → z ≤ embed M * bsq) w-bsq-eq
             (*-monoʳ-≤-nonNeg bsq {{bsq-nn}} w≤eM)

    ε-pos : Positive (ε k)
    ε-pos = 1/pos⇒pos (embed (suc k)) {{e-pos}}

    ε-nn : NonNegative (ε k)
    ε-nn = pos⇒nonNeg (ε k) {{ε-pos}}

    ε-left : ε k * embed (suc k) ≡ 1ℚ
    ε-left = *-inverseˡ (embed (suc k)) {{e-nz}}

    ε-right : ε k * (embed M * bsq) ≡ (embed M * bsq) * ε k
    ε-right = *-comm (ε k) (embed M * bsq)

    key2 : 1ℚ ≤ (embed M * bsq) * ε k
    key2 = subst₂ _≤_ ε-left ε-right
             (*-monoˡ-≤-nonNeg (ε k) {{ε-nn}} key1)

    key3 : (1/ embed M) {{eM-nz}} ≤ bsq * ε k
    key3 = *-cancelˡ-≤-pos (embed M) {{eM-pos}}
             (subst₂ _≤_
               (sym (*-inverseʳ (embed M) {{eM-nz}}))
               (*-assoc (embed M) bsq (ε k))
               key2)

    M<sM : embed M < embed (suc M)
    M<sM = embed-mono-< (s≤s (≤ℕ-refl {M}))

    strict : ε M < (1/ embed M) {{eM-nz}}
    strict = recip-strict eM>0 M<sM

    goal : ε M < bsq * ε k
    goal = <-≤-trans strict key3

------------------------------------------------------------------------
-- Reciprocal of a positive Cauchy sequence
--
-- Constructs the reciprocal Cauchy sequence from a positive Cauchy
-- sequence, using the algebraic identity for reciprocal differences
-- to establish the Cauchy condition.
--
-- 正 Cauchy 序列的倒数
--
-- 从正 Cauchy 序列构造其倒数 Cauchy 序列，利用倒数差的代数恒等式
-- 来建立柯西条件。

recipCauchy : PosCauchy → CauchySeq
recipCauchy pc = record
  { f      = h
  ; μ      = μ-h
  ; cauchy = cauchy-h
  }
  where
    x    = PosCauchy.seq pc
    bp   = PosCauchy.b pc
    0<bp = PosCauchy.0<b pc
    N0   = PosCauchy.N₀ pc
    low  = PosCauchy.lower pc

    g : ℕ → ℚ
    g n = seq-f x (N0 +ℕ n)

    0<g : ∀ n → 0ℚ < g n
    0<g n = <-≤-trans 0<bp (low (N0 +ℕ n) (m≤m+n N0 n))

    nz-g : ∀ n → NonZero (g n)
    nz-g n = pos⇒nonZero (g n) {{positive (0<g n)}}

    h : ℕ → ℚ
    h n = (1/ g n) {{nz-g n}}

    μ-h : ℕ → ℕ
    μ-h k = seq-μ x (recip-modulus bp 0<bp k)

    cauchy-h : ∀ k n m → n ≥ μ-h k → m ≥ μ-h k → ∣ h n - h m ∣ < ε k
    cauchy-h k n m n≥μ m≥μ = goal
      where
        M : ℕ
        M = recip-modulus bp 0<bp k

        bsq : ℚ
        bsq = bp * bp

        bsq-pos : Positive bsq
        bsq-pos = pos*pos⇒pos bp {{positive 0<bp}} bp {{positive 0<bp}}

        bsq-nz : NonZero bsq
        bsq-nz = pos⇒nonZero bsq {{bsq-pos}}

        inv-bsq : ℚ
        inv-bsq = (1/ bsq) {{bsq-nz}}

        inv-bsq-pos : Positive inv-bsq
        inv-bsq-pos = 1/pos⇒pos bsq {{bsq-pos}}

        n-shift : seq-μ x M ≤ℕ N0 +ℕ n
        n-shift = ≤ℕ-trans n≥μ (m≤n+m n N0)

        m-shift : seq-μ x M ≤ℕ N0 +ℕ m
        m-shift = ≤ℕ-trans m≥μ (m≤n+m m N0)

        cg : ∣ g n - g m ∣ < ε M
        cg = seq-cauchy x M (N0 +ℕ n) (N0 +ℕ m) n-shift m-shift

        gn≥bp : bp ≤ g n
        gn≥bp = low (N0 +ℕ n) (m≤m+n N0 n)

        gm≥bp : bp ≤ g m
        gm≥bp = low (N0 +ℕ m) (m≤m+n N0 m)

        0<gn : 0ℚ < g n
        0<gn = <-≤-trans 0<bp gn≥bp

        0<gm : 0ℚ < g m
        0<gm = <-≤-trans 0<bp gm≥bp

        gn-nz : NonZero (g n)
        gn-nz = pos⇒nonZero (g n) {{positive 0<gn}}

        gm-nz : NonZero (g m)
        gm-nz = pos⇒nonZero (g m) {{positive 0<gm}}

        gn*gm-nz : NonZero (g n * g m)
        gn*gm-nz = pos⇒nonZero (g n * g m)
                     {{pos*pos⇒pos (g n) {{positive 0<gn}}
                                    (g m) {{positive 0<gm}}}}

        gn*gm-bsq : bsq ≤ g n * g m
        gn*gm-bsq = *-mono-≤-nonNeg (<⇒≤ 0<bp) gn≥bp (<⇒≤ 0<bp) gm≥bp

        -- Algebraic identity:
        --   h n - h m ≡ (g m - g n) * (1/(g n * g m))
        -- Multiply both sides by the positive g n * g m; it reduces
        -- to g m - g n, then cancel by positivity.
        --
        -- 代数恒等式：
        --   h n - h m ≡ (g m - g n) * (1/(g n * g m))
        -- 两边同乘正数 g n * g m，化简为 g m - g n，
        -- 再用正数约去。
        iP = (1/ (g n * g m)) {{gn*gm-nz}}

        inv-eq : h n - h m ≡ (g m + neg (g n)) * iP
        inv-eq = inv-sub (g n) (g m) {{gn-nz}} {{gm-nz}} {{gn*gm-nz}}

        -- From inv-eq take absolute values; the absolute value
        -- distributes over the product, then |g m - g n| is replaced
        -- by |g n - g m| (they are mutual negatives).
        -- g m - g n ≡ neg (g n - g m): swap addends, expand the
        -- negative, then neg(neg x)=x.
        --
        -- 由 inv-eq 取绝对值，绝对值把乘积拆开，再把 |g m - g n|
        -- 换成 |g n - g m|（二者互为相反数）。
        -- g m - g n ≡ neg (g n - g m)：交换加项、展开负号、
        -- neg(neg x)=x。
        minus-flip : g m - g n ≡ neg (g n - g m)
        minus-flip =
          trans (+-comm (g m) (neg (g n)))
          (sym
            (trans (neg-distrib-+ (g n) (neg (g m)))
                   (cong (λ z → neg (g n) + z) (neg-involutive (g m)))))

        flip : ∣ g m - g n ∣ ≡ ∣ g n - g m ∣
        flip =
          trans (cong ∣_∣ minus-flip)
                (∣-p∣≡∣p∣ (g n - g m))

        iP-pos : Positive iP
        iP-pos = 1/pos⇒pos (g n * g m)
                   {{pos*pos⇒pos (g n) {{positive 0<gn}}
                               (g m) {{positive 0<gm}}}}
        0≤iP : 0ℚ ≤ iP
        0≤iP = <⇒≤ (positive⁻¹ iP {{iP-pos}})

        abs-eq : ∣ h n - h m ∣ ≡ ∣ g n - g m ∣ * iP
        abs-eq =
          begin
            ∣ h n - h m ∣
              ≡⟨ cong ∣_∣ inv-eq ⟩
            ∣ (g m - g n) * iP ∣
              ≡⟨ ∣p*q∣≡∣p∣*∣q∣ (g m - g n) iP ⟩
            ∣ g m - g n ∣ * ∣ iP ∣
              ≡⟨ cong (∣ g m - g n ∣ *_) (0≤p⇒∣p∣≡p 0≤iP) ⟩
            ∣ g m - g n ∣ * iP
              ≡⟨ cong (_* iP) flip ⟩
            ∣ g n - g m ∣ * iP
          ∎

        recip-bound : ((1/ (g n * g m)) {{gn*gm-nz}})
                      ≤ ((1/ bsq) {{bsq-nz}})
        recip-bound = recip-antitone {a = bsq} {b = g n * g m}
                        (positive⁻¹ bsq {{bsq-pos}})
                        gn*gm-bsq

        bound : ∣ h n - h m ∣ ≤ ∣ g n - g m ∣ * ((1/ bsq) {{bsq-nz}})
        bound = subst (λ z → z ≤ ∣ g n - g m ∣ * ((1/ bsq) {{bsq-nz}}))
                  (sym abs-eq)
                  (*-monoˡ-≤-nonNeg ∣ g n - g m ∣
                    {{nonNegative (0≤∣p∣ (g n - g m))}} recip-bound)

        eps-bound : ε M * ((1/ bsq) {{bsq-nz}}) < ε k
        eps-bound = subst
          (λ z → ε M * ((1/ bsq) {{bsq-nz}}) < z) right-eq step1
          where
            spec : ε M < bsq * ε k
            spec = recip-modulus-spec bp 0<bp k

            step1 : ε M * ((1/ bsq) {{bsq-nz}})
                    < (bsq * ε k) * ((1/ bsq) {{bsq-nz}})
            step1 = *-monoˡ-<-pos ((1/ bsq) {{bsq-nz}})
                      {{inv-bsq-pos}} spec

            right-eq : (bsq * ε k) * ((1/ bsq) {{bsq-nz}}) ≡ ε k
            right-eq = begin
              (bsq * ε k) * ((1/ bsq) {{bsq-nz}})
                ≡⟨ *-assoc bsq (ε k) ((1/ bsq) {{bsq-nz}}) ⟩
              bsq * (ε k * ((1/ bsq) {{bsq-nz}}))
                ≡⟨ cong (bsq *_) (*-comm (ε k) ((1/ bsq) {{bsq-nz}})) ⟩
              bsq * (((1/ bsq) {{bsq-nz}}) * ε k)
                ≡⟨ sym (*-assoc bsq ((1/ bsq) {{bsq-nz}}) (ε k)) ⟩
              (bsq * ((1/ bsq) {{bsq-nz}})) * ε k
                ≡⟨ cong (_* ε k) (*-inverseʳ bsq {{bsq-nz}}) ⟩
              1ℚ * ε k
                ≡⟨ *-identityˡ (ε k) ⟩
              ε k
              ∎

        goal : ∣ h n - h m ∣ < ε k
        goal = ≤-<-trans bound
                 (<-trans
                   (*-monoˡ-<-pos
                     ((1/ bsq) {{bsq-nz}}) {{inv-bsq-pos}}
                     cg)
                   eps-bound)

------------------------------------------------------------------------
-- Positive interval real to positive Cauchy sequence
--
-- 正区间实数 → 正 Cauchy 序列

realI→posCauchy : (x : RealI) → 0ℝ <ℝ x → PosCauchy
realI→posCauchy x 0<x = record
  { seq   = realI→cauchy x
  ; b     = l x n
  ; 0<b   = 0<lxn
  ; N₀    = n
  ; lower = bound
  }
  where
    n      = proj₁ 0<x
    δn<lxn = proj₂ 0<x

    0<lxn : 0ℚ < l x n
    0<lxn = <-trans (δ-pos n)
              (subst (λ z → z < l x n) (u-0ℝ n) δn<lxn)

    bound : ∀ m → m ≥ n → l x n ≤ seq-f (realI→cauchy x) m
    bound m m≥n =
      ≤-trans (l-mono x m≥n) (centre-l x m)

------------------------------------------------------------------------
-- Reciprocal of a positive interval real
--
-- 正区间实数的倒数

recipℝ : (x : RealI) → 0ℝ <ℝ x → RealI
recipℝ x 0<x = cauchy→realI (recipCauchy (realI→posCauchy x 0<x))

------------------------------------------------------------------------
-- Reciprocal of a non-zero interval real
--
-- 非零区间实数的倒数

recipℝ' : (x : RealI) → (0ℝ <ℝ x) ⊎ (x <ℝ 0ℝ) → RealI
recipℝ' x (inj₁ 0<x) = recipℝ x 0<x
recipℝ' x (inj₂ x<0) =
  negℝ (recipℝ (negℝ x) (≈-<-resp negℝ-0ℝ (<-neg x 0ℝ x<0)))

------------------------------------------------------------------------
-- ℕ arithmetic auxiliaries
--
-- ℕ 算术辅助

private
  2^n*2^n≡4^n : ∀ n → 2 ^ n ℕ* 2 ^ n ≡ 4 ^ n
  2^n*2^n≡4^n n = sym (^-distribʳ-* n 2 2)

  4n²≤4^n : ∀ n → n ≥ 4 → 4 ℕ* (n ℕ* n) ≤ℕ 4 ^ n
  4n²≤4^n n n≥4 = goal
    where
    0<n : 0 <ℕ n
    0<n = ℕP.<-≤-trans (s≤s (z≤n {3})) n≥4
    m = n ∸ 1
    sm≡n : suc m ≡ n
    sm≡n = suc∸1 0<n
    n≡sucm : n ≡ suc m
    n≡sucm = sym sm≡n
    n≤2^m : n ≤ℕ 2 ^ m
    n≤2^m = ≤ℕ-trans (ℕP.≤-reflexive n≡sucm) (n<2^n m)
    n²≤4^m : n ℕ* n ≤ℕ 4 ^ m
    n²≤4^m = ≤ℕ-trans (*-mono-≤ n≤2^m n≤2^m)
                        (ℕP.≤-reflexive (2^n*2^n≡4^n m))
    4n²≤4^m : 4 ℕ* (n ℕ* n) ≤ℕ 4 ℕ* (4 ^ m)
    4n²≤4^m = *-mono-≤ (≤ℕ-refl {4}) n²≤4^m
    goal : 4 ℕ* (n ℕ* n) ≤ℕ 4 ^ n
    goal = ≤ℕ-trans 4n²≤4^m
                      (ℕP.≤-reflexive (cong (4 ^_) (sym n≡sucm)))

  4^n≤K-2n : ∀ n → 4 ^ n ≤ℕ K (2 ℕ* n)
  4^n≤K-2n n = ≤ℕ-trans (≤ℕ-trans p1 p2) (≤ℕ-trans p3 p4)
    where
    p1 : 4 ^ n ≤ℕ 2 ^ n ℕ* 2 ^ n
    p1 = ℕP.≤-reflexive (sym (2^n*2^n≡4^n n))
    p2 : 2 ^ n ℕ* 2 ^ n ≤ℕ 2 ^ (n +ℕ n)
    p2 = ℕP.≤-reflexive (sym (^-distribˡ-+-* 2 n n))
    m = 2 ^ (n +ℕ n)
    p3 : m ≤ℕ m ℕ* 4
    p3 = ≤ℕ-trans (m≤m+n m (m ℕ* 3))
                    (ℕP.≤-reflexive (sym (*-suc m 3)))
    2n≡n+n : 2 ℕ* n ≡ n +ℕ n
    2n≡n+n = trans (*-commℕ 2 n)
               (trans (*-suc n 1) (cong (n +ℕ_) (*-identityʳℕ n)))
    +2≡suc² : ∀ m → m +ℕ 2 ≡ suc (suc m)
    +2≡suc² m = begin
      m +ℕ 2
        ≡⟨ +-suc m 1 ⟩
      suc (m +ℕ 1)
        ≡⟨ cong suc (+-suc m 0) ⟩
      suc (suc (m +ℕ 0))
        ≡⟨ cong (λ k → suc (suc k)) (ℕP.+-identityʳ m) ⟩
      suc (suc m)
      ∎
    exp-eq : (n +ℕ n) +ℕ 2 ≡ suc (suc (2 ℕ* n))
    exp-eq = trans (+2≡suc² (n +ℕ n))
              (cong (λ k → suc (suc k)) (sym 2n≡n+n))
    p4 : m ℕ* 4 ≤ℕ K (2 ℕ* n)
    p4 = ℕP.≤-reflexive
      (begin
        m ℕ* 4
          ≡⟨ sym (^-distribˡ-+-* 2 (n +ℕ n) 2) ⟩
        2 ^ ((n +ℕ n) +ℕ 2)
          ≡⟨ cong (2 ^_) exp-eq ⟩
        K (2 ℕ* n)
        ∎)

  from-not : ∀ m n → ¬ (suc m ≤ℕ n) → n ≤ℕ m
  from-not m n f = ℕP.≤-pred (ℕP.≰⇒> f)

------------------------------------------------------------------------
-- Strict lower bound for recip-modulus
--
-- recip-modulus 的严格下界

recip-modulus-lower :
    (b : ℚ) (0<b : 0ℚ < b) (k : ℕ) →
    embed (suc k) < b * b * embed (suc (recip-modulus b 0<b k))
recip-modulus-lower b 0<b k = goal
  where
    bsq = b * b
    bsq-pos : Positive bsq
    bsq-pos = pos*pos⇒pos b {{positive 0<b}} b {{positive 0<b}}
    bsq-nz : NonZero bsq
    bsq-nz = pos⇒nonZero bsq {{bsq-pos}}
    bsq-nn : NonNegative bsq
    bsq-nn = pos⇒nonNeg bsq {{bsq-pos}}
    inv-bsq = (1/ bsq) {{bsq-nz}}
    e-sk = embed (suc k)
    e-sk-pos : Positive e-sk
    e-sk-pos = embed-suc-pos
    w = e-sk * inv-bsq
    inv-bsq-pos : Positive inv-bsq
    inv-bsq-pos = 1/pos⇒pos bsq {{bsq-pos}}
    w-pos : Positive w
    w-pos = pos*pos⇒pos e-sk {{e-sk-pos}} inv-bsq {{inv-bsq-pos}}
    Mm = recip-modulus b 0<b k
    w≤eM : w ≤ embed Mm
    w≤eM = proj₂ (bound-w w (<⇒≤ (positive⁻¹ w {{w-pos}})))
    w*bsq-eq : w * bsq ≡ e-sk
    w*bsq-eq = begin
      w * bsq
        ≡⟨ *-assoc e-sk inv-bsq bsq ⟩
      e-sk * (inv-bsq * bsq)
        ≡⟨ cong (e-sk *_) (*-comm inv-bsq bsq) ⟩
      e-sk * (bsq * inv-bsq)
        ≡⟨ cong (e-sk *_) (*-inverseʳ bsq {{bsq-nz}}) ⟩
      e-sk * 1ℚ
        ≡⟨ *-identityʳ e-sk ⟩
      e-sk
      ∎
    key1 : e-sk ≤ embed Mm * bsq
    key1 = begin≤
      e-sk
        ≈⟨ sym w*bsq-eq ⟩
      w * bsq
        ≤⟨ *-monoʳ-≤-nonNeg bsq {{bsq-nn}} w≤eM ⟩
      embed Mm * bsq
      ≤∎
    M<sM : embed Mm < embed (suc Mm)
    M<sM = embed-mono-< (s≤s (≤ℕ-refl {Mm}))
    key2 : embed Mm * bsq < embed (suc Mm) * bsq
    key2 = *-monoˡ-<-pos bsq {{bsq-pos}} M<sM
    goal : e-sk < bsq * embed (suc Mm)
    goal = <-≤-trans
      (≤-<-trans key1 key2)
      (≤-reflexive (*-comm (embed (suc Mm)) bsq))

-- 2b² grows in the tail
--
-- 2b² 在尾部的增长
embed-n≥2b² :
    (b : ℚ) (N : ℕ) →
    embed 2 * b * b ≤ embed N →
    ∀ n → n ≥ N → embed 2 * b * b ≤ embed n
embed-n≥2b² b N base n n≥N =
  ≤-trans base (embed-mono-≤ n≥N)

-- 2n·b² ≤ 4^n in the tail
--
-- 2n·b² ≤ 4^n 在尾部
2n*b²≤4^n :
    (b : ℚ) (0<b : 0ℚ < b) (N : ℕ) →
    N ≥ 4 →
    (∀ n → n ≥ N → embed 2 * b * b ≤ embed n) →
    ∀ n → n ≥ N → embed (2 ℕ* n) * b * b ≤ embed (4 ^ n)
2n*b²≤4^n b 0<b N N≥4 hb n n≥N = goal
  where
    b-pos : Positive b
    b-pos = positive 0<b
    bsq = b * b
    bsq-pos : Positive bsq
    bsq-pos = pos*pos⇒pos b {{b-pos}} b {{b-pos}}
    bsq-nn = pos⇒nonNeg bsq {{bsq-pos}}
    e2n = embed (2 ℕ* n)
    e2n-nn = nonNegative (0≤embed (2 ℕ* n))
    assoc : (embed 2 * b) * b ≡ embed 2 * bsq
    assoc = *-assoc (embed 2) b b
    2b²≤e2n : embed 2 * bsq ≤ e2n
    2b²≤e2n = begin≤
      embed 2 * bsq
        ≈⟨ sym assoc ⟩
      (embed 2 * b) * b
        ≤⟨ hb (2 ℕ* n) (≤ℕ-trans n≥N (n≤2n n)) ⟩
      e2n
      ≤∎
    1≤2 : 1ℚ ≤ embed 2
    1≤2 = embed-mono-≤ (s≤s z≤n)
    mono : bsq * 1ℚ ≤ bsq * embed 2
    mono = *-monoˡ-≤-nonNeg bsq {{bsq-nn}} 1≤2
    bsq≤2b² : bsq ≤ embed 2 * bsq
    bsq≤2b² = begin≤
      bsq
        ≈⟨ sym (*-identityʳ bsq) ⟩
      bsq * 1ℚ
        ≤⟨ mono ⟩
      bsq * embed 2
        ≈⟨ *-comm bsq (embed 2) ⟩
      embed 2 * bsq
      ≤∎
    bsq≤e2n : bsq ≤ e2n
    bsq≤e2n = ≤-trans bsq≤2b² 2b²≤e2n
    step1 : e2n * bsq ≤ e2n * e2n
    step1 = *-monoˡ-≤-nonNeg e2n {{e2n-nn}} bsq≤e2n
    prod-eq : e2n * e2n ≡ embed ((2 ℕ* n) ℕ* (2 ℕ* n))
    prod-eq = sym (embed-*-hom (2 ℕ* n) (2 ℕ* n))
    step2 : e2n * bsq ≤ embed ((2 ℕ* n) ℕ* (2 ℕ* n))
    step2 = ≤-trans step1 (≤-reflexive prod-eq)
    4n²≡ : (2 ℕ* n) ℕ* (2 ℕ* n) ≡ 4 ℕ* (n ℕ* n)
    4n²≡ = begin
      (2 ℕ* n) ℕ* (2 ℕ* n)
        ≡⟨ *-assocℕ 2 n (2 ℕ* n) ⟩
      2 ℕ* (n ℕ* (2 ℕ* n))
        ≡⟨ cong (2 ℕ*_) (*-commℕ n (2 ℕ* n)) ⟩
      2 ℕ* ((2 ℕ* n) ℕ* n)
        ≡⟨ cong (2 ℕ*_) (*-assocℕ 2 n n) ⟩
      2 ℕ* (2 ℕ* (n ℕ* n))
        ≡⟨ sym (*-assocℕ 2 2 (n ℕ* n)) ⟩
      (2 ℕ* 2) ℕ* (n ℕ* n)
        ≡⟨ cong (λ k → k ℕ* (n ℕ* n)) (*-suc 2 1) ⟩
      4 ℕ* (n ℕ* n)
        ∎
    step3 : e2n * bsq ≤ embed (4 ℕ* (n ℕ* n))
    step3 = ≤-trans step2 (≤-reflexive (cong embed 4n²≡))
    goal' : e2n * bsq ≤ embed (4 ^ n)
    goal' = ≤-trans step3
      (embed-mono-≤ (4n²≤4^n n (≤ℕ-trans N≥4 n≥N)))
    assocg : (e2n * b) * b ≡ e2n * bsq
    assocg = *-assoc e2n b b
    goal : e2n * b * b ≤ embed (4 ^ n)
    goal = begin≤
      e2n * b * b
        ≈⟨ assocg ⟩
      e2n * bsq
        ≤⟨ goal' ⟩
      embed (4 ^ n)
      ≤∎

-- recip-modulus at K(2n) is at least 2n
--
-- recip-modulus 在 K(2n) 处至少为 2n
recip-modulus-≥2n :
    (b : ℚ) (0<b : 0ℚ < b) (N : ℕ) →
    (∀ n → n ≥ N → embed (2 ℕ* n) * b * b ≤ embed (4 ^ n)) →
    ∀ n → n ≥ N → recip-modulus b 0<b (K (2 ℕ* n)) ≥ 2 ℕ* n
recip-modulus-≥2n b 0<b N h n n≥N = helper
  where
    b-pos : Positive b
    b-pos = positive 0<b
    bsq = b * b
    bsq-pos : Positive bsq
    bsq-pos = pos*pos⇒pos b {{b-pos}} b {{b-pos}}
    bsq-nn : NonNegative bsq
    bsq-nn = pos⇒nonNeg bsq {{bsq-pos}}
    k = K (2 ℕ* n)
    Nm = recip-modulus b 0<b k
    lb = recip-modulus-lower b 0<b k
    4n<sK : 4 ^ n <ℕ suc k
    4n<sK = ℕP.≤-<-trans (4^n≤K-2n n) (s≤s (≤ℕ-refl {k}))
    e4n<esK : embed (4 ^ n) < embed (suc k)
    e4n<esK = embed-mono-< 4n<sK
    chain :
      suc Nm ≤ℕ 2 ℕ* n → bsq * embed (suc Nm) ≤ embed (4 ^ n)
    chain h' = begin≤
      bsq * embed (suc Nm)
        ≤⟨ *-monoˡ-≤-nonNeg bsq {{bsq-nn}} (embed-mono-≤ h') ⟩
      bsq * embed (2 ℕ* n)
        ≈⟨ *-comm bsq (embed (2 ℕ* n)) ⟩
      embed (2 ℕ* n) * bsq
        ≈⟨ sym (*-assoc (embed (2 ℕ* n)) b b) ⟩
      (embed (2 ℕ* n) * b) * b
        ≤⟨ h n n≥N ⟩
      embed (4 ^ n)
      ≤∎
    absurd : suc Nm ≤ℕ 2 ℕ* n → ⊥
    absurd h' =
      <-irrefl refl
        (<-trans e4n<esK (<-≤-trans lb (chain h')))
    helper : 2 ℕ* n ≤ℕ Nm
    helper = from-not Nm (2 ℕ* n) absurd
