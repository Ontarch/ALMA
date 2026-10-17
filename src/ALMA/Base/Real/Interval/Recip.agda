------------------------------------------------------------------------
-- Reciprocals of interval reals
--
-- Reciprocal construction for positive Cauchy sequences and interval
-- reals, together with the algebraic identity for differences of
-- reciprocals.
--
-- 区间实数的倒数
--
-- 正 Cauchy 序列与区间实数的倒数构造，连同倒数差的代数恒等式。
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module ALMA.Base.Real.Interval.Recip where

open import Data.Nat using (ℕ; suc; _≥_; s≤s) renaming (_≤_ to _≤ℕ_; _+_ to _+ℕ_)
open import Data.Nat.Properties using
  (m≤m+n; m≤n+m) renaming (≤-trans to ≤ℕ-trans; ≤-refl to ≤ℕ-refl)
open import Data.Product using (proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Rational using
  (ℚ; 0ℚ; 1ℚ; _+_; _-_; _*_; _<_; _≤_; ∣_∣; Positive; NonZero; positive)
open import Data.Rational.Base using (1/_; NonNegative; nonNegative) renaming (-_ to neg)
open import Data.Rational.Properties using
  (pos⇒nonZero; positive⁻¹; 1/pos⇒pos; pos*pos⇒pos; pos⇒nonNeg; <⇒≤; <-trans
  ; ≤-trans; *-comm; *-assoc; *-identityʳ; *-identityˡ; *-inverseʳ
  ; *-inverseˡ; *-distribʳ-+; neg-distribˡ-*; neg-distrib-+; +-identityʳ
  ; +-comm; <-≤-trans; ≤-<-trans; *-monoˡ-≤-nonNeg; *-monoʳ-≤-nonNeg
  ; *-monoˡ-<-pos; *-cancelˡ-≤-pos; 0≤∣p∣; ∣-p∣≡∣p∣
  ; ∣p*q∣≡∣p∣*∣q∣; 0≤p⇒∣p∣≡p)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; sym; trans; cong; cong₂; subst; subst₂; module ≡-Reasoning)
open ≡-Reasoning

open import ALMA.Base.Real using (CauchySeq; ε; embed; embed-suc-pos)
open CauchySeq renaming (f to seq-f; μ to seq-μ; cauchy to seq-cauchy)
open import ALMA.Base.Real.Interval using (RealI; δ; δ-pos)
open import ALMA.Base.Real.IntervalEquiv using
  (l; u; l-mono; centre-l; bound-w; realI→cauchy; embed-mono-<)
open import ALMA.Base.Real.CauchyToInterval using (cauchy→realI; recip-strict)
open import ALMA.Base.Real.Interval.Order using (_<ℝ_)
open import ALMA.Base.Real.Interval.Arith using (0ℝ; negℝ)
open import ALMA.Base.Real.Interval.OrderLaws using (≈-<-resp; <-neg)
open import ALMA.Base.Real.Interval.ArithLaws using (negℝ-0ℝ)
open import ALMA.Base.Real.Interval.Kit using (*-mono-≤-nonNeg; recip-antitone)
open import ALMA.Base.Real.Interval.Node using (u-dyadic)
open import ALMA.Physics.RationalKit using (neg-involutive)

------------------------------------------------------------------------
-- Common denominator: the difference of two reciprocals is (B − A)
-- times the reciprocal of A * B.
--
-- 公共分母：把两个倒数之差写成 (B − A) 乘 A*B 的倒数。

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
-- The upper bound of 0ℝ at precision K is exactly δ K.
--
-- 零区间实数的上界
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
        -- g m - g n ≡ neg (g n - g m)：交换加项、展开负号、neg(neg x)=x。
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
