------------------------------------------------------------------------
-- Reciprocal of a non-zero interval real
--
-- 非零区间实数的倒数
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module Real.Interval.Inverse where

open import Data.Nat using
  (ℕ; _⊔_; _^_; _≥_) renaming (_≤_ to _≤ℕ_; _+_ to _+ℕ_; _*_ to _ℕ*_)
open import Data.Nat.Properties using
  (m≤m⊔n; m≤n⊔m; m≤m+n; m≤n+m)
  renaming (≤-trans to ≤ℕ-trans; ≤-refl to ≤ℕ-refl)
import Data.Nat.Properties as ℕP
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Rational using
  (ℚ; 0ℚ; 1ℚ; _+_; _-_; _*_; _<_; _≤_; ∣_∣; NonZero; Positive; NonNegative
  ; positive; nonNegative)
open import Data.Rational.Base using (1/_) renaming (-_ to neg)
open import Data.Rational.Properties using
  (≤-refl; ≤-trans; <⇒≤; ≤-<-trans; <-≤-trans; +-mono-≤; *-comm; *-assoc
  ; *-inverseʳ; *-monoˡ-≤-nonNeg; positive⁻¹; 1/pos⇒pos; pos⇒nonZero
  ; pos⇒nonNeg; 0≤∣p∣; ∣p*q∣≡∣p∣*∣q∣; 0≤p⇒∣p∣≡p; *-distribʳ-+
  ; neg-distribˡ-*; nonNeg*nonNeg⇒nonNeg; nonNeg+nonNeg⇒nonNeg;
   nonNegative⁻¹)
open import Relation.Binary.PropositionalEquality using
  (_≡_; cong; sym; module ≡-Reasoning)
open ≡-Reasoning

open import Real using (CauchySeq; embed-mono-≤; half; embed; embed-suc-pos)
open CauchySeq renaming (f to seq-f)
open import Real.Interval using (RealI)
open import Real.Interval.Arith using (0ℝ; 1ℝ; negℝ)
open import Real.Interval.Mul using (_*ℝ_)
open import Real.Interval.Equiv using (_≈ℝ_; ≈ℝ-refl; ≈ℝ-sym; ≈ℝ-trans)
open import Real.IntervalEquiv using
  (l; u; centre; width; centre-diff; bound-w; recipPow2; μx-dom)
open import Real.Interval.Order using (_<ℝ_)
open import Real.Interval.Kit using
  (0≤half; *-mono-≤-nonNeg; recipPow2-bound;
   recip-antitone; tri-diff)
open import Real.Interval.Node using (centre-1ℝ; 0≤width-n; width-rec)
open import Real.Interval.Mul.Core using (term1)
open import Real.Interval.Mul.Laws using (*ℝ-comm)
open import Real.Interval.Mul.Cong using (*ℝ-cong)
open import Real.Interval.Mul.Order using (≈-neg; negℝ-*ℝ)
open import Real.Interval.ArithLaws using (negℝ-negℝ; negℝ-0ℝ)
open import Real.Interval.OrderLaws using (≈-<-resp; <-neg)
open import Real.Interval.Recip using
  (recipℝ; recipℝ'; recipCauchy; realI→posCauchy; PosCauchy; recip-modulus
  ; embed-n≥2b²; 2n*b²≤4^n; recip-modulus-≥2n)
open import Real.CauchyToInterval using (M; K; μ≤M; centre-cauchy→realI)
open import Real.Interval.Reasoning using (begin≤_; _≈⟨_⟩_; _≤⟨_⟩_; _≤∎)
open import Real.Interval.Reasoning.Equiv

------------------------------------------------------------------------
-- Tail convergence engine
--
-- The geometric bound |centre difference| ≤ C · recipPow2 n is only
-- required eventually, for n ≥ N₀. The finite prefix does not affect
-- equivalence (same as ≈ℝ-of-rec, only relaxed to the tail).
--
-- 尾部收敛引擎
--
-- |中心差| ≤ C · recipPow2 n 仅需对 n ≥ N₀ 成立。有限前段不影响
-- 等价性（与 ≈ℝ-of-rec 相同，仅放宽为尾部）。

≈ℝ-of-recN : (x y : RealI) (N₀ : ℕ) (C : ℚ) → 0ℚ ≤ C →
  (∀ n → n ≥ N₀ → ∣ centre x n - centre y n ∣ ≤ C * recipPow2 n) →
  x ≈ℝ y
≈ℝ-of-recN x y N₀ C 0≤C h k =
  let N₁ , w = recipPow2-bound C 0≤C k
      N = N₀ ⊔ N₁
  in N , λ n n≥N →
       let n≥N₀ = ≤ℕ-trans (m≤m⊔n N₀ N₁) n≥N
           n≥N₁ = ≤ℕ-trans (m≤n⊔m N₀ N₁) n≥N
       in ≤-<-trans (h n n≥N₀) (w n n≥N₁)

------------------------------------------------------------------------
-- Setup for reciprocal theorems
--
-- 倒数定理的参数设置

module ReciprocalSetup (x : RealI) (0<x : 0ℝ <ℝ x) where

  R : RealI
  R = recipℝ x 0<x

  pc : PosCauchy
  pc = realI→posCauchy x 0<x

  cs : CauchySeq
  cs = recipCauchy pc

  n₀ : ℕ
  n₀ = proj₁ 0<x

  b : ℚ
  b = l x n₀

  δn<lxn : u 0ℝ n₀ < b
  δn<lxn = proj₂ 0<x

  0<b : 0ℚ < b
  0<b = PosCauchy.0<b pc

  b-pos : Positive b
  b-pos = positive 0<b

  b-nz : NonZero b
  b-nz = pos⇒nonZero b {{b-pos}}

  w0 : ℚ
  w0 = width x 0

  wR0 : ℚ
  wR0 = width R 0

  0≤w0 : 0ℚ ≤ w0
  0≤w0 = 0≤width-n x 0

  0≤wR0 : 0ℚ ≤ wR0
  0≤wR0 = 0≤width-n R 0

  w0-nn : NonNegative w0
  w0-nn = nonNegative 0≤w0

  wR0-nn : NonNegative wR0
  wR0-nn = nonNegative 0≤wR0

  half-nn : NonNegative half
  half-nn = nonNegative 0≤half

  invb : ℚ
  invb = (1/ b) {{b-nz}}

  invb-pos : Positive invb
  invb-pos = 1/pos⇒pos b {{b-pos}}

  invb-nn : NonNegative invb
  invb-nn = pos⇒nonNeg invb {{invb-pos}}

  w0*wR0-nn : NonNegative (w0 * wR0)
  w0*wR0-nn = nonNeg*nonNeg⇒nonNeg w0 {{w0-nn}} wR0 {{wR0-nn}}

  t1-nn : NonNegative (w0 * wR0 * half)
  t1-nn = nonNeg*nonNeg⇒nonNeg (w0 * wR0) {{w0*wR0-nn}} half {{half-nn}}

  t2-nn : NonNegative (w0 * invb)
  t2-nn = nonNeg*nonNeg⇒nonNeg w0 {{w0-nn}} invb {{invb-nn}}

  C : ℚ
  C = w0 * wR0 * half + w0 * invb

  0≤C : 0ℚ ≤ C
  0≤C = nonNegative⁻¹ C
    {{nonNeg+nonNeg⇒nonNeg (w0 * wR0 * half) {{t1-nn}}
                           (w0 * invb) {{t2-nn}}}}

  e2-pos : Positive (embed 2)
  e2-pos = embed-suc-pos

  e2-nn : NonNegative (embed 2)
  e2-nn = pos⇒nonNeg (embed 2) {{e2-pos}}

  b-nn : NonNegative b
  b-nn = pos⇒nonNeg b {{b-pos}}

  e2*b-nn : NonNegative (embed 2 * b)
  e2*b-nn = nonNeg*nonNeg⇒nonNeg (embed 2) {{e2-nn}} b {{b-nn}}

  C-aux : ℚ
  C-aux = embed 2 * b * b

  0≤C-aux : 0ℚ ≤ C-aux
  0≤C-aux = nonNegative⁻¹ C-aux
    {{nonNeg*nonNeg⇒nonNeg (embed 2 * b) {{e2*b-nn}} b {{b-nn}}}}

  N-b : ℕ
  N-b = proj₁ (bound-w C-aux 0≤C-aux)

  C-aux≤N-b : C-aux ≤ embed N-b
  C-aux≤N-b = proj₂ (bound-w C-aux 0≤C-aux)

  N : ℕ
  N = 4 ⊔ N-b

  N≥4 : N ≥ 4
  N≥4 = m≤m⊔n 4 N-b

  N≥N-b : N ≥ N-b
  N≥N-b = m≤n⊔m 4 N-b

  embed-2b²≤N : embed 2 * b * b ≤ embed N
  embed-2b²≤N =
    ≤-trans C-aux≤N-b
      (embed-mono-≤ (≤ℕ-trans N≥N-b (≤ℕ-refl {N})))

  embed-n≥2b²-inst : ∀ n → n ≥ N → embed 2 * b * b ≤ embed n
  embed-n≥2b²-inst = embed-n≥2b² b N embed-2b²≤N

  2n-inst : ∀ n → n ≥ N → embed (2 ℕ* n) * b * b ≤ embed (4 ^ n)
  2n-inst = 2n*b²≤4^n b 0<b N N≥4 embed-n≥2b²-inst

  recip-modulus-≥2n-inst :
    ∀ n → n ≥ N → recip-modulus b 0<b (K (2 ℕ* n)) ≥ 2 ℕ* n
  recip-modulus-≥2n-inst = recip-modulus-≥2n b 0<b N 2n-inst

  term1-inst :
    ∀ n →
    ∣ centre (x *ℝ R) n - centre x (2 ℕ* n) * centre R (2 ℕ* n) ∣
      ≤ (w0 * wR0 * half) * recipPow2 n
  term1-inst n = term1 x R n

  -- M cs (2n) is at least the modulus of cs at K(2n) (prefix max),
  -- and the modulus of cs is μ-h (K(2n)) = seq-μ (realI→cauchy x) r,
  -- where r = recip-modulus b 0<b (K(2n)). The carried modulus is
  -- dominated by its index (μx-dom), so seq-μ ... r ≥ r; and
  -- recip-modulus-≥2n gives r ≥ 2n. Hence M cs (2n) ≥ 2n, and
  -- adding N₀ yields j n ≥ 2n.
  --
  -- M cs (2n) 不小于 cs 在 K(2n) 处的模数（前缀最大），而 cs 的模数
  -- 为 μ-h (K(2n)) = seq-μ (realI→cauchy x) r，其中
  -- r = recip-modulus b 0<b (K(2n))。携带模数被其下标控制
  -- （μx-dom），故 seq-μ ... r ≥ r；又由 recip-modulus-≥2n 有
  -- r ≥ 2n。于是 M cs (2n) ≥ 2n，加上 N₀ 即得 j n ≥ 2n。
  j : ℕ → ℕ
  j n = PosCauchy.N₀ pc +ℕ M cs (2 ℕ* n)

  Mcs≥2n : ∀ n → n ≥ N → M cs (2 ℕ* n) ≥ 2 ℕ* n
  Mcs≥2n n n≥N =
    ≤ℕ-trans (≤ℕ-trans (recip-modulus-≥2n-inst n n≥N)
                       (μx-dom x r))
             (μ≤M cs (2 ℕ* n))
    where
      r = recip-modulus b 0<b (K (2 ℕ* n))

  j≥2n : ∀ n → n ≥ N → j n ≥ 2 ℕ* n
  j≥2n n n≥N =
    ≤ℕ-trans (Mcs≥2n n n≥N)
             (m≤n+m (M cs (2 ℕ* n)) (PosCauchy.N₀ pc))

  jn≥N₀ : ∀ n → PosCauchy.N₀ pc ≤ℕ j n
  jn≥N₀ n = m≤m+n (PosCauchy.N₀ pc) (M cs (2 ℕ* n))

  -- The centre of R at level 2n is the reciprocal of the centre of
  -- x at level j n.
  --
  -- R 第 2n 层的中心是 x 在 j n 处中心的倒数。
  centre-R-close : ∀ n → n ≥ N →
    ∣ centre R (2 ℕ* n) * centre x (2 ℕ* n) - 1ℚ ∣
      ≤ (1/ b) {{b-nz}} * width x (2 ℕ* n)
  centre-R-close n n≥N = begin≤
    ∣ centre R (2 ℕ* n) * c - 1ℚ ∣
      ≈⟨ abs-target ⟩
    ∣ c * invd - 1ℚ ∣
      ≈⟨ abs-lemma ⟩
    ∣ c - d ∣ * invd
      ≤⟨ step1 ⟩
    width x (2 ℕ* n) * invd
      ≤⟨ step2 ⟩
    width x (2 ℕ* n) * invb
      ≈⟨ *-comm (width x (2 ℕ* n)) invb ⟩
    invb * width x (2 ℕ* n)
    ≤∎
    where
      c = centre x (2 ℕ* n)
      d = centre x (j n)

      b≤d : b ≤ d
      b≤d = PosCauchy.lower pc (j n) (jn≥N₀ n)

      0<d : 0ℚ < d
      0<d = <-≤-trans 0<b b≤d

      d-pos : Positive d
      d-pos = positive 0<d

      d-nz : NonZero d
      d-nz = pos⇒nonZero d {{d-pos}}

      invd = (1/ d) {{d-nz}}

      invd-pos : Positive invd
      invd-pos = 1/pos⇒pos d {{d-pos}}

      0≤invd : 0ℚ ≤ invd
      0≤invd = <⇒≤ (positive⁻¹ invd {{invd-pos}})

      centreR≡ : centre R (2 ℕ* n) ≡ invd
      centreR≡ =
        begin
          centre R (2 ℕ* n)
            ≡⟨ centre-cauchy→realI cs (2 ℕ* n) ⟩
          seq-f cs (M cs (2 ℕ* n))
            ≡⟨⟩
          invd
        ∎

      diff≤width : ∣ c - d ∣ ≤ width x (2 ℕ* n)
      diff≤width =
        centre-diff x (2 ℕ* n) (2 ℕ* n) (j n)
                     (≤ℕ-refl {2 ℕ* n}) (j≥2n n n≥N)

      invd≤invb : invd ≤ invb
      invd≤invb = recip-antitone 0<b b≤d

      prod-minus1 : c * invd - 1ℚ ≡ (c - d) * invd
      prod-minus1 =
        begin
          c * invd - 1ℚ
            ≡⟨ cong (λ z → c * invd - z)
                   (sym (*-inverseʳ d {{d-nz}})) ⟩
          c * invd - d * invd
            ≡⟨ cong (λ z → c * invd + z) (neg-distribˡ-* d invd) ⟩
          c * invd + neg d * invd
            ≡⟨ sym (*-distribʳ-+ invd c (neg d)) ⟩
          (c + neg d) * invd
            ≡⟨⟩
          (c - d) * invd
        ∎

      abs-lemma : ∣ c * invd - 1ℚ ∣ ≡ ∣ c - d ∣ * invd
      abs-lemma =
        begin
          ∣ c * invd - 1ℚ ∣
            ≡⟨ cong ∣_∣ prod-minus1 ⟩
          ∣ (c - d) * invd ∣
            ≡⟨ ∣p*q∣≡∣p∣*∣q∣ (c - d) invd ⟩
          ∣ c - d ∣ * ∣ invd ∣
            ≡⟨ cong (∣ c - d ∣ *_) (0≤p⇒∣p∣≡p 0≤invd) ⟩
          ∣ c - d ∣ * invd
        ∎

      abs-target : ∣ centre R (2 ℕ* n) * c - 1ℚ ∣
                 ≡ ∣ c * invd - 1ℚ ∣
      abs-target =
        begin
          ∣ centre R (2 ℕ* n) * c - 1ℚ ∣
            ≡⟨ cong (λ z → ∣ z * c - 1ℚ ∣) centreR≡ ⟩
          ∣ invd * c - 1ℚ ∣
            ≡⟨ cong (λ z → ∣ z - 1ℚ ∣) (*-comm invd c) ⟩
          ∣ c * invd - 1ℚ ∣
        ∎

      step1 : ∣ c - d ∣ * invd ≤ width x (2 ℕ* n) * invd
      step1 =
        *-mono-≤-nonNeg (0≤∣p∣ (c - d)) diff≤width
                        0≤invd (≤-refl {invd})

      step2 : width x (2 ℕ* n) * invd
            ≤ width x (2 ℕ* n) * invb
      step2 =
        *-monoˡ-≤-nonNeg (width x (2 ℕ* n))
          {{nonNegative (0≤width-n x (2 ℕ* n))}} invd≤invb

  -- Combine centre-R-close with the geometric width decay
  -- width x (2n) ≤ w0 · recipPow2 n to obtain the closed-form bound
  -- for the second error term.
  --
  -- 由 centre-R-close 与几何宽度 width x (2n) ≤ w0 · recipPow2 n，
  -- 得到第二误差项的闭式界。
  term2 : ∀ n → n ≥ N →
    ∣ centre x (2 ℕ* n) * centre R (2 ℕ* n) - 1ℚ ∣
      ≤ (w0 * invb) * recipPow2 n
  term2 n n≥N = begin≤
    ∣ c * centre R (2 ℕ* n) - 1ℚ ∣
      ≈⟨ abs-comm ⟩
    ∣ centre R (2 ℕ* n) * c - 1ℚ ∣
      ≤⟨ centre-R-close n n≥N ⟩
    invb * width x (2 ℕ* n)
      ≤⟨ *-monoˡ-≤-nonNeg invb {{invb-nn}} (width-rec x n) ⟩
    invb * (w0 * r)
      ≈⟨ reorder ⟩
    (w0 * invb) * r
    ≤∎
    where
      c = centre x (2 ℕ* n)
      r = recipPow2 n

      abs-comm :
        ∣ c * centre R (2 ℕ* n) - 1ℚ ∣
        ≡ ∣ centre R (2 ℕ* n) * c - 1ℚ ∣
      abs-comm =
        cong (λ z → ∣ z - 1ℚ ∣)
             (*-comm c (centre R (2 ℕ* n)))

      reorder : invb * (w0 * r) ≡ (w0 * invb) * r
      reorder =
        begin
          invb * (w0 * r)
            ≡⟨ sym (*-assoc invb w0 r) ⟩
          (invb * w0) * r
            ≡⟨ cong (_* r) (*-comm invb w0) ⟩
          (w0 * invb) * r
        ∎

  -- Triangle inequality:
  --   centre(x*R)n − 1 = [centre(x*R)n − c·Rc] + [c·Rc − 1],
  -- where the first part is bounded by term1 with
  -- (w0·wR0·half)·recipPow2 n, and the second by term2 with
  -- (w0·invb)·recipPow2 n. Factoring out gives C · recipPow2 n.
  --
  -- 三角不等式：
  --   centre(x*R)n − 1 = [centre(x*R)n − c·Rc] + [c·Rc − 1]，
  -- 第一段由 term1 界为 (w0·wR0·half)·recipPow2 n，
  -- 第二段由 term2 界为 (w0·invb)·recipPow2 n，
  -- 提公因子即得 C · recipPow2 n。
  body : ∀ n → n ≥ N →
    ∣ centre (x *ℝ R) n - centre 1ℝ n ∣ ≤ C * recipPow2 n
  body n n≥N = begin≤
    ∣ centre (x *ℝ R) n - centre 1ℝ n ∣
      ≈⟨ cong (λ z → ∣ centre (x *ℝ R) n - z ∣) (centre-1ℝ n) ⟩
    ∣ P - 1ℚ ∣
      ≤⟨ tri-diff P Q 1ℚ ⟩
    ∣ P - Q ∣ + ∣ Q - 1ℚ ∣
      ≤⟨ +-mono-≤ (term1-inst n) (term2 n n≥N) ⟩
    t1c * r + t2c * r
      ≈⟨ sym (*-distribʳ-+ r t1c t2c) ⟩
    C * r
    ≤∎
    where
      P = centre (x *ℝ R) n
      Q = centre x (2 ℕ* n) * centre R (2 ℕ* n)
      r = recipPow2 n
      t1c = w0 * wR0 * half
      t2c = w0 * invb

------------------------------------------------------------------------
-- Main theorem
--
-- The product of a positive interval real and its reciprocal is
-- approximately one.
--
-- 主定理
--
-- 正区间实数与其倒数之积近似等于 1。

*ℝ-inverse-pos : (x : RealI) (0<x : 0ℝ <ℝ x)
               → x *ℝ recipℝ x 0<x ≈ℝ 1ℝ
*ℝ-inverse-pos x 0<x = ≈ℝ-of-recN (x *ℝ R) 1ℝ N C 0≤C body
  where
    open ReciprocalSetup x 0<x

------------------------------------------------------------------------
-- Multiplication with a negated factor
--
-- 取负因子的乘法

*ℝ-neg : (x y : RealI) → x *ℝ negℝ y ≈ℝ negℝ (x *ℝ y)
*ℝ-neg x y =
  beginℝ
    x *ℝ negℝ y
      ≈ℝ⟨ *ℝ-comm x (negℝ y) ⟩
    negℝ y *ℝ x
      ≈ℝ⟨ ≈ℝ-sym (negℝ-*ℝ y x) ⟩
    negℝ (y *ℝ x)
      ≈ℝ⟨ ≈-neg (*ℝ-comm y x) ⟩
    negℝ (x *ℝ y)
  ∎ℝ

------------------------------------------------------------------------
-- Non-zero multiplicative inverse
--
-- The product of a non-zero interval real and its reciprocal is
-- approximately one. The positive case is *ℝ-inverse-pos; the negative
-- case introduces two negations which cancel.
--
-- 非零乘法逆元
--
-- 非零区间实数与其倒数之积近似等于 1。正情形为 *ℝ-inverse-pos；
-- 负情形引入两层取负，最终相消。

*ℝ-inverse : (x : RealI) (nz : (0ℝ <ℝ x) ⊎ (x <ℝ 0ℝ))
           → x *ℝ recipℝ' x nz ≈ℝ 1ℝ
*ℝ-inverse x (inj₁ 0<x) = *ℝ-inverse-pos x 0<x
*ℝ-inverse x (inj₂ x<0) =
  let
    nx : RealI
    nx = negℝ x

    0<nx : 0ℝ <ℝ nx
    0<nx = ≈-<-resp negℝ-0ℝ (<-neg x 0ℝ x<0)

    rnx : RealI
    rnx = recipℝ nx 0<nx

    pos-inv : nx *ℝ rnx ≈ℝ 1ℝ
    pos-inv = *ℝ-inverse-pos nx 0<nx

    step1 : x *ℝ negℝ rnx ≈ℝ negℝ (x *ℝ rnx)
    step1 = *ℝ-neg x rnx

    step2 : negℝ (x *ℝ rnx) ≈ℝ negℝ (negℝ nx *ℝ rnx)
    step2 = ≈-neg (*ℝ-cong {x = x} {x' = negℝ nx} {y = rnx} {y' = rnx}
                          (≈ℝ-sym (negℝ-negℝ x)) ≈ℝ-refl)

    step3 : negℝ (negℝ nx *ℝ rnx) ≈ℝ negℝ (negℝ (nx *ℝ rnx))
    step3 = ≈-neg (≈ℝ-sym (negℝ-*ℝ nx rnx))

    step4 : negℝ (negℝ (nx *ℝ rnx)) ≈ℝ negℝ (negℝ 1ℝ)
    step4 = ≈-neg (≈-neg pos-inv)

    step5 : negℝ (negℝ 1ℝ) ≈ℝ 1ℝ
    step5 = negℝ-negℝ 1ℝ
  in
    ≈ℝ-trans step1
      (≈ℝ-trans step2
        (≈ℝ-trans step3
          (≈ℝ-trans step4 step5)))
