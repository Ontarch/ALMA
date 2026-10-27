------------------------------------------------------------------------
-- Reciprocal laws for positive and non-zero interval reals
--
-- 正区间实数与非零区间实数的倒数定律
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module Real.Interval.RecipLaws where

open import Data.Nat using (ℕ; suc; _^_; _≥_; z≤n)
  renaming (_+_ to _+N_; _*_ to _*N_; _<_ to _<N_)
open import Data.Nat.Properties using (m≤m+n; n<1+n)
  renaming (<-trans to <N-trans; ≤-<-trans to ≤N-<-trans)
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.Sum using (inj₂)
open import Data.Rational using
  (ℚ; 0ℚ; 1ℚ; _+_; _-_; _*_; _<_; _≤_; NonZero; Positive; positive)
open import Data.Rational.Base using (1/_) renaming (-_ to neg)
open import Data.Rational.Properties using
  (≤-trans; <⇒≤; ≤-<-trans; <-≤-trans; +-monoˡ-<; +-assoc; +-identityʳ
  ; +-inverseʳ; *-comm; *-assoc; *-identityˡ; *-identityʳ; *-inverseˡ; *-inverseʳ
  ; *-distribʳ-+; pos⇒nonZero; pos*pos⇒pos; positive⁻¹)
  renaming (<-trans to <-transQ)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; sym; trans; cong; cong₂; subst; module ≡-Reasoning)
open ≡-Reasoning

open import Real using
  (CauchySeq; embed; embed-*-hom; embed-mono-<; embed-suc-pos; reciprocal-cong)
open CauchySeq renaming (f to seq-f)
open import Real.Interval using (RealI; δ; δ-pos)
open import Real.Interval.Arith using (0ℝ; 1ℝ; negℝ)
open import Real.Interval.Mul using (_*ℝ_)
open import Real.Interval.Equiv using (_≈ℝ_; ≈ℝ-refl; ≈ℝ-sym; ≈ℝ-trans)
open import Real.IntervalEquiv using
  (l; u; centre; centre-u; u-mono; bound-w; n<2^n; realI→cauchy; node)
open import Real.Interval.Order using (_<ℝ_; <-irrefl)
open import Real.Interval.OrderComplete.Base using (_≤ℝ_)
open import Real.Interval.Mul.Laws using
  (*ℝ-comm; *ℝ-assoc; *ℝ-identityˡ; *ℝ-identityʳ)
open import Real.Interval.Mul.Cong using (*ℝ-cong)
open import Real.Interval.Mul.Order using (pos*pos; <-*mono; ≈-<-respʳ)
open import Real.Interval.ArithLaws using (negℝ-0ℝ)
open import Real.Interval.Inverse using (*ℝ-inverse-pos)
open import Real.Interval.Embed using (0ℝ<ℝ1ℝ)
open import Real.Interval.Recip using
  (recipℝ; recipℝ'; recipCauchy; realI→posCauchy; PosCauchy; u-0ℝ)
open import Real.CauchyToInterval using
  (cauchy→realI; M; node-go; recip-strict)
open import Real.Interval.Kit using (recip-antitone)
open import Real.Interval.OrderLaws using (≈-<-resp; <-neg)
open import Real.Interval.Reasoning.Equiv

------------------------------------------------------------------------
-- Rational arithmetic helpers
--
-- 有理数算术辅助

-- Doubling as a sum.
--
-- 二倍写法。
2q≡q+q : (q : ℚ) → embed 2 * q ≡ q + q
2q≡q+q q =
  begin
    embed 2 * q
      ≡⟨⟩
    (1ℚ + 1ℚ) * q
      ≡⟨ *-distribʳ-+ q 1ℚ 1ℚ ⟩
    1ℚ * q + 1ℚ * q
      ≡⟨ cong₂ _+_ (*-identityˡ q) (*-identityˡ q) ⟩
    q + q
  ∎

-- Move an additive term to the other side of a strict inequality.
--
-- 移项消去左侧加项。
add-cancel-< : {a b c : ℚ} → a + b < c → a < c - b
add-cancel-< {a} {b} {c} s =
  subst (λ z → z < c - b) (sym prefix) (+-monoˡ-< (neg b) s)
  where
  prefix : a ≡ (a + b) + neg b
  prefix =
    begin
      a
        ≡⟨ sym (+-identityʳ a) ⟩
      a + 0ℚ
        ≡⟨ cong (a +_) (sym (+-inverseʳ b)) ⟩
      a + (b + neg b)
        ≡⟨ sym (+-assoc a b (neg b)) ⟩
      (a + b) + neg b
    ∎

-- Left cancellation of a positive factor.
--
-- 正因子的左消去。
cancel-* : {c x y : ℚ} → (nz : NonZero c) → 0ℚ < c → c * x ≡ c * y → x ≡ y
cancel-* {c} {x} {y} nz 0<c eq =
  let ic : ℚ
      ic = (1/_) c {{nz}}
  in
  begin
    x
      ≡⟨ sym (*-identityˡ x) ⟩
    1ℚ * x
      ≡⟨ sym (cong (_* x) (*-inverseˡ c {{nz}})) ⟩
    ic * c * x
      ≡⟨ *-assoc ic c x ⟩
    ic * (c * x)
      ≡⟨ cong (ic *_) eq ⟩
    ic * (c * y)
      ≡⟨ sym (*-assoc ic c y) ⟩
    (ic * c) * y
      ≡⟨ cong (_* y) (*-inverseˡ c {{nz}}) ⟩
    1ℚ * y
      ≡⟨ *-identityˡ y ⟩
    y
  ∎

-- The doubling identity for powers of two.
--
-- 二的幂的倍增关系。
2*2^n≡ : ∀ n → 2 *N 2 ^ n ≡ 2 ^ suc n
2*2^n≡ n = refl

-- Reciprocal of a product splits into the product of reciprocals.
--
-- 乘积的倒数分配。
recip-mul : (A B : ℚ) (pA : Positive A) (pB : Positive B)
  (nzA : NonZero A) (nzB : NonZero B) (nzAB : NonZero (A * B))
  → (1/_) (A * B) {{nzAB}} ≡ (1/_) A {{nzA}} * (1/_) B {{nzB}}
recip-mul A B pA pB nzA nzB nzAB = cancel-* nzAB 0<AB eq
  where

  pAB : Positive (A * B)
  pAB = pos*pos⇒pos A {{pA}} B {{pB}}

  0<AB : 0ℚ < A * B
  0<AB = positive⁻¹ (A * B) {{pAB}}

  iA : ℚ
  iA = (1/_) A {{nzA}}

  iB : ℚ
  iB = (1/_) B {{nzB}}

  step : (A * B) * iA ≡ B
  step =
    begin
      (A * B) * iA
        ≡⟨ cong (_* iA) (*-comm A B) ⟩
      (B * A) * iA
        ≡⟨ *-assoc B A iA ⟩
      B * (A * iA)
        ≡⟨ cong (B *_) (*-inverseʳ A {{nzA}}) ⟩
      B * 1ℚ
        ≡⟨ *-identityʳ B ⟩
      B
    ∎

  rhs : (A * B) * (iA * iB) ≡ 1ℚ
  rhs =
    begin
      (A * B) * (iA * iB)
        ≡⟨ sym (*-assoc (A * B) iA iB) ⟩
      ((A * B) * iA) * iB
        ≡⟨ cong (_* iB) step ⟩
      B * iB
        ≡⟨ *-inverseʳ B {{nzB}} ⟩
      1ℚ
    ∎

  lhs : (A * B) * (1/_) (A * B) {{nzAB}} ≡ 1ℚ
  lhs = *-inverseʳ (A * B) {{nzAB}}

  eq : (A * B) * (1/_) (A * B) {{nzAB}} ≡ (A * B) * (iA * iB)
  eq = trans lhs (sym rhs)

------------------------------------------------------------------------
-- Sign preservation: 0 < recipℝ x
--
-- The reciprocal Cauchy sequence has terms h k = 1 / g k, with g k
-- bounded above by U = u x 0 and below by b > 0. Hence h k ≥ 1 / U.
-- Choosing n with 2 · δ n < 1 / U gives h (M cs n) - δ n > δ n.
--
-- 保号性
--
-- 倒数 Cauchy 序列的项以某个正有理数为下界、以上界 U 为上界，
-- 故其倒数项不小于 1/U。选取足够深的层级使两倍二进容差低于 1/U，
-- 即得该层下端点严格为正。

module RecipPosAux (x : RealI) (0<x : 0ℝ <ℝ x) where

  pc : PosCauchy
  pc = realI→posCauchy x 0<x

  cs : CauchySeq
  cs = recipCauchy pc

  N₀ : ℕ
  N₀ = PosCauchy.N₀ pc

  b : ℚ
  b = PosCauchy.b pc

  0<b : 0ℚ < b
  0<b = PosCauchy.0<b pc

  low : ∀ n → n ≥ N₀ → b ≤ seq-f (realI→cauchy x) n
  low = PosCauchy.lower pc

  g : ℕ → ℚ
  g k = centre x (N₀ +N k)

  0<g : ∀ k → 0ℚ < g k
  0<g k = <-≤-trans 0<b (low (N₀ +N k) (m≤m+n N₀ k))

  g-nz : ∀ k → NonZero (g k)
  g-nz k = pos⇒nonZero (g k) {{positive (0<g k)}}

  h≡ : ∀ k → seq-f cs k ≡ (1/_) (g k) {{g-nz k}}
  h≡ k = refl

  g≤U : ∀ k → g k ≤ u x 0
  g≤U k =
    ≤-trans (centre-u x (N₀ +N k))
            (u-mono x (z≤n {N₀ +N k}))

  U : ℚ
  U = u x 0

  n₀ : ℕ
  n₀ = proj₁ 0<x

  δn₀<l : δ n₀ < l x n₀
  δn₀<l = subst (λ z → z < l x n₀) (u-0ℝ n₀) (proj₂ 0<x)

  l≤U : l x n₀ ≤ u x 0
  l≤U = ≤-trans (<⇒≤ (RealI.lo (node x n₀)))
                (u-mono x (z≤n {n₀}))

  0<U : 0ℚ < U
  0<U = <-transQ (δ-pos n₀) (<-≤-trans δn₀<l l≤U)

  U-nz : NonZero U
  U-nz = pos⇒nonZero U {{positive 0<U}}

  iU : ℚ
  iU = (1/_) U {{U-nz}}

  h≥ : ∀ k → iU ≤ seq-f cs k
  h≥ k =
    subst (λ z → iU ≤ z) (sym (h≡ k))
      (recip-antitone (0<g k) (g≤U k))

  Mw : ℕ
  Mw = proj₁ (bound-w U (<⇒≤ 0<U))

  U≤eMw : U ≤ embed Mw
  U≤eMw = proj₂ (bound-w U (<⇒≤ 0<U))

  n : ℕ
  n = suc Mw

  A : ℚ
  A = embed 2

  B : ℚ
  B = embed (2 ^ n)

  A-pos : Positive A
  A-pos = embed-suc-pos

  B-pos : Positive B
  B-pos = positive (embed-mono-< (≤N-<-trans z≤n (n<2^n n)))

  nzA : NonZero A
  nzA = pos⇒nonZero A {{A-pos}}

  nzB : NonZero B
  nzB = pos⇒nonZero B {{B-pos}}

  nzAB : NonZero (A * B)
  nzAB = pos⇒nonZero (A * B)
           {{pos*pos⇒pos A {{A-pos}} B {{B-pos}}}}

  nzE : NonZero (embed (2 ^ suc n))
  nzE = pos⇒nonZero (embed (2 ^ suc n))
    {{positive (embed-mono-< (≤N-<-trans z≤n (n<2^n (suc n))))}}

  iE : ℚ
  iE = (1/_) (embed (2 ^ suc n)) {{nzE}}

  iAB : ℚ
  iAB = (1/_) (A * B) {{nzAB}}

  iA : ℚ
  iA = (1/_) A {{nzA}}

  iB : ℚ
  iB = (1/_) B {{nzB}}

  Mw<2^n : Mw <N 2 ^ n
  Mw<2^n = <N-trans (n<1+n Mw) (n<2^n n)

  U<e2n : U < embed (2 ^ n)
  U<e2n = ≤-<-trans U≤eMw (embed-mono-< Mw<2^n)

  inv< : iB < iU
  inv< = recip-strict 0<U U<e2n

  den-eq : embed (2 ^ suc n) ≡ A * B
  den-eq = trans (cong embed (sym (2*2^n≡ n))) (embed-*-hom 2 (2 ^ n))

  rec-step : iE ≡ iAB
  rec-step = reciprocal-cong (embed (2 ^ suc n)) (A * B) {{nzE}} {{nzAB}} den-eq

  2δ≡ : A * δ n ≡ iB
  2δ≡ =
    begin
      A * δ n
        ≡⟨⟩
      A * iE
        ≡⟨ cong (A *_) rec-step ⟩
      A * iAB
        ≡⟨ cong (A *_) (recip-mul A B A-pos B-pos nzA nzB nzAB) ⟩
      A * (iA * iB)
        ≡⟨ sym (*-assoc A iA iB) ⟩
      (A * iA) * iB
        ≡⟨ cong (_* iB) (*-inverseʳ A {{nzA}}) ⟩
      1ℚ * iB
        ≡⟨ *-identityˡ iB ⟩
      iB
    ∎

  2δ< : embed 2 * δ n < iU
  2δ< = subst (λ z → z < iU) (sym 2δ≡) inv<

  hn≥ : iU ≤ seq-f cs (M cs n)
  hn≥ = h≥ (M cs n)

  lR≡ : l (cauchy→realI cs) n ≡ seq-f cs (M cs n) - δ n
  lR≡ = cong RealI.l (node-go cs n)

  δn<lR : δ n < seq-f cs (M cs n) - δ n
  δn<lR =
    add-cancel-<
      (subst (λ z → z < seq-f cs (M cs n))
             (2q≡q+q (δ n))
             (<-≤-trans 2δ< hn≥))

  goal : u 0ℝ n < l (cauchy→realI cs) n
  goal =
    subst (λ z → z < l (cauchy→realI cs) n)
          (sym (u-0ℝ n))
          (subst (λ z → δ n < z) (sym lR≡) δn<lR)

-- Sign preservation.
--
-- 保号性。
recipℝ-pos : (x : RealI) (0<x : 0ℝ <ℝ x) →
  0ℝ <ℝ recipℝ x 0<x
recipℝ-pos x 0<x =
  let n = RecipPosAux.n x 0<x
  in n , RecipPosAux.goal x 0<x

------------------------------------------------------------------------
-- Reciprocal involution
--
-- 倒数对合

recipℝ-invol : (x : RealI) (0<x : 0ℝ <ℝ x) →
  recipℝ (recipℝ x 0<x) (recipℝ-pos x 0<x) ≈ℝ x
recipℝ-invol x 0<x =
  let R : RealI
      R = recipℝ x 0<x
      0<R : 0ℝ <ℝ R
      0<R = recipℝ-pos x 0<x
      R' : RealI
      R' = recipℝ R 0<R
      R*x≈1 : R *ℝ x ≈ℝ 1ℝ
      R*x≈1 = ≈ℝ-trans (*ℝ-comm R x) (*ℝ-inverse-pos x 0<x)
  in
  beginℝ
    R'
      ≈ℝ⟨ ≈ℝ-sym (*ℝ-identityʳ R') ⟩
    R' *ℝ 1ℝ
      ≈ℝ⟨ *ℝ-cong ≈ℝ-refl (≈ℝ-sym R*x≈1) ⟩
    R' *ℝ (R *ℝ x)
      ≈ℝ⟨ ≈ℝ-sym (*ℝ-assoc R' R x) ⟩
    (R' *ℝ R) *ℝ x
      ≈ℝ⟨ *ℝ-cong (≈ℝ-sym (*ℝ-comm R R')) ≈ℝ-refl ⟩
    (R *ℝ R') *ℝ x
      ≈ℝ⟨ *ℝ-cong (*ℝ-inverse-pos R 0<R) ≈ℝ-refl ⟩
    1ℝ *ℝ x
      ≈ℝ⟨ *ℝ-identityˡ x ⟩
    x
  ∎ℝ

------------------------------------------------------------------------
-- Congruence of the reciprocal
--
-- 倒数的合同性

recipℝ-cong : (x y : RealI) (0<x : 0ℝ <ℝ x) (0<y : 0ℝ <ℝ y) →
  x ≈ℝ y → recipℝ x 0<x ≈ℝ recipℝ y 0<y
recipℝ-cong x y 0<x 0<y x≈y =
  let Rx : RealI
      Rx = recipℝ x 0<x
      Ry : RealI
      Ry = recipℝ y 0<y
      y*Ry≈1 : y *ℝ Ry ≈ℝ 1ℝ
      y*Ry≈1 = *ℝ-inverse-pos y 0<y
      Rx*x≈1 : Rx *ℝ x ≈ℝ 1ℝ
      Rx*x≈1 = ≈ℝ-trans (*ℝ-comm Rx x) (*ℝ-inverse-pos x 0<x)
  in
  beginℝ
    Rx
      ≈ℝ⟨ ≈ℝ-sym (*ℝ-identityʳ Rx) ⟩
    Rx *ℝ 1ℝ
      ≈ℝ⟨ *ℝ-cong ≈ℝ-refl (≈ℝ-sym y*Ry≈1) ⟩
    Rx *ℝ (y *ℝ Ry)
      ≈ℝ⟨ ≈ℝ-sym (*ℝ-assoc Rx y Ry) ⟩
    (Rx *ℝ y) *ℝ Ry
      ≈ℝ⟨ *ℝ-cong (*ℝ-cong ≈ℝ-refl (≈ℝ-sym x≈y)) ≈ℝ-refl ⟩
    (Rx *ℝ x) *ℝ Ry
      ≈ℝ⟨ *ℝ-cong Rx*x≈1 ≈ℝ-refl ⟩
    1ℝ *ℝ Ry
      ≈ℝ⟨ *ℝ-identityˡ Ry ⟩
    Ry
  ∎ℝ

------------------------------------------------------------------------
-- Multiplicativity of the reciprocal
--
-- 倒数的乘性

recipℝ-mul : (x y : RealI) (0<x : 0ℝ <ℝ x) (0<y : 0ℝ <ℝ y) →
  recipℝ (x *ℝ y) (pos*pos x y 0<x 0<y) ≈ℝ
  recipℝ x 0<x *ℝ recipℝ y 0<y
recipℝ-mul x y 0<x 0<y =
  let Rx : RealI
      Rx = recipℝ x 0<x
      Ry : RealI
      Ry = recipℝ y 0<y
      P : RealI
      P = Rx *ℝ Ry
      0<xy : 0ℝ <ℝ x *ℝ y
      0<xy = pos*pos x y 0<x 0<y
      Q : RealI
      Q = recipℝ (x *ℝ y) 0<xy
      xy*Q≈1 : (x *ℝ y) *ℝ Q ≈ℝ 1ℝ
      xy*Q≈1 = *ℝ-inverse-pos (x *ℝ y) 0<xy
      P*inv≈1 : (x *ℝ y) *ℝ P ≈ℝ 1ℝ
      P*inv≈1 =
        beginℝ
          (x *ℝ y) *ℝ (Rx *ℝ Ry)
            ≈ℝ⟨ ≈ℝ-sym (*ℝ-assoc (x *ℝ y) Rx Ry) ⟩
          ((x *ℝ y) *ℝ Rx) *ℝ Ry
            ≈ℝ⟨ *ℝ-cong (*ℝ-assoc x y Rx) ≈ℝ-refl ⟩
          (x *ℝ (y *ℝ Rx)) *ℝ Ry
            ≈ℝ⟨ *ℝ-cong (*ℝ-cong ≈ℝ-refl (*ℝ-comm y Rx)) ≈ℝ-refl ⟩
          (x *ℝ (Rx *ℝ y)) *ℝ Ry
            ≈ℝ⟨ *ℝ-cong (≈ℝ-sym (*ℝ-assoc x Rx y)) ≈ℝ-refl ⟩
          ((x *ℝ Rx) *ℝ y) *ℝ Ry
            ≈ℝ⟨ *ℝ-assoc (x *ℝ Rx) y Ry ⟩
          (x *ℝ Rx) *ℝ (y *ℝ Ry)
            ≈ℝ⟨ *ℝ-cong (*ℝ-inverse-pos x 0<x) (*ℝ-inverse-pos y 0<y) ⟩
          1ℝ *ℝ 1ℝ
            ≈ℝ⟨ *ℝ-identityˡ 1ℝ ⟩
          1ℝ
        ∎ℝ
  in
  beginℝ
    Q
      ≈ℝ⟨ ≈ℝ-sym (*ℝ-identityʳ Q) ⟩
    Q *ℝ 1ℝ
      ≈ℝ⟨ *ℝ-cong ≈ℝ-refl (≈ℝ-sym P*inv≈1) ⟩
    Q *ℝ ((x *ℝ y) *ℝ P)
      ≈ℝ⟨ ≈ℝ-sym (*ℝ-assoc Q (x *ℝ y) P) ⟩
    (Q *ℝ (x *ℝ y)) *ℝ P
      ≈ℝ⟨ *ℝ-cong (*ℝ-comm Q (x *ℝ y)) ≈ℝ-refl ⟩
    ((x *ℝ y) *ℝ Q) *ℝ P
      ≈ℝ⟨ *ℝ-cong xy*Q≈1 ≈ℝ-refl ⟩
    1ℝ *ℝ P
      ≈ℝ⟨ *ℝ-identityˡ P ⟩
    P
  ∎ℝ

------------------------------------------------------------------------
-- Reciprocal of one and non-vanishing
--
-- 一的倒数与非零性

recipℝ-1 : recipℝ 1ℝ 0ℝ<ℝ1ℝ ≈ℝ 1ℝ
recipℝ-1 =
  beginℝ
    R1
      ≈ℝ⟨ ≈ℝ-sym (*ℝ-identityˡ R1) ⟩
    1ℝ *ℝ R1
      ≈ℝ⟨ *ℝ-inverse-pos 1ℝ 0ℝ<ℝ1ℝ ⟩
    1ℝ
  ∎ℝ
  where
  R1 : RealI
  R1 = recipℝ 1ℝ 0ℝ<ℝ1ℝ

-- The reciprocal of a positive real is never equal to zero.
--
-- 正实数的倒数不可能等于零。
recipℝ-nonzero : (x : RealI) (0<x : 0ℝ <ℝ x) →
  ¬ (recipℝ x 0<x ≈ℝ 0ℝ)
recipℝ-nonzero x 0<x R≈0 =
  <-irrefl 0ℝ (≈-<-respʳ R≈0 (recipℝ-pos x 0<x))

------------------------------------------------------------------------
-- Sign law for the signed reciprocal on a negative input
--
-- 带符号倒数在负输入上的符号律

recipℝ'-neg : (x : RealI) (x<0 : x <ℝ 0ℝ) →
  recipℝ' x (inj₂ x<0) ≈ℝ
  negℝ (recipℝ (negℝ x) (≈-<-resp negℝ-0ℝ (<-neg x 0ℝ x<0)))
recipℝ'-neg x x<0 = ≈ℝ-refl

------------------------------------------------------------------------
-- Cancelling a positive factor from a strict order
--
-- 从严格序中消去正因子

<-*cancel : (x y z : RealI) (0<z : 0ℝ <ℝ z) →
  x *ℝ z <ℝ y *ℝ z → x <ℝ y
<-*cancel x y z 0<z h =
  let Rz : RealI
      Rz = recipℝ z 0<z
      0<Rz : 0ℝ <ℝ Rz
      0<Rz = recipℝ-pos z 0<z
      z*Rz≈1 : z *ℝ Rz ≈ℝ 1ℝ
      z*Rz≈1 = *ℝ-inverse-pos z 0<z
      left≈ : (x *ℝ z) *ℝ Rz ≈ℝ x
      left≈ =
        beginℝ
          (x *ℝ z) *ℝ Rz
            ≈ℝ⟨ *ℝ-assoc x z Rz ⟩
          x *ℝ (z *ℝ Rz)
            ≈ℝ⟨ *ℝ-cong ≈ℝ-refl z*Rz≈1 ⟩
          x *ℝ 1ℝ
            ≈ℝ⟨ *ℝ-identityʳ x ⟩
          x
        ∎ℝ
      right≈ : (y *ℝ z) *ℝ Rz ≈ℝ y
      right≈ =
        beginℝ
          (y *ℝ z) *ℝ Rz
            ≈ℝ⟨ *ℝ-assoc y z Rz ⟩
          y *ℝ (z *ℝ Rz)
            ≈ℝ⟨ *ℝ-cong ≈ℝ-refl z*Rz≈1 ⟩
          y *ℝ 1ℝ
            ≈ℝ⟨ *ℝ-identityʳ y ⟩
          y
        ∎ℝ
  in
  ≈-<-respʳ right≈
    (≈-<-resp left≈ (<-*mono (x *ℝ z) (y *ℝ z) Rz h 0<Rz))

------------------------------------------------------------------------
-- Multiplicative monotonicity of _≤ℝ_
--
-- _≤ℝ_ 的乘法单调性

≤ℝ-*-mono : {x y z : RealI} → x ≤ℝ y → 0ℝ <ℝ z →
  x *ℝ z ≤ℝ y *ℝ z
≤ℝ-*-mono {x} {y} {z} x≤y 0<z y*z<x*z =
  x≤y (<-*cancel y x z 0<z y*z<x*z)
