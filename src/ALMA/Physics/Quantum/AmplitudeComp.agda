------------------------------------------------------------------------
-- L2 amplitude composition
--
-- A complex unitary conserves total norm. Composing two amplitude
-- instruments sums amplitudes (not weights), so interference appears.
-- The primitive recombination is a 2×2 unitary with complex entries
--
--     U = [[ u, v ], [ -conj v, conj u ]],      |u|² + |v|² = 1,
--
-- acting on a two-level state (α, β). The module proves, over ℚ[i],
--
--     |uα + vβ|² + |(-conj v)α + (conj u)β|² = |α|² + |β|².
--
-- The diagonal terms carry the factor |u|² + |v|² = 1; the two
-- interference (cross) terms are exact opposites and cancel by the
-- commutative-ring and conjugation laws alone, with no 8-variable
-- expansion. Orthogonality is again a carried hypothesis.
--
-- L2 振幅复合
--
-- 复幺正保持总范数。复合两个振幅仪器是对振幅（而非权重）求和，故
-- 出现干涉。其基本重组是带复元素的 2×2 幺正
--
--     U = [[ u, v ], [ -conj v, conj u ]]，     |u|² + |v|² = 1，
--
-- 作用于二能级态 (α, β)。本模块在 ℚ[i] 上证明
--
--     |uα + vβ|² + |(-conj v)α + (conj u)β|² = |α|² + |β|²。
--
-- 对角项带上因子 |u|² + |v|² = 1；两个干涉（交叉）项互为相反数，仅凭
-- 交换环与共轭律相消——无需 8 变量展开。正交仍是携带假设。
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module ALMA.Physics.Quantum.AmplitudeComp where

open import Data.Rational using (ℚ; 0ℚ; 1ℚ; _+_; _*_; _-_; -_; _/_)
open import Data.Rational.Properties using
  (+-assoc; +-comm; +-identityʳ; +-inverseʳ; *-assoc; *-comm; *-identityˡ
  ; *-distribˡ-+; *-distribʳ-+; neg-distrib-+; neg-distribˡ-*; neg-distribʳ-*)
open import Data.Integer.Base using (ℤ; 1ℤ) renaming (_+_ to _ℤ+_)
open import Data.Product.Base using (_,_)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; sym; trans; cong; cong₂; module ≡-Reasoning)

open import ALMA.Physics.Quantum.Gaussian using
  (ℂ; re; conj; norm²; _+ᶜ_; _*ᶜ_; norm²-mul; norm²-conj)
open import ALMA.Physics.RationalKit using
  (neg-involutive; neg-neg-mul; sq+; +interchange; flat4; sub-+-assoc; *ʳ-sub; *ˡ-sub)

-- Additive inverse on ℚ[i], componentwise.
--
-- ℚ[i] 的加法逆元，逐分量取负。
-ᶜ_ : ℂ → ℂ
-ᶜ_ (a , b) = (- a , - b)

------------------------------------------------------------------------
-- Local helpers not in RationalKit
--
-- perm4 and gather-t have four-term shapes specific to the complex
-- multiplication tables below, so they stay local.
--
-- RationalKit 之外的本地辅助引理
--
-- perm4 与 gather-t 是为下面复数乘法表量身定做的四项形状，故留在本地。

private
  -- Rotate the last three addends: a + b + c + d = a + c + d + b.
  --
  -- 末三项轮换：a + b + c + d = a + c + d + b。
  perm4 : ∀ a b c d → a + (b + (c + d)) ≡ a + (c + (d + b))
  perm4 a b c d = let open ≡-Reasoning in begin
    a + (b + (c + d))
    ≡⟨ sym (+-assoc a b (c + d)) ⟩
    (a + b) + (c + d)
    ≡⟨ +interchange a b c d ⟩
    (a + c) + (b + d)
    ≡⟨ cong ((a + c) +_) (+-comm b d) ⟩
    (a + c) + (d + b)
    ≡⟨ +-assoc a c (d + b) ⟩
    a + (c + (d + b)) ∎

  -- Cancel opposite copies of t carried by two pairs, then interchange.
  --
  -- 消去两对中一正一负的 t，再交换收拢。
  gather-t : ∀ P Q R S t →
             ((P + Q) + t) + ((R + S) + (- t)) ≡ (P + R) + (Q + S)
  gather-t P Q R S t = let open ≡-Reasoning in begin
    ((P + Q) + t) + ((R + S) + (- t))
    ≡⟨ +interchange (P + Q) t (R + S) (- t) ⟩
    ((P + Q) + (R + S)) + (t + (- t))
    ≡⟨ cong (((P + Q) + (R + S)) +_) (+-inverseʳ t) ⟩
    ((P + Q) + (R + S)) + 0ℚ
    ≡⟨ +-identityʳ ((P + Q) + (R + S)) ⟩
    (P + Q) + (R + S)
    ≡⟨ +interchange P Q R S ⟩
    (P + R) + (Q + S) ∎

------------------------------------------------------------------------
-- ℚ[i] is a commutative ring
--
-- The laws used to reorder amplitude products abstractly.
--
-- ℚ[i] 是交换环
--
-- 用于抽象重排振幅乘积的环律。

private
  *ᶜ-comm : ∀ x y → x *ᶜ y ≡ y *ᶜ x
  *ᶜ-comm (a , b) (c , d) = cong₂ _,_ real imag
    where
    real = let open ≡-Reasoning in begin
      a * c - b * d
      ≡⟨ cong₂ _-_ (*-comm a c) (*-comm b d) ⟩
      c * a - d * b ∎
    imag = let open ≡-Reasoning in begin
      a * d + b * c
      ≡⟨ cong₂ _+_ (*-comm a d) (*-comm b c) ⟩
      d * a + c * b
      ≡⟨ +-comm (d * a) (c * b) ⟩
      c * b + d * a ∎

  *ᶜ-assoc : ∀ x y z → (x *ᶜ y) *ᶜ z ≡ x *ᶜ (y *ᶜ z)
  *ᶜ-assoc (a , b) (c , d) (e , f) = cong₂ _,_ real imag
    where
    -- Four signed monomials of the real part, permuted between the two
    -- parenthesisations.
    --
    -- 实部的四个带符号单项式，在两种括号化间仅作排列。
    r1 = (a * c) * e ; r2 = - ((b * d) * e)
    r3 = - ((a * d) * f) ; r4 = - ((b * c) * f)

    realR : a * (c * e - d * f) - b * (c * f + d * e)
          ≡ r1 + (r3 + (r4 + r2))
    realR = let open ≡-Reasoning in begin
      a * (c * e - d * f) - b * (c * f + d * e)
      ≡⟨ cong₂ _-_ (*ˡ-sub a (c * e) (d * f))
                    (*-distribˡ-+ b (c * f) (d * e)) ⟩
      (a * (c * e) - a * (d * f)) - (b * (c * f) + b * (d * e))
      ≡⟨ sub-+-assoc (a * (c * e) - a * (d * f)) (b * (c * f))
                                                      (b * (d * e)) ⟩
      ((a * (c * e) - a * (d * f)) - b * (c * f)) - b * (d * e)
      ≡⟨ flat4 (a * (c * e)) (- (a * (d * f))) (- (b * (c * f)))
                              (- (b * (d * e))) ⟩
      a * (c * e) + (- (a * (d * f))
                   + (- (b * (c * f)) + - (b * (d * e))))
      ≡⟨ cong₂ _+_ (sym (*-assoc a c e))
            (cong₂ _+_ (cong -_ (sym (*-assoc a d f)))
              (cong₂ _+_ (cong -_ (sym (*-assoc b c f)))
                         (cong -_ (sym (*-assoc b d e))))) ⟩
      r1 + (r3 + (r4 + r2)) ∎

    real = let open ≡-Reasoning in begin
      (a * c - b * d) * e - (a * d + b * c) * f
      ≡⟨ cong₂ _-_ (*ʳ-sub (a * c) (b * d) e)
                    (*-distribʳ-+ f (a * d) (b * c)) ⟩
      ((a * c) * e - (b * d) * e) - ((a * d) * f + (b * c) * f)
      ≡⟨ sub-+-assoc ((a * c) * e - (b * d) * e) ((a * d) * f)
                                                     ((b * c) * f) ⟩
      (((a * c) * e - (b * d) * e) - (a * d) * f) - (b * c) * f
      ≡⟨ flat4 r1 r2 r3 r4 ⟩
      r1 + (r2 + (r3 + r4))
      ≡⟨ perm4 r1 r2 r3 r4 ⟩
      r1 + (r3 + (r4 + r2))
      ≡⟨ sym realR ⟩
      a * (c * e - d * f) - b * (c * f + d * e) ∎

    -- Imaginary part: same permutation, four monomials.
    --
    -- 虚部：四个单项式的同一排列。
    t1 = (a * c) * f ; t2 = - ((b * d) * f)
    t3 = (a * d) * e ; t4 = (b * c) * e

    imagR : a * (c * f + d * e) + b * (c * e - d * f)
          ≡ t1 + (t3 + (t4 + t2))
    imagR = let open ≡-Reasoning in begin
      a * (c * f + d * e) + b * (c * e - d * f)
      ≡⟨ cong₂ _+_ (*-distribˡ-+ a (c * f) (d * e))
                    (*ˡ-sub b (c * e) (d * f)) ⟩
      (a * (c * f) + a * (d * e)) + (b * (c * e) - b * (d * f))
      ≡⟨ cong₂ _+_
            (cong₂ _+_ (sym (*-assoc a c f)) (sym (*-assoc a d e)))
            (cong₂ _+_ (sym (*-assoc b c e))
                       (cong -_ (sym (*-assoc b d f)))) ⟩
      (t1 + t3) + (t4 + t2)
      ≡⟨ sym (+-assoc (t1 + t3) t4 t2) ⟩
      ((t1 + t3) + t4) + t2
      ≡⟨ flat4 t1 t3 t4 t2 ⟩
      t1 + (t3 + (t4 + t2)) ∎

    imag = let open ≡-Reasoning in begin
      (a * c - b * d) * f + (a * d + b * c) * e
      ≡⟨ cong₂ _+_ (*ʳ-sub (a * c) (b * d) f)
                    (*-distribʳ-+ e (a * d) (b * c)) ⟩
      ((a * c) * f - (b * d) * f) + ((a * d) * e + (b * c) * e)
      ≡⟨ sym (+-assoc ((a * c) * f - (b * d) * f) ((a * d) * e)
                                                      ((b * c) * e)) ⟩
      (((a * c) * f - (b * d) * f) + (a * d) * e) + (b * c) * e
      ≡⟨ flat4 t1 t2 t3 t4 ⟩
      t1 + (t2 + (t3 + t4))
      ≡⟨ perm4 t1 t2 t3 t4 ⟩
      t1 + (t3 + (t4 + t2))
      ≡⟨ sym imagR ⟩
      a * (c * f + d * e) + b * (c * e - d * f) ∎

  -- Conjugation is an involution and preserves products: ℚ[i] is
  -- commutative, so conj(xy) = conj x · conj y.
  --
  -- 共轭为对合且保持乘积：ℚ[i] 交换，故 conj(xy) = conj x · conj y。
  conj-invol : ∀ z → conj (conj z) ≡ z
  conj-invol (a , b) = cong (a ,_) (neg-involutive b)

  conj-neg : ∀ z → conj (-ᶜ z) ≡ -ᶜ conj z
  conj-neg (a , b) = refl

  conj-mul : ∀ x y → conj (x *ᶜ y) ≡ conj x *ᶜ conj y
  conj-mul (a , b) (c , d) = cong₂ _,_ (sym real) (sym imag)
    where
    real = let open ≡-Reasoning in begin
      a * c - (- b) * (- d)
      ≡⟨ cong (λ z → a * c - z) (let open ≡-Reasoning in begin
        (- b) * (- d)
        ≡⟨ sym (neg-distribˡ-* b (- d)) ⟩
        - (b * (- d))
        ≡⟨ cong -_ (sym (neg-distribʳ-* b d)) ⟩
        - (- (b * d))
        ≡⟨ neg-involutive (b * d) ⟩
        b * d ∎) ⟩
      a * c - b * d ∎
    imag = let open ≡-Reasoning in begin
      a * (- d) + (- b) * c
      ≡⟨ cong₂ _+_ (sym (neg-distribʳ-* a d))
                    (sym (neg-distribˡ-* b c)) ⟩
      - (a * d) + - (b * c)
      ≡⟨ sym (neg-distrib-+ (a * d) (b * c)) ⟩
      - (a * d + b * c) ∎

  -- Negation through multiplication, on either side.
  --
  -- 取负穿过乘法的两侧恒等式。
  neg-mulˡ : ∀ x y → (-ᶜ x) *ᶜ y ≡ -ᶜ (x *ᶜ y)
  neg-mulˡ (a , b) (c , d) = cong₂ _,_ real imag
    where
    real = let open ≡-Reasoning in begin
      (- a) * c - (- b) * d
      ≡⟨ cong₂ _-_ (sym (neg-distribˡ-* a c))
                    (sym (neg-distribˡ-* b d)) ⟩
      - (a * c) - - (b * d)
      ≡⟨ cong (λ z → - (a * c) + z) (neg-involutive (b * d)) ⟩
      - (a * c) + b * d
      ≡⟨ cong (λ z → - (a * c) + z) (sym (neg-involutive (b * d))) ⟩
      - (a * c) + - (- (b * d))
      ≡⟨ sym (neg-distrib-+ (a * c) (- (b * d))) ⟩
      - (a * c - b * d) ∎
    imag = let open ≡-Reasoning in begin
      (- a) * d + (- b) * c
      ≡⟨ cong₂ _+_ (sym (neg-distribˡ-* a d))
                    (sym (neg-distribˡ-* b c)) ⟩
      - (a * d) + - (b * c)
      ≡⟨ sym (neg-distrib-+ (a * d) (b * c)) ⟩
      - (a * d + b * c) ∎

  neg-mulʳ : ∀ x y → x *ᶜ (-ᶜ y) ≡ -ᶜ (x *ᶜ y)
  neg-mulʳ x y = let open ≡-Reasoning in begin
    x *ᶜ (-ᶜ y)
    ≡⟨ *ᶜ-comm x (-ᶜ y) ⟩
    (-ᶜ y) *ᶜ x
    ≡⟨ neg-mulˡ y x ⟩
    -ᶜ (y *ᶜ x)
    ≡⟨ cong -ᶜ_ (*ᶜ-comm y x) ⟩
    -ᶜ (x *ᶜ y) ∎

  re-neg : ∀ z → re (-ᶜ z) ≡ - re z
  re-neg (a , b) = refl

norm²-neg : ∀ z → norm² (-ᶜ z) ≡ norm² z
norm²-neg (a , b) =
  cong₂ _+_ (neg-neg-mul a a) (neg-neg-mul b b)

------------------------------------------------------------------------
-- Polarization
--
-- |x + y|² = |x|² + |y|² + 2·Re(conj x · y).
-- Interference term: twice the real part of the Hermitian overlap.
--
-- 极化恒等式
--
-- |x + y|² = |x|² + |y|² + 2·Re(conj x · y)。
-- 干涉项：Hermite 内积实部的两倍。

cross : ℂ → ℂ → ℚ
cross x y = re (conj x *ᶜ y) + re (conj x *ᶜ y)

private
  re-overlap : ∀ (a b d e : ℚ) →
               re (conj (a , b) *ᶜ (d , e)) ≡ a * d + b * e
  re-overlap a b d e = let open ≡-Reasoning in begin
    (a * d) - ((- b) * e)
    ≡⟨ cong (λ z → (a * d) - z) (sym (neg-distribˡ-* b e)) ⟩
    (a * d) - (- (b * e))
    ≡⟨ cong (λ z → (a * d) + z) (neg-involutive (b * e)) ⟩
    a * d + b * e ∎

norm²-add : ∀ (x y : ℂ) →
            norm² (x +ᶜ y) ≡ norm² x + norm² y + cross x y
norm²-add (a , b) (d , e) = let open ≡-Reasoning in begin
  (a + d) * (a + d) + (b + e) * (b + e)
  ≡⟨ cong₂ _+_ (sq+ a d) (sq+ b e) ⟩
  (a² + (d² + P)) + (b² + (e² + Q))
  ≡⟨ +interchange a² (d² + P) b² (e² + Q) ⟩
  (a² + b²) + ((d² + P) + (e² + Q))
  ≡⟨ cong ((a² + b²) +_) (+interchange d² P e² Q) ⟩
  (a² + b²) + ((d² + e²) + (P + Q))
  ≡⟨ cong (λ z → (a² + b²) + ((d² + e²) + z)) swap ⟩
  (a² + b²) + ((d² + e²) + cross (a , b) (d , e))
  ≡⟨ sym (+-assoc (a² + b²) (d² + e²) (cross (a , b) (d , e))) ⟩
  (a² + b²) + (d² + e²) + cross (a , b) (d , e) ∎
  where
  a² = a * a ; d² = d * d ; b² = b * b ; e² = e * e
  P = a * d + a * d ; Q = b * e + b * e
  ovl = re (conj (a , b) *ᶜ (d , e))
  swap = let open ≡-Reasoning in begin
    P + Q
    ≡⟨ +interchange (a * d) (a * d) (b * e) (b * e) ⟩
    (a * d + b * e) + (a * d + b * e)
    ≡⟨ sym (cong₂ _+_ (re-overlap a b d e) (re-overlap a b d e)) ⟩
    ovl + ovl ∎

------------------------------------------------------------------------
-- The two interference terms of a unitary row pair are opposites
--
-- 幺正两行的两个干涉项互为相反数

private
  -- B = conj(x')·y' is the additive inverse of A = conj(x)·y for the
  -- second row x' = -conj v · α, y' = conj u · β.
  --
  -- 对第二行 x' = -conj v · α、y' = conj u · β，B = conj(x')·y' 是
  -- A = conj(x)·y 的加法逆元。
  cross-opposite : ∀ (u v α β : ℂ) →
      let x  = u *ᶜ α
          y  = v *ᶜ β
          x' = (-ᶜ conj v) *ᶜ α
          y' = conj u *ᶜ β
      in cross x' y' ≡ - cross x y
  cross-opposite u v α β = let open ≡-Reasoning in begin
    re B + re B
    ≡⟨ cong₂ _+_ (cong re B≡-A) (cong re B≡-A) ⟩
    re (-ᶜ A) + re (-ᶜ A)
    ≡⟨ cong₂ _+_ (re-neg A) (re-neg A) ⟩
    (- re A) + (- re A)
    ≡⟨ sym (neg-distrib-+ (re A) (re A)) ⟩
    - (re A + re A) ∎
    where
    x  = u *ᶜ α
    y  = v *ᶜ β
    x' = (-ᶜ conj v) *ᶜ α
    y' = conj u *ᶜ β
    A  = conj x *ᶜ y
    B  = conj x' *ᶜ y'
    w  = conj u *ᶜ v
    F  = conj α *ᶜ w

    flip : conj (u *ᶜ α) ≡ conj α *ᶜ conj u
    flip = let open ≡-Reasoning in begin
      conj (u *ᶜ α)
      ≡⟨ conj-mul u α ⟩
      conj u *ᶜ conj α
      ≡⟨ *ᶜ-comm (conj u) (conj α) ⟩
      conj α *ᶜ conj u ∎

    A≡ : A ≡ F *ᶜ β
    A≡ = let open ≡-Reasoning in begin
      conj (u *ᶜ α) *ᶜ (v *ᶜ β)
      ≡⟨ cong (_*ᶜ (v *ᶜ β)) flip ⟩
      (conj α *ᶜ conj u) *ᶜ (v *ᶜ β)
      ≡⟨ *ᶜ-assoc (conj α) (conj u) (v *ᶜ β) ⟩
      conj α *ᶜ (conj u *ᶜ (v *ᶜ β))
      ≡⟨ cong (conj α *ᶜ_) (sym (*ᶜ-assoc (conj u) v β)) ⟩
      conj α *ᶜ ((conj u *ᶜ v) *ᶜ β)
      ≡⟨ sym (*ᶜ-assoc (conj α) w β) ⟩
      F *ᶜ β ∎

    conjx'≡ : conj x' ≡ conj α *ᶜ (-ᶜ v)
    conjx'≡ = let open ≡-Reasoning in begin
      conj ((-ᶜ conj v) *ᶜ α)
      ≡⟨ conj-mul (-ᶜ conj v) α ⟩
      conj (-ᶜ conj v) *ᶜ conj α
      ≡⟨ *ᶜ-comm (conj (-ᶜ conj v)) (conj α) ⟩
      conj α *ᶜ conj (-ᶜ conj v)
      ≡⟨ cong (conj α *ᶜ_) (conj-neg (conj v)) ⟩
      conj α *ᶜ (-ᶜ conj (conj v))
      ≡⟨ cong (conj α *ᶜ_) (cong -ᶜ_ (conj-invol v)) ⟩
      conj α *ᶜ (-ᶜ v) ∎

    mid≡ : (-ᶜ v) *ᶜ conj u ≡ -ᶜ w
    mid≡ = let open ≡-Reasoning in begin
      (-ᶜ v) *ᶜ conj u
      ≡⟨ neg-mulˡ v (conj u) ⟩
      -ᶜ (v *ᶜ conj u)
      ≡⟨ cong -ᶜ_ (*ᶜ-comm v (conj u)) ⟩
      -ᶜ (conj u *ᶜ v) ∎

    B≡-A : B ≡ -ᶜ A
    B≡-A = let open ≡-Reasoning in begin
      B
      ≡⟨ cong (_*ᶜ y') conjx'≡ ⟩
      (conj α *ᶜ (-ᶜ v)) *ᶜ (conj u *ᶜ β)
      ≡⟨ *ᶜ-assoc (conj α) (-ᶜ v) (conj u *ᶜ β) ⟩
      conj α *ᶜ ((-ᶜ v) *ᶜ (conj u *ᶜ β))
      ≡⟨ cong (conj α *ᶜ_) (sym (*ᶜ-assoc (-ᶜ v) (conj u) β)) ⟩
      conj α *ᶜ (((-ᶜ v) *ᶜ conj u) *ᶜ β)
      ≡⟨ cong (conj α *ᶜ_) (cong (_*ᶜ β) mid≡) ⟩
      conj α *ᶜ ((-ᶜ w) *ᶜ β)
      ≡⟨ cong (conj α *ᶜ_) (neg-mulˡ w β) ⟩
      conj α *ᶜ (-ᶜ (w *ᶜ β))
      ≡⟨ neg-mulʳ (conj α) (w *ᶜ β) ⟩
      -ᶜ (conj α *ᶜ (w *ᶜ β))
      ≡⟨ cong -ᶜ_ (sym (*ᶜ-assoc (conj α) w β)) ⟩
      -ᶜ ((conj α *ᶜ w) *ᶜ β)
      ≡⟨ cong -ᶜ_ (sym A≡) ⟩
      -ᶜ A ∎

------------------------------------------------------------------------
-- Main theorem
--
-- A complex 2×2 unitary conserves total norm. U = [[u, v], [-conj v,
-- conj u]], with carried |u|² + |v|² = 1.
--
-- 主定理
--
-- 复 2×2 幺正保持总范数。U = [[u, v], [-conj v, conj u]]，携带
-- |u|² + |v|² = 1。
unitary2-pres : ∀ (u v α β : ℂ) →
                norm² u + norm² v ≡ 1ℚ →
                norm² (u *ᶜ α +ᶜ v *ᶜ β)
              + norm² ((-ᶜ conj v) *ᶜ α +ᶜ conj u *ᶜ β)
              ≡ norm² α + norm² β
unitary2-pres u v α β h = let open ≡-Reasoning in begin
  norm² γ0 + norm² γ1
  ≡⟨ cong₂ _+_ (norm²-add x y) (norm²-add x' y') ⟩
  (Dxy + cross x y) + (Dx'y' + cross x' y')
  ≡⟨ cong (λ c → (Dxy + cross x y) + (Dx'y' + c))
          (cross-opposite u v α β) ⟩
  (Dxy + cross x y) + (Dx'y' + (- cross x y))
  ≡⟨ cong₂ (λ p q → (p + cross x y) + (q + (- cross x y))) dxy dx'y' ⟩
  ((Uαα + Vββ) + cross x y) + ((Vαα + Uββ) + (- cross x y))
  ≡⟨ gather-t Uαα Vββ Vαα Uββ (cross x y) ⟩
  (Uαα + Vαα) + (Vββ + Uββ)
  ≡⟨ cong (λ s → (Uαα + Vαα) + s) (+-comm Vββ Uββ) ⟩
  (Uαα + Vαα) + (Uββ + Vββ)
  ≡⟨ cong₂ _+_ (sym (*-distribʳ-+ (norm² α) (norm² u) (norm² v)))
                (sym (*-distribʳ-+ (norm² β) (norm² u) (norm² v))) ⟩
  (norm² u + norm² v) * norm² α
    + (norm² u + norm² v) * norm² β
  ≡⟨ cong₂ _+_ (cong (_* norm² α) h) (cong (_* norm² β) h) ⟩
  1ℚ * norm² α + 1ℚ * norm² β
  ≡⟨ cong₂ _+_ (*-identityˡ (norm² α)) (*-identityˡ (norm² β)) ⟩
  norm² α + norm² β ∎
  where
  x  = u *ᶜ α
  y  = v *ᶜ β
  x' = (-ᶜ conj v) *ᶜ α
  y' = conj u *ᶜ β
  γ0 = x +ᶜ y
  γ1 = x' +ᶜ y'
  Uαα = norm² u * norm² α
  Vββ = norm² v * norm² β
  Vαα = norm² v * norm² α
  Uββ = norm² u * norm² β
  Dxy   = norm² x + norm² y
  Dx'y' = norm² x' + norm² y'

  diagx : norm² x ≡ Uαα
  diagx = let open ≡-Reasoning in begin
    norm² (u *ᶜ α) ≡⟨ norm²-mul u α ⟩ norm² u * norm² α ∎
  diagy : norm² y ≡ Vββ
  diagy = let open ≡-Reasoning in begin
    norm² (v *ᶜ β) ≡⟨ norm²-mul v β ⟩ norm² v * norm² β ∎
  diagx' : norm² x' ≡ Vαα
  diagx' = let open ≡-Reasoning in begin
    norm² ((-ᶜ conj v) *ᶜ α)
    ≡⟨ norm²-mul (-ᶜ conj v) α ⟩
    norm² (-ᶜ conj v) * norm² α
    ≡⟨ cong (_* norm² α) (norm²-neg (conj v)) ⟩
    norm² (conj v) * norm² α
    ≡⟨ cong (_* norm² α) (norm²-conj v) ⟩
    norm² v * norm² α ∎
  diagy' : norm² y' ≡ Uββ
  diagy' = let open ≡-Reasoning in begin
    norm² (conj u *ᶜ β)
    ≡⟨ norm²-mul (conj u) β ⟩
    norm² (conj u) * norm² β
    ≡⟨ cong (_* norm² β) (norm²-conj u) ⟩
    norm² u * norm² β ∎

  dxy : Dxy ≡ Uαα + Vββ
  dxy = cong₂ _+_ diagx diagy
  dx'y' : Dx'y' ≡ Vαα + Uββ
  dx'y' = cong₂ _+_ diagx' diagy'

------------------------------------------------------------------------
-- Rational-complex instance
--
-- u = 3/5, v = (4/5)i, |u|² + |v|² = 1.
--
-- 有理复实例
--
-- u = 3/5、v = (4/5)i，|u|² + |v|² = 1。

private
  i3 i4 : ℤ
  i3 = (1ℤ ℤ+ 1ℤ) ℤ+ 1ℤ
  i4 = i3 ℤ+ 1ℤ
  c₃₄₅ s₃₄₅ : ℚ
  c₃₄₅ = i3 / 5
  s₃₄₅ = i4 / 5

u₃₄₅ v₃₄₅ : ℂ
u₃₄₅ = (c₃₄₅ , 0ℚ)
v₃₄₅ = (0ℚ , s₃₄₅)

-- Closed Pythagorean arithmetic normalises to 1 by refl.
--
-- 闭项勾股算术经 refl 规范化为 1。
pythagoras-345 : norm² u₃₄₅ + norm² v₃₄₅ ≡ 1ℚ
pythagoras-345 = refl

-- The complex unitary with u = 3/5, v = (4/5)i conserves total norm.
--
-- u = 3/5、v = (4/5)i 的复幺正保持总范数。
unitary2-345 : ∀ (α β : ℂ) →
  norm² (u₃₄₅ *ᶜ α +ᶜ v₃₄₅ *ᶜ β)
  + norm² ((-ᶜ conj v₃₄₅) *ᶜ α +ᶜ conj u₃₄₅ *ᶜ β)
  ≡ norm² α + norm² β
unitary2-345 α β = unitary2-pres u₃₄₅ v₃₄₅ α β pythagoras-345
