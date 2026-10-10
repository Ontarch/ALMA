------------------------------------------------------------------------
-- Left ℚ-bilinearity of the quadratic Poisson bracket.
--
--   {f + g, h} = {f,h} + {g,h},   {r f, g} = r {f,g}.
--
-- Right-linearity follows from antisymmetry in the next slice.
--
-- 二次 Poisson 括号的左 ℚ-双线性。
--
--   {f + g, h} = {f,h} + {g,h}，  {r f, g} = r {f,g}。
--
-- 右参数线性由下一切片的反对称推出。
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module ALMA.Physics.Newton.QuadraticBilinear where

open import ALMA.Physics.Newton.Quadratic as Q
  using (Obs; obs; bracket; add; scale; twoℚ; fourℚ)

open import Data.Rational using (ℚ; _+_; _*_; -_)
open import Data.Rational.Properties using
  ( +-assoc; +-comm
  ; *-assoc; *-comm
  ; *-distribˡ-+; *-distribʳ-+
  ; neg-distrib-+; neg-distribʳ-* )
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; sym; trans; cong; cong₂; module ≡-Reasoning)

------------------------------------------------------------------------
-- Additive rearrangement
-- 加法重排
------------------------------------------------------------------------

private
  -- (x + y) + (u + v) = (x + u) + (y + v).
  swap4 : ∀ x y u v → (x + y) + (u + v) ≡ (x + u) + (y + v)
  swap4 x y u v = let open ≡-Reasoning in begin
    (x + y) + (u + v)
    ≡⟨ +-assoc x y (u + v) ⟩
    x + (y + (u + v))
    ≡⟨ cong (x +_) (sym (+-assoc y u v)) ⟩
    x + ((y + u) + v)
    ≡⟨ cong (x +_) (cong (λ z → z + v) (+-comm y u)) ⟩
    x + ((u + y) + v)
    ≡⟨ cong (x +_) (+-assoc u y v) ⟩
    x + (u + (y + v))
    ≡⟨ sym (+-assoc x u (y + v)) ⟩
    (x + u) + (y + v) ∎

  -- Regroup two interleaved pairs:
  --   (x₁ + y₁) + (x₂ + y₂) = (x₁ + x₂) + (y₁ + y₂).
  pairs2 : ∀ x₁ x₂ y₁ y₂ →
           (x₁ + y₁) + (x₂ + y₂) ≡ (x₁ + x₂) + (y₁ + y₂)
  pairs2 x₁ x₂ y₁ y₂ = swap4 x₁ y₁ x₂ y₂

  -- Regroup four interleaved pairs into two left-associated groups.
  pairs4 : ∀ x₁ x₂ x₃ x₄ y₁ y₂ y₃ y₄ →
          (((x₁ + y₁) + (x₂ + y₂)) + ((x₃ + y₃) + (x₄ + y₄)))
          ≡ ((((x₁ + x₂) + x₃) + x₄) + (((y₁ + y₂) + y₃) + y₄))
  pairs4 x₁ x₂ x₃ x₄ y₁ y₂ y₃ y₄ = let open ≡-Reasoning in begin
      (((x₁ + y₁) + (x₂ + y₂)) + ((x₃ + y₃) + (x₄ + y₄)))
    ≡⟨ cong₂ _+_ (swap4 x₁ y₁ x₂ y₂) (swap4 x₃ y₃ x₄ y₄) ⟩
      (((x₁ + x₂) + (y₁ + y₂)) + ((x₃ + x₄) + (y₃ + y₄)))
    ≡⟨ swap4 (x₁ + x₂) (y₁ + y₂) (x₃ + x₄) (y₃ + y₄) ⟩
      (((x₁ + x₂) + (x₃ + x₄)) + ((y₁ + y₂) + (y₃ + y₄)))
    ≡⟨ cong₂ _+_ (sym (+-assoc (x₁ + x₂) x₃ x₄))
                 (sym (+-assoc (y₁ + y₂) y₃ y₄)) ⟩
      ((((x₁ + x₂) + x₃) + x₄) + (((y₁ + y₂) + y₃) + y₄)) ∎

  -- (u + v) * z = u*z + v*z.
  splitR : ∀ z u v → (u + v) * z ≡ u * z + v * z
  splitR z u v = *-distribʳ-+ z u v

  -- s * (u + v) = s*u + s*v.
  splitL : ∀ s u v → s * (u + v) ≡ s * u + s * v
  splitL s u v = *-distribˡ-+ s u v

-- Assemble six field equalities into an equality of records.
-- 由六个字段等式组装为记录相等。
private
  mk : ∀ {lc la lb ld le lf rc ra rb rd re rf}
     → lc ≡ rc → la ≡ ra → lb ≡ rb
     → ld ≡ rd → le ≡ re → lf ≡ rf
     → obs lc la lb ld le lf ≡ obs rc ra rb rd re rf
  mk pc pa pb pd pe pf = let open ≡-Reasoning in begin
    obs _ _ _ _ _ _
    ≡⟨ cong (λ x → obs x _ _ _ _ _) pc ⟩
    obs _ _ _ _ _ _
    ≡⟨ cong (λ x → obs _ x _ _ _ _) pa ⟩
    obs _ _ _ _ _ _
    ≡⟨ cong (λ x → obs _ _ x _ _ _) pb ⟩
    obs _ _ _ _ _ _
    ≡⟨ cong (λ x → obs _ _ _ x _ _) pd ⟩
    obs _ _ _ _ _ _
    ≡⟨ cong (λ x → obs _ _ _ _ x _) pe ⟩
    obs _ _ _ _ _ _
    ≡⟨ cong (obs _ _ _ _ _) pf ⟩
    obs _ _ _ _ _ _ ∎

------------------------------------------------------------------------
-- Additive linearity in the first argument
-- 第一参数的加法线性
------------------------------------------------------------------------

bracket-addˡ : ∀ f g h →
               bracket (add f g) h ≡ add (bracket f h) (bracket g h)
bracket-addˡ (obs _ a b d e f) (obs _ a' b' d' e' f')
             (obs _ A B D E F) = mk c-c q-c p-c d-c e-c f-c
  where
  -- f- and g-parts of every monomial (signs included).
  x₁ = a * E;           y₁ = a' * E
  x₂ = twoℚ * d * B;    y₂ = twoℚ * d' * B
  x₃ = - (e * A);       y₃ = - (e' * A)
  x₄ = - (twoℚ * b * D); y₄ = - (twoℚ * b' * D)
  X₁ = twoℚ * a * F;    Y₁ = twoℚ * a' * F
  X₂ = e * B;           Y₂ = e' * B
  X₃ = - (b * E);       Y₃ = - (b' * E)
  X₄ = - (twoℚ * f * A); Y₄ = - (twoℚ * f' * A)
  Z₁ = twoℚ * d * E;    Z₁' = twoℚ * d' * E
  Z₂ = - (twoℚ * e * D); Z₂' = - (twoℚ * e' * D)
  W₁ = fourℚ * d * F;   W₁' = fourℚ * d' * F
  W₂ = - (fourℚ * f * D); W₂' = - (fourℚ * f' * D)
  V₁ = twoℚ * e * F;    V₁' = twoℚ * e' * F
  V₂ = - (twoℚ * f * E); V₂' = - (twoℚ * f' * E)

  c-c = let open ≡-Reasoning
            c₁ = a * B; c₁' = a' * B
        in begin
    (a + a') * B + - ((b + b') * A)
    ≡⟨ cong₂ (λ X Y → X + - Y)
             (splitR B a a') (splitR A b b') ⟩
    (c₁ + c₁') + - (b * A + b' * A)
    ≡⟨ cong ((c₁ + c₁') +_)
            (neg-distrib-+ (b * A) (b' * A)) ⟩
    (c₁ + c₁') + (- (b * A) + - (b' * A))
    ≡⟨ pairs2 c₁ (- (b * A)) c₁' (- (b' * A)) ⟩
    (c₁ + - (b * A)) + (c₁' + - (b' * A)) ∎

  -- Split a scalar-prefixed summand s*((u+v))*z into s*u*z + s*v*z.
  splitSZ : ∀ s z u v →
            (s * (u + v)) * z ≡ (s * u) * z + (s * v) * z
  splitSZ s z u v = let open ≡-Reasoning in begin
    (s * (u + v)) * z
    ≡⟨ cong (λ t → t * z) (splitL s u v) ⟩
    (s * u + s * v) * z
    ≡⟨ splitR z (s * u) (s * v) ⟩
    (s * u) * z + (s * v) * z ∎

  -- Split a negated summand -((u+v)*z) into -(u*z) + -(v*z).
  splitNeg : ∀ z u v →
             - ((u + v) * z) ≡ - (u * z) + - (v * z)
  splitNeg z u v = let open ≡-Reasoning in begin
    - ((u + v) * z)
    ≡⟨ cong -_ (splitR z u v) ⟩
    - (u * z + v * z)
    ≡⟨ neg-distrib-+ (u * z) (v * z) ⟩
    - (u * z) + - (v * z) ∎

  splitNegSZ : ∀ s z u v →
               - ((s * (u + v)) * z) ≡ - ((s * u) * z) + - ((s * v) * z)
  splitNegSZ s z u v = let open ≡-Reasoning in begin
    - ((s * (u + v)) * z)
    ≡⟨ cong -_ (splitSZ s z u v) ⟩
    - ((s * u) * z + (s * v) * z)
    ≡⟨ neg-distrib-+ ((s * u) * z) ((s * v) * z) ⟩
    - ((s * u) * z) + - ((s * v) * z) ∎

  q-c = let open ≡-Reasoning
            u1 = (a + a') * E
            u2 = twoℚ * (d + d') * B
            u3 = - ((e + e') * A)
            u4 = - (twoℚ * (b + b') * D)
        in begin
      (((u1 + u2) + u3) + u4)
    ≡⟨ cong (λ t → (((t + u2) + u3) + u4))
            (splitR E a a') ⟩
      ((((x₁ + y₁) + u2) + u3) + u4)
    ≡⟨ cong (λ t → ((((x₁ + y₁) + t) + u3) + u4))
            (splitSZ twoℚ B d d') ⟩
      ((((x₁ + y₁) + (x₂ + y₂)) + u3) + u4)
    ≡⟨ cong (λ t → ((((x₁ + y₁) + (x₂ + y₂)) + t) + u4))
            (splitNeg A e e') ⟩
      ((((x₁ + y₁) + (x₂ + y₂)) + (x₃ + y₃)) + u4)
    ≡⟨ cong (λ t → (((x₁ + y₁) + (x₂ + y₂)) + (x₃ + y₃)) + t)
            (splitNegSZ twoℚ D b b') ⟩
      ((((x₁ + y₁) + (x₂ + y₂)) + (x₃ + y₃)) + (x₄ + y₄))
    ≡⟨ +-assoc ((x₁ + y₁) + (x₂ + y₂)) (x₃ + y₃) (x₄ + y₄) ⟩
      (((x₁ + y₁) + (x₂ + y₂)) + ((x₃ + y₃) + (x₄ + y₄)))
    ≡⟨ pairs4 x₁ x₂ x₃ x₄ y₁ y₂ y₃ y₄ ⟩
      ((((x₁ + x₂) + x₃) + x₄) + (((y₁ + y₂) + y₃) + y₄)) ∎

  p-c = let open ≡-Reasoning
            u1 = twoℚ * (a + a') * F
            u2 = (e + e') * B
            u3 = - ((b + b') * E)
            u4 = - (twoℚ * (f + f') * A)
        in begin
      (((u1 + u2) + u3) + u4)
    ≡⟨ cong (λ t → (((t + u2) + u3) + u4))
            (splitSZ twoℚ F a a') ⟩
      ((((X₁ + Y₁) + u2) + u3) + u4)
    ≡⟨ cong (λ t → ((((X₁ + Y₁) + t) + u3) + u4))
            (splitR B e e') ⟩
      ((((X₁ + Y₁) + (X₂ + Y₂)) + u3) + u4)
    ≡⟨ cong (λ t → ((((X₁ + Y₁) + (X₂ + Y₂)) + t) + u4))
            (splitNeg E b b') ⟩
      ((((X₁ + Y₁) + (X₂ + Y₂)) + (X₃ + Y₃)) + u4)
    ≡⟨ cong (λ t → (((X₁ + Y₁) + (X₂ + Y₂)) + (X₃ + Y₃)) + t)
            (splitNegSZ twoℚ A f f') ⟩
      ((((X₁ + Y₁) + (X₂ + Y₂)) + (X₃ + Y₃)) + (X₄ + Y₄))
    ≡⟨ +-assoc ((X₁ + Y₁) + (X₂ + Y₂)) (X₃ + Y₃) (X₄ + Y₄) ⟩
      (((X₁ + Y₁) + (X₂ + Y₂)) + ((X₃ + Y₃) + (X₄ + Y₄)))
    ≡⟨ pairs4 X₁ X₂ X₃ X₄ Y₁ Y₂ Y₃ Y₄ ⟩
      ((((X₁ + X₂) + X₃) + X₄) + (((Y₁ + Y₂) + Y₃) + Y₄)) ∎

  d-c = let open ≡-Reasoning in begin
    twoℚ * (d + d') * E + - (twoℚ * (e + e') * D)
    ≡⟨ cong₂ (λ X Y → X + - Y)
             (splitSZ twoℚ E d d') (splitSZ twoℚ D e e') ⟩
    (Z₁ + Z₁') + - ((twoℚ * e) * D + (twoℚ * e') * D)
    ≡⟨ cong ((Z₁ + Z₁') +_)
            (neg-distrib-+ ((twoℚ * e) * D) ((twoℚ * e') * D)) ⟩
    (Z₁ + Z₁') + (Z₂ + Z₂')
    ≡⟨ pairs2 Z₁ Z₂ Z₁' Z₂' ⟩
    (Z₁ + Z₂) + (Z₁' + Z₂') ∎

  e-c = let open ≡-Reasoning in begin
    fourℚ * (d + d') * F + - (fourℚ * (f + f') * D)
    ≡⟨ cong₂ (λ X Y → X + - Y)
             (splitSZ fourℚ F d d') (splitSZ fourℚ D f f') ⟩
    (W₁ + W₁') + - ((fourℚ * f) * D + (fourℚ * f') * D)
    ≡⟨ cong ((W₁ + W₁') +_)
            (neg-distrib-+ ((fourℚ * f) * D) ((fourℚ * f') * D)) ⟩
    (W₁ + W₁') + (W₂ + W₂')
    ≡⟨ pairs2 W₁ W₂ W₁' W₂' ⟩
    (W₁ + W₂) + (W₁' + W₂') ∎

  f-c = let open ≡-Reasoning in begin
    twoℚ * (e + e') * F + - (twoℚ * (f + f') * E)
    ≡⟨ cong₂ (λ X Y → X + - Y)
             (splitSZ twoℚ F e e') (splitSZ twoℚ E f f') ⟩
    (V₁ + V₁') + - ((twoℚ * f) * E + (twoℚ * f') * E)
    ≡⟨ cong ((V₁ + V₁') +_)
            (neg-distrib-+ ((twoℚ * f) * E) ((twoℚ * f') * E)) ⟩
    (V₁ + V₁') + (V₂ + V₂')
    ≡⟨ pairs2 V₁ V₂ V₁' V₂' ⟩
    (V₁ + V₂) + (V₁' + V₂') ∎

------------------------------------------------------------------------
-- Scalar linearity in the first argument
-- 第一参数的数乘线性
------------------------------------------------------------------------

private
  -- s*(r*x) = r*(s*x).
  swap-scalar : ∀ {r} s x → (s * (r * x)) ≡ r * (s * x)
  swap-scalar {r} s x = let open ≡-Reasoning in begin
    s * (r * x)
    ≡⟨ sym (*-assoc s r x) ⟩
    (s * r) * x
    ≡⟨ cong (λ z → z * x) (*-comm s r) ⟩
    (r * s) * x
    ≡⟨ *-assoc r s x ⟩
    r * (s * x) ∎

  -- (r*x)*z = r*(x*z).
  front : ∀ {r} z x → (r * x) * z ≡ r * (x * z)
  front {r} z x = *-assoc r x z

  -- (s*(r*x))*z = r*((s*x)*z).
  frontS : ∀ {r} s z x → (s * (r * x)) * z ≡ r * ((s * x) * z)
  frontS {r} s z x = let open ≡-Reasoning in begin
    (s * (r * x)) * z
    ≡⟨ cong (λ t → t * z) (swap-scalar {r} s x) ⟩
    (r * (s * x)) * z
    ≡⟨ *-assoc r (s * x) z ⟩
    r * ((s * x) * z) ∎

  -- -(r*x) = r*(-x).
  front-neg : ∀ {r} x → - (r * x) ≡ r * (- x)
  front-neg {r} x = neg-distribʳ-* r x

  -- r*x + r*(-y) = r*(x + -y).
  factor2 : ∀ {r} x y → r * x + r * (- y) ≡ r * (x + - y)
  factor2 {r} x y = sym (*-distribˡ-+ r x (- y))

  -- Factor r from four left-associated signed summands.
  factor4 : ∀ {r} x y z w →
            (((r * x + r * y) + r * (- z)) + r * (- w))
            ≡ r * (((x + y) + - z) + - w)
  factor4 {r} x y z w = let open ≡-Reasoning in begin
      (((r * x + r * y) + r * (- z)) + r * (- w))
    ≡⟨ cong (λ t → (t + r * (- z)) + r * (- w))
            (sym (*-distribˡ-+ r x y)) ⟩
      ((r * (x + y) + r * (- z)) + r * (- w))
    ≡⟨ cong (λ t → t + r * (- w))
            (sym (*-distribˡ-+ r (x + y) (- z))) ⟩
      r * ((x + y) + - z) + r * (- w)
    ≡⟨ sym (*-distribˡ-+ r ((x + y) + - z) (- w)) ⟩
      r * (((x + y) + - z) + - w) ∎

bracket-scaleˡ : ∀ r f g →
                 bracket (scale r f) g ≡ scale r (bracket f g)
bracket-scaleˡ r (obs _ a b d e f) (obs _ A B D E F) =
  mk c-c q-c p-c d-c e-c f-c
  where
  c-c = let open ≡-Reasoning in begin
    (r * a) * B + - ((r * b) * A)
    ≡⟨ cong₂ (λ X Y → X + - Y) (front {r} B a) (front {r} A b) ⟩
    r * (a * B) + - (r * (b * A))
    ≡⟨ cong (r * (a * B) +_) (front-neg {r} (b * A)) ⟩
    r * (a * B) + r * (- (b * A))
    ≡⟨ factor2 {r} (a * B) (b * A) ⟩
    r * (a * B + - (b * A)) ∎

  -- Transform one negated, scalar-prefixed summand to r*(-target).
  front-negS : ∀ s z x →
               - ((s * (r * x)) * z) ≡ r * (- ((s * x) * z))
  front-negS s z x = let open ≡-Reasoning in begin
    - ((s * (r * x)) * z)
    ≡⟨ cong -_ (frontS {r} s z x) ⟩
    - (r * ((s * x) * z))
    ≡⟨ front-neg {r} ((s * x) * z) ⟩
    r * (- ((s * x) * z)) ∎

  q-c = let open ≡-Reasoning
            u1 = (r * a) * E
            u2 = (twoℚ * (r * d)) * B
            u3 = - ((r * e) * A)
            u4 = - ((twoℚ * (r * b)) * D)
            p3 = trans (cong -_ (front {r} A e)) (front-neg {r} (e * A))
        in begin
      (((u1 + u2) + u3) + u4)
    ≡⟨ cong (λ t → (((t + u2) + u3) + u4)) (front {r} E a) ⟩
      (((r * (a * E) + u2) + u3) + u4)
    ≡⟨ cong (λ t → (((r * (a * E) + t) + u3) + u4))
            (frontS {r} twoℚ B d) ⟩
      (((r * (a * E) + r * (twoℚ * d * B)) + u3) + u4)
    ≡⟨ cong (λ t → (((r * (a * E) + r * (twoℚ * d * B)) + t) + u4)) p3 ⟩
      (((r * (a * E) + r * (twoℚ * d * B)) + r * (- (e * A))) + u4)
    ≡⟨ cong (λ t → (((r * (a * E) + r * (twoℚ * d * B))
                    + r * (- (e * A))) + t))
            (front-negS twoℚ D b) ⟩
      (((r * (a * E) + r * (twoℚ * d * B)) + r * (- (e * A)))
       + r * (- (twoℚ * b * D)))
    ≡⟨ factor4 {r} (a * E) (twoℚ * d * B) (e * A) (twoℚ * b * D) ⟩
      r * (((a * E + twoℚ * d * B) + - (e * A)) + - (twoℚ * b * D)) ∎

  p-c = let open ≡-Reasoning
            u1 = (twoℚ * (r * a)) * F
            u2 = (r * e) * B
            u3 = - ((r * b) * E)
            u4 = - ((twoℚ * (r * f)) * A)
            p3 = trans (cong -_ (front {r} E b)) (front-neg {r} (b * E))
        in begin
      (((u1 + u2) + u3) + u4)
    ≡⟨ cong (λ t → (((t + u2) + u3) + u4))
            (frontS {r} twoℚ F a) ⟩
      (((r * (twoℚ * a * F) + u2) + u3) + u4)
    ≡⟨ cong (λ t → (((r * (twoℚ * a * F) + t) + u3) + u4))
            (front {r} B e) ⟩
      (((r * (twoℚ * a * F) + r * (e * B)) + u3) + u4)
    ≡⟨ cong (λ t → (((r * (twoℚ * a * F) + r * (e * B)) + t) + u4)) p3 ⟩
      (((r * (twoℚ * a * F) + r * (e * B)) + r * (- (b * E))) + u4)
    ≡⟨ cong (λ t → (((r * (twoℚ * a * F) + r * (e * B))
                    + r * (- (b * E))) + t))
            (front-negS twoℚ A f) ⟩
      (((r * (twoℚ * a * F) + r * (e * B)) + r * (- (b * E)))
       + r * (- (twoℚ * f * A)))
    ≡⟨ factor4 {r} (twoℚ * a * F) (e * B) (b * E) (twoℚ * f * A) ⟩
      r * (((twoℚ * a * F + e * B) + - (b * E)) + - (twoℚ * f * A)) ∎

  d-c = let open ≡-Reasoning in begin
    (twoℚ * (r * d)) * E + - ((twoℚ * (r * e)) * D)
    ≡⟨ cong₂ (λ X Y → X + - Y)
             (frontS {r} twoℚ E d) (frontS {r} twoℚ D e) ⟩
    r * (twoℚ * d * E) + - (r * (twoℚ * e * D))
    ≡⟨ cong (r * (twoℚ * d * E) +_)
            (front-neg {r} (twoℚ * e * D)) ⟩
    r * (twoℚ * d * E) + r * (- (twoℚ * e * D))
    ≡⟨ factor2 {r} (twoℚ * d * E) (twoℚ * e * D) ⟩
    r * (twoℚ * d * E + - (twoℚ * e * D)) ∎

  e-c = let open ≡-Reasoning in begin
    (fourℚ * (r * d)) * F + - ((fourℚ * (r * f)) * D)
    ≡⟨ cong₂ (λ X Y → X + - Y)
             (frontS {r} fourℚ F d) (frontS {r} fourℚ D f) ⟩
    r * (fourℚ * d * F) + - (r * (fourℚ * f * D))
    ≡⟨ cong (r * (fourℚ * d * F) +_)
            (front-neg {r} (fourℚ * f * D)) ⟩
    r * (fourℚ * d * F) + r * (- (fourℚ * f * D))
    ≡⟨ factor2 {r} (fourℚ * d * F) (fourℚ * f * D) ⟩
    r * (fourℚ * d * F + - (fourℚ * f * D)) ∎

  f-c = let open ≡-Reasoning in begin
    (twoℚ * (r * e)) * F + - ((twoℚ * (r * f)) * E)
    ≡⟨ cong₂ (λ X Y → X + - Y)
             (frontS {r} twoℚ F e) (frontS {r} twoℚ E f) ⟩
    r * (twoℚ * e * F) + - (r * (twoℚ * f * E))
    ≡⟨ cong (r * (twoℚ * e * F) +_)
            (front-neg {r} (twoℚ * f * E)) ⟩
    r * (twoℚ * e * F) + r * (- (twoℚ * f * E))
    ≡⟨ factor2 {r} (twoℚ * e * F) (twoℚ * f * E) ⟩
    r * (twoℚ * e * F + - (twoℚ * f * E)) ∎
