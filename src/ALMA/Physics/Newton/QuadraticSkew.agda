------------------------------------------------------------------------
-- Algebraic Newtonian mechanics: skew-symmetry and right linearity.
--
-- The quadratic Poisson bracket is skew-symmetric:
--   {g, f} = - {f, g}.
-- Together with the left linearity of the previous slice this yields
-- linearity in the second argument, completing Q-bilinearity:
--   {f, g + h} = {f, g} + {f, h},
--   {f, r g}   = r {f, g}.
--
-- 代数版牛顿力学：反对称与右线性。
--
-- 二次 Poisson 括号反对称：
--   {g, f} = - {f, g}。
-- 与上一切片的左线性结合，得到第二参数的线性，闭合 Q-双线性：
--   {f, g + h} = {f, g} + {f, h}，
--   {f, r g}   = r {f, g}。
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module ALMA.Physics.Newton.QuadraticSkew where

open import Data.Rational using (ℚ; 0ℚ; _+_; _*_; -_)
open import Data.Rational.Properties using
  ( +-comm; +-assoc; +-identityˡ; +-identityʳ; +-inverseˡ
  ; *-comm; *-assoc
  ; neg-distrib-+; neg-distribʳ-* )
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; sym; trans; cong; cong₂; module ≡-Reasoning)

open import ALMA.Physics.Newton.Quadratic as Q using
  (Obs; obs; bracket; add; scale; neg; twoℚ; fourℚ)
open import ALMA.Physics.Newton.QuadraticBilinear using
  (bracket-addˡ; bracket-scaleˡ)

private
  -- Assemble six field equalities into an equality of observables.
  -- 由六个字段等式组装为观测量相等。
  mkObs : ∀ {lc la lb ld le lf rc ra rb rd re rf}
        → lc ≡ rc → la ≡ ra → lb ≡ rb
        → ld ≡ rd → le ≡ re → lf ≡ rf
        → obs lc la lb ld le lf ≡ obs rc ra rb rd re rf
  mkObs pc pa pb pd pe pf = let open ≡-Reasoning in begin
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

  -- Flip the last two factors of a left-associated triple product.
  -- 翻转左结合三元乘积的后两个因子。
  flip3 : ∀ s x y → (s * x) * y ≡ (s * y) * x
  flip3 s x y = let open ≡-Reasoning in begin
    (s * x) * y
    ≡⟨ *-assoc s x y ⟩
    s * (x * y)
    ≡⟨ cong (s *_) (*-comm x y) ⟩
    s * (y * x)
    ≡⟨ sym (*-assoc s y x) ⟩
    (s * y) * x ∎

  -- Rotate the first two of four summands to the end.
  -- 将四个加项的前两个移到末尾。
  rot4 : ∀ X Y U V → ((X + Y) + U) + V ≡ ((U + V) + X) + Y
  rot4 X Y U V = let open ≡-Reasoning in begin
    ((X + Y) + U) + V
    ≡⟨ +-assoc (X + Y) U V ⟩
    (X + Y) + (U + V)
    ≡⟨ +-comm (X + Y) (U + V) ⟩
    (U + V) + (X + Y)
    ≡⟨ sym (+-assoc (U + V) X Y) ⟩
    ((U + V) + X) + Y ∎

  -- Reverse the order of four summands.
  -- 反转四个加项的次序。
  rev4 : ∀ X Y U V → ((X + Y) + U) + V ≡ ((V + U) + Y) + X
  rev4 X Y U V = let open ≡-Reasoning in begin
    ((X + Y) + U) + V
    ≡⟨ +-assoc (X + Y) U V ⟩
    (X + Y) + (U + V)
    ≡⟨ +-comm (X + Y) (U + V) ⟩
    (U + V) + (X + Y)
    ≡⟨ cong₂ _+_ (+-comm U V) (+-comm X Y) ⟩
    (V + U) + (Y + X)
    ≡⟨ sym (+-assoc (V + U) Y X) ⟩
    ((V + U) + Y) + X ∎

  -- Double negation: - (- x) = x.
  -- 双重否定：- (- x) = x。
  neg-involutive : ∀ x → - (- x) ≡ x
  neg-involutive x = let open ≡-Reasoning in begin
    - (- x)
    ≡⟨ sym (+-identityʳ (- (- x))) ⟩
    - (- x) + 0ℚ
    ≡⟨ cong (λ t → - (- x) + t) (sym (+-inverseˡ x)) ⟩
    - (- x) + (- x + x)
    ≡⟨ sym (+-assoc (- (- x)) (- x) x) ⟩
    (- (- x) + - x) + x
    ≡⟨ cong (λ t → t + x) (+-inverseˡ (- x)) ⟩
    0ℚ + x
    ≡⟨ +-identityˡ x ⟩
    x ∎

  -- Fold the distributed negation of a two-term signed sum:
  -- -(x + - y) = - x + y.
  -- 折叠两项带符号和的展开取负：-(x + - y) = - x + y。
  foldNeg : ∀ x y → - (x + - y) ≡ - x + y
  foldNeg x y = let open ≡-Reasoning in begin
    - (x + - y)
    ≡⟨ neg-distrib-+ x (- y) ⟩
    - x + - (- y)
    ≡⟨ cong (- x +_) (neg-involutive y) ⟩
    - x + y ∎

  -- Negation of a four-term signed sum, with the last two summands
  -- written - c and - d:
  --   - (((a + b) + - c) + - d) = ((- a + - b) + c) + d.
  -- 四项带符号和取负，后两项写成 - c、- d：
  --   - (((a + b) + - c) + - d) = ((- a + - b) + c) + d。
  neg4 : ∀ a b c d →
         - (((a + b) + - c) + - d) ≡ ((- a + - b) + c) + d
  neg4 a b c d = let open ≡-Reasoning in begin
      - (((a + b) + - c) + - d)
    ≡⟨ neg-distrib-+ ((a + b) + - c) (- d) ⟩
      - ((a + b) + - c) + - (- d)
    ≡⟨ cong₂ _+_ (inner a b c) (neg-involutive d) ⟩
      ((- a + - b) + c) + d ∎
    where
    inner : ∀ a b c → - ((a + b) + - c) ≡ (- a + - b) + c
    inner a b c = let open ≡-Reasoning in begin
      - ((a + b) + - c)
      ≡⟨ neg-distrib-+ (a + b) (- c) ⟩
      - (a + b) + - (- c)
      ≡⟨ cong (λ t → - (a + b) + t) (neg-involutive c) ⟩
      - (a + b) + c
      ≡⟨ cong (λ t → t + c) (neg-distrib-+ a b) ⟩
      (- a + - b) + c ∎

------------------------------------------------------------------------
-- Skew-symmetry
-- 反对称
------------------------------------------------------------------------

-- {g, f} = - {f, g}.
-- {g, f} = - {f, g}。
bracket-skew : ∀ f g → bracket g f ≡ neg (bracket f g)
bracket-skew (obs _ a b d e f) (obs _ a' b' d' e' f') =
  mkObs c-c q-c p-c d-c e-c f-c
  where
  -- Two-term coefficients: flip the factors of both products, then the
  -- positive and negative summands exchange by commutativity.
  -- 两项系数：翻转两个乘积的因子，正、负加项再由交换律换位。
  c-c = let open ≡-Reasoning in begin
      a' * b + - (b' * a)
    ≡⟨ cong (λ t → t + - (b' * a)) (*-comm a' b) ⟩
      b * a' + - (b' * a)
    ≡⟨ cong (λ t → b * a' + - t) (*-comm b' a) ⟩
      b * a' + - (a * b')
    ≡⟨ +-comm (b * a') (- (a * b')) ⟩
      - (a * b') + b * a'
    ≡⟨ sym (foldNeg (a * b') (b * a')) ⟩
      - (a * b' + - (b * a')) ∎

  d-c = let open ≡-Reasoning in begin
      twoℚ * d' * e + - (twoℚ * e' * d)
    ≡⟨ cong (λ t → t + - (twoℚ * e' * d)) (flip3 twoℚ d' e) ⟩
      twoℚ * e * d' + - (twoℚ * e' * d)
    ≡⟨ cong (λ t → twoℚ * e * d' + - t) (flip3 twoℚ e' d) ⟩
      twoℚ * e * d' + - (twoℚ * d * e')
    ≡⟨ +-comm (twoℚ * e * d') (- (twoℚ * d * e')) ⟩
      - (twoℚ * d * e') + twoℚ * e * d'
    ≡⟨ sym (foldNeg (twoℚ * d * e') (twoℚ * e * d')) ⟩
      - (twoℚ * d * e' + - (twoℚ * e * d')) ∎

  e-c = let open ≡-Reasoning in begin
      fourℚ * d' * f + - (fourℚ * f' * d)
    ≡⟨ cong (λ t → t + - (fourℚ * f' * d)) (flip3 fourℚ d' f) ⟩
      fourℚ * f * d' + - (fourℚ * f' * d)
    ≡⟨ cong (λ t → fourℚ * f * d' + - t) (flip3 fourℚ f' d) ⟩
      fourℚ * f * d' + - (fourℚ * d * f')
    ≡⟨ +-comm (fourℚ * f * d') (- (fourℚ * d * f')) ⟩
      - (fourℚ * d * f') + fourℚ * f * d'
    ≡⟨ sym (foldNeg (fourℚ * d * f') (fourℚ * f * d')) ⟩
      - (fourℚ * d * f' + - (fourℚ * f * d')) ∎

  f-c = let open ≡-Reasoning in begin
      twoℚ * e' * f + - (twoℚ * f' * e)
    ≡⟨ cong (λ t → t + - (twoℚ * f' * e)) (flip3 twoℚ e' f) ⟩
      twoℚ * f * e' + - (twoℚ * f' * e)
    ≡⟨ cong (λ t → twoℚ * f * e' + - t) (flip3 twoℚ f' e) ⟩
      twoℚ * f * e' + - (twoℚ * e * f')
    ≡⟨ +-comm (twoℚ * f * e') (- (twoℚ * e * f')) ⟩
      - (twoℚ * e * f') + twoℚ * f * e'
    ≡⟨ sym (foldNeg (twoℚ * e * f') (twoℚ * f * e')) ⟩
      - (twoℚ * e * f' + - (twoℚ * f * e')) ∎

  -- Four-term coefficients: flip every product in place, then rotate the
  -- signed summands into the negated order.
  -- 四项系数：原地翻转每个乘积，再将带符号加项旋转为取负后的次序。
  q-c = let open ≡-Reasoning in begin
      ((a' * e + twoℚ * d' * b) + - (e' * a)) + - (twoℚ * b' * d)
    ≡⟨ cong (λ t → ((t + twoℚ * d' * b) + - (e' * a))
                    + - (twoℚ * b' * d))
            (*-comm a' e) ⟩
      ((e * a' + twoℚ * d' * b) + - (e' * a)) + - (twoℚ * b' * d)
    ≡⟨ cong (λ t → ((e * a' + t) + - (e' * a))
                    + - (twoℚ * b' * d))
            (flip3 twoℚ d' b) ⟩
      ((e * a' + twoℚ * b * d') + - (e' * a)) + - (twoℚ * b' * d)
    ≡⟨ cong (λ t → ((e * a' + twoℚ * b * d') + t)
                    + - (twoℚ * b' * d))
            (cong -_ (*-comm e' a)) ⟩
      ((e * a' + twoℚ * b * d') + - (a * e')) + - (twoℚ * b' * d)
    ≡⟨ cong (λ t → ((e * a' + twoℚ * b * d') + - (a * e')) + t)
            (cong -_ (flip3 twoℚ b' d)) ⟩
      ((e * a' + twoℚ * b * d') + - (a * e')) + - (twoℚ * d * b')
    ≡⟨ rot4 (e * a') (twoℚ * b * d') (- (a * e'))
                 (- (twoℚ * d * b')) ⟩
      ((- (a * e') + - (twoℚ * d * b')) + e * a')
        + twoℚ * b * d'
    ≡⟨ sym (neg4 (a * e') (twoℚ * d * b') (e * a')
                      (twoℚ * b * d')) ⟩
      - (((a * e' + twoℚ * d * b') + - (e * a'))
           + - (twoℚ * b * d')) ∎

  p-c = let open ≡-Reasoning in begin
      ((twoℚ * a' * f + e' * b) + - (b' * e)) + - (twoℚ * f' * a)
    ≡⟨ cong (λ t → ((t + e' * b) + - (b' * e))
                    + - (twoℚ * f' * a))
            (flip3 twoℚ a' f) ⟩
      ((twoℚ * f * a' + e' * b) + - (b' * e)) + - (twoℚ * f' * a)
    ≡⟨ cong (λ t → ((twoℚ * f * a' + t) + - (b' * e))
                    + - (twoℚ * f' * a))
            (*-comm e' b) ⟩
      ((twoℚ * f * a' + b * e') + - (b' * e)) + - (twoℚ * f' * a)
    ≡⟨ cong (λ t → ((twoℚ * f * a' + b * e') + t)
                    + - (twoℚ * f' * a))
            (cong -_ (*-comm b' e)) ⟩
      ((twoℚ * f * a' + b * e') + - (e * b')) + - (twoℚ * f' * a)
    ≡⟨ cong (λ t → ((twoℚ * f * a' + b * e') + - (e * b')) + t)
            (cong -_ (flip3 twoℚ f' a)) ⟩
      ((twoℚ * f * a' + b * e') + - (e * b')) + - (twoℚ * a * f')
    ≡⟨ rev4 (twoℚ * f * a') (b * e') (- (e * b'))
                 (- (twoℚ * a * f')) ⟩
      ((- (twoℚ * a * f') + - (e * b')) + b * e')
        + twoℚ * f * a'
    ≡⟨ sym (neg4 (twoℚ * a * f') (e * b') (b * e')
                      (twoℚ * f * a')) ⟩
      - (((twoℚ * a * f' + e * b') + - (b * e'))
           + - (twoℚ * f * a')) ∎

------------------------------------------------------------------------
-- Negation distributes over addition and scaling of observables
-- 取负对观测量加法与数乘的分配
------------------------------------------------------------------------

-- - (f + g) = - f + - g.
-- - (f + g) = - f + - g。
neg-add : ∀ f g → neg (add f g) ≡ add (neg f) (neg g)
neg-add (obs c a b d e f) (obs c' a' b' d' e' f') =
  mkObs (neg-distrib-+ c c') (neg-distrib-+ a a') (neg-distrib-+ b b')
        (neg-distrib-+ d d') (neg-distrib-+ e e') (neg-distrib-+ f f')

-- - (r f) = r (- f).
-- - (r f) = r (- f)。
neg-scale : ∀ r f → neg (scale r f) ≡ scale r (neg f)
neg-scale r (obs c a b d e f) =
  mkObs (neg-distribʳ-* r c) (neg-distribʳ-* r a) (neg-distribʳ-* r b)
        (neg-distribʳ-* r d) (neg-distribʳ-* r e) (neg-distribʳ-* r f)

------------------------------------------------------------------------
-- Additive and scalar linearity in the second argument
-- 第二参数的加法与数乘线性
------------------------------------------------------------------------

-- {f, g + h} = {f, g} + {f, h}.
-- {f, g + h} = {f, g} + {f, h}。
bracket-addʳ : ∀ f g h →
               bracket f (add g h) ≡ add (bracket f g) (bracket f h)
bracket-addʳ f g h = let open ≡-Reasoning in begin
    bracket f (add g h)
  ≡⟨ bracket-skew (add g h) f ⟩
    neg (bracket (add g h) f)
  ≡⟨ cong neg (bracket-addˡ g h f) ⟩
    neg (add (bracket g f) (bracket h f))
  ≡⟨ neg-add (bracket g f) (bracket h f) ⟩
    add (neg (bracket g f)) (neg (bracket h f))
  ≡⟨ cong₂ add (sym (bracket-skew g f)) (sym (bracket-skew h f)) ⟩
    add (bracket f g) (bracket f h) ∎

-- {f, r g} = r {f, g}.
-- {f, r g} = r {f, g}。
bracket-scaleʳ : ∀ r f g →
                 bracket f (scale r g) ≡ scale r (bracket f g)
bracket-scaleʳ r f g = let open ≡-Reasoning in begin
    bracket f (scale r g)
  ≡⟨ bracket-skew (scale r g) f ⟩
    neg (bracket (scale r g) f)
  ≡⟨ cong neg (bracket-scaleˡ r g f) ⟩
    neg (scale r (bracket g f))
  ≡⟨ neg-scale r (bracket g f) ⟩
    scale r (neg (bracket g f))
  ≡⟨ cong (scale r) (sym (bracket-skew g f)) ⟩
    scale r (bracket f g) ∎
