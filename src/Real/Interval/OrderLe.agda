------------------------------------------------------------------------
-- Non-strict order laws for _≤ℝ_
--
-- 非严格序 _≤ℝ_ 的定律
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module Real.Interval.OrderLe where

open import Data.Empty using (⊥-elim)
open import Data.Product using (_×_; _,_)
open import Data.Sum using (inj₁; inj₂)
open import Data.Rational using
  (ℚ; 0ℚ; _+_; _-_; _*_; _≤_; ∣_∣) renaming (-_ to neg)
open import Data.Rational.Properties using
  (≤-refl; ≤-reflexive; +-mono-≤; +-assoc; +-comm; +-identityˡ
  ; +-identityʳ; +-inverseˡ; +-inverseʳ; *-distribʳ-+; neg-antimono-≤; neg-distrib-+
  ; ∣p∣≡p∨∣p∣≡-p)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; sym; cong; cong₂; module ≡-Reasoning)
open ≡-Reasoning

open import Base.RationalRing using (neg-involutive)
open import Real.Interval using (RealI)
open import Real.Interval.Arith using (_+ℝ_; negℝ; _-ℝ_)
open import Real.Interval.Equiv using (_≈ℝ_; ≈ℝ-sym)
open import Real.IntervalEquiv using
  (l; u; centre; width; width-n; centre-l; centre-u; recipPow2)
open import Real.Interval.Order using (_<ℝ_; <-irrefl; <-trans; <-cotrans)
open import Real.Interval.OrderComplete.Base using (_≤ℝ_)
open import Real.Interval.Node using (0≤width-n; centre-add; centre-neg)
open import Real.Interval.Kit using (≈ℝ-of-rec; ≈ℝ-of-eq)
open import Real.Interval.Rational using (¬<⇒≥)
open import Real.Interval.OrderLaws using (≈-<-resp; <-sub)
open import Real.Interval.Mul.Order using (≈-<-respʳ)
open import Real.Interval.Reasoning using (begin≤_; _≤⟨_⟩_; _≤∎)

------------------------------------------------------------------------
-- Rational arithmetic helpers
--
-- 有理数算术辅助

-- Monotonicity of subtraction.
--
-- 减法的单调性。
sub-mono : {a a' b b' : ℚ} → a ≤ a' → b' ≤ b → a - b ≤ a' - b'
sub-mono {a} {a'} {b} {b'} p q = begin≤
  a - b
    ≤⟨ +-mono-≤ p (≤-refl {neg b}) ⟩
  a' - b
    ≤⟨ +-mono-≤ (≤-refl {a'}) (neg-antimono-≤ q) ⟩
  a' - b'
  ≤∎

-- Subtracting a fixed term.
--
-- 减去固定项。
sub-fixed : {a b c : ℚ} → a ≤ b → a - c ≤ b - c
sub-fixed {a} {b} {c} p = begin≤
  a - c
    ≤⟨ +-mono-≤ p (≤-refl {neg c}) ⟩
  b - c
  ≤∎

-- Reassociation of a two-step difference.
--
-- 两步差重新结合。
reassoc : (a b c : ℚ) → (a - b) + (b - c) ≡ a - c
reassoc a b c =
  begin
    (a - b) + (b - c)
      ≡⟨ +-assoc a (neg b) (b - c) ⟩
    a + (neg b + (b - c))
      ≡⟨ cong (a +_) (sym (+-assoc (neg b) b (neg c))) ⟩
    a + ((neg b + b) + neg c)
      ≡⟨ cong (a +_) (cong (_+ neg c) (+-inverseˡ b)) ⟩
    a + (0ℚ + neg c)
      ≡⟨ cong (a +_) (+-identityˡ (neg c)) ⟩
    a - c
  ∎

-- Negation flips a difference.
--
-- 取负翻转差值。
neg-diff-flip : (a b : ℚ) → neg (a - b) ≡ b - a
neg-diff-flip a b =
  begin
    neg (a - b)
      ≡⟨ neg-distrib-+ a (neg b) ⟩
    neg a + neg (neg b)
      ≡⟨ cong (neg a +_) (neg-involutive b) ⟩
    neg a + b
      ≡⟨ +-comm (neg a) b ⟩
    b + neg a
      ≡⟨⟩
    b - a
  ∎

------------------------------------------------------------------------
-- Basic laws of _≤ℝ_
--
-- _≤ℝ_ 的基本定律

-- Reflexivity.
--
-- 自反性。
≤ℝ-refl : {x : RealI} → x ≤ℝ x
≤ℝ-refl {x} = <-irrefl x

-- Transitivity, by cotransitivity of _<ℝ_.
--
-- 传递性，借助 _<ℝ_ 的余传递性。
≤ℝ-trans : {x y z : RealI} → x ≤ℝ y → y ≤ℝ z → x ≤ℝ z
≤ℝ-trans {x} {y} {z} x≤y y≤z z<x
  with <-cotrans z<x
...  | inj₁ z<y = y≤z z<y
...  | inj₂ y<x = x≤y y<x

-- Strict order embeds into non-strict order.
--
-- 严格序嵌入非严格序。
<⇒≤ℝ : {x y : RealI} → x <ℝ y → x ≤ℝ y
<⇒≤ℝ {x} x<y y<x = <-irrefl x (<-trans x<y y<x)

-- Equality embeds into non-strict order.
--
-- 相等嵌入非严格序。
≈⇒≤ℝ : {x y : RealI} → x ≈ℝ y → x ≤ℝ y
≈⇒≤ℝ {x} {y} x≈y y<x =
  <-irrefl x (≈-<-resp (≈ℝ-sym x≈y) y<x)

-- Strict order excludes the reverse non-strict order.
--
-- 严格序排除反向的非严格序。
<⇒¬≤ℝ : {x y : RealI} → x <ℝ y → ¬ (y ≤ℝ x)
<⇒¬≤ℝ x<y y≤x = y≤x x<y

------------------------------------------------------------------------
-- Antisymmetry
--
-- 反对称性

-- Two mutually non-strictly ordered reals are approximately equal. The
-- proof bounds the centre difference by the sum of the two layer widths,
-- which shrinks geometrically.
--
-- 互相非严格序控制的两实数近似相等。证明把中心差界为两层宽度之和，
-- 而该和随层数几何衰减。

module AntisymAux (x y : RealI)
  (x≤y : x ≤ℝ y) (y≤x : y ≤ℝ x) where

  gap1 : ∀ n → l x n ≤ u y n
  gap1 n = ¬<⇒≥ (λ hyp → x≤y (n , hyp))

  gap2 : ∀ n → l y n ≤ u x n
  gap2 n = ¬<⇒≥ (λ hyp → y≤x (n , hyp))

  -- Forward centre difference bound.
  --
  -- 正向中心差界。
  cx-cy≤ : ∀ n → centre x n - centre y n ≤ width x n + width y n
  cx-cy≤ n =
    begin≤
      centre x n - centre y n
        ≤⟨ sub-mono (centre-u x n) (centre-l y n) ⟩
      u x n - l y n
        ≤⟨ ≤-reflexive (sym (reassoc (u x n) (l x n) (l y n))) ⟩
      (u x n - l x n) + (l x n - l y n)
        ≤⟨ +-mono-≤
              (≤-reflexive (refl {x = u x n - l x n}))
              (sub-fixed {a = l x n} {b = u y n} {c = l y n} (gap1 n)) ⟩
      (u x n - l x n) + (u y n - l y n)
        ≤⟨ ≤-reflexive (refl {x = (u x n - l x n) + (u y n - l y n)}) ⟩
      width x n + width y n
    ≤∎

  -- Backward centre difference bound.
  --
  -- 反向中心差界。
  cy-cx≤ : ∀ n → centre y n - centre x n ≤ width y n + width x n
  cy-cx≤ n =
    begin≤
      centre y n - centre x n
        ≤⟨ sub-mono (centre-u y n) (centre-l x n) ⟩
      u y n - l x n
        ≤⟨ ≤-reflexive (sym (reassoc (u y n) (l y n) (l x n))) ⟩
      (u y n - l y n) + (l y n - l x n)
        ≤⟨ +-mono-≤
              (≤-reflexive (refl {x = u y n - l y n}))
              (sub-fixed {a = l y n} {b = u x n} {c = l x n} (gap2 n)) ⟩
      (u y n - l y n) + (u x n - l x n)
        ≤⟨ ≤-reflexive (refl {x = (u y n - l y n) + (u x n - l x n)}) ⟩
      width y n + width x n
    ≤∎

  -- Absolute centre difference bound.
  --
  -- 中心差的绝对值界。
  abs≤ : ∀ n → ∣ centre x n - centre y n ∣ ≤ width x n + width y n
  abs≤ n with ∣p∣≡p∨∣p∣≡-p (centre x n - centre y n)
  ... | inj₁ eq = begin≤
        ∣ centre x n - centre y n ∣
          ≤⟨ ≤-reflexive eq ⟩
        centre x n - centre y n
          ≤⟨ cx-cy≤ n ⟩
        width x n + width y n
        ≤∎
  ... | inj₂ eq = begin≤
        ∣ centre x n - centre y n ∣
          ≤⟨ ≤-reflexive eq ⟩
        neg (centre x n - centre y n)
          ≤⟨ ≤-reflexive (neg-diff-flip (centre x n) (centre y n)) ⟩
        centre y n - centre x n
          ≤⟨ cy-cx≤ n ⟩
        width y n + width x n
          ≤⟨ ≤-reflexive (+-comm (width y n) (width x n)) ⟩
        width x n + width y n
        ≤∎

  C : ℚ
  C = width x 0 + width y 0

  -- Nonnegativity of the geometric constant.
  --
  -- 几何常数的非负性。
  0≤C : 0ℚ ≤ C
  0≤C = begin≤
    0ℚ
      ≤⟨ +-mono-≤ (0≤width-n x 0) (0≤width-n y 0) ⟩
    width x 0 + width y 0
    ≤∎

  -- Geometric bound on the width sum.
  --
  -- 宽度和的几何界。
  geo≤ : ∀ n → width x n + width y n ≤ C * recipPow2 n
  geo≤ n =
    begin≤
      width x n + width y n
        ≤⟨ +-mono-≤ (width-n x n) (width-n y n) ⟩
      (width x 0 * recipPow2 n) + (width y 0 * recipPow2 n)
        ≤⟨ ≤-reflexive (sym (*-distribʳ-+ (recipPow2 n) (width x 0) (width y 0))) ⟩
      C * recipPow2 n
    ≤∎

  -- Combine the absolute bound with the geometric bound.
  --
  -- 绝对值界与几何界的合成。
  body : ∀ n →
    ∣ centre x n - centre y n ∣ ≤ C * recipPow2 n
  body n = begin≤
    ∣ centre x n - centre y n ∣
      ≤⟨ abs≤ n ⟩
    width x n + width y n
      ≤⟨ geo≤ n ⟩
    C * recipPow2 n
    ≤∎

-- Antisymmetry.
--
-- 反对称性。
≤ℝ-antisym : {x y : RealI} → x ≤ℝ y → y ≤ℝ x → x ≈ℝ y
≤ℝ-antisym {x} {y} x≤y y≤x =
  ≈ℝ-of-rec x y (AntisymAux.C x y x≤y y≤x)
               (AntisymAux.0≤C x y x≤y y≤x)
               (AntisymAux.body x y x≤y y≤x)

------------------------------------------------------------------------
-- Equality versus non-strict order
--
-- 相等与非严格序的关系

-- Equality gives both non-strict orders.
--
-- 相等同时给出双向的非严格序。
≈⇒≤ℝ∧ : {x y : RealI} → x ≈ℝ y → (x ≤ℝ y) × (y ≤ℝ x)
≈⇒≤ℝ∧ x≈y = ≈⇒≤ℝ x≈y , ≈⇒≤ℝ (≈ℝ-sym x≈y)

-- Replacement of _≤ℝ_ under _≈ℝ_.
--
-- _≤ℝ_ 在 _≈ℝ_ 下的替换律。
≤ℝ-resp-≈ : {x x' y y' : RealI} →
  x ≈ℝ x' → y ≈ℝ y' → x ≤ℝ y → x' ≤ℝ y'
≤ℝ-resp-≈ {x} {x'} {y} {y'} x≈x' y≈y' x≤y y'<x' =
  x≤y (≈-<-respʳ (≈ℝ-sym x≈x')
        (≈-<-resp (≈ℝ-sym y≈y') y'<x'))

------------------------------------------------------------------------
-- Coupling of strict and non-strict order
--
-- 严格序与非严格序的耦合

-- Strict-then-non-strict transitivity.
--
-- 严格序后接非严格序的复合传递性。
<-≤ℝ-trans : {x y z : RealI} → x <ℝ y → y ≤ℝ z → x <ℝ z
<-≤ℝ-trans {x} {y} {z} x<y y≤z
  with <-cotrans x<y
...  | inj₁ x<z = x<z
...  | inj₂ z<y = ⊥-elim (y≤z z<y)

-- Non-strict-then-strict transitivity.
--
-- 非严格序后接严格序的复合传递性。
≤ℝ-<trans : {x y z : RealI} → x ≤ℝ y → y <ℝ z → x <ℝ z
≤ℝ-<trans {x} {y} {z} x≤y y<z
  with <-cotrans y<z
...  | inj₁ y<x = ⊥-elim (x≤y y<x)
...  | inj₂ x<z = x<z

------------------------------------------------------------------------
-- Additive monotonicity of _≤ℝ_
--
-- _≤ℝ_ 的加法单调性

-- Adding then subtracting the same term is the identity.
--
-- 加后再减同一项等于恒等。
+-cancelʳ : (a b : RealI) → (a +ℝ b) -ℝ b ≈ℝ a
+-cancelʳ a b = ≈ℝ-of-eq ((a +ℝ b) -ℝ b) a λ n →
  begin
    centre ((a +ℝ b) -ℝ b) n
      ≡⟨ centre-add (a +ℝ b) (negℝ b) n ⟩
    centre (a +ℝ b) n + centre (negℝ b) n
      ≡⟨ cong₂ _+_ (centre-add a b n) (centre-neg b n) ⟩
    (centre a n + centre b n) + neg (centre b n)
      ≡⟨ +-assoc (centre a n) (centre b n) (neg (centre b n)) ⟩
    centre a n + (centre b n + neg (centre b n))
      ≡⟨ cong (centre a n +_) (+-inverseʳ (centre b n)) ⟩
    centre a n + 0ℚ
      ≡⟨ +-identityʳ (centre a n) ⟩
    centre a n
  ∎

-- Strict order is reflected by adding a common term.
--
-- 加上同一项后严格序可反向。
<-+mono-reflect : {x y z : RealI} → y +ℝ z <ℝ x +ℝ z → y <ℝ x
<-+mono-reflect {x} {y} {z} h =
  ≈-<-respʳ (+-cancelʳ x z)
    (≈-<-resp (+-cancelʳ y z) (<-sub (y +ℝ z) (x +ℝ z) z h))

-- Additive monotonicity.
--
-- 加法单调性。
≤ℝ-+-mono : {x y z : RealI} → x ≤ℝ y → x +ℝ z ≤ℝ y +ℝ z
≤ℝ-+-mono {x} {y} {z} x≤y y+z<x+z =
  x≤y (<-+mono-reflect {x} {y} {z} y+z<x+z)
