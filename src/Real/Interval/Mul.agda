------------------------------------------------------------------------
-- Interval multiplication
--
-- 区间乘法
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module Real.Interval.Mul where

open import Data.Rational using
  (ℚ; 0ℚ; 1ℚ; _⊓_; _⊔_; _+_; _-_; _*_; _≤_; _<_; ∣_∣; NonNegative; positive
  ; nonNegative; nonPositive)
open import Data.Rational.Base using (_÷_; 1/_) renaming (-_ to neg)
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Data.Empty using (⊥-elim)
open import Data.Rational.Properties using
  (+-mono-≤; +-mono-≤-<; +-assoc; +-comm; +-identityʳ; +-identityˡ; +-inverseʳ
  ; +-inverseˡ; *-assoc; *-comm; *-distribʳ-+; *-distribˡ-+; neg-distribˡ-*
  ; neg-distribʳ-*; ≤-refl; ≤-reflexive; ≤-trans; ≤-antisym; ≤-total; <⇒≤
  ; <-≤-trans; *-monoʳ-≤-nonNeg; *-monoˡ-≤-nonNeg; *-monoʳ-≤-nonPos
  ; *-monoˡ-≤-nonPos; pos*pos⇒pos; positive⁻¹; <-cmp; *-identityˡ; *-inverseʳ
  ; *-zeroʳ; ∣p*q∣≡∣p∣*∣q∣; ∣p∣≡p∨∣p∣≡-p; ∣-p∣≡∣p∣; 0≤∣p∣
  ; 0≤p⇒∣p∣≡p; 1/pos⇒pos; p⊓q≤p; p⊓q≤q; p≤p⊔q; p≤q⊔p; p≤q⇒p⊔q≡q
  ; p≥q⇒p⊔q≡p; ⊓-glb; ⊔-lub; ⊔-mono-≤)
  renaming (<-irrefl to <-irreflℚ)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; cong; cong₂; sym; trans; subst; module ≡-Reasoning)
open ≡-Reasoning
open import Relation.Nullary.Negation using (¬_)
open import Relation.Binary.Definitions using (tri<; tri≈; tri>)

open import Real using (embed; 2ℚ; embed-suc-pos)
open import Real.Interval using (RealI)
open import Real.IntervalEquiv using (bounded-diff; mono-half)
open import Real.Interval.Rational using
  (pos-diff; sub-add; negsub; mag; mag-≤; r≤|r|)
open import Real.Interval.Kit using (add-self)
open import Real.Interval.Reasoning

------------------------------------------------------------------------
-- Basic lemmas
--
-- 基本引理

nn : ∀ {p : ℚ} → 0ℚ ≤ p → NonNegative p
nn = nonNegative

0≤mag : ∀ a b → 0ℚ ≤ mag a b
0≤mag a b = ≤-trans (0≤∣p∣ a) (p≤p⊔q ∣ a ∣ ∣ b ∣)

0≤diff : ∀ {a b : ℚ} → a ≤ b → 0ℚ ≤ b - a
0≤diff {a} {b} a≤b =
  subst (λ z → z ≤ b + neg a) (+-inverseʳ a)
        (+-mono-≤ a≤b (≤-refl {neg a}))

le-addˡ : ∀ {x y z : ℚ} → x ≤ z → 0ℚ ≤ y → x ≤ y + z
le-addˡ {x} {y} {z} x≤z 0≤y =
  ≤-trans x≤z (subst (λ w → w ≤ y + z) (+-identityˡ z)
                     (+-mono-≤ 0≤y (≤-refl {z})))

le-addʳ : ∀ {x y z : ℚ} → x ≤ y → 0ℚ ≤ z → x ≤ y + z
le-addʳ {x} {y} {z} x≤y 0≤z =
  ≤-trans x≤y (subst (λ w → w ≤ y + z) (+-identityʳ y)
                     (+-mono-≤ (≤-refl {y}) 0≤z))

cancelʳ : ∀ x y → (x - y) + y ≡ x
cancelʳ x y = begin
  (x - y) + y
    ≡⟨ +-assoc x (neg y) y ⟩
  x + (neg y + y)
    ≡⟨ cong (x +_) (+-inverseˡ y) ⟩
  x + 0ℚ
    ≡⟨ +-identityʳ x ⟩
  x
  ∎

cancel-z : ∀ z y → (z + y) - z ≡ y
cancel-z z y = begin
  (z + y) - z
    ≡⟨ +-assoc z y (neg z) ⟩
  z + (y + neg z)
    ≡⟨ cong (z +_) (+-comm y (neg z)) ⟩
  z + (neg z + y)
    ≡⟨ sym (+-assoc z (neg z) y) ⟩
  (z + neg z) + y
    ≡⟨ cong (_+ y) (+-inverseʳ z) ⟩
  0ℚ + y
    ≡⟨ +-identityˡ y ⟩
  y
  ∎

le-shift : ∀ {x y z : ℚ} → x - y ≤ z → x ≤ z + y
le-shift {x} {y} {z} h =
  subst (λ w → w ≤ z + y) (cancelʳ x y) (+-mono-≤ h (≤-refl {y}))

sub-mono : ∀ {a b c : ℚ} → a ≤ b → a - c ≤ b - c
sub-mono {a} {b} {c} h = +-mono-≤ h (≤-refl {neg c})

sub-swap : ∀ {x y z : ℚ} → x - y ≤ z → x - z ≤ y
sub-swap {x} {y} {z} h =
  ≤-trans (sub-mono {a = x} {b = z + y} {c = z} (le-shift h))
          (≤-reflexive (cancel-z z y))

mag-le : ∀ {l u l' u' : ℚ} → l ≤ l' → l' ≤ u' → u' ≤ u → mag l' u' ≤ mag l u
mag-le {l} {u} {l'} {u'} l≤l' l'≤u' u'≤u =
  ≤-trans (⊔-mono-≤ (mag-≤ l≤l' (≤-trans l'≤u' u'≤u))
                    (mag-≤ (≤-trans l≤l' l'≤u') u'≤u))
          (≤-reflexive (p≥q⇒p⊔q≡p {p = mag l u} {q = mag l u} ≤-refl))

-- Split on the sign of x; both sign branches are named arguments
-- rather than a with-clause at each use site.
--
-- 按 x 的符号分情况；两个符号分支作为命名参数给出，避免每个使用点都
-- 写一次 with。
sign-split : ∀ (x : ℚ) {P : Set}
           → (0ℚ ≤ x → P) → (x ≤ 0ℚ → P) → P
sign-split x nonneg nonpos with ≤-total x 0ℚ
... | inj₁ x≤0 = nonpos x≤0
... | inj₂ 0≤x = nonneg 0≤x

------------------------------------------------------------------------
-- Splitting a product and bounding a product difference
--
-- 乘积拆分与乘积之差的界

split-prod : ∀ a a' b b' → a * b - a' * b' ≡ a * (b - b') + (a - a') * b'
split-prod a a' b b' =
  sym
    (begin
       a * (b - b') + (a - a') * b'
     ≡⟨ cong₂ _+_ s1 s2 ⟩
       (a * b + neg (a * b')) + (a * b' + neg (a' * b'))
     ≡⟨ sym (+-assoc (a * b + neg (a * b')) (a * b') (neg (a' * b'))) ⟩
       ((a * b + neg (a * b')) + a * b') + neg (a' * b')
     ≡⟨ cong (λ z → z + neg (a' * b'))
             (+-assoc (a * b) (neg (a * b')) (a * b')) ⟩
       (a * b + (neg (a * b') + a * b')) + neg (a' * b')
     ≡⟨ cong (λ z → (a * b + z) + neg (a' * b')) (+-inverseˡ (a * b')) ⟩
       (a * b + 0ℚ) + neg (a' * b')
     ≡⟨ cong (λ z → z + neg (a' * b')) (+-identityʳ (a * b)) ⟩
       a * b + neg (a' * b')
     ∎)
  where

    s1 : a * (b - b') ≡ a * b + neg (a * b')
    s1 =
      begin
        a * (b - b')
      ≡⟨ *-distribˡ-+ a b (neg b') ⟩
        a * b + a * neg b'
      ≡⟨ cong (a * b +_) (sym (neg-distribʳ-* a b')) ⟩
        a * b + neg (a * b')
      ∎

    s2 : (a - a') * b' ≡ a * b' + neg (a' * b')
    s2 =
      begin
        (a - a') * b'
      ≡⟨ *-distribʳ-+ b' a (neg a') ⟩
        a * b' + (neg a') * b'
      ≡⟨ cong (a * b' +_) (sym (neg-distribˡ-* a' b')) ⟩
        a * b' + neg (a' * b')
      ∎

-- Bound on the difference of two products, one-directional.
--
-- 两个乘积之差（单向）的界
prod-diff≤ : ∀ {l u l' u' a a' b b' : ℚ} →
  l ≤ a → a ≤ u → l ≤ a' → a' ≤ u →
  l' ≤ b → b ≤ u' → l' ≤ b' → b' ≤ u' →
  a * b - a' * b' ≤ mag l u * (u' - l') + (u - l) * mag l' u'
prod-diff≤ {l} {u} {l'} {u'} {a} {a'} {b} {b'}
           l≤a a≤u l≤a' a'≤u l'≤b b≤u' l'≤b' b'≤u' =
  begin≤
    a * b - a' * b'
      ≈⟨ split-prod a a' b b' ⟩
    a * (b - b') + (a - a') * b'
      ≤⟨ +-mono-≤ stepA stepB ⟩
    U * W' + W * U'
  ≤∎
  where
    U = mag l u
    U' = mag l' u'
    W = u - l
    W' = u' - l'

    0≤U : 0ℚ ≤ U
    0≤U = 0≤mag l u

    0≤W : 0ℚ ≤ W
    0≤W = 0≤diff (≤-trans l≤a a≤u)

    stepA : a * (b - b') ≤ U * W'
    stepA =
      begin≤
        a * (b - b')
          ≤⟨ r≤|r| (a * (b - b')) ⟩
        ∣ a * (b - b') ∣
          ≈⟨ ∣p*q∣≡∣p∣*∣q∣ a (b - b') ⟩
        ∣ a ∣ * ∣ b - b' ∣
          ≤⟨ *-monoʳ-≤-nonNeg ∣ b - b' ∣ {{nn (0≤∣p∣ (b - b'))}}
                                  (mag-≤ l≤a a≤u) ⟩
        U * ∣ b - b' ∣
          ≤⟨ *-monoˡ-≤-nonNeg U {{nn 0≤U}}
                                  (bounded-diff l'≤b b≤u' l'≤b' b'≤u') ⟩
        U * W'
      ≤∎

    stepB : (a - a') * b' ≤ W * U'
    stepB =
      begin≤
        (a - a') * b'
          ≤⟨ r≤|r| ((a - a') * b') ⟩
        ∣ (a - a') * b' ∣
          ≈⟨ ∣p*q∣≡∣p∣*∣q∣ (a - a') b' ⟩
        ∣ a - a' ∣ * ∣ b' ∣
          ≤⟨ *-monoʳ-≤-nonNeg ∣ b' ∣ {{nn (0≤∣p∣ b')}}
                                  (bounded-diff l≤a a≤u l≤a' a'≤u) ⟩
        W * ∣ b' ∣
          ≤⟨ *-monoˡ-≤-nonNeg W {{nn 0≤W}} (mag-≤ l'≤b' b'≤u') ⟩
        W * U'
      ≤∎

-- Bound on the difference of two products, two-directional.
--
-- 两个乘积之差的界（双向）
prod-diff : ∀ {l u l' u' a a' b b' : ℚ} →
  l ≤ a → a ≤ u → l ≤ a' → a' ≤ u →
  l' ≤ b → b ≤ u' → l' ≤ b' → b' ≤ u' →
  ∣ a * b - a' * b' ∣ ≤ mag l u * (u' - l') + (u - l) * mag l' u'
prod-diff {l} {u} {l'} {u'} {a} {a'} {b} {b'}
          l≤a a≤u l≤a' a'≤u l'≤b b≤u' l'≤b' b'≤u'
  with ∣p∣≡p∨∣p∣≡-p (a * b - a' * b')
... | inj₁ e =
      begin≤
        ∣ a * b - a' * b' ∣
          ≈⟨ e ⟩
        a * b - a' * b'
          ≤⟨ prod-diff≤ l≤a a≤u l≤a' a'≤u l'≤b b≤u' l'≤b' b'≤u' ⟩
        mag l u * (u' - l') + (u - l) * mag l' u'
      ≤∎
... | inj₂ e =
      begin≤
        ∣ a * b - a' * b' ∣
          ≈⟨ trans e (negsub (a * b) (a' * b')) ⟩
        a' * b' - a * b
          ≤⟨ prod-diff≤ l≤a' a'≤u l≤a a≤u l'≤b' b'≤u' l'≤b b≤u' ⟩
        mag l u * (u' - l') + (u - l) * mag l' u'
      ≤∎

------------------------------------------------------------------------
-- Four corners of an interval product
--
-- X = [lx, ux], Y = [ly, uy]; lo4 / hi4 are the minimum and maximum
-- of the four corner products, i.e. the two endpoints of the product
-- interval [lo4, hi4].
--
-- 区间乘积的四角
--
-- X = [lx,ux]、Y = [ly,uy]；lo4 / hi4 是四角乘积的最小 / 最大，即乘
-- 积区间 [lo4, hi4] 的两个端点。

module Corner (lx ux ly uy : ℚ) (lx≤ux : lx ≤ ux) (ly≤uy : ly ≤ uy) where

  c1 c2 c3 c4 : ℚ
  c1 = lx * ly
  c2 = lx * uy
  c3 = ux * ly
  c4 = ux * uy

  lo4 hi4 : ℚ
  lo4 = (c1 ⊓ c2) ⊓ (c3 ⊓ c4)
  hi4 = (c1 ⊔ c2) ⊔ (c3 ⊔ c4)

  lo4≤c1 : lo4 ≤ c1
  lo4≤c1 = ≤-trans (p⊓q≤p (c1 ⊓ c2) (c3 ⊓ c4)) (p⊓q≤p c1 c2)

  lo4≤c2 : lo4 ≤ c2
  lo4≤c2 = ≤-trans (p⊓q≤p (c1 ⊓ c2) (c3 ⊓ c4)) (p⊓q≤q c1 c2)

  lo4≤c3 : lo4 ≤ c3
  lo4≤c3 = ≤-trans (p⊓q≤q (c1 ⊓ c2) (c3 ⊓ c4)) (p⊓q≤p c3 c4)

  lo4≤c4 : lo4 ≤ c4
  lo4≤c4 = ≤-trans (p⊓q≤q (c1 ⊓ c2) (c3 ⊓ c4)) (p⊓q≤q c3 c4)

  c1≤hi4 : c1 ≤ hi4
  c1≤hi4 = ≤-trans (p≤p⊔q c1 c2) (p≤p⊔q (c1 ⊔ c2) (c3 ⊔ c4))

  c2≤hi4 : c2 ≤ hi4
  c2≤hi4 = ≤-trans (p≤q⊔p c1 c2) (p≤p⊔q (c1 ⊔ c2) (c3 ⊔ c4))

  c3≤hi4 : c3 ≤ hi4
  c3≤hi4 = ≤-trans (p≤p⊔q c3 c4) (p≤q⊔p (c1 ⊔ c2) (c3 ⊔ c4))

  c4≤hi4 : c4 ≤ hi4
  c4≤hi4 = ≤-trans (p≤q⊔p c3 c4) (p≤q⊔p (c1 ⊔ c2) (c3 ⊔ c4))

  lo4≤hi4 : lo4 ≤ hi4
  lo4≤hi4 = ≤-trans lo4≤c1 c1≤hi4

  -- Any product of interval points lies between lo4 and hi4.
  --
  -- 四角夹住区间中的任意乘积。
  lo4≤prod-+ : ∀ {a b : ℚ} → 0ℚ ≤ b → lx ≤ a → a ≤ ux → ly ≤ b → b ≤ uy →
               lo4 ≤ a * b
  lo4≤prod-+ {a} {b} 0≤b l≤a a≤u l'≤b b≤u' =
    sign-split lx
      (λ 0≤lx →
        begin≤
          lo4
            ≤⟨ lo4≤c1 ⟩
          c1
            ≤⟨ *-monoˡ-≤-nonNeg lx {{nn 0≤lx}} l'≤b ⟩
          lx * b
            ≤⟨ *-monoʳ-≤-nonNeg b {{nn 0≤b}} l≤a ⟩
          a * b
        ≤∎)
      (λ lx≤0 →
        begin≤
          lo4
            ≤⟨ lo4≤c2 ⟩
          c2
            ≤⟨ *-monoˡ-≤-nonPos lx {{nonPositive lx≤0}} b≤u' ⟩
          lx * b
            ≤⟨ *-monoʳ-≤-nonNeg b {{nn 0≤b}} l≤a ⟩
          a * b
        ≤∎)

  lo4≤prod- : ∀ {a b : ℚ} → b ≤ 0ℚ → lx ≤ a → a ≤ ux → ly ≤ b → b ≤ uy →
              lo4 ≤ a * b
  lo4≤prod- {a} {b} b≤0 l≤a a≤u l'≤b b≤u' =
    sign-split ux
      (λ 0≤ux →
        begin≤
          lo4
            ≤⟨ lo4≤c3 ⟩
          c3
            ≤⟨ *-monoˡ-≤-nonNeg ux {{nn 0≤ux}} l'≤b ⟩
          ux * b
            ≤⟨ *-monoʳ-≤-nonPos b {{nonPositive b≤0}} a≤u ⟩
          a * b
        ≤∎)
      (λ ux≤0 →
        begin≤
          lo4
            ≤⟨ lo4≤c4 ⟩
          c4
            ≤⟨ *-monoˡ-≤-nonPos ux {{nonPositive ux≤0}} b≤u' ⟩
          ux * b
            ≤⟨ *-monoʳ-≤-nonPos b {{nonPositive b≤0}} a≤u ⟩
          a * b
        ≤∎)

  lo4≤prod : ∀ {a b : ℚ} → lx ≤ a → a ≤ ux → ly ≤ b → b ≤ uy → lo4 ≤ a * b
  lo4≤prod {a} {b} l≤a a≤u l'≤b b≤u' with ≤-total b 0ℚ
  ... | inj₁ b≤0 = lo4≤prod- b≤0 l≤a a≤u l'≤b b≤u'
  ... | inj₂ 0≤b = lo4≤prod-+ 0≤b l≤a a≤u l'≤b b≤u'

  prod≤hi4-+ : ∀ {a b : ℚ} → 0ℚ ≤ b → lx ≤ a → a ≤ ux → ly ≤ b → b ≤ uy →
               a * b ≤ hi4
  prod≤hi4-+ {a} {b} 0≤b l≤a a≤u l'≤b b≤u' =
    sign-split ux
      (λ 0≤ux →
        begin≤
          a * b
            ≤⟨ *-monoʳ-≤-nonNeg b {{nn 0≤b}} a≤u ⟩
          ux * b
            ≤⟨ *-monoˡ-≤-nonNeg ux {{nn 0≤ux}} b≤u' ⟩
          c4
            ≤⟨ c4≤hi4 ⟩
          hi4
        ≤∎)
      (λ ux≤0 →
        begin≤
          a * b
            ≤⟨ *-monoʳ-≤-nonNeg b {{nn 0≤b}} a≤u ⟩
          ux * b
            ≤⟨ *-monoˡ-≤-nonPos ux {{nonPositive ux≤0}} l'≤b ⟩
          c3
            ≤⟨ c3≤hi4 ⟩
          hi4
        ≤∎)

  prod≤hi4- : ∀ {a b : ℚ} → b ≤ 0ℚ → lx ≤ a → a ≤ ux → ly ≤ b → b ≤ uy →
              a * b ≤ hi4
  prod≤hi4- {a} {b} b≤0 l≤a a≤u l'≤b b≤u' =
    sign-split lx
      (λ 0≤lx →
        begin≤
          a * b
            ≤⟨ *-monoʳ-≤-nonPos b {{nonPositive b≤0}} l≤a ⟩
          lx * b
            ≤⟨ *-monoˡ-≤-nonNeg lx {{nn 0≤lx}} b≤u' ⟩
          c2
            ≤⟨ c2≤hi4 ⟩
          hi4
        ≤∎)
      (λ lx≤0 →
        begin≤
          a * b
            ≤⟨ *-monoʳ-≤-nonPos b {{nonPositive b≤0}} l≤a ⟩
          lx * b
            ≤⟨ *-monoˡ-≤-nonPos lx {{nonPositive lx≤0}} l'≤b ⟩
          c1
            ≤⟨ c1≤hi4 ⟩
          hi4
        ≤∎)

  prod≤hi4 : ∀ {a b : ℚ} → lx ≤ a → a ≤ ux → ly ≤ b → b ≤ uy → a * b ≤ hi4
  prod≤hi4 {a} {b} l≤a a≤u l'≤b b≤u' with ≤-total b 0ℚ
  ... | inj₁ b≤0 = prod≤hi4- b≤0 l≤a a≤u l'≤b b≤u'
  ... | inj₂ 0≤b = prod≤hi4-+ 0≤b l≤a a≤u l'≤b b≤u'

  ----------------------------------------------------------------------
  -- Bound on the width
  --
  --   B = U_X · w_Y + U_Y · w_X
  --
  -- hi4 − lo4 ≤ B: the difference of any two corners is bounded by B,
  -- so every corner lies below lo4 + B. B ≤ 2 (hi4 − lo4): take the
  -- endpoint of largest |·| and multiply it with both endpoints of the
  -- other interval.
  --
  -- 宽度的界
  --
  -- hi4 − lo4 ≤ B：任意两角之差不超过 B，故四角皆被 lo4 + B 盖住。
  -- B ≤ 2 (hi4 − lo4)：取 |·| 最大的端点，与另一区间的两端作积。

  B : ℚ
  B = mag lx ux * (uy - ly) + mag ly uy * (ux - lx)

  -- Difference of an arbitrary pair of interval-point products.
  --
  -- 任意一对区间点之乘积之差。
  point-diff : ∀ {a a' b b' : ℚ} →
    lx ≤ a → a ≤ ux → lx ≤ a' → a' ≤ ux →
    ly ≤ b → b ≤ uy → ly ≤ b' → b' ≤ uy → a * b - a' * b' ≤ B
  point-diff {a} {a'} {b} {b'} l≤a a≤u l≤a' a'≤u l'≤b b≤u' l'≤b' b'≤u' =
    begin≤
      a * b - a' * b'
        ≤⟨ r≤|r| (a * b - a' * b') ⟩
      ∣ a * b - a' * b' ∣
        ≤⟨ prod-diff l≤a a≤u l≤a' a'≤u l'≤b b≤u' l'≤b' b'≤u' ⟩
      mag lx ux * (uy - ly) + (ux - lx) * mag ly uy
        ≈⟨ cong (λ z → mag lx ux * (uy - ly) + z)
                (*-comm (ux - lx) (mag ly uy)) ⟩
      mag lx ux * (uy - ly) + mag ly uy * (ux - lx)
    ≤∎

  -- Every corner is covered by lo4 + B.
  --
  -- 每个角都被 lo4 + B 盖住。
  corner≤ : ∀ {a b : ℚ} → lx ≤ a → a ≤ ux → ly ≤ b → b ≤ uy →
            a * b ≤ lo4 + B
  corner≤ {a} {b} l≤a a≤u l'≤b b≤u' =
    le-shift {x = a * b} {y = B} {z = lo4}
             (⊓-glb (⊓-glb g1 g2) (⊓-glb g3 g4))
    where
      g1 : a * b - B ≤ c1
      g1 = sub-swap {x = a * b} {y = c1} {z = B}
             (point-diff {a' = lx} {b' = ly} l≤a a≤u ≤-refl lx≤ux
                         l'≤b b≤u' ≤-refl ly≤uy)
      g2 : a * b - B ≤ c2
      g2 = sub-swap {x = a * b} {y = c2} {z = B}
             (point-diff {a' = lx} {b' = uy} l≤a a≤u ≤-refl lx≤ux
                         l'≤b b≤u' ly≤uy ≤-refl)
      g3 : a * b - B ≤ c3
      g3 = sub-swap {x = a * b} {y = c3} {z = B}
             (point-diff {a' = ux} {b' = ly} l≤a a≤u lx≤ux ≤-refl
                         l'≤b b≤u' ≤-refl ly≤uy)
      g4 : a * b - B ≤ c4
      g4 = sub-swap {x = a * b} {y = c4} {z = B}
             (point-diff {a' = ux} {b' = uy} l≤a a≤u lx≤ux ≤-refl
                         l'≤b b≤u' ly≤uy ≤-refl)

  spanB : hi4 - lo4 ≤ B
  spanB =
    ≤-trans (sub-mono {a = hi4} {b = lo4 + B} {c = lo4}
              (⊔-lub (⊔-lub h1 h2) (⊔-lub h3 h4)))
            (≤-reflexive (cancel-z lo4 B))
    where
      h1 : c1 ≤ lo4 + B
      h1 = corner≤ ≤-refl lx≤ux ≤-refl ly≤uy
      h2 : c2 ≤ lo4 + B
      h2 = corner≤ ≤-refl lx≤ux ly≤uy ≤-refl
      h3 : c3 ≤ lo4 + B
      h3 = corner≤ lx≤ux ≤-refl ≤-refl ly≤uy
      h4 : c4 ≤ lo4 + B
      h4 = corner≤ lx≤ux ≤-refl ly≤uy ≤-refl

  -- Two ways to write a corner difference.
  --
  -- 角差的两写法。
  c1-c2≡ : c1 - c2 ≡ lx * (ly - uy)
  c1-c2≡ = begin
    c1 - c2
      ≡⟨ cong (lx * ly +_) (neg-distribʳ-* lx uy) ⟩
    lx * ly + lx * neg uy
      ≡⟨ sym (*-distribˡ-+ lx ly (neg uy)) ⟩
    lx * (ly - uy)
    ∎

  c3-c4≡ : c3 - c4 ≡ ux * (ly - uy)
  c3-c4≡ = begin
    c3 - c4
      ≡⟨ cong (ux * ly +_) (neg-distribʳ-* ux uy) ⟩
    ux * ly + ux * neg uy
      ≡⟨ sym (*-distribˡ-+ ux ly (neg uy)) ⟩
    ux * (ly - uy)
    ∎

  c1-c3≡ : c1 - c3 ≡ (lx - ux) * ly
  c1-c3≡ = begin
    c1 - c3
      ≡⟨ cong (lx * ly +_) (neg-distribˡ-* ux ly) ⟩
    lx * ly + (neg ux) * ly
      ≡⟨ sym (*-distribʳ-+ ly lx (neg ux)) ⟩
    (lx - ux) * ly
    ∎

  c2-c4≡ : c2 - c4 ≡ (lx - ux) * uy
  c2-c4≡ = begin
    c2 - c4
      ≡⟨ cong (lx * uy +_) (neg-distribˡ-* ux uy) ⟩
    lx * uy + (neg ux) * uy
      ≡⟨ sym (*-distribʳ-+ uy lx (neg ux)) ⟩
    (lx - ux) * uy
    ∎

  -- Absolute-value normalisation.
  --
  -- 绝对值化归。
  abs-lo-hi : ∣ ly - uy ∣ ≡ uy - ly
  abs-lo-hi = begin
    ∣ ly - uy ∣
      ≡⟨ cong ∣_∣ (sym (negsub uy ly)) ⟩
    ∣ neg (uy - ly) ∣
      ≡⟨ ∣-p∣≡∣p∣ (uy - ly) ⟩
    ∣ uy - ly ∣
      ≡⟨ 0≤p⇒∣p∣≡p {uy - ly} (0≤diff ly≤uy) ⟩
    uy - ly
    ∎

  abs-hi-lo : ∣ lx - ux ∣ ≡ ux - lx
  abs-hi-lo = begin
    ∣ lx - ux ∣
      ≡⟨ cong ∣_∣ (sym (negsub ux lx)) ⟩
    ∣ neg (ux - lx) ∣
      ≡⟨ ∣-p∣≡∣p∣ (ux - lx) ⟩
    ∣ ux - lx ∣
      ≡⟨ 0≤p⇒∣p∣≡p {ux - lx} (0≤diff lx≤ux) ⟩
    ux - lx
    ∎

  -- Lower bound: U_X · w_Y ≤ hi4 − lo4.
  --
  -- 下界：U_X · w_Y ≤ hi4 − lo4。
  mag-widthˡ : mag lx ux * (uy - ly) ≤ hi4 - lo4
  mag-widthˡ with ≤-total ∣ ux ∣ ∣ lx ∣
  ... | inj₁ |ux|≤|lx| =
        begin≤
          mag lx ux * (uy - ly)
            ≈⟨ cong (λ z → z * (uy - ly))
                    (p≥q⇒p⊔q≡p {p = ∣ lx ∣} {q = ∣ ux ∣} |ux|≤|lx|) ⟩
          ∣ lx ∣ * (uy - ly)
            ≈⟨ sym (trans (cong ∣_∣ c1-c2≡)
                    (trans (∣p*q∣≡∣p∣*∣q∣ lx (ly - uy))
                           (cong (∣ lx ∣ *_) abs-lo-hi))) ⟩
          ∣ c1 - c2 ∣
            ≤⟨ bounded-diff lo4≤c1 c1≤hi4 lo4≤c2 c2≤hi4 ⟩
          hi4 - lo4
        ≤∎
  ... | inj₂ |lx|≤|ux| =
        begin≤
          mag lx ux * (uy - ly)
            ≈⟨ cong (λ z → z * (uy - ly))
                    (p≤q⇒p⊔q≡q {p = ∣ lx ∣} {q = ∣ ux ∣} |lx|≤|ux|) ⟩
          ∣ ux ∣ * (uy - ly)
            ≈⟨ sym (trans (cong ∣_∣ c3-c4≡)
                    (trans (∣p*q∣≡∣p∣*∣q∣ ux (ly - uy))
                           (cong (∣ ux ∣ *_) abs-lo-hi))) ⟩
          ∣ c3 - c4 ∣
            ≤⟨ bounded-diff lo4≤c3 c3≤hi4 lo4≤c4 c4≤hi4 ⟩
          hi4 - lo4
        ≤∎

  -- Lower bound: U_Y · w_X ≤ hi4 − lo4.
  --
  -- 下界：U_Y · w_X ≤ hi4 − lo4。
  mag-widthʳ : mag ly uy * (ux - lx) ≤ hi4 - lo4
  mag-widthʳ with ≤-total ∣ uy ∣ ∣ ly ∣
  ... | inj₁ |uy|≤|ly| =
        begin≤
          mag ly uy * (ux - lx)
            ≈⟨ trans (cong (λ z → z * (ux - lx))
                           (p≥q⇒p⊔q≡p {p = ∣ ly ∣} {q = ∣ uy ∣} |uy|≤|ly|))
                     (*-comm ∣ ly ∣ (ux - lx)) ⟩
          (ux - lx) * ∣ ly ∣
            ≈⟨ sym (trans (cong ∣_∣ c1-c3≡)
                    (trans (∣p*q∣≡∣p∣*∣q∣ (lx - ux) ly)
                           (cong (_* ∣ ly ∣) abs-hi-lo))) ⟩
          ∣ c1 - c3 ∣
            ≤⟨ bounded-diff lo4≤c1 c1≤hi4 lo4≤c3 c3≤hi4 ⟩
          hi4 - lo4
        ≤∎
  ... | inj₂ |ly|≤|uy| =
        begin≤
          mag ly uy * (ux - lx)
            ≈⟨ trans (cong (λ z → z * (ux - lx))
                           (p≤q⇒p⊔q≡q {p = ∣ ly ∣} {q = ∣ uy ∣} |ly|≤|uy|))
                     (*-comm ∣ uy ∣ (ux - lx)) ⟩
          (ux - lx) * ∣ uy ∣
            ≈⟨ sym (trans (cong ∣_∣ c2-c4≡)
                    (trans (∣p*q∣≡∣p∣*∣q∣ (lx - ux) uy)
                           (cong (_* ∣ uy ∣) abs-hi-lo))) ⟩
          ∣ c2 - c4 ∣
            ≤⟨ bounded-diff lo4≤c2 c2≤hi4 lo4≤c4 c4≤hi4 ⟩
          hi4 - lo4
        ≤∎

------------------------------------------------------------------------
-- Multiplication
--
-- 乘法

infixl 7 _*ℝ_

_*ℝ_ : RealI → RealI → RealI
RealI.l (x *ℝ y) =
  ((RealI.l x * RealI.l y) ⊓ (RealI.l x * RealI.u y))
    ⊓ ((RealI.u x * RealI.l y) ⊓ (RealI.u x * RealI.u y))
RealI.u (x *ℝ y) =
  ((RealI.l x * RealI.l y) ⊔ (RealI.l x * RealI.u y))
    ⊔ ((RealI.u x * RealI.l y) ⊔ (RealI.u x * RealI.u y))
RealI.lo (x *ℝ y) = lo<hi
  where

    lx = RealI.l x; ux = RealI.u x
    ly = RealI.l y; uy = RealI.u y

    open module C = Corner lx ux ly uy (<⇒≤ (RealI.lo x)) (<⇒≤ (RealI.lo y))

    step1 : lx * (ly - uy) ≡ (neg lx) * (uy - ly)
    step1 =
      begin
        lx * (ly - uy)
      ≡⟨ cong (lx *_) (sym (negsub uy ly)) ⟩
        lx * neg (uy - ly)
      ≡⟨ sym (neg-distribʳ-* lx (uy - ly)) ⟩
        neg (lx * (uy - ly))
      ≡⟨ neg-distribˡ-* lx (uy - ly) ⟩
        (neg lx) * (uy - ly)
      ∎

    c4-c3≡ : c4 - c3 ≡ ux * (uy - ly)
    c4-c3≡ =
      begin
        ux * uy - ux * ly
      ≡⟨ refl ⟩
        ux * uy + neg (ux * ly)
      ≡⟨ cong (ux * uy +_) (neg-distribʳ-* ux ly) ⟩
        ux * uy + ux * neg ly
      ≡⟨ sym (*-distribˡ-+ ux uy (neg ly)) ⟩
        ux * (uy + neg ly)
      ≡⟨ refl ⟩
        ux * (uy - ly)
      ∎

    key : (c1 + c4) - (c2 + c3) ≡ (ux - lx) * (uy - ly)
    key =
      begin
        (c1 + c4) - (c2 + c3)
      ≡⟨ sub-add c1 c4 c2 c3 ⟩
        (c1 - c2) + (c4 - c3)
      ≡⟨ cong₂ _+_ c1-c2≡ c4-c3≡ ⟩
        (lx * (ly - uy)) + (ux * (uy - ly))
      ≡⟨ cong (_+ ux * (uy - ly)) step1 ⟩
        ((neg lx) * (uy - ly)) + (ux * (uy - ly))
      ≡⟨ sym (*-distribʳ-+ (uy - ly) (neg lx) ux) ⟩
        ((neg lx) + ux) * (uy - ly)
      ≡⟨ cong (_* (uy - ly)) (+-comm (neg lx) ux) ⟩
        (ux - lx) * (uy - ly)
      ∎

    d1 d2 : ℚ
    d1 = ux - lx
    d2 = uy - ly

    d1>0 : 0ℚ < d1
    d1>0 = pos-diff lx ux (RealI.lo x)
    d2>0 : 0ℚ < d2
    d2>0 = pos-diff ly uy (RealI.lo y)

    d1d2>0 : 0ℚ < d1 * d2
    d1d2>0 = positive⁻¹ (d1 * d2)
      {{pos*pos⇒pos d1 {{positive d1>0}} d2 {{positive d2>0}}}}

    zero<diff : 0ℚ < (c1 + c4) - (c2 + c3)
    zero<diff = subst (λ z → 0ℚ < z) (sym key) d1d2>0

    sum-gt : c2 + c3 < c1 + c4
    sum-gt =
      subst (λ z → c2 + c3 < z) right-eq
        (subst (λ z → z < (c2 + c3) + ((c1 + c4) - (c2 + c3)))
               left-eq
               (+-mono-≤-< (≤-refl {c2 + c3}) zero<diff))
      where
        left-eq : (c2 + c3) + 0ℚ ≡ c2 + c3
        left-eq = +-identityʳ (c2 + c3)
        right-eq : (c2 + c3) + ((c1 + c4) - (c2 + c3)) ≡ c1 + c4
        right-eq =
          begin
            (c2 + c3) + ((c1 + c4) - (c2 + c3))
          ≡⟨ refl ⟩
            (c2 + c3) + ((c1 + c4) + neg (c2 + c3))
          ≡⟨ sym (+-assoc (c2 + c3) (c1 + c4) (neg (c2 + c3))) ⟩
            ((c2 + c3) + (c1 + c4)) + neg (c2 + c3)
          ≡⟨ cong (_+ neg (c2 + c3)) (+-comm (c2 + c3) (c1 + c4)) ⟩
            ((c1 + c4) + (c2 + c3)) + neg (c2 + c3)
          ≡⟨ +-assoc (c1 + c4) (c2 + c3) (neg (c2 + c3)) ⟩
            (c1 + c4) + ((c2 + c3) + neg (c2 + c3))
          ≡⟨ cong ((c1 + c4) +_) (+-inverseʳ (c2 + c3)) ⟩
            (c1 + c4) + 0ℚ
          ≡⟨ +-identityʳ (c1 + c4) ⟩
            c1 + c4
          ∎

    lo≠hi : ¬ (lo4 ≡ hi4)
    lo≠hi eq =
      let
        hi≤lo : hi4 ≤ lo4
        hi≤lo = ≤-reflexive (sym eq)

        c1≤lo : c1 ≤ lo4
        c1≤lo = ≤-trans c1≤hi4 hi≤lo
        c2≤lo : c2 ≤ lo4
        c2≤lo = ≤-trans c2≤hi4 hi≤lo
        c3≤lo : c3 ≤ lo4
        c3≤lo = ≤-trans c3≤hi4 hi≤lo
        c4≤lo : c4 ≤ lo4
        c4≤lo = ≤-trans c4≤hi4 hi≤lo

        c1≤c2 : c1 ≤ c2
        c1≤c2 = ≤-trans c1≤lo lo4≤c2
        c2≤c1 : c2 ≤ c1
        c2≤c1 = ≤-trans c2≤lo lo4≤c1
        c1≡c2 : c1 ≡ c2
        c1≡c2 = ≤-antisym c1≤c2 c2≤c1

        c3≤c4 : c3 ≤ c4
        c3≤c4 = ≤-trans c3≤lo lo4≤c4
        c4≤c3 : c4 ≤ c3
        c4≤c3 = ≤-trans c4≤lo lo4≤c3
        c3≡c4 : c3 ≡ c4
        c3≡c4 = ≤-antisym c3≤c4 c4≤c3

        eq-sum : c1 + c4 ≡ c2 + c3
        eq-sum = trans (cong (_+ c4) c1≡c2)
                       (cong (c2 +_) (sym c3≡c4))

        bad : c2 + c3 < c2 + c3
        bad = subst (λ z → c2 + c3 < z) eq-sum sum-gt
      in <-irreflℚ refl bad

    lo<hi : lo4 < hi4
    lo<hi with <-cmp lo4 hi4
    ... | tri< lt _ _ = lt
    ... | tri≈ _ eq _ = ⊥-elim (lo≠hi eq)
    ... | tri> _ _ gt = ⊥-elim (<-irreflℚ refl (<-≤-trans gt lo4≤hi4))

RealI.next (x *ℝ y) =
  RealI.next (RealI.next x) *ℝ RealI.next (RealI.next y)
RealI.nest (x *ℝ y) = nest1 , nest2 , nest3
  where
    lx ux ly uy : ℚ
    lx = RealI.l x; ux = RealI.u x
    ly = RealI.l y; uy = RealI.u y

    lx' ux' ly' uy' : ℚ
    lx' = RealI.l (RealI.next (RealI.next x))
    ux' = RealI.u (RealI.next (RealI.next x))
    ly' = RealI.l (RealI.next (RealI.next y))
    uy' = RealI.u (RealI.next (RealI.next y))

    lx≤lx' : lx ≤ lx'
    lx≤lx' = ≤-trans (proj₁ (RealI.nest x))
                      (proj₁ (RealI.nest (RealI.next x)))
    ux'≤ux : ux' ≤ ux
    ux'≤ux = ≤-trans (proj₁ (proj₂ (RealI.nest (RealI.next x))))
                      (proj₁ (proj₂ (RealI.nest x)))
    ly≤ly' : ly ≤ ly'
    ly≤ly' = ≤-trans (proj₁ (RealI.nest y))
                      (proj₁ (RealI.nest (RealI.next y)))
    uy'≤uy : uy' ≤ uy
    uy'≤uy = ≤-trans (proj₁ (proj₂ (RealI.nest (RealI.next y))))
                      (proj₁ (proj₂ (RealI.nest y)))

    lx≤ux : lx ≤ ux
    lx≤ux = <⇒≤ (RealI.lo x)
    ly≤uy : ly ≤ uy
    ly≤uy = <⇒≤ (RealI.lo y)
    lx'≤ux' : lx' ≤ ux'
    lx'≤ux' = <⇒≤ (RealI.lo (RealI.next (RealI.next x)))
    ly'≤uy' : ly' ≤ uy'
    ly'≤uy' = <⇒≤ (RealI.lo (RealI.next (RealI.next y)))

    lx≤ux' : lx ≤ ux'
    lx≤ux' = ≤-trans lx≤lx' lx'≤ux'
    ly≤uy' : ly ≤ uy'
    ly≤uy' = ≤-trans ly≤ly' ly'≤uy'
    lx'≤ux : lx' ≤ ux
    lx'≤ux = ≤-trans lx'≤ux' ux'≤ux
    ly'≤uy : ly' ≤ uy
    ly'≤uy = ≤-trans ly'≤uy' uy'≤uy

    module S = Corner lx ux ly uy lx≤ux ly≤uy
    module D = Corner lx' ux' ly' uy' lx'≤ux' ly'≤uy'

    nest1 : S.lo4 ≤ D.lo4
    nest1 =
      ⊓-glb (⊓-glb (S.lo4≤prod {a = lx'} {b = ly'}
                      lx≤lx' lx'≤ux ly≤ly' ly'≤uy)
                   (S.lo4≤prod {a = lx'} {b = uy'}
                      lx≤lx' lx'≤ux ly≤uy' uy'≤uy))
            (⊓-glb (S.lo4≤prod {a = ux'} {b = ly'}
                      lx≤ux' ux'≤ux ly≤ly' ly'≤uy)
                   (S.lo4≤prod {a = ux'} {b = uy'}
                      lx≤ux' ux'≤ux ly≤uy' uy'≤uy))

    nest2 : D.hi4 ≤ S.hi4
    nest2 =
      ⊔-lub (⊔-lub (S.prod≤hi4 {a = lx'} {b = ly'}
                      lx≤lx' lx'≤ux ly≤ly' ly'≤uy)
                   (S.prod≤hi4 {a = lx'} {b = uy'}
                      lx≤lx' lx'≤ux ly≤uy' uy'≤uy))
            (⊔-lub (S.prod≤hi4 {a = ux'} {b = ly'}
                      lx≤ux' ux'≤ux ly≤ly' ly'≤uy)
                   (S.prod≤hi4 {a = ux'} {b = uy'}
                      lx≤ux' ux'≤ux ly≤uy' uy'≤uy))

    h : ℚ
    h = 1/ embed 2

    0<h : 0ℚ < h
    0<h = positive⁻¹ h {{1/pos⇒pos (embed 2) {{embed-suc-pos {1}}}}}

    0≤h : 0ℚ ≤ h
    0≤h = <⇒≤ 0<h

    0≤hh : 0ℚ ≤ h * h
    0≤hh = subst (λ z → z ≤ h * h) (*-zeroʳ h)
                 (*-monoˡ-≤-nonNeg h {{nn 0≤h}} 0≤h)

    wX wX' wY wY' U U' Uy Uy' : ℚ
    wX = ux - lx
    wX' = ux' - lx'
    wY = uy - ly
    wY' = uy' - ly'
    U = mag lx ux
    U' = mag lx' ux'
    Uy = mag ly uy
    Uy' = mag ly' uy'

    0≤U : 0ℚ ≤ U
    0≤U = 0≤mag lx ux
    0≤Uy : 0ℚ ≤ Uy
    0≤Uy = 0≤mag ly uy
    0≤wX' : 0ℚ ≤ wX'
    0≤wX' = 0≤diff lx'≤ux'
    0≤wY' : 0ℚ ≤ wY'
    0≤wY' = 0≤diff ly'≤uy'

    U'≤U : U' ≤ U
    U'≤U = mag-le lx≤lx' lx'≤ux' ux'≤ux
    Uy'≤Uy : Uy' ≤ Uy
    Uy'≤Uy = mag-le ly≤ly' ly'≤uy' uy'≤uy

    wX'≤ : wX' ≤ wX * (h * h)
    wX'≤ =
      ≤-trans (≤-trans (proj₂ (proj₂ (RealI.nest (RealI.next x))))
                       (mono-half (proj₂ (proj₂ (RealI.nest x)))))
              (≤-reflexive (*-assoc wX h h))

    wY'≤ : wY' ≤ wY * (h * h)
    wY'≤ =
      ≤-trans (≤-trans (proj₂ (proj₂ (RealI.nest (RealI.next y))))
                       (mono-half (proj₂ (proj₂ (RealI.nest y)))))
              (≤-reflexive (*-assoc wY h h))

    double-h : ∀ W → (W + W) * (h * h) ≡ W * h
    double-h W = begin
      (W + W) * (h * h)
        ≡⟨ cong (_* (h * h)) (add-self W) ⟩
      (2ℚ * W) * (h * h)
        ≡⟨ *-assoc 2ℚ W (h * h) ⟩
      2ℚ * (W * (h * h))
        ≡⟨ cong (2ℚ *_) (sym (*-assoc W h h)) ⟩
      2ℚ * ((W * h) * h)
        ≡⟨ cong (λ z → 2ℚ * (z * h)) (*-comm W h) ⟩
      2ℚ * ((h * W) * h)
        ≡⟨ cong (2ℚ *_) (*-assoc h W h) ⟩
      2ℚ * (h * (W * h))
        ≡⟨ sym (*-assoc 2ℚ h (W * h)) ⟩
      (2ℚ * h) * (W * h)
        ≡⟨ cong (_* (W * h)) (*-inverseʳ (embed 2)) ⟩
      1ℚ * (W * h)
        ≡⟨ *-identityˡ (W * h) ⟩
      W * h
      ∎

    B' : ℚ
    B' = U' * wY' + Uy' * wX'

    step1 : U' * wY' ≤ U * (wY * (h * h))
    step1 =
      ≤-trans (*-monoʳ-≤-nonNeg wY' {{nn 0≤wY'}} U'≤U)
              (*-monoˡ-≤-nonNeg U {{nn 0≤U}} wY'≤)

    step2 : Uy' * wX' ≤ Uy * (wX * (h * h))
    step2 =
      ≤-trans (*-monoʳ-≤-nonNeg wX' {{nn 0≤wX'}} Uy'≤Uy)
              (*-monoˡ-≤-nonNeg Uy {{nn 0≤Uy}} wX'≤)

    g2 : B' ≤ U * (wY * (h * h)) + Uy * (wX * (h * h))
    g2 = +-mono-≤ step1 step2

    g3 : U * (wY * (h * h)) + Uy * (wX * (h * h))
       ≡ (U * wY + Uy * wX) * (h * h)
    g3 = sym (begin
      (U * wY + Uy * wX) * (h * h)
        ≡⟨ *-distribʳ-+ (h * h) (U * wY) (Uy * wX) ⟩
      (U * wY) * (h * h) + (Uy * wX) * (h * h)
        ≡⟨ cong₂ _+_ (*-assoc U wY (h * h)) (*-assoc Uy wX (h * h)) ⟩
      U * (wY * (h * h)) + Uy * (wX * (h * h))
      ∎)

    g4 : (U * wY + Uy * wX) * (h * h)
       ≤ ((S.hi4 - S.lo4) + (S.hi4 - S.lo4)) * (h * h)
    g4 = *-monoʳ-≤-nonNeg (h * h) {{nn 0≤hh}}
           (+-mono-≤ S.mag-widthˡ S.mag-widthʳ)

    nest3 : D.hi4 - D.lo4 ≤ (S.hi4 - S.lo4) ÷ embed 2
    nest3 =
      begin≤
        D.hi4 - D.lo4
          ≤⟨ D.spanB ⟩
        U' * wY' + Uy' * wX'
          ≤⟨ g2 ⟩
        U * (wY * (h * h)) + Uy * (wX * (h * h))
          ≈⟨ g3 ⟩
        (U * wY + Uy * wX) * (h * h)
          ≤⟨ g4 ⟩
        ((S.hi4 - S.lo4) + (S.hi4 - S.lo4)) * (h * h)
          ≈⟨ double-h (S.hi4 - S.lo4) ⟩
        (S.hi4 - S.lo4) * h
          ≈⟨ refl ⟩
        (S.hi4 - S.lo4) ÷ embed 2
      ≤∎
