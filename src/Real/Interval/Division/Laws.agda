------------------------------------------------------------------------
-- Derived laws for division of interval reals
--
-- 区间实数除法的派生定律
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module Real.Interval.Division.Laws where

open import Data.Sum using (_⊎_)

open import Real.Interval using (RealI)
open import Real.Interval.Arith using (0ℝ; 1ℝ; _+ℝ_)
open import Real.Interval.Mul using (_*ℝ_)
open import Real.Interval.Equiv using (_≈ℝ_; ≈ℝ-refl; ≈ℝ-sym; ≈ℝ-trans)
open import Real.Interval.Order using (_<ℝ_)
open import Real.Interval.Mul.Laws using
  (*ℝ-comm; *ℝ-assoc; *ℝ-identityʳ; *ℝ-zeroˡ; *ℝ-distribʳ-+)
open import Real.Interval.Mul.Cong using (*ℝ-cong)
open import Real.Interval.Mul.Order using (+ℝ-cong)
open import Real.Interval.Recip using (recipℝ')
open import Real.Interval.Inverse using (*ℝ-inverse)
open import Real.Interval.Division using
  (_/ℝ_; nonzero-mul; /ℝ-congˡ; /ℝ-congʳ; *ℝ-/ℝ; /ℝ-*ℝ; 0/ℝ; /ℝ-cancel)
open import Real.Interval.Reasoning.Equiv

------------------------------------------------------------------------
-- Equality cancellation
--
-- 等式乘法消去

*ℝ-cancel : (x y z : RealI) (nz : (0ℝ <ℝ z) ⊎ (z <ℝ 0ℝ))
          → x *ℝ z ≈ℝ y *ℝ z → x ≈ℝ y
*ℝ-cancel x y z nz xz≈yz =
  beginℝ
    x
      ≈ℝ⟨ ≈ℝ-sym (*ℝ-identityʳ x) ⟩
    x *ℝ 1ℝ
      ≈ℝ⟨ *ℝ-cong {x = x} {x' = x}
                   {y = 1ℝ} {y' = z *ℝ recipℝ' z nz}
                   ≈ℝ-refl (≈ℝ-sym (*ℝ-inverse z nz)) ⟩
    x *ℝ (z *ℝ recipℝ' z nz)
      ≈ℝ⟨ ≈ℝ-sym (*ℝ-assoc x z (recipℝ' z nz)) ⟩
    (x *ℝ z) *ℝ recipℝ' z nz
      ≈ℝ⟨ *ℝ-cong {x = x *ℝ z} {x' = y *ℝ z}
                   {y = recipℝ' z nz} {y' = recipℝ' z nz}
                   xz≈yz ≈ℝ-refl ⟩
    (y *ℝ z) *ℝ recipℝ' z nz
      ≈ℝ⟨ *ℝ-assoc y z (recipℝ' z nz) ⟩
    y *ℝ (z *ℝ recipℝ' z nz)
      ≈ℝ⟨ *ℝ-cong {x = y} {x' = y}
                   {y = z *ℝ recipℝ' z nz} {y' = 1ℝ}
                   ≈ℝ-refl (*ℝ-inverse z nz) ⟩
    y *ℝ 1ℝ
      ≈ℝ⟨ *ℝ-identityʳ y ⟩
    y
  ∎ℝ

------------------------------------------------------------------------
-- Self-division
--
-- 自除

/ℝ-self : (x : RealI) (nz : (0ℝ <ℝ x) ⊎ (x <ℝ 0ℝ))
        → _/ℝ_ x x nz ≈ℝ 1ℝ
/ℝ-self x nz = *ℝ-inverse x nz

------------------------------------------------------------------------
-- Division / multiplication equivalence
--
-- 除法与乘法的等价刻画

/ℝ→*ℝ : (x y z : RealI) (nz : (0ℝ <ℝ y) ⊎ (y <ℝ 0ℝ))
      → _/ℝ_ x y nz ≈ℝ z → x ≈ℝ z *ℝ y
/ℝ→*ℝ x y z nz x/y≈z =
  beginℝ
    x
      ≈ℝ⟨ ≈ℝ-sym (/ℝ-*ℝ x y nz) ⟩
    _/ℝ_ x y nz *ℝ y
      ≈ℝ⟨ *ℝ-cong {x = _/ℝ_ x y nz} {x' = z}
                   {y = y} {y' = y}
                   x/y≈z ≈ℝ-refl ⟩
    z *ℝ y
  ∎ℝ

*ℝ→/ℝ : (x y z : RealI) (nz : (0ℝ <ℝ y) ⊎ (y <ℝ 0ℝ))
      → x ≈ℝ z *ℝ y → _/ℝ_ x y nz ≈ℝ z
*ℝ→/ℝ x y z nz x≈zy =
  beginℝ
    _/ℝ_ x y nz
      ≈ℝ⟨ *ℝ-cong {x = x} {x' = z *ℝ y}
                   {y = recipℝ' y nz} {y' = recipℝ' y nz}
                   x≈zy ≈ℝ-refl ⟩
    _/ℝ_ (z *ℝ y) y nz
      ≈ℝ⟨ *ℝ-/ℝ z y nz ⟩
    z
  ∎ℝ

------------------------------------------------------------------------
-- Cross multiplication
--
-- 交叉相乘

/ℝ-cross→ : (x x' y y' : RealI)
  (nz_y : (0ℝ <ℝ y) ⊎ (y <ℝ 0ℝ))
  (nz_y' : (0ℝ <ℝ y') ⊎ (y' <ℝ 0ℝ))
  → _/ℝ_ x y nz_y ≈ℝ _/ℝ_ x' y' nz_y'
  → x *ℝ y' ≈ℝ x' *ℝ y
/ℝ-cross→ x x' y y' nz_y nz_y' h =
  beginℝ
    x *ℝ y'
      ≈ℝ⟨ *ℝ-cong {x = x} {x' = _/ℝ_ x y nz_y *ℝ y}
                   {y = y'} {y' = y'}
                   (≈ℝ-sym (/ℝ-*ℝ x y nz_y)) ≈ℝ-refl ⟩
    (_/ℝ_ x y nz_y *ℝ y) *ℝ y'
      ≈ℝ⟨ *ℝ-assoc (_/ℝ_ x y nz_y) y y' ⟩
    _/ℝ_ x y nz_y *ℝ (y *ℝ y')
      ≈ℝ⟨ *ℝ-cong {x = _/ℝ_ x y nz_y} {x' = _/ℝ_ x' y' nz_y'}
                   {y = y *ℝ y'} {y' = y *ℝ y'}
                   h ≈ℝ-refl ⟩
    _/ℝ_ x' y' nz_y' *ℝ (y *ℝ y')
      ≈ℝ⟨ *ℝ-cong {x = _/ℝ_ x' y' nz_y'} {x' = _/ℝ_ x' y' nz_y'}
                   {y = y *ℝ y'} {y' = y' *ℝ y}
                   ≈ℝ-refl (*ℝ-comm y y') ⟩
    _/ℝ_ x' y' nz_y' *ℝ (y' *ℝ y)
      ≈ℝ⟨ ≈ℝ-sym (*ℝ-assoc (_/ℝ_ x' y' nz_y') y' y) ⟩
    (_/ℝ_ x' y' nz_y' *ℝ y') *ℝ y
      ≈ℝ⟨ *ℝ-cong {x = _/ℝ_ x' y' nz_y' *ℝ y'} {x' = x'}
                   {y = y} {y' = y}
                   (/ℝ-*ℝ x' y' nz_y') ≈ℝ-refl ⟩
    x' *ℝ y
  ∎ℝ

/ℝ-cross← : (x x' y y' : RealI)
  (nz_y : (0ℝ <ℝ y) ⊎ (y <ℝ 0ℝ))
  (nz_y' : (0ℝ <ℝ y') ⊎ (y' <ℝ 0ℝ))
  → x *ℝ y' ≈ℝ x' *ℝ y
  → _/ℝ_ x y nz_y ≈ℝ _/ℝ_ x' y' nz_y'
/ℝ-cross← x x' y y' nz_y nz_y' h =
  let
    nz_yy' = nonzero-mul y y' nz_y nz_y'
    nz_y'y = nonzero-mul y' y nz_y' nz_y
    step1 : _/ℝ_ x y nz_y ≈ℝ _/ℝ_ (x *ℝ y') (y *ℝ y') nz_yy'
    step1 = ≈ℝ-sym (/ℝ-cancel x y y' nz_y nz_y')
    step2 : _/ℝ_ (x *ℝ y') (y *ℝ y') nz_yy'
          ≈ℝ _/ℝ_ (x' *ℝ y) (y *ℝ y') nz_yy'
    step2 = /ℝ-congˡ {x = x *ℝ y'} {x' = x' *ℝ y}
                     {y = y *ℝ y'} {nz = nz_yy'} h
    step3 : _/ℝ_ (x' *ℝ y) (y *ℝ y') nz_yy'
          ≈ℝ _/ℝ_ (x' *ℝ y) (y' *ℝ y) nz_y'y
    step3 = /ℝ-congʳ nz_yy' nz_y'y (*ℝ-comm y y')
    step4 : _/ℝ_ (x' *ℝ y) (y' *ℝ y) nz_y'y ≈ℝ _/ℝ_ x' y' nz_y'
    step4 = /ℝ-cancel x' y' y nz_y' nz_y
  in ≈ℝ-trans step1 (≈ℝ-trans step2 (≈ℝ-trans step3 step4))

------------------------------------------------------------------------
-- Addition over a general denominator
--
-- 一般分母加法

/ℝ-+-general :
  (x y z w : RealI)
  (nz_y : (0ℝ <ℝ y) ⊎ (y <ℝ 0ℝ))
  (nz_w : (0ℝ <ℝ w) ⊎ (w <ℝ 0ℝ))
  → _/ℝ_ x y nz_y +ℝ _/ℝ_ z w nz_w
    ≈ℝ _/ℝ_ (x *ℝ w +ℝ z *ℝ y) (y *ℝ w) (nonzero-mul y w nz_y nz_w)
/ℝ-+-general x y z w nz_y nz_w =
  let
    nz_yw = nonzero-mul y w nz_y nz_w
  in
  ≈ℝ-sym
    (*ℝ→/ℝ (x *ℝ w +ℝ z *ℝ y) (y *ℝ w)
           (_/ℝ_ x y nz_y +ℝ _/ℝ_ z w nz_w)
           nz_yw goal)
  where
    goal : x *ℝ w +ℝ z *ℝ y
         ≈ℝ (_/ℝ_ x y nz_y +ℝ _/ℝ_ z w nz_w) *ℝ (y *ℝ w)
    goal =
      let
        t1 : x *ℝ w ≈ℝ _/ℝ_ x y nz_y *ℝ (y *ℝ w)
        t1 =
          beginℝ
            x *ℝ w
              ≈ℝ⟨ *ℝ-cong {x = x} {x' = _/ℝ_ x y nz_y *ℝ y}
                           {y = w} {y' = w}
                           (≈ℝ-sym (/ℝ-*ℝ x y nz_y)) ≈ℝ-refl ⟩
            (_/ℝ_ x y nz_y *ℝ y) *ℝ w
              ≈ℝ⟨ *ℝ-assoc (_/ℝ_ x y nz_y) y w ⟩
            _/ℝ_ x y nz_y *ℝ (y *ℝ w)
          ∎ℝ
        t2 : z *ℝ y ≈ℝ _/ℝ_ z w nz_w *ℝ (y *ℝ w)
        t2 =
          beginℝ
            z *ℝ y
              ≈ℝ⟨ *ℝ-cong {x = z} {x' = _/ℝ_ z w nz_w *ℝ w}
                           {y = y} {y' = y}
                           (≈ℝ-sym (/ℝ-*ℝ z w nz_w)) ≈ℝ-refl ⟩
            (_/ℝ_ z w nz_w *ℝ w) *ℝ y
              ≈ℝ⟨ *ℝ-assoc (_/ℝ_ z w nz_w) w y ⟩
            _/ℝ_ z w nz_w *ℝ (w *ℝ y)
              ≈ℝ⟨ *ℝ-cong {x = _/ℝ_ z w nz_w} {x' = _/ℝ_ z w nz_w}
                           {y = w *ℝ y} {y' = y *ℝ w}
                           ≈ℝ-refl (*ℝ-comm w y) ⟩
            _/ℝ_ z w nz_w *ℝ (y *ℝ w)
          ∎ℝ
      in
      beginℝ
        x *ℝ w +ℝ z *ℝ y
          ≈ℝ⟨ +ℝ-cong {x = x *ℝ w}
                       {x' = _/ℝ_ x y nz_y *ℝ (y *ℝ w)}
                       {y = z *ℝ y}
                       {y' = _/ℝ_ z w nz_w *ℝ (y *ℝ w)}
                       t1 t2 ⟩
        _/ℝ_ x y nz_y *ℝ (y *ℝ w) +ℝ _/ℝ_ z w nz_w *ℝ (y *ℝ w)
          ≈ℝ⟨ ≈ℝ-sym (*ℝ-distribʳ-+
                (y *ℝ w) (_/ℝ_ x y nz_y) (_/ℝ_ z w nz_w)) ⟩
        (_/ℝ_ x y nz_y +ℝ _/ℝ_ z w nz_w) *ℝ (y *ℝ w)
      ∎ℝ

------------------------------------------------------------------------
-- Zero quotient
--
-- 商为零的刻画

/ℝ-zero→ : (x y : RealI) (nz : (0ℝ <ℝ y) ⊎ (y <ℝ 0ℝ))
         → _/ℝ_ x y nz ≈ℝ 0ℝ → x ≈ℝ 0ℝ
/ℝ-zero→ x y nz x/y≈0 =
  beginℝ
    x
      ≈ℝ⟨ ≈ℝ-sym (/ℝ-*ℝ x y nz) ⟩
    _/ℝ_ x y nz *ℝ y
      ≈ℝ⟨ *ℝ-cong {x = _/ℝ_ x y nz} {x' = 0ℝ}
                   {y = y} {y' = y}
                   x/y≈0 ≈ℝ-refl ⟩
    0ℝ *ℝ y
      ≈ℝ⟨ *ℝ-zeroˡ y ⟩
    0ℝ
  ∎ℝ

/ℝ-zero← : (x y : RealI) (nz : (0ℝ <ℝ y) ⊎ (y <ℝ 0ℝ))
         → x ≈ℝ 0ℝ → _/ℝ_ x y nz ≈ℝ 0ℝ
/ℝ-zero← x y nz x≈0 =
  ≈ℝ-trans
    (/ℝ-congˡ {x = x} {x' = 0ℝ} {y = y} {nz = nz} x≈0)
    (0/ℝ y nz)

------------------------------------------------------------------------
-- No zero divisors
--
-- 无零因子

*ℝ-no-zero-divisor :
  (x y : RealI) (nz_x : (0ℝ <ℝ x) ⊎ (x <ℝ 0ℝ))
  → x *ℝ y ≈ℝ 0ℝ → y ≈ℝ 0ℝ
*ℝ-no-zero-divisor x y nz_x xy≈0 =
  *ℝ-cancel y 0ℝ x nz_x
    (≈ℝ-trans (≈ℝ-trans (*ℝ-comm y x) xy≈0)
              (≈ℝ-sym (*ℝ-zeroˡ x)))
