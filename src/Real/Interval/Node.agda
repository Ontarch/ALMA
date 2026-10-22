------------------------------------------------------------------------
-- Node-level structural lemmas for RealI
--
-- RealI 的节点层结构引理
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module Real.Interval.Node where

open import Data.Nat using (ℕ; zero; suc) renaming (_*_ to _ℕ*_)
open import Data.Nat.Properties using (*-suc)
open import Data.Rational using
  (ℚ; 0ℚ; 1ℚ; _+_; _-_; _*_; _≤_; nonNegative) renaming (-_ to neg)
open import Data.Rational.Properties using
  (+-identityˡ; +-identityʳ; +-inverseˡ; +-comm; *-identityʳ; *-zeroˡ; *-assoc
  ; *-comm; *-distribʳ-+; neg-distrib-+; neg-distribˡ-*; ≤-refl; <⇒≤
  ; +-mono-≤; *-inverseʳ; *-monoˡ-≤-nonNeg)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; cong; cong₂; sym; subst; module ≡-Reasoning)
open ≡-Reasoning

open import Real.IntervalEquiv using
  (node; l; u; centre; width; width-n; 0<width; recipPow2)
open import Real using (embed; 2ℚ; 2ℚ≡1+1)
open import Real.Interval using (RealI; dyadic; δ)
open import Real.Interval.Arith using (0ℝ; 1ℝ; _+ℝ_; negℝ; div-add)
open import Real.Interval.Mul using (_*ℝ_)
open import Real.Interval.Rational using (sub-add)
open import Real.Interval.Kit using
  (embed2-nz; half; recipPow2-mono; n≤2n; n≤4n; *-mono-≤-nonNeg; 0≤recipPow2)
open import Base.RationalRing using (+interchange)
open import Real.Interval.Reasoning

------------------------------------------------------------------------
-- node commutes with dyadic
--
-- node 与 dyadic 交换

node-dyadic : (q : ℚ) (n : ℕ) → node (dyadic q 0) n ≡ dyadic q n
node-dyadic q zero    = refl
node-dyadic q (suc n) = cong RealI.next (node-dyadic q n)

l-dyadic : (q : ℚ) (n : ℕ) → l (dyadic q 0) n ≡ neg (δ n) + q
l-dyadic q n = cong RealI.l (node-dyadic q n)

u-dyadic : (q : ℚ) (n : ℕ) → u (dyadic q 0) n ≡ δ n + q
u-dyadic q n = cong RealI.u (node-dyadic q n)

------------------------------------------------------------------------
-- node commutes with +ℝ
--
-- node 与 +ℝ 交换

node-+ℝ : (x y : RealI) (n : ℕ) →
  node (x +ℝ y) n ≡ node x n +ℝ node y n
node-+ℝ x y zero    = refl
node-+ℝ x y (suc n) = cong RealI.next (node-+ℝ x y n)

l-hom : (x y : RealI) (n : ℕ) → l (x +ℝ y) n ≡ l x n + l y n
l-hom x y n = cong RealI.l (node-+ℝ x y n)

u-hom : (x y : RealI) (n : ℕ) → u (x +ℝ y) n ≡ u x n + u y n
u-hom x y n = cong RealI.u (node-+ℝ x y n)

------------------------------------------------------------------------
-- centre linearity for +
--
-- + 的中心线性

centre-add : (x y : RealI) (n : ℕ) →
  centre (x +ℝ y) n ≡ centre x n + centre y n
centre-add x y n =
  let
    lx = l x n; ux = u x n
    ly = l y n; uy = u y n
  in begin
    centre (x +ℝ y) n
      ≡⟨ cong₂ (λ a b → (a + b) * half) (l-hom x y n) (u-hom x y n) ⟩
    ((lx + ly) + (ux + uy)) * half
      ≡⟨ cong (_* half) (+interchange lx ly ux uy) ⟩
    ((lx + ux) + (ly + uy)) * half
      ≡⟨ div-add (lx + ux) (ly + uy) ⟩
    ((lx + ux) * half) + ((ly + uy) * half)
      ≡⟨ refl ⟩
    centre x n + centre y n
      ∎

------------------------------------------------------------------------
-- node commutes with negℝ
--
-- node 与 negℝ 交换

node-negℝ : (x : RealI) (n : ℕ) → node (negℝ x) n ≡ negℝ (node x n)
node-negℝ x zero    = refl
node-negℝ x (suc n) = cong RealI.next (node-negℝ x n)

l-neg : (x : RealI) (n : ℕ) → l (negℝ x) n ≡ neg (u x n)
l-neg x n = cong RealI.l (node-negℝ x n)

u-neg : (x : RealI) (n : ℕ) → u (negℝ x) n ≡ neg (l x n)
u-neg x n = cong RealI.u (node-negℝ x n)

centre-neg : (x : RealI) (n : ℕ) →
  centre (negℝ x) n ≡ neg (centre x n)
centre-neg x n =
  let
    lx = l x n
    ux = u x n
  in begin
    centre (negℝ x) n
      ≡⟨ cong₂ (λ a b → (a + b) * half) (l-neg x n) (u-neg x n) ⟩
    (neg ux + neg lx) * half
      ≡⟨ cong (_* half) (+-comm (neg ux) (neg lx)) ⟩
    (neg lx + neg ux) * half
      ≡⟨ cong (_* half) (sym (neg-distrib-+ lx ux)) ⟩
    neg (lx + ux) * half
      ≡⟨ sym (neg-distribˡ-* (lx + ux) half) ⟩
    neg ((lx + ux) * half)
      ≡⟨ refl ⟩
    neg (centre x n)
      ∎

------------------------------------------------------------------------
-- centre of 0ℝ and 1ℝ
--
-- 0ℝ 与 1ℝ 的中心

centre-0ℝ : (n : ℕ) → centre 0ℝ n ≡ 0ℚ
centre-0ℝ n =
  let
    dn = δ n
    l0 : l 0ℝ n ≡ neg dn
    l0 = begin
      l 0ℝ n
        ≡⟨ l-dyadic 0ℚ n ⟩
      neg dn + 0ℚ
        ≡⟨ +-identityʳ (neg dn) ⟩
      neg dn
        ∎
    u0 : u 0ℝ n ≡ dn
    u0 = begin
      u 0ℝ n
        ≡⟨ u-dyadic 0ℚ n ⟩
      dn + 0ℚ
        ≡⟨ +-identityʳ dn ⟩
      dn
        ∎
  in begin
    centre 0ℝ n
      ≡⟨ cong₂ (λ a b → (a + b) * half) l0 u0 ⟩
    (neg dn + dn) * half
      ≡⟨ cong (_* half) (+-inverseˡ dn) ⟩
    0ℚ * half
      ≡⟨ *-zeroˡ half ⟩
    0ℚ
      ∎

centre-1ℝ : (n : ℕ) → centre 1ℝ n ≡ 1ℚ
centre-1ℝ n =
  let
    dn = δ n
  in begin
    centre 1ℝ n
      ≡⟨ cong₂ (λ a b → (a + b) * half)
               (l-dyadic 1ℚ n) (u-dyadic 1ℚ n) ⟩
    ((neg dn + 1ℚ) + (dn + 1ℚ)) * half
      ≡⟨ cong (_* half) (+interchange (neg dn) 1ℚ dn 1ℚ) ⟩
    ((neg dn + dn) + (1ℚ + 1ℚ)) * half
      ≡⟨ cong (λ z → (z + (1ℚ + 1ℚ)) * half) (+-inverseˡ dn) ⟩
    (0ℚ + (1ℚ + 1ℚ)) * half
      ≡⟨ cong (_* half) (+-identityˡ (1ℚ + 1ℚ)) ⟩
    (1ℚ + 1ℚ) * half
      ≡⟨ cong (_* half) (sym 2ℚ≡1+1) ⟩
    2ℚ * half
      ≡⟨ *-inverseʳ (embed 2) {{embed2-nz}} ⟩
    1ℚ
      ∎

------------------------------------------------------------------------
-- node commutes with *ℝ
--
-- Two-level jump: node (x *ℝ y) n = node x (2n) *ℝ node y (2n).
--
-- node 与 *ℝ 交换
--
-- 两级跳跃：node (x *ℝ y) n = node x (2n) *ℝ node y (2n)。

node-*ℝ : (x y : RealI) (n : ℕ) →
  node (x *ℝ y) n ≡ node x (2 ℕ* n) *ℝ node y (2 ℕ* n)
node-*ℝ x y zero    = refl
node-*ℝ x y (suc n) =
  let
    eq : suc (suc (2 ℕ* n)) ≡ 2 ℕ* suc n
    eq = sym (*-suc 2 n)
  in begin
    node (x *ℝ y) (suc n)
      ≡⟨ cong RealI.next (node-*ℝ x y n) ⟩
    node x (suc (suc (2 ℕ* n))) *ℝ node y (suc (suc (2 ℕ* n)))
      ≡⟨ cong₂ (λ a b → node x a *ℝ node y b) eq eq ⟩
    node x (2 ℕ* suc n) *ℝ node y (2 ℕ* suc n)
      ∎

------------------------------------------------------------------------
-- Private algebraic helpers
--
-- 私有代数助手

mul-pair : ∀ a b h → (a * h) * (b * h) ≡ (a * b) * (h * h)
mul-pair a b h = begin
  (a * h) * (b * h)
    ≡⟨ *-assoc a h (b * h) ⟩
  a * (h * (b * h))
    ≡⟨ cong (a *_) (begin
          h * (b * h)
            ≡⟨ sym (*-assoc h b h) ⟩
          (h * b) * h
            ≡⟨ cong (_* h) (*-comm h b) ⟩
          (b * h) * h
            ≡⟨ *-assoc b h h ⟩
          b * (h * h)
            ∎) ⟩
  a * (b * (h * h))
    ≡⟨ sym (*-assoc a b (h * h)) ⟩
  (a * b) * (h * h)
    ∎

mul-nonNeg : ∀ {p q : ℚ} → 0ℚ ≤ p → 0ℚ ≤ q → 0ℚ ≤ p * q
mul-nonNeg {p} {q} 0≤p 0≤q =
  subst (λ z → z ≤ p * q) (*-zeroˡ 0ℚ)
        (*-mono-≤-nonNeg (≤-refl {0ℚ}) 0≤p (≤-refl {0ℚ}) 0≤q)

add2-nonNeg : ∀ {p q : ℚ} → 0ℚ ≤ p → 0ℚ ≤ q → 0ℚ ≤ p + q
add2-nonNeg {p} {q} 0≤p 0≤q =
  subst (λ z → z ≤ p + q) (+-identityˡ 0ℚ) (+-mono-≤ 0≤p 0≤q)

0≤width-n : (r : RealI) (n : ℕ) → 0ℚ ≤ width r n
0≤width-n r n = <⇒≤ (0<width (node r n))

recipPow2≤1 : ∀ n → recipPow2 n ≤ 1ℚ
recipPow2≤1 n =
  begin≤
    recipPow2 n
      ≤⟨ recipPow2-mono (Data.Nat.z≤n {n}) ⟩
    recipPow2 0
      ≈⟨ refl ⟩
    1ℚ
  ≤∎

rr≤r : ∀ {r : ℚ} → 0ℚ ≤ r → r ≤ 1ℚ → r * r ≤ r
rr≤r {r} 0≤r r≤1 =
  begin≤
    r * r
      ≤⟨ *-monoˡ-≤-nonNeg r {{nonNegative 0≤r}} r≤1 ⟩
    r * 1ℚ
      ≈⟨ *-identityʳ r ⟩
    r
  ≤∎

prod-rec : ∀ {a a' b b' r : ℚ} → 0ℚ ≤ r → r ≤ 1ℚ →
            a ≤ a' * r → b ≤ b' * r →
            0ℚ ≤ a → 0ℚ ≤ b → 0ℚ ≤ a' → 0ℚ ≤ b' →
            a * b ≤ (a' * b') * r
prod-rec {a} {a'} {b} {b'} {r} 0≤r r≤1 ha hb 0≤a 0≤b 0≤a' 0≤b' =
  begin≤
    a * b
      ≤⟨ *-mono-≤-nonNeg 0≤a ha 0≤b hb ⟩
    (a' * r) * (b' * r)
      ≈⟨ mul-pair a' b' r ⟩
    (a' * b') * (r * r)
      ≤⟨ *-monoˡ-≤-nonNeg (a' * b')
            {{nonNegative (mul-nonNeg 0≤a' 0≤b')}} (rr≤r 0≤r r≤1) ⟩
    (a' * b') * r
  ≤∎

------------------------------------------------------------------------
-- Width estimates
--
-- 宽度估计

width-+ : (x y : RealI) (n : ℕ) → width (x +ℝ y) n ≡ width x n + width y n
width-+ x y n = begin
  width (x +ℝ y) n
    ≡⟨ cong₂ _-_ (u-hom x y n) (l-hom x y n) ⟩
  (u x n + u y n) - (l x n + l y n)
    ≡⟨ sub-add (u x n) (u y n) (l x n) (l y n) ⟩
  (u x n - l x n) + (u y n - l y n)
    ≡⟨ refl ⟩
  width x n + width y n
    ∎

width-rec : (x : RealI) (n : ℕ) → width x (2 ℕ* n) ≤ width x 0 * recipPow2 n
width-rec x n =
  begin≤
    width x (2 ℕ* n)
      ≤⟨ width-n x (2 ℕ* n) ⟩
    width x 0 * recipPow2 (2 ℕ* n)
      ≤⟨ *-monoˡ-≤-nonNeg (width x 0) {{nonNegative (0≤width-n x 0)}}
                            (recipPow2-mono (n≤2n n)) ⟩
    width x 0 * recipPow2 n
  ≤∎

width-rec4 : (x : RealI) (n : ℕ) → width x (4 ℕ* n) ≤ width x 0 * recipPow2 n
width-rec4 x n =
  begin≤
    width x (4 ℕ* n)
      ≤⟨ width-n x (4 ℕ* n) ⟩
    width x 0 * recipPow2 (4 ℕ* n)
      ≤⟨ *-monoˡ-≤-nonNeg (width x 0) {{nonNegative (0≤width-n x 0)}}
                            (recipPow2-mono (n≤4n n)) ⟩
    width x 0 * recipPow2 n
  ≤∎

width-sum-rec : (x y : RealI) (n : ℕ) →
  width (x +ℝ y) (2 ℕ* n) ≤ (width x 0 + width y 0) * recipPow2 n
width-sum-rec x y n =
  begin≤
    width (x +ℝ y) (2 ℕ* n)
      ≈⟨ width-+ x y (2 ℕ* n) ⟩
    width x (2 ℕ* n) + width y (2 ℕ* n)
      ≤⟨ +-mono-≤ (width-rec x n) (width-rec y n) ⟩
    width x 0 * recipPow2 n + width y 0 * recipPow2 n
      ≈⟨ sym (*-distribʳ-+ (recipPow2 n) (width x 0) (width y 0)) ⟩
    (width x 0 + width y 0) * recipPow2 n
  ≤∎

width-prod : (x y : RealI) (n : ℕ) →
  width x (2 ℕ* n) * width y (2 ℕ* n)
    ≤ (width x 0 * width y 0) * recipPow2 n
width-prod x y n =
  begin≤
    width x (2 ℕ* n) * width y (2 ℕ* n)
      ≤⟨ prod-rec (0≤recipPow2 n) (recipPow2≤1 n)
                   (width-rec x n) (width-rec y n)
                   (0≤width-n x (2 ℕ* n)) (0≤width-n y (2 ℕ* n))
                   (0≤width-n x 0) (0≤width-n y 0) ⟩
    (width x 0 * width y 0) * recipPow2 n
  ≤∎

width-x-sum : (x y z : RealI) (n : ℕ) →
  width x (2 ℕ* n) * width (y +ℝ z) (2 ℕ* n)
    ≤ (width x 0 * (width y 0 + width z 0)) * recipPow2 n
width-x-sum x y z n =
  begin≤
    width x (2 ℕ* n) * width (y +ℝ z) (2 ℕ* n)
      ≤⟨ prod-rec (0≤recipPow2 n) (recipPow2≤1 n)
                   (width-rec x n) (width-sum-rec y z n)
                   (0≤width-n x (2 ℕ* n)) (0≤width-n (y +ℝ z) (2 ℕ* n))
                   (0≤width-n x 0)
                   (add2-nonNeg (0≤width-n y 0) (0≤width-n z 0)) ⟩
    (width x 0 * (width y 0 + width z 0)) * recipPow2 n
  ≤∎
