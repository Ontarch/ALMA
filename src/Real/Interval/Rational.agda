------------------------------------------------------------------------
-- Rational lemmas for real-interval arithmetic
--
-- 实区间算术所需的有理引理
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module Real.Interval.Rational where

open import Data.Empty using (⊥-elim)
open import Data.Integer using (+_; +<+) renaming (_*_ to _*ℤ_; _<_ to _<ℤ_)
import Data.Integer.Properties as ℤP
open import Data.Nat using
  (ℕ; zero; suc; z≤n; s≤s; _^_; _∸_) renaming (_+_ to _+ℕ_; _*_ to _*ℕ_; _<_ to _<ℕ_)
import Data.Nat.Properties as ℕP
open import Data.Rational using
  (ℚ; 0ℚ; _⊓_; _⊔_; _+_; _-_; _<_; _≤_; ∣_∣; fromℚᵘ; toℚᵘ)
  renaming (-_ to neg)
open import Data.Rational.Properties using
  (+-comm; +-inverseʳ; neg-distrib-+; +-mono-<-≤; ≤-refl; <⇒≤; <-cmp; ≤-trans
  ; ≤-antisym; neg-antimono-≤; 0≤∣p∣; ∣-p∣≡∣p∣; ∣p∣≡p∨∣p∣≡-p
  ; 0≤p⇒∣p∣≡p; toℚᵘ-cancel-<; toℚᵘ-fromℚᵘ; p⊓q≤p; p⊓q≤q; p≤p⊔q; p≤q⊔p
  ; p≤q⇒p⊓q≡p; p≥q⇒p⊓q≡q; p≤q⇒p⊔q≡q; p≥q⇒p⊔q≡p; ⊓-glb; ⊔-lub; ⊓-sel; ⊔-sel)
open import Data.Rational.Unnormalised.Base
  using (ℚᵘ; mkℚᵘ; _≃_; *≡*; *<*) renaming (_<_ to _<ᵘ_)
open import Data.Rational.Unnormalised.Properties using (<-respˡ-≃; <-respʳ-≃)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Function.Base using (case_of_)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; cong; sym; subst; subst₂; module ≡-Reasoning)
open ≡-Reasoning
open import Relation.Nullary.Negation using (¬_)
open import Relation.Binary.Definitions using (tri<; tri≈; tri>)

open import Base.RationalRing using (neg-involutive; +interchange)
open import Real.Interval.Reasoning using (begin≤_; _≈⟨_⟩_; _≤⟨_⟩_; _≤∎)

------------------------------------------------------------------------
-- Positive difference
--
-- a < b implies 0 < b − a.
--
-- 正差
--
-- 由 a < b 得正差。

pos-diff : ∀ a b → a < b → 0ℚ < b - a
pos-diff a b a<b =
  subst (λ z → z < b - a)
        (+-inverseʳ a)
        (+-mono-<-≤ a<b (≤-refl {neg a}))

------------------------------------------------------------------------
-- Algebra of subtraction
--
-- sub-add distributes subtraction over addition; negsub and neg-sub
-- flip differences.
--
-- 减法代数
--
-- sub-add 把减法分配到加法；negsub 与 neg-sub 翻转差。

sub-add : (a b c d : ℚ) → (a + b) - (c + d) ≡ (a - c) + (b - d)
sub-add a b c d = begin
  (a + b) - (c + d)
    ≡⟨ cong (λ z → (a + b) + z) (neg-distrib-+ c d) ⟩
  (a + b) + (neg c + neg d)
    ≡⟨ +interchange a b (neg c) (neg d) ⟩
  (a - c) + (b - d)
  ∎

negsub : ∀ x y → neg (x - y) ≡ y - x
negsub x y = begin
  neg (x - y)
    ≡⟨ refl ⟩
  neg (x + neg y)
    ≡⟨ neg-distrib-+ x (neg y) ⟩
  neg x + neg (neg y)
    ≡⟨ cong (λ z → neg x + z) (neg-involutive y) ⟩
  neg x + y
    ≡⟨ +-comm (neg x) y ⟩
  y + neg x
    ≡⟨ refl ⟩
  y - x
  ∎

neg-sub : ∀ a b → neg a - neg b ≡ b - a
neg-sub a b = begin
  neg a - neg b
    ≡⟨ refl ⟩
  neg a + neg (neg b)
    ≡⟨ cong (λ z → neg a + z) (neg-involutive b) ⟩
  neg a + b
    ≡⟨ +-comm (neg a) b ⟩
  b + neg a
    ≡⟨ refl ⟩
  b - a
  ∎

------------------------------------------------------------------------
-- Trichotomy elimination
--
-- From a proof of each of the three cases, build a proof of P.
--
-- 三歧性消去
--
-- 由三种情形的证明构造 P 的证明。

tri-elim : ∀ {P : Set} (a b : ℚ)
  → (a < b → P) → (a ≡ b → P) → (b < a → P) → P
tri-elim a b lt eq gt =
  case <-cmp a b of λ where
    (tri< a<b _ _) → lt a<b
    (tri≈ _ a≡b _) → eq a≡b
    (tri> _ _ b<a) → gt b<a

------------------------------------------------------------------------
-- Minimum and maximum
--
-- 最小值与最大值

min<max : ∀ a b → ¬ (a ≡ b) → a ⊓ b < a ⊔ b
min<max a b a≠b = tri-elim a b
  (λ a<b →
     subst₂ _<_
       (sym (p≤q⇒p⊓q≡p (<⇒≤ a<b)))
       (sym (p≤q⇒p⊔q≡q (<⇒≤ a<b)))
       a<b)
  (λ a≡b → ⊥-elim (a≠b a≡b))
  (λ b<a →
     subst₂ _<_
       (sym (p≥q⇒p⊓q≡q (<⇒≤ b<a)))
       (sym (p≥q⇒p⊔q≡p (<⇒≤ b<a)))
       b<a)

------------------------------------------------------------------------
-- Absolute value and magnitude bounds
--
-- The two elementary absolute-value bounds state that both r and -r
-- are at most |r|. The magnitude combines the endpoint absolute values
-- into their maximum, and mag-≤ shows that any point inside an interval
-- is bounded by that maximum.
--
-- 绝对值与量级界
--
-- 两条基本绝对值界给出 r 与 -r 都不超过 |r|；mag 将端点绝对值
-- 合并为上确界，mag-≤ 表明区间内任意点的绝对值不超过该上确界。

r≤|r| : ∀ r → r ≤ ∣ r ∣
r≤|r| r =
  let
    helper : ∣ r ∣ ≡ r ⊎ ∣ r ∣ ≡ neg r → r ≤ ∣ r ∣
    helper = λ where
      (inj₁ |r|≡r) → begin≤
        r      ≈⟨ sym |r|≡r ⟩
        ∣ r ∣  ≤∎
      (inj₂ |r|≡-r) →
        let
          0≤-r : 0ℚ ≤ neg r
          0≤-r = subst (λ z → 0ℚ ≤ z) |r|≡-r (0≤∣p∣ r)

          r≤0 : r ≤ 0ℚ
          r≤0 = subst (λ z → z ≤ 0ℚ) (neg-involutive r) (neg-antimono-≤ 0≤-r)
        in begin≤
          r      ≤⟨ r≤0 ⟩
          0ℚ     ≤⟨ 0≤-r ⟩
          neg r  ≈⟨ sym |r|≡-r ⟩
          ∣ r ∣  ≤∎
  in helper (∣p∣≡p∨∣p∣≡-p r)

-r≤|r| : ∀ r → neg r ≤ ∣ r ∣
-r≤|r| r = subst (λ z → neg r ≤ z) (∣-p∣≡∣p∣ r) (r≤|r| (neg r))

-- The magnitude of an interval is the maximum of its endpoint
-- absolute values.
--
-- 区间量级为其端点绝对值的最大值。
mag : ℚ → ℚ → ℚ
mag l u = ∣ l ∣ ⊔ ∣ u ∣

mag-≤ : ∀ {l u x : ℚ} → l ≤ x → x ≤ u → ∣ x ∣ ≤ mag l u
mag-≤ {l} {u} {x} l≤x x≤u =
  let
    helper : ∣ x ∣ ≡ x ⊎ ∣ x ∣ ≡ neg x → ∣ x ∣ ≤ mag l u
    helper = λ where
      (inj₁ |x|≡x) → begin≤
        ∣ x ∣          ≈⟨ |x|≡x ⟩
        x              ≤⟨ x≤u ⟩
        u              ≤⟨ r≤|r| u ⟩
        ∣ u ∣          ≤⟨ p≤q⊔p ∣ l ∣ ∣ u ∣ ⟩
        ∣ l ∣ ⊔ ∣ u ∣  ≤∎
      (inj₂ |x|≡-x) →
        let
          0≤-x : 0ℚ ≤ neg x
          0≤-x = subst (λ z → 0ℚ ≤ z) |x|≡-x (0≤∣p∣ x)

          x≤0 : x ≤ 0ℚ
          x≤0 = subst (λ z → z ≤ 0ℚ) (neg-involutive x) (neg-antimono-≤ 0≤-x)

          l≤0 : l ≤ 0ℚ
          l≤0 = ≤-trans l≤x x≤0

          0≤-l : 0ℚ ≤ neg l
          0≤-l = neg-antimono-≤ l≤0

          |l|≡-l : ∣ l ∣ ≡ neg l
          |l|≡-l = subst (λ z → z ≡ neg l) (∣-p∣≡∣p∣ l)
                      (0≤p⇒∣p∣≡p {neg l} 0≤-l)
        in begin≤
          ∣ x ∣          ≈⟨ |x|≡-x ⟩
          neg x          ≤⟨ neg-antimono-≤ l≤x ⟩
          neg l          ≈⟨ sym |l|≡-l ⟩
          ∣ l ∣          ≤⟨ p≤p⊔q ∣ l ∣ ∣ u ∣ ⟩
          ∣ l ∣ ⊔ ∣ u ∣  ≤∎
  in helper (∣p∣≡p∨∣p∣≡-p x)

------------------------------------------------------------------------
-- Fraction comparison with a general denominator
--
-- If N * (k+1) < (suc d) * 2^t then N / (suc d * 2^t) < 1/(k+1).
-- This generalises fracL-strict from IntervalEquiv, which is the
-- special case d = 0.
--
-- 一般分母的分数比较
--
-- 若整数交叉相乘条件成立，则上述分数不等式成立。它推广了
-- IntervalEquiv 的 fracL-strict，后者是 d = 0 的特例。

0<2^t : (t : ℕ) → 0 <ℕ 2 ^ t
0<2^t zero    = s≤s z≤n
0<2^t (suc t) = ℕP.≤-trans (s≤s z≤n) (ℕP.*-monoʳ-≤ 2 (0<2^t t))

-- suc (n ∸ 1) ≡ n for n > 0.
--
-- 当 n > 0 时结论成立。
suc∸1 : {n : ℕ} → 0 <ℕ n → suc (n ∸ 1) ≡ n
suc∸1 {n} 0<n = begin
  suc (n ∸ 1)
    ≡⟨ refl ⟩
  1 +ℕ (n ∸ 1)
    ≡⟨ ℕP.+-comm 1 (n ∸ 1) ⟩
  (n ∸ 1) +ℕ 1
    ≡⟨ ℕP.m∸n+n≡m 0<n ⟩
  n
  ∎

-- The product of a successor and a power of two is positive.
--
-- 后继与二的幂的乘积为正。
0<sucd*2^t : (d t : ℕ) → 0 <ℕ suc d *ℕ 2 ^ t
0<sucd*2^t d t = ℕP.≤-trans (0<2^t t) (ℕP.m≤n*m (2 ^ t) (suc d))

-- Raw combined fraction N / (suc d * 2^t).
-- mkℚᵘ's second argument is denominator - 1, so to get denominator
-- (suc d) * 2^t we pass (suc d) * 2^t ∸ 1.
--
-- 原始组合分数。
-- mkℚᵘ 的第二参数是分母减一，故传入相应的减一值。
rawComb : (N d t : ℕ) → ℚᵘ
rawComb N d t = mkℚᵘ (+ N) (suc d *ℕ 2 ^ t ∸ 1)

-- Raw right-hand side 1/(suc k).
-- mkℚᵘ (+ 1) k has denominator suc k, hence value 1/(suc k).
--
-- 原始右端。
-- mkℚᵘ (+ 1) k 的分母为 suc k。
rawR : (k : ℕ) → ℚᵘ
rawR k = mkℚᵘ (+ 1) k

combFrac : (N d t : ℕ) → ℚ
combFrac N d t = fromℚᵘ (rawComb N d t)

flip-≃ : {a b : ℚᵘ} → _≃_ a b → _≃_ b a
flip-≃ (*≡* e) = *≡* (sym e)

-- Cross-multiplication, general version.
--
-- 交叉乘法，一般版本。
rawCross : (N d k t : ℕ) →
  N *ℕ suc k <ℕ suc d *ℕ 2 ^ t →
  (+ N) *ℤ (+ suc k) <ℤ (+ 1) *ℤ (+ suc (suc d *ℕ 2 ^ t ∸ 1))
rawCross N d k t h =
  let dd    = suc d *ℕ 2 ^ t ∸ 1
      dd-eq : suc dd ≡ suc d *ℕ 2 ^ t
      dd-eq = suc∸1 (0<sucd*2^t d t)
  in
  ℤP.<-≤-trans
    (ℤP.≤-<-trans
       (ℤP.≤-reflexive (ℤP.+◃n≡+n (N *ℕ suc k)))
       (ℤP.<-≤-trans
          (+<+ h)
          (ℤP.≤-reflexive (cong +_ (sym dd-eq)))))
    (ℤP.≤-reflexive (sym (ℤP.*-identityˡ (+ suc dd))))

-- If N * (k+1) < (suc d) * 2^t then N / (suc d * 2^t) < 1/(k+1).
--
-- 若整数交叉相乘条件成立，则分数不等式成立。
comb-strict : (N d k t : ℕ) →
  N *ℕ suc k <ℕ suc d *ℕ 2 ^ t →
  combFrac N d t < fromℚᵘ (rawR k)
comb-strict N d k t h =
  toℚᵘ-cancel-<
    (let eqL : _≃_ (toℚᵘ (combFrac N d t)) (rawComb N d t)
         eqL = toℚᵘ-fromℚᵘ (rawComb N d t)
         eqR : _≃_ (toℚᵘ (fromℚᵘ (rawR k))) (rawR k)
         eqR = toℚᵘ-fromℚᵘ (rawR k)
         cross : _<ᵘ_ (rawComb N d t) (rawR k)
         cross = *<* (rawCross N d k t h)
         p1 : _<ᵘ_ (toℚᵘ (combFrac N d t)) (rawR k)
         p1 = <-respˡ-≃ (flip-≃ eqL) cross
         p2 : _<ᵘ_ (toℚᵘ (combFrac N d t))
                     (toℚᵘ (fromℚᵘ (rawR k)))
         p2 = <-respʳ-≃ (flip-≃ eqR) p1
     in p2)

------------------------------------------------------------------------
-- Negation of min/max
--
-- 取负下的 min/max

min-neg : ∀ a b → (neg a) ⊓ (neg b) ≡ neg (a ⊔ b)
min-neg a b = ≤-antisym upper lower
  where
    lower : neg (a ⊔ b) ≤ (neg a) ⊓ (neg b)
    lower = ⊓-glb (neg-antimono-≤ (p≤p⊔q a b))
                  (neg-antimono-≤ (p≤q⊔p a b))

    upper : (neg a) ⊓ (neg b) ≤ neg (a ⊔ b)
    upper =
      let
        helper : a ⊔ b ≡ a ⊎ a ⊔ b ≡ b → (neg a) ⊓ (neg b) ≤ neg (a ⊔ b)
        helper = λ where
          (inj₁ max≡a) → begin≤
            (neg a) ⊓ (neg b)  ≤⟨ p⊓q≤p (neg a) (neg b) ⟩
            neg a              ≈⟨ cong neg (sym max≡a) ⟩
            neg (a ⊔ b)        ≤∎
          (inj₂ max≡b) → begin≤
            (neg a) ⊓ (neg b)  ≤⟨ p⊓q≤q (neg a) (neg b) ⟩
            neg b              ≈⟨ cong neg (sym max≡b) ⟩
            neg (a ⊔ b)        ≤∎
      in helper (⊔-sel a b)

max-neg : ∀ a b → (neg a) ⊔ (neg b) ≡ neg (a ⊓ b)
max-neg a b = ≤-antisym upper lower
  where
    upper : (neg a) ⊔ (neg b) ≤ neg (a ⊓ b)
    upper = ⊔-lub (neg-antimono-≤ (p⊓q≤p a b))
                  (neg-antimono-≤ (p⊓q≤q a b))

    lower : neg (a ⊓ b) ≤ (neg a) ⊔ (neg b)
    lower =
      let
        helper : a ⊓ b ≡ a ⊎ a ⊓ b ≡ b → neg (a ⊓ b) ≤ (neg a) ⊔ (neg b)
        helper = λ where
          (inj₁ min≡a) → begin≤
            neg (a ⊓ b)        ≈⟨ cong neg min≡a ⟩
            neg a              ≤⟨ p≤p⊔q (neg a) (neg b) ⟩
            (neg a) ⊔ (neg b)  ≤∎
          (inj₂ min≡b) → begin≤
            neg (a ⊓ b)        ≈⟨ cong neg min≡b ⟩
            neg b              ≤⟨ p≤q⊔p (neg a) (neg b) ⟩
            (neg a) ⊔ (neg b)  ≤∎
      in helper (⊓-sel a b)
