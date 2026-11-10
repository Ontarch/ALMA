------------------------------------------------------------------------
-- Arbitrary-tolerance convergence of rational sequences
--
-- 有理序列的任意容差收敛
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module Real.Convergence where

open import Data.Empty using (⊥-elim)
open import Data.Nat using (ℕ; _≥_; _⊔_)
open import Data.Nat.Properties using (m≤m⊔n; m≤n⊔m; ≤-trans)
open import Data.Product using (Σ; _,_)
open import Data.Rational using (ℚ; 0ℚ; _+_; _-_; _*_; _<_; _≤_; ∣_∣)
  renaming (-_ to neg)
open import Data.Rational.Base using (positive)
open import Data.Rational.Properties using
  (≤-refl; ≤-<-trans; <-irrefl; +-mono-<; +-identityˡ; +-inverseʳ; 0≤p⇒∣p∣≡p
  ; positive⁻¹; pos*pos⇒pos; ∣p+q∣≤∣p∣+∣q∣; ∣-p∣≡∣p∣; 0≤∣p∣; ≤⇒≯
  ; ∣p∣≡0⇒p≡0; <-cmp; neg-distrib-+)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; sym; trans; cong; subst)
open import Relation.Nullary.Negation using (¬_)
open import Relation.Binary.Definitions using (tri<; tri≈; tri>)

open import Base.RationalRing using (neg-involutive)
open import Real using (half)
open import Real.Interval.Kit using (0<half; tri-diff; two-half; abs-swap)
open import Real.Interval.Rational using (sub-add)
open import Real.Interval.Mul using (cancelʳ)

------------------------------------------------------------------------
-- Convergence of a raw rational sequence
--
-- Unlike the layer-wise _⟶_ on RealI, convergence here quantifies over
-- every positive rational tolerance. This is the standard notion and
-- supports all algebraic limit laws.
--
-- 原始有理序列的收敛
--
-- 与 RealI 上逐层的 _⟶_ 不同，这里对每个正有理容差量化，是标准收敛
-- 概念，可支撑全部极限运算律。

Converges : (ℕ → ℚ) → ℚ → Set
Converges g l =
  ∀ (e : ℚ) → 0ℚ < e →
    Σ ℕ λ N → ∀ n → n ≥ N → ∣ g n - l ∣ < e

------------------------------------------------------------------------
-- Uniqueness of limits
--
-- 极限唯一

-- For every positive tolerance the gap is less than twice it.
--
-- 对每个正容差，间隙小于其两倍。
gap-bound : ∀ {g l m} (cl : Converges g l) (cm : Converges g m)
  (e : ℚ) (0<e : 0ℚ < e) → ∣ l - m ∣ < e + e
gap-bound {g} {l} {m} cl cm e 0<e =
  let Nl , pl = cl e 0<e
      Nm , pm = cm e 0<e
      N = Nl ⊔ Nm
      n = N
      n≥Nl : n ≥ Nl
      n≥Nl = m≤m⊔n Nl Nm
      n≥Nm : n ≥ Nm
      n≥Nm = m≤n⊔m Nl Nm
      a = ∣ g n - l ∣
      b = ∣ g n - m ∣
      ha : a < e
      ha = pl n n≥Nl
      hb : b < e
      hb = pm n n≥Nm
      -- ∣ l - m ∣ ≤ a + b < e + e
      raw : ∣ l - m ∣ ≤ ∣ l - g n ∣ + b
      raw = tri-diff l (g n) m
      swap : ∣ l - g n ∣ ≡ a
      swap = abs-swap l (g n)
      tri : ∣ l - m ∣ ≤ a + b
      tri = subst (λ z → ∣ l - m ∣ ≤ z + b) swap raw
      sum< : a + b < e + e
      sum< = +-mono-< ha hb
  in ≤-<-trans tri sum<

-- A nonnegative point that is not positive must be zero.
--
-- 非负且不为正的点必为零。
nonneg-no-pos : ∀ {x} → 0ℚ ≤ x → ¬ (0ℚ < x) → x ≡ 0ℚ
nonneg-no-pos {x} 0≤x ¬x>0 with <-cmp x 0ℚ
nonneg-no-pos 0≤x ¬x>0 | tri< x<0 _ _ = ⊥-elim (≤⇒≯ 0≤x x<0)
nonneg-no-pos 0≤x ¬x>0 | tri≈ _ x≡0 _ = x≡0
nonneg-no-pos 0≤x ¬x>0 | tri> _ _ 0<x = ⊥-elim (¬x>0 0<x)

-- The gap is nonnegative; if it were positive, halving it yields a
-- tolerance contradicting gap-bound.
--
-- 间隙非负；若它为正，取其半作容差即与间隙界矛盾。
unique : ∀ {g l m} → Converges g l → Converges g m → l ≡ m
unique {g} {l} {m} cl cm =
  let gap = ∣ l - m ∣
      0≤gap : 0ℚ ≤ gap
      0≤gap = 0≤∣p∣ (l - m)
      no-pos : ¬ (0ℚ < gap)
      no-pos 0<gap =
        let e = gap * half
            0<e : 0ℚ < e
            0<e = positive⁻¹ e
                    ⦃ pos*pos⇒pos gap ⦃ positive 0<gap ⦄
                                  half ⦃ positive 0<half ⦄ ⦄
            h = gap-bound {g} {l} {m} cl cm e 0<e
            ee≡gap : e + e ≡ gap
            ee≡gap = two-half gap
        in <-irrefl refl (subst (λ z → gap < z) ee≡gap h)
      gap≡0 : gap ≡ 0ℚ
      gap≡0 = nonneg-no-pos 0≤gap no-pos
      l-m≡0 : l - m ≡ 0ℚ
      l-m≡0 = ∣p∣≡0⇒p≡0 (l - m) gap≡0
  in sub-eq l m l-m≡0
  where
  sub-eq : ∀ a b → a - b ≡ 0ℚ → a ≡ b
  sub-eq a b h =
    trans (sym (cancelʳ a b))
      (trans (cong (_+ b) h) (+-identityˡ b))

------------------------------------------------------------------------
-- Constant sequences
--
-- 常序列

-- Constant sequences converge to their value.
--
-- 常序列收敛到其值。
const-converges : ∀ l → Converges (λ _ → l) l
const-converges l e 0<e =
  let p≡0 : l - l ≡ 0ℚ
      p≡0 = +-inverseʳ l
      abs0 : ∣ 0ℚ ∣ ≡ 0ℚ
      abs0 = 0≤p⇒∣p∣≡p ≤-refl
      zero≡ : ∣ l - l ∣ ≡ 0ℚ
      zero≡ = subst (λ z → ∣ z ∣ ≡ 0ℚ) (sym p≡0) abs0
  in 0 , λ n _ → subst (λ z → z < e) (sym zero≡) 0<e

------------------------------------------------------------------------
-- Negation
--
-- 取负

-- Absolute value after negating both terms.
--
-- 两项同时取负后的绝对值。
neg-abs : (a b : ℚ) → ∣ neg a - neg b ∣ ≡ ∣ a - b ∣
neg-abs a b =
  let s1 : neg a - neg b ≡ neg a + b
      s1 = cong (neg a +_) (neg-involutive b)
      s3 : neg (a - b) ≡ neg a + b
      s3 = trans (neg-distrib-+ a (neg b))
                 (cong (neg a +_) (neg-involutive b))
      full : neg a - neg b ≡ neg (a - b)
      full = trans s1 (sym s3)
  in trans (cong ∣_∣ full) (∣-p∣≡∣p∣ (a - b))

-- Transport a strict bound across simultaneous negation.
--
-- 同时取负下严格界的传递。
transport-neg : (e a b : ℚ) → ∣ a - b ∣ < e → ∣ neg a - neg b ∣ < e
transport-neg e a b h =
  subst {A = ℚ} (λ z → z < e) (sym (neg-abs a b)) h

-- Negation of a convergent sequence converges to the negated limit.
--
-- 收敛序列的取负收敛到极限的取负。
neg-converges : ∀ {g l} → Converges g l →
  Converges (λ n → neg (g n)) (neg l)
neg-converges {g} {l} cg e 0<e =
  let N , p = cg e 0<e
  in N , λ n n≥N → transport-neg e (g n) l (p n n≥N)

------------------------------------------------------------------------
-- Addition
--
-- 加法

-- Sums of convergent sequences converge to the sum of limits.
--
-- 收敛序列之和收敛到极限之和。
add-converges : ∀ {g h l m} → Converges g l → Converges h m →
  Converges (λ n → g n + h n) (l + m)
add-converges {g} {h} {l} {m} cg ch e 0<e =
  let t = e * half
      0<t : 0ℚ < t
      0<t = positive⁻¹ t
              ⦃ pos*pos⇒pos e ⦃ positive 0<e ⦄
                        half ⦃ positive 0<half ⦄ ⦄
      Ng , pg = cg t 0<t
      Nh , ph = ch t 0<t
      N = Ng ⊔ Nh
      tri : ∀ n →
        ∣ (g n + h n) - (l + m) ∣ ≤
          ∣ g n - l ∣ + ∣ h n - m ∣
      tri n =
        let path : (g n - l) + (h n - m) ≡ (g n + h n) - (l + m)
            path = sym (sub-add (g n) (h n) l m)
        in subst (λ z → ∣ z ∣ ≤ ∣ g n - l ∣ + ∣ h n - m ∣) path
             (∣p+q∣≤∣p∣+∣q∣ (g n - l) (h n - m))
  in N , λ n n≥N →
       let a< : ∣ g n - l ∣ < t
           a< = pg n (≤-trans (m≤m⊔n Ng Nh) n≥N)
           b< : ∣ h n - m ∣ < t
           b< = ph n (≤-trans (m≤n⊔m Ng Nh) n≥N)
           sum< : ∣ g n - l ∣ + ∣ h n - m ∣ < t + t
           sum< = +-mono-< a< b<
           tt : t + t ≡ e
           tt = two-half e
       in ≤-<-trans (tri n)
           (subst (λ z → ∣ g n - l ∣ + ∣ h n - m ∣ < z) tt sum<)
