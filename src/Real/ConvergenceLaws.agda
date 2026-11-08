------------------------------------------------------------------------
-- Boundedness and multiplication law for arbitrary-tolerance convergence
--
-- 任意容差收敛的有界性与乘法极限律
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module Real.ConvergenceLaws where

open import Data.Nat using (ℕ; zero; suc; _≥_; s≤s; z≤n)
  renaming (_⊔_ to _⊔N_; _<_ to _<N_; _≤_ to _≤N_)
open import Data.Nat.Properties using
  (m≤n⇒m<n∨m≡n; m<1+n⇒m≤n; ≤-antisym; ≤-pred)
open import Data.Nat.Properties using (m≤m⊔n; m≤n⊔m; ≤-total)
  renaming (≤-trans to ≤N-trans)
open import Data.Product using (Σ; _×_; _,_)
open import Data.Sum using (inj₁; inj₂)
open import Data.Rational using (ℚ; 0ℚ; 1ℚ; _+_; _-_; _*_; _<_; _≤_; _⊔_; ∣_∣)
open import Data.Rational.Base using
  (Positive; positive; nonNegative; 1/_; NonZero)
open import Data.Rational.Properties using
  (≤-refl; ≤-reflexive; ≤-trans; ≤-<-trans; <⇒≤; +-mono-<; +-mono-≤; +-mono-≤-<
  ; +-identityʳ; +-comm; *-assoc; *-comm; *-identityʳ; *-inverseʳ; *-monoˡ-<-pos
  ; *-monoʳ-<-pos; 1/pos⇒pos; *-monoʳ-≤-nonNeg; *-monoˡ-≤-nonNeg; pos*pos⇒pos
  ; positive⁻¹; 0≤∣p∣; pos⇒nonZero; ∣p*q∣≡∣p∣*∣q∣; ∣p+q∣≤∣p∣+∣q∣
  ; p≤p⊔q; p≤q⊔p)
open import Function using (case_of_)
open import Relation.Binary.PropositionalEquality using
  (_≡_; sym; trans; cong; cong₂; subst; module ≡-Reasoning)
open ≡-Reasoning

open import Base.RationalRing using (0<1; 0≤1)
open import Real using (half)
open import Real.Convergence using (Converges)
open import Real.Interval.Kit using (B+1-pos; two-half; 0<half)
open import Real.Interval.Mul using (split-prod; cancelʳ)

------------------------------------------------------------------------
-- Prefix maximum of absolute values
--
-- 绝对值的前缀最大值

-- Maximum of ∣ g k ∣ over k < n.
--
-- 前 n 项绝对值的最大值。
abs-max : ℕ → (ℕ → ℚ) → ℚ
abs-max zero    g = 0ℚ
abs-max (suc n) g = abs-max n g ⊔ ∣ g n ∣

-- The prefix maximum is nonnegative.
--
-- 前缀最大值非负。
0≤abs-max : ∀ n g → 0ℚ ≤ abs-max n g
0≤abs-max zero    g = ≤-refl
0≤abs-max (suc n) g =
  ≤-trans (0≤abs-max n g) (p≤p⊔q (abs-max n g) ∣ g n ∣)

-- Inductive helper: k ≤ n places ∣ g k ∣ within abs-max (suc n).
--
-- 归纳辅助引理：下标不超过 n 的项落在当前前缀最大值之内。
abs-max-≤ : ∀ n g k → k ≤N n → ∣ g k ∣ ≤ abs-max (suc n) g
abs-max-≤ zero g k k≤0 = 
      let k≡0 = ≤-antisym k≤0 z≤n
      in subst (λ z → ∣ g z ∣ ≤ abs-max 1 g) (sym k≡0) (p≤q⊔p 0ℚ ∣ g 0 ∣)
abs-max-≤ (suc n) g k k≤sucn = 
      case m≤n⇒m<n∨m≡n k≤sucn of λ
      { (inj₁ k<sucn) -> 
          let k≤n = m<1+n⇒m≤n k<sucn
              rec = abs-max-≤ n g k k≤n
          in ≤-trans rec (p≤p⊔q (abs-max (suc n) g) ∣ g (suc n) ∣)
      ; (inj₂ k≡sucn) -> 
          subst (λ z → ∣ g z ∣ ≤ abs-max (suc n) g ⊔ ∣ g (suc n) ∣) (sym k≡sucn)
                (p≤q⊔p (abs-max (suc n) g) ∣ g (suc n) ∣)
      }

-- Every earlier absolute value is below the prefix maximum.
--
-- 每个更早的绝对值都不超过前缀最大值。
abs-max-upper : ∀ n g k → k <N n → ∣ g k ∣ ≤ abs-max n g
abs-max-upper zero    g k ()
abs-max-upper (suc n) g k k<sucn = abs-max-≤ n g k (≤-pred k<sucn)

------------------------------------------------------------------------
-- A convergent sequence is bounded
--
-- 收敛序列必有界

-- Adding one gives a non-strict upper shift.
--
-- 加一给出非严格的上移界。
plus1 : ∀ x → x ≤ x + 1ℚ
plus1 x =
  ≤-trans (≤-reflexive (sym (+-identityʳ x)))
          (+-mono-≤ (≤-refl {x}) 0≤1)

-- Every convergent rational sequence admits a uniform nonnegative bound.
--
-- 每个收敛的有理序列都有一致的非负界。
bounded-converges : ∀ {g l} → Converges g l →
  Σ ℚ λ B → 0ℚ ≤ B × (∀ n → ∣ g n ∣ ≤ B)
bounded-converges {g} {l} cv =
  let N , w = cv 1ℚ 0<1
      tailB = ∣ l ∣ + 1ℚ
      pre = abs-max (suc N) g
      B = tailB ⊔ pre

      0<tailB : 0ℚ < tailB
      0<tailB = positive⁻¹ tailB ⦃ B+1-pos ∣ l ∣ (0≤∣p∣ l) ⦄

      0≤B : 0ℚ ≤ B
      0≤B = ≤-trans (<⇒≤ 0<tailB) (p≤p⊔q tailB pre)

      -- Past the modulus, the triangle inequality places g n within
      -- ∣ l ∣ + 1.
      --
      -- 越过模数后，三角不等式给出统一上界。
      tail-≤ : ∀ n → n ≥ N → ∣ g n ∣ ≤ B
      tail-≤ n n≥N =
        let h : ∣ g n - l ∣ < 1ℚ
            h = w n n≥N
            id : g n ≡ l + (g n - l)
            id = trans (sym (cancelʳ (g n) l))
                       (+-comm (g n - l) l)
            tri : ∣ g n ∣ ≤ ∣ l ∣ + ∣ g n - l ∣
            tri = subst (λ z → ∣ z ∣ ≤ ∣ l ∣ + ∣ g n - l ∣) (sym id)
                    (∣p+q∣≤∣p∣+∣q∣ l (g n - l))
            step : ∣ l ∣ + ∣ g n - l ∣ < tailB
            step = +-mono-≤-< (≤-refl {x = ∣ l ∣}) h
        in ≤-trans (<⇒≤ (≤-<-trans tri step)) (p≤p⊔q tailB pre)

      -- Before the modulus, the prefix maximum applies.
      --
      -- 模数之前由前缀最大值支配。
      pre-≤ : ∀ n → n <N suc N → ∣ g n ∣ ≤ B
      pre-≤ n n<sN =
        ≤-trans (abs-max-upper (suc N) g n n<sN)
                (p≤q⊔p tailB pre)

      bound : ∀ n → ∣ g n ∣ ≤ B
      bound n = case ≤-total N n of λ
        { (inj₁ a) → tail-≤ n a
        ; (inj₂ b) → pre-≤ n (s≤s b)
        }
  in B , 0≤B , bound

------------------------------------------------------------------------
-- Multiplication law
--
-- 乘法极限律

-- Cancelling a positive divisor: x * (y ÷ x) ≡ y.
--
-- 消去正除数。
/-cancel : ∀ x y → .{{px : Positive x}} → .{{nzx : NonZero x}} →
  x * (y * (1/_ x ⦃ nzx ⦄)) ≡ y
/-cancel x y {{px}} {{nzx}} =
  begin
    x * (y * 1/_ x ⦃ nzx ⦄)
      ≡⟨ sym (*-assoc x y (1/_ x ⦃ nzx ⦄)) ⟩
    (x * y) * 1/_ x ⦃ nzx ⦄
      ≡⟨ cong (_* 1/_ x ⦃ nzx ⦄) (*-comm x y) ⟩
    (y * x) * 1/_ x ⦃ nzx ⦄
      ≡⟨ *-assoc y x (1/_ x ⦃ nzx ⦄) ⟩
    y * (x * 1/_ x ⦃ nzx ⦄)
      ≡⟨ cong (y *_) (*-inverseʳ x ⦃ nzx ⦄) ⟩
    y * 1ℚ
      ≡⟨ *-identityʳ y ⟩
    y
  ∎

-- Products of convergent sequences converge to the product of limits.
--
-- 收敛序列之积收敛到极限之积。
mul-converges : ∀ {g h l m} →
  Converges g l → Converges h m →
  Converges (λ n → g n * h n) (l * m)
mul-converges {g} {h} {l} {m} cg ch e 0<e =
  let B0 , 0≤B0 , g-bound = bounded-converges cg

      -- B = B0 + 1 and M' = ∣ m ∣ + 1 are always strictly positive, so
      -- the reciprocal tolerances below never divide by zero even when
      -- the bound or the limit is zero.
      --
      -- B 与 M' 恒严格为正，下述倒数容差不会在界或极限为零时除零。
      B = B0 + 1ℚ
      B-pos : Positive B
      B-pos = B+1-pos B0 0≤B0
      B-nz : NonZero B
      B-nz = pos⇒nonZero B {{B-pos}}
      g≤B : ∀ n → ∣ g n ∣ ≤ B
      g≤B n = ≤-trans (g-bound n) (plus1 B0)

      Mabs = ∣ m ∣
      M' = Mabs + 1ℚ
      M'-pos : Positive M'
      M'-pos = B+1-pos Mabs (0≤∣p∣ m)
      M'-nz : NonZero M'
      M'-nz = pos⇒nonZero M' {{M'-pos}}
      m≤M' : Mabs ≤ M'
      m≤M' = plus1 Mabs

      -- Half the target tolerance goes to each summand.
      --
      -- 目标容差的一半分给两个加项。
      s = e * half
      0<s : 0ℚ < s
      0<s = positive⁻¹ s
        ⦃ pos*pos⇒pos e ⦃ positive 0<e ⦄ half ⦃ positive 0<half ⦄ ⦄

      th = s * (1/_ B ⦃ B-nz ⦄)
      th-pos : Positive th
      th-pos = pos*pos⇒pos s ⦃ positive 0<s ⦄ (1/_ B ⦃ B-nz ⦄) ⦃ 1/pos⇒pos B ⦃ B-pos ⦄ ⦄
      0<th : 0ℚ < th
      0<th = positive⁻¹ th ⦃ th-pos ⦄

      tg = s * (1/_ M' ⦃ M'-nz ⦄)
      tg-pos : Positive tg
      tg-pos = pos*pos⇒pos s ⦃ positive 0<s ⦄ (1/_ M' ⦃ M'-nz ⦄) ⦃ 1/pos⇒pos M' ⦃ M'-pos ⦄ ⦄
      0<tg : 0ℚ < tg
      0<tg = positive⁻¹ tg ⦃ tg-pos ⦄

      Nh , ph = ch th 0<th
      Ng , pg = cg tg 0<tg
      N = Nh ⊔N Ng
  in N , λ n n≥N →
    let h< : ∣ h n - m ∣ < th
        h< = ph n (≤N-trans (m≤m⊔n Nh Ng) n≥N)
        g< : ∣ g n - l ∣ < tg
        g< = pg n (≤N-trans (m≤n⊔m Nh Ng) n≥N)

        -- split-prod rewrites the product difference into the two
        -- separately controlled terms.
        --
        -- split-prod 把乘积之差改写成两个分别受控的加项。
        eq : ∣ g n * h n - l * m ∣
           ≡ ∣ g n * (h n - m) + (g n - l) * m ∣
        eq = cong ∣_∣ (split-prod (g n) l (h n) m)

        tri≤ : ∣ g n * (h n - m) + (g n - l) * m ∣
             ≤ ∣ g n * (h n - m) ∣ + ∣ (g n - l) * m ∣
        tri≤ = ∣p+q∣≤∣p∣+∣q∣ (g n * (h n - m)) ((g n - l) * m)

        e1 : ∣ g n * (h n - m) ∣ ≡ ∣ g n ∣ * ∣ h n - m ∣
        e1 = ∣p*q∣≡∣p∣*∣q∣ (g n) (h n - m)
        e2 : ∣ (g n - l) * m ∣ ≡ ∣ g n - l ∣ * Mabs
        e2 = ∣p*q∣≡∣p∣*∣q∣ (g n - l) m

        t1≤ : ∣ g n ∣ * ∣ h n - m ∣ ≤ B * ∣ h n - m ∣
        t1≤ = *-monoʳ-≤-nonNeg ∣ h n - m ∣
                ⦃ nonNegative (0≤∣p∣ (h n - m)) ⦄ (g≤B n)
        t1< : B * ∣ h n - m ∣ < B * th
        t1< = *-monoʳ-<-pos B ⦃ B-pos ⦄ h<
        t1 : ∣ g n ∣ * ∣ h n - m ∣ < B * th
        t1 = ≤-<-trans t1≤ t1<

        t2≤ : ∣ g n - l ∣ * Mabs ≤ ∣ g n - l ∣ * M'
        t2≤ = *-monoˡ-≤-nonNeg ∣ g n - l ∣
                ⦃ nonNegative (0≤∣p∣ (g n - l)) ⦄ m≤M'
        t2< : ∣ g n - l ∣ * M' < tg * M'
        t2< = *-monoˡ-<-pos M' ⦃ M'-pos ⦄ g<
        t2 : ∣ g n - l ∣ * Mabs < tg * M'
        t2 = ≤-<-trans t2≤ t2<

        sum< : ∣ g n ∣ * ∣ h n - m ∣ + ∣ g n - l ∣ * Mabs
             < B * th + tg * M'
        sum< = +-mono-< t1 t2

        c1 : B * th ≡ s
        c1 = /-cancel B s ⦃ B-pos ⦄ ⦃ B-nz ⦄
        c2 : tg * M' ≡ s
        c2 = trans (*-comm tg M') (/-cancel M' s ⦃ M'-pos ⦄ ⦃ M'-nz ⦄)

        step1 : ∣ g n * h n - l * m ∣
              ≤ ∣ g n ∣ * ∣ h n - m ∣ + ∣ g n - l ∣ * Mabs
        step1 = subst (λ z → z ≤ ∣ g n ∣ * ∣ h n - m ∣ + ∣ g n - l ∣ * Mabs)
                      (sym eq)
                      (≤-trans tri≤ (≤-reflexive (cong₂ _+_ e1 e2)))

        step2 : ∣ g n * h n - l * m ∣ < B * th + tg * M'
        step2 = ≤-<-trans step1 sum<

        final : ∣ g n * h n - l * m ∣ < e
        final =
          subst (λ z → ∣ g n * h n - l * m ∣ < z)
                (trans (cong₂ _+_ c1 c2) (two-half e))
                step2
    in final
