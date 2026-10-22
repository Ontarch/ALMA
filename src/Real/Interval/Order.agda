------------------------------------------------------------------------
-- Order on real intervals
--
-- 实数区间上的序
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module Real.Interval.Order where

open import Data.Nat using (ℕ; zero; suc; _∸_; _^_)
  renaming (_≤_ to _≤ℕ_; _<_ to _<ℕ_; _+_ to _+ℕ_)
open import Data.Nat.Properties using (m∸n+n≡m; +-suc; m≤m+n)
  renaming (+-comm to +-commℕ; +-identityʳ to +-identityʳℕ)
open import Data.Rational using
  (ℚ; 0ℚ; 1ℚ; _-_; _*_; _<_; _≤_; NonZero; Positive; NonNegative)
open import Data.Rational.Base using (1/_; positive)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Rational.Properties using
  (+-mono-≤; neg-antimono-≤; *-assoc; *-comm; *-inverseʳ; *-inverseˡ; *-identityˡ
  ; *-identityʳ; *-zeroˡ; *-monoʳ-≤-nonNeg; *-monoˡ-<-pos; ≤-reflexive; ≤-trans
  ; <⇒≤; ≤-<-trans; pos⇒nonZero; pos⇒nonNeg; 1/pos⇒pos; <-cmp)
  renaming (<-trans to <-transℚ; <-irrefl to <-irreflℚ)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; cong; sym; subst; module ≡-Reasoning)
open ≡-Reasoning
open import Relation.Nullary.Negation using (¬_)
open import Relation.Binary.Definitions using (Tri; tri<; tri≈; tri>)

open import Real using (embed; reciprocal-cong; embed-suc-pos)
open import Real.Interval using (RealI)
open import Real.IntervalEquiv using
  (node; width; width-n; recipPow2; bound-w; embed-mono-<; n<2^n; suc∸1; 0<2^n; pos-2^t)
open import Real.Interval.Rational using (¬<⇒≥; pos-diff)
open import Real.Interval.Reasoning

------------------------------------------------------------------------
-- Bounds of the n-th node
--
-- 第 n 个节点的上下界

l : RealI → ℕ → ℚ
l r n = RealI.l (node r n)

u : RealI → ℕ → ℚ
u r n = RealI.u (node r n)

------------------------------------------------------------------------
-- Strict order
--
-- x <ℝ y when at some level the upper bound of x lies below the lower
-- bound of y.
--
-- 严格序
--
-- 若在某层级 x 的上界低于 y 的下界，则 x <ℝ y。

infix 4 _<ℝ_

_<ℝ_ : RealI → RealI → Set
x <ℝ y = Σ ℕ (λ n → u x n < l y n)

------------------------------------------------------------------------
-- Monotonicity of the bounds
--
-- The lower bounds are non-decreasing and the upper bounds
-- non-increasing along nodes. These give l-mono' and u-mono', used to
-- bring two witnesses to a common level.
--
-- 界的单调性
--
-- 沿节点方向，下界不减、上界不增。由此得 l-mono' 与 u-mono'，用于
-- 把两个见证移到同一层级。

l-step : (r : RealI) (n : ℕ) → l r n ≤ l r (suc n)
l-step r n = proj₁ (RealI.nest (node r n))

u-step : (r : RealI) (n : ℕ) → u r (suc n) ≤ u r n
u-step r n = proj₁ (proj₂ (RealI.nest (node r n)))

l-up : (r : RealI) (n d : ℕ) → l r n ≤ l r (n +ℕ d)
l-up r n zero    = ≤-reflexive (cong (l r) (sym (+-identityʳℕ n)))
l-up r n (suc d) =
  ≤-trans (l-up r n d)
          (subst (λ k → l r (n +ℕ d) ≤ l r k)
                  (sym (+-suc n d))
                  (l-step r (n +ℕ d)))

u-down : (r : RealI) (n d : ℕ) → u r (n +ℕ d) ≤ u r n
u-down r n zero    = ≤-reflexive (cong (u r) (+-identityʳℕ n))
u-down r n (suc d) =
  ≤-trans
    (subst (λ k → u r k ≤ u r (n +ℕ d))
            (sym (+-suc n d))
            (u-step r (n +ℕ d)))
    (u-down r n d)

l-mono' : (r : RealI) {n m : ℕ} → n ≤ℕ m → l r n ≤ l r m
l-mono' r {n} {m} n≤m =
  subst (λ k → l r n ≤ l r k)
        (begin
           n +ℕ (m ∸ n)
             ≡⟨ +-commℕ n (m ∸ n) ⟩
           (m ∸ n) +ℕ n
             ≡⟨ m∸n+n≡m n≤m ⟩
           m
             ∎)
        (l-up r n (m ∸ n))

u-mono' : (r : RealI) {n m : ℕ} → n ≤ℕ m → u r m ≤ u r n
u-mono' r {n} {m} n≤m =
  subst (λ k → u r k ≤ u r n)
        (begin
           n +ℕ (m ∸ n)
             ≡⟨ +-commℕ n (m ∸ n) ⟩
           (m ∸ n) +ℕ n
             ≡⟨ m∸n+n≡m n≤m ⟩
           m
             ∎)
        (u-down r n (m ∸ n))

------------------------------------------------------------------------
-- Irreflexivity and transitivity
--
-- 非自反与传递

<-irrefl : (x : RealI) → ¬ (x <ℝ x)
<-irrefl x (n , uxn<lxn) =
  <-irreflℚ refl (<-transℚ (RealI.lo (node x n)) uxn<lxn)

<-trans : ∀ {x y z} → x <ℝ y → y <ℝ z → x <ℝ z
<-trans {x} {y} {z} (n , uxn<lyn) (m , uym<lzm) =
  let k   = n +ℕ m
      n≤k = m≤m+n n m
      m≤k = subst (λ j → m ≤ℕ j) (+-commℕ m n) (m≤m+n m n)

      uxk≤uxn : u x k ≤ u x n
      uxk≤uxn = u-mono' x n≤k

      lyn≤lyk : l y n ≤ l y k
      lyn≤lyk = l-mono' y n≤k

      uyk≤uym : u y k ≤ u y m
      uyk≤uym = u-mono' y m≤k

      lzm≤lzk : l z m ≤ l z k
      lzm≤lzk = l-mono' z m≤k

      lyk≤uyk : l y k ≤ u y k
      lyk≤uyk = <⇒≤ (RealI.lo (node y k))

      -- step1' : u x k < l y n
      step1' : u x k < l y n
      step1' = u x k ≤⟨ uxk≤uxn ⟩< uxn<lyn

      -- step1 : u x k < l y k
      step1 : u x k < l y k
      step1 = u x k <⟨ step1' ⟩≤[ lyn≤lyk ]

      -- step2 : u x k < u y k
      step2 : u x k < u y k
      step2 = u x k <⟨ step1 ⟩≤[ lyk≤uyk ]

      -- step3' : u y k < l z m
      step3' : u y k < l z m
      step3' = u y k ≤⟨ uyk≤uym ⟩< uym<lzm

      -- step3 : u y k < l z k
      step3 : u y k < l z k
      step3 = u y k <⟨ step3' ⟩≤[ lzm≤lzk ]
  in k , <-transℚ step2 step3

------------------------------------------------------------------------
-- Cotransitivity
--
-- From x < z one may decide x < y or y < z. Let d = l z n − u x n > 0
-- be the gap at the separating level. Choose N so that the width of y
-- at N is below d via bound-w; then at level m = n + N the two
-- alternatives are exhaustive, since if neither held the width of y at
-- m would be at least d, contradicting width-ym < d.
--
-- 余传递
--
-- 由 x < z 可判定 x < y 或 y < z。设 d = l z n − u x n > 0 为分离
-- 层级的间隙。经 bound-w 选取 N 使 y 在 N 处的宽度低于 d；于是在
-- 层级 m = n + N 两择一穷尽：若二者皆不成立，则 y 在 m 处的宽度将
-- 不低于 d，与 width-ym < d 矛盾。

<-cotrans : ∀ {x y z} → x <ℝ z → (x <ℝ y) ⊎ (y <ℝ z)
<-cotrans {x} {y} {z} (n , uxn<lzn) = go
  where
    d : ℚ
    d = l z n - u x n

    d>0 : 0ℚ < d
    d>0 = pos-diff (u x n) (l z n) uxn<lzn

    d-pos : Positive d
    d-pos = positive d>0

    d-nz : NonZero d
    d-nz = pos⇒nonZero d {{d-pos}}

    w0 : ℚ
    w0 = u y 0 - l y 0

    w0>0 : 0ℚ < w0
    w0>0 = pos-diff (l y 0) (u y 0) (RealI.lo y)

    w0≥0 : 0ℚ ≤ w0
    w0≥0 = <⇒≤ w0>0

    invd : ℚ
    invd = 1/_ d {{d-nz}}

    invd-pos : Positive invd
    invd-pos = 1/pos⇒pos d {{d-pos}}

    invd-nn : NonNegative invd
    invd-nn = pos⇒nonNeg invd {{invd-pos}}

    q : ℚ
    q = w0 * invd

    q≥0 : 0ℚ ≤ q
    q≥0 =
      subst (λ z → z ≤ q)
            (*-zeroˡ invd)
            (*-monoʳ-≤-nonNeg invd {{invd-nn}} w0≥0)

    N : ℕ
    N = proj₁ (bound-w q q≥0)

    N-bound : q ≤ embed N
    N-bound = proj₂ (bound-w q q≥0)

    N<2N : N <ℕ 2 ^ N
    N<2N = n<2^n N

    q<embed2N : q < embed (2 ^ N)
    q<embed2N = ≤-<-trans N-bound (embed-mono-< N<2N)

    eN-nz : NonZero (embed (2 ^ N))
    eN-nz = pos⇒nonZero (embed (2 ^ N)) {{pos-2^t N}}

    eN-pos : Positive (embed (2 ^ N))
    eN-pos = pos-2^t N

    inv2N : ℚ
    inv2N = 1/_ (embed (2 ^ N)) {{eN-nz}}

    inv2N-pos : Positive inv2N
    inv2N-pos = 1/pos⇒pos (embed (2 ^ N)) {{eN-pos}}

    w0≡q·d : w0 ≡ q * d
    w0≡q·d = sym (begin
      q * d
        ≡⟨ *-assoc w0 invd d ⟩
      w0 * (invd * d)
        ≡⟨ cong (w0 *_) (*-inverseˡ d {{d-nz}}) ⟩
      w0 * 1ℚ
        ≡⟨ *-identityʳ w0 ⟩
      w0
        ∎)

    w0<e2N·d : w0 < embed (2 ^ N) * d
    w0<e2N·d =
      ≤-<-trans
        (≤-reflexive w0≡q·d)
        (*-monoˡ-<-pos d {{d-pos}} q<embed2N)

    cancel : (embed (2 ^ N) * d) * inv2N ≡ d
    cancel = begin
      (embed (2 ^ N) * d) * inv2N
        ≡⟨ *-assoc (embed (2 ^ N)) d inv2N ⟩
      embed (2 ^ N) * (d * inv2N)
        ≡⟨ cong (embed (2 ^ N) *_) (*-comm d inv2N) ⟩
      embed (2 ^ N) * (inv2N * d)
        ≡⟨ sym (*-assoc (embed (2 ^ N)) inv2N d) ⟩
      (embed (2 ^ N) * inv2N) * d
        ≡⟨ cong (_* d) (*-inverseʳ (embed (2 ^ N)) {{eN-nz}}) ⟩
      1ℚ * d
        ≡⟨ *-identityˡ d ⟩
      d
        ∎

    w0·inv2N<d : w0 * inv2N < d
    w0·inv2N<d =
      subst (λ z → w0 * inv2N < z)
            cancel
            (*-monoˡ-<-pos inv2N {{inv2N-pos}} w0<e2N·d)

    recipPow2-eq : recipPow2 N ≡ inv2N
    recipPow2-eq =
      reciprocal-cong (embed (suc (2 ^ N ∸ 1))) (embed (2 ^ N))
        {{pos⇒nonZero (embed (suc (2 ^ N ∸ 1))) {{embed-suc-pos}}}}
        {{eN-nz}}
        (cong embed (suc∸1 (0<2^n N)))

    width-yN-≤ : width y N ≤ w0 * inv2N
    width-yN-≤ =
      subst (λ z → width y N ≤ w0 * z)
            recipPow2-eq
            (width-n y N)

    width-yN<d : width y N < d
    width-yN<d = ≤-<-trans width-yN-≤ w0·inv2N<d

    m : ℕ
    m = n +ℕ N

    n≤m : n ≤ℕ m
    n≤m = m≤m+n n N

    N≤m : N ≤ℕ m
    N≤m = subst (λ j → N ≤ℕ j) (+-commℕ N n) (m≤m+n N n)

    uxm lzm uym lym : ℚ
    uxm = u x m
    lzm = l z m
    uym = u y m
    lym = l y m

    width-ym<d : u y m - l y m < d
    width-ym<d =
      ≤-<-trans
        (+-mono-≤ (u-mono' y N≤m)
                  (neg-antimono-≤ (l-mono' y N≤m)))
        width-yN<d

    absurd : ¬ (uym < lzm) → ¬ (uxm < lym) → ⊥
    absurd ¬uym<lzm ¬uxm<lym =
      let
        lzm≤uym : lzm ≤ uym
        lzm≤uym = ¬<⇒≥ ¬uym<lzm

        lym≤uxm : lym ≤ uxm
        lym≤uxm = ¬<⇒≥ ¬uxm<lym

        width-ym≥d : d ≤ uym - lym
        width-ym≥d =
          begin≤
            d
              ≤⟨ +-mono-≤ (l-mono' z n≤m)
                          (neg-antimono-≤ (u-mono' x n≤m)) ⟩
            lzm - uxm
              ≤⟨ +-mono-≤ lzm≤uym (neg-antimono-≤ lym≤uxm) ⟩
            uym - lym
          ≤∎
      in <-irreflℚ refl (≤-<-trans width-ym≥d width-ym<d)

    go : (x <ℝ y) ⊎ (y <ℝ z)
    go =
      let
        handle-xy : Tri (uxm < lym) (uxm ≡ lym) (lym < uxm)
                  → ¬ (uym < lzm) → (x <ℝ y) ⊎ (y <ℝ z)
        handle-xy = λ { (tri< uxm<lym _ _) _ →
                          inj₁ (m , uxm<lym)
                      ; (tri≈ ¬uxm<lym _ _) ¬uym<lzm →
                          ⊥-elim (absurd ¬uym<lzm ¬uxm<lym)
                      ; (tri> ¬uxm<lym _ _) ¬uym<lzm →
                          ⊥-elim (absurd ¬uym<lzm ¬uxm<lym)
                      }

        handle-yz : Tri (uym < lzm) (uym ≡ lzm) (lzm < uym)
                  → (x <ℝ y) ⊎ (y <ℝ z)
        handle-yz = λ { (tri< uym<lzm _ _) →
                          inj₂ (m , uym<lzm)
                      ; (tri≈ ¬uym<lzm _ _) →
                          handle-xy (<-cmp uxm lym) ¬uym<lzm
                      ; (tri> ¬uym<lzm _ _) →
                          handle-xy (<-cmp uxm lym) ¬uym<lzm
                      }
      in
        handle-yz (<-cmp uym lzm)
