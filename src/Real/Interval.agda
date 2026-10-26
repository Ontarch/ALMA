------------------------------------------------------------------------
-- Coinductive reals as a nested interval chain
--
-- 余归纳实数作为嵌套区间链
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module Real.Interval where

open import Data.Nat using (ℕ; suc; _^_)
open import Data.Nat.Coprimality using (1-coprimeTo)
  renaming (sym to coprime-sym)
open import Data.Nat.Properties using (m^n≢0)
open import Data.Product using (_,_; _×_)
open import Data.Rational using
  (ℚ; 0ℚ; 1ℚ; _<_; _≤_; _+_; _*_; Positive; NonZero)
open import Data.Rational.Base using (_÷_; _-_) renaming (-_ to neg)
open import Data.Rational.Properties using
  (mkℚ+-pos; pos⇒nonZero; positive⁻¹; 1/pos⇒pos; ≤-reflexive; ≤-refl
  ; ≤-trans; <⇒≤; <-trans; +-mono-≤; +-mono-<-≤; +-identityʳ
  ; +-identityˡ; +-inverseʳ; +-assoc; +-comm; neg-distrib-+; *-inverseʳ
  ; *-assoc; *-comm; *-distribʳ-+; *-identityˡ; neg-antimono-≤)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; sym; cong; cong₂; subst; module ≡-Reasoning)
open ≡-Reasoning

open import Base.RationalRing using (neg-involutive)
open import Real using (embed; 2ℚ; 2*embed; halve; reciprocal-cong; 2ℚ≡1+1)

------------------------------------------------------------------------
-- The standard coinductive real: a nested chain of rational intervals
--
-- Each node carries the current interval (l, u) with l < u and a chosen
-- subinterval (the next node) whose length is at most half. The real is
-- the intersection over the nested chain.
-- This corrects the point-centre neighbourhood tree (Neighborhood.agda):
-- a real chooses nested intervals (deterministic corecursive step),
-- whereas the E-M tree with caller-supplied branches cannot be totalised
-- along a single fast path. The nesting is carried data, not a branch.
--
-- 标准余归纳实数：有理区间的嵌套链
--
-- 每个节点携带当前区间 (l, u)，l < u，并选择一个长度至多减半的子区间
-- （下一节点）。实数即嵌套链的交集。
-- 这修正了点中心邻域树（Neighborhood.agda）：实数选择嵌套区间
-- （确定性余归纳步骤），而调用者携带分支的 E-M 树无法沿单条快速路径
-- 良定义。嵌套是携带数据，不是分支。

pos-pow : ∀ k → Positive (embed (2 ^ suc k))
pos-pow k =
  mkℚ+-pos (2 ^ suc k) 1
    {{m^n≢0 2 (suc k)}}
    {c = coprime-sym (1-coprimeTo (2 ^ suc k))}

-- Summable dyadic tolerance.
--
-- 可求和的二进容差。
δ : ℕ → ℚ
δ k =
  Data.Rational.Base.1/_ (embed (2 ^ suc k))
    {{pos⇒nonZero (embed (2 ^ suc k)) {{pos-pow k}}}}

δ-pos : ∀ k → 0ℚ < δ k
δ-pos k =
  positive⁻¹ (δ k)
    {{1/pos⇒pos (embed (2 ^ suc k)) {{pos-pow k}}}}

-- Coinductive nested-interval real.
--
-- 余归纳嵌套区间实数。
mutual
  record RealI : Set where
    coinductive
    field
      l : ℚ
      u : ℚ
      lo : l < u
      next : RealI
      nest : Nest l u next

  Nest : (l u : ℚ) (next : RealI) → Set
  Nest l u next =
    l ≤ RealI.l next ×
    RealI.u next ≤ u ×
    RealI.u next - RealI.l next ≤ (u - l) ÷ embed 2

-- Doubling a successor-level tolerance recovers the current level.
--
-- 后继层容差加倍回到当前层。
δ-half : ∀ k → δ (suc k) + δ (suc k) ≡ δ k
δ-half k =
  let m = embed (2 ^ suc k)
      nm = pos⇒nonZero m {{pos-pow k}}
      e : 2ℚ * m ≡ embed (2 ^ suc (suc k))
      e = 2*embed (2 ^ suc k)
      n2m = subst NonZero (sym e)
              (pos⇒nonZero (embed (2 ^ suc (suc k))) {{pos-pow (suc k)}})
      nd = pos⇒nonZero (embed (2 ^ suc (suc k))) {{pos-pow (suc k)}}
      t = Data.Rational.Base.1/_ (2ℚ * m) {{n2m}}
      one/m = Data.Rational.Base.1/_ m {{nm}}
      t≡δ : t ≡ δ (suc k)
      t≡δ = reciprocal-cong (2ℚ * m) (embed (2 ^ suc (suc k)))
              {{n2m}} {{nd}} e
      h = halve m {{nm}} {{n2m}}
      tt : t + t ≡ δ (suc k) + δ (suc k)
      tt = cong₂ _+_ t≡δ t≡δ
      rhs : one/m ≡ δ k
      rhs = reciprocal-cong m (embed (2 ^ suc k)) {{nm}} {{nm}} refl
  in begin
       δ (suc k) + δ (suc k)
         ≡⟨ sym tt ⟩
       t + t
         ≡⟨ h ⟩
       one/m
         ≡⟨ rhs ⟩
       δ k
       ∎

-- Negated tolerance sits strictly below the positive one.
--
-- 取负后的容差严格低于正容差。
negδ<δ : ∀ k → neg (δ k) < δ k
negδ<δ k =
  let p : 0ℚ < δ k
      p = δ-pos k
      a : 0ℚ + neg (δ k) < δ k + neg (δ k)
      a = +-mono-<-≤ p (≤-refl { neg (δ k)})
      b : 0ℚ + neg (δ k) < 0ℚ
      b = subst (λ z → 0ℚ + neg (δ k) < z) (+-inverseʳ (δ k)) a
      n : neg (δ k) < 0ℚ
      n = subst (λ z → z < 0ℚ) (+-identityˡ (neg (δ k))) b
  in <-trans n p

-- Tolerances decrease along the successor direction.
--
-- 容差沿后继方向递减。
δs≤δ : ∀ k → δ (suc k) ≤ δ k
δs≤δ k =
  let d = δ (suc k)
      d0 : d + 0ℚ ≤ d + d
      d0 = +-mono-≤ (≤-refl {d}) (<⇒≤ (δ-pos (suc k)))
      sum : d ≤ d + d
      sum = subst (λ z → z ≤ d + d) (+-identityʳ d) d0
  in ≤-trans sum (≤-reflexive (δ-half k))

-- Shift cancellation in a difference.
--
-- 差值中的平移消去。
sub-cancel : (a b c : ℚ) → (a + c) - (b + c) ≡ a + neg b
sub-cancel a b c = begin
  (a + c) - (b + c)
    ≡⟨ cong (λ z → (a + c) + z) (neg-distrib-+ b c) ⟩
  (a + c) + (neg b + neg c)
    ≡⟨ reorder ⟩
  a + (neg b + (c + neg c))
    ≡⟨ cong (λ z → a + z)
            (cong (λ z → neg b + z) (+-inverseʳ c)) ⟩
  a + (neg b + 0ℚ)
    ≡⟨ cong (λ z → a + z) (+-identityʳ (neg b)) ⟩
  a + neg b
  ∎
  where
  reorder : (a + c) + (neg b + neg c) ≡ a + (neg b + (c + neg c))
  reorder = begin
    (a + c) + (neg b + neg c)
      ≡⟨ +-assoc a c (neg b + neg c) ⟩
    a + (c + (neg b + neg c))
      ≡⟨ cong (λ z → a + z) (sym (+-assoc c (neg b) (neg c))) ⟩
    a + ((c + neg b) + neg c)
      ≡⟨ cong (λ z → a + (z + neg c)) (+-comm c (neg b)) ⟩
    a + ((neg b + c) + neg c)
      ≡⟨ cong (λ z → a + z) (+-assoc (neg b) c (neg c)) ⟩
    a + (neg b + (c + neg c))
    ∎

-- Halving a doubled value returns it.
--
-- 加倍后再减半回到原值。
double-half : (x : ℚ) → (x + x) ÷ embed 2 ≡ x
double-half x = begin
  (x + x) ÷ embed 2
    ≡⟨ refl ⟩
  (x + x) * half
    ≡⟨ cong (λ z → z * half) (sym 2x) ⟩
  (embed 2 * x) * half
    ≡⟨ main ⟩
  x
  ∎
  where
  n2 = pos⇒nonZero (embed 2) {{pos-pow 0}}
  half = Data.Rational.Base.1/_ (embed 2) {{n2}}

  2x : embed 2 * x ≡ x + x
  2x = begin
    embed 2 * x
      ≡⟨ cong (λ z → z * x) 2ℚ≡1+1 ⟩
    (1ℚ + 1ℚ) * x
      ≡⟨ *-distribʳ-+ x 1ℚ 1ℚ ⟩
    1ℚ * x + 1ℚ * x
      ≡⟨ cong (λ z → z + z) (*-identityˡ x) ⟩
    x + x
    ∎

  inv : embed 2 * half ≡ 1ℚ
  inv = *-inverseʳ (embed 2) {{n2}}

  main : (embed 2 * x) * half ≡ x
  main = begin
    (embed 2 * x) * half
      ≡⟨ *-assoc (embed 2) x half ⟩
    embed 2 * (x * half)
      ≡⟨ cong (λ z → embed 2 * z) (*-comm x half) ⟩
    embed 2 * (half * x)
      ≡⟨ sym (*-assoc (embed 2) half x) ⟩
    (embed 2 * half) * x
      ≡⟨ cong (λ z → z * x) inv ⟩
    1ℚ * x
      ≡⟨ *-identityˡ x ⟩
    x
    ∎

-- Canonical dyadic nested intervals around a rational centre.
--
-- 有理中心周围的典范二进嵌套区间。
dyadic : (q : ℚ) (k : ℕ) → RealI
dyadic q k .RealI.l = neg (δ k) + q
dyadic q k .RealI.u = δ k + q
dyadic q k .RealI.lo = +-mono-<-≤ (negδ<δ k) (≤-refl {q})
dyadic q k .RealI.next = dyadic q (suc k)
dyadic q k .RealI.nest =
  let δₖ = δ k
      dₖ = δ (suc k)
      n1 : neg δₖ ≤ neg dₖ
      n1 = neg-antimono-≤ (δs≤δ k)
      nest1 : neg δₖ + q ≤ neg dₖ + q
      nest1 = +-mono-≤ n1 (≤-refl {q})
      nest2 : dₖ + q ≤ δₖ + q
      nest2 = +-mono-≤ (δs≤δ k) (≤-refl {q})
      lhs : (dₖ + q) - (neg dₖ + q) ≡ dₖ + dₖ
      lhs = begin
        (dₖ + q) - (neg dₖ + q)
          ≡⟨ sub-cancel dₖ (neg dₖ) q ⟩
        dₖ + neg (neg dₖ)
          ≡⟨ cong (λ z → dₖ + z) (neg-involutive dₖ) ⟩
        dₖ + dₖ
        ∎
      rhs : ((δₖ + q) - (neg δₖ + q)) ÷ embed 2 ≡ δₖ
      rhs = begin
        ((δₖ + q) - (neg δₖ + q)) ÷ embed 2
          ≡⟨ cong (λ z → z ÷ embed 2)
                  (sub-cancel δₖ (neg δₖ) q) ⟩
        (δₖ + neg (neg δₖ)) ÷ embed 2
          ≡⟨ cong (λ z → (δₖ + z) ÷ embed 2)
                  (neg-involutive δₖ) ⟩
        (δₖ + δₖ) ÷ embed 2
          ≡⟨ double-half δₖ ⟩
        δₖ
        ∎
      nest3 : (dₖ + q) - (neg dₖ + q) ≤
                ((δₖ + q) - (neg δₖ + q)) ÷ embed 2
      nest3 =
        ≤-trans (≤-reflexive lhs)
        (≤-trans (≤-reflexive (δ-half k))
                 (≤-reflexive (sym rhs)))
  in nest1 , nest2 , nest3

-- Embed a rational as a coinductive interval real.
--
-- 把有理数嵌入为余归纳区间实数。
embedℚ : ℚ → RealI
embedℚ q = dyadic q 0
