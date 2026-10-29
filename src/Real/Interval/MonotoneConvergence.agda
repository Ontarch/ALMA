------------------------------------------------------------------------
-- Bridge: order completeness and Cauchy completeness
--
-- 桥接：序完备与柯西完备
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module Real.Interval.MonotoneConvergence where

open import Data.Nat using (ℕ; zero; suc; _⊔_; _^_; _∸_; z≤n; s≤s)
  renaming (_+_ to _+ℕ_; _*_ to _*ℕ_; _≤_ to _≤N_; _≥_ to _≥N_; _<_ to _<N_)
open import Data.Nat.Properties using
  (m≤m⊔n; m≤n⊔m; m≤m+n; n≤1+n; ^-monoʳ-≤; m+[n∸m]≡n)
  renaming (≤-trans to ≤N-trans; ≤-refl to ≤N-refl; ≤-reflexive to ≤N-reflexive
  ; +-identityʳ to +ℕ-identityʳ; +-suc to +ℕ-suc)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Data.Sum.Base using (inj₁; inj₂)
open import Base.RationalRing using (neg-involutive)
open import Data.Rational using
  (ℚ; 0ℚ; 1ℚ; _+_; _-_; _*_; _<_; _≤_; ∣_∣; NonZero; nonNegative; positive)
  renaming (-_ to neg)
open import Data.Rational.Base using (_÷_; 1/_)
open import Data.Rational.Properties using
  (≤-refl; ≤-trans; ≤-reflexive; <⇒≤; ≤-<-trans; +-mono-≤; +-assoc; +-comm
  ; +-identityˡ; +-identityʳ; *-monoʳ-≤-nonNeg; *-monoˡ-≤-nonNeg; *-assoc
  ; *-identityʳ; *-identityˡ; *-inverseʳ; *-inverseˡ; *-distribʳ-+; *-distribˡ-+
  ; neg-distrib-+; neg-distribˡ-*; pos⇒nonNeg; pos⇒nonZero; *-monoˡ-<-pos
  ; +-inverseʳ; +-inverseˡ; nonNegative⁻¹; neg-antimono-≤; module ≤-Reasoning)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; sym; cong; cong₂; subst; trans; module ≡-Reasoning)
open ≡-Reasoning

open import Real using
  (CauchySeq; ε; embed; 0<ε; embed-suc-pos; reciprocal-cong; half; 2ℚ; 2ℚ≡1+1
  ; 2*embed; embed2-nonZero; 0<embed)
open import Real.CauchyToInterval using
  (cauchy→realI; centre-cauchy→realI; M; K; ε-K<δ-suc)
open import Real.Interval using (RealI; δ; δ-half; δs≤δ; embedℚ; sub-cancel)
open import Real.Interval.Order using (_<ℝ_)
open import Real.Interval.Equiv using (_≈ℝ_; ≈ℝ-refl; ≈ℝ-sym)
open import Real.IntervalEquiv using
  (centre; width; l; u; node; recipPow2; bounded-diff; n<2^n; centre-in-l
  ; centre-in-u; pos-2^t)
open import Real.Interval.Kit using
  (tail-bound; ≈ℝ-of-rec; recipPow2-mono; two-half; half≤1)
open import Real.Interval.OrderComplete.Base using
  (Subset; Located; Bracket; _≤ℝ_; hp; δ-dec; a+d≡b)
open import Real.Interval.OrderComplete.Bisect using
  (bw; bw-pos; bw-nn; initBracket; widenBracket; cbr-seq; cwb; step₃-a≤a
  ; step₃-b≤b; step₃-shrink)
open import Real.Interval.RegularRep using (reg; i; width-i; fold≥k+4)
open import Real.Interval.OrderLe using
  (≤ℝ-refl; ≤ℝ-trans; ≤ℝ-resp-≈; <⇒≤ℝ; <-≤ℝ-trans)
open import Real.Interval.Mul.Order using (≈-<-respʳ)
open import Real.Interval.Rational using (suc∸1; 0<2^t; ¬<⇒≥)
open import Real.Interval.WeakArith using (recip-antitone; recip-antitone-≤)
open import Real.Interval.Node using (u-dyadic; l-dyadic)

------------------------------------------------------------------------
-- The range of a sequence
--
-- 序列的范围

range : (ℕ → RealI) → Subset
range f x = Σ ℕ λ n → x ≈ℝ f n

------------------------------------------------------------------------
-- Constructive monotone convergence
--
-- 构造性单调收敛

module _ {f : ℕ → RealI}
         (mono : ∀ n → f n ≤ℝ f (suc n))
         {bnd : RealI}
         (bounded : ∀ n → f n ≤ℝ bnd)
         (loc : Located (range f))
  where

  -- The first term occupies the range.
  --
  -- 首项占据范围。
  range-f0 : range f (f 0)
  range-f0 = 0 , ≈ℝ-refl

  -- bnd is an upper bound of the range.
  --
  -- bnd 是范围的上界。
  range-upper : (x : RealI) → range f x → x ≤ℝ bnd
  range-upper x (n , x≈fn) =
    ≤ℝ-resp-≈ (≈ℝ-sym x≈fn) ≈ℝ-refl (bounded n)

  -- The bisection bracket sequence for the range.
  --
  -- 范围的二分括号序列。
  br0 : Bracket (range f)
  br0 = widenBracket (initBracket (f 0) range-f0 bnd range-upper)

  br-seq : ℕ → Bracket (range f)
  br-seq = cbr-seq loc br0

  -- Subtracting a smaller index from a larger one and adding it back
  -- recovers the larger index.
  --
  -- 用大下标减去小下标再加回来，得到大下标。
  add-diff : ∀ j n → j ≤N n → j +ℕ (n ∸ j) ≡ n
  add-diff j n p = m+[n∸m]≡n p

  -- Rational bracket endpoints.
  --
  -- 有理括号端点。
  a b : ℕ → ℚ
  a j = Bracket.a (br-seq j)
  b j = Bracket.b (br-seq j)

  -- The lower endpoints are non-decreasing, the upper endpoints
  -- non-increasing.
  --
  -- 下端点单调不减，上端点单调不增。
  a-mono : ∀ j → a j ≤ a (suc j)
  a-mono j = step₃-a≤a loc (br-seq j)

  b-mono : ∀ j → b (suc j) ≤ b j
  b-mono j = step₃-b≤b loc (br-seq j)

  -- The bracket width shrinks geometrically.
  --
  -- 括号宽度几何收缩。
  bw≤ : ∀ j → bw (br-seq j) ≤ bw br0 * hp j
  bw≤ j = cwb loc br0 j

  -- Iterated lower-endpoint monotonicity.
  --
  -- 下端点的迭代单调性。
  a-chain : ∀ j d → a j ≤ a (j +ℕ d)
  a-chain j zero    = ≤-reflexive (cong a (sym (+ℕ-identityʳ j)))
  a-chain j (suc d) =
    let ih = a-chain j d
        step = subst (λ k → a (j +ℕ d) ≤ a k)
                     (sym (+ℕ-suc j d)) (a-mono (j +ℕ d))
    in ≤-trans ih step

  a-in : ∀ j n → j ≤N n → a j ≤ a n
  a-in j n p =
    let d = n ∸ j
        e : j +ℕ d ≡ n
        e = add-diff j n p
    in subst (λ k → a j ≤ a k) e (a-chain j d)

  -- Iterated upper-endpoint monotonicity.
  --
  -- 上端点的迭代单调性。
  b-chain : ∀ j d → b (j +ℕ d) ≤ b j
  b-chain j zero    = ≤-reflexive (cong b (+ℕ-identityʳ j))
  b-chain j (suc d) =
    let step = subst (λ k → b k ≤ b (j +ℕ d))
                     (sym (+ℕ-suc j d)) (b-mono (j +ℕ d))
    in ≤-trans step (b-chain j d)

  b-in : ∀ j n → j ≤N n → b n ≤ b j
  b-in j n p =
    let d = n ∸ j
        e : j +ℕ d ≡ n
        e = add-diff j n p
    in subst (λ k → b k ≤ b j) e (b-chain j d)

  -- Each bracket satisfies a n ≤ b n.
  --
  -- 每层括号的下端点都不超过上端点。
  a≤b : ∀ n → a n ≤ b n
  a≤b n = <⇒≤ (Bracket.a<b (br-seq n))

  -- Two lower endpoints past level j differ by at most the level-j
  -- bracket width.
  --
  -- 第 j 层之后的两个下端点之差不超过第 j 层括号宽度。
  a-diff : ∀ j n m → j ≤N n → j ≤N m → ∣ a n - a m ∣ ≤ bw (br-seq j)
  a-diff j n m j≤n j≤m =
    bounded-diff (a-in j n j≤n) (≤-trans (a≤b n) (b-in j n j≤n))
                 (a-in j m j≤m) (≤-trans (a≤b m) (b-in j m j≤m))

------------------------------------------------------------------------
-- The lower endpoints form a rational Cauchy sequence
--
-- 下端点构成有理柯西序列

  -- The order-completeness halving factor equals the interval
  -- geometric factor.
  --
  -- 序完备的折半因子等于区间的几何因子。
  hp≡recip : ∀ n → hp n ≡ recipPow2 n
  hp≡recip n =
    let e : embed (2 ^ n) ≡ embed (suc (2 ^ n ∸ 1))
        e = cong embed (sym (suc∸1 (0<2^t n)))
        nzN : Data.Rational.NonZero (embed (2 ^ n))
        nzN = subst (λ m → Data.Rational.NonZero (embed m))
                    (suc∸1 (0<2^t n))
                    (pos⇒nonZero (embed (suc (2 ^ n ∸ 1)))
                       ⦃ embed-suc-pos ⦄)
    in reciprocal-cong (embed (2 ^ n)) (embed (suc (2 ^ n ∸ 1)))
                      ⦃ nzN ⦄
                      ⦃ pos⇒nonZero (embed (suc (2 ^ n ∸ 1)))
                          ⦃ embed-suc-pos ⦄ ⦄
                      e

  -- Monotonicity of the halving factor in the reverse direction:
  -- larger index gives smaller value, transported from the geometric
  -- factor via a single subst₂.
  --
  -- 折半因子的反向单调性：下标越大值越小，经一次 subst₂ 从几何因子转移。
  hp-mono : ∀ m n → m ≥N n → hp m ≤ hp n
  hp-mono m n ge =
    Relation.Binary.PropositionalEquality.subst₂ (λ x y → x ≤ y)
      (sym (hp≡recip m)) (sym (hp≡recip n))
      (recipPow2-mono ge)

  -- Modulus: a level at which the bracket width is below the given
  -- precision. The extra maximum with k makes the modulus dominate
  -- its argument, so the sampling index is at least n.
  --
  -- 模数：使括号宽度低于给定精度的层；与 k 取大保证模数不小于其参数，
  -- 从而采样下标不小于当前层。
  a-mod : ℕ → ℕ
  a-mod k = proj₁ (tail-bound (bw br0) (bw-nn br0) (ε k) (0<ε k)) ⊔ k

  a-mod< : ∀ k → bw br0 * hp (a-mod k) < ε k
  a-mod< k =
    let N0 = proj₁ (tail-bound (bw br0) (bw-nn br0) (ε k) (0<ε k))
        h = proj₂ (tail-bound (bw br0) (bw-nn br0) (ε k) (0<ε k))
        N = a-mod k
        N0≤N : N0 ≤N N
        N0≤N = m≤m⊔n N0 k
        raw : bw br0 * recipPow2 N0 < ε k
        raw = h N0 ≤N-refl
        mon : bw br0 * recipPow2 N ≤ bw br0 * recipPow2 N0
        mon = *-monoˡ-≤-nonNeg (bw br0)
                {{pos⇒nonNeg (bw br0) {{positive (bw-pos br0)}}}}
                (recipPow2-mono N0≤N)
        mid : bw br0 * recipPow2 N < ε k
        mid = ≤-<-trans mon raw
    in subst (λ z → bw br0 * z < ε k) (sym (hp≡recip N)) mid

  a-seq : CauchySeq
  a-seq = record
    { f = a
    ; μ = a-mod
    ; cauchy = a-cauchy
    }
    where
    a-cauchy : ∀ k n m → n ≥N a-mod k → m ≥N a-mod k
             → ∣ a n - a m ∣ < ε k
    a-cauchy k n m n≥N m≥N =
      let N = a-mod k
      in ≤-<-trans (a-diff N n m n≥N m≥N)
           (≤-<-trans (bw≤ N) (a-mod< k))

  -- The Cauchy limit of the lower endpoints.
  --
  -- 下端点的柯西极限。
  L : RealI
  L = cauchy→realI a-seq

  -- The supremum reconstructed as the bracket nested interval.
  --
  -- 上确界重构为括号嵌套区间。
  mutual
    supI : ℕ → RealI
    supI j .RealI.l    = a j
    supI j .RealI.u    = b j
    supI j .RealI.lo   = Bracket.a<b (br-seq j)
    supI j .RealI.next = supI (suc j)
    supI j .RealI.nest = a-mono j , b-mono j , nest-shrink j

    nest-shrink : ∀ j → b (suc j) - a (suc j) ≤ (b j - a j) ÷ embed 2
    nest-shrink j = step₃-shrink loc (br-seq j)

  s : RealI
  s = supI 0

  -- At level n the supremum's endpoints are exactly the bracket bounds.
  --
  -- 在第 n 层，上确界的端点恰为括号端点。
  l-s≡ : ∀ n → l s n ≡ a n
  l-s≡ n = cong RealI.l (node-sup n)
    where
    node-sup : ∀ n → node s n ≡ supI n
    node-sup zero    = refl
    node-sup (suc n) = cong RealI.next (node-sup n)

  u-s≡ : ∀ n → u s n ≡ b n
  u-s≡ n = cong RealI.u (node-sup n)
    where
    node-sup : ∀ n → node s n ≡ supI n
    node-sup zero    = refl
    node-sup (suc n) = cong RealI.next (node-sup n)

  -- The supremum equals the Cauchy limit of the lower endpoints.
  --
  -- 上确界等于下端点的柯西极限。

  -- The modulus dominates its argument.
  --
  -- 模数不小于其参数。
  a-mod≥k : ∀ k → k ≤N a-mod k
  a-mod≥k k =
    let N0 = proj₁ (tail-bound (bw br0) (bw-nn br0) (ε k) (0<ε k))
    in m≤n⊔m N0 k

  -- The sampling index dominates the current level.
  --
  -- 采样下标不小于当前层。
  K≥n : ∀ n → n ≤N K n
  K≥n n =
    let n<2n : n <N 2 ^ n
        n<2n = n<2^n n
        n≤2n : n ≤N 2 ^ n
        n≤2n = ≤N-trans (n≤1+n n) n<2n
        n≤2s : n ≤N suc (suc n)
        n≤2s = ≤N-trans (n≤1+n n) (n≤1+n (suc n))
        2n≤K : 2 ^ n ≤N K n
        2n≤K = ^-monoʳ-≤ 2 n≤2s
    in ≤N-trans n≤2n 2n≤K

  -- The prefix sampling index dominates the current level.
  --
  -- 前缀采样下标不小于当前层。
  M≥n : ∀ n → n ≤N M a-seq n
  M≥n zero =
    let a-mod≥K : K zero ≤N a-mod (K zero)
        a-mod≥K = a-mod≥k (K zero)
    in ≤N-trans z≤n a-mod≥K
  M≥n (suc n) =
    let a-mod≥K : K (suc n) ≤N a-mod (K (suc n))
        a-mod≥K = a-mod≥k (K (suc n))
        K≥ : suc n ≤N K (suc n)
        K≥ = K≥n (suc n)
        term : a-mod (K (suc n)) ≤N M a-seq (suc n)
        term = m≤n⊔m (M a-seq n) (a-mod (K (suc n)))
    in ≤N-trans (≤N-trans K≥ a-mod≥K) term

  -- The prefix sampling index dominates the modulus at the sampling
  -- precision.
  --
  -- 前缀采样下标不小于采样精度处的模数。
  M≥a-mod-K : ∀ t → a-mod (K t) ≤N M a-seq t
  M≥a-mod-K zero    = ≤N-refl
  M≥a-mod-K (suc t) = m≤n⊔m (M a-seq t) (a-mod (K (suc t)))

  -- Every power of two is at least its exponent plus one.
  --
  -- 二的幂不小于其指数加一。
  2^t≥t+1 : ∀ t → suc t ≤N 2 ^ t
  2^t≥t+1 zero    = s≤s z≤n
  2^t≥t+1 (suc t) =
    let ih = 2^t≥t+1 t
        1≤2^t : 1 ≤N 2 ^ t
        1≤2^t = ≤N-trans (s≤s z≤n) ih
        step1 : suc (suc t) ≤N suc (2 ^ t)
        step1 = s≤s ih
        step2 : suc (2 ^ t) ≤N 2 ^ t +ℕ 2 ^ t
        step2 =
          let e1 : suc (2 ^ t) ≡ 2 ^ t +ℕ 1
              e1 = Data.Nat.Properties.+-comm 1 (2 ^ t)
              e2 : 2 ^ t +ℕ 1 ≤N 2 ^ t +ℕ 2 ^ t
              e2 = Data.Nat.Properties.+-monoʳ-≤ (2 ^ t) 1≤2^t
          in ≤N-trans (≤N-reflexive e1) e2
        exp : 2 ^ suc t ≡ 2 ^ t +ℕ 2 ^ t
        exp =
          let n = 2 ^ t
          in begin
            2 ^ suc t
              ≡⟨ refl ⟩
            2 *ℕ n
              ≡⟨ refl ⟩
            n +ℕ (n +ℕ 0)
              ≡⟨ cong (n +ℕ_) (Data.Nat.Properties.+-identityʳ n) ⟩
            n +ℕ n
            ∎
    in subst (λ n → suc (suc t) ≤N n) (sym exp)
         (≤N-trans step1 step2)

  -- The sampling precision is a power of two.
  --
  -- 采样精度是 2 的幂。
  K≡ : ∀ t → K t ≡ 2 ^ suc (suc t)
  K≡ t = refl

  -- Sum of the first and third successors does not exceed the current
  -- level.
  --
  -- 第一与第三后继的二进容差之和不超过当前层的二进容差。
  δ-sum≤δ : ∀ t → δ (suc t) + δ (suc (suc (suc t))) ≤ δ t
  δ-sum≤δ t =
    let d3≤d1 : δ (suc (suc (suc t))) ≤ δ (suc t)
        d3≤d1 = ≤-trans (δs≤δ (suc (suc t))) (δs≤δ (suc t))
        d1+d1≡dt : δ (suc t) + δ (suc t) ≡ δ t
        d1+d1≡dt = δ-half t
    in ≤-trans (+-mono-≤ (≤-refl {x = δ (suc t)}) d3≤d1)
               (≤-reflexive d1+d1≡dt)

  -- The current tolerance is at most half of ε.
  --
  -- 当前层的二进容差不超过 ε 的一半。
  δ≤ε-half : ∀ t → δ t ≤ ε t * half
  δ≤ε-half t =
    let a = 2 *ℕ suc t
        b = 2 ^ suc t
        a≤b : a ≤N b
        a≤b =
          let t+1≤2^t : suc t ≤N 2 ^ t
              t+1≤2^t = 2^t≥t+1 t
          in Data.Nat.Properties.*-monoʳ-≤ 2 t+1≤2^t
        ap = t +ℕ suc t
        a≡ : a ≡ suc ap
        a≡ =
          begin
            a
              ≡⟨ refl ⟩
            2 *ℕ suc t
              ≡⟨ refl ⟩
            suc t +ℕ (suc t +ℕ 0)
              ≡⟨ cong (suc t +ℕ_) (Data.Nat.Properties.+-identityʳ (suc t)) ⟩
            suc t +ℕ suc t
              ≡⟨ refl ⟩
            suc (t +ℕ suc t)
            ∎
        0<a : 0ℚ < embed a
        0<a = subst (λ n → 0ℚ < embed n) (sym a≡) (0<embed ap)
        nzA : NonZero (embed a)
        nzA = pos⇒nonZero (embed a) {{positive 0<a}}
        nzB : NonZero (embed b)
        nzB = pos⇒nonZero (embed b) {{pos-2^t (suc t)}}
        inv = recip-antitone-≤ a b 0<a a≤b {{nzA}} {{nzB}}
        lhs = ≤-refl
        -- ε t * half = 1/embed (suc t) * 1/embed 2 = 1/embed a.
        rhs : 1/ (embed a) ≤ ε t * half
        rhs =
          let p = embed (suc t)
              nzST : NonZero p
              nzST = pos⇒nonZero p {{positive (0<embed t)}}
              z = 2ℚ * p
              b = embed a
              e2m : z ≡ b
              e2m = 2*embed (suc t)
              nzZ : NonZero z
              nzZ = subst NonZero (sym e2m) (pos⇒nonZero b)
              z≡a : z ≡ embed a
              z≡a = e2m
              nz2 : NonZero 2ℚ
              nz2 = embed2-nonZero
              prod : (1/ p) * (1/ 2ℚ) ≡ 1/_ z ⦃ nzZ ⦄
              prod =
                let step : ((1/ p) * (1/ 2ℚ)) * z ≡ 1ℚ
                    step =
                      begin
                        ((1/ p) * (1/ 2ℚ)) * z
                          ≡⟨ *-assoc (1/ p) (1/ 2ℚ) z ⟩
                        (1/ p) * ((1/ 2ℚ) * z)
                          ≡⟨ refl ⟩
                        (1/ p) * ((1/ 2ℚ) * (2ℚ * p))
                          ≡⟨ cong ((1/ p) *_) (sym (*-assoc (1/ 2ℚ) 2ℚ p)) ⟩
                        (1/ p) * (((1/ 2ℚ) * 2ℚ) * p)
                          ≡⟨ cong ((1/ p) *_) (cong (_* p) (*-inverseʳ 2ℚ ⦃ nz2 ⦄)) ⟩
                        (1/ p) * (1ℚ * p)
                          ≡⟨ cong ((1/ p) *_) (*-identityˡ p) ⟩
                        (1/ p) * p
                          ≡⟨ *-inverseˡ p ⦃ nzST ⦄ ⟩
                        1ℚ
                        ∎
                    main : (1/ p) * (1/ 2ℚ) ≡ 1/_ z ⦃ nzZ ⦄
                    main =
                      begin
                        (1/ p) * (1/ 2ℚ)
                          ≡⟨ sym (*-identityʳ ((1/ p) * (1/ 2ℚ))) ⟩
                        ((1/ p) * (1/ 2ℚ)) * 1ℚ
                          ≡⟨ cong (((1/ p) * (1/ 2ℚ)) *_) (sym (*-inverseʳ z ⦃ nzZ ⦄)) ⟩
                        ((1/ p) * (1/ 2ℚ)) * (z * (1/_ z ⦃ nzZ ⦄))
                          ≡⟨ sym (*-assoc ((1/ p) * (1/ 2ℚ)) z (1/_ z ⦃ nzZ ⦄)) ⟩
                        (((1/ p) * (1/ 2ℚ)) * z) * (1/_ z ⦃ nzZ ⦄)
                          ≡⟨ cong (_* (1/_ z ⦃ nzZ ⦄)) step ⟩
                        1ℚ * (1/_ z ⦃ nzZ ⦄)
                          ≡⟨ *-identityˡ (1/_ z ⦃ nzZ ⦄) ⟩
                        1/_ z ⦃ nzZ ⦄
                        ∎
                in main
              e1 : ε t ≡ 1/ p
              e1 = refl
              e2 : half ≡ 1/ 2ℚ
              e2 = refl
              full : ε t * half ≡ 1/ (embed a)
              full =
                begin
                  ε t * half
                    ≡⟨ cong₂ _*_ e1 e2 ⟩
                  (1/ p) * (1/ 2ℚ)
                    ≡⟨ prod ⟩
                  1/_ z ⦃ nzZ ⦄
                    ≡⟨ reciprocal-cong z (embed a) ⦃ nzZ ⦄ ⦃ nzA ⦄ z≡a ⟩
                  1/ (embed a)
                  ∎
          in ≤-reflexive (sym full)
    in ≤-trans (≤-trans lhs inv) rhs

  -- A point in a closed interval around a centre with a given
  -- half-width is at distance at most that half-width from the centre.
  --
  -- 落在以给定中心与半宽围成的闭区间内的点，到中心的距离不超过半宽。
  abs-two-sided : ∀ x c d → c - d ≤ x → x ≤ c + d →
    ∣ x - c ∣ ≤ d
  abs-two-sided x c d lo hi =
    let p : x - c ≤ d
        p =
          let e1 : x + neg c ≤ (c + d) + neg c
              e1 = +-mono-≤ hi (≤-refl {neg c})
              e2 : (c + d) + neg c ≡ d
              e2 =
                begin
                  (c + d) + neg c
                ≡⟨ +-assoc c d (neg c) ⟩
                  c + (d + neg c)
                ≡⟨ cong (c +_) (+-comm d (neg c)) ⟩
                  c + (neg c + d)
                ≡⟨ sym (+-assoc c (neg c) d) ⟩
                  (c + neg c) + d
                ≡⟨ cong (_+ d) (+-inverseʳ c) ⟩
                  0ℚ + d
                ≡⟨ +-identityˡ d ⟩
                  d
                ∎
          in subst (λ z → x + neg c ≤ z) e2 e1
        q : c - x ≤ d
        q =
          let e0 : (c + neg d) + d ≤ x + d
              e0 = +-mono-≤ lo (≤-refl {d})
              e0eq : (c + neg d) + d ≡ c
              e0eq =
                begin
                  (c + neg d) + d
                ≡⟨ +-assoc c (neg d) d ⟩
                  c + (neg d + d)
                ≡⟨ cong (c +_) (+-inverseˡ d) ⟩
                  c + 0ℚ
                ≡⟨ +-identityʳ c ⟩
                  c
                ∎
              e1 : c ≤ x + d
              e1 = subst (λ z → z ≤ x + d) e0eq e0
              e2 : c + neg x ≤ (x + d) + neg x
              e2 = +-mono-≤ e1 (≤-refl {neg x})
              e3 : (x + d) + neg x ≡ d
              e3 =
                begin
                  (x + d) + neg x
                ≡⟨ +-assoc x d (neg x) ⟩
                  x + (d + neg x)
                ≡⟨ cong (x +_) (+-comm d (neg x)) ⟩
                  x + (neg x + d)
                ≡⟨ sym (+-assoc x (neg x) d) ⟩
                  (x + neg x) + d
                ≡⟨ cong (_+ d) (+-inverseʳ x) ⟩
                  0ℚ + d
                ≡⟨ +-identityˡ d ⟩
                  d
                ∎
          in subst (λ z → c + neg x ≤ z) e3 e2
        z = x - c
        nid : neg z ≡ c + neg x
        nid =
          begin
            neg (x + neg c)
          ≡⟨ neg-distrib-+ x (neg c) ⟩
            neg x + neg (neg c)
          ≡⟨ cong (neg x +_) (neg-involutive c) ⟩
            neg x + c
          ≡⟨ +-comm (neg x) c ⟩
            c + neg x
          ∎
        q' : neg z ≤ d
        q' = subst (λ w → w ≤ d) (sym nid) q
        cases : Data.Sum.Base._⊎_ (∣ z ∣ ≡ z) (∣ z ∣ ≡ neg z)
        cases = Data.Rational.Properties.∣p∣≡p∨∣p∣≡-p z
    in abs-case cases p q'
    where
    abs-case : ∀ {z d} → Data.Sum.Base._⊎_ (∣ z ∣ ≡ z) (∣ z ∣ ≡ neg z)
             → z ≤ d → neg z ≤ d → ∣ z ∣ ≤ d
    abs-case (inj₁ e) p _ = subst (λ w → w ≤ _) (sym e) p
    abs-case (inj₂ e) _ q = subst (λ w → w ≤ _) (sym e) q

  -- The Cauchy limit's centre equals the lower endpoint at the prefix
  -- sampling index.
  --
  -- 柯西极限的中心等于前缀采样下标处的下端点。
  cL≡ : ∀ n → centre L n ≡ a (M a-seq n)
  cL≡ n = centre-cauchy→realI a-seq n

  cL-lo : ∀ n → a n ≤ centre L n
  cL-lo n =
    let p : a n ≤ a (M a-seq n)
        p = a-in n (M a-seq n) (M≥n n)
        q : a (M a-seq n) ≤ centre L n
        q = ≤-reflexive (sym (cL≡ n))
    in ≤-trans p q

  cL-hi : ∀ n → centre L n ≤ b n
  cL-hi n =
    let p1 : a (M a-seq n) ≤ b (M a-seq n)
        p1 = a≤b (M a-seq n)
        p2 : b (M a-seq n) ≤ b n
        p2 = b-in n (M a-seq n) (M≥n n)
        p : a (M a-seq n) ≤ b n
        p = ≤-trans p1 p2
        q : centre L n ≤ a (M a-seq n)
        q = ≤-reflexive (cL≡ n)
    in ≤-trans q p

  cs-lo : ∀ n → a n ≤ centre s n
  cs-lo n =
    let p : l s n ≤ centre s n
        p = centre-in-l s {n} {n} ≤N-refl
    in ≤-trans (≤-reflexive (sym (l-s≡ n))) p

  cs-hi : ∀ n → centre s n ≤ b n
  cs-hi n =
    let p : centre s n ≤ u s n
        p = centre-in-u s {n} {n} ≤N-refl
    in ≤-trans p (≤-reflexive (u-s≡ n))

  L-s-diff : ∀ n →
    ∣ centre L n - centre s n ∣ ≤ b n - a n
  L-s-diff n = bounded-diff (cL-lo n) (cL-hi n) (cs-lo n) (cs-hi n)

  bw≤n : ∀ n → b n - a n ≤ bw br0 * hp n
  bw≤n n = bw≤ n

  bw≤r : ∀ n → bw br0 * hp n ≤ bw br0 * recipPow2 n
  bw≤r n =
    let e : hp n ≡ recipPow2 n
        e = hp≡recip n
    in ≤-reflexive (cong (bw br0 *_) e)

  L-s-bound : ∀ n →
    ∣ centre L n - centre s n ∣ ≤ bw br0 * recipPow2 n
  L-s-bound n =
    ≤-trans (≤-trans (L-s-diff n) (bw≤n n)) (bw≤r n)

  L≈s : L ≈ℝ s
  L≈s = ≈ℝ-of-rec L s (bw br0) (bw-nn br0) L-s-bound

------------------------------------------------------------------------
-- Monotone convergence
--
-- 单调收敛

  -- Iterated monotonicity: f n ≤ f m for n ≤ m.
  --
  -- 迭代单调性：下标越大，序列值越大。
  f-chain : ∀ n d → f n ≤ℝ f (n +ℕ d)
  f-chain n zero    =
    subst (λ k → f n ≤ℝ f k) (sym (+ℕ-identityʳ n)) ≤ℝ-refl
  f-chain n (suc d) =
    let step = subst (λ k → f (n +ℕ d) ≤ℝ f k)
                     (sym (+ℕ-suc n d)) (mono (n +ℕ d))
    in ≤ℝ-trans (f-chain n d) step

  mono-iter : ∀ n m → n ≤N m → f n ≤ℝ f m
  mono-iter n m p =
    let d = m ∸ n
        e : n +ℕ d ≡ m
        e = add-diff n m p
    in subst (λ k → f n ≤ℝ f k) e (f-chain n d)

  -- The occupied member at bracket level j, with its index.
  --
  -- 第 j 层括号的占据成员及其下标。
  occ-pack : ∀ j → Σ ℕ λ n → embedℚ (a j) <ℝ f n
  occ-pack j =
    let x , (n , x≈fn) , a<x = Bracket.occ (br-seq j)
    in n , ≈-<-respʳ x≈fn a<x

  -- Non-strict containment: f n ≤ℝ embedℚ (b j).
  --
  -- 非严格包含：序列项不超过第 j 层括号的上端点嵌入。
  fn-upper : ∀ j n → f n ≤ℝ embedℚ (b j)
  fn-upper j n =
    let up : f n <ℝ embedℚ (b j)
        up = Bracket.upper (br-seq j) (f n) (n , ≈ℝ-refl)
    in <⇒≤ℝ up

  -- Non-strict containment: embedℚ (a j) ≤ℝ f n once n passes the
  -- occupied index at level j.
  --
  -- 非严格包含：当 n 越过第 j 层占据下标时，序列项不小于第 j 层括号
  -- 的下端点嵌入。
  fn-lower : ∀ j n → n ≥N proj₁ (occ-pack j) → embedℚ (a j) ≤ℝ f n
  fn-lower j n n≥nj =
    let nj = proj₁ (occ-pack j)
        a<fnj : embedℚ (a j) <ℝ f nj
        a<fnj = proj₂ (occ-pack j)
        fnj≤fn : f nj ≤ℝ f n
        fnj≤fn = mono-iter nj n n≥nj
        a<fn : embedℚ (a j) <ℝ f n
        a<fn = <-≤ℝ-trans a<fnj fnj≤fn
    in <⇒≤ℝ a<fn

  -- Non-strict upper bound: when the sequence term is at most the
  -- upper-endpoint embedding, its lower endpoint is controlled.
  --
  -- 非严格上界：序列项不超过上端点嵌入时，其下端点受控。
  l≤b : (x : RealI) (b : ℚ) (m : ℕ) → x ≤ℝ embedℚ b → l x m ≤ b + δ m
  l≤b x b m x≤b =
    ¬<⇒≥ (λ h →
      let e : u (embedℚ b) m ≡ b + δ m
          e = trans (u-dyadic b m) (+-comm (δ m) b)
          w : u (embedℚ b) m < l x m
          w = subst (λ q → q < l x m) (sym e) h
      in x≤b (m , w))

  -- Non-strict lower bound: when the lower-endpoint embedding is at
  -- most the sequence term, its upper endpoint is controlled.
  --
  -- 非严格下界：下端点嵌入不超过序列项时，序列项上端点受控。
  a≤u : (x : RealI) (a : ℚ) (m : ℕ) → embedℚ a ≤ℝ x → a - δ m ≤ u x m
  a≤u x a m a≤x =
    ¬<⇒≥ (λ h →
      let e : l (embedℚ a) m ≡ a - δ m
          e = trans (l-dyadic a m) (+-comm (neg (δ m)) a)
          w : u x m < l (embedℚ a) m
          w = subst (λ q → u x m < q) (sym e) h
      in a≤x (m , w))

  -- Width decomposition: the upper endpoint is the lower endpoint plus
  -- the width.
  --
  -- 宽度分解：上端点等于下端点加宽度。
  u-decomp : (x : RealI) (m : ℕ) → u x m ≡ l x m + width x m
  u-decomp x m =
    begin
      u x m
        ≡⟨ sym (+-identityʳ (u x m)) ⟩
      u x m + 0ℚ
        ≡⟨ cong (u x m +_) (sym (+-inverseʳ (l x m))) ⟩
      u x m + (l x m + neg (l x m))
        ≡⟨ sym (+-assoc (u x m) (l x m) (neg (l x m))) ⟩
      (u x m + l x m) + neg (l x m)
        ≡⟨ cong (_+ neg (l x m)) (+-comm (u x m) (l x m)) ⟩
      (l x m + u x m) + neg (l x m)
        ≡⟨ +-assoc (l x m) (u x m) (neg (l x m)) ⟩
      l x m + (u x m + neg (l x m))
        ≡⟨⟩
      l x m + width x m
        ∎

  -- Width decomposition: the lower endpoint is the upper endpoint
  -- minus the width.
  --
  -- 宽度分解：下端点等于上端点减宽度。
  l-decomp : (x : RealI) (m : ℕ) → l x m ≡ u x m - width x m
  l-decomp x m =
    begin
      l x m
        ≡⟨ sym (+-identityʳ (l x m)) ⟩
      l x m + 0ℚ
        ≡⟨ cong (l x m +_) (sym (+-inverseʳ (width x m))) ⟩
      l x m + (width x m + neg (width x m))
        ≡⟨ sym (+-assoc (l x m) (width x m) (neg (width x m))) ⟩
      (l x m + width x m) + neg (width x m)
        ≡⟨ cong (_+ neg (width x m)) (sym (u-decomp x m)) ⟩
      u x m + neg (width x m)
        ≡⟨⟩
      u x m - width x m
        ∎

  -- Upper bound on the regular representative at the reg level.
  --
  -- 正则下标处正则代表的上界。
  reg-hi : ∀ j n m → f n ≤ℝ embedℚ (b j) →
           centre (f n) m ≤ b j + δ m + width (f n) m
  reg-hi j n m fn≤bj =
    let l≤ : l (f n) m ≤ b j + δ m
        l≤ = l≤b (f n) (b j) m fn≤bj
        c≤u : centre (f n) m ≤ u (f n) m
        c≤u = centre-in-u (f n) {m} {m} ≤N-refl
        c≤l+w : centre (f n) m ≤ l (f n) m + width (f n) m
        c≤l+w = subst (λ q → centre (f n) m ≤ q) (u-decomp (f n) m) c≤u
    in ≤-trans c≤l+w (+-mono-≤ l≤ ≤-refl)

  -- Lower bound on the regular representative at the reg level.
  --
  -- 正则下标处正则代表的下界。
  reg-lo : ∀ j n m → embedℚ (a j) ≤ℝ f n →
           a j - δ m - width (f n) m ≤ centre (f n) m
  reg-lo j n m a≤fn =
    let u≥ : a j - δ m ≤ u (f n) m
        u≥ = a≤u (f n) (a j) m a≤fn
        l≤c : l (f n) m ≤ centre (f n) m
        l≤c = centre-in-l (f n) {m} {m} ≤N-refl
        u-w≤c : u (f n) m - width (f n) m ≤ centre (f n) m
        u-w≤c = subst (λ q → q ≤ centre (f n) m) (l-decomp (f n) m) l≤c
        sub : (a j - δ m) - width (f n) m ≤ u (f n) m - width (f n) m
        sub = +-mono-≤ u≥ ≤-refl
    in ≤-trans sub u-w≤c

  -- Bracket endpoint relation: the upper endpoint is the lower
  -- endpoint plus the bracket width.
  --
  -- 括号端点关系：上端点等于下端点加括号宽度。
  b≡a+bw : ∀ j → b j ≡ a j + bw (br-seq j)
  b≡a+bw j =
    begin
      b j
        ≡⟨ sym (+-identityʳ (b j)) ⟩
      b j + 0ℚ
        ≡⟨ cong (b j +_) (sym (+-inverseʳ (a j))) ⟩
      b j + (a j + neg (a j))
        ≡⟨ sym (+-assoc (b j) (a j) (neg (a j))) ⟩
      (b j + a j) + neg (a j)
        ≡⟨ cong (_+ neg (a j)) (+-comm (b j) (a j)) ⟩
      (a j + b j) + neg (a j)
        ≡⟨ +-assoc (a j) (b j) (neg (a j)) ⟩
      a j + (b j + neg (a j))
        ≡⟨⟩
      a j + bw (br-seq j)
        ∎

  -- Upper bound on the supremum centre relative to bracket j.
  --
  -- 上确界中心相对第 j 层括号的上界。
  cs-hi-b : ∀ j t → j ≥N t → centre s t ≤ b j + bw (br-seq t)
  cs-hi-b j t j≥t =
    let c≤bt : centre s t ≤ b t
        c≤bt = cs-hi t
        at≤aj : a t ≤ a j
        at≤aj = a-in t j j≥t
        bt≤ : b t ≤ a j + bw (br-seq t)
        bt≤ =
          let w = bw (br-seq t)
              at+bw≤aj+bw : a t + w ≤ a j + w
              at+bw≤aj+bw = +-mono-≤ at≤aj (≤-refl {x = w})
              eq : a t + w ≡ b t
              eq = sym (b≡a+bw t)
          in subst (λ q → q ≤ a j + w) eq at+bw≤aj+bw
        aj≤bj : a j ≤ b j
        aj≤bj = a≤b j
        bt≤2 : b t ≤ b j + bw (br-seq t)
        bt≤2 = ≤-trans bt≤ (+-mono-≤ aj≤bj ≤-refl)
    in ≤-trans c≤bt bt≤2

  -- Lower bound on the supremum centre relative to bracket j.
  --
  -- 上确界中心相对第 j 层括号的下界。
  cs-lo-b : ∀ j t → j ≥N t → a j - bw (br-seq t) ≤ centre s t
  cs-lo-b j t j≥t =
    let at≤c : a t ≤ centre s t
        at≤c = cs-lo t
        w = bw (br-seq t)
        aj≤bt : a j ≤ b t
        aj≤bt =
          let bj≤bt : b j ≤ b t
              bj≤bt = b-in t j j≥t
          in ≤-trans (a≤b j) bj≤bt
        bt≡ : b t ≡ a t + w
        bt≡ = b≡a+bw t
        aj≤at+w : a j ≤ a t + w
        aj≤at+w = subst (λ q → a j ≤ q) bt≡ aj≤bt
        cancel : (a t + w) - w ≡ a t
        cancel =
          begin
            (a t + w) - w
              ≡⟨ +-assoc (a t) w (neg w) ⟩
            a t + (w + neg w)
              ≡⟨ cong (a t +_) (+-inverseʳ w) ⟩
            a t + 0ℚ
              ≡⟨ +-identityʳ (a t) ⟩
            a t
              ∎
        aj-w≤ : a j - w ≤ (a t + w) - w
        aj-w≤ = +-mono-≤ aj≤at+w (≤-refl {x = neg w})
        aj-w≤at : a j - w ≤ a t
        aj-w≤at = subst (λ q → a j - w ≤ q) cancel aj-w≤
    in ≤-trans aj-w≤at at≤c

  -- The centre equals the lower endpoint plus half the width.
  --
  -- 中心等于下端点加半宽。
  centre-half : (x : RealI) (m : ℕ) →
    centre x m ≡ l x m + (width x m) * half
  centre-half x m =
    let open ≡-Reasoning
        l′ = l x m; u′ = u x m
        2h : embed 2 * half ≡ 1ℚ
        2h = *-inverseʳ (embed 2) {{embed2-nonZero}}
        l*2≡ : l′ * embed 2 ≡ l′ + l′
        l*2≡ =
          begin
            l′ * embed 2
              ≡⟨ cong (l′ *_) (sym 2ℚ≡1+1) ⟩
            l′ * (1ℚ + 1ℚ)
              ≡⟨ *-distribˡ-+ l′ 1ℚ 1ℚ ⟩
            l′ * 1ℚ + l′ * 1ℚ
              ≡⟨ cong (_+ l′ * 1ℚ) (*-identityʳ l′) ⟩
            l′ + l′ * 1ℚ
              ≡⟨ cong (l′ +_) (*-identityʳ l′) ⟩
            l′ + l′
              ∎
        l+u-l≡ : l′ + (u′ - l′) ≡ u′
        l+u-l≡ =
          begin
            l′ + (u′ - l′)
              ≡⟨ sym (+-assoc l′ u′ (neg l′)) ⟩
            (l′ + u′) + neg l′
              ≡⟨ cong (_+ neg l′) (+-comm l′ u′) ⟩
            (u′ + l′) + neg l′
              ≡⟨ +-assoc u′ l′ (neg l′) ⟩
            u′ + (l′ + neg l′)
              ≡⟨ cong (u′ +_) (+-inverseʳ l′) ⟩
            u′ + 0ℚ
              ≡⟨ +-identityʳ u′ ⟩
            u′
              ∎
        l2+ : l′ * embed 2 + (u′ - l′) ≡ l′ + u′
        l2+ =
          begin
            l′ * embed 2 + (u′ - l′)
              ≡⟨ cong (_+ (u′ - l′)) l*2≡ ⟩
            (l′ + l′) + (u′ - l′)
              ≡⟨ +-assoc l′ l′ (u′ - l′) ⟩
            l′ + (l′ + (u′ - l′))
              ≡⟨ cong (l′ +_) l+u-l≡ ⟩
            l′ + u′
              ∎
        l+u≡ : l′ + u′ ≡ l′ * embed 2 + (u′ - l′)
        l+u≡ = sym l2+
        l2h≡ : l′ * (embed 2 * half) ≡ l′
        l2h≡ =
          begin
            l′ * (embed 2 * half)
              ≡⟨ cong (l′ *_) 2h ⟩
            l′ * 1ℚ
              ≡⟨ *-identityʳ l′ ⟩
            l′
              ∎
    in
    begin
      centre x m
        ≡⟨⟩
      (l′ + u′) * half
        ≡⟨ cong (_* half) l+u≡ ⟩
      (l′ * embed 2 + (u′ - l′)) * half
        ≡⟨ *-distribʳ-+ half (l′ * embed 2) (u′ - l′) ⟩
      (l′ * embed 2) * half + (u′ - l′) * half
        ≡⟨ cong (_+ (u′ - l′) * half) (*-assoc l′ (embed 2) half) ⟩
      l′ * (embed 2 * half) + (u′ - l′) * half
        ≡⟨ cong (_+ (u′ - l′) * half) l2h≡ ⟩
      l′ + (u′ - l′) * half
        ∎

  -- The centre equals the upper endpoint minus half the width.
  --
  -- 中心等于上端点减半宽。
  centre-half-lower : (x : RealI) (m : ℕ) →
    centre x m ≡ u x m - (width x m) * half
  centre-half-lower x m =
    let open ≡-Reasoning
        l′ = l x m; u′ = u x m
        w = u′ - l′
        h = w * half
        h+h≡w : h + h ≡ w
        h+h≡w =
          begin
            h + h
              ≡⟨ sym (*-distribʳ-+ half w w) ⟩
            (w + w) * half
              ≡⟨ cong (λ z → z * half) (
                  begin
                    w + w
                      ≡⟨ sym (
                          begin
                            w * embed 2
                              ≡⟨ cong (w *_) (sym 2ℚ≡1+1) ⟩
                            w * (1ℚ + 1ℚ)
                              ≡⟨ *-distribˡ-+ w 1ℚ 1ℚ ⟩
                            w * 1ℚ + w * 1ℚ
                              ≡⟨ cong (_+ w * 1ℚ) (*-identityʳ w) ⟩
                            w + w * 1ℚ
                              ≡⟨ cong (w +_) (*-identityʳ w) ⟩
                            w + w
                              ∎
                          ) ⟩
                    w * embed 2
                      ∎
                  ) ⟩
            w * embed 2 * half
              ≡⟨ *-assoc w (embed 2) half ⟩
            w * (embed 2 * half)
              ≡⟨ cong (w *_) (*-inverseʳ (embed 2) {{embed2-nonZero}}) ⟩
            w * 1ℚ
              ≡⟨ *-identityʳ w ⟩
            w
              ∎
        negw+h≡negh : neg w + h ≡ neg h
        negw+h≡negh =
          begin
            neg w + h
              ≡⟨ cong (λ z → z + h) (sym (
                  begin
                    neg h + neg h
                      ≡⟨ sym (neg-distrib-+ h h) ⟩
                    neg (h + h)
                      ≡⟨ cong neg h+h≡w ⟩
                    neg w
                      ∎
                  )) ⟩
            (neg h + neg h) + h
              ≡⟨ +-assoc (neg h) (neg h) h ⟩
            neg h + (neg h + h)
              ≡⟨ cong (neg h +_) (+-inverseˡ h) ⟩
            neg h + 0ℚ
              ≡⟨ +-identityʳ (neg h) ⟩
            neg h
              ∎
        l≡u-w : l′ ≡ u′ - w
        l≡u-w = l-decomp x m
    in
    begin
      centre x m
        ≡⟨ centre-half x m ⟩
      l′ + w * half
        ≡⟨ cong (_+ h) l≡u-w ⟩
      (u′ - w) + h
        ≡⟨ +-assoc u′ (neg w) h ⟩
      u′ + (neg w + h)
        ≡⟨ cong (u′ +_) negw+h≡negh ⟩
      u′ + neg h
        ≡⟨⟩
      u′ - h
        ∎

  -- The supremum's width at level t is the bracket width.
  --
  -- 上确界第 t 层宽度恰为第 t 层括号宽度。
  width-s≡ : ∀ t → width s t ≡ bw (br-seq t)
  width-s≡ t =
    let open ≡-Reasoning
    in
    begin
      width s t
        ≡⟨⟩
      u s t - l s t
        ≡⟨ cong₂ _-_ (u-s≡ t) (l-s≡ t) ⟩
      b t - a t
        ≡⟨⟩
      bw (br-seq t)
        ∎

  -- The supremum's centre at level t is the lower endpoint plus half
  -- the bracket width.
  --
  -- 上确界第 t 层中心等于下端点加半宽。
  cs≡ : ∀ t → centre s t ≡ a t + bw (br-seq t) * half
  cs≡ t =
    let open ≡-Reasoning
    in
    begin
      centre s t
        ≡⟨ centre-half s t ⟩
      l s t + width s t * half
        ≡⟨ cong (l s t +_) (cong (_* half) (width-s≡ t)) ⟩
      l s t + bw (br-seq t) * half
        ≡⟨ cong (_+ bw (br-seq t) * half) (l-s≡ t) ⟩
      a t + bw (br-seq t) * half
        ∎

  -- The bracket width shrinks one level.
  --
  -- 括号宽度随后继不增。
  bw-step-mono : ∀ n → bw (br-seq (suc n)) ≤ bw (br-seq n)
  bw-step-mono n =
    let open ≤-Reasoning renaming (begin_ to begin≤_; _∎ to _∎≤)
        shrink : bw (br-seq (suc n)) ≤ bw (br-seq n) * half
        shrink = step₃-shrink loc (br-seq n)
        wn-nn : 0ℚ ≤ bw (br-seq n)
        wn-nn = bw-nn (br-seq n)
        wn*half≤wn : bw (br-seq n) * half ≤ bw (br-seq n)
        wn*half≤wn =
          begin≤
            bw (br-seq n) * half
              ≤⟨ *-monoˡ-≤-nonNeg (bw (br-seq n)) ⦃ nonNegative wn-nn ⦄ half≤1 ⟩
            bw (br-seq n) * 1ℚ
              ≤-Reasoning.≡⟨ *-identityʳ (bw (br-seq n)) ⟩
            bw (br-seq n)
              ∎≤
    in ≤-trans shrink wn*half≤wn

  -- The bracket width shrinks along addition.
  --
  -- 括号宽度沿加法迭代单调递减。
  bw-mono : ∀ t d → bw (br-seq (t +ℕ d)) ≤ bw (br-seq t)
  bw-mono t zero =
    subst (λ k → bw (br-seq k) ≤ bw (br-seq t))
          (sym (+ℕ-identityʳ t)) (≤-refl {x = bw (br-seq t)})
  bw-mono t (suc d) =
    let prev : bw (br-seq (t +ℕ suc d)) ≤ bw (br-seq (t +ℕ d))
        prev = subst (λ k → bw (br-seq k) ≤ bw (br-seq (t +ℕ d)))
                    (sym (+ℕ-suc t d)) (bw-step-mono (t +ℕ d))
    in ≤-trans prev (bw-mono t d)

  -- Half-width upper bound on the regular representative.
  --
  -- 正则代表的半宽上界。
  reg-hi-half : ∀ j n m → f n ≤ℝ embedℚ (b j) →
    centre (f n) m ≤ b j + δ m + (width (f n) m) * half
  reg-hi-half j n m fn≤bj =
    let l≤ : l (f n) m ≤ b j + δ m
        l≤ = l≤b (f n) (b j) m fn≤bj
        c≡ : centre (f n) m ≡ l (f n) m + (width (f n) m) * half
        c≡ = centre-half (f n) m
        l+w/2≤ : l (f n) m + (width (f n) m) * half
                   ≤ (b j + δ m) + (width (f n) m) * half
        l+w/2≤ = +-mono-≤ l≤ ≤-refl
    in subst (λ q → q ≤ (b j + δ m) + (width (f n) m) * half)
             (sym c≡) l+w/2≤

  -- Half-width lower bound on the regular representative.
  --
  -- 正则代表的半宽下界。
  reg-lo-half : ∀ j n m → embedℚ (a j) ≤ℝ f n →
    a j - δ m - (width (f n) m) * half ≤ centre (f n) m
  reg-lo-half j n m a≤fn =
    let u≥ : a j - δ m ≤ u (f n) m
        u≥ = a≤u (f n) (a j) m a≤fn
        c≡ : centre (f n) m ≡ u (f n) m - (width (f n) m) * half
        c≡ = centre-half-lower (f n) m
        u-w/2≥ : (a j - δ m) - (width (f n) m) * half
                   ≤ u (f n) m - (width (f n) m) * half
        u-w/2≥ = +-mono-≤ u≥ ≤-refl
    in subst (λ q → (a j - δ m) - (width (f n) m) * half ≤ q)
             (sym c≡) u-w/2≥

  -- One half plus half the difference equals half the target.
  --
  -- 一半加差值的一半等于目标的一半。
  half-mid : ∀ x y → x * half + (y - x) * half ≡ y * half
  half-mid x y =
    begin
      x * half + (y - x) * half
        ≡⟨ sym (*-distribʳ-+ half x (y - x)) ⟩
      (x + (y - x)) * half
        ≡⟨ cong (_* half) (
            begin
              x + (y - x)
                ≡⟨ sym (+-assoc x y (neg x)) ⟩
              (x + y) + neg x
                ≡⟨ cong (_+ neg x) (+-comm x y) ⟩
              (y + x) + neg x
                ≡⟨ +-assoc y x (neg x) ⟩
              y + (x + neg x)
                ≡⟨ cong (y +_) (+-inverseʳ x) ⟩
              y + 0ℚ
                ≡⟨ +-identityʳ y ⟩
              y
                ∎
          ) ⟩
      y * half
        ∎

  -- A two-half sum rewritten as the left endpoint plus half the gap.
  --
  -- 两半之和重写为左端加上差值的一半。
  half-sum-rearrange : ∀ x y → x * half + y * half ≡ x + (y - x) * half
  half-sum-rearrange x y =
    begin
      x * half + y * half
        ≡⟨ sym (
            begin
              x + (y - x) * half
                ≡⟨ cong (λ q → q + (y - x) * half) (sym (two-half x)) ⟩
              (x * half + x * half) + (y - x) * half
                ≡⟨ +-assoc (x * half) (x * half) ((y - x) * half) ⟩
              x * half + (x * half + (y - x) * half)
                ≡⟨ cong (x * half +_) (half-mid x y) ⟩
              x * half + y * half
                ∎
          ) ⟩
      x + (y - x) * half
        ∎

  -- Half-width upper bound on the supremum centre relative to
  -- bracket j.
  --
  -- 上确界中心相对第 j 层括号的半宽上界。
  cs-hi-b-half : ∀ j t → j ≥N t →
    centre s t ≤ b j + (bw (br-seq t) - bw (br-seq j)) * half
  cs-hi-b-half j t j≥t =
    let open ≤-Reasoning renaming (begin_ to begin≤_; _∎ to _∎≤)
        wt = bw (br-seq t); wj = bw (br-seq j)
        at≤aj : a t ≤ a j
        at≤aj = a-in t j j≥t
        wt≤wj+wt : wt ≤ wj + wt
        wt≤wj+wt =
          begin≤
            wt
              ≤-Reasoning.≡⟨ sym (+-identityʳ wt) ⟩
            wt + 0ℚ
              ≤⟨ +-mono-≤ (≤-refl {x = wt}) (bw-nn (br-seq j)) ⟩
            wt + wj
              ≤-Reasoning.≡⟨ +-comm wt wj ⟩
            wj + wt
              ∎≤
        wt/2≤wj+wt/2 : wt * half ≤ (wj + wt) * half
        wt/2≤wj+wt/2 =
          *-monoʳ-≤-nonNeg half ⦃ nonNegative (nonNegative⁻¹ half) ⦄ wt≤wj+wt
        rearrange : a j + (wj + wt) * half ≡ b j + (wt - wj) * half
        rearrange =
          ≡-Reasoning.begin
            a j + (wj + wt) * half
              ≡-Reasoning.≡⟨ cong (a j +_) (*-distribʳ-+ half wj wt) ⟩
            a j + (wj * half + wt * half)
              ≡-Reasoning.≡⟨ cong (a j +_) (
                  ≡-Reasoning.begin
                    wj * half + wt * half
                      ≡-Reasoning.≡⟨ half-sum-rearrange wj wt ⟩
                    wj + (wt - wj) * half
                      ≡-Reasoning.∎
                ) ⟩
            a j + (wj + (wt - wj) * half)
              ≡-Reasoning.≡⟨ sym (+-assoc (a j) wj ((wt - wj) * half)) ⟩
            (a j + wj) + (wt - wj) * half
              ≡-Reasoning.≡⟨ cong (λ q → q + (wt - wj) * half) (sym (b≡a+bw j)) ⟩
            b j + (wt - wj) * half
              ≡-Reasoning.∎
    in
    begin≤
      centre s t
        ≤-Reasoning.≡⟨ cs≡ t ⟩
      a t + wt * half
        ≤⟨ +-mono-≤ at≤aj wt/2≤wj+wt/2 ⟩
      a j + (wj + wt) * half
        ≤-Reasoning.≡⟨ rearrange ⟩
      b j + (wt - wj) * half
        ∎≤

  -- Half-width lower bound on the supremum centre relative to
  -- bracket j.
  --
  -- 上确界中心相对第 j 层括号的半宽下界。

  cs-lo-b-half : ∀ j t → j ≥N t →
    a j - (bw (br-seq t) - bw (br-seq j)) * half ≤ centre s t
  cs-lo-b-half j t j≥t =
    let open ≤-Reasoning renaming (begin_ to begin≤_; _∎ to _∎≤)
        wt = bw (br-seq t); wj = bw (br-seq j)
        bj≤bt : b j ≤ b t
        bj≤bt = b-in t j j≥t
        bj=aj+wj : b j ≡ a j + wj
        bj=aj+wj = b≡a+bw j
        bt=at+wt : b t ≡ a t + wt
        bt=at+wt = b≡a+bw t
        aj+wj≤at+wt : a j + wj ≤ a t + wt
        aj+wj≤at+wt =
          subst (λ q → a j + wj ≤ q) bt=at+wt
            (subst (λ q → q ≤ b t) bj=aj+wj bj≤bt)
        -- a j - a t ≤ wt - wj
        aj-at≤ : a j - a t ≤ wt - wj
        aj-at≤ =
          let lhs≡ : (a j + wj) - (a t + wj) ≡ a j - a t
              lhs≡ = sub-cancel (a j) (a t) wj
              rhs≡ : (a t + wt) - (a t + wj) ≡ wt - wj
              rhs≡ =
                ≡-Reasoning.begin
                  (a t + wt) - (a t + wj)
                    ≡-Reasoning.≡⟨ cong (λ q → (a t + wt) - q) (+-comm (a t) wj) ⟩
                  (a t + wt) - (wj + a t)
                    ≡-Reasoning.≡⟨ cong (λ q → q - (wj + a t)) (+-comm (a t) wt) ⟩
                  (wt + a t) - (wj + a t)
                    ≡-Reasoning.≡⟨ sub-cancel wt wj (a t) ⟩
                  wt - wj
                    ≡-Reasoning.∎
              mono : (a j + wj) - (a t + wj) ≤ (a t + wt) - (a t + wj)
              mono = +-mono-≤ aj+wj≤at+wt (≤-refl {x = neg (a t + wj)})
          in subst (λ q → q ≤ wt - wj) lhs≡
               (subst (λ q → (a j + wj) - (a t + wj) ≤ q) rhs≡ mono)
        -- Negating the half-difference.
        --
        -- 半差之取负。
        neg-diff/2 : neg ((wt - wj) * half) ≡ (wj - wt) * half
        neg-diff/2 =
          ≡-Reasoning.begin
            neg ((wt - wj) * half)
              ≡-Reasoning.≡⟨ neg-distribˡ-* (wt - wj) half ⟩
            neg (wt - wj) * half
              ≡-Reasoning.≡⟨ cong (_* half) (
                  ≡-Reasoning.begin
                    neg (wt - wj)
                      ≡-Reasoning.≡⟨ neg-distrib-+ wt (neg wj) ⟩
                    neg wt + neg (neg wj)
                      ≡-Reasoning.≡⟨ cong (neg wt +_) (neg-involutive wj) ⟩
                    neg wt + wj
                      ≡-Reasoning.≡⟨ +-comm (neg wt) wj ⟩
                    wj + neg wt
                      ≡-Reasoning.≡⟨⟩
                    wj - wt
                      ≡-Reasoning.∎
                ) ⟩
            (wj - wt) * half
              ≡-Reasoning.∎
        -- The half-difference is at most half the current width.
        --
        -- 半差不超过当前层宽度的一半。
        wj-nn : 0ℚ ≤ wj
        wj-nn = bw-nn (br-seq j)
        diff≤wt : wt - wj ≤ wt
        diff≤wt =
          begin≤
            wt - wj
              ≤-Reasoning.≡⟨ sym (+-identityʳ (wt - wj)) ⟩
            (wt - wj) + 0ℚ
              ≤⟨ +-mono-≤ (≤-refl {x = wt - wj}) (
                  begin≤
                    0ℚ
                      ≤-Reasoning.≡⟨ sym (+-identityʳ 0ℚ) ⟩
                    0ℚ + 0ℚ
                      ≤⟨ +-mono-≤ (≤-refl {x = 0ℚ}) wj-nn ⟩
                    0ℚ + wj
                      ≤-Reasoning.≡⟨ +-identityˡ wj ⟩
                    wj
                      ∎≤) ⟩
            (wt - wj) + wj
              ≤-Reasoning.≡⟨ +-assoc wt (neg wj) wj ⟩
            wt + (neg wj + wj)
              ≤-Reasoning.≡⟨ cong (wt +_) (+-inverseˡ wj) ⟩
            wt + 0ℚ
              ≤-Reasoning.≡⟨ +-identityʳ wt ⟩
            wt
              ∎≤
        diff/2≤wt/2 : (wt - wj) * half ≤ wt * half
        diff/2≤wt/2 =
          *-monoʳ-≤-nonNeg half ⦃ nonNegative (nonNegative⁻¹ half) ⦄ diff≤wt
        -- A value minus its own half equals its half.
        --
        -- 一个数减去自身的一半等于其一半。
        d+neg-d/2≡d/2 : ∀ d → d + neg (d * half) ≡ d * half
        d+neg-d/2≡d/2 d =
          ≡-Reasoning.begin
            d + neg (d * half)
              ≡-Reasoning.≡⟨ cong (λ q → q + neg (d * half)) (sym (two-half d)) ⟩
            (d * half + d * half) + neg (d * half)
              ≡-Reasoning.≡⟨ +-assoc (d * half) (d * half) (neg (d * half)) ⟩
            d * half + (d * half + neg (d * half))
              ≡-Reasoning.≡⟨ cong (d * half +_) (+-inverseʳ (d * half)) ⟩
            d * half + 0ℚ
              ≡-Reasoning.≡⟨ +-identityʳ (d * half) ⟩
            d * half
              ≡-Reasoning.∎
        -- Middle rearrangement step.
        --
        -- 中间一步的重排。
        mid-step : a j + (wj - wt) * half ≤ a t + (wt - wj) * half
        mid-step =
          let d = wt - wj
              aj-at≤d : a j - a t ≤ d
              aj-at≤d = aj-at≤
              bound : (a j - a t) + neg (d * half) ≤ d * half
              bound =
                begin≤
                  (a j - a t) + neg (d * half)
                    ≤⟨ +-mono-≤ aj-at≤d (≤-refl {x = neg (d * half)}) ⟩
                  d + neg (d * half)
                    ≤-Reasoning.≡⟨ d+neg-d/2≡d/2 d ⟩
                  d * half
                    ∎≤
              rearrange1 : a j + (wj - wt) * half
                             ≡ a t + ((a j - a t) + neg (d * half))
              rearrange1 =
                ≡-Reasoning.begin
                  a j + (wj - wt) * half
                    ≡-Reasoning.≡⟨ cong (a j +_) (sym neg-diff/2) ⟩
                  a j + neg (d * half)
                    ≡-Reasoning.≡⟨ cong (λ q → q + neg (d * half))
                            (sym (a+d≡b (a t) (a j))) ⟩
                  (a t + (a j - a t)) + neg (d * half)
                    ≡-Reasoning.≡⟨ +-assoc (a t) (a j - a t) (neg (d * half)) ⟩
                  a t + ((a j - a t) + neg (d * half))
                    ≡-Reasoning.∎
          in
          begin≤
            a j + (wj - wt) * half
              ≤-Reasoning.≡⟨ rearrange1 ⟩
            a t + ((a j - a t) + neg (d * half))
              ≤⟨ +-mono-≤ (≤-refl {x = a t}) bound ⟩
            a t + d * half
              ∎≤
    in
    begin≤
      a j - (wt - wj) * half
        ≤-Reasoning.≡⟨ cong (a j +_) neg-diff/2 ⟩
      a j + (wj - wt) * half
        ≤⟨ mid-step ⟩
      a t + (wt - wj) * half
        ≤⟨ +-mono-≤ (≤-refl {x = a t}) diff/2≤wt/2 ⟩
      a t + wt * half
        ≤-Reasoning.≡⟨ sym (cs≡ t) ⟩
      centre s t
        ∎≤

  -- The sequence converges to the Cauchy limit in the
  -- regular-representative metric. Together with the equality of the
  -- limit and the supremum, this identifies the Cauchy limit with the
  -- order supremum.
  --
  -- 序列在正则代表度量下收敛到柯西极限；配合极限与上确界等价，即得
  -- 序列收敛到上确界。
  converges : ∀ k → Σ ℕ (λ N → ∀ n → n ≥N N →
    ∣ reg (f n) (suc k) - centre L (suc k) ∣ < ε (suc k))
  converges k =
    let t = suc k
        M = M a-seq t
        N = proj₁ (occ-pack M)
        body : ∀ n → n ≥N N →
          ∣ reg (f n) t - centre L t ∣ < ε t
        body n n≥N =
          let open ≤-Reasoning renaming (begin_ to begin≤_; _∎ to _∎≤)
              m = i (f n) t
              w = width (f n) m
              fn≤bM : f n ≤ℝ embedℚ (b M)
              fn≤bM = fn-upper M n
              aM≤fn : embedℚ (a M) ≤ℝ f n
              aM≤fn = fn-lower M n n≥N
              hi : reg (f n) t ≤ b M + δ m + w * half
              hi = reg-hi-half M n m fn≤bM
              lo : a M - δ m - w * half ≤ reg (f n) t
              lo = reg-lo-half M n m aM≤fn
              -- centre L t ≡ a M
              cL : centre L t ≡ a M
              cL = cL≡ t
              -- bw (br-seq M) + δ m ≤ δ t
              bwM : bw (br-seq M) ≤ bw br0 * hp M
              bwM = bw≤ M
              m≥t+3 : m ≥N suc (suc (suc t))
              m≥t+3 = fold≥k+4 (f n) (t ∸ 1)
              δm≤ : δ m ≤ δ (suc (suc (suc t)))
              δm≤ =
                let d = m ∸ (suc (suc (suc t)))
                    e : (suc (suc (suc t))) +ℕ d ≡ m
                    e = add-diff (suc (suc (suc t))) m m≥t+3
                in subst (λ k → δ k ≤ δ (suc (suc (suc t)))) e
                      (δ-dec (suc (suc (suc t)))
                                  ((suc (suc (suc t))) +ℕ d)
                                  (m≤m+n (suc (suc (suc t))) d))
              bwδ≤δt : bw (br-seq M) + δ m ≤ δ t
              bwδ≤δt =
                let M≥mod : a-mod (K t) ≤N M
                    M≥mod = M≥a-mod-K t
                    hpM≤ : hp M ≤ hp (a-mod (K t))
                    hpM≤ = hp-mono M (a-mod (K t)) M≥mod
                    bwM' : bw (br-seq M) ≤ bw br0 * hp M
                    bwM' = bwM
                    bwM'' : bw (br-seq M) ≤ bw br0 * hp (a-mod (K t))
                    bwM'' =
                      ≤-trans bwM'
                        (*-monoˡ-≤-nonNeg (bw br0)
                           {{pos⇒nonNeg (bw br0)
                              {{positive (bw-pos br0)}}}}
                           hpM≤)
                    bw<εK : bw (br-seq M) < ε (K t)
                    bw<εK = ≤-<-trans bwM'' (a-mod< (K t))
                    bw<δ : bw (br-seq M) < δ (suc t)
                    bw<δ = ≤-<-trans (<⇒≤ bw<εK) (ε-K<δ-suc t)
                    sum : bw (br-seq M) + δ m
                            ≤ δ (suc t) + δ (suc (suc (suc t)))
                    sum = +-mono-≤ (<⇒≤ bw<δ) δm≤
                in ≤-trans sum (δ-sum≤δ t)
              -- w * half < ε (suc t) * half
              w< : w < ε (suc t)
              w< = width-i (f n) t
              w/2< : w * half < ε (suc t) * half
              w/2< = *-monoˡ-<-pos half w<
              -- total < ε t
              total : ∣ reg (f n) t - a M ∣ < ε t
              total =
                let bwM = b M - a M
                    bwM≥0 : 0ℚ ≤ bwM
                    bwM≥0 =
                      let a<b : a M < b M
                          a<b = Bracket.a<b (br-seq M)
                          e : a M + neg (a M) < b M + neg (a M)
                          e = Data.Rational.Properties.+-mono-<-≤ a<b (≤-refl {neg (a M)})
                          e0 : a M + neg (a M) ≡ 0ℚ
                          e0 = +-inverseʳ (a M)
                      in <⇒≤ (subst (λ z → z < b M + neg (a M)) e0 e)
                    bM≡raw : b M ≡ a M + bwM
                    bM≡raw =
                      ≡-Reasoning.begin
                        b M
                      ≡-Reasoning.≡⟨ sym (+-identityʳ (b M)) ⟩
                        b M + 0ℚ
                      ≡-Reasoning.≡⟨ cong (b M +_) (sym (+-inverseʳ (a M))) ⟩
                        b M + (a M + neg (a M))
                      ≡-Reasoning.≡⟨ sym (+-assoc (b M) (a M) (neg (a M))) ⟩
                        (b M + a M) + neg (a M)
                      ≡-Reasoning.≡⟨ cong (_+ neg (a M)) (+-comm (b M) (a M)) ⟩
                        (a M + b M) + neg (a M)
                      ≡-Reasoning.≡⟨ +-assoc (a M) (b M) (neg (a M)) ⟩
                        a M + (b M + neg (a M))
                      ≡-Reasoning.∎
                    bwM≡bw : bwM ≡ bw (br-seq M)
                    bwM≡bw =
                      let e3 : a M + bwM ≡ a M + bw (br-seq M)
                          e3 = trans (sym bM≡raw) (b≡a+bw M)
                          cancel : ∀ {x y z} → x + y ≡ x + z → y ≡ z
                          cancel {x} {y} {z} e =
                            ≡-Reasoning.begin
                              y
                            ≡-Reasoning.≡⟨ sym (+-identityˡ y) ⟩
                              0ℚ + y
                            ≡-Reasoning.≡⟨ cong (λ q → q + y) (sym (+-inverseˡ x)) ⟩
                              (neg x + x) + y
                            ≡-Reasoning.≡⟨ +-assoc (neg x) x y ⟩
                              neg x + (x + y)
                            ≡-Reasoning.≡⟨ cong (neg x +_) e ⟩
                              neg x + (x + z)
                            ≡-Reasoning.≡⟨ sym (+-assoc (neg x) x z) ⟩
                              (neg x + x) + z
                            ≡-Reasoning.≡⟨ cong (_+ z) (+-inverseˡ x) ⟩
                              0ℚ + z
                            ≡-Reasoning.≡⟨ +-identityˡ z ⟩
                              z
                            ≡-Reasoning.∎
                      in cancel {x = a M} {y = bwM}
                                {z = bw (br-seq M)} e3
                    hi' : reg (f n) t
                            ≤ a M + (bwM + δ m) + w * half
                    hi' =
                      begin≤
                        reg (f n) t
                      ≤⟨ hi ⟩
                        b M + δ m + w * half
                      ≤-Reasoning.≡⟨ cong (λ z → z + δ m + w * half) bM≡raw ⟩
                        (a M + bwM) + δ m + w * half
                      ≤-Reasoning.≡⟨ cong (_+ w * half)
                                            (+-assoc (a M) bwM (δ m)) ⟩
                        a M + (bwM + δ m) + w * half
                      ∎≤
                    lo' : a M - (δ m + w * half) ≤ reg (f n) t
                    lo' =
                      let e : (a M - δ m) - w * half
                              ≡ a M - (δ m + w * half)
                          e =
                            ≡-Reasoning.begin
                              (a M - δ m) - w * half
                            ≡-Reasoning.≡⟨ +-assoc (a M) (neg (δ m))
                                                          (neg (w * half)) ⟩
                              a M + (neg (δ m) + neg (w * half))
                            ≡-Reasoning.≡⟨ cong (a M +_)
                                 (sym (neg-distrib-+ (δ m) (w * half))) ⟩
                              a M + neg (δ m + w * half)
                            ≡-Reasoning.∎
                      in subst (λ z → z ≤ reg (f n) t) e lo
                    d = bwM + δ m + w * half
                    abs≤ : ∣ reg (f n) t - a M ∣ ≤ d
                    abs≤ =
                      let hi'' : reg (f n) t ≤ a M + d
                          hi'' =
                            let e : a M + (bwM + δ m) + w * half
                                    ≡ a M + d
                                e = +-assoc (a M) (bwM + δ m)
                                             (w * half)
                            in subst (λ z → reg (f n) t ≤ z) e hi'
                          lo'' : a M - d ≤ reg (f n) t
                          lo'' =
                            let d≥ : δ m + w * half ≤ d
                                d≥ =
                                  begin≤
                                    (δ m + w * half)
                                      ≤-Reasoning.≡⟨ sym (+-identityˡ
                                                (δ m + w * half)) ⟩
                                    0ℚ + (δ m + w * half)
                                      ≤⟨ +-mono-≤ bwM≥0 ≤-refl ⟩
                                    bwM + (δ m + w * half)
                                      ≤-Reasoning.≡⟨ sym (+-assoc bwM (δ m)
                                                  (w * half)) ⟩
                                    (bwM + δ m) + w * half
                                      ≤-Reasoning.≡⟨⟩
                                    d
                                    ∎≤
                            in ≤-trans
                                 (begin≤
                                   (a M - d)
                                     ≤⟨ +-mono-≤ (≤-refl {x = a M})
                                                 (neg-antimono-≤ d≥) ⟩
                                   a M - (δ m + w * half)
                                   ∎≤)
                                 lo'
                      in abs-two-sided (reg (f n) t) (a M) d lo'' hi''
                    d<εt : d < ε t
                    d<εt =
                      let bwMδ≤δt : bwM + δ m ≤ δ t
                          bwMδ≤δt =
                            subst (λ z → z + δ m ≤ δ t)
                                  (sym bwM≡bw) bwδ≤δt
                          step1 : (bwM + δ m) + w * half
                                   ≤ δ t + w * half
                          step1 = +-mono-≤ bwMδ≤δt
                                      (≤-refl {x = w * half})
                          step2 : δ t + w * half
                                    < δ t + ε (suc t) * half
                          step2 = Data.Rational.Properties.+-mono-≤-<
                                     (≤-refl {x = δ t}) w/2<
                          step3 : δ t + ε (suc t) * half
                                    ≤ ε t * half + ε (suc t) * half
                          step3 = +-mono-≤ (δ≤ε-half t)
                                      (≤-refl {x = ε (suc t) * half})
                          step4 : ε t * half + ε (suc t) * half
                                    < ε t * half + ε t * half
                          step4 =
                            let εsuc< : ε (suc t) * half < ε t * half
                                εsuc< =
                                  let e1 : ε (suc t) < ε t
                                      e1 =
                                        let p = embed (suc t)
                                            q = embed (suc (suc t))
                                            nzp : NonZero p
                                            nzp = pos⇒nonZero p
                                                    {{positive (0<embed t)}}
                                            nzq : NonZero q
                                            nzq = pos⇒nonZero q
                                                    {{positive (0<embed (suc t))}}
                                        in recip-antitone (suc t) (suc (suc t))
                                             (0<embed t)
                                             (≤N-refl)
                                             {{nzp}} {{nzq}}
                                  in *-monoˡ-<-pos half e1
                            in Data.Rational.Properties.+-mono-≤-<
                                 (≤-refl {x = ε t * half}) εsuc<
                          step5 : ε t * half + ε t * half ≡ ε t
                          step5 = two-half (ε t)
                      in Data.Rational.Properties.<-≤-trans
                           (≤-<-trans (<⇒≤ (Data.Rational.Properties.<-≤-trans
                             (≤-<-trans step1 step2) step3)) step4)
                             (≤-reflexive step5)
                in ≤-<-trans abs≤ d<εt
          in subst (λ c → ∣ reg (f n) t - c ∣ < ε t) (sym cL) total
    in N , body
