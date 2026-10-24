------------------------------------------------------------------------
-- Completeness of real intervals under the weakest (full-metric) Cauchy
-- condition
--
-- 最弱（全度量）柯西条件下实数区间的完备性
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module Real.Interval.WeakComplete where

open import Data.Nat using (ℕ; zero; suc; _⊔_; _^_; _∸_; s≤s; z≤n)
  renaming (_≤_ to _≤N_; _≥_ to _≥N_; _+_ to _+ℕ_; _*_ to _*ℕ_; _<_ to _<N_)
open import Data.Nat.Properties using
  (m≤m⊔n; m≤n⊔m; m≤m+n; m≤n+m; ≤-total; n≤1+n; n<1+n; m+[n∸m]≡n
  ; +-suc; *-suc; *-monoʳ-≤; *-monoˡ-≤; ^-monoʳ-≤; *-distribˡ-+
  ; m≤n⇒m⊔n≡n; m≤n*m)
  renaming (≤-trans to ≤N-trans; ≤-refl to ≤N-refl
          ; ≤-reflexive to ≤N-reflexive; <⇒≤ to <N⇒≤N
          ; +-comm to +-commℕ; +-mono-≤ to +-mono-≤N
          ; +-identityˡ to +-identityˡℕ; +-identityʳ to +-identityʳℕ
          ; +-assoc to +-assocℕ; *-assoc to *-assocℕ
          ; ≤-<-trans to ≤N-<-trans; <-≤-trans to <-≤N-trans
          ; *-comm to *-commℕ; *-identityʳ to *-identityʳℕ)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Rational using
  (ℚ; 0ℚ; 1ℚ; _+_; _-_; _*_; _<_; _≤_; ∣_∣; positive; Positive; NonZero)
open import Data.Rational.Base using (1/_; *<*; -_)
open import Data.Integer using (+<+)
open import Data.Rational.Properties using
  (≤-refl; ≤-reflexive; ≤-trans; ≤-<-trans; <-≤-trans; <-trans
  ; +-mono-<; +-mono-≤; +-mono-≤-<; +-identityʳ; +-identityˡ; +-assoc
  ; +-inverseʳ; +-inverseˡ; neg-distrib-+
  ; ∣p+q∣≤∣p∣+∣q∣; ∣-p∣≡∣p∣; positive⁻¹
  ; pos⇒nonNeg; pos⇒nonZero; pos*pos⇒pos; *-monoʳ-≤-nonNeg; *-inverseʳ
  ; *-inverseˡ; *-assoc; *-comm; *-identityˡ; *-identityʳ; <⇒≤
  ; *-distribʳ-+; +-comm)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; cong; cong₂; sym; trans; subst; module ≡-Reasoning)
open ≡-Reasoning

open import Real using
  (CauchySeq; ε; 0<ε; embed; embed-suc-pos; embed-suc-nonZero; 2ℚ; 2*embed
  ; halve; reciprocal-cong; 0<embed; 1/embed; embed-mono-<; embed-mono-≤
  ; embed-+-hom; embed-*-hom; embed-*)
open CauchySeq using (μ)
open import Real.Interval using (RealI)
open import Real.IntervalEquiv using
  (centre; width; width-n; width-nV; recipPow2; bound-w; realI→cauchy
  ; B<2^sucB; frac-strict; 0<width)
open import Real.Interval.Kit using (tri-diff)
open import Real.CauchyToInterval using
  (cauchy→realI; centre-cauchy→realI; M; K; M≥μK; K≥k)
open import Real.Interval.WeakArith using
  (half; h; h-mono; h≡suc2c; h≥2k
  ; h+1; h+1≡suc; h+1≥2*suc
  ; 2ss; 2ss-nonZero; εs-half; 2ss2a≡4a
  ; h+1-nonZero; strict-recip
  ; recip-antitone-≤; base-bound; prod≤2^; embed-prod<
  ; cancel-*; doubleN; diff-neg)
open import Real.Interval.RegularRep using (reg; reg-reg)

------------------------------------------------------------------------
-- Weakest (full-metric) Cauchy condition
--
-- For every precision k there is an index N such that, for all n,m ≥ N,
-- the regular representatives at the successor precision are within
-- ε (suc k) / 2.
--
-- 最弱（全度量）柯西条件
--
-- 每个精度 k 存在索引 N，使得对所有 n,m ≥ N，在后继精度处的正则
-- 代表落在 ε (suc k) / 2 内。

WeakCauchy : (ℕ → RealI) → Set
WeakCauchy f = ∀ k → Σ ℕ (λ N →
  ∀ n m → n ≥N N → m ≥N N →
    ∣ reg (f n) (suc k) - reg (f m) (suc k) ∣ < ε (suc k) * half)

module _ {f : ℕ → RealI} (w : WeakCauchy f) where

  ----------------------------------------------------------------------
  -- Monotone witness
  --
  -- 单调见证

  rawWit : ℕ → ℕ
  rawWit k = proj₁ (w k)

  monoWit : ℕ → ℕ
  monoWit zero    = rawWit zero
  monoWit (suc k) = monoWit k ⊔ rawWit (suc k)

  monoWit-mono : ∀ k → monoWit k ≤N monoWit (suc k)
  monoWit-mono k = m≤m⊔n (monoWit k) (rawWit (suc k))

  raw≤mono : ∀ t → rawWit t ≤N monoWit t
  raw≤mono zero    = ≤N-refl
  raw≤mono (suc t) = m≤n⊔m (monoWit t) (rawWit (suc t))

  monoWit-step : ∀ a d → monoWit a ≤N monoWit (d +ℕ a)
  monoWit-step a zero    = ≤N-refl
  monoWit-step a (suc d) =
    ≤N-trans (monoWit-step a d)
             (m≤m⊔n (monoWit (d +ℕ a)) (rawWit (suc (d +ℕ a))))

  monoWit≥raw : ∀ k t → t ≤N k → rawWit t ≤N monoWit k
  monoWit≥raw k t t≤k =
    subst (λ j → rawWit t ≤N monoWit j) eq
      (≤N-trans (raw≤mono t) (monoWit-step t (k ∸ t)))
    where
    eq : (k ∸ t) +ℕ t ≡ k
    eq = trans (sym (+-commℕ t (k ∸ t))) (m+[n∸m]≡n t≤k)

  ----------------------------------------------------------------------
  -- Increasing regular subsequence
  --
  -- 递增正则子序列

  n : ℕ → ℕ
  n zero    = monoWit zero
  n (suc k) = suc (n k) ⊔ monoWit (suc k)

  n-mono : ∀ k → n k <N n (suc k)
  n-mono k = m≤m⊔n (suc (n k)) (monoWit (suc k))

  n≥mono : ∀ k → monoWit k ≤N n k
  n≥mono zero    = ≤N-refl
  n≥mono (suc k) = m≤n⊔m (suc (n k)) (monoWit (suc k))

  n≥raw : ∀ k → rawWit k ≤N n k
  n≥raw k = ≤N-trans (monoWit≥raw k k ≤N-refl) (n≥mono k)

  iter : ℕ → ℕ → ℕ
  iter zero    k = k
  iter (suc d) k = suc (iter d k)

  iter≡+ : ∀ d k → iter d k ≡ d +ℕ k
  iter≡+ zero    k = +-identityˡℕ k
  iter≡+ (suc d) k = cong suc (iter≡+ d k)

  n-step : ∀ k d → n k ≤N n (iter d k)
  n-step k zero    = ≤N-refl
  n-step k (suc d) = ≤N-trans (n-step k d) (<N⇒≤N (n-mono (iter d k)))

  n≤a : ∀ k a → k ≤N a → n k ≤N n a
  n≤a k a le =
    subst (λ j → n k ≤N n j) eq (n-step k (a ∸ k))
    where
    eq : iter (a ∸ k) k ≡ a
    eq = trans (iter≡+ (a ∸ k) k)
               (trans (+-commℕ (a ∸ k) k) (m+[n∸m]≡n le))

  ----------------------------------------------------------------------
  -- Diagonal: a rational Cauchy sequence
  --
  -- h k = 2k + 1; b k = reg (f (n (h k))) (h k).
  --
  -- 对角：有理柯西序列

  b : ℕ → ℚ
  b k = reg (f (n (h k))) (h k)

  -- n (h k) ≥ rawWit (2k), since h k = 2k + 1 ≥ 2k.
  --
  -- n (h k) ≥ rawWit (2k)，因 h k = 2k + 1 ≥ 2k。
  n-h≥raw : ∀ k → n (h k) ≥N rawWit (2 *ℕ k)
  n-h≥raw k =
    ≤N-trans (monoWit≥raw (h k) (2 *ℕ k) (h≥2k k))
             (n≥mono (h k))

  ----------------------------------------------------------------------
  -- Chain-style proof that b is Cauchy
  --
  -- b 为柯西序列的链式证明

  b-go : ∀ k a c → a ≥N k → c ≥N k → a ≤N c → ∣ b a - b c ∣ < ε k
  b-go k a c a≥k c≥k a≤c =
    let pa = n (h a); pc = n (h c)
        ra = f pa; rc = f pc
        -- Thresholds: pa ≥ rawWit (2a); pc ≥ pa ≥ rawWit (2a).
        pa≥raw : pa ≥N rawWit (2 *ℕ a)
        pa≥raw = n-h≥raw a
        pc≥pa : pc ≥N pa
        pc≥pa = n≤a (h a) (h c) (h-mono a c a≤c)
        pc≥raw : pc ≥N rawWit (2 *ℕ a)
        pc≥raw = ≤N-trans pa≥raw pc≥pa
        -- Cross at precision 2a (= h a ∸ 1):
        -- reg ra (h a) vs reg rc (h a), budget ε (h a) * half.
        crossRaw : ∣ reg ra (h a) - reg rc (h a) ∣ < ε (h a) * half
        crossRaw =
          subst (λ i → ∣ reg ra i - reg rc i ∣ < ε i * half)
                (sym (h≡suc2c a))
                (proj₂ (w (2 *ℕ a)) pa pc pa≥raw pc≥raw)
        -- Tail (reg-reg): reg rc (h a) → reg rc (h c) = b c,
        -- budget ε (suc (h a)).
        tail : ∣ reg rc (h a) - reg rc (h c) ∣ < ε (suc (h a))
        tail = reg-reg rc (h a) (h a) (h c) ≤N-refl
                          (h-mono a c a≤c)
        -- Bounds: crossB = 1/embed (4a+4), tailB = 1/embed (2a+3).
        crossB = 1/ embed (4 *ℕ suc a)
        tailB = 1/ embed (suc (h+1 a))
        crossEq : ε (h a) * half ≡ crossB
        crossEq =
          begin
            ε (h a) * half
              ≡⟨ cong (λ e → e * half) (cong ε (h≡suc2c a)) ⟩
            ε (suc (2 *ℕ a)) * half
              ≡⟨ εs-half (2 *ℕ a) ⟩
            (1/ embed (2ss (2 *ℕ a))) {{2ss-nonZero {2 *ℕ a}}}
              ≡⟨ reciprocal-cong (embed (2ss (2 *ℕ a)))
                                  (embed (4 *ℕ suc a))
                                  {{2ss-nonZero {2 *ℕ a}}}
                                  (cong embed (2ss2a≡4a a)) ⟩
            crossB
              ∎
        tailEq : ε (suc (h a)) ≡ tailB
        tailEq =
          begin
            ε (suc (h a))
              ≡⟨⟩
            1/ embed (suc (suc (h a)))
              ≡⟨ reciprocal-cong (embed (suc (suc (h a))))
                                  (embed (suc (h+1 a)))
                                  (cong embed
                                    (sym (cong suc (h+1≡suc a)))) ⟩
            tailB
              ∎
        cross : ∣ reg ra (h a) - reg rc (h a) ∣ < crossB
        cross = subst (λ z → ∣ reg ra (h a) - reg rc (h a) ∣ < z)
                      crossEq crossRaw
        tail' : ∣ reg rc (h a) - b c ∣ < tailB
        tail' = subst (λ z → ∣ reg rc (h a) - b c ∣ < z)
                      tailEq tail
        -- Triangle: b a = reg ra (h a), via reg rc (h a), to b c.
        tri : ∣ b a - b c ∣ < crossB + tailB
        tri = ≤-<-trans (tri-diff (b a) (reg rc (h a)) (b c))
                        (+-mono-< cross tail')
        -- a ≥ k: 4a+4 ≥ 4k+4 and 2a+3 ≥ 2k+3, so the sum is bounded
        -- by the base-bound LHS, which is < ε k.
        4a≥4k : 4 *ℕ suc a ≥N 4 *ℕ suc k
        4a≥4k = *-monoʳ-≤ 4 (s≤s a≥k)
        t2a≥t2k : suc (h+1 a) ≥N suc (2 *ℕ suc k)
        t2a≥t2k = s≤s (h+1≥2*suc a k a≥k)
        -- 4·suc k = suc (k + (k + (suc k + (suc k + 0)))) (stdlib form).
        pos4k : 0ℚ < embed (4 *ℕ suc k)
        pos4k = 0<embed (k +ℕ (suc k +ℕ (suc k +ℕ (suc k +ℕ 0))))
        sum≤ : crossB + tailB ≤
                  1/ embed (4 *ℕ suc k) + 1/ embed (suc (2 *ℕ suc k))
        sum≤ = +-mono-≤ (recip-antitone-≤ (4 *ℕ suc k) (4 *ℕ suc a)
                                          pos4k 4a≥4k)
                        (recip-antitone-≤ (suc (2 *ℕ suc k))
                                          (suc (h+1 a))
                                          (0<embed (2 *ℕ suc k))
                                          t2a≥t2k)
    in <-trans (<-≤-trans tri sum≤) (base-bound k)

  b-total : ∀ k a c → a ≥N k → c ≥N k →
            (a ≤N c) ⊎ (c ≤N a) → ∣ b a - b c ∣ < ε k
  b-total k a c a≥k c≥k (inj₁ a≤c) = b-go k a c a≥k c≥k a≤c
  b-total k a c a≥k c≥k (inj₂ c≤a) =
    subst (λ x → x < ε k) abs-eq (b-go k c a c≥k a≥k c≤a)
    where
    abs-eq : ∣ b c - b a ∣ ≡ ∣ b a - b c ∣
    abs-eq =
      trans (cong ∣_∣ (sym (diff-neg (b a) (b c))))
            (∣-p∣≡∣p∣ (b a - b c))

  b-cauchy : ∀ k a c → a ≥N k → c ≥N k → ∣ b a - b c ∣ < ε k
  b-cauchy k a c a≥k c≥k =
    b-total k a c a≥k c≥k (≤-total a c)

  ----------------------------------------------------------------------
  -- Limit and convergence
  --
  -- 极限与收敛

  b-seq : CauchySeq
  b-seq = record { f = b ; μ = λ k → k ; cauchy = b-cauchy }

  L : RealI
  L = cauchy→realI b-seq

  _⟶_ : (ℕ → RealI) → RealI → Set
  f ⟶ L = ∀ k → Σ ℕ (λ N → ∀ n → n ≥N N →
    ∣ reg (f n) (suc k) - centre L (suc k) ∣ < ε (suc k))

  weak-complete : f ⟶ L
  weak-complete k = N , step
    where
    j = K (suc k)

    -- K is increasing: K n ≤ K (suc n).
    --
    -- K 单调：K n ≤ K (suc n)。
    K-inc : ∀ n → K n ≤N K (suc n)
    K-inc n =
      ≤N-trans (m≤m+n (K n) (K n))
               (≤N-reflexive (sym (doubleN (K n))))

    -- M b-seq n ≡ K n: the modulus is the identity and K is increasing.
    --
    -- M b-seq n ≡ K n：模数为恒等，且 K 单调。
    M-id : ∀ n → M b-seq n ≡ K n
    M-id zero    = refl
    M-id (suc n) =
      begin
        M b-seq (suc n)
          ≡⟨⟩
        M b-seq n ⊔ K (suc n)
          ≡⟨ cong (_⊔ K (suc n)) (M-id n) ⟩
        K n ⊔ K (suc n)
          ≡⟨ m≤n⇒m⊔n≡n (K-inc n) ⟩
        K (suc n)
          ∎

    cL : centre L (suc k) ≡ b j
    cL =
      begin
        centre L (suc k)
          ≡⟨ centre-cauchy→realI b-seq (suc k) ⟩
        b (M b-seq (suc k))
          ≡⟨ cong b (M-id (suc k)) ⟩
        b j
          ∎

    j≤2j : j ≤N 2 *ℕ j
    j≤2j = ≤N-trans (m≤m+n j j) (≤N-reflexive (sym (doubleN j)))
    hj≥sk : h j ≥N suc k
    hj≥sk =
      ≤N-trans (K≥k (suc k))
               (≤N-trans j≤2j (h≥2k j))

    -- Anchor index pa = n (h j), with pa ≥ rawWit (2j).
    --
    -- 锚点下标 pa = n (h j)，满足 pa ≥ rawWit (2j)。
    pa = n (h j)
    pa≥raw : pa ≥N rawWit (2 *ℕ j)
    pa≥raw = n-h≥raw j

    -- Convergence threshold: n ≥ rawWit (2j).
    --
    -- 收敛阈值：n ≥ rawWit (2j)。
    N = rawWit (2 *ℕ j)

    m+1≡suc : (suc (suc k)) +ℕ 1 ≡ suc (suc (suc k))
    m+1≡suc =
      trans (+-suc (suc (suc k)) 0)
            (cong suc (+-identityʳℕ (suc (suc k))))

    step : ∀ n → n ≥N N →
      ∣ reg (f n) (suc k) - centre L (suc k) ∣ < ε (suc k)
    step n n≥N =
      let A = reg (f n) (suc k)
          B = reg (f n) (h j)
          C = b j
          n≥raw : n ≥N rawWit (2 *ℕ j)
          n≥raw = n≥N

          -- Segment 1 (reg-reg): A → B, budget ε (suc(suc k)).
          --
          -- 第一段（reg-reg）：A → B，预算 ε (suc(suc k))。
          seg1 : ∣ A - B ∣ < ε (suc (suc k))
          seg1 = reg-reg (f n) (suc k) (suc k) (h j) ≤N-refl hj≥sk

          -- Segment 2 (cross): B vs C at precision h j, budget
          -- ε(h j)*half.
          --
          -- 第二段（cross）：B 与 C 在精度 h j 处，预算 ε(h j)*half。
          crossRaw : ∣ B - C ∣ < ε (h j) * half
          crossRaw =
            subst (λ i → ∣ reg (f n) i - reg (f pa) i ∣ < ε i * half)
                  (sym (h≡suc2c j))
                  (proj₂ (w (2 *ℕ j)) n pa n≥raw pa≥raw)
          crossB = 1/ embed (4 *ℕ suc j)
          crossEq : ε (h j) * half ≡ crossB
          crossEq =
            begin
              ε (h j) * half
                ≡⟨ cong (λ e → e * half) (cong ε (h≡suc2c j)) ⟩
              ε (suc (2 *ℕ j)) * half
                ≡⟨ εs-half (2 *ℕ j) ⟩
              (1/ embed (2ss (2 *ℕ j))) {{2ss-nonZero {2 *ℕ j}}}
                ≡⟨ reciprocal-cong (embed (2ss (2 *ℕ j)))
                                   (embed (4 *ℕ suc j))
                                   {{2ss-nonZero {2 *ℕ j}}}
                                   (cong embed (2ss2a≡4a j)) ⟩
              crossB
                ∎
          seg2 : ∣ B - C ∣ < crossB
          seg2 = subst (λ z → ∣ B - C ∣ < z) crossEq crossRaw

          -- Triangle: ∣ A - C ∣ < ε (suc(suc k)) + crossB.
          --
          -- 三角不等式：∣ A - C ∣ < ε (suc(suc k)) + crossB。
          tri : ∣ A - C ∣ < ε (suc (suc k)) + crossB
          tri = ≤-<-trans (tri-diff A B C) (+-mono-< seg1 seg2)

          -- Rational scaffolding:
          --   x = k+2, y = k+3, t = 1/((k+2)(k+3)).
          --
          -- 有理脚手架：
          --   x = k+2，y = k+3，t = 1/((k+2)(k+3))。
          x = embed (suc (suc k))
          y = embed (suc (suc (suc k)))
          instance
            pos-x : Positive x
            pos-x = embed-suc-pos
            pos-y : Positive y
            pos-y = embed-suc-pos
            pos-xy : Positive (x * y)
            pos-xy = pos*pos⇒pos x y
            nz-xy : NonZero (x * y)
            nz-xy = pos⇒nonZero (x * y)
            pos-yx : Positive (y * x)
            pos-yx = pos*pos⇒pos y x
            nz-yx : NonZero (y * x)
            nz-yx = pos⇒nonZero (y * x)
          t = 1/(x * y)
          inv-x = 1/ x
          inv-y = 1/ y

          h1 : x * t ≡ inv-y
          h1 = cancel-* x y

          inv-yx : 1/(y * x) ≡ t
          inv-yx = reciprocal-cong (y * x) (x * y) (*-comm y x)

          h2 : y * t ≡ inv-x
          h2 = trans (cong (y *_) (sym inv-yx)) (cancel-* y x)

          x+1≡y : x + 1ℚ ≡ y
          x+1≡y =
            begin
              x + 1ℚ
                ≡⟨ refl ⟩
              x + embed 1
                ≡⟨ sym (embed-+-hom (suc (suc k)) 1) ⟩
              embed ((suc (suc k)) +ℕ 1)
                ≡⟨ cong embed m+1≡suc ⟩
              y
                ∎

          distrib : (x * t) + t ≡ (x + 1ℚ) * t
          distrib =
            begin
              (x * t) + t
                ≡⟨ cong (λ z → (x * t) + z) (sym (*-identityˡ t)) ⟩
              (x * t) + (1ℚ * t)
                ≡⟨ sym (*-distribʳ-+ t x 1ℚ) ⟩
              (x + 1ℚ) * t
                ∎

          frac-id : inv-y + t ≡ inv-x
          frac-id =
            begin
              inv-y + t
                ≡⟨ cong (λ z → z + t) (sym h1) ⟩
              (x * t) + t
                ≡⟨ distrib ⟩
              (x + 1ℚ) * t
                ≡⟨ cong (_* t) x+1≡y ⟩
              y * t
                ≡⟨ h2 ⟩
              inv-x
                ∎
          j<4sj : j <N 4 *ℕ suc j
          j<4sj = <-≤N-trans (n<1+n j) (m≤n*m (suc j) 4)

          -- crossB < t (strict reciprocals):
          --   x*y < embed(4·suc j), so 1/embed(4·suc j) < 1/(x*y).
          --
          -- crossB < t（严格倒数）：
          --   x*y < embed(4·suc j)，故 1/embed(4·suc j) < 1/(x*y)。
          ab<4sj : (suc (suc k)) *ℕ (suc (suc (suc k))) <N 4 *ℕ suc j
          ab<4sj = ≤N-<-trans (prod≤2^ k) j<4sj
          x*y<4sj : x * y < embed (4 *ℕ suc j)
          x*y<4sj =
            embed-prod< (suc (suc k)) (suc (suc (suc k)))
                       (4 *ℕ suc j) ab<4sj
          seg2<t : crossB < t
          seg2<t =
            strict-recip (x * y) (embed (4 *ℕ suc j))
                         (positive⁻¹ (x * y)) x*y<4sj
          e1≡ : ε (suc (suc k)) ≡ inv-y
          e1≡ = sym (1/embed (suc (suc k)))
          ek≡ : ε (suc k) ≡ inv-x
          ek≡ = sym (1/embed (suc k))
          s1 : inv-y + crossB < inv-y + t
          s1 = +-mono-≤-< ≤-refl seg2<t
          sum< : ε (suc (suc k)) + crossB < inv-x
          sum< =
            subst (λ z → z + crossB < inv-x) (sym e1≡)
                  (<-≤-trans s1 (≤-reflexive frac-id))
          total : ∣ A - C ∣ < ε (suc k)
          total =
            subst (λ z → ∣ A - C ∣ < z) ek≡
                  (<-trans tri sum<)
      in subst (λ z → ∣ A - z ∣ < ε (suc k)) (sym cL) total
