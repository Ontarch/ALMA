------------------------------------------------------------------------
-- Full pushback: rational Cauchy convergence reflects to layer-wise
-- convergence of the nested-interval real
--
-- 完整回推：有理柯西收敛反映为嵌套区间实数的逐层收敛
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module Real.Pushback where

open import Data.Nat using (ℕ; zero; suc; s≤s; z≤n; _⊔_; _≥_; _*_; _^_)
  renaming (_+_ to _+N_; _≤_ to _≤N_; _<_ to _<N_)
open import Data.Nat.Properties as ℕP using (≤-trans; m≤m+n; m≤m⊔n; m≤n⊔m; +-suc)
open import Data.Product using (Σ; _,_)
open import Data.Rational using (ℚ; _+_; _-_; _<_; _≤_; ∣_∣)
open import Data.Rational.Properties using
  (<⇒≤; ≤-<-trans; +-mono-<-≤) renaming (<-trans to ℚ<-trans)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; trans; subst; sym; cong)

open import Real using (CauchySeq; ε; 0<ε; embed; 0<embed; ε-half; embed-mono-<)
open CauchySeq renaming (f to seq-f; μ to seq-μ; cauchy to seq-cauchy)
open import Real.Convergence using (Converges)
open import Real.Interval using (RealI)
open import Real.IntervalEquiv using (node; centre; n<2^n)
open import Real.Interval.Kit using (tri-diff; strict-recip)
open import Real.Interval.Complete using (_⟶_)
open import Real.CauchyToInterval using
  (cauchy→realI; M; K; μ≤M; point; centre-point; centre-cauchy→realI)

-- ε is strictly antitone: a strictly larger index gives a strictly
-- smaller tolerance.
--
-- ε 严格反单调：下标严格增大时，容差严格减小。
ε-< : ∀ {i j} → i Data.Nat.< j → ε j < ε i
ε-< {i} {j} i<j = strict-recip (embed (suc i)) (embed (suc j))
                          (0<embed i) (embed-mono-< (s≤s i<j))

-- At every precision k there is a layer n whose centre of the
-- nested-interval real lies strictly within ε k of the rational limit.
--
-- 在每个精度下，存在某一层，使该嵌套区间实数的中心落在有理极限的
-- 对应严格邻域之内。
centre-approximates : (x : CauchySeq) (l : ℚ) →
  Converges (seq-f x) l →
  ∀ k → Σ ℕ λ n →
    ∣ centre (cauchy→realI x) n - l ∣ < ε k
centre-approximates x l cv k =
  let h = suc (2 * k)
      n = h
      N0 , w0 = cv (ε h) (0<ε h)
      mn = M x n ⊔ N0
      M≤mn = ℕP.m≤m⊔n (M x n) N0
      N0≤mn = ℕP.m≤n⊔m (M x n) N0
      h<2h : h <N 2 ^ h
      h<2h = n<2^n h
      1<2 : 1 <N 2
      1<2 = s≤s (s≤s z≤n)
      h≤s : h ≤N suc h
      h≤s = ℕP.n≤1+n h
      h<ss : h <N suc (suc h)
      h<ss = s≤s h≤s
      2h<Kh : 2 ^ h <N 2 ^ suc (suc h)
      2h<Kh = ℕP.^-monoʳ-< 2 1<2 h<ss
      h<Kh : h <N K h
      h<Kh = ℕP.<-trans h<2h 2h<Kh
      μ≤mn : seq-μ x (K n) ≤N mn
      μ≤mn = ℕP.≤-trans (μ≤M x n) M≤mn
      c1 : ∣ seq-f x (M x n) - seq-f x mn ∣ < ε (K n)
      c1 = seq-cauchy x (K n) (M x n) mn (μ≤M x n) μ≤mn
      c1′ : ∣ seq-f x (M x n) - seq-f x mn ∣ < ε h
      c1′ = ℚ<-trans c1 (ε-< h<Kh)
      c2 : ∣ seq-f x mn - l ∣ < ε h
      c2 = w0 mn N0≤mn
      sum< : ∣ seq-f x (M x n) - seq-f x mn ∣ + ∣ seq-f x mn - l ∣ < ε h + ε h
      sum< = +-mono-<-≤ c1′ (<⇒≤ c2)
      tri≤ : ∣ seq-f x (M x n) - l ∣ ≤
             ∣ seq-f x (M x n) - seq-f x mn ∣ + ∣ seq-f x mn - l ∣
      tri≤ = tri-diff (seq-f x (M x n)) (seq-f x mn) l
      bound : ∣ seq-f x (M x n) - l ∣ < ε h + ε h
      bound = ≤-<-trans tri≤ sum<
      final : ∣ seq-f x (M x n) - l ∣ < ε k
      final = subst (λ z → ∣ seq-f x (M x n) - l ∣ < z) (ε-half k) bound
      eq = centre-cauchy→realI x n
  in n , subst (λ z → ∣ z - l ∣ < ε k) (sym eq) final

-- Reading a real from layer n shifts the centre index.
--
-- 从第 n 层读取实数，中心指标相应平移。
node-next : (r : RealI) (k : ℕ) →
  node (RealI.next r) k ≡ RealI.next (node r k)
node-next r zero    = refl
node-next r (suc k) = cong RealI.next (node-next r k)

-- Centres of the same real at shifted indices agree.
--
-- 同一实数在平移下标处的中心相同。
centre-shift : (x : RealI) (n k : ℕ) →
  centre (node x n) k ≡ centre x (n +N k)
centre-shift x zero k = refl
centre-shift x (suc n) k =
  trans (cong (λ r → centre r zero) (node-next (node x n) k))
        (trans (centre-shift x n (suc k))
               (cong (centre x) (+-suc n k)))


-- The sequence of deeper-and-deeper nodes of the constructed real.
--
-- 所构造实数逐层深入的节点序列。
tail-seq : CauchySeq → ℕ → RealI
tail-seq x n = node (cauchy→realI x) n

-- Rational convergence of the underlying Cauchy sequence implies the
-- tail sequence converges layer-wise to the constant point l.
--
-- 底层柯西序列的有理收敛蕴含其尾序列逐层收敛于常点 l。
pushback : (x : CauchySeq) (l : ℚ) →
  Converges (seq-f x) l → tail-seq x ⟶ point l
pushback x l cv k =
  let h = suc (2 * k)
      N0 , w0 = cv (ε h) (0<ε h)
      bound-at : (j : ℕ) → j ≥ h →
        ∣ seq-f x (M x j) - l ∣ < ε k
      bound-at j j≥h =
        let mn = M x j ⊔ N0
            M≤mn = m≤m⊔n (M x j) N0
            N0≤mn = m≤n⊔m (M x j) N0
            μ≤mn = ≤-trans (μ≤M x j) M≤mn

            h<Kh : h <N K h
            h<Kh = ℕP.<-≤-trans (n<2^n h)
                    (ℕP.^-monoʳ-≤ 2 (ℕP.m≤n+m h 2))

            Kh≤Kj : K h ≤N K j
            Kh≤Kj = ℕP.^-monoʳ-≤ 2 (s≤s (s≤s j≥h))

            h<Kj : h <N K j
            h<Kj = ℕP.<-≤-trans h<Kh Kh≤Kj

            c1 = seq-cauchy x (K j) (M x j) mn (μ≤M x j) μ≤mn
            c1′ = ℚ<-trans c1 (ε-< h<Kj)
            c2 = w0 mn N0≤mn
            sum< = +-mono-<-≤ c1′ (<⇒≤ c2)
            tri≤ = tri-diff (seq-f x (M x j)) (seq-f x mn) l
            bound = ≤-<-trans tri≤ sum<
        in subst (λ z → ∣ seq-f x (M x j) - l ∣ < z) (ε-half k) bound
      proof : (n : ℕ) → n ≥ h →
        ∣ centre (tail-seq x n) k - centre (point l) k ∣ < ε k
      proof n n≥h =
        let j = n +N k
            j≥h : j ≥ h
            j≥h = ℕP.≤-trans n≥h (m≤m+n n k)
            cs = centre-shift (cauchy→realI x) n k
            cp = centre-point l k
            eq : centre (tail-seq x n) k ≡ seq-f x (M x j)
            eq = trans cs (centre-cauchy→realI x j)
            b = bound-at j j≥h
        in subst (λ z → ∣ z - centre (point l) k ∣ < ε k) (sym eq)
             (subst (λ z → ∣ seq-f x (M x j) - z ∣ < ε k) (sym cp) b)
  in h , proof
