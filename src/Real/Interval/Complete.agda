------------------------------------------------------------------------
-- Completeness of real intervals
--
-- Proves completeness of RealI under the Cauchy condition.
--
-- 实数区间的完备性
--
-- 证明 RealI 在柯西条件下的完备性。
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module Real.Interval.Complete where

open import Data.Nat using (ℕ; _⊔_; _≥_) renaming (_≤_ to _≤ℕ_)
open import Data.Nat.Properties using
  (m≤m⊔n; m≤n⊔m) renaming (≤-trans to ≤ℕ-trans; ≤-refl to ≤ℕ-refl)
open import Data.Product using (Σ; _,_; _×_; proj₁; proj₂)
open import Data.Rational using
  (ℚ; 0ℚ; _+_; _-_; _*_; _<_; _≤_; ∣_∣; positive)
open import Data.Rational.Properties using
  (≤-<-trans; +-mono-<; <-trans; +-monoʳ-<; +-identityʳ; pos*pos⇒pos;
   positive⁻¹)
open import Relation.Binary.PropositionalEquality using (_≡_; sym; subst)

open import Real using (CauchySeq; ε; 0<ε)
open import Real.Interval using (RealI)
open import Real.IntervalEquiv using (width; centre; centre-diff)
open import Real.CauchyToInterval using
  (cauchy→realI; M; centre-cauchy→realI; K; M≥μK; K≥k)
open import Real.Interval.Kit using (half; 0<half; two-half; tri-diff)

------------------------------------------------------------------------
-- ε-half
--
-- For any precision index k, half of the tolerance ε k is strictly
-- less than ε k itself. This is used to split error bounds in the
-- completeness proof.
--
-- ε 减半
--
-- 对任意精度索引 k，容差 ε k 的一半严格小于 ε k 本身。
-- 此引理用于在完备性证明中拆分误差界。

ε-half< : ∀ k → ε k * half < ε k
ε-half< k =
  let
    a : ℚ
    a = ε k * half

    0<a : 0ℚ < a
    0<a = positive⁻¹ a
            {{pos*pos⇒pos (ε k) {{positive (0<ε k)}}
                          half {{positive 0<half}}}}

    a<a+a : a < a + a
    a<a+a = subst (λ z → z < a + a) (+-identityʳ a)
              (+-monoʳ-< a 0<a)

    a+a≡ : a + a ≡ ε k
    a+a≡ = two-half (ε k)
  in subst (λ z → a < z) a+a≡ a<a+a

------------------------------------------------------------------------
-- Cauchy condition for RealI sequences
--
-- A sequence of real intervals is Cauchy if there exists a modulus μ
-- such that beyond μ k, all intervals have width less than ε k / 2,
-- and their centres are mutually within ε k / 2.
--
-- RealI 序列的柯西条件
--
-- 一个实数区间序列是柯西的，当且仅当存在模函数 μ，使得对于所有
-- 超过 μ k 的项，其区间宽度小于 ε k / 2，且它们的中心点之间的
-- 距离也小于 ε k / 2。

CauchyI : (ℕ → RealI) → Set
CauchyI f = Σ (ℕ → ℕ) (λ μ →
              (∀ k → μ k ≥ k) ×
              (∀ k j → k ≤ℕ j → μ k ≤ℕ μ j) ×
              (∀ k → (∀ n → n ≥ μ k → width (f n) k < ε k * half) ×
                     (∀ n m → n ≥ μ k → m ≥ μ k →
                       ∣ centre (f n) n - centre (f m) m ∣ < ε k * half)))

------------------------------------------------------------------------
-- Converting a Cauchy RealI sequence to a CauchySeq
--
-- Extracts the centre values from a Cauchy interval sequence to form
-- a standard rational Cauchy sequence, using ε-half< to satisfy the
-- Cauchy condition with full ε tolerance.
--
-- 将柯西 RealI 序列转换为 CauchySeq
--
-- 从柯西区间序列中提取中心值以构成标准的有理数柯西序列，
-- 利用 ε-half< 确保满足完整 ε 容差下的柯西条件。

toCauchy : (f : ℕ → RealI) → CauchyI f → CauchySeq
toCauchy f cf = record
  { f      = λ n → centre (f n) n
  ; μ      = proj₁ cf
  ; cauchy = λ k n m n≥μ m≥μ →
      <-trans (proj₂ (proj₂ (proj₂ (proj₂ cf)) k) n m n≥μ m≥μ)
              (ε-half< k)
  }

------------------------------------------------------------------------
-- Limit construction
--
-- The limit of a Cauchy interval sequence is defined by first
-- converting it to a Cauchy sequence and then applying the
-- cauchy→realI construction.
--
-- 极限构造
--
-- 柯西区间序列的极限通过先将其转换为柯西序列，再应用
-- cauchy→realI 构造来定义。

lim : (f : ℕ → RealI) → CauchyI f → RealI
lim f cf = cauchy→realI (toCauchy f cf)

------------------------------------------------------------------------
-- Convergence
--
-- A sequence f converges to L if for every precision k, there exists
-- an index N such that for all n ≥ N, the centre of f n at precision k
-- is within ε k of the centre of L at precision k.
--
-- 收敛性
--
-- 序列 f 收敛于 L，当且仅当对每个精度 k，存在索引 N，使得对所有
-- n ≥ N，f n 在精度 k 处的中心与 L 在精度 k 处的中心之差小于 ε k。

_⟶_ : (ℕ → RealI) → RealI → Set
f ⟶ L = ∀ k → Σ ℕ (λ N → ∀ n → n ≥ N →
              ∣ centre (f n) k - centre L k ∣ < ε k)

------------------------------------------------------------------------
-- Completeness
--
-- Every Cauchy sequence of real intervals converges to its constructed
-- limit. The proof uses a triangle inequality argument splitting the
-- distance into: (1) approximation error within f n, and (2) Cauchy
-- closeness between f n and the limit representative f j.
--
-- 完备性
--
-- 每个实数区间的柯西序列都收敛于其构造的极限。证明使用三角不等式，
-- 将距离拆分为：(1) f n 内部的逼近误差；(2) f n 与极限代表元 f j
-- 之间的柯西接近程度。

complete : (f : ℕ → RealI) (cf : CauchyI f) → f ⟶ lim f cf
complete f cf k = N , proof
  where
    μ : ℕ → ℕ
    μ = proj₁ cf

    μ≥ : ∀ i → μ i ≥ i
    μ≥ = proj₁ (proj₂ cf)

    μ-mono : ∀ i j → i ≤ℕ j → μ i ≤ℕ μ j
    μ-mono = proj₁ (proj₂ (proj₂ cf))

    width-cond : ∀ i n → n ≥ μ i → width (f n) i < ε i * half
    width-cond i = proj₁ (proj₂ (proj₂ (proj₂ cf)) i)

    centre-cond : ∀ i n m → n ≥ μ i → m ≥ μ i →
                  ∣ centre (f n) n - centre (f m) m ∣ < ε i * half
    centre-cond i = proj₂ (proj₂ (proj₂ (proj₂ cf)) i)

    cs : CauchySeq
    cs = toCauchy f cf

    L : RealI
    L = cauchy→realI cs

    j : ℕ
    j = M cs k

    j≥μk : j ≥ μ k
    j≥μk = ≤ℕ-trans (μ-mono k (K k) (K≥k k))
                    (M≥μK cs k)

    centre-L : centre L k ≡ centre (f j) j
    centre-L = centre-cauchy→realI cs k

    N : ℕ
    N = μ k ⊔ j

    N≥μk : N ≥ μ k
    N≥μk = m≤m⊔n (μ k) j

    N≥j : N ≥ j
    N≥j = m≤n⊔m (μ k) j

    proof : ∀ n → n ≥ N → ∣ centre (f n) k - centre L k ∣ < ε k
    proof n n≥N =
      let
        n≥μk : n ≥ μ k
        n≥μk = ≤ℕ-trans N≥μk n≥N

        n≥j : n ≥ j
        n≥j = ≤ℕ-trans N≥j n≥N

        k≤j : k ≤ℕ j
        k≤j = ≤ℕ-trans (μ≥ k) j≥μk

        k≤n : k ≤ℕ n
        k≤n = ≤ℕ-trans k≤j n≥j

        tri1 : ∣ centre (f n) k - centre (f n) n ∣ ≤ width (f n) k
        tri1 = centre-diff (f n) k k n (≤ℕ-refl {k}) k≤n

        first : ∣ centre (f n) k - centre (f n) n ∣ < ε k * half
        first = ≤-<-trans tri1 (width-cond k n n≥μk)

        second : ∣ centre (f n) n - centre (f j) j ∣ < ε k * half
        second = centre-cond k n j n≥μk j≥μk

        tri : ∣ centre (f n) k - centre (f j) j ∣
              < ε k * half + ε k * half
        tri = ≤-<-trans
                (tri-diff (centre (f n) k) (centre (f n) n) (centre (f j) j))
                (+-mono-< first second)

        sum-eps : ε k * half + ε k * half ≡ ε k
        sum-eps = two-half (ε k)

        final : ∣ centre (f n) k - centre L k ∣ < ε k
        final = subst (λ z → ∣ centre (f n) k - z ∣ < ε k)
                      (sym centre-L)
                      (subst (λ z → ∣ centre (f n) k - centre (f j) j ∣ < z)
                             sum-eps
                             tri)
      in final
