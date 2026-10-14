------------------------------------------------------------------------
-- Coinductive reals as a neighbourhood tree
--
-- Instantiate the general E-M skeleton (ALMA.Base.MCorr.M) over the
-- index set I = ℚ × ℕ (current rational centre plus precision level),
-- with A _ = ⊤ and
--
--   E (x , k) _ (y , k') = k' ≡ suc k × |y - x| < δ k ,
--
-- where δ k = 1 / 2^(k+1) is a summable dyadic tolerance. A point of
-- this tree rooted at a rational starting centre is a coinductive
-- nested sequence of rational centres converging to a real; this is
-- the coinductive reals, a third representation of ℝ alongside Cauchy
-- and Dedekind. The tolerance is summable because the nested centres
-- are related step by step by δ, so the total displacement Σ δ must be
-- finite (geometric) for convergence. The native E-M bisimulation
-- identifies trees with pointwise-equal nested centres; the limit-level
-- identification of two different nested sequences converging to the
-- same real is a metric notion, constructed separately.
--
-- 余归纳实数作为邻域树
--
-- 将通用 E-M 骨架（ALMA.Base.MCorr.M）实例化于索引集 I = ℚ × ℕ
-- （当前有理中心加精度层），A _ = ⊤，且
--
--   E (x , k) _ (y , k') = k' ≡ suc k × |y - x| < δ k ，
--
-- 其中 δ k = 1 / 2^(k+1) 为可求和二进容差。此树以某有理起点为根的
-- 一点，是收敛到某实数的余归纳嵌套有理中心序列；这是余归纳实数，
-- 与 Cauchy、Dedekind 并列的第三种 ℝ 表示。容差须可求和，因为嵌套
-- 中心逐步由 δ 关联，故总位移 Σ δ 必须有限（几何级数）才能收敛。
-- E-M 原生互模拟识别嵌套中心逐点重合的树；两条收敛到同一实数的不同
-- 嵌套序列的极限级识别是度量概念，另行构造。
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module ALMA.Base.Real.Neighborhood where

open import Data.Nat using (ℕ; suc; _^_)
open import Data.Integer using (+_)
open import Data.Rational using (ℚ; 0ℚ; ∣_∣; _-_; _<_; Positive)
open import Data.Rational.Base using (mkℚ; 1/_)
open import Data.Nat.Coprimality using (1-coprimeTo) renaming (sym to coprime-sym)
open import Data.Rational.Properties using (mkℚ+-pos; pos⇒nonZero; positive⁻¹; 1/pos⇒pos)
open import Data.Product using (Σ; _,_; _×_)
open import Data.Unit.Polymorphic using (⊤; tt)
open import Data.Nat.Properties using (m^n≢0)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

open import ALMA.Base.MCorr using (M; here; below)

-- Raw ℕ embedding so the reciprocal reduces definitionally.
--
-- 底层 ℕ 嵌入，使倒数定义性归约。
embed : ℕ → ℚ
embed n = mkℚ (+ n) 0 (coprime-sym (1-coprimeTo n))

-- Positive witness for the dyadic denominator.
--
-- 二进分母的正性见证。
pos-pow : ∀ k → Positive (embed (2 ^ suc k))
pos-pow k =
  mkℚ+-pos (2 ^ suc k) 1
    {{m^n≢0 2 (suc k)}}
    {c = coprime-sym (1-coprimeTo (2 ^ suc k))}

-- Summable dyadic tolerance δ k = 1 / 2^(k+1).
--
-- 可求和二进容差 δ k = 1 / 2^(k+1)。
δ : ℕ → ℚ
δ k =
  Data.Rational.Base.1/_ (embed (2 ^ suc k))
    {{pos⇒nonZero (embed (2 ^ suc k)) {{pos-pow k}}}}

-- δ k is positive.
--
-- δ k 为正。
δ-pos : ∀ k → 0ℚ < δ k
δ-pos k =
  positive⁻¹ (δ k)
    {{1/pos⇒pos (embed (2 ^ suc k)) {{pos-pow k}}}}

-- Index: current rational centre and precision level.
--
-- 索引：当前有理中心与精度层。
I : Set
I = ℚ × ℕ

A : I → Set
A _ = ⊤

-- Neighbourhood edge: next level carries any centre within δ k.
--
-- 邻域边：下一层携带任何在 δ k 内的中心。
E : (i : I) (a : A i) (j : I) → Set
E (x , k) _ (y , k') = k' ≡ suc k × ∣ y - x ∣ < δ k

-- A coinductive real is a point of the neighbourhood tree rooted at a
-- rational starting centre.
--
-- 余归纳实数是以某有理起点为根的邻域树的一点。
RealC : Set
RealC = Σ ℚ λ x → M A E (x , 0)

-- Total nested tree rooted at (q, k): at the next level, whichever
-- centre y is chosen within δ k, the subtree stays at y. The branch
-- y = q gives the constant nested centres equal q.
--
-- 以 (q, k) 为根的全嵌套树：下一层无论选 δ k 内哪个中心 y，子树都
-- 停在 y。分支 y = q 给出常嵌套中心等于 q。
const-tree : (q : ℚ) (k : ℕ) → M A E (q , k)
const-tree q k .here = tt
const-tree q k .below (y , .(suc k)) (refl , _) =
  const-tree y (suc k)

-- Embed a rational as a coinductive real.
--
-- 将有理数嵌入为余归纳实数。
embedℚ : ℚ → RealC
embedℚ q = q , const-tree q 0
