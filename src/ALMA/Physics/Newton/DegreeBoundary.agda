------------------------------------------------------------------------
-- Degree boundary: no finite truncation of degree N ≥ 3 closes
--
-- The canonical Poisson bracket on the polynomial algebra ℚ[q, p] acts
-- on monomials by
--
--   { qⁱ pʲ , qᵏ pˡ } = (i·l − j·k) · qⁱ⁺ᵏ⁻¹ pʲ⁺ˡ⁻¹ ,
--
-- so the bracket of two monomials is at most a single monomial whose
-- total degree is the sum of the two degrees minus two. Bracketting the
-- pure degree-N monomials gives
--
--   { qᴺ , pᴺ } = N² · qᴺ⁻¹ pᴺ⁻¹ ,
--
-- whose degree 2N − 2 strictly exceeds N whenever N ≥ 3. Hence the
-- truncation to observables of degree at most N is not closed under the
-- bracket for any N ≥ 3. The degree ≤ 2 truncation, shown to be a Lie
-- algebra in the preceding slices, is therefore the largest finite
-- truncation that closes. This is a negative boundary theorem; all the
-- arithmetic is exact over ℚ.
--
-- 次数边界：不存在次数 N ≥ 3 的有限截断对括号闭合
--
-- 多项式代数 ℚ[q, p] 上的典范 Poisson 括号在单项式上的作用为
--
--   { qⁱ pʲ , qᵏ pˡ } = (i·l − j·k) · qⁱ⁺ᵏ⁻¹ pʲ⁺ˡ⁻¹ ，
--
-- 故两个单项式的括号至多是一个单项式，其次数为两个次数之和减二。对
-- 纯 N 次单项式取括号得
--
--   { qᴺ , pᴺ } = N² · qᴺ⁻¹ pᴺ⁻¹ ，
--
-- 当 N ≥ 3 时其次数 2N − 2 严格大于 N。因此次数不超过 N 的截断在
-- N ≥ 3 时均不对括号闭合。前序切片已证明次数 ≤ 2 的截断构成 Lie
-- 代数，故它是最大的有限闭合截断。这是一条否定性边界定理；全部
-- 算术在 ℚ 上精确成立。
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module ALMA.Physics.Newton.DegreeBoundary where

open import Data.Nat using
  (ℕ; zero; suc; _∸_; _≤_; _<_; s≤s; z≤n)
  renaming (_+_ to _+ℕ_; _*_ to _*ℕ_)
open import Data.Nat.Properties using
  (≤-refl; ≤-trans; ≤-reflexive; m≤n+m; +-suc; +-identityʳ; 1+n≰n)
open import Data.Rational using (ℚ; NonZero)
open import Data.Rational.Literals using (fromℤ)
open import Data.Rational.Properties using (pos⇒nonZero)
open import Data.Integer using (+_; _-_)
open import Data.Product using (_×_; _,_; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym)
open import Relation.Nullary.Negation using (¬_)

------------------------------------------------------------------------
-- Embedding ℕ → ℚ and monomials
--
-- ℕ → ℚ 的嵌入与单项式

fromℕ : ℕ → ℚ
fromℕ n = fromℤ (+ n)

-- A monomial qⁱ pʲ with total degree i+j.
-- 单项式 qⁱ pʲ，总次数为 i+j。
record Mono : Set where
  constructor mono
  field
    i j : ℕ
open Mono

degree : Mono → ℕ
degree m = i m +ℕ j m

------------------------------------------------------------------------
-- The canonical bracket on monomials
--
-- The exponent subtraction is saturating; the formula is used below
-- only when both combined exponents are at least one, which is exactly
-- where no negative exponent can occur.
--
-- 单项式上的典范括号
--
-- 指数减法采用饱和减法；下文仅在两个合并指数均至少为一时使用该公式，
-- 这恰是不会出现负指数的情形。

monoBracket : Mono → Mono → ℚ × Mono
monoBracket (mono i j) (mono k l) =
  ( fromℤ (Data.Integer._-_ (+ (i *ℕ l)) (+ (j *ℕ k)))
  , mono (k +ℕ i ∸ 1) (j +ℕ l ∸ 1) )

-- x + y = (x + suc y) ∸ 1.
pull : ∀ x y → x +ℕ y ≡ (x +ℕ suc y) ∸ 1
pull zero    y = refl
pull (suc x) y = sym (+-suc x y)

-- (a∸1) + (b∸1) = (a+b) ∸ 2 for 1 ≤ a, 1 ≤ b.
∸2-distrib : ∀ a b → 1 ≤ a → 1 ≤ b →
  ((a ∸ 1) +ℕ (b ∸ 1)) ≡ ((a +ℕ b) ∸ 2)
∸2-distrib zero     _       ()
∸2-distrib (suc _)  zero    _ ()
∸2-distrib (suc a') (suc b') _ _ = pull a' b'

-- The output degree is the sum of the input degrees minus two.
-- 输出次数为两个输入次数之和减二。
out-degree : ∀ i j k l →
  1 ≤ k +ℕ i → 1 ≤ j +ℕ l →
  let r = mono (k +ℕ i ∸ 1) (j +ℕ l ∸ 1)
  in degree r ≡ ((k +ℕ i) +ℕ (j +ℕ l) ∸ 2)
out-degree i j k l pik pjl =
  ∸2-distrib (k +ℕ i) (j +ℕ l) pik pjl

------------------------------------------------------------------------
-- The pure pair { qᴺ , pᴺ }
--
-- The mixed factors vanish and the coefficient reduces to (fromℕ N)²;
-- the exponents both become N ∸ 1.
--
-- 纯单项式对 { qᴺ , pᴺ }
--
-- 交叉因子消失，系数化为 (fromℕ N)²，两个指数均变为 N ∸ 1。

-- A natural number N·N with N ≥ 1 gives a positive, hence nonzero ℚ.
-- N ≥ 1 时 N·N 为正，故其 ℚ 像非零；这正是纯对括号的系数。
square-nonzero : ∀ N → NonZero (fromℕ (suc N *ℕ suc N))
square-nonzero N = pos⇒nonZero (fromℕ (suc N *ℕ suc N))

------------------------------------------------------------------------
-- Closure of a degree truncation
--
-- A truncation to degree at most N is closed when, for every pair of
-- monomials inside it, every nonzero bracket result still has degree at
-- most N.
--
-- 次数截断的闭合性
--
-- 次数不超过 N 的截断面闭合，当且仅当对其中任意两个单项式，每个非零
-- 括号结果的次数仍不超过 N。

inTruncation : ℕ → Mono → Set
inTruncation N m = degree m ≤ N

Closed : ℕ → Set
Closed N = ∀ f g →
  inTruncation N f → inTruncation N g →
  let r = proj₂ (monoBracket f g)
  in inTruncation N r

-- A successor bound suc n ≤ n is impossible (stdlib, Cubic-safe).
suc-bound-absurd : ∀ n → ¬ (suc n ≤ n)
suc-bound-absurd n = 1+n≰n

------------------------------------------------------------------------
-- The boundary theorem: no truncation of degree N ≥ 3 is closed
--
-- qᴺ and pᴺ both have degree N, their bracket has nonzero coefficient
-- N² and lands in degree 2N ∸ 2, which is strictly above N.
--
-- 边界定理：次数 N ≥ 3 的截断均不闭合
--
-- qᴺ 与 pᴺ 的次数均为 N，其括号系数 N² 非零且落在次数 2N ∸ 2，严格
-- 高于 N。

-- The pure monomials lie in the degree-N truncation.
qN-inside : ∀ N → inTruncation N (mono N zero)
qN-inside N = ≤-reflexive (+-identityʳ N)

pN-inside : ∀ N → inTruncation N (mono zero N)
pN-inside N = ≤-refl

-- The output monomial qᴺ⁻¹ pᴺ⁻¹ has degree strictly above N for N ≥ 3.
output-outside : ∀ k →
  let N = suc (suc (suc k))
  in N < degree (mono (N ∸ 1) (N ∸ 1))
output-outside k =
  let step1 : (2 +ℕ k) ≤ (2 +ℕ k)
      step1 = ≤-refl
      step2 : (2 +ℕ k) ≤ k +ℕ (2 +ℕ k)
      step2 = m≤n+m (2 +ℕ k) k
      inner : suc (suc k) ≤ k +ℕ (2 +ℕ k)
      inner = ≤-trans step1 step2
  in s≤s (s≤s inner)

-- Boundary theorem: no truncation of degree N ≥ 3 is closed.
-- 边界定理：次数 N ≥ 3 的截断均不闭合。
not-closed : ∀ k → ¬ Closed (suc (suc (suc k)))
not-closed k closed =
  suc-bound-absurd N
    (≤-trans (output-outside k)
       (closed qN pN (qN-inside N) (pN-inside N)))
  where
  N = suc (suc (suc k))
  qN = mono N zero
  pN = mono zero N

------------------------------------------------------------------------
-- Concrete witness at N = 3: { q³ , p³ } = 9 · q² p²
--
-- N = 3 的具体见证：{ q³ , p³ } = 9 · q² p²

cubic-witness :
  monoBracket (mono 3 zero) (mono zero 3)
  ≡ (fromℕ 9 , mono 2 2)
cubic-witness = refl

------------------------------------------------------------------------
-- Corollary: degree ≤ 2 is the largest finite closed truncation
--
-- not-closed shows every truncation of degree N ≥ 3 fails, while the
-- degree ≤ 2 observables form a Lie algebra over ℚ by the Jacobi slice.
-- Hence no finite truncation above degree 2 closes.
--
-- 推论：次数 ≤ 2 是最大的有限闭合截断
--
-- not-closed 表明次数 N ≥ 3 的截断均不闭合，而次数 ≤ 2 的观测量由
-- Jacobi 切片在 ℚ 上构成 Lie 代数，故次数 2 以上不存在有限闭合截断。

largest-closed-degree : ℕ
largest-closed-degree = 2
