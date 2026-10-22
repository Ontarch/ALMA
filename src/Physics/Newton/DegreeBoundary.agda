------------------------------------------------------------------------
-- Degree boundary: no finite truncation of degree N ≥ 3 closes
--
-- The bracket of two monomials is at most a single monomial whose total
-- degree is the sum of the two degrees minus two; bracketing two pure
-- degree-N monomials therefore lands in degree 2N − 2 > N for N ≥ 3.
-- Hence the degree ≤ 2 truncation, shown to be a Lie algebra in the
-- preceding slices, is the largest finite truncation that closes.
--
-- 次数边界：不存在次数 N ≥ 3 的有限截断对括号闭合
--
-- 两个单项式的括号至多是一个单项式，其次数为两个次数之和减二；故对
-- 两个纯 N 次单项式取括号落在次数 2N − 2 > N 处（N ≥ 3）。因此次数
-- ≤ 2 的截断——前序切片已证其为 Lie 代数——是最大的有限闭合截断。
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module Physics.Newton.DegreeBoundary where

open import Data.Bool.Base using (if_then_else_)
open import Data.Nat using
  (ℕ; zero; suc; _∸_; _≤_; _<_; _≤ᵇ_; s≤s) renaming (_+_ to _+ℕ_; _*_ to _*ℕ_)
open import Data.Nat.Properties using
  (≤-refl; ≤-trans; ≤-reflexive; m≤n+m; +-suc; +-identityʳ; 1+n≰n)
import Data.Nat.Coprimality as Cop
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)
open import Data.Rational using (ℚ; NonZero; -_)
open import Data.Rational.Base using (mkℚ+)
open import Data.Rational.Properties using (mkℚ+-pos; pos⇒nonZero)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym)
open import Relation.Nullary.Negation using (¬_)

------------------------------------------------------------------------
-- Embedding ℕ → ℚ
--
-- Uses mkℚ+ directly, so mkℚ+-pos applies without any gcd reduction.
--
-- ℕ → ℚ 的嵌入
--
-- 直接用 mkℚ+ 构造，使 mkℚ+-pos 无需任何 gcd 归约即可适用。

fromℕ : ℕ → ℚ
fromℕ n = mkℚ+ n 1 (Cop.sym (Cop.1-coprimeTo n))

-- ℚ-image of a natural-number difference, taken in the direction that
-- keeps the numerator nonnegative.
--
-- 自然数差的 ℚ 像，方向取使分子非负的一侧。

diff : (a b : ℕ) → ℚ
diff a b = if a ≤ᵇ b then - fromℕ (b ∸ a) else fromℕ (a ∸ b)

------------------------------------------------------------------------
-- A monomial qⁱ pʲ with total degree i+j.
--
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
-- Gives the bracket of two monomials; the exponent subtraction is
-- saturating, and the formula is used below only when both combined
-- exponents are at least one, exactly where no negative exponent can
-- occur.
--
-- 单项式上的典范括号
--
-- 给出两个单项式的括号；指数减法采用饱和减法，下文仅在两个合并指数
-- 均至少为一时使用该公式，这恰是不会出现负指数的情形。

monoBracket : Mono → Mono → ℚ × Mono
monoBracket (mono i j) (mono k l) =
  ( diff (i *ℕ l) (j *ℕ k)
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
--
-- 输出次数为两个输入次数之和减二。
out-degree : ∀ i j k l
           → 1 ≤ k +ℕ i → 1 ≤ j +ℕ l
           → degree (mono (k +ℕ i ∸ 1) (j +ℕ l ∸ 1))
             ≡ ((k +ℕ i) +ℕ (j +ℕ l) ∸ 2)
out-degree i j k l pik pjl =
  ∸2-distrib (k +ℕ i) (j +ℕ l) pik pjl

------------------------------------------------------------------------
-- Closure of a degree truncation
--
-- Defines when a truncation to degree at most N is closed under the
-- bracket.
--
-- 次数截断的闭合性
--
-- 定义次数不超过 N 的截断何时对括号闭合。

inTruncation : ℕ → Mono → Set
inTruncation N m = degree m ≤ N

Closed : ℕ → Set
Closed N = ∀ f g →
  inTruncation N f → inTruncation N g →
  let r = proj₂ (monoBracket f g)
  in inTruncation N r

-- A successor bound suc n ≤ n is impossible (stdlib, Cubical-safe).
--
-- 后继界 suc n ≤ n 不可能（stdlib，Cubical 安全）。
suc-bound-absurd : ∀ n → ¬ (suc n ≤ n)
suc-bound-absurd n = 1+n≰n

------------------------------------------------------------------------
-- The boundary theorem
--
-- Constructs the counterexample witnessing non-closure: the pure
-- monomials qᴺ and pᴺ lie inside the truncation, and their bracket
-- falls outside it.
--
-- 边界定理
--
-- 构造见证不闭合的反例：纯单项式 qᴺ 与 pᴺ 落在截断内，其括号落在
-- 截断外。

-- The pure monomials lie in the degree-N truncation.
--
-- 纯单项式落在 N 次截断内。
qN-inside : ∀ N → inTruncation N (mono N zero)
qN-inside N = ≤-reflexive (+-identityʳ N)

pN-inside : ∀ N → inTruncation N (mono zero N)
pN-inside N = ≤-refl

-- The output monomial qᴺ⁻¹ pᴺ⁻¹ has degree strictly above N for N ≥ 3.
--
-- 对 N ≥ 3，输出单项式 qᴺ⁻¹ pᴺ⁻¹ 的次数严格高于 N。
output-outside : ∀ k →
  let N = suc (suc (suc k))
  in N < degree (mono (N ∸ 1) (N ∸ 1))
output-outside k = s≤s (s≤s inner)
  where
  inner : suc (suc k) ≤ k +ℕ (2 +ℕ k)
  inner = ≤-trans ≤-refl (m≤n+m (2 +ℕ k) k)

-- Boundary theorem: no truncation of degree N ≥ 3 is closed.
--
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
-- Nonzero coefficient of the pure pair
--
-- The bracket coefficient of { qᴺ , pᴺ } is N², which is positive for
-- N ≥ 1; the counterexample is therefore not the zero polynomial. The
-- coefficient reduces to fromℕ (suc N *ℕ suc N) because zero *ℕ suc N
-- = zero and the Boolean test (suc N *ℕ suc N) ≤ᵇ zero returns false,
-- so diff picks the `fromℕ (a ∸ b)` branch. Positivity comes from
-- mkℚ+-pos.
--
-- 纯对括号的非零系数
--
-- { qᴺ , pᴺ } 的括号系数是 N²，对 N ≥ 1 为正；故反例不是零多项式。
-- 系数归约为 fromℕ (suc N *ℕ suc N)：因为 zero *ℕ suc N = zero 且
-- 布尔测试 (suc N *ℕ suc N) ≤ᵇ zero 返回 false，diff 走
-- `fromℕ (a ∸ b)` 分支。正性由 mkℚ+-pos 给出。

pure-coeff-nonzero : ∀ N → NonZero
  (proj₁ (monoBracket (mono (suc N) zero) (mono zero (suc N))))
pure-coeff-nonzero N =
  pos⇒nonZero (fromℕ (suc N *ℕ suc N))
    {{ mkℚ+-pos (suc N *ℕ suc N) 1
                 {c = Cop.sym (Cop.1-coprimeTo (suc N *ℕ suc N))} }}

------------------------------------------------------------------------
-- The strengthened boundary theorem
--
-- The strengthened closure predicate asks only that nonzero brackets
-- stay inside the truncation. The pure pair qᴺ, pᴺ still falls outside
-- it: its bracket has nonzero coefficient N², and its degree 2N − 2
-- exceeds N.
--
-- 加强版边界定理
--
-- 加强版闭合谓词只要求非零括号结果留在截断内。纯对 qᴺ、pᴺ 仍落在
-- 截断外：其括号系数 N² 非零，度数 2N − 2 超过 N。

Closed-Nonzero : ℕ → Set
Closed-Nonzero N = ∀ f g
  → inTruncation N f → inTruncation N g
  → NonZero (proj₁ (monoBracket f g))
  → inTruncation N (proj₂ (monoBracket f g))

not-closed-nonzero : ∀ k → ¬ Closed-Nonzero (suc (suc (suc k)))
not-closed-nonzero k cn =
  suc-bound-absurd N
    (≤-trans (output-outside k)
       (cn qN pN (qN-inside N) (pN-inside N)
           (pure-coeff-nonzero (suc (suc k)))))
  where
  N = suc (suc (suc k))
  qN = mono N zero
  pN = mono zero N

------------------------------------------------------------------------
-- Concrete witness at N = 3
--
-- Evaluates the bracket of q³ and p³ explicitly.
--
-- N = 3 的具体见证
--
-- 显式计算 q³ 与 p³ 的括号。

cubic-witness :
  monoBracket (mono 3 zero) (mono zero 3)
  ≡ (fromℕ 9 , mono 2 2)
cubic-witness = refl

------------------------------------------------------------------------
-- Corollary
--
-- Records the numerical value of the largest closed degree; the
-- argument is in the module header together with the Jacobi slice.
--
-- 推论
--
-- 记录最大闭合次数的数值；论证见模块头与 Jacobi 切片。

largest-closed-degree : ℕ
largest-closed-degree = 2
