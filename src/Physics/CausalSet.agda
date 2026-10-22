------------------------------------------------------------------------
-- Combinatorial GR skeleton: causal sets on a finite decidable order
--
-- A causal set is a locally finite set of events carrying a strict
-- causal order. Here an event set is Fin n and the order is a decidable
-- boolean relation _≺_. The metric and curvature are not supplied: they
-- are read off the order by counting chains. The four-point diamond is
-- worked as the flat reference.
--
-- 组合 GR 骨架：有限可判定序上的因果集
--
-- 因果集是携带严格因果序的局部有限事件集。此处事件集为 Fin n，序为可
-- 判定的布尔关系 _≺_。度规与曲率不被给定，而通过对链计数从序中读出。
-- 四点菱形作为平坦参考。
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module Physics.CausalSet where

open import Data.Nat using (ℕ; zero; suc) renaming (_+_ to _+ℕ_; _≡ᵇ_ to _≡ℕᵇ_)
open import Data.Fin using (Fin; toℕ)
open import Data.Bool using (Bool; true; false; T; _∧_; _∨_)
open import Data.Vec using (allFin; toList)
open import Data.List using (List; _∷_; [])
open import Data.Integer using (ℤ; _+_; _*_; +_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

------------------------------------------------------------------------
-- Finite-list folding over a boolean predicate
--
-- 布尔谓词上的有限列表折叠

boolFilter : ∀ {a} {A : Set a} → (A → Bool) → List A → List A
boolFilter p [] = []
boolFilter p (x ∷ xs) with p x
... | true  = x ∷ boolFilter p xs
... | false = boolFilter p xs

sumOver : ∀ {a} {A : Set a} → List A → (A → ℕ) → ℕ
sumOver [] f = 0
sumOver (x ∷ xs) f = f x +ℕ sumOver xs f

------------------------------------------------------------------------
-- A causal set on n events with decidable strict order _≺_
--
-- n 个事件、可判定严格序 _≺_ 的因果集

module Core (n : ℕ) (_≺_ : Fin n → Fin n → Bool) where

  events : List (Fin n)
  events = toList (allFin n)

  succs : Fin n → List (Fin n)
  succs x = boolFilter (λ y → x ≺ y) events

  -- Total k-chains whose least event is x; g m counts chains of length
  -- 1 + m.
  --
  -- 以 x 为最小事件的 k-链总数；g m 计长度 1 + m 的链。
  chainsFrom : ℕ → Fin n → ℕ
  chainsFrom 0 x = 0
  chainsFrom (suc m) x = g m x
    where
    g : ℕ → Fin n → ℕ
    g 0 x = 1
    g (suc j) x = sumOver (succs x) (g j)

  chains : ℕ → ℕ
  chains k = sumOver events (chainsFrom k)

  -- k-chains from x to y (least x, greatest y).
  --
  -- 从 x 到 y 的 k-链（最小 x，最大 y）。
  between : ℕ → Fin n → Fin n → ℕ
  between 0 x y = 0
  between (suc m) x y = h m x
    where
    h : ℕ → Fin n → ℕ
    h 0 z with toℕ z ≡ℕᵇ toℕ y
    ... | true = 1
    ... | false = 0
    h (suc j) z = sumOver (succs z) (h j)

  -- Interior events of the Alexandrov interval I(x, y), and its volume.
  --
  -- Alexandrov 区间 I(x, y) 的内部事件及其体积。
  interior : Fin n → Fin n → List (Fin n)
  interior x y =
    boolFilter (λ z → (x ≺ z) ∧ (z ≺ y)) events

  interval-volume : Fin n → Fin n → ℕ
  interval-volume x y = 2 +ℕ sumOver (interior x y) (λ _ → 1)

  ----------------------------------------------------------------------
  -- Curvature functional
  --
  -- An explicit integer linear combination of the interval chain
  -- counts, starting at one-chains. The physical coefficients depend
  -- on spacetime dimension and the fundamental volume, so they are an
  -- argument rather than a claimed universal constant.
  --
  -- 曲率泛函
  --
  -- 区间链计数的显式整数线性组合，从一链起。物理系数依赖时空维度与基
  -- 本体积，故作为参数，而非冒称的普适常数。

  weighted : List ℤ → ℕ → (ℕ → ℕ) → ℤ
  weighted [] k f = + 0
  weighted (c ∷ cs) k f = c * + (f k) + weighted cs (suc k) f

  curvatureAt : List ℤ → Fin n → Fin n → ℤ
  curvatureAt coeffs x y = weighted coeffs 1 (λ k → between k x y)

------------------------------------------------------------------------
-- Strict partial order witnesses
--
-- IsCausalSet packages the irreflexivity and transitivity witnesses
-- that make _≺_ a strict partial order; counting itself needs only the
-- boolean relation and is computed by folding the finite list of
-- events, so no clause relies on Fin constructor injectivity.
--
-- 严格偏序见证
--
-- IsCausalSet 打包使 _≺_ 成为严格偏序的非自反性与传递性见证；计数本身
-- 只需布尔关系，通过折叠有限事件列表计算，故无子句依赖 Fin 构造子的单
-- 射性。

record IsCausalSet (n : ℕ) (_≺_ : Fin n → Fin n → Bool) : Set where
  field
    irrefl : ∀ x → ¬ T (_≺_ x x)
    trans  : ∀ x y z → T (_≺_ x y) → T (_≺_ y z) → T (_≺_ x z)

------------------------------------------------------------------------
-- The diamond order, defined on ℕ so that proofs never match Fin
-- constructors. The Fin-level diamond is the pullback along toℕ.
--
-- 菱形序定义在 ℕ 上，使证明绝不匹配 Fin 构造子。Fin 层的菱形是沿
-- toℕ 的拉回。

diamondℕ : ℕ → ℕ → Bool
diamondℕ a b =
  ((a ≡ℕᵇ 0) ∧ ((b ≡ℕᵇ 1) ∨ (b ≡ℕᵇ 2) ∨ (b ≡ℕᵇ 3)))
  ∨ (((a ≡ℕᵇ 1) ∨ (a ≡ℕᵇ 2)) ∧ (b ≡ℕᵇ 3))

diamond : Fin 4 → Fin 4 → Bool
diamond x y = diamondℕ (toℕ x) (toℕ y)

------------------------------------------------------------------------
-- The four-point flat diamond as a concrete reference instance
--
-- A minimal 1+1 Alexandrov interval has two spacelike interior events,
-- interval volume four, and two three-chains.
--
-- 四点平坦菱形作为具体参考实例
--
-- 最小的 1+1 Alexandrov 区间有两个类空内部事件，区间体积为四，三链数为
-- 二。

open Core 4 diamond

d0 : Fin 4
d0 = Data.Fin.zero

d3 : Fin 4
d3 = Data.Fin.fromℕ 3

diamond-C1 : chains 1 ≡ 4
diamond-C1 = refl

diamond-C2 : chains 2 ≡ 5
diamond-C2 = refl

diamond-C3 : chains 3 ≡ 2
diamond-C3 = refl

diamond-between3 : between 3 d0 d3 ≡ 2
diamond-between3 = refl

diamond-between4 : between 4 d0 d3 ≡ 0
diamond-between4 = refl

diamond-volume : interval-volume d0 d3 ≡ 4
diamond-volume = refl

------------------------------------------------------------------------
-- The four-point diamond is a causal set
--
-- 四点菱形是因果集

diamondℕ-irrefl : ∀ a → ¬ T (diamondℕ a a)
diamondℕ-irrefl zero                    = λ ()
diamondℕ-irrefl (suc zero)              = λ ()
diamondℕ-irrefl (suc (suc zero))        = λ ()
diamondℕ-irrefl (suc (suc (suc zero)))  = λ ()
diamondℕ-irrefl (suc (suc (suc (suc _)))) = λ ()

diamond-irrefl : ∀ x → ¬ T (diamond x x)
diamond-irrefl x = diamondℕ-irrefl (toℕ x)

diamond-trans : ∀ x y z → T (diamond x y) → T (diamond y z) → T (diamond x z)
diamond-trans x y z p q = trans-helper (toℕ x) (toℕ y) (toℕ z) p q
  where
    -- Case split on the three natural readings. The fourth argument
    -- inhabits T (diamondℕ a b) and the fifth inhabits T (diamondℕ b c);
    -- `()` in either position closes the empty cases.
    --
    -- 对三个自然读数分情况。第四参数栖居于 T (diamondℕ a b)，第五参数
    -- 栖居于 T (diamondℕ b c)；任一位置的 `()` 闭合空情形。
    trans-helper : ∀ a b c
                 → T (diamondℕ a b) → T (diamondℕ b c) → T (diamondℕ a c)
    -- Both premises hold: (0,1,3) and (0,2,3).
    --
    -- 两个前件都成立：(0,1,3) 与 (0,2,3)。
    trans-helper zero (suc zero) (suc (suc (suc zero))) _ _ = _
    trans-helper zero (suc (suc zero)) (suc (suc (suc zero))) _ _ = _
    -- First premise empty.
    --
    -- 第一前件为空。
    trans-helper zero zero _ () _
    trans-helper zero (suc zero) zero _ ()
    trans-helper zero (suc zero) (suc zero) _ ()
    trans-helper zero (suc zero) (suc (suc zero)) _ ()
    trans-helper zero (suc zero) (suc (suc (suc (suc _)))) _ ()
    trans-helper zero (suc (suc zero)) zero _ ()
    trans-helper zero (suc (suc zero)) (suc zero) _ ()
    trans-helper zero (suc (suc zero)) (suc (suc zero)) _ ()
    trans-helper zero (suc (suc zero)) (suc (suc (suc (suc _)))) _ ()
    trans-helper zero (suc (suc (suc zero))) _ _ ()
    trans-helper zero (suc (suc (suc (suc _)))) _ () _
    trans-helper (suc zero) zero _ () _
    trans-helper (suc zero) (suc zero) _ () _
    trans-helper (suc zero) (suc (suc zero)) _ () _
    trans-helper (suc zero) (suc (suc (suc zero))) _ _ ()
    trans-helper (suc zero) (suc (suc (suc (suc _)))) _ () _
    trans-helper (suc (suc zero)) zero _ () _
    trans-helper (suc (suc zero)) (suc zero) _ () _
    trans-helper (suc (suc zero)) (suc (suc zero)) _ () _
    trans-helper (suc (suc zero)) (suc (suc (suc zero))) _ _ ()
    trans-helper (suc (suc zero)) (suc (suc (suc (suc _)))) _ () _
    trans-helper (suc (suc (suc zero))) _ _ () _
    trans-helper (suc (suc (suc (suc _)))) _ _ () _

diamond-causal : IsCausalSet 4 diamond
diamond-causal = record
  { irrefl = diamond-irrefl
  ; trans  = diamond-trans
  }
