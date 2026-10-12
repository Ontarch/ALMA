------------------------------------------------------------------------
-- Combinatorial GR skeleton: causal sets on a finite decidable order
--
-- A causal set is a locally finite set of events carrying a strict
-- causal order. Here an event set is Fin n and the order is a decidable
-- boolean relation _≺_. The metric and curvature are not supplied: they
-- are read off the order by counting chains.
--
--   * chains k            : total number of k-chains (k strictly ordered
--                           events).
--   * between k x y       : number of k-chains with least event x and
--                           greatest event y -- the chain content of the
--                           Alexandrov interval I(x, y).
--   * interior / interval-volume : the events z with x ≺ z ≺ y; the
--                           interval volume is two plus their count.
--   * curvatureAt         : a curvature functional as an explicit finite
--                           integer linear combination of the interval
--                           chain counts. The physical coefficients
--                           depend on spacetime dimension and the
--                           fundamental volume, so they are an argument
--                           rather than a claimed universal constant.
--
-- IsCausalOrder packages the irreflexivity and transitivity witnesses
-- that make _≺_ a strict partial order; counting itself needs only the
-- boolean relation and is computed by folding the finite list of
-- events, so no clause relies on Fin constructor injectivity.
--
-- The four-point diamond is worked as the flat reference: a minimal
-- 1+1 Alexandrov interval has two spacelike interior events, interval
-- volume four, and two three-chains.
--
-- 组合 GR 骨架：有限可判定序上的因果集
--
-- 因果集是携带严格因果序的局部有限事件集。此处事件集为 Fin n，序为可判
-- 定的布尔关系 _≺_。度规与曲率不被给定，而通过对链计数从序中读出。
--
--   * chains k            ：k-链（k 个严格排序事件）的总数。
--   * between k x y       ：以 x 为最小事件、y 为最大事件的 k-链数——
--                           Alexandrov 区间 I(x, y) 的链含量。
--   * interior / 区间体积 ：满足 x ≺ z ≺ y 的事件 z；区间体积为二加其内
--                           部点数。
--   * curvatureAt         ：曲率泛函，显式为区间链计数的有限整数线性组
--                           合。物理系数依赖时空维度与基本体积，故作为参
--                           数，而非冒称的普适常数。
--
-- IsCausalOrder 打包使 _≺_ 成为严格偏序的非自反性与传递性见证；计数本身
-- 只需布尔关系，通过折叠有限事件列表计算，故无子句依赖 Fin 构造子的单射
-- 性。
--
-- 四点菱形作为平坦参考：最小的 1+1 Alexandrov 区间有两个类空内部事件，区
-- 间体积为四，三链数为二。
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module ALMA.Physics.CausalSet where

open import Data.Nat using (ℕ; zero; suc)
  renaming (_+_ to _+ℕ_; _≡ᵇ_ to _≡ℕᵇ_)
open import Data.Fin using (Fin; toℕ)
open import Data.Bool using (Bool; true; false; T; _∧_; _∨_)
open import Data.Vec using (allFin; toList)
open import Data.List using (List; _∷_; [])
open import Data.Empty using (⊥)
open import Data.Unit using (⊤)
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
  -- Curvature functional: explicit integer linear combination of the
  -- interval chain counts, starting at one-chains.
  --
  -- 曲率泛函：区间链计数的显式整数线性组合，从一链起。

  weighted : List ℤ → ℕ → (ℕ → ℕ) → ℤ
  weighted [] k f = + 0
  weighted (c ∷ cs) k f = c * + (f k) + weighted cs (suc k) f

  curvatureAt : List ℤ → Fin n → Fin n → ℤ
  curvatureAt coeffs x y = weighted coeffs 1 (λ k → between k x y)

------------------------------------------------------------------------
-- Strict partial order witnesses
--
-- 严格偏序见证

record IsCausalSet (n : ℕ) (_≺_ : Fin n → Fin n → Bool) : Set where
  field
    irrefl : ∀ x → ¬ T (_≺_ x x)
    trans  : ∀ x y z → T (_≺_ x y) → T (_≺_ y z) → T (_≺_ x z)

------------------------------------------------------------------------
-- The four-point flat diamond as a concrete reference instance
--
-- 四点平坦菱形作为具体参考实例

diamond : Fin 4 → Fin 4 → Bool
diamond x y =
  let a = toℕ x; b = toℕ y in
  ((a ≡ℕᵇ 0) ∧ ((b ≡ℕᵇ 1) ∨ (b ≡ℕᵇ 2) ∨ (b ≡ℕᵇ 3)))
  ∨ (((a ≡ℕᵇ 1) ∨ (a ≡ℕᵇ 2)) ∧ (b ≡ℕᵇ 3))

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
