------------------------------------------------------------------------
-- Degeneration at Obs = ⊤
--
-- ScaleInvariant at Obs = ⊤. The non-trivial theory on this position
-- is Coalgebra, obtained by adding x ≡ y as base case. The module
-- contains Iteration and Coalgebra.
--
-- 退化到 Obs = ⊤
--
-- Obs = ⊤ 处的 ScaleInvariant。该位置上的非平凡理论是 Coalgebra，
-- 由加上 base case x ≡ y 得到。模块包含 Iteration 与 Coalgebra。
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module Equivalence.LinearDynamics where

open import Agda.Primitive using (lzero)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Sigma using (Σ; _,_)
open import Data.Unit.Polymorphic.Base using (⊤; tt)
open import Data.Nat.Base using (ℕ; zero; suc; _+_; _≤_; z≤n; s≤s; _<_)
open import Data.Nat.Properties using (+-comm; +-identityʳ; +-suc)
open import Data.Product.Base using (proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality.Core using (sym; trans; cong)
open import Relation.Binary.Structures using (IsEquivalence)
open import Relation.Binary.PropositionalEquality.Properties using (module ≡-Reasoning)
open ≡-Reasoning

open import Base.IndexedMType using (snd)
open import Equivalence.ScaleInvariant using (ScaleInvariant)

------------------------------------------------------------------------
-- Alias
--
-- ScaleInvariant's universe depends only on Obs, not on X.
--
-- 别名
--
-- ScaleInvariant 的 universe 只依赖 Obs，不依赖 X。

LinearDynamics : {a : _} {X : Set a} → (f : X → X) → X → X → Set lzero
LinearDynamics {a} {X} f = ScaleInvariant {Obs = ⊤ {lzero}} (λ x _ → f x)

------------------------------------------------------------------------
-- Iteration
--
-- The free monoid action of ℕ on X induced by f.
--
-- 迭代
--
-- 由 f 诱导的 ℕ 在 X 上的自由幺半群作用。

module Iteration
    {a : _} {X : Set a}
    (f : X → X) where

  _^[_] : X → ℕ → X
  x ^[ zero ]  = x
  x ^[ suc n ] = f (x ^[ n ])

  ^-zero : ∀ x → x ^[ 0 ] ≡ x
  ^-zero x = refl

  ^-suc : ∀ x n → x ^[ suc n ] ≡ f (x ^[ n ])
  ^-suc x n = refl

  -- Bridges the two syntactic forms x ^[ suc n ] and (f x) ^[ n ].
  --
  -- 桥接两种语法形式 x ^[ suc n ] 与 (f x) ^[ n ]。
  ^-suc-shift : ∀ x n → x ^[ suc n ] ≡ (f x) ^[ n ]
  ^-suc-shift x zero    = refl
  ^-suc-shift x (suc n) = cong f (^-suc-shift x n)

  ^-+ : ∀ x m n → x ^[ m + n ] ≡ (x ^[ m ]) ^[ n ]
  ^-+ x m zero    = cong (λ k → x ^[ k ]) (+-identityʳ m)
  ^-+ x m (suc n) = begin
    x ^[ m + suc n ]
      ≡⟨ cong (λ k → x ^[ k ]) (+-suc m n) ⟩
    x ^[ suc (m + n) ]
      ≡⟨ refl ⟩
    f (x ^[ m + n ])
      ≡⟨ cong f (^-+ x m n) ⟩
    f ((x ^[ m ]) ^[ n ])
      ≡⟨ refl ⟩
    (x ^[ m ]) ^[ suc n ]
      ∎

------------------------------------------------------------------------
-- Coalgebra
--
-- The final coalgebra equality of f.
--
-- Coalgebra
--
-- f 的最终 coalgebra 相等。

module Coalgebra
    {a : _} {X : Set a}
    (f : X → X) where

  open Iteration f

  -- Sync x y iff all iterates agree.
  --
  -- Sync x y 当且仅当所有迭代一致。
  Sync : X → X → Set a
  Sync x y = ∀ n → x ^[ n ] ≡ y ^[ n ]

  sync-isEquivalence : IsEquivalence Sync
  sync-isEquivalence = record
    { refl  = λ {x} n → refl
    ; sym   = λ p n → sym (p n)
    ; trans = λ p q n → trans (p n) (q n)
    }

  -- Coinductive characterisation; ^-suc-shift converts between
  -- x ^[ suc n ] and (f x) ^[ n ].
  --
  -- 余归纳刻画；^-suc-shift 在 x ^[ suc n ] 与 (f x) ^[ n ] 之间转换。
  sync-char : ∀ {x y} → Sync x y → (x ≡ y) × Sync (f x) (f y)
  sync-char {x} {y} p =
    p 0 ,
    (λ n → begin
      (f x) ^[ n ]
        ≡⟨ sym (^-suc-shift x n) ⟩
      x ^[ suc n ]
        ≡⟨ p (suc n) ⟩
      y ^[ suc n ]
        ≡⟨ ^-suc-shift y n ⟩
      (f y) ^[ n ]
        ∎)

  sync-intro : ∀ {x y} → x ≡ y → Sync (f x) (f y) → Sync x y
  sync-intro {x} {y} refl q zero    = refl
  sync-intro {x} {y} refl q (suc n) = begin
    x ^[ suc n ]
      ≡⟨ ^-suc-shift x n ⟩
    (f x) ^[ n ]
      ≡⟨ q n ⟩
    (f y) ^[ n ]
      ≡⟨ sym (^-suc-shift y n) ⟩
    y ^[ suc n ]
      ∎

  -- Sync is the largest relation R with
  -- R x y → x ≡ y × R (f x) (f y).
  --
  -- Sync 是满足 R x y → x ≡ y × R (f x) (f y) 的最大关系 R。
  sync-final
    : (R : X → X → Set a)
    → (∀ {x y} → R x y → (x ≡ y) × R (f x) (f y))
    → ∀ {x y} → R x y → Sync x y
  sync-final R step {x} {y} r zero    = proj₁ (step r)
  sync-final R step {x} {y} r (suc n) = begin
    x ^[ suc n ]
      ≡⟨ ^-suc-shift x n ⟩
    (f x) ^[ n ]
      ≡⟨ sync-final R step (proj₂ (step r)) n ⟩
    (f y) ^[ n ]
      ≡⟨ sym (^-suc-shift y n) ⟩
    y ^[ suc n ]
      ∎

  sync-refl : ∀ x → Sync x x
  sync-refl x = IsEquivalence.refl sync-isEquivalence

  -- Fixed points of f
  --
  -- f 的不动点
  IsFixed : X → Set a
  IsFixed x = f x ≡ x

  -- Periodic points: return to themselves after some positive number
  -- of iterations.
  --
  -- 周期点：经过某个正数次迭代后回到自身。
  IsPeriodic : X → Set a
  IsPeriodic x = Σ ℕ (λ n → Σ (0 < n) (λ _ → x ^[ n ] ≡ x))

  fixed→periodic : ∀ {x} → IsFixed x → IsPeriodic x
  fixed→periodic {x} fx = 1 , (s≤s z≤n , fx)

  -- If x has period p, every iterate x^[k] has period p.
  --
  -- 若 x 的周期为 p，则每个迭代 x^[k] 的周期也是 p。
  periodic-stable
    : ∀ {x} → IsPeriodic x
    → Σ ℕ (λ p → Σ (0 < p) (λ _ → ∀ k → (x ^[ k ]) ^[ p ] ≡ x ^[ k ]))
  periodic-stable {x} (p , 0<p , eq) = p , 0<p , period-iter
    where
      period-iter : ∀ k → (x ^[ k ]) ^[ p ] ≡ x ^[ k ]
      period-iter k = begin
        (x ^[ k ]) ^[ p ]
          ≡⟨ sym (^-+ x k p) ⟩
        x ^[ k + p ]
          ≡⟨ cong (λ j → x ^[ j ]) (+-comm k p) ⟩
        x ^[ p + k ]
          ≡⟨ ^-+ x p k ⟩
        (x ^[ p ]) ^[ k ]
          ≡⟨ cong (λ z → z ^[ k ]) eq ⟩
        x ^[ k ]
          ∎

  periodic-iterate
    : ∀ {x} → IsPeriodic x
    → Σ ℕ (λ p → Σ (0 < p) (λ _ → ∀ n → x ^[ n + p ] ≡ x ^[ n ]))
  periodic-iterate {x} per with periodic-stable {x} per
  ... | p , 0<p , iter = p , 0<p , period-law
    where
      period-law : ∀ n → x ^[ n + p ] ≡ x ^[ n ]
      period-law n = begin
        x ^[ n + p ]
          ≡⟨ ^-+ x n p ⟩
        (x ^[ n ]) ^[ p ]
          ≡⟨ iter n ⟩
        x ^[ n ]
        ∎

------------------------------------------------------------------------
-- Truncation
--
-- No layer condition, so every depth is trivially inhabited; the flat
-- truncation at the empty observation limit.
--
-- 截断
--
-- 无 layer 条件，每个深度都平凡可居；这是空观察极限处的平坦截断。

module LinearDynamics-Depth
    {a : _} {X : Set a} {f : X → X} where

  LD-depth : (n : ℕ) → (x y : X) → Set lzero
  LD-depth zero    x y = ⊤ {lzero}
  LD-depth (suc n) x y = LD-depth n (f x) (f y)

  ld→LD-depth : ∀ {x y} → LinearDynamics f x y
              → ∀ n → LD-depth n x y
  ld→LD-depth p zero    = tt
  ld→LD-depth p (suc n) = ld→LD-depth (p .snd tt) n

  LD-depth-mono : ∀ {m n} (m≤n : m ≤ n) {x y : X}
                → LD-depth n x y → LD-depth m x y
  LD-depth-mono z≤n       p = tt
  LD-depth-mono (s≤s m≤n) {x} {y} p =
    LD-depth-mono m≤n {x = f x} {y = f y} p
