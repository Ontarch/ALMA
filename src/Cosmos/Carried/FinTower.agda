------------------------------------------------------------------------
-- Zero-subst colimit of a tower of finite endofunctions
--
-- A tower is a family f m : Fin (n-at m) → Fin (n-at m) together with
-- the one-step coherence
--   toℕ (f (suc m) (inject₁ x)) ≡ toℕ (f m x).
-- The colimit is a FinCone over ℕ: at m x = toℕ (f m x), compat is the
-- supplied coherence, and FinCone derives at-cl / g∞ / extends / unique
-- with zero subst. The canonical reading g∞ k = toℕ (f k (natToFin k))
-- is the F₀ of the tower colimit, and unique is its Set-level universal
-- property.
--
-- 有限自函数塔的零 subst 余极限
--
-- 一个塔即一族 f m : Fin (n-at m) → Fin (n-at m)，附带一步相干性
--   toℕ (f (suc m) (inject₁ x)) ≡ toℕ (f m x)。
-- 余极限是 ℕ 上的一个 FinCone：at m x = toℕ (f m x)，compat 即所给
-- 相干性，FinCone 零 subst 地派生出 at-cl / g∞ / extends / unique。
-- 典范读数 g∞ k = toℕ (f k (natToFin k)) 即塔余极限的 F₀，unique 即
-- 其集合层泛性质。
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module Cosmos.Carried.FinTower where

open import Agda.Builtin.Equality using (_≡_)
open import Data.Nat using (ℕ; suc)
open import Data.Fin.Base using (Fin; toℕ; inject₁)

open import Cosmos.Carried.LimitSystem using (n-at)
open import Cosmos.Carried.FinColimit using (FinCone)

------------------------------------------------------------------------
-- The cone of a tower of finite endofunctions
--
-- 有限自函数塔的锥

finTowerCone
  : (f : ∀ m → Fin (n-at m) → Fin (n-at m))
  → (embed-compat : ∀ m (x : Fin (n-at m))
       → toℕ (f (suc m) (inject₁ x)) ≡ toℕ (f m x))
  → FinCone ℕ
finTowerCone f embed-compat = record
  { at     = λ m x → toℕ (f m x)
  ; compat = embed-compat
  }

------------------------------------------------------------------------
-- Convenience wrapper
--
-- Opens the full cone surface (at-cl, g∞, extends, unique) for a given
-- tower.
--
-- 便捷包装
--
-- 为给定塔打开完整锥表面（at-cl、g∞、extends、unique）。

module FinTower
  (f : ∀ m → Fin (n-at m) → Fin (n-at m))
  (embed-compat : ∀ m (x : Fin (n-at m))
       → toℕ (f (suc m) (inject₁ x)) ≡ toℕ (f m x))
  where

  cone : FinCone ℕ
  cone = finTowerCone f embed-compat

  open FinCone cone public
    using (at; compat; compat-emb; at-cl; g∞; extends; unique)
