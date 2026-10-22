------------------------------------------------------------------------
-- Lambek's lemma for the terminal M-Cosmos, up to bisimulation
--
-- In M the self-reference is native (no separate Unfolding seed type):
-- the structure map is the observation coalgebra unfold-coalgebra
-- (label = M.here, child = step), and its inverse is simply ana of that
-- observation coalgebra. The two round-trips are therefore exactly the
-- eta pair already established in Cosmos/M/Object:
--   in-F ∘ out ≈ id   :=   ana-unfold
--   out ∘ in-F ≈ id   :=   ana-unfold˘
-- No inverse is synthesised and no transport is used.
--
-- 终 M-Cosmos 的 Lambek 引理（互模拟意义下）
--
-- 在 M 中自指是内建的（无独立 Unfolding 种子类型）：结构映射即观察
-- 余代数 unfold-coalgebra（label = M.here，child = step），其逆不过是
-- 对该观察余代数取 ana。两条往返恰是 Cosmos/M/Object 中已证的 eta 对：
--   in-F ∘ out ≈ id   :=   ana-unfold
--   out ∘ in-F ≈ id   :=   ana-unfold˘
-- 无需综合逆映射，也不用任何传输。
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module Cosmos.M.Lambek where

open import Agda.Primitive using (Level)
open import Categories.Category.Core using (Category)
open import Categories.Functor.Core using (Functor)

open import Cosmos.ContCategory using (ContCat)
open import Base.MCorr.Setoid using (EqOn)
open import Cosmos.M.Object using
  (I; A; ana; ana-unfold; ana-unfold˘; CosmosM; ≈CosmosM; unfold-coalgebra)

module _ {o h e s p : Level}
         {C  : Category o h e}
         {FC : Functor C (ContCat s p)} where

  module _ {ℓd : Level}
           (≈CD : (i : I C FC) → EqOn {ℓ = ℓd} (A C FC i)) where

    --------------------------------------------------------------------
    -- in-F ∘ out ≈ id
    --
    -- This is ana-unfold.
    --
    -- in-F ∘ out ≈ id
    --
    -- 即 ana-unfold。

    lambek-in∘out : ∀ {i : I C FC} (t : CosmosM C FC i)
                  → ≈CosmosM C FC ≈CD
                      (ana C FC (unfold-coalgebra C FC) i t) t
    lambek-in∘out t = ana-unfold C FC ≈CD t

    --------------------------------------------------------------------
    -- out ∘ in-F ≈ id
    --
    -- This is ana-unfold˘.
    --
    -- out ∘ in-F ≈ id
    --
    -- 即 ana-unfold˘。

    lambek-out∘in : ∀ {i : I C FC} (t : CosmosM C FC i)
                  → ≈CosmosM C FC ≈CD
                      t (ana C FC (unfold-coalgebra C FC) i t)
    lambek-out∘in t = ana-unfold˘ C FC ≈CD t
