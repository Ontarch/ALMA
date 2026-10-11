------------------------------------------------------------------------
-- Terminality of the M-Cosmos (carried)
--
-- Self-reference is native to M, so the terminal coalgebra vocabulary
-- is directly that of Cosmos/M/Object: ana γ gives the anamorphism from
-- any one-step state coalgebra (matching the edge (p , refl)
-- constructively); unfold-coalgebra is the canonical coalgebra on
-- CosmosM (label = head, child = step); ana-unfold / ana-unfold˘ show
-- ana of it is the identity up to ≈CosmosM. This module is the
-- canonical namespace for the M-base CoalgCat / Lambek migration.
--
-- M-Cosmos 的终性（携带式）
--
-- 自指为 M 内建，故终余代数词表直接就是 Cosmos/M/Object 的词表：
-- ana γ 从任意一步状态余代数给出 anamorphism（构造性匹配边
-- (p , refl)）；unfold-coalgebra 是 CosmosM 上的典范余代数（label 取
-- 头部、child 取 step）；ana-unfold / ana-unfold˘ 表明对其取 ana 在
-- ≈CosmosM 下双向为恒等。本模块是 M 底座 CoalgCat / Lambek 迁移的规范
-- 命名空间。
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module ALMA.Cosmos.M.Terminal where

open import Agda.Primitive using (Level)

open import Categories.Category.Core using (Category)
open import Categories.Functor.Core using (Functor)

open import ALMA.Cosmos.ContCategory using (ContCat)
open import ALMA.Base.MCorrSetoid using ( EqOn; SysEq; ≈Mˢ-sym; ≈Mˢ-trans)
open import ALMA.Cosmos.M.Object as MO
open MO using
  (CosmosM; Rooted; step; next; nextOf; Coalgebra; ana; unfold-coalgebra
  ; ≈CosmosM; ≈CosmosM-refl; ana-unfold; ana-unfold˘)

------------------------------------------------------------------------
-- Bisimulation equivalence on CosmosM
--
-- Specialised from the generic _≈Mˢ_ symmetry/transitivity at the
-- M-Cosmos system; they contain no transport.
--
-- CosmosM 上的互模拟等价
--
-- 由通用 _≈Mˢ_ 的对称/传递在 M-Cosmos 系统处特化而来；不含传输。

module _ {o h e s p : Level}
         {C  : Category o h e}
         {FC : Functor C (ContCat s p)} where

  ≈CosmosM-sym : ∀ {ℓd : Level}
                   (≈CD : (i : MO.I C FC) → EqOn {ℓ = ℓd} (MO.A C FC i))
                   {i : MO.I C FC} {t s : MO.CosmosM C FC i}
               → MO.≈CosmosM C FC ≈CD {i = i} t s
               → MO.≈CosmosM C FC ≈CD {i = i} s t
  ≈CosmosM-sym ≈CD =
    ≈Mˢ-sym (SysEq.≈A (MO.sys C FC ≈CD))
            (SysEq.≈E (MO.sys C FC ≈CD))

  ≈CosmosM-trans : ∀ {ℓd : Level}
                     (≈CD : (i : MO.I C FC) → EqOn {ℓ = ℓd} (MO.A C FC i))
                     {i : MO.I C FC} {t m s : MO.CosmosM C FC i}
                 → MO.≈CosmosM C FC ≈CD {i = i} t m
                 → MO.≈CosmosM C FC ≈CD {i = i} m s
                 → MO.≈CosmosM C FC ≈CD {i = i} t s
  ≈CosmosM-trans ≈CD =
    ≈Mˢ-trans (SysEq.≈A (MO.sys C FC ≈CD))
              (SysEq.≈E (MO.sys C FC ≈CD))

  ----------------------------------------------------------------------
  -- The bisimulation as a manifest EqOn on CosmosM i
  --
  -- No carrier coercion.
  --
  -- 互模拟作为 CosmosM i 上的外显 EqOn
  --
  -- 无载体强制转换。

  ≈CosmosM-isEqOn : ∀ {ℓd : Level}
                      (≈CD : (i : MO.I C FC) → EqOn {ℓ = ℓd} (MO.A C FC i))
                      {i : MO.I C FC}
                    → EqOn (MO.CosmosM C FC i)
  ≈CosmosM-isEqOn ≈CD {i = i} = record
    { _≈_ = MO.≈CosmosM C FC ≈CD {i = i}
    ; isEquivalence = record
      { refl  = λ {t} → MO.≈CosmosM-refl C FC ≈CD t
      ; sym   = ≈CosmosM-sym ≈CD
      ; trans = ≈CosmosM-trans ≈CD
      }
    }
