------------------------------------------------------------------------
-- The M-Cosmos category
--
-- MCorrCatˢ specialised to the M-Cosmos levels. The generic
-- Base.MCorrSetoidCat has setoid systems (SysEq) as objects and
-- deterministic carried setoid functors FMˢ as morphisms, with
-- behavioural bisimulation as hom equality. This module only pins the
-- levels so that the M-Cosmos system Object.sys ≈CD is a canonical
-- object.
-- The deterministic endomorphisms of sys ≈CD are the carried type of the
-- old container deterministic self-morphism _⇒ℱ[S]_.
--
-- M-Cosmos 范畴
--
-- MCorrCatˢ 在 M-Cosmos 层级处的特化。通用范畴 Base.MCorrSetoidCat 以
-- setoid 系统（SysEq）为对象、确定性携带 setoid 函子 FMˢ 为态射、
-- 行为互模拟为 hom 等价。本模块只钉住层级，使 M-Cosmos 系统
-- Object.sys ≈CD 成为典范对象。
-- sys ≈CD 的确定性自态射即旧容器确定性自态射 _⇒ℱ[S]_ 的携带式类型。
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module ALMA.Cosmos.M.CosmosCategory where

open import Agda.Primitive using (Level; _⊔_; lsuc)

open import Categories.Category.Core using (Category)
open import Categories.Functor.Core using (Functor)

open import ALMA.Cosmos.ContCategory using (ContCat)
open import ALMA.Base.MCorrSetoid using (SysEq; EqOn)
open import ALMA.Base.MCorrSetoidCat using (MCorrCatˢ; FMˢ; idFMˢ; compFMˢ)
open import ALMA.Cosmos.M.Object using (I; A; sys)

module _ {o h e s p : Level}
         (C  : Category o h e)
         (FC : Functor C (ContCat s p)) where

  private
    iL = o ⊔ s
    aL = o ⊔ h ⊔ e ⊔ s ⊔ p
    bL = o ⊔ s ⊔ p

  -- The canonical M-Cosmos system at ≈CD
  --
  -- ≈CD is the single seam selecting propositional labels (container
  -- regime) vs natural-isomorphism labels (general category regime).
  --
  -- 在 ≈CD 下的典范 M-Cosmos 系统
  --
  -- ≈CD 是选择命题标签（容器制度）还是自然同构标签（一般范畴制度）的
  -- 唯一接缝。
  cosmosSys : ∀ {ℓd : Level}
              (≈CD : (i : I C FC) → EqOn {ℓ = ℓd} (A C FC i))
            → SysEq iL aL bL ℓd bL
  cosmosSys ≈CD = sys C FC ≈CD

  -- MCorrCatˢ with its level arguments pinned
  --
  -- sys ≈CD is an object.
  --
  -- 钉住层级参数的 MCorrCatˢ
  --
  -- sys ≈CD 是其一个对象。
  CosmosMCat : ∀ {ℓd : Level}
               (≈CD : (i : I C FC) → EqOn {ℓ = ℓd} (A C FC i))
             → Category (lsuc (aL ⊔ ℓd)) (aL ⊔ ℓd) (aL ⊔ ℓd)
  CosmosMCat {ℓd = ℓd} _ = MCorrCatˢ iL aL bL ℓd bL

  -- Deterministic carried endofunctors of the M-Cosmos system
  --
  -- The carried type replacing the old _⇒ℱ[S]_.
  --
  -- M-Cosmos 系统的确定性携带自函子
  --
  -- 取代旧 _⇒ℱ[S]_ 的携带式类型。
  CosmosM-endo : ∀ {ℓd : Level}
                  (≈CD : (i : I C FC) → EqOn {ℓ = ℓd} (A C FC i))
                → Set (aL ⊔ ℓd)
  CosmosM-endo ≈CD = FMˢ (cosmosSys ≈CD) (cosmosSys ≈CD)

  id-endo : ∀ {ℓd : Level}
              (≈CD : (i : I C FC) → EqOn {ℓ = ℓd} (A C FC i))
          → CosmosM-endo ≈CD
  id-endo _ = idFMˢ

  comp-endo : ∀ {ℓd : Level}
                (≈CD : (i : I C FC) → EqOn {ℓ = ℓd} (A C FC i))
              → CosmosM-endo ≈CD → CosmosM-endo ≈CD → CosmosM-endo ≈CD
  comp-endo _ g f = compFMˢ g f
