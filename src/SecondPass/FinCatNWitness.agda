------------------------------------------------------------------------
-- Witness over FinCat n for n ≥ 2
--
-- Provides the trivial container, the tower, the two distinguished
-- cosmoi (cosmos-idN and cosmos-const0N), and their non-bisimilarity.
-- The parameter m encodes n = suc (suc m), so n ≥ 2 holds
-- definitionally; this is required by cosmos-idN≉cosmos-const0N,
-- since at n = 1 the type Fin 1 is a singleton and the two cosmoi
-- coincide
--
-- FinCat n（n ≥ 2）上的见证
--
-- 提供平凡容器、塔、两个区分宇宙（cosmos-idN 与 cosmos-const0N）
-- 及其非互模拟性。参数 m 编码 n = suc (suc m)，使 n ≥ 2 定义性成立；
-- 这是 cosmos-idN≉cosmos-const0N 所必需的，因 n = 1 时 Fin 1 为单点集，
-- 两个宇宙重合
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module SecondPass.FinCatNWitness where

open import Agda.Primitive using (lzero)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Level using (Lift; lift)
open import Relation.Nullary using (¬_)
open import Data.Unit.Polymorphic.Base using (⊤; tt)
open import Data.Product.Base using (proj₁)
open import Data.Nat using (ℕ; suc)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)

open import Categories.Category.Core using (Category)
open import Categories.Category.Indiscrete using (Indiscrete)
open import Categories.Functor.Core using (Functor)

open import Cosmos.ContCategory using (ContCat)
open import SecondPass.Cosmos using (Cosmos; out)
open import SecondPass.Terminal using (_≈C_)
open _≈C_
open import SecondPass.StrictLift using (StrictLayer)
open import SecondPass.CumulativeHierarchyLimit using (LayerIdx; Tower)

module FinCatN (m : ℕ) where

  -- n = suc (suc m), so n ≥ 2 definitionally
  -- n = suc (suc m)，故 n ≥ 2 定义性成立
  n : ℕ
  n = suc (suc m)

  -- FinCat n = Indiscrete (Fin n), all at lzero
  -- FinCat n = Indiscrete (Fin n)，均在 lzero
  FinCatN : Category lzero lzero lzero
  FinCatN = Indiscrete (Fin n)

  -- Trivial container at lzero: singleton shapes and positions
  -- lzero 上的平凡容器：形状与位置均为单点
  TrivialFCN : Functor FinCatN (ContCat lzero lzero)
  TrivialFCN = record
    { F₀ = λ _ → record
        { Shape    = Lift lzero (⊤ {lzero})
        ; Position = λ _ → Lift lzero (⊤ {lzero})
        }
    ; F₁ = λ _ → record
        { shape    = λ _ → lift tt
        ; position = λ _ → lift tt
        }
    ; identity = record
        { shape-eq    = λ { (lift tt) → refl }
        ; position-eq = λ _ _ → refl
        }
    ; homomorphism = record
        { shape-eq    = λ _ → refl
        ; position-eq = λ _ _ → refl
        }
    ; F-resp-≈ = λ _ → record
        { shape-eq    = λ _ → refl
        ; position-eq = λ _ _ → refl
        }
    }

  -- Base layer at lzero
  -- 基础层，均在 lzero
  nLayer : StrictLayer lzero lzero lzero lzero lzero
  nLayer = record { C = FinCatN ; FC = TrivialFCN }

  -- Layer index at lzero
  -- 层索引，均在 lzero
  nIdx : LayerIdx
  nIdx = record
    { o = lzero
    ; h = lzero
    ; e = lzero
    ; s = lzero
    ; p = lzero
    }

  -- Tower starting at nLayer
  -- 从 nLayer 起始的塔
  nTower : Tower nIdx
  nTower = record { layer₀ = nLayer }

  -- Cosmos with F₀ = proj₁ (identity-like universe)
  -- F₀ = proj₁ 的宇宙（类恒等宇宙）
  cosmos-idN : Cosmos FinCatN TrivialFCN
  cosmos-idN .out = record
    { unfoldFunctor = record
        { F₀ = proj₁
        ; F₁ = λ _ → tt
        ; identity     = refl
        ; homomorphism = refl
        ; F-resp-≈     = λ _ → refl
        }
    ; unfold-next     = λ _ → cosmos-idN
    ; pos-to-shape    = λ _ _ → lift tt
    ; pos-actS-compat = λ _ _ _ → refl
    }

  -- Cosmos with F₀ = λ _ → fzero (constant on first object)
  -- F₀ = λ _ → fzero 的宇宙（常值于第一个对象）
  cosmos-const0N : Cosmos FinCatN TrivialFCN
  cosmos-const0N .out = record
    { unfoldFunctor = record
        { F₀ = λ _ → fzero
        ; F₁ = λ _ → tt
        ; identity     = refl
        ; homomorphism = refl
        ; F-resp-≈     = λ _ → refl
        }
    ; unfold-next     = λ _ → cosmos-const0N
    ; pos-to-shape    = λ _ _ → lift tt
    ; pos-actS-compat = λ _ _ _ → refl
    }

  -- In Fin (suc (suc m)), fsuc fzero ≠ fzero
  -- 在 Fin (suc (suc m)) 上，fsuc fzero ≠ fzero
  fsuc-fzero≠fzero
    : ¬ (fsuc {n = suc m} (fzero {n = m}) ≡ fzero {n = suc m})
  fsuc-fzero≠fzero ()

  -- cosmos-idN and cosmos-const0N are not bisimilar: their F₀ differ
  -- at fsuc fzero
  -- cosmos-idN 与 cosmos-const0N 不互模拟：在 fsuc fzero 处 F₀ 不同
  cosmos-idN≉cosmos-const0N : ¬ (cosmos-idN ≈C cosmos-const0N)
  cosmos-idN≉cosmos-const0N eq =
    fsuc-fzero≠fzero
      (unfoldFunctor₀-eq eq
        {A = fsuc {n = suc m} (fzero {n = m})}
        (lift tt))
