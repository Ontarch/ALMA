------------------------------------------------------------------------
-- FinCat∞: the colimit category Indiscrete ℕ (carried, zero-subst core)
--
-- The family {FinCatN m} = {Indiscrete (Fin n_m)}, n_m = suc (suc m),
-- has colimit Indiscrete ℕ. This module now keeps only the live surface:
--
--   FinCat∞ / TrivialFC∞ / ∞Layer / ∞Idx / ∞Tower / n-at
--
-- FinCat∞：余极限范畴 Indiscrete ℕ（携带式零 subst 内核）
--
-- 有限族 {FinCatN m} = {Indiscrete (Fin n_m)}（n_m = suc (suc m)）的余
-- 极限为 Indiscrete ℕ。本模块现在只保留活跃表面：
--
--   FinCat∞ / TrivialFC∞ / ∞Layer / ∞Idx / ∞Tower / n-at
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module SecondPass.FinCatInfinity where

open import Agda.Primitive using (lzero)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Level using (Lift; lift)
open import Data.Unit.Polymorphic.Base using (⊤; tt)
open import Data.Nat using (ℕ)
open import Data.Fin.Base using (Fin; toℕ)

open import Categories.Category.Core using (Category)
open import Categories.Category.Indiscrete using (Indiscrete)
open import Categories.Functor.Core using (Functor)

open import Cosmos.ContCategory using (ContCat)
open import SecondPass.StrictLift using (StrictLayer)
open import SecondPass.CumulativeHierarchyLimit using (LayerIdx; Tower)

-- The carried, zero-subst size / representatives / embedding and the
-- Set-level universal property (single source of truth).
--
-- 携带式零 subst 的尺寸 / 代表 / 嵌入与 Set 层泛性质（唯一事实来源）。
open import Cosmos.Carried.LimitSystem public
  using (n-at; natToFin; toℕ-natToFin; embFin; toℕ-embFin)
open import Cosmos.Carried.SeqColimit public using (shift)
open import Cosmos.Carried.FinColimit public
  using (FinCone; colimitUniv)

-- The colimit category and its trivial container functor (all shapes and
-- positions are the lifted unit).
--
-- 余极限范畴及其平凡容器函子（所有形状与位置均为提升的单位类型）。
FinCat∞ : Category lzero lzero lzero
FinCat∞ = Indiscrete ℕ

TrivialFC∞ : Functor FinCat∞ (ContCat lzero lzero)
TrivialFC∞ = record
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

∞Layer : StrictLayer lzero lzero lzero lzero lzero
∞Layer = record { C = FinCat∞ ; FC = TrivialFC∞ }

∞Idx : LayerIdx
∞Idx = record { o = lzero ; h = lzero ; e = lzero ; s = lzero ; p = lzero }

∞Tower : Tower ∞Idx
∞Tower = record { layer₀ = ∞Layer }

------------------------------------------------------------------------
-- Historical API names, backed by the zero-subst carried construction.
--
-- 历史 API 名，由零 subst 携带式构造支撑。
------------------------------------------------------------------------

-- A compatible cone over the finite stages (formerly ColimitCone).
-- FinCone carries at / compat plus the subst-free compat-emb.
--
-- 有限层上的相容锥（旧名 ColimitCone）。FinCone 携带 at / compat 以及
-- 零 subst 的 compat-emb。
ColimitCone : Set → Set
ColimitCone = FinCone

-- d-fold finite embedding, stated with the carried shift index (which is
-- definitionally m + d). This replaces the old subst Fin (+-suc) packaging.
--
-- d 次有限嵌入，以携带式 shift 索引陈述（定义性等于 m + d）。取代旧的
-- subst Fin (+-suc) 包装。
inject₁^d : ∀ d {m} → Fin (n-at m) → Fin (n-at (shift d m))
inject₁^d d {m} x = embFin d m x

-- The iterated embedding preserves the natural-number position.
--
-- 迭代嵌入保持自然数位置。
toℕ-inject₁^d : ∀ d {m} (x : Fin (n-at m))
              → toℕ (inject₁^d d {m} x) ≡ toℕ x
toℕ-inject₁^d d {m} x = toℕ-embFin d m x
