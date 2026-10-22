------------------------------------------------------------------------
-- Coinductive indexed M-type
--
-- 余归纳索引 M 型
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module Base.IndexedMType where

open import Agda.Primitive using (_⊔_; lzero)
open import Data.Unit.Polymorphic.Base using (⊤; tt)

------------------------------------------------------------------------
-- The coinductive skeleton Mᵢ
--
-- An index i carries a first component fst : A i and a guarded
-- continuation snd that advances the index via next. LayeredEqGen and
-- IndexedLayeredEq are applications of Mᵢ.
--
-- 余归纳骨架 Mᵢ
--
-- 索引 i 携带首分量 fst : A i，以及经 next 推进索引的受保护延续
-- snd。LayeredEqGen 与 IndexedLayeredEq 是 Mᵢ 的应用。

record Mᵢ {i a b} {I : Set i}
          (A : I → Set a)
          (B : (i : I) (a : A i) → Set b)
          (next : (i : I) (a : A i) (p : B i a) → I)
          (i : I) : Set (a ⊔ b) where
  coinductive
  field
    fst : A i
    snd : (p : B i fst) → Mᵢ A B next (next i fst p)

open Mᵢ public

------------------------------------------------------------------------
-- The non-indexed M
--
-- 无索引的 M

M : ∀ {a b} (A : Set a) (B : A → Set b) → Set (a ⊔ b)
M A B = Mᵢ {i = lzero} {I = ⊤} (λ _ → A) (λ _ x → B x)
          (λ _ _ _ → tt) tt
