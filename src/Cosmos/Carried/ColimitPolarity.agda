------------------------------------------------------------------------
-- Polarity obstruction for a carried sequential-colimit leg
--
-- A deterministic carried morphism FMapˢ is a pull notion: its childF
-- field supplies, for every target index v, a source index x in the
-- graph of the index map (u x ≡ v), so u is necessarily surjective. A
-- fixed finite stage of a direct sequence embeds into the limit
-- non-surjectively -- the bounded Fin (suc k) → ℕ inclusion misses the
-- new top suc k -- hence that inclusion cannot underlie any FMˢ leg.
-- Non-trivial colimit legs are therefore forward simulations, not pull
-- morphisms.
--
-- 携带式序列余极限腿的极性障碍
--
-- 确定性携带态射 FMapˢ 是 pull 概念：其 childF 字段对每个目标索引 v
-- 给出处于索引映射之图中的源索引 x（u x ≡ v），故 u 必满。直接序列的
-- 固定有限层到极限的嵌入不满——有界的 Fin (suc k) → ℕ 嵌入漏掉新末位
-- suc k——故此嵌入不能承载任何 FMˢ 腿。非平凡余极限腿因而是前向模拟
-- 而非 pull 态射。
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module Cosmos.Carried.ColimitPolarity where

open import Agda.Primitive using (Level; lzero)
open import Agda.Builtin.Sigma using (Σ; _,_)
open import Agda.Builtin.Equality using (_≡_)
open import Data.Unit.Polymorphic.Base using (⊤; tt)
open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Nat.Properties using (<-irrefl)
open import Data.Fin.Base using (Fin; zero; toℕ)
open import Data.Fin.Properties using (toℕ<n)
open import Data.Empty using (⊥)
open import Function.Base using (id)
open import Relation.Nullary.Negation using (¬_)
open import Relation.Binary.PropositionalEquality.Core using (sym; trans)

open import Base.MCorr.Setoid using (SysEq; propEqOn)
open import Base.MCorr.SetoidCat using (FMapˢ; FMˢ)

open SysEq
open FMapˢ
open FMˢ

------------------------------------------------------------------------
-- Pull polarity
--
-- FMapˢ forces the index map to be a submersion, so a non-surjective
-- index map cannot underlie a FMapˢ, and the same obstruction lifts to
-- the FMˢ level used by the colimit legs.
--
-- pull 极性
--
-- FMapˢ 迫使索引映射为满射，故不满的索引映射不能承载 FMapˢ，且同一
-- 障碍提升到余锥腿所用的 FMˢ 层面。

module _ {i j a b c d ℓa ℓe ℓc ℓd : Level}
         {X : SysEq i a b ℓa ℓe}
         {Y : SysEq j c d ℓc ℓd} where

  -- Every target index has a source preimage in the graph of u.
  --
  -- 每个目标索引在 u 的图中都有源原像。
  FMapˢ-surjective : (f : FMapˢ X Y) (x₀ : I X) (a₀ : A X x₀)
                   → (v : I Y) → Σ (I X) λ x → u f x ≡ v
  FMapˢ-surjective f x₀ a₀ v = childF f x₀ a₀ v

  -- A non-surjective index map cannot underlie a FMapˢ.
  --
  -- 不满的索引映射不能承载 FMapˢ。
  no-FMap-nonsurjective
    : (x₀ : I X) (a₀ : A X x₀)
      (u₀ : I X → I Y) (v₀ : I Y)
    → (¬ Σ (I X) λ x → u₀ x ≡ v₀)
    → (f : FMapˢ X Y)
    → ((x : I X) → u f x ≡ u₀ x)
    → ⊥
  no-FMap-nonsurjective x₀ a₀ u₀ v₀ miss f eq-u =
    miss (let x , e = childF f x₀ a₀ v₀
          in x , trans (sym (eq-u x)) e)

  -- Same obstruction at the FMˢ level used by the colimit legs.
  --
  -- 余锥腿所用 FMˢ 层面上的同一障碍。
  no-FM-nonsurjective
    : (x₀ : I X) (a₀ : A X x₀)
      (u₀ : I X → I Y) (v₀ : I Y)
    → (¬ Σ (I X) λ x → u₀ x ≡ v₀)
    → (g : FMˢ X Y)
    → ((x : I X) → u (mor g) x ≡ u₀ x)
    → ⊥
  no-FM-nonsurjective x₀ a₀ u₀ v₀ miss g =
    no-FMap-nonsurjective x₀ a₀ u₀ v₀ miss (mor g)

------------------------------------------------------------------------
-- Trivial-fibre setoid system
--
-- Over an index type with one deterministic successor; only the index
-- sets matter for the polarity witness.
--
-- 平凡纤维 setoid 系统
--
-- 索引类型上的平凡纤维 setoid 系统，具唯一确定性后继；极性见证只依赖
-- 索引集。

TrivSysEq : {i : Level} (I : Set i) (step : I → I)
          → SysEq i lzero i lzero i
TrivSysEq {i = i} I step = record
  { I   = I
  ; A   = λ _ → ⊤ {lzero}
  ; E   = λ x _ y → y ≡ step x
  ; ≈A  = λ _ → propEqOn (⊤ {lzero})
  ; ≈E  = λ { x _ y → propEqOn (y ≡ step x) }
  }

------------------------------------------------------------------------
-- Concrete witness
--
-- The bounded finite-stage inclusion misses the top: the new top suc k
-- has no finite-stage preimage under toℕ, so no FMˢ colimit leg can have
-- the bounded inclusion as index map.
--
-- 具体见证
--
-- 有界有限层嵌入漏掉末位：新末位 suc k 在 toℕ 下无有限层原像，故任何
-- FMˢ 余极限腿都不能以有界嵌入为索引映射。

module _ (k : ℕ) where

  -- The stage has k+1 positions 0..k; the limit index is ℕ.
  --
  -- 该层有 k+1 个位置 0..k；极限索引为 ℕ。
  Stage : SysEq lzero lzero lzero lzero lzero
  Stage = TrivSysEq (Fin (suc k)) id

  Limit : SysEq lzero lzero lzero lzero lzero
  Limit = TrivSysEq ℕ id

  -- The new top suc k has no finite-stage preimage under toℕ.
  --
  -- 新末位 suc k 在 toℕ 下无有限层原像。
  top-missing : ¬ Σ (Fin (suc k)) λ x → toℕ x ≡ suc k
  top-missing (x , e) = <-irrefl e (toℕ<n x)

  -- No FMˢ colimit leg can have the bounded inclusion as index map.
  --
  -- 任何 FMˢ 余极限腿都不能以有界嵌入为索引映射。
  no-leg : (g : FMˢ Stage Limit)
         → ((x : Fin (suc k)) → u (mor g) x ≡ toℕ x)
         → ⊥
  no-leg = no-FM-nonsurjective {X = Stage} {Y = Limit}
                             zero tt toℕ (suc k) top-missing
