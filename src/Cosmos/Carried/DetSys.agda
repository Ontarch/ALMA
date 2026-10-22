------------------------------------------------------------------------
-- Deterministic indexed M-types as edge-indexed MCorr systems
--
-- A deterministic (I, A, B, next) presentation gives an MCorr system
-- whose edge fibre E x a y = Σ (B x a) λ p → y ≡ next x a p has
-- exactly one inhabitant per reachable child and is empty otherwise.
-- No dependent transport appears: the successor equation is a
-- homogeneous equation on the single index type I, carried inside the
-- edge witness rather than eliminated by J.
--
-- 确定性索引 M 型到边索引 MCorr 系统的桥接
--
-- 确定性的 (I, A, B, next) 给出一个 MCorr 系统，其边纤维
-- E x a y = Σ (B x a) λ p → y ≡ next x a p 对每个可达子节点恰有一个
-- 栖居者、其余为空。全程无依赖传输：后继等式是单一索引类型 I 上的
-- 同质等式，携带在边见证内，而非用 J 消去。
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module Cosmos.Carried.DetSys where

open import Agda.Primitive using (Level; _⊔_; lzero)
open import Agda.Builtin.Sigma using (Σ)
open import Agda.Builtin.Equality using (_≡_)
open import Data.Unit.Polymorphic.Base using (⊤)

open import Base.MCorr using (Sys; M)

------------------------------------------------------------------------
-- The deterministic system built from (I, A, B, next)
--
-- 由 (I, A, B, next) 构造的确定性系统

module DetSys {i a b : Level}
             (I : Set i)
             (A : I → Set a)
             (B : (x : I) (a : A x) → Set b)
             (next : (x : I) (a : A x) (p : B x a) → I)
             where

  -- The edge witness carries the position p and the homogeneous
  -- successor equation; it is never transported.
  --
  -- 边见证携带位置 p 与同质后继等式；绝不传输。
  E : (x : I) (a : A x) (y : I) → Set (i ⊔ b)
  E x a y = Σ (B x a) λ p → y ≡ next x a p

  -- Edge level is i ⊔ b (the witness stores an index equation);
  -- labels stay at level a.
  --
  -- 边层级为 i ⊔ b（见证存一条索引等式）；标签层级仍为 a。
  sys : Sys i a (i ⊔ b)
  sys = record { I = I ; A = A ; E = E }

  DetM : (x : I) → Set (a ⊔ i ⊔ b)
  DetM x = M A E x

------------------------------------------------------------------------
-- Trivial-fibre deterministic system
--
-- Over an index type I, every node carries one trivial label and one
-- trivial position, hence exactly one successor step x. The only real
-- data is the transition on indices; the edge fibre
-- E x tt y = y ≡ step x is a singleton at the unique successor and
-- empty elsewhere, so it lives at the index level i.
--
-- 平凡纤维确定性系统
--
-- 索引类型 I 上的平凡纤维确定性系统：每个节点恰有一个平凡标签与一个
-- 平凡位置，故恰有一个后继 step x。唯一真实数据是索引上的转移；边纤维
-- E x tt y = y ≡ step x 在唯一后继处为单点、其余为空，故位于索引层 i。

module TrivDet {i : Level} (I : Set i) (step : I → I) where

  private
    Aᵗ : I → Set lzero
    Aᵗ _ = ⊤

    Bᵗ : (x : I) → Aᵗ x → Set lzero
    Bᵗ _ _ = ⊤

    nextᵗ : (x : I) (a : Aᵗ x) (p : Bᵗ x a) → I
    nextᵗ x _ _ = step x

  open DetSys I Aᵗ Bᵗ nextᵗ public
