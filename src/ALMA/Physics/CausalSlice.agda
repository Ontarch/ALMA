------------------------------------------------------------------------
-- Constant-time slices are spacelike hypersurfaces
--
-- A strict causal grading turns the "cognitive section = spatial
-- slice" remark into a theorem: if every edge raises the layer by
-- exactly one and every event occupies a unique layer, then each layer
-- is an Antichain, and the same grading entails Acyclic. The time
-- arrow and the spatial slices therefore arise from one carried
-- structure.
--
-- 等时截面即类空超曲面
--
-- 严格因果分层把“认知截面 = 空间切片”落成定理：若每条边恰把层推进
-- 一、每事件占据唯一层，则每层是反链，且同一分层蕴含 Acyclic。时间
-- 箭头与空间切片因此出自同一个携带结构。
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module ALMA.Physics.CausalSlice where

open import Agda.Primitive using (Level; _⊔_)
open import Agda.Builtin.Sigma using (Σ; _,_)
open import Data.Empty using (⊥)
open import Data.Product.Base using (_×_)
open import Data.Nat.Base using (ℕ; suc)

open import ALMA.Base.MCorrSetoid using (SysEq)
open import ALMA.Physics.CausalOrder using (Acyclic; Antichain; _⇝⁺_; step; more)

------------------------------------------------------------------------
-- Strict order on layers
--
-- Inductively, with no arithmetic equality.
--
-- 层上的严格序
--
-- 归纳给出，不使用算术等式。

data _<ℕ_ : ℕ → ℕ → Set where
  <suc  : ∀ {n} → n <ℕ suc n
  <step : ∀ {n m} → n <ℕ m → n <ℕ suc m

<ℕ-trans : ∀ {n m k} → n <ℕ m → m <ℕ k → n <ℕ k
<ℕ-trans p <suc     = <step p
<ℕ-trans p (<step q) = <step (<ℕ-trans p q)

module _ {i a b ℓa ℓe : Level} (X : SysEq i a b ℓa ℓe) where

  open SysEq X

  private
    ℓord = i ⊔ a ⊔ b

  ----------------------------------------------------------------------
  -- Strict causal grading
  --
  -- L n is the layer at time n; every edge goes from layer n to suc n;
  -- g-disjoint says an event occupies one layer (its time coordinate is
  -- unique); g-surj says every event is graded.
  --
  -- 严格因果分层
  --
  -- L n 为时刻 n 的层；每条边从层 n 到 suc n；g-disjoint 表示每事件只
  -- 占一层（时间坐标唯一）；g-surj 表示每事件都被分层。
  record Grading {ℓ : Level} (L : ℕ → I → Set ℓ)
         : Set (ℓord ⊔ ℓ) where
    field
      g-edge     : ∀ {n x y} → L n x
                 → (a : A x) (e : E x a y) → L (suc n) y
      g-disjoint : ∀ {n m x} → n <ℕ m → L n x → L m x → ⊥
      g-surj     : ∀ (x : I) → Σ ℕ λ n → L n x

  module _ {ℓ : Level} {L : ℕ → I → Set ℓ} (G : Grading L) where

    open Grading G

    -- A positive path out of layer n ends on a strictly higher layer,
    -- carrying the higher-layer witness.
    --
    -- 从层 n 出发的正路径终止于严格更高的层，并携带高层见证。
    raise : ∀ {n x y} → L n x → _⇝⁺_ X x y
          → Σ ℕ λ m → (n <ℕ m) × L m y
    raise Lx (step a e)              = suc _ , <suc , g-edge Lx a e
    raise Lx (more a e p) with raise (g-edge Lx a e) p
    ... | m , sm , Lm               = m , <ℕ-trans <suc sm , Lm

    -- Two events sharing a layer cannot positively precede each other.
    --
    -- 同层两事件不能互相正在先。
    layer-future-⊥ : ∀ {n x y} → L n x → L n y → _⇝⁺_ X x y → ⊥
    layer-future-⊥ Lx Ly p with raise Lx p
    ... | m , nm , Lm = g-disjoint nm Ly Lm

    -- Every layer is a spatial (spacelike) slice.
    --
    -- 每一层都是空间（类空）切片。
    layer-antichain : ∀ n → Antichain X (L n)
    layer-antichain n {x} {y} Lx Ly =
        layer-future-⊥ Lx Ly
      , (λ q → layer-future-⊥ Ly Lx q)

    -- A strict grading orients the edge family: no positive path loops.
    --
    -- 严格分层为边族定向：无正路径成环。
    grading-acyclic : Acyclic X
    grading-acyclic {x} p with g-surj x
    ... | n , Ln with raise Ln p
    ... | m , nm , Lm = g-disjoint nm Ln Lm
