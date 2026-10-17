------------------------------------------------------------------------
-- Lattice coherence: separation lemmas interderive
--
-- The base and physical lattices share their two upper corners
-- definitionally; their bottom corners differ (DiscreteEq versus
-- QuantumLayer). A uniform lift from either bottom corner to a full
-- LayeredEqGen produces a uniform lift from the other, so the two
-- separation lemmas are equivalent.
--
-- 格一致性：分离引理互推
--
-- 基础格与物理格的两个上角定义性地重合；底角不同（DiscreteEq 与
-- QuantumLayer）。从任一底角到完整 LayeredEqGen 的一致提升都会
-- 产生从另一底角的一致提升，故两个分离引理等价。
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module ALMA.Physics.LatticeCoherence where

open import Agda.Primitive using (lzero)
open import Data.Unit.Polymorphic.Base using (⊤; tt)
open import Relation.Nullary.Negation.Core using (¬_)

open import ALMA.Base.Equivalence.Core using (LayeredEqGen)
open import ALMA.Base.Equivalence.DiscreteEq using (DiscreteEq)
open import ALMA.Base.Equivalence.QuantumLayer
  using (QuantumLayer; ofDiscrete; toDiscrete)

------------------------------------------------------------------------
-- The two lifts
--
-- A base lift takes a bare relation to a full LayeredEqGen; a physical
-- lift does the same from a QuantumLayer, ignoring the amplitude.
--
-- 两个提升
--
-- 基础提升把裸关系送到完整 LayeredEqGen；物理提升从 QuantumLayer
-- 出发做同样的事，忽略振幅。

BaseLift : Set _
BaseLift =
  (X : Set)
  (rel : X → X → Set)
  (Obs : X → Set)
  (step : (x : X) → Obs x → X)
  (obs-map : (x y : X) → rel x y → Obs x → Obs y)
  → ∀ {x y} → DiscreteEq rel x y → LayeredEqGen Obs step rel obs-map x y

PhysLift : Set _
PhysLift =
  (X : Set)
  (S : Set)
  (Q : QuantumLayer X S)
  (Obs : X → Set)
  (step : (x : X) → Obs x → X)
  (obs-map : (x y : X) → toDiscrete Q x y → Obs x → Obs y)
  → ∀ {x y} → toDiscrete Q x y
             → LayeredEqGen Obs step (toDiscrete Q) obs-map x y

BaseSep : Set _
BaseSep = ¬ BaseLift

PhysSep : Set _
PhysSep = ¬ PhysLift

------------------------------------------------------------------------
-- Direction: a base lift yields a physical lift
--
-- Given a base lift L, the physical lift on a QuantumLayer Q applies
-- L to the underlying relation toDiscrete Q. The amplitude plays no
-- role.
--
-- 方向：基础提升给出物理提升
--
-- 给定基础提升 L，QuantumLayer Q 上的物理提升把 L 应用到其底层
-- 关系 toDiscrete Q。振幅不起作用。

base→phys : BaseLift → PhysLift
base→phys L X S Q Obs step obs-map {x} {y} p =
  L X (toDiscrete Q) Obs step obs-map {x} {y} p

------------------------------------------------------------------------
-- Direction: a physical lift yields a base lift
--
-- Given a physical lift P, the base lift on a relation rel is obtained
-- by decorating rel with the trivial amplitude into a QuantumLayer and
-- applying P. The underlying relation is unchanged definitionally, so
-- the two lifts agree at every point.
--
-- 方向：物理提升给出基础提升
--
-- 给定物理提升 P，关系 rel 上的基础提升通过把 rel 装饰为平凡振幅
-- 得到 QuantumLayer 并应用 P 获得。底层关系定义性地不变，故两个
-- 提升在每一点上一致。

phys→base : PhysLift → BaseLift
phys→base P X rel Obs step obs-map {x} {y} p =
  P X (⊤ {lzero}) (ofDiscrete rel (λ _ _ _ → tt))
    Obs step obs-map {x} {y} p

------------------------------------------------------------------------
-- Separation lemmas interderive
--
-- 分离引理互推

base-sep→phys-sep : BaseSep → PhysSep
base-sep→phys-sep base-sep p = base-sep (phys→base p)

phys-sep→base-sep : PhysSep → BaseSep
phys-sep→base-sep phys-sep q = phys-sep (base→phys q)
