------------------------------------------------------------------------
-- Equivalence
--
-- The degeneration lattice of LayeredEq. The subsections list the
-- modules of this hierarchy, grouped by their role in the lattice.
--
-- 等价
--
-- LayeredEq 的退化格。各节列出本层级中的模块，按其在格中的角色分组。
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module Equivalence where

------------------------------------------------------------------------
-- Core
--
-- Centre of the lattice.
--
-- 核心
--
-- 格的中央。

open import Equivalence.Core public

------------------------------------------------------------------------
-- Layer relations and bridge
--
-- 同层关系与桥接

open import Equivalence.SubstTransport public

------------------------------------------------------------------------
-- Generic laws and preservation
--
-- 通用律与保持性

open import Equivalence.Properties public
open import Equivalence.LayeredEqGenDepth public
open import Equivalence.Map public

------------------------------------------------------------------------
-- Degeneration: ScaleInvariant
--
-- LayeredEq / trivial layer.
--
-- 退化：ScaleInvariant
--
-- LayeredEq / 平凡层。

open import Equivalence.ScaleInvariant public

------------------------------------------------------------------------
-- Degeneration: DiscreteEq
--
-- Drop next-eq.
--
-- 退化：DiscreteEq
--
-- 去掉 next-eq。

open import Equivalence.DiscreteEq public

------------------------------------------------------------------------
-- Further degenerations of ScaleInvariant
--
-- GroupInvariant is ScaleInvariant under a group action;
-- LinearDynamics is ScaleInvariant with no branching.
--
-- ScaleInvariant 的更深退化
--
-- GroupInvariant 是群作用下的 ScaleInvariant；
-- LinearDynamics 是无分支的 ScaleInvariant。

open import Equivalence.GroupInvariant public
open import Equivalence.LinearDynamics public

------------------------------------------------------------------------
-- Further degenerations of DiscreteEq
--
-- TopologicalEq is DiscreteEq under a topology; ManifoldEq is a
-- single-directional LayeredEqGen instance.
--
-- DiscreteEq 的更深退化
--
-- TopologicalEq 是拓扑下的 DiscreteEq；ManifoldEq 是单向的
-- LayeredEqGen 实例。

open import Equivalence.TopologicalEq public
open import Equivalence.ManifoldEq public

------------------------------------------------------------------------
-- Quantum decoration of DiscreteEq
--
-- QuantumLayer adds a scalar amplitude to each related pair of a
-- DiscreteEq layer, together with the conservation predicate that
-- qualifies the decoration.
--
-- DiscreteEq 的量子装饰
--
-- QuantumLayer 在 DiscreteEq 层的每对相关状态上添加标量振幅，并
-- 携带使装饰成为量子角的守恒谓词。

open import Equivalence.QuantumLayer public

------------------------------------------------------------------------
-- Lattice structure
--
-- Projections and joint projection.
--
-- 格结构
--
-- 投影与联合投影。

open import Equivalence.Lattice public

------------------------------------------------------------------------
-- Category-level bridge
--
-- 范畴层桥接

open import Equivalence.StrongEquiv public
