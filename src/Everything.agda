{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module Everything where

import ALMA.Base.IndexedMType
import ALMA.Base.MCategory
import ALMA.Base.MCorr  -- Carried correspondence kernel (zero subst / cast)
                        -- 携带式对应内核（零 subst / cast）
import ALMA.Base.MCorrSetoid
import ALMA.Base.MCorrSetoidCat
import ALMA.Base.DetCat
import ALMA.Base.MCorrSetoidCoalg
import ALMA.Base.SetoidColimit
import ALMA.Base.MCorrSetoidPush
import ALMA.Base.MCorrSetoidPushMap
import ALMA.Base.MCorrSetoidPushComp
import ALMA.Base.MCorrSetoidPushCat
import ALMA.Base.RelEquipment
import ALMA.Base.MCorrTerminalSequence
import ALMA.Base.MCorrInitialAlgebra
import ALMA.Base.WContainerInstance

import ALMA.Base.Equivalence
import ALMA.Base.Equivalence.Core
import ALMA.Base.Equivalence.SubstTransport
import ALMA.Base.Equivalence.Properties
import ALMA.Base.Equivalence.LayeredEqGenDepth
import ALMA.Base.Equivalence.Map
import ALMA.Base.Equivalence.ScaleInvariant
import ALMA.Base.Equivalence.DiscreteEq
import ALMA.Base.Equivalence.GroupInvariant
import ALMA.Base.Equivalence.LinearDynamics
import ALMA.Base.Equivalence.TopologicalEq
import ALMA.Base.Equivalence.ManifoldEq
import ALMA.Base.Equivalence.Lattice
import ALMA.Base.Equivalence.StrongEquiv

import ALMA.Physics.RationalKit
import ALMA.Physics.CausalOrder
import ALMA.Physics.CausalSlice
import ALMA.Physics.Spacetime.LorentzForm
import ALMA.Physics.Spacetime.LorentzGroup
import ALMA.Physics.Quantum.Gaussian
import ALMA.Physics.Quantum.FiniteVec
import ALMA.Physics.Quantum.Measurement
import ALMA.Physics.Quantum.Stochastic
import ALMA.Physics.Quantum.Rotation
import ALMA.Physics.Quantum.AmplitudeComp
import ALMA.Physics.Quantum.UnitaryInstrument
import ALMA.Physics.Newton.Poisson
import ALMA.Physics.Newton.Quadratic
import ALMA.Physics.Newton.QuadraticBilinear
import ALMA.Physics.Newton.QuadraticSkew
import ALMA.Physics.Newton.QuadraticJacobi
import ALMA.Physics.Newton.DegreeBoundary

import ALMA.Cosmos
import ALMA.Cosmos.ContCategory
import ALMA.Cosmos.ContCategoryLemmas
import ALMA.Cosmos.ContFunctor
import ALMA.Cosmos.ContCatEquiv

import ALMA.Cosmos.M.Object
import ALMA.Cosmos.M.ContainerInstance
import ALMA.Cosmos.M.Terminal
import ALMA.Cosmos.M.CoalgCat
import ALMA.Cosmos.M.Lambek
import ALMA.Cosmos.M.CosmosCategory
import ALMA.Cosmos.M.DetCongruence
import ALMA.Cosmos.M.GenCongruence
import ALMA.Cosmos.M.ListCosmos
import ALMA.Cosmos.M.ListSwap
import ALMA.Cosmos.M.ListSwapDef
import ALMA.Cosmos.M.MorphismCorrespondence
import ALMA.Cosmos.M.ContainerAutomorphism
import ALMA.Cosmos.M.PermutationNonCommutative
import ALMA.Cosmos.M.PermutedEmbedding
import ALMA.Cosmos.M.TowerSeparation
import ALMA.Cosmos.M.NontrivialLimit
import ALMA.Cosmos.M.SewingObstruction

import ALMA.Cosmos.Carried.FinNatUIP
import ALMA.Cosmos.Carried.DetSys
import ALMA.Cosmos.Carried.TrivProj
import ALMA.Cosmos.Carried.FinProj
import ALMA.Cosmos.Carried.SeqColimit
import ALMA.Cosmos.Carried.LimitSystem
import ALMA.Cosmos.Carried.FinEmbed
import ALMA.Cosmos.Carried.FinColimit
import ALMA.Cosmos.Carried.FinTower
import ALMA.Cosmos.Carried.DetColimit
import ALMA.Cosmos.Carried.Boundaries

import ALMA.Cosmos.Carried.SeqColimitS
import ALMA.Cosmos.Carried.SeqColimitCat
import ALMA.Cosmos.Carried.ColimitPolarity
import ALMA.Cosmos.Carried.LimitSystemS
import ALMA.Cosmos.Carried.FinPushMediateS
import ALMA.Cosmos.Carried.FinPushColimitS
import ALMA.Cosmos.Carried.FinPushColimitCat

import ALMA.Cosmos.Carried.SameIndexCatS
import ALMA.Cosmos.Carried.SameIndexColimitS
import ALMA.Cosmos.Carried.NontrivialPullTowerS
import ALMA.Cosmos.Carried.NontrivialPushTowerS
import ALMA.Cosmos.Carried.ChainColimitPropS

------------------------------------------------------------------------
-- Frozen archives
-- The ontological root of subst: when A is essentially determined by B
-- at parameter p₀, yet is expressed independently, the misalignment
-- between A's self-contained appearance and its instance-position
-- must manifest as subst at every point of connection between A and B.
--
-- 冻结存档
-- subst 的本体论根源：当 A 本质上由 B 在参数 p₀ 处决定，却被独立表达时，
-- A 的自足外观与其实例位置之间的错位，必然在 A 与 B 的每个连接点上以 subst
-- 的形式显露。

import ALMA.SecondPass.ContCatEquivFunctor
import ALMA.SecondPass.Unfolding
import ALMA.SecondPass.MorphismObject
import ALMA.SecondPass.MorphismObject.Covariant
import ALMA.SecondPass.MorphismObject.MorphismObject
import ALMA.SecondPass.ContCatEquivLemmas
import ALMA.SecondPass.MorphismMorphism
import ALMA.SecondPass.Cosmos
import ALMA.SecondPass.Terminal
import ALMA.SecondPass.CoalgCat
import ALMA.SecondPass.Lambek
import ALMA.SecondPass.CosmosCategory
import ALMA.SecondPass.MorphismCorrespondence
import ALMA.SecondPass.Closure
import ALMA.SecondPass.ContainerAutomorphism
import ALMA.SecondPass.ListCosmos
import ALMA.SecondPass.CumulativeHierarchy
import ALMA.SecondPass.CumulativeHierarchyInner
import ALMA.SecondPass.StrictLift
import ALMA.SecondPass.StrictLiftShape
import ALMA.SecondPass.CumulativeHierarchyInstances
import ALMA.SecondPass.CumulativeHierarchyLimit
import ALMA.SecondPass.CumulativeHierarchySewing
import ALMA.SecondPass.FinCatNInnerSewing
import ALMA.SecondPass.FinCatNWitness
import ALMA.SecondPass.FinCatNTowerLemmas
import ALMA.SecondPass.ConditionalNontrivialLimit
import ALMA.SecondPass.LayerZeroMediator
import ALMA.SecondPass.FinCatNColimit
import ALMA.SecondPass.FinCatNEmbeddingMismatch
import ALMA.SecondPass.DependentEmbedding
import ALMA.SecondPass.FinCatNColimitWithDep
import ALMA.SecondPass.FinCatNSurjectivity
import ALMA.SecondPass.FinCatNDefaultUnif
import ALMA.SecondPass.FinCatNFunctorial
import ALMA.SecondPass.FinCatNProjectiveObstruction
import ALMA.SecondPass.FinCatNOuterObstruction
import ALMA.SecondPass.FinCatNInnerObstruction
import ALMA.SecondPass.FinCatNPermutedEmbedding
import ALMA.SecondPass.FinCatNNonCommutative
import ALMA.SecondPass.FinCatInfinity
import ALMA.SecondPass.FinCatInfinityProjection
import ALMA.SecondPass.FinCatInfinityTowerCompat
import ALMA.SecondPass.FinCatInfinityColimit
import ALMA.SecondPass.FinCatInfinityColimitUniversal
import ALMA.SecondPass.Instances
-- import ALMA.SecondPass.WIP  -- uniqueness blocked at FMap/⇒ℱX layer
                               -- 唯一性在 FMap/⇒ℱX 层受阻

import ALMA.InitialPass.ObjEquivCat
import ALMA.InitialPass.ObjEquivFunctor
import ALMA.InitialPass.ContCategory
import ALMA.InitialPass.ContCategoryLemmas
import ALMA.InitialPass.ContCatEquiv
import ALMA.InitialPass.ContCatEquivFunctor
import ALMA.InitialPass.Unfolding
import ALMA.InitialPass.MorphismObject
import ALMA.InitialPass.ContCatEquivLemmas
import ALMA.InitialPass.MorphismMorphism
import ALMA.InitialPass.Cosmos

import ALMA.Prototype.Prelude
import ALMA.Prototype.Cosmos
import ALMA.Prototype.Indestructibility
import ALMA.Prototype.Beings
import ALMA.Prototype.Universe
import ALMA.Prototype.StandardModel
-- import ALMA.Prototype.Properties  -- comp-cong-≃⇒ℱ hit a subst coherence
                                     -- obstruction and was left as a hole,
                                     -- excluded from CI
                                     -- comp-cong-≃⇒ℱ 撞上 subst 相干性障碍，
                                     -- 留为洞，从 CI 排除
