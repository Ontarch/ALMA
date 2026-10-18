{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module Everything where

import ALMA.Base.IndexedMType
import ALMA.Base.MCategory
import ALMA.Base.MCorr  -- Carried correspondence kernel / 携带式对应内核
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
import ALMA.Base.Equivalence.QuantumLayer
import ALMA.Base.Equivalence.Lattice
import ALMA.Base.Equivalence.StrongEquiv

import ALMA.Base.Real
import ALMA.Base.Real.Sequence
import ALMA.Base.Real.Neighborhood
import ALMA.Base.Real.Interval
import ALMA.Base.Real.Interval.Rational
import ALMA.Base.Real.IntervalEquiv
import ALMA.Base.Real.CauchyToInterval
import ALMA.Base.Real.Interval.Reasoning
import ALMA.Base.Real.Interval.Equiv
import ALMA.Base.Real.Interval.Kit
import ALMA.Base.Real.Interval.Arith
import ALMA.Base.Real.Interval.Mul
import ALMA.Base.Real.Interval.Node
import ALMA.Base.Real.Interval.Order
import ALMA.Base.Real.Interval.Bounded
import ALMA.Base.Real.Interval.Abs
import ALMA.Base.Real.Interval.ArithLaws
import ALMA.Base.Real.Interval.MulLaws
import ALMA.Base.Real.Interval.OrderLaws
import ALMA.Base.Real.Interval.MulOrder
import ALMA.Base.Real.Interval.Recip
import ALMA.Base.Real.Interval.Complete
import ALMA.Base.Real.Interval.Inverse

import ALMA.Physics.RationalKit
import ALMA.Physics.CausalOrder
import ALMA.Physics.CausalSlice
import ALMA.Physics.CausalSet
import ALMA.Physics.CausalSetOrder
import ALMA.Physics.CausalCurvature
import ALMA.Physics.EinsteinAction
import ALMA.Physics.FourDAction

import ALMA.Physics.Spacetime.LorentzForm
import ALMA.Physics.Spacetime.LorentzGroup
import ALMA.Physics.Spacetime.Clifford

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

import ALMA.Physics.LatticeCoherence
import ALMA.Physics.Lattice

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
import ALMA.SecondPass.ShiftedTower
import ALMA.SecondPass.FinCatInfinitySubstitution
import ALMA.SecondPass.FinCatInfinityProjectionUnfold
import ALMA.SecondPass.FinCatInfinitySubCocone
import ALMA.SecondPass.FinCatInfinityMediate
import ALMA.SecondPass.FinCatInfinityMediateUniqueness
import ALMA.SecondPass.FinCatInfinityEndomorphismCandidates
import ALMA.SecondPass.FinCatInfinitySubstDstSelf

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
import ALMA.Prototype.Properties.SubstCore
import ALMA.Prototype.Properties.Transport
import ALMA.Prototype.Properties.Equiv
import ALMA.Prototype.Properties.Composition
import ALMA.Prototype.Properties.CongBase
-- import ALMA.Prototype.Properties.Cong  -- comp-cong-≃⇒ℱ.onunfold-eq is a hole;
                                          -- excluded from CI
                                          -- comp-cong-≃⇒ℱ.onunfold-eq 是洞；
                                          -- 从 CI 排除
import ALMA.Prototype.Properties.MorphLift
import ALMA.Prototype.Properties.Bisim
import ALMA.Prototype.Properties.Dynamics
import ALMA.Prototype.Indestructibility
import ALMA.Prototype.Beings
import ALMA.Prototype.Universe
import ALMA.Prototype.StandardModel
