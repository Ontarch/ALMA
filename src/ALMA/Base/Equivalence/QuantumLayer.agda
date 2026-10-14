------------------------------------------------------------------------
-- Quantum layer: DiscreteEq with amplitude decoration
--
-- A quantum transition carries, alongside its underlying discrete
-- relation, a scalar amplitude on each related pair. This module
-- packages that structure, and the conservation predicate that
-- qualifies a decoration as a quantum corner: the amplitudes must
-- sum to one along every input's output set.
--
-- 量子层：带振幅装饰的 DiscreteEq
--
-- 量子转移在底层离散关系之外，在每对相关状态上携带标量振幅。本模块
-- 打包该结构，以及使装饰成为量子角的守恒谓词：沿每个输入的输出集，
-- 振幅求和为一。
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module ALMA.Base.Equivalence.QuantumLayer where

open import Agda.Primitive using (Level; _⊔_; lsuc)
open import Data.Nat.Base using (ℕ)
open import Data.Fin.Base using (Fin)
open import Data.Product.Base using (Σ; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import ALMA.Base.Equivalence.DiscreteEq using (DiscreteEq)

------------------------------------------------------------------------
-- The structure
--
-- 结构

record QuantumLayer {a s : Level} (X : Set a) (Scalar : Set s)
    : Set (a ⊔ lsuc s) where
  field
    layer : X → X → Set s
    amp   : (x y : X) → layer x y → Scalar

open QuantumLayer

------------------------------------------------------------------------
-- Conservation predicate
--
-- A QuantumLayer is conservation-qualified when each input has a
-- finite output set whose amplitudes sum to one. Input selects which
-- states carry an output obligation; Sum and One abstract the scalar
-- algebra.
--
-- 守恒谓词
--
-- 当每个输入都有一个有限输出集、其上振幅求和为一时，QuantumLayer
-- 是守恒合格的。Input 选出承担输出义务的状态；Sum 与 One 抽象标量
-- 代数。

record IsConservative {a s : Level} {X : Set a} {Scalar : Set s}
                      (Q : QuantumLayer X Scalar)
                      (Input : X → Set a)
                      (Sum : (n : ℕ) → (Fin n → Scalar) → Scalar)
                      (One : Scalar) : Set (a ⊔ s) where
  field
    outputs  : (x : X) (ix : Input x) → ℕ
    index    : (x : X) (ix : Input x) → Fin (outputs x ix) → X
    reach    : (x : X) (ix : Input x) (i : Fin (outputs x ix))
             → layer Q x (index x ix i)
    sum-one  : (x : X) (ix : Input x)
             → Sum (outputs x ix)
                    (λ i → amp Q x (index x ix i) (reach x ix i))
               ≡ One

open IsConservative

------------------------------------------------------------------------
-- Projection to DiscreteEq
--
-- The underlying discrete relation: the amplitude decoration is
-- forgotten.
--
-- 投影到 DiscreteEq
--
-- 底层离散关系：忘掉振幅装饰。

toDiscrete : ∀ {a s} {X : Set a} {Scalar : Set s}
           → QuantumLayer X Scalar → X → X → Set s
toDiscrete Q = layer Q

------------------------------------------------------------------------
-- Trivial decoration
--
-- Every DiscreteEq layer lifts to a QuantumLayer by giving every
-- related pair an amplitude.
--
-- 平凡装饰
--
-- 每个 DiscreteEq 层通过给每个相关对一个振幅提升为 QuantumLayer。

ofDiscrete : ∀ {a s} {X : Set a} {Scalar : Set s}
           → (rel : X → X → Set s)
           → ((x y : X) → rel x y → Scalar)
           → QuantumLayer X Scalar
ofDiscrete rel a = record { layer = rel ; amp = a }

------------------------------------------------------------------------
-- Equivalent Σ-form
--
-- A QuantumLayer is exactly a DiscreteEq layer together with an
-- amplitude function. The round trips below are definitional.
--
-- 等价的 Σ-形式
--
-- QuantumLayer 精确地是 DiscreteEq 层加上振幅函数。下面的往返是
-- 定义性的。

toSigma : ∀ {a s} {X : Set a} {Scalar : Set s}
        → QuantumLayer X Scalar
        → Σ (X → X → Set s) (λ rel → (x y : X) → rel x y → Scalar)
toSigma Q = layer Q , amp Q

fromSigma : ∀ {a s} {X : Set a} {Scalar : Set s}
          → Σ (X → X → Set s) (λ rel → (x y : X) → rel x y → Scalar)
          → QuantumLayer X Scalar
fromSigma (rel , a) = record { layer = rel ; amp = a }

to-from : ∀ {a s} {X : Set a} {Scalar : Set s}
          (Q : QuantumLayer X Scalar)
        → fromSigma (toSigma Q) ≡ Q
to-from Q = refl

from-to : ∀ {a s} {X : Set a} {Scalar : Set s}
          (p : Σ (X → X → Set s) (λ rel → (x y : X) → rel x y → Scalar))
        → toSigma (fromSigma p) ≡ p
from-to p = refl
