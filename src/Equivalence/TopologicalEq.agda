------------------------------------------------------------------------
-- Degeneration: DiscreteEq under a topology
--
-- TopologicalEq is DiscreteEq at the same-opens layer induced by a
-- topology; it sits on the "drop next-eq" branch of the degeneration
-- lattice. The same-opens relation is the symmetrisation of the
-- specialisation order _≤ₛ_: two points are topologically
-- indistinguishable when every open treats them equally.
--
-- 退化：拓扑下的 DiscreteEq
--
-- TopologicalEq 是拓扑诱导的相同开集 layer 处的 DiscreteEq，位于
-- 退化格的“去掉 next-eq”分支上。相同开集关系是特化序 _≤ₛ_ 的对称化：
-- 两点拓扑不可区分，当且仅当每个开集同等对待它们。
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module Equivalence.TopologicalEq where

open import Agda.Primitive using (lsuc)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Sigma using (Σ; _,_)
open import Data.Product.Base using (_×_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality.Core using (sym; trans; subst)
open import Relation.Binary.Structures using (IsEquivalence; IsPreorder)

open import Equivalence.DiscreteEq using (DiscreteEq; module Symmetrisation)

------------------------------------------------------------------------
-- Minimal topology
--
-- A family of opens together with a membership relation. The full
-- topological axioms (finite intersections, arbitrary unions) are not
-- needed below.
--
-- 最小拓扑
--
-- 开集族与成员关系。下面的定理不需要完整的拓扑公理
-- （有限交、任意并）。

record TopologyStructure {a} (X : Set a) : Set (lsuc a) where
  field
    Open : Set a
    _∈_  : X → Open → Set a

open TopologyStructure public

------------------------------------------------------------------------
-- Specialisation order
--
-- Defined before TopologicalEq so that same-opens can be obtained by
-- reuse of the generic Symmetrisation module.
--
-- 特化序
--
-- 先于 TopologicalEq 定义，使 same-opens 可复用通用 Symmetrisation
-- 模块得到。

module _ {a} {X : Set a} (𝒯 : TopologyStructure X) where
  private
    module 𝒯 = TopologyStructure 𝒯

  _≤ₛ_ : X → X → Set a
  x ≤ₛ y = ∀ U → 𝒯._∈_ x U → 𝒯._∈_ y U

  ≤ₛ-refl : ∀ x → x ≤ₛ x
  ≤ₛ-refl x U x∈U = x∈U

  ≤ₛ-trans : ∀ {x y z} → x ≤ₛ y → y ≤ₛ z → x ≤ₛ z
  ≤ₛ-trans p q U x∈U = q U (p U x∈U)

  ≤ₛ-isPreorder : IsPreorder _≡_ _≤ₛ_
  ≤ₛ-isPreorder = record
    { isEquivalence = record
      { refl  = λ {x} → refl
      ; sym   = λ {x} {y} → sym
      ; trans = λ {x} {y} {z} → trans
      }
    ; reflexive = λ {x} {y} x≡y U x∈U → subst (λ z → 𝒯._∈_ z U) x≡y x∈U
    ; trans     = ≤ₛ-trans
    }

------------------------------------------------------------------------
-- TopologicalEq
--
-- DiscreteEq at the symmetrisation of _≤ₛ_. The equivalence relation
-- comes from sym-isEquivalence applied to ≤ₛ-isPreorder.
--
-- TopologicalEq
--
-- _≤ₛ_ 对称化处的 DiscreteEq。等价关系由 sym-isEquivalence 应用于
-- ≤ₛ-isPreorder 得到。

module TopologicalEq
    {a} {X : Set a}
    (𝒯 : TopologyStructure X)
  where

  same-opens : X → X → Set a
  same-opens = Symmetrisation.Sym (_≤ₛ_ 𝒯)

  TopologicalEq : X → X → Set a
  TopologicalEq = DiscreteEq same-opens

  TopologicalEq-eq : ∀ {x y} → TopologicalEq x y → same-opens x y
  TopologicalEq-eq p = p

  TopologicalEq-intro : ∀ {x y} → same-opens x y → TopologicalEq x y
  TopologicalEq-intro p = p

  top-isEquivalence : IsEquivalence TopologicalEq
  top-isEquivalence =
    Symmetrisation.sym-isEquivalence (_≤ₛ_ 𝒯) (≤ₛ-isPreorder 𝒯)

open TopologicalEq public

------------------------------------------------------------------------
-- TopologicalEq-Math
--
-- T0 characterisation, maximality of same-opens among symmetric
-- subrelations, and preservation under continuous maps.
--
-- TopologicalEq-Math
--
-- T0 刻画、same-opens 在对称子关系中的最大性、连续映射下的保持性。

module TopologicalEq-Math
    {a} {X : Set a} {Y : Set a}
    (𝒯X : TopologyStructure X)
    (𝒯Y : TopologyStructure Y)
  where

  module TX = TopologicalEq 𝒯X
  module TY = TopologicalEq 𝒯Y
  module SX = TopologyStructure 𝒯X
  module SY = TopologyStructure 𝒯Y

  -- Plain function names, avoiding the parsing issue caused by mixing
  -- symbol and letter characters in an infix alias.
  --
  -- 普通函数名，避免中缀别名中符号与字母混合导致的解析问题。
  private
    leqX : X → X → Set a
    leqX = _≤ₛ_ 𝒯X

    leqY : Y → Y → Set a
    leqY = _≤ₛ_ 𝒯Y

  ----------------------------------------------------------------------
  -- T0 characterisation
  --
  -- Indistinguishability collapses to equality iff the specialisation
  -- order is antisymmetric.
  --
  -- T0 刻画
  --
  -- 不可区分性塌缩为相等，当且仅当特化序反对称。

  T0 : Set a
  T0 = ∀ x y → TX.TopologicalEq x y → x ≡ y

  ≤ₛ-antisym : Set a
  ≤ₛ-antisym = ∀ {x y} → leqX x y → leqX y x → x ≡ y

  T0→≤ₛ-antisym : T0 → ≤ₛ-antisym
  T0→≤ₛ-antisym t0 p q = t0 _ _ (TX.TopologicalEq-intro (p , q))

  ≤ₛ-antisym→T0 : ≤ₛ-antisym → T0
  ≤ₛ-antisym→T0 antisym x y p =
    antisym (proj₁ (TX.TopologicalEq-eq p))
            (proj₂ (TX.TopologicalEq-eq p))

  T0-iff-antisym : (T0 → ≤ₛ-antisym) × (≤ₛ-antisym → T0)
  T0-iff-antisym = T0→≤ₛ-antisym , ≤ₛ-antisym→T0

  T0-collapses : T0 → ∀ {x y} → TX.TopologicalEq x y → x ≡ y
  T0-collapses t0 p = t0 _ _ p

  ----------------------------------------------------------------------
  -- Maximality
  --
  -- same-opens is the largest symmetric subrelation of _≤ₛ_.
  --
  -- 最大性
  --
  -- same-opens 是 _≤ₛ_ 的最大对称子关系。

  module SymX = Symmetrisation leqX

  sym-sub-⊆-same-opens
    : (R : X → X → Set a)
    → (∀ {x y} → R x y → R y x)
    → (∀ {x y} → R x y → leqX x y)
    → ∀ {x y} → R x y → TX.TopologicalEq x y
  sym-sub-⊆-same-opens R sym-R R-⊆-leq p =
    TX.TopologicalEq-intro (R-⊆-leq p , R-⊆-leq (sym-R p))

  ----------------------------------------------------------------------
  -- Continuity
  --
  -- For every open U in Y there is an open V in X whose extension is
  -- exactly f⁻¹(U).
  --
  -- 连续性
  --
  -- 对 Y 中每个开集 U，存在 X 中开集 V，其外延恰为 f⁻¹(U)。

  Continuous : (X → Y) → Set a
  Continuous f =
    ∀ (U : SY.Open)
    → Σ SX.Open (λ V →
        ∀ z → (SX._∈_ z V → SY._∈_ (f z) U)
            × (SY._∈_ (f z) U → SX._∈_ z V))

  continuous-preserves-≤ₛ
    : (f : X → Y) → Continuous f
    → ∀ {x y} → leqX x y → leqY (f x) (f y)
  continuous-preserves-≤ₛ f cont {x} {y} p U fx∈U =
    let V , prf = cont U
        x∈V    = proj₂ (prf x) fx∈U
        y∈V    = p V x∈V
    in  proj₁ (prf y) y∈V

  continuous-preserves-indist
    : (f : X → Y) → Continuous f
    → ∀ {x y} → TX.TopologicalEq x y → TY.TopologicalEq (f x) (f y)
  continuous-preserves-indist f cont {x} {y} p =
    TY.TopologicalEq-intro
      ( continuous-preserves-≤ₛ f cont {x} {y}
          (proj₁ (TX.TopologicalEq-eq p))
      , continuous-preserves-≤ₛ f cont {y} {x}
          (proj₂ (TX.TopologicalEq-eq p)) )

------------------------------------------------------------------------
-- Identity map is continuous on any topology.
--
-- 恒等映射在任意拓扑上连续。

module TopologicalEq-Identity
    {a} {X : Set a}
    (𝒯X : TopologyStructure X)
  where

  module MXX = TopologicalEq-Math 𝒯X 𝒯X

  continuous-id : MXX.Continuous (λ x → x)
  continuous-id U = U , (λ x → (λ p → p) , (λ p → p))

------------------------------------------------------------------------
-- Composite of two continuous maps is continuous.
--
-- 两个连续映射的复合连续。

module TopologicalEq-Functorial
    {a} {X : Set a} {Y : Set a} {Z : Set a}
    (𝒯X : TopologyStructure X)
    (𝒯Y : TopologyStructure Y)
    (𝒯Z : TopologyStructure Z)
  where

  module MXY = TopologicalEq-Math 𝒯X 𝒯Y
  module MYZ = TopologicalEq-Math 𝒯Y 𝒯Z
  module MXZ = TopologicalEq-Math 𝒯X 𝒯Z

  continuous-∘
    : (f : X → Y) (g : Y → Z)
    → MXY.Continuous f → MYZ.Continuous g
    → MXZ.Continuous (λ x → g (f x))
  continuous-∘ f g cf cg U =
    let V , prf-V = cg U
        W , prf-W = cf V
    in  W ,
        ( λ x →
            ( λ x∈W → proj₁ (prf-V (f x)) (proj₁ (prf-W x) x∈W) )
          , ( λ gfx∈U → proj₂ (prf-W x) (proj₂ (prf-V (f x)) gfx∈U) ) )
