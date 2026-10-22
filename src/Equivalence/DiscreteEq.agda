------------------------------------------------------------------------
-- Degeneration
--
-- Drop next. No recursion, no observation family, only the current-layer
-- relation. The mathematical content is the theory of binary relations,
-- organised into RelationAlgebra, GaloisConnection, Symmetrisation, and
-- Fixpoint.
--
-- 退化
--
-- 去掉 next。没有递归、没有观察族，只有当前层关系。数学内容是二元
-- 关系理论，组织为 RelationAlgebra、GaloisConnection、Symmetrisation
-- 与 Fixpoint。
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module Equivalence.DiscreteEq where

open import Agda.Primitive using (_⊔_; Level)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Sigma using (Σ; _,_)
open import Data.Product.Base using (_×_)
open import Relation.Binary.Structures using (IsEquivalence; IsPreorder)

------------------------------------------------------------------------
-- DiscreteEq
--
-- The base layer relation, marking the "drop next" position of the
-- degeneration lattice.
--
-- 基础 layer 关系的别名，标记退化格的“去掉 next”位置。

DiscreteEq : {a d : Level} {X : Set a} → (layer : X → X → Set d)
           → X → X → Set d
DiscreteEq layer x y = layer x y

------------------------------------------------------------------------
-- Relation algebra
--
-- 关系代数

module RelationAlgebra
    {a d : Level} {X : Set a} where

  _⊆_ : {d₁ d₂ : Level}
      → (X → X → Set d₁) → (X → X → Set d₂) → Set (a ⊔ d₁ ⊔ d₂)
  R ⊆ S = ∀ {x y} → R x y → S x y

  Id : X → X → Set a
  Id x y = x ≡ y

  -- R ∘ S means "first S, then R", matching function composition.
  --
  -- R ∘ S 表示“先 S 后 R”，与函数复合一致。
  infixr 19 _∘_
  _∘_ : {d₁ d₂ : Level}
      → (X → X → Set d₂) → (X → X → Set d₁) → X → X → Set (a ⊔ d₁ ⊔ d₂)
  (R ∘ S) x z = Σ X (λ y → S x y × R y z)

  infix 25 _⁻¹
  _⁻¹ : {d₁ : Level} → (X → X → Set d₁) → X → X → Set d₁
  R ⁻¹ = λ x y → R y x

  ∘-assoc : (R S T : X → X → Set d)
          → ((R ∘ S) ∘ T) ⊆ (R ∘ (S ∘ T))
  ∘-assoc R S T (y , Txy , (z , Syz , Rzw)) = z , ((y , Txy , Syz) , Rzw)

  ∘-assoc' : (R S T : X → X → Set d)
           → (R ∘ (S ∘ T)) ⊆ ((R ∘ S) ∘ T)
  ∘-assoc' R S T (z , ((y , Txy , Syz) , Rzw)) = y , Txy , (z , Syz , Rzw)

  Id-left : (R : X → X → Set d) → (Id ∘ R) ⊆ R
  Id-left R (y , Rxy , refl) = Rxy

  Id-right : (R : X → X → Set d) → (R ∘ Id) ⊆ R
  Id-right R (y , refl , Ryz) = Ryz

  ⁻¹-invol : (R : X → X → Set d) → ((R ⁻¹) ⁻¹) ⊆ R
  ⁻¹-invol R p = p

  ⁻¹-invol' : (R : X → X → Set d) → R ⊆ ((R ⁻¹) ⁻¹)
  ⁻¹-invol' R p = p

  ⁻¹-∘ : (R S : X → X → Set d)
       → ((R ∘ S) ⁻¹) ⊆ (S ⁻¹ ∘ R ⁻¹)
  ⁻¹-∘ R S (y , Swy , Ryx) = y , Ryx , Swy

  ⁻¹-∘' : (R S : X → X → Set d)
        → (S ⁻¹ ∘ R ⁻¹) ⊆ ((R ∘ S) ⁻¹)
  ⁻¹-∘' R S (y , Ryx , Swy) = y , Swy , Ryx

  Symmetric : (R : X → X → Set d) → Set (a ⊔ d)
  Symmetric R = R ⊆ R ⁻¹

  Transitive : (R : X → X → Set d) → Set (a ⊔ d)
  Transitive R = (R ∘ R) ⊆ R

  Reflexive : (R : X → X → Set d) → Set (a ⊔ d)
  Reflexive R = Id ⊆ R

  reflexive-symmetric-transitive→equivalence
    : (R : X → X → Set d)
    → Reflexive R → Symmetric R → Transitive R
    → IsEquivalence R
  reflexive-symmetric-transitive→equivalence R refl-R sym-R trans-R = record
    { refl  = λ {x} → refl-R refl
    ; sym   = λ {x} {y} → sym-R
    ; trans = λ {x} {y} {z} p q → trans-R (y , p , q)
    }

------------------------------------------------------------------------
-- Galois connections
--
-- The order-theoretic analogue of _⊣_, replacing round-trip equalities
-- by a pair of adjunctions f ⊣ g iff f x ⊑ y ⟺ x ≤ g y.
--
-- _⊣_ 的序论类比，把往返等式替换为一对伴随 f ⊣ g，
-- 即 f x ⊑ y ⟺ x ≤ g y。

module GaloisConnection
    {a b d e : Level} {X : Set a} {Y : Set b}
    (_≤_ : X → X → Set d) (_⊑_ : Y → Y → Set e) where

  record Galois (f : X → Y) (g : Y → X) : Set (a ⊔ b ⊔ d ⊔ e) where
    field
      adj   : ∀ {x y} → f x ⊑ y → x ≤ g y
      coadj : ∀ {x y} → x ≤ g y → f x ⊑ y

  open Galois public

  module ClosureProperties
      (≤-refl  : ∀ x → x ≤ x)
      (≤-trans : ∀ {x y z} → x ≤ y → y ≤ z → x ≤ z)
      (⊑-refl  : ∀ y → y ⊑ y)
      (⊑-trans : ∀ {x y z} → x ⊑ y → y ⊑ z → x ⊑ z)
      (f : X → Y) (g : Y → X)
      (gal : Galois f g) where

    g-mono : ∀ {y y'} → y ⊑ y' → g y ≤ g y'
    g-mono {y} {y'} y⊑y' =
      Galois.adj gal
        (⊑-trans (Galois.coadj gal (≤-refl (g y))) y⊑y')

    f-mono : ∀ {x x'} → x ≤ x' → f x ⊑ f x'
    f-mono {x} {x'} x≤x' =
      Galois.coadj gal
        (≤-trans x≤x' (Galois.adj gal (⊑-refl (f x'))))

    -- Closure operator c = g ∘ f.
    --
    -- 闭包算子 c = g ∘ f。
    c : X → X
    c = λ x → g (f x)

    c-extensive : ∀ x → x ≤ c x
    c-extensive x = Galois.adj gal (⊑-refl (f x))

    c-idempotent : ∀ x → c (c x) ≤ c x
    c-idempotent x = g-mono (Galois.coadj gal (≤-refl (c x)))

    c-mono : ∀ {x x'} → x ≤ x' → c x ≤ c x'
    c-mono {x} {x'} x≤x' = g-mono (f-mono x≤x')

------------------------------------------------------------------------
-- Symmetrisation
--
-- Sym x y = (x ≤ y) × (y ≤ x) is an equivalence relation and the
-- largest symmetric subrelation of ≤.
--
-- Sym x y = (x ≤ y) × (y ≤ x) 是等价关系，并且是 ≤ 的最大对称子关系。

module Symmetrisation
    {a d : Level} {X : Set a}
    (_≤_ : X → X → Set d) where

  Sym : X → X → Set d
  Sym x y = (x ≤ y) × (y ≤ x)

  sym-refl : (∀ x → x ≤ x) → ∀ x → Sym x x
  sym-refl refl-≤ x = refl-≤ x , refl-≤ x

  sym-sym : ∀ {x y} → Sym x y → Sym y x
  sym-sym (p , q) = q , p

  sym-trans : (∀ {x y z} → x ≤ y → y ≤ z → x ≤ z)
            → ∀ {x y z} → Sym x y → Sym y z → Sym x z
  sym-trans trans-≤ (p₁ , p₂) (q₁ , q₂) =
    trans-≤ p₁ q₁ , trans-≤ q₂ p₂

  sym-isEquivalence : IsPreorder _≡_ _≤_ → IsEquivalence Sym
  sym-isEquivalence pre = record
    { refl  = λ {x} → sym-refl (λ y → IsPreorder.refl pre) x
    ; sym   = sym-sym
    ; trans = sym-trans (IsPreorder.trans pre)
    }

  sym-universal
    : (R : X → X → Set d)
    → (∀ {x y} → R x y → R y x)
    → (∀ {x y} → R x y → x ≤ y)
    → ∀ {x y} → R x y → Sym x y
  sym-universal R sym-R R⊆≤ p = R⊆≤ p , R⊆≤ (sym-R p)

------------------------------------------------------------------------
-- Fixed points
--
-- Every fixed point x is Sym-related to its image c x, since c x ≤ x
-- (fixed) and x ≤ c x (extensive).
--
-- 每个不动点 x 与其像 c x 在 Sym 意义下等价，因为 c x ≤ x（不动点）
-- 且 x ≤ c x（扩张性）。

module Fixpoint
    {a d : Level} {X : Set a}
    (_≤_ : X → X → Set d)
    (c : X → X) where

  record IsClosureOperator : Set (a ⊔ d) where
    field
      extensive  : ∀ x → x ≤ c x
      monotone   : ∀ {x y} → x ≤ y → c x ≤ c y
      idempotent : ∀ x → c (c x) ≤ c x

  open IsClosureOperator public

  IsFixed : X → Set d
  IsFixed x = c x ≤ x

  fixed-stable : IsClosureOperator → ∀ x → IsFixed (c x)
  fixed-stable co x = IsClosureOperator.idempotent co x

  fixed-closed
    : IsClosureOperator → ∀ x
    → IsFixed x → Symmetrisation.Sym _≤_ (c x) x
  fixed-closed co x fixed = fixed , IsClosureOperator.extensive co x

  FixedRel : X → X → Set d
  FixedRel x y = IsFixed x × IsFixed y

------------------------------------------------------------------------
-- Bridge
--
-- The closure operator induced by a Galois connection is a closure
-- operator in the sense of Fixpoint. Formal support for the arrow
-- GaloisConnection → Fixpoint in the degeneration diagram.
--
-- Galois 连接诱导的闭包算子是 Fixpoint 意义下的闭包算子。
-- 这是退化图中 GaloisConnection → Fixpoint 箭头的形式化支撑。

module GaloisFixpointBridge
    {a b d e : Level} {X : Set a} {Y : Set b}
    (_≤_ : X → X → Set d) (_⊑_ : Y → Y → Set e)
    (≤-refl  : ∀ x → x ≤ x)
    (≤-trans : ∀ {x y z} → x ≤ y → y ≤ z → x ≤ z)
    (⊑-refl  : ∀ y → y ⊑ y)
    (⊑-trans : ∀ {x y z} → x ⊑ y → y ⊑ z → x ⊑ z)
    (f : X → Y) (g : Y → X)
    (gal : GaloisConnection.Galois _≤_ _⊑_ f g) where

  open GaloisConnection _≤_ _⊑_
  module CP = ClosureProperties ≤-refl ≤-trans ⊑-refl ⊑-trans f g gal
  module FP = Fixpoint _≤_ CP.c

  galois-c-is-closure : FP.IsClosureOperator
  galois-c-is-closure = record
    { extensive  = CP.c-extensive
    ; monotone   = CP.c-mono
    ; idempotent = CP.c-idempotent
    }

------------------------------------------------------------------------
-- Solid arrows: formally established degeneration.
-- Dashed grouping: shared preorder structure.
--
-- 实线箭头：已形式化的退化。
-- 分组虚线：共享预序结构。
--
--                    LayeredEqGen
--                         │
--                         │ drop next
--                         ↓
--                    DiscreteEq
--                         │
--         ┌───────────────┼───────────────┐
--         │               │               │
--         │ relations     │ preorders     │ symmetrisation
--         ↓               ↓               ↓
--   RelationAlgebra  GaloisConnection  Symmetrisation
--                         │               ↑
--                         │ c = g ∘ f     │
--                         ↓               │
--                      Fixpoint ──────────┘
--                         ↑
--                         │ galois-c-is-closure
--                    (bridge module)
