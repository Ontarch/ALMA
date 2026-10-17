------------------------------------------------------------------------
-- The degeneration lattice of physical theories
--
-- Newton, general relativity and quantum mechanics sit at corners of
-- the degeneration lattice of LayeredEqGen. The axes are the two
-- fields of LayeredEqGen: fst (layer) and snd (recursion). The
-- lattice is closed in both directions: forward projections carry
-- each corner to the corners below it, and separation lemmas show
-- the two projections are irreversible.
--
-- 物理理论的退化格
--
-- 牛顿、广义相对论与量子力学占据 LayeredEqGen 退化格的角。两轴即
-- LayeredEqGen 的两个字段：fst（layer）与 snd（递归）。格在两个方向
-- 上闭合：正向投影把每个角送到其下方的角，分离引理表明两个投影不可
-- 逆。
--
--                    keep next
--                        ↑
--       Newton           |   General relativity
--   (ScaleInvariant)     |   (LayeredEqGen)
--                        |
--   drop layer ←---------+---------→ keep layer
--                        |
--                        |   Quantum
--                        |   (DiscreteEq + amplitude)
--                        ↓
--                    drop next
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module ALMA.Physics.Lattice where

open import Agda.Primitive using (lzero)
open import Data.Unit.Polymorphic.Base using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Fin.Base using (Fin)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Rational.Base using (ℚ; 1ℚ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary.Negation.Core using (¬_)

open import ALMA.Base.IndexedMType using (Mᵢ; fst; snd)
open import ALMA.Base.Equivalence.Core using (LayeredEqGen)
open import ALMA.Base.Equivalence.ScaleInvariant using (ScaleInvariant)
open import ALMA.Base.Equivalence.LinearDynamics using (LinearDynamics)
open import ALMA.Base.Equivalence.DiscreteEq using (DiscreteEq)
open import ALMA.Base.Equivalence.ManifoldEq using (ManifoldStructure; module ManifoldEq)
open import ALMA.Base.Equivalence.QuantumLayer
  using (QuantumLayer; IsConservative; toDiscrete)

open import ALMA.Physics.Quantum.FiniteVec using (sumFin)
open import ALMA.Physics.Quantum.Gaussian using (norm²)
open import ALMA.Physics.Quantum.Stochastic using (Kernel)
open Kernel
open import ALMA.Physics.Quantum.Measurement using (Instrument)
open Instrument

------------------------------------------------------------------------
-- Corner correspondences
--
-- Each physical theory is, by definition, an instance of the
-- corresponding skeleton. These are definitional equalities, not
-- theorems: they record which corner the theory occupies.
--
-- 角落对应
--
-- 每个物理理论按定义是对应骨架的实例。这些是定义等式而非定理：它们
-- 记录该理论坐落在哪个角。

newton-as-ScaleInvariant
  : ∀ {a} {X : Set a} (f : X → X)
  → LinearDynamics f ≡ ScaleInvariant {Obs = ⊤ {lzero}} (λ x _ → f x)
newton-as-ScaleInvariant f = refl

module _ {a} {X : Set a} (𝕄 : ManifoldStructure X) where
  open ManifoldEq 𝕄

  gr-as-LayeredEqGen : ManifoldEq ≡ LayeredEqGen Obs step layer obs-map
  gr-as-LayeredEqGen = refl

quantum-to-DiscreteEq
  : ∀ {a s} {X : Set a} {Scalar : Set s}
  → QuantumLayer X Scalar → X → X → Set s
quantum-to-DiscreteEq = toDiscrete

------------------------------------------------------------------------
-- Forward projections
--
-- Each corner projects down to the corners below it. The projections
-- reuse the shape of Base.Equivalence.Lattice.Projections, stated
-- here at the physical level so the lattice is closed on the forward
-- side.
--
-- gr-to-quantum forgets the recursion and keeps the layer; it needs no
-- constant-observation assumption. gr-to-newton trivialises the layer
-- and keeps the recursion; it requires a constant observation family,
-- which is exactly the Newton corner.
--
-- 正向投影
--
-- 每个角投影到格中位于其下方的角。投影复用
-- Base.Equivalence.Lattice.Projections 的形状，在物理层面陈述以在
-- 正向侧闭合格。
--
-- gr-to-quantum 忘掉递归、保留 layer；不需要常量观测假设。
-- gr-to-newton 平凡化 layer、保留递归；需要常量观测族，这正是牛顿
-- 角。

module ForwardProjections where

  gr-to-quantum
    : ∀ {a b c} {X : Set a} {Obs : X → Set b}
      (step : (x : X) → Obs x → X)
      (layer : X → X → Set c)
      (obs-map : (x' y' : X) → layer x' y' → Obs x' → Obs y')
    → ∀ {x y} → LayeredEqGen Obs step layer obs-map x y
    → DiscreteEq layer x y
  gr-to-quantum step layer obs-map p = p .Mᵢ.fst

  gr-to-newton
    : ∀ {a b c} {X : Set a} {Obs : Set b}
      (step : X → Obs → X)
      (layer : X → X → Set c)
    → ∀ {x y} → LayeredEqGen (λ _ → Obs) (λ x s → step x s)
                             layer (λ _ _ _ o → o) x y
    → ScaleInvariant step x y
  gr-to-newton step layer p .Mᵢ.fst = tt
  gr-to-newton step layer p .Mᵢ.snd s =
    gr-to-newton step layer (p .Mᵢ.snd s)

------------------------------------------------------------------------
-- Separation: Newton is not general relativity
--
-- There is no canonical map from ScaleInvariant back to a general
-- LayeredEqGen, holding the underlying state space, dynamics and
-- observation family fixed and letting only the layer vary. The proof
-- instantiates the unit type with the constant dynamics, keeps Obs = ⊤
-- and step = λ _ _ → tt on both sides, and takes layer = ⊥: the
-- ScaleInvariant side is trivially inhabited, while the LayeredEqGen
-- side demands an element of ⊥ at its first field.
--
-- 分离：牛顿不是广义相对论
--
-- 不存在从 ScaleInvariant 回到一般 LayeredEqGen 的典范映射，且保持
-- 底层状态空间、动力学与观测族固定，只让 layer 变化。证明在单位
-- 类型上用常量动力学实例化，两侧都取 Obs = ⊤、step = λ _ _ → tt，
-- 并取 layer = ⊥：ScaleInvariant 侧平凡可居，而 LayeredEqGen 侧
-- 在其第一个字段上要求 ⊥ 的元素。

no-newton-to-gr
  : ¬ (∀ (X : Set) (f : X → X) (x y : X)
       (layer : X → X → Set)
       (obs-map : (x' y' : X) → layer x' y' → ⊤ {lzero} → ⊤ {lzero})
       → ScaleInvariant {X = X} {Obs = ⊤ {lzero}} (λ x _ → f x) x y
       → LayeredEqGen {X = X} (λ _ → ⊤ {lzero}) (λ x _ → f x)
                      layer obs-map x y)
no-newton-to-gr lift = le .fst
  where
    X : Set
    X = ⊤ {lzero}

    f : X → X
    f _ = tt

    layer : X → X → Set
    layer _ _ = ⊥

    obs-map : (x y : X) → layer x y → ⊤ {lzero} → ⊤ {lzero}
    obs-map _ _ ()

    si : ScaleInvariant {X = X} {Obs = ⊤ {lzero}} (λ _ _ → tt) tt tt
    si .fst = tt
    si .snd _ = si

    le : LayeredEqGen {X = X} (λ _ → ⊤ {lzero}) (λ _ _ → tt)
                      layer obs-map tt tt
    le = lift X f tt tt layer obs-map si

------------------------------------------------------------------------
-- Separation: quantum is not general relativity
--
-- There is no canonical map from a DiscreteEq layer back to a general
-- LayeredEqGen: DiscreteEq keeps only the current layer and drops the
-- recursion, so it provides no evidence that the layer survives a
-- step. The proof exhibits a layer that holds at one state but not at
-- its step successor.
--
-- 分离：量子不是广义相对论
--
-- 不存在从 DiscreteEq 层回到一般 LayeredEqGen 的典范映射：DiscreteEq
-- 只保留当前 layer 并丢掉递归，故不提供 layer 在 step 之后仍成立的
-- 证据。证明给出一个 layer 在某状态成立而在其后继上不成立的例子。

no-quantum-to-gr
  : ¬ (∀ (ObsI : ⊤ {lzero} ⊎ ⊤ {lzero} → Set)
         (step : (b : ⊤ {lzero} ⊎ ⊤ {lzero})
               → ObsI b → ⊤ {lzero} ⊎ ⊤ {lzero})
         (rel : ⊤ {lzero} ⊎ ⊤ {lzero}
              → ⊤ {lzero} ⊎ ⊤ {lzero} → Set)
         (obs-map : (x y : ⊤ {lzero} ⊎ ⊤ {lzero})
                  → rel x y → ObsI x → ObsI y)
         (x y : ⊤ {lzero} ⊎ ⊤ {lzero})
       → DiscreteEq rel x y
       → LayeredEqGen ObsI step rel obs-map x y)
no-quantum-to-gr lift = contradiction
  where
    B : Set
    B = ⊤ {lzero} ⊎ ⊤ {lzero}

    ObsI : B → Set
    ObsI _ = ⊤ {lzero}

    step : (b : B) → ObsI b → B
    step (inj₁ _) _ = inj₂ tt
    step (inj₂ _) _ = inj₁ tt

    rel : B → B → Set
    rel (inj₁ _) (inj₁ _) = ⊥
    rel (inj₁ _) (inj₂ _) = ⊥
    rel (inj₂ _) (inj₁ _) = ⊥
    rel (inj₂ _) (inj₂ _) = ⊤ {lzero}

    obs-map : (x y : B) → rel x y → ObsI x → ObsI y
    obs-map (inj₁ _) (inj₁ _) ()
    obs-map (inj₁ _) (inj₂ _) ()
    obs-map (inj₂ _) (inj₁ _) ()
    obs-map (inj₂ _) (inj₂ _) _ _ = tt

    d : DiscreteEq rel (inj₂ tt) (inj₂ tt)
    d = tt

    le : LayeredEqGen ObsI step rel obs-map (inj₂ tt) (inj₂ tt)
    le = lift ObsI step rel obs-map (inj₂ tt) (inj₂ tt) d

    contradiction : ⊥
    contradiction = le .snd tt .fst

------------------------------------------------------------------------
-- Quantum qualification: column conservation
--
-- A DiscreteEq layer with amplitude decoration sits at the quantum
-- corner only when its amplitudes sum to one along every input-output
-- column. The two concrete instantiations carry this by construction:
-- the Stochastic kernel via totals, the Measurement instrument via
-- norm.
--
-- 量子资格：列守恒
--
-- 带振幅装饰的 DiscreteEq 层只有沿每个输入-输出列的振幅求和为一，
-- 才位于量子角。两个具体实例按构造携带该性质：Stochastic 核通过
-- totals，Measurement 仪器通过 norm。

module QuantumConservation where

  kernel-conserves
    : ∀ {m n} (K : Kernel m n) (j : Fin n)
    → sumFin (λ i → cell K i j) ≡ 1ℚ
  kernel-conserves K j = totals K j

  instrument-conserves
    : ∀ {m n} (M : Instrument m n) (j : Fin n)
    → sumFin (λ i → norm² (amp M i j)) ≡ 1ℚ
  instrument-conserves M j = norm M j

------------------------------------------------------------------------
-- Concrete connection: Kernel to QuantumLayer
--
-- A Kernel lifts to a QuantumLayer over the disjoint union of its
-- input and output indices. The layer relates each input to every
-- output; the amplitude is the kernel cell.
--
-- 具体连接：Kernel 到 QuantumLayer
--
-- Kernel 提升为其输入与输出索引不交并上的 QuantumLayer。层把每个
-- 输入连接到每个输出；振幅是核的 cell。

kernel-QL : ∀ {m n} → Kernel m n → QuantumLayer (Fin m ⊎ Fin n) ℚ
kernel-QL {m} {n} K = record
  { layer = layer'
  ; amp   = amp'
  }
  where
  layer' : Fin m ⊎ Fin n → Fin m ⊎ Fin n → Set
  layer' (inj₁ _) (inj₁ _) = ⊥
  layer' (inj₁ _) (inj₂ _) = ⊥
  layer' (inj₂ _) (inj₁ _) = ⊤
  layer' (inj₂ _) (inj₂ _) = ⊥

  amp' : (x y : Fin m ⊎ Fin n) → layer' x y → ℚ
  amp' (inj₂ j) (inj₁ i) tt = cell K i j
  amp' (inj₂ _) (inj₂ _) ()
  amp' (inj₁ _) (inj₁ _) ()
  amp' (inj₁ _) (inj₂ _) ()

------------------------------------------------------------------------
-- Quantum qualification, made specific
--
-- The Kernel QuantumLayer is conservation-qualified at its input
-- states: for every input j, the sum of amplitudes over its output
-- indices equals one. This is the theorem that turns "quantum corner =
-- DiscreteEq + conservation" from two parallel facts into a single
-- statement.
--
-- 量子资格的具体化
--
-- Kernel 提升出的 QuantumLayer 在输入状态上守恒合格：对每个输入 j，
-- 振幅在其输出索引上求和为一。这就是把“量子角 = DiscreteEq + 守恒”
-- 从两条平行事实变成一条定理的定理。

kernel-QL-isConservative
  : ∀ {m n} (K : Kernel m n)
  → IsConservative (kernel-QL K)
      (λ { (inj₂ _) → ⊤ {lzero} ; (inj₁ _) → ⊥ })
      (λ k f → sumFin f)
      1ℚ
kernel-QL-isConservative {m} {n} K = record
  { outputs = λ { (inj₂ _) tt → m ; (inj₁ _) () }
  ; index   = λ { (inj₂ _) tt i → inj₁ i ; (inj₁ _) () }
  ; reach   = λ { (inj₂ _) tt i → tt ; (inj₁ _) () }
  ; sum-one = λ { (inj₂ j) tt → totals K j ; (inj₁ _) () }
  }
