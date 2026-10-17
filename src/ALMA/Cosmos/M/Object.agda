------------------------------------------------------------------------
-- Cosmos on the setoid-parameterised M base: object layer
--
-- The index is a base object together with a shape; the label carries
-- the unfolding functor uf and the position-to-shape map pts; an edge
-- is a source position together with the HOMOGENEOUS equation pinning
-- the target index. Where the equalities live: edge/index equations are
-- propositional and constructive, always introduced as (p , refl), the
-- non-propositional equivalence lives in the LABEL, carried as the
-- label EqOn ≈CD (natural isomorphism at the morphism layer); position
-- edges are sets, so their fibre EqOn is propositional. The object
-- system is a MCorrSetoid SysEq and _≈Mˢ_ relates nodes up to the
-- carried label EqOn.
--
-- 在 setoid 参数化 M 底座上重建的 Cosmos：对象层
--
-- 索引为基对象连同形状；标签携带展开函子 uf 与位置到形状映射 pts；
-- 边是源位置连同把目标索引钉为该位置处 uf/pts 作用结果的同质等式。
-- 等式的位置：边/索引等式是命题且构造性的，总以 (p , refl) 引入，
-- 非命题等价活在标签层，作为标签 EqOn ≈CD 携带（态射层的自然同构）；
-- 位置边是集合，故其纤维 EqOn 是命题的。对象系统即 MCorrSetoid 的
-- SysEq，_≈Mˢ_ 按携带的标签 EqOn 联系节点。
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module ALMA.Cosmos.M.Object where

open import Agda.Primitive using (Level; _⊔_)
open import Agda.Builtin.Sigma using (Σ; _,_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Product.Base using (proj₂)

open import Categories.Category.Core using (Category)
open import Categories.Functor.Core using (Functor)

open import ALMA.Base.MCorr using (M; _⍮_)
open import ALMA.Base.MCorrSetoid using
  (EqOn; SysEq; propEqOn; idAdjˢ; _≈Mˢ_; here-eq; below-eq; ≈Mˢ-refl; Morphˢ
  ; compMˢ; idMˢ)
import ALMA.Base.MCorrSetoidCoalg as GCP
open import ALMA.Cosmos.ContCategory using (ContCat)
open import ALMA.Cosmos.ContCategoryLemmas using (ShapeOf; PosOf)
open import ALMA.Cosmos.ContCatEquiv using (ShapeCat)

module _ {o h e s p : Level}
         (C  : Category o h e)
         (FC : Functor C (ContCat s p)) where

  ----------------------------------------------------------------------
  -- Index
  --
  -- A base object together with a shape over it.
  --
  -- 索引
  --
  -- 基对象连同其上的形状。

  I : Set (o ⊔ s)
  I = Σ (Category.Obj C) (ShapeOf FC)

  ----------------------------------------------------------------------
  -- Per-layer unfolding data (uf + pts)
  --
  -- 每层展开数据（uf + pts）

  record CosmosData : Set (o ⊔ h ⊔ e ⊔ s ⊔ p) where
    field
      uf  : Functor (ShapeCat C FC) C
      pts : ∀ {A} (s : ShapeOf FC A) → PosOf FC s
          → ShapeOf FC (Functor.F₀ uf (A , s))
  open CosmosData public

  A : I → Set (o ⊔ h ⊔ e ⊔ s ⊔ p)
  A _ = CosmosData

  -- Edge: source position plus the constructive homogeneous equation
  -- pinning the target index; always introduced as (p , refl).
  --
  -- 边：源位置加钉住目标索引的构造性同质等式；总以 (p , refl) 引入。
  E : (i : I) (d : A i) (j : I) → Set (o ⊔ s ⊔ p)
  E (A₀ , s) d (A₁ , s₁) =
    Σ (PosOf FC s) λ p →
      (A₁ , s₁) ≡ ( Functor.F₀ (uf d) (A₀ , s)
                  , pts d s p )

  ----------------------------------------------------------------------
  -- Nodes and the derived step / root
  --
  -- 节点与派生的 step / root

  CosmosM : I → Set (o ⊔ h ⊔ e ⊔ s ⊔ p)
  CosmosM i = M A E i

  nextOf : (i : I) (d : A i) (p : PosOf FC (proj₂ i)) → I
  nextOf (A₀ , s) d p =
    ( Functor.F₀ (uf d) (A₀ , s)
    , pts d s p )

  next : (i : I) (t : CosmosM i) (p : PosOf FC (proj₂ i)) → I
  next i t p = nextOf i (M.here t) p

  step : (i : I) (t : CosmosM i) (p : PosOf FC (proj₂ i))
       → CosmosM (next i t p)
  step (A₀ , s) t p =
    M.below t (next (A₀ , s) t p) (p , refl)

  Rooted : (A₀ : Category.Obj C) → ShapeOf FC A₀
         → Set (o ⊔ h ⊔ e ⊔ s ⊔ p)
  Rooted A₀ s₀ = CosmosM (A₀ , s₀)

  ----------------------------------------------------------------------
  -- Terminality corecursor
  --
  -- A one-step coalgebra over a state family Xst gives, at each index, a
  -- label and for every position a child state at nextOf; ana produces a
  -- CosmosM by the native guarded corecursion of M, matching the edge
  -- (p , refl) constructively.
  --
  -- 终性余递归子
  --
  -- 状态族 Xst 上的一步余代数在每个索引给出标签与每个位置的子状态；
  -- ana 借 M 内建的受保护余递归产生 CosmosM，构造性匹配边 (p , refl)。

  -- Propositional system over the same I/A/E; used to lift the generic
  -- carried anamorphism (which is independent of the label regime).
  --
  -- 同一 I/A/E 上的命题系统；用于提升泛型携带式 anamorphism（其与
  -- 标签等价制度无关）。
  sysProp : SysEq (o ⊔ s) (o ⊔ h ⊔ e ⊔ s ⊔ p) (o ⊔ s ⊔ p)
                  (o ⊔ h ⊔ e ⊔ s ⊔ p) (o ⊔ s ⊔ p)
  sysProp = record
    { I  = I
    ; A  = A
    ; E  = E
    ; ≈A = λ i → propEqOn (A i)
    ; ≈E = λ i d j → propEqOn (E i d j)
    }

  record Coalgebra (u : Level) (Xst : I → Set u)
         : Set (o ⊔ h ⊔ e ⊔ s ⊔ p ⊔ u) where
    field
      label : (i : I) → Xst i → A i
      child : (i : I) (x : Xst i) (p : PosOf FC (proj₂ i))
            → Xst (nextOf i (label i x) p)
  open Coalgebra public

  -- The deterministic container coalgebra is the generic carried
  -- coalgebra at the constructive edge (p , refl): the generic child
  -- matches the edge, which pins j to nextOf. Determinism lives entirely
  -- in this adapter.
  --
  -- 确定性容器余代数即泛型携带式余代数在构造性边 (p , refl) 处的实例：
  -- 泛型 child 匹配该边，从而把 j 钉为 nextOf。确定性完全集中于此适配
  -- 器。
  gcoalg : ∀ {u : Level} {Xst : I → Set u}
         → Coalgebra u Xst → GCP.Coalgebra sysProp u Xst
  gcoalg γ .GCP.Coalgebra.label i x = label γ i x
  gcoalg γ .GCP.Coalgebra.child i x .(nextOf i (label γ i x) p) (p , refl)
    = child γ i x p

  -- The anamorphism is the generic carried one at the (p , refl) edge.
  --
  -- anamorphism 即 (p , refl) 边处的泛型携带式 anamorphism。
  ana : ∀ {u : Level} {Xst : I → Set u}
        (γ : Coalgebra u Xst)
      → (i : I) (x : Xst i) → CosmosM i
  ana γ i x = GCP.ana sysProp (gcoalg γ) i x

  -- Observation coalgebra of a node: state is CosmosM, label reads the
  -- head, child steps along the edge; ana of it rebuilds the tree, and
  -- ana-unfold shows the rebuild is bisimilar to the original.
  --
  -- 节点的观察余代数：状态即 CosmosM，label 读头部，child 沿边 step；
  -- 对其取 ana 即重建树，ana-unfold 表明重建树与原树互模拟。
  unfold-coalgebra : Coalgebra (o ⊔ h ⊔ e ⊔ s ⊔ p) CosmosM
  unfold-coalgebra .label i t = M.here t
  unfold-coalgebra .child i t p = step i t p

  ----------------------------------------------------------------------
  -- The object system as a SysEq carrying a label EqOn ≈CD
  --
  -- Position fibres use the propositional EqOn. ≈CD is the single seam
  -- at which the equivalence regime is chosen.
  --
  -- 对象系统作为携带标签 EqOn ≈CD 的 SysEq
  --
  -- 位置纤维取命题 EqOn。≈CD 是选择等价制度的唯一接缝。

  sys : ∀ {ℓd : Level}
        (≈CD : (i : I) → EqOn {ℓ = ℓd} (A i))
      → SysEq (o ⊔ s) (o ⊔ h ⊔ e ⊔ s ⊔ p) (o ⊔ s ⊔ p) ℓd (o ⊔ s ⊔ p)
  sys ≈CD = record
    { I  = I
    ; A  = A
    ; E  = E
    ; ≈A = ≈CD
    ; ≈E = λ i d j → propEqOn (E i d j)
    }

  ----------------------------------------------------------------------
  -- Coinductive bisimulation up to the carried label EqOn
  --
  -- 在携带标签 EqOn 下的余归纳互模拟

  ≈CosmosM : ∀ {ℓd : Level}
             (≈CD : (i : I) → EqOn {ℓ = ℓd} (A i))
           → ∀ {i : I} → CosmosM i → CosmosM i
           → Set (o ⊔ h ⊔ e ⊔ s ⊔ p ⊔ ℓd)
  ≈CosmosM ≈CD = _≈Mˢ_ (SysEq.≈A (sys ≈CD)) (SysEq.≈E (sys ≈CD))

  ≈CosmosM-refl : ∀ {ℓd : Level}
                  (≈CD : (i : I) → EqOn {ℓ = ℓd} (A i))
                → ∀ {i : I} (t : CosmosM i) → ≈CosmosM ≈CD t t
  ≈CosmosM-refl ≈CD = ≈Mˢ-refl (SysEq.≈A (sys ≈CD)) (SysEq.≈E (sys ≈CD))

  ----------------------------------------------------------------------
  -- Terminality / eta
  --
  -- ana of a node's observation coalgebra rebuilds a tree bisimilar to
  -- the original, up to the carried label EqOn.
  --
  -- 终性 / eta
  --
  -- 对节点观察余代数取 ana，重建出与原树在携带标签 EqOn 下互模拟的树。

  mutual
    ana-unfold : ∀ {ℓd : Level}
                 (≈CD : (i : I) → EqOn {ℓ = ℓd} (A i))
               → ∀ {i : I} (t : CosmosM i)
               → ≈CosmosM ≈CD (ana unfold-coalgebra i t) t
    ana-unfold ≈CD {i = i} t .here-eq = EqOn.refl (≈CD i)
    ana-unfold ≈CD {i = i} t .below-eq y =
        idAdjˢ (SysEq.≈E (sys ≈CD) i (M.here t) y)
      , ( (λ { (p , refl) → ana-unfold ≈CD (step i t p) })
        , (λ { (p , refl) → ana-unfold˘ ≈CD (step i t p) }) )

    ana-unfold˘ : ∀ {ℓd : Level}
                  (≈CD : (i : I) → EqOn {ℓ = ℓd} (A i))
                → ∀ {i : I} (t : CosmosM i)
                → ≈CosmosM ≈CD t (ana unfold-coalgebra i t)
    ana-unfold˘ ≈CD {i = i} t .here-eq = EqOn.refl (≈CD i)
    ana-unfold˘ ≈CD {i = i} t .below-eq y =
        idAdjˢ (SysEq.≈E (sys ≈CD) i (M.here t) y)
      , ( (λ { (p , refl) → ana-unfold˘ ≈CD (step i t p) })
        , (λ { (p , refl) → ana-unfold ≈CD (step i t p) }) )

  ----------------------------------------------------------------------
  -- Carried correspondences between M-Cosmos nodes
  --
  -- A Morphˢ over an arbitrary index relation R (need not be
  -- propositional). Identity and composition are the generic carried
  -- ones instantiated at sys; they contain no subst. The deterministic
  -- _⇒ℱ[S]_ is recovered at the container instance by taking R to be
  -- the graph of S.₀ and the edge FiberAdjˢ to be onPosAdj (see
  -- ContainerInstance).
  --
  -- M-Cosmos 节点间的携带式对应
  --
  -- 任意索引关系 R 上的 Morphˢ（R 不必命题）。恒等与复合即通用携带
  -- 版本在 sys 处的实例化，不含 subst。确定性 _⇒ℱ[S]_ 在容器实例处
  -- 通过令 R 为 S.₀ 的图、边 FiberAdjˢ 为 onPosAdj 而恢复（见
  -- ContainerInstance）。

  CosmosM⇒ : ∀ {ℓd ℓr : Level}
             (≈CD : (i : I) → EqOn {ℓ = ℓd} (A i))
             (R : I → I → Set ℓr)
           → Set (o ⊔ h ⊔ e ⊔ s ⊔ p ⊔ ℓd ⊔ ℓr)
  CosmosM⇒ ≈CD R = Morphˢ (sys ≈CD) (sys ≈CD) R

  idCosmosM : ∀ {ℓd : Level}
              (≈CD : (i : I) → EqOn {ℓ = ℓd} (A i))
            → CosmosM⇒ ≈CD (λ (x y : I) → x ≡ y)
  idCosmosM ≈CD = idMˢ (sys ≈CD)

  compCosmosM : ∀ {ℓd ℓ₁ ℓ₂ : Level}
                (≈CD : (i : I) → EqOn {ℓ = ℓd} (A i))
              → ∀ {R : I → I → Set ℓ₁} {S : I → I → Set ℓ₂}
              → CosmosM⇒ ≈CD R → CosmosM⇒ ≈CD S
              → CosmosM⇒ ≈CD (R ⍮ S)
  compCosmosM ≈CD φ ψ = compMˢ φ ψ
