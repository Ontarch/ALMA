------------------------------------------------------------------------
-- Colimit of an arbitrary quiver-shaped diagram in SameIndexCatS
--
-- A diagram assigns a LabelSys to every vertex of a small quiver (K, Q)
-- and an identity-index forward arrow Idx⇒ to every edge. The apex
-- label fibre at global index v is the disjoint union of the stage
-- fibres Σ K (fibre x v), quotiented by the equivalence closure of two
-- generators: equality within a stage (same) and identification along
-- an edge (edge). The carrier is a SETOID quotient that is never
-- collapsed, so the injections stage → apex are free: every element
-- carries its vertex and no born-at-0 section or stage isomorphism is
-- assumed. The mediating arrow is the equivalence-closure fold; its
-- factorisation is definitional and uniqueness is pointwise at every
-- tagged label, lifted to morphism bisimulation by pointwise-i.
--
-- The vertex level k and fibre level ℓ are separate; the construction
-- lives at L = k ⊔ ℓ. The ω-chain is the quiver with K = ℕ and the
-- single successor edge SucArrow, so k = lzero and L = ℓ with no lift;
-- the direct limit is then unconditional, whereas a compatible-family
-- (projection-cone) presentation would additionally need a born-at-0
-- section or stage isomorphisms. Collapsing the closure to
-- propositional equality remains independent of the flags (a set
-- quotient/HIT to construct, a provably non-UIP fibre to refute),
-- exactly as for the chain direct limit.
--
-- SameIndexCatS 中任意 quiver 形状图示的余极限
--
-- 图示给小 quiver (K, Q) 的每个顶点赋一个 LabelSys，给每条边赋一个索引
-- 恒等的前向箭头 Idx⇒。顶点在全局索引 v 处的标签纤维是阶段纤维的不交并
-- Σ K (fibre x v)，再对两个生成子取等价闭包：阶段内相等（same）与沿边
-- 识别（edge）。载体是从不被压合的 SETOID 商，故“阶段 → 顶点”注入免费：
-- 每个元素携带其顶点，无需诞生 0 截面或阶段同构。mediate 箭头即等价闭包
-- 折叠；因子分解定义性成立，唯一性在每个带标签代表元上逐点成立，并由
-- pointwise-i 提升为态射互模拟。
--
-- 顶点层 k 与纤维层 ℓ 分离，构造位于 L = k ⊔ ℓ。ω-链即 K = ℕ、仅含后继
-- 边 SucArrow 的 quiver，此时 k = lzero、L = ℓ，无需提升；直接极限因而
-- 无条件成立，而相容族（投影锥）表示还需额外的诞生 0 截面或阶段同构。
-- 把闭包压成命题相等仍与开关独立（构造需集合商/HIT，证伪需可证不满足
-- UIP 的纤维），与链直接极限相同。
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module Cosmos.Carried.SameIndexColimitS where

open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)
open import Agda.Builtin.Sigma using (Σ; _,_)
open import Data.Nat.Base using (ℕ; suc)
open import Relation.Binary.Core using (Rel)
open import Relation.Binary.Bundles using (Setoid)
open import Relation.Binary.Construct.Closure.Equivalence as EqClosure using
  (EqClosure; setoid; return; gfold)

open import Base.MCorr.Setoid using (EqOn)
open import Cosmos.Carried.SameIndexCatS using
  (LabelSys; Idx⇒; compi; _≈i_; pointwise-i)

------------------------------------------------------------------------
-- The ω shape
--
-- One successor edge per vertex, no propositional index.
--
-- ω 形状
--
-- 每顶点一条后继边，不含命题索引。

data SucArrow {ℓ : Level} : ℕ → ℕ → Set ℓ where
  sfwd : (m : ℕ) → SucArrow m (suc m)

------------------------------------------------------------------------
-- A quiver-shaped diagram and its colimit
--
-- quiver 形状图示及其余极限

module Build (d : ℕ → ℕ) {k ℓ : Level}
             (K : Set k) (Q : K → K → Set (k ⊔ ℓ)) where

  private L = k ⊔ ℓ

  -- A diagram: a stage object per vertex and a forward arrow per edge.
  --
  -- 图示：每顶点一个阶段对象，每边一条前向箭头。
  record Diagram : Set (lsuc L) where
    field
      X₀ : K → LabelSys L
      e  : ∀ {x y} → Q x y → Idx⇒ d (X₀ x) (X₀ y)
  open Diagram public

  module WithDia (dia : Diagram) where

    private
      fibre : (x : K) (v : ℕ) → Set L
      fibre x v = LabelSys.A₀ (X₀ dia x) v

      ≈fibre : (x : K) (v : ℕ) → EqOn (fibre x v)
      ≈fibre x v = LabelSys.≈A₀ (X₀ dia x) v

      fwd : ∀ {x y} (f : Q x y) (v : ℕ)
          → fibre x v → fibre y v
      fwd f v = Idx⇒.shape (e dia f) v

    -- Apex carrier at v: a stage fibre element tagged with its vertex.
    --
    -- 顶点在 v 处的载体：带顶点标签的阶段纤维元素。
    ColimCarrier : (v : ℕ) → Set L
    ColimCarrier v = Σ K λ x → fibre x v

    -- The generating relation at a fixed global index v
    --
    -- v is a module parameter, not a data index, so the only data indices
    -- are the tagged pairs: matching causes no cubical indexed-match
    -- warning.
    --
    -- 固定全局索引 v 处的生成关系
    --
    -- v 是模块参数而非数据索引，故数据仅被带标签对索引，匹配不触发
    -- cubical 索引匹配警告。
    module Slice (v : ℕ) where
      data _∼₀_ : Rel (ColimCarrier v) L where
        same : ∀ {x} {a a' : fibre x v}
             → EqOn._≈_ (≈fibre x v) a a'
             → (x , a) ∼₀ (x , a')
        edge : ∀ {x y} (f : Q x y) {a : fibre x v}
             → (x , a) ∼₀ (y , fwd f v a)

      ≈raw : EqOn (ColimCarrier v)
      ≈raw = record
        { _≈_           = EqClosure _∼₀_
        ; isEquivalence = Setoid.isEquivalence (setoid _∼₀_)
        }

    -- Fibre setoid of the apex.
    --
    -- 顶点的纤维 setoid。
    ≈colim : (v : ℕ) → EqOn (ColimCarrier v)
    ≈colim v = Slice.≈raw v

    -- The colimit apex.
    --
    -- 余极限顶点。
    apex : LabelSys L
    apex = record { A₀ = ColimCarrier ; ≈A₀ = ≈colim }

    -- Canonical injections; same-fibre equality maps to one closure step.
    --
    -- 规范注入；同纤维相等映为一步闭包。
    leg : (x : K) → Idx⇒ d (X₀ dia x) apex
    leg x = record
      { shape      = λ v a → x , a
      ; shape-cong = λ {v} → leg-cong v
      }
      where
      leg-cong : (v : ℕ) {a a' : fibre x v}
               → EqOn._≈_ (≈fibre x v) a a'
               → EqOn._≈_ (≈colim v) (x , a) (x , a')
      leg-cong v eq = let open Slice v in return (same eq)

    --------------------------------------------------------------------
    -- A cocone over the diagram with apex Y
    --
    -- One leg per vertex and label-level commutation along every edge.
    --
    -- 以 Y 为顶点的余锥
    --
    -- 每顶点一条腿，沿每边有标签级相干。
    record Cocone (Y : LabelSys L) : Set (lsuc L) where
      field
        ψ    : (x : K) → Idx⇒ d (X₀ dia x) Y
        comm : ∀ {x y} (f : Q x y) (v : ℕ) (a : fibre x v)
             → EqOn._≈_ (LabelSys.≈A₀ Y v)
                        (Idx⇒.shape (ψ y) v (fwd f v a))
                        (Idx⇒.shape (ψ x) v a)

      -- Edge commutation as a morphism bisimulation.
      --
      -- 边相干的态射互模拟形式。
      comm-i : ∀ {x y} (f : Q x y)
             → _≈i_ d (compi d (ψ y) (e dia f)) (ψ x)
      comm-i {x = x} f =
        pointwise-i d {X = X₀ dia x} {Y = Y}
          (compi d (ψ _) (e dia f)) (ψ x)
          (λ v a → comm f v a)

    module _ {Y : LabelSys L} (cn : Cocone Y) where

      private
        rep : (v : ℕ) → ColimCarrier v → LabelSys.A₀ Y v
        rep v (x , a) = Idx⇒.shape (Cocone.ψ cn x) v a

        -- Fold the closure at v into Y's fibre setoid.
        --
        -- 在 v 处把闭包折叠进 Y 的纤维 setoid。
        mediate-cong : (v : ℕ) {p q : ColimCarrier v}
                     → EqOn._≈_ (≈colim v) p q
                     → EqOn._≈_ (LabelSys.≈A₀ Y v) (rep v p) (rep v q)
        mediate-cong v =
          gfold (EqOn.isEquivalence (LabelSys.≈A₀ Y v)) (rep v) step
          where
          open Slice v
          step : ∀ {p q} → _∼₀_ p q
               → EqOn._≈_ (LabelSys.≈A₀ Y v) (rep v p) (rep v q)
          step (same eq) = Idx⇒.shape-cong (Cocone.ψ cn _) eq
          step (edge {x = x} {y = y} f {a = a}) =
            EqOn.sym (LabelSys.≈A₀ Y v)
                     (Cocone.comm cn {x = x} {y = y} f v a)

      -- Mediating arrow.
      --
      -- mediate 箭头。
      mediate : Idx⇒ d apex Y
      mediate = record { shape = rep ; shape-cong = λ {v} → mediate-cong v }

      -- Factorisation: mediate after leg x is ψ x, definitionally.
      --
      -- 因子分解：mediate 接 leg x 即 ψ x，定义性成立。
      factor : (x : K)
             → _≈i_ d (compi d mediate (leg x)) (Cocone.ψ cn x)
      factor x =
        pointwise-i d {X = X₀ dia x} {Y = Y}
          (compi d mediate (leg x)) (Cocone.ψ cn x)
          (λ _ _ → EqOn.refl (LabelSys.≈A₀ Y _))

      -- Uniqueness among arrows agreeing with the legs at every label.
      --
      -- 在每个标签上与各腿一致的箭头中唯一。
      unique : (h : Idx⇒ d apex Y)
             → (∀ x v (a : fibre x v)
                → EqOn._≈_ (LabelSys.≈A₀ Y v)
                            (Idx⇒.shape h v (x , a))
                            (Idx⇒.shape (Cocone.ψ cn x) v a))
             → _≈i_ d h mediate
      unique h fac = pointwise-i d {X = apex} {Y = Y} h mediate eq
        where
        eq : (v : ℕ) (p : ColimCarrier v)
           → EqOn._≈_ (LabelSys.≈A₀ Y v)
                       (Idx⇒.shape h v p) (rep v p)
        eq v (x , a) = fac x v a

------------------------------------------------------------------------
-- The ω-chain specialisation
--
-- Vertices ℕ, successor edges only. With k = lzero the object level is
-- L = ℓ, so no lift is needed and the colimit needs no stage isomorphism
-- or born-at-0 section, unlike a compatible-family (projection-cone)
-- representation.
--
-- ω-链特例
--
-- 顶点 ℕ，仅后继边。k = lzero 时对象层 L = ℓ，无需提升；与相容族
-- （投影锥）表示不同，余极限无需阶段同构或诞生 0 截面。

module ωBuild (d : ℕ → ℕ) {ℓ : Level}
             (X₀ : ℕ → LabelSys ℓ)
             (step : (m : ℕ) → Idx⇒ d (X₀ m) (X₀ (suc m))) where

  private
    module W = Build d {k = lzero} {ℓ = ℓ} ℕ (SucArrow {ℓ = ℓ})

    dia : W.Diagram
    dia = record
      { X₀ = X₀
      ; e  = λ { (SucArrow.sfwd m) → step m }
      }

  open W.WithDia dia public
    using (ColimCarrier; apex; leg; Cocone; mediate; factor; unique)
