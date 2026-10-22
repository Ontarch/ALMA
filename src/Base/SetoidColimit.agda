------------------------------------------------------------------------
-- Colimit of a setoid diagram over a quiver shape
--
-- quiver 形状上 setoid 图示的余极限
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module Base.SetoidColimit where

open import Agda.Primitive using (Level; _⊔_)
open import Agda.Builtin.Sigma using (Σ; _,_)
open import Function.Bundles using (Func; _⟨$⟩_)
open import Relation.Binary.Core using (Rel)
open import Relation.Binary.Bundles using (Setoid)
open import Relation.Binary.Construct.Closure.Equivalence using
  (setoid; return; symmetric; gfold)

open Func using (cong)
open Setoid using (Carrier; isEquivalence)

module _ {k c ℓ q : Level}
         (K : Set k)
         (Q : K → K → Set q)
         (D : K → Setoid c ℓ)
         (D₁ : ∀ {x y} → Q x y → Func (D x) (D y)) where

  ----------------------------------------------------------------------
  -- Disjoint union of the fibres
  --
  -- An element carries its birth vertex.
  --
  -- 各纤维的不交并
  --
  -- 元素携带其诞生顶点。

  ColimCarrier : Set (k ⊔ c)
  ColimCarrier = Σ K λ x → Carrier (D x)

  ----------------------------------------------------------------------
  -- Generating identification
  --
  -- Within-fibre equality, or one arrow step.
  --
  -- 生成性识别
  --
  -- 纤维内相等，或沿一条箭头前进一步。

  data _∼₀_ : Rel ColimCarrier (k ⊔ c ⊔ q ⊔ ℓ) where
    same : ∀ {x} {a a' : Carrier (D x)}
         → Setoid._≈_ (D x) a a'
         → (x , a) ∼₀ (x , a')
    edge : ∀ {x y} (f : Q x y) {a : Carrier (D x)}
         → (x , a) ∼₀ (y , D₁ f ⟨$⟩ a)

  ----------------------------------------------------------------------
  -- The colimit setoid
  --
  -- The equivalence closure of the generators. The carrier is never
  -- collapsed, so no HIT, univalence, K or transport is needed, and
  -- the fibres may carry arbitrary setoids. Collapsing the closure
  -- to propositional equality on a bare Set is a separate theorem
  -- needing a HIT and a non-UIP fibre, hence independent of the
  -- flags.
  --
  -- 余极限 setoid
  --
  -- 生成子的等价闭包。载体从不被压合，故无需 HIT、univalence、K 或
  -- 传输，纤维可带任意 setoid。把闭包压成裸 Set 上的命题相等是另一
  -- 个定理，需要 HIT 与非 UIP 纤维，故与开关独立。

  Colim : Setoid (k ⊔ c) (k ⊔ c ⊔ q ⊔ ℓ)
  Colim = setoid _∼₀_

  ----------------------------------------------------------------------
  -- Leg of the canonical cocone
  --
  -- Tag an element with its vertex.
  --
  -- 规范余锥的腿
  --
  -- 给元素打上顶点标签。

  inj : (x : K) → Func (D x) Colim
  inj x = record
    { to   = λ a → x , a
    ; cong = λ a≈ → return (same a≈)
    }

  ----------------------------------------------------------------------
  -- Canonical cocone commutation
  --
  -- The image along f is the same element reached by one edge step,
  -- read backwards.
  --
  -- 规范余锥交换
  --
  -- 沿 f 的像即走一条 edge 后到达的同一元素（反向读取）。

  canonical-comm : ∀ {x y} (f : Q x y) {a : Carrier (D x)}
    → Setoid._≈_ Colim (y , D₁ f ⟨$⟩ a) (x , a)
  canonical-comm f {a} = symmetric _∼₀_ (return (edge f {a}))

  module Cocone {cN ℓN : Level} (N : Setoid cN ℓN) where

    ------------------------------------------------------------------
    -- A cocone
    --
    -- A leg out of every fibre, agreeing along every arrow.
    --
    -- 余锥
    --
    -- 每条纤维一条腿，且沿任意箭头相容。

    record Cocone : Set (k ⊔ c ⊔ ℓ ⊔ q ⊔ cN ⊔ ℓN) where
      field
        ψ    : (x : K) → Func (D x) N
        comm : ∀ {x y} (f : Q x y) {a : Carrier (D x)}
             → Setoid._≈_ N (ψ y ⟨$⟩ (D₁ f ⟨$⟩ a))
                            (ψ x ⟨$⟩ a)

    open Cocone

    ------------------------------------------------------------------
    -- The mediating map on representatives
    --
    -- Defined on representatives, then closed under the generators:
    -- same uses the leg's congruence, edge uses commutation.
    --
    -- 代表元上的中介映射
    --
    -- 先在代表元上定义，再对生成子封闭：
    -- same 用腿的同余，edge 用交换律。

    rep : (cn : Cocone) → ColimCarrier → Carrier N
    rep cn (x , a) = ψ cn x ⟨$⟩ a

    rep-step : (cn : Cocone) → ∀ {u v} → u ∼₀ v
             → Setoid._≈_ N (rep cn u) (rep cn v)
    rep-step cn (same a≈)    = cong (ψ cn _) a≈
    rep-step cn (edge f {a}) = Setoid.sym N (comm cn f {a})

    ------------------------------------------------------------------
    -- Unique mediating morphism
    --
    -- The fold extends rep over the closure.
    --
    -- 唯一 mediate 态射
    --
    -- fold 把 rep 扩张到整个等价闭包。

    mediate : (cn : Cocone) → Func Colim N
    mediate cn = record
      { to   = rep cn
      ; cong = gfold (isEquivalence N) (rep cn) (rep-step cn)
      }

    ------------------------------------------------------------------
    -- Factorisation
    --
    -- Mediating after the leg is the leg, definitionally.
    --
    -- 因子分解
    --
    -- mediate 复合腿即该腿（定义性成立）。

    factor : (cn : Cocone) (x : K) {a : Carrier (D x)}
      → Setoid._≈_ N (mediate cn ⟨$⟩ (x , a)) (ψ cn x ⟨$⟩ a)
    factor cn x = Setoid.refl N

    ------------------------------------------------------------------
    -- Uniqueness
    --
    -- Any morphism agreeing with the legs on every fibre agrees with
    -- mediate at every tagged representative.
    --
    -- 唯一性
    --
    -- 任何在每条纤维上与各腿一致的态射，在每个带标签代表元上都与
    -- mediate 一致。

    unique : (cn : Cocone) (h : Func Colim N)
      → (∀ (x : K) {a : Carrier (D x)}
           → Setoid._≈_ N (h ⟨$⟩ (x , a)) (ψ cn x ⟨$⟩ a))
      → ∀ (u : ColimCarrier)
      → Setoid._≈_ N (h ⟨$⟩ u) (mediate cn ⟨$⟩ u)
    unique cn h fac (x , a) = fac x
