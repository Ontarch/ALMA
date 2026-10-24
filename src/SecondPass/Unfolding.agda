------------------------------------------------------------------------
-- Unfolding functor record
--
-- Defines the unfolding functor for a cosmos layer, mapping shaped objects to
-- the base category with seeds for the next universe
-- Also provides the setoid of unfoldings and the induced endofunctor on Setoids
--
-- 展开函子记录
--
-- 为宇宙层定义展开函子，将带形状的对象映射到基范畴，并为下一层宇宙提供种子
-- 同时给出展开的 Setoid 结构及其诱导的 Setoids 自函子
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module SecondPass.Unfolding where

open import Agda.Primitive using (Level; _⊔_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Sigma using (Σ; _,_)
open import Relation.Binary.Definitions using (Reflexive; Symmetric; Transitive)
open import Relation.Binary.PropositionalEquality.Core using (cong; subst)
open import Relation.Binary.PropositionalEquality.Properties using (setoid)
open import Relation.Binary.Bundles using (Setoid)
open import Function.Base using (id; _∘_)
open import Function.Bundles using (Func)
open import Data.Product.Base using (proj₁; proj₂)

open import Categories.Category.Core using (Category)
open import Categories.Category.Instance.Setoids using (Setoids)
open import Categories.Functor.Core using (Functor)

open import Equivalence using (module SubstTransport-Left)
open import Cosmos.ContCategory using (ContCat)
open import Cosmos.ContCategoryLemmas using (ShapeOf; PosOf; actSOf; actPOf)
open import Cosmos.ContCatEquiv using (ShapeCat)

-- Unfolding for a Cosmos layer:
-- given a functor F : C → ContCat and a seed set X, an Unfolding records
-- a functor from the shape category back to C, a next-seed assignment,
-- and a position-to-shape map compatible with the functorial action
--
-- 宇宙层的展开：
-- 给定函子 F : C → ContCat 与种子集 X，Unfolding 记录
-- 一个从形状范畴回到 C 的函子、一个下一层种子赋值，
-- 以及与函子作用相容的位置到形状映射
module _ {o h e s p u : Level}
         {C : Category o h e}
         (F : Functor C (ContCat s p))
         (X : Set u) where
  private
    open Category C
    ShapeCat′ = ShapeCat C F

  record Unfolding : Set (o ⊔ h ⊔ e ⊔ s ⊔ p ⊔ u) where
    field
      -- The unfolding functor: ShapeCat(F) → C
      --
      -- 展开函子：ShapeCat(F) → C
      unfoldFunctor   : Functor ShapeCat′ C
      -- Next-seed assignment: each shape yields a seed in X
      --
      -- 下一层种子赋值：每个形状产生 X 中的一个种子
      unfold-next     : ∀ {A} → ShapeOf F A → X
      -- Position-to-shape map: positions of a shape become shapes of the unfolded object
      --
      -- 位置到形状映射：某形状的位置成为展开后对象的形状
      pos-to-shape    : ∀ {A} (s : ShapeOf F A) → PosOf F s → ShapeOf F (Functor.₀ unfoldFunctor (A , s))
      -- Compatibility: pos-to-shape commutes with the functorial action on shapes/positions
      --
      -- 相容性：pos-to-shape 与形状/位置上的函子作用交换
      pos-actS-compat : ∀ {A B} {s : ShapeOf F A} {t : ShapeOf F B}
                      → (f : A ⇒ B) (q : actSOf F f s ≡ t)
                      → (p : PosOf F (actSOf F f s))
                      → pos-to-shape t (subst (PosOf F) q p)
                        ≡ actSOf F (Functor.₁ unfoldFunctor (f , q))
                                (pos-to-shape s (actPOf F f s p))
open Unfolding public

-- Functorial action on unfoldings: map the seed set along a function X → Y
--
-- 展开上的函子作用：沿函数 X → Y 映射种子集
mapUnfolding : ∀ {o h e s p u v} {C : Category o h e} {F : Functor C (ContCat s p)} {X : Set u} {Y : Set v}
             → (X → Y) → Unfolding F X → Unfolding F Y
mapUnfolding f u = record
  { unfoldFunctor   = unfoldFunctor u
  ; unfold-next     = λ s → f (unfold-next u s)
  ; pos-to-shape    = pos-to-shape u
  ; pos-actS-compat = pos-actS-compat u
  }

-- Identity law: mapUnfolding id u ≡ u
--
-- 恒等律：mapUnfolding id u ≡ u
mapUnfolding-id : ∀ {o h e s p u} {C : Category o h e} {F : Functor C (ContCat s p)} {X : Set u}
                 (u : Unfolding F X) → mapUnfolding id u ≡ u
mapUnfolding-id u = refl

-- Composition law: mapUnfolding (f ∘ g) u ≡ mapUnfolding f (mapUnfolding g u)
--
-- 复合律：mapUnfolding (f ∘ g) u ≡ mapUnfolding f (mapUnfolding g u)
mapUnfolding-∘ : ∀ {o h e s p u v w}
                   {C : Category o h e}
                   {F : Functor C (ContCat s p)}
                   {X : Set u} {Y : Set v} {Z : Set w}
                   (f : Y → Z) (g : X → Y)
                   (u : Unfolding F X)
               → mapUnfolding (f ∘ g) u ≡ mapUnfolding f (mapUnfolding g u)
mapUnfolding-∘ f g u = refl

-- Setoid structure for unfoldings
--
-- 展开的集合（Setoid）结构
module UnfoldingSetoid {o h e s p : Level}
                       {C : Category o h e}
                       {F : Functor C (ContCat s p)} where
  private
    ShapeOf′ = ShapeOf F
    PosOf′   = PosOf F

  -- Alignment: instantiate _≈sl_ at Unfolding, parameterised over the seed Setoid
  --
  -- 对齐：把 _≈sl_ 实例化到 Unfolding，参数化在种子 Setoid 上
  module _ {u v : Level} (X : Setoid u v) where
    open SubstTransport-Left
      {S = Σ (Category.Obj C) ShapeOf′}
      {T = Category.Obj C}
      ShapeOf′
      (λ { (A , s) → PosOf′ s })
      {F = Unfolding F (Setoid.Carrier X)}
      (λ U → Functor.₀ (Unfolding.unfoldFunctor U))
      (λ U {s} → Unfolding.pos-to-shape U {proj₁ s} (proj₂ s)) public

  -- `mapUnfolding` leaves `unfoldFunctor` and `pos-to-shape` unchanged,
  -- hence it preserves the `_≈sl_` component
  --
  -- mapUnfolding 保持 unfoldFunctor 与 pos-to-shape 不变，因此保持 _≈sl_
  -- 分量
  mapUnfolding-preserves-≈sl
    : {u v : Level} {X Y : Setoid u v}
      (f : Func X Y)
      {u₁ u₂ : Unfolding F (Setoid.Carrier X)}
    → _≈sl_ X u₁ u₂
    → _≈sl_ Y (mapUnfolding (Func.to f) u₁) (mapUnfolding (Func.to f) u₂)
  mapUnfolding-preserves-≈sl f
    (record { shape-eq = se ; position-eq = pe }) =
    record { shape-eq = se ; position-eq = pe }

  -- Equivalence on unfoldings: the generic _≈sl_ instance paired with
  -- pointwise equivalent next-seed assignments
  --
  -- 展开上的等价关系：通用 _≈sl_ 实例与逐点等价的下一层种子赋值配对
  record _≈U_ {u v : Level} {X : Setoid u v}
              (u₁ u₂ : Unfolding F (Setoid.Carrier X))
              : Set (o ⊔ s ⊔ p ⊔ v) where
    private
      module X  = Setoid X
      module U₁ = Unfolding u₁
      module U₂ = Unfolding u₂
    field
      -- Pointwise equal object maps plus compatible pos-to-shape,
      -- packaged as the generic _≈sl_ instance
      --
      -- 对象映射逐点相等且 pos-to-shape 相容，直接打包为通用的 _≈sl_ 实例
      sl-eq          : _≈sl_ X u₁ u₂

      -- Next-seed assignments are pointwise equivalent in X
      --
      -- 下一层种子赋值在 X 中逐点等价
      unfold-next-eq   : ∀ {A} (s : ShapeOf′ A)
                       → X._≈_ (U₁.unfold-next s) (U₂.unfold-next s)
  open _≈U_

  -- Reflexivity of _≈U_
  --
  -- _≈U_ 的自反性
  ≈U-refl : {u v : Level} {X : Setoid u v} → Reflexive (_≈U_ {X = X})
  ≈U-refl {X = X} = record
    { sl-eq          = ≈sl-refl X
    ; unfold-next-eq = λ _ → Setoid.refl X
    }

  -- Symmetry of _≈U_ via SubstTransport-Left
  --
  -- 通过 SubstTransport-Left 得到 _≈U_ 的对称性
  ≈U-sym : {u v : Level} (X : Setoid u v) → Symmetric (_≈U_ {X = X})
  ≈U-sym X {u₁} {u₂} eq = record
    { sl-eq          = ≈sl-sym X (eq .sl-eq)
    ; unfold-next-eq = λ s → Setoid.sym X (eq .unfold-next-eq s)
    }

  -- Transitivity of _≈U_ via SubstTransport-Left
  --
  -- 通过 SubstTransport-Left 得到 _≈U_ 的传递性
  ≈U-trans : {u v : Level} (X : Setoid u v) → Transitive (_≈U_ {X = X})
  ≈U-trans X {u₁} {u₂} {u₃} eq₁ eq₂ = record
    { sl-eq          = ≈sl-trans X (eq₁ .sl-eq) (eq₂ .sl-eq)
    ; unfold-next-eq = λ s → Setoid.trans X
                         (eq₁ .unfold-next-eq s) (eq₂ .unfold-next-eq s)
    }

  -- Assemble the setoid of unfoldings over a given setoid X
  --
  -- 组装给定集合 X 上的展开 Setoid
  unfoldingSetoid : {u v : Level} → Setoid u v
                  → Setoid (o ⊔ h ⊔ e ⊔ s ⊔ p ⊔ u) (o ⊔ s ⊔ p ⊔ v)
  unfoldingSetoid X = record
    { Carrier       = Unfolding F (Setoid.Carrier X)
    ; _≈_           = _≈U_ {X = X}
    ; isEquivalence = record
      { refl  = ≈U-refl {X = X}
      ; sym   = ≈U-sym X
      ; trans = ≈U-trans X
      }
    }

  -- mapUnfolding respects setoid equivalence: lifts Func X Y to Func (Unf X) (Unf Y)
  --
  -- mapUnfolding 保持集合等价：将 Func X Y 提升为 Func (Unf X) (Unf Y)
  mapUnfolding-resp : {u v : Level} {X Y : Setoid u v} → Func X Y
                    → Func (unfoldingSetoid X) (unfoldingSetoid Y)
  mapUnfolding-resp {X = X} {Y = Y} f = record
    { to   = λ u → mapUnfolding (Func.to f) u
    ; cong = λ {u₁ u₂} eq → helper eq
    }
    where
      helper : {u₁ u₂ : Unfolding F (Setoid.Carrier X)}
             → _≈U_ {X = X} u₁ u₂
             → _≈U_ {X = Y} (mapUnfolding (Func.to f) u₁)
                            (mapUnfolding (Func.to f) u₂)
      helper (record { sl-eq = sl ; unfold-next-eq = un }) = record
        { sl-eq          = mapUnfolding-preserves-≈sl f sl
        ; unfold-next-eq = λ s → Func.cong f (un s)
        }

  -- Pointwise version: if f ≈ g pointwise and u₁ _≈U_ u₂, then mapUnfolding f u₁ _≈U_ mapUnfolding g u₂
  --
  -- 逐点版本：若 f ≈ g 逐点成立且 u₁ _≈U_ u₂，则 mapUnfolding f u₁ _≈U_ mapUnfolding g u₂
  mapUnfolding-resp-≈ : {u : Level} (A B : Set u)
                      (f g : A → B)
                      → (∀ {x} → f x ≡ g x)
                      → {u₁ u₂ : Unfolding F A}
                      → _≈U_ {X = setoid A} u₁ u₂
                      → _≈U_ {X = setoid B} (mapUnfolding f u₁) (mapUnfolding g u₂)
  mapUnfolding-resp-≈ A B f g f≈g {u₁} {u₂} u₁≈u₂ =
    let
      SA = setoid A
      SB = setoid B
      sf : Func SA SB
      sf = record { to = f ; cong = cong f }
      module R = Func (mapUnfolding-resp {X = SA} {Y = SB} sf)
      fg-eq : _≈U_ {X = SB} (mapUnfolding f u₂) (mapUnfolding g u₂)
      fg-eq = record
        { sl-eq = record
            { shape-eq    = λ _ → refl
            ; position-eq = λ _ _ → refl
            }
        ; unfold-next-eq = λ s → f≈g {unfold-next u₂ s}
        }
      module SBS = Setoid (unfoldingSetoid SB)
    in SBS.trans (R.cong u₁≈u₂) fg-eq

-- UnfoldingEndoFunctor — Unfolding as an endofunctor on Setoids
--
-- 展开函子作为 Setoids 上的自函子
module UnfoldingEndoFunctor {o h e s p : Level} {C : Category o h e}
                            {FC : Functor C (ContCat s p)} where
  open UnfoldingSetoid
  private
    L  = o ⊔ h ⊔ e ⊔ s ⊔ p
    Lʳ = o ⊔ s ⊔ p
    S = Setoids L Lʳ
    module S = Category S

  -- Object mapping: an unfolding of FC over X becomes an unfolding over Y
  --
  -- 对象映射：X 上的 FC 展开变为 Y 上的展开
  F₀ : S.Obj → S.Obj
  F₀ X = unfoldingSetoid {F = FC} X

  private
    -- Congruence of mapUnfolding with respect to _≈U_
    --
    -- mapUnfolding 关于 _≈U_ 的同余性
    mapUnfolding-cong : ∀ {X Y : S.Obj} (f : S._⇒_ X Y)
      → {u₁ u₂ : Unfolding FC (Setoid.Carrier X)}
      → Setoid._≈_ (F₀ X) u₁ u₂
      → Setoid._≈_ (F₀ Y) (mapUnfolding (Func.to f) u₁)
                            (mapUnfolding (Func.to f) u₂)
    mapUnfolding-cong f = Func.cong (mapUnfolding-resp {F = FC} f)

  -- Morphism mapping: lift a Setoid morphism to an unfolding morphism
  --
  -- 态射映射：将 Setoid 态射提升为展开态射
  F₁ : ∀ {X Y : S.Obj} → S._⇒_ X Y → S._⇒_ (F₀ X) (F₀ Y)
  F₁ f = record
    { to   = mapUnfolding (Func.to f)
    ; cong = mapUnfolding-cong f
    }

  private
    -- Identity law for the endofunctor
    --
    -- 自函子的恒等律
    identity-law : ∀ {X : S.Obj} → S._≈_ (F₁ (S.id {X})) (S.id {F₀ X})
    identity-law {X} {u} = ≈U-refl {X = X} {u}

    -- Composition law for the endofunctor
    --
    -- 自函子的复合律
    homomorphism-law : ∀ {X Y Z : S.Obj}
      {f : S._⇒_ X Y} {g : S._⇒_ Y Z}
      → S._≈_ (F₁ (g S.∘ f)) (F₁ g S.∘ F₁ f)
    homomorphism-law {X} {Y} {Z} {f} {g} {u} = ≈U-refl {X = Z}

    -- Equivalence preservation for the endofunctor
    --
    -- 自函子的等价保持
    F-resp-≈-law : ∀ {X Y : S.Obj} {f g : S._⇒_ X Y}
      → S._≈_ f g → S._≈_ (F₁ f) (F₁ g)
    F-resp-≈-law {X} {Y} {f} {g} f≈g {u} = record
      { sl-eq = record
          { shape-eq    = λ _ → refl
          ; position-eq = λ _ _ → refl
          }
      ; unfold-next-eq = λ {A} s →
          f≈g {x = Unfolding.unfold-next u {A = A} s}
      }

  -- The endofunctor on Setoids induced by unfolding
  --
  -- 由展开诱导的 Setoids 上的自函子
  UnfoldingEndoFunctor : Functor S S
  UnfoldingEndoFunctor = record
    { F₀           = F₀
    ; F₁           = F₁
    ; identity     = identity-law
    ; homomorphism = λ {X} {Y} {Z} {f} {g} {u} →
        homomorphism-law {X} {Y} {Z} {f} {g} {u}
    ; F-resp-≈     = λ {X} {Y} {f} {g} f≈g {u} →
        F-resp-≈-law {X} {Y} {f} {g} f≈g {u}
    }
