------------------------------------------------------------------------
-- Cumulative Hierarchy of Cosmoi — Core Abstraction
--
-- Defines the iteration of shape categories: Cₙ₊₁ = ShapeCat Cₙ FCₙ,
-- FCₙ₊₁ = FCₙ ∘F π, together with the coinductive embedding construction
-- from EmbeddingData, the consistency conditions for uniform families,
-- and the Lambek consistency package.  Concrete instances are provided in
-- the separate module CumulativeHierarchyInstances
--
-- 宇宙的累积层级 —— 核心抽象
--
-- 定义形状范畴的迭代：Cₙ₊₁ = ShapeCat Cₙ FCₙ，FCₙ₊₁ = FCₙ ∘F π，
-- 并给出由 EmbeddingData 构造的余归纳嵌入、一致族应满足的一致性条件，
-- 以及 Lambek 一致性封装。 具体实例在单独的 CumulativeHierarchyInstances
-- 模块中提供
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module SecondPass.CumulativeHierarchy where

open import Agda.Primitive using (Level; _⊔_; lsuc)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Sigma using (_,_)
open import Data.Product.Base using (proj₁; proj₂)
open import Relation.Binary.PropositionalEquality.Core using (cong; sym; subst)
open import Relation.Binary.PropositionalEquality.Properties using (module ≡-Reasoning)

open import Categories.Category.Core using (Category)
open import Categories.Functor.Core using (Functor)
open import Categories.Functor using (_∘F_)

open import Cosmos.ContCategory using (ContCat; _≈sr_)
open import Cosmos.ContCategoryLemmas using (ShapeOf; PosOf; actSOf; actPOf)
open import Cosmos.ContCatEquiv using (ShapeCat)
open import SecondPass.Unfolding using (Unfolding)
open import SecondPass.Cosmos using (Cosmos; out)
open import SecondPass.Terminal using (_≈C_)
open import SecondPass.Lambek using (in-F; in∘out≈id)

-- The projection functor from the shape category back to the base category
--
-- 从形状范畴返回到基范畴的投影函子
π : ∀ {o h e s p : Level} (C : Category o h e) (FC : Functor C (ContCat s p))
  → Functor (ShapeCat C FC) C
π C FC = record
  { F₀           = proj₁
  ; F₁           = proj₁
  ; identity     = λ {A} → Equiv.refl
  ; homomorphism = λ {X} {Y} {Z} {f} {g} → Equiv.refl
  ; F-resp-≈     = λ f≈g → f≈g
  }
  where open Category C

-- Composition of the container functor with the projection π
--
-- 容器函子与投影 π 的复合
FC∘π : ∀ {o h e s p} {C : Category o h e} (FC : Functor C (ContCat s p))
     → Functor (ShapeCat C FC) (ContCat s p)
FC∘π {C = C} FC = FC ∘F π C FC

-- A layer consists of a base category C and a container functor FC over it
--
-- 一个层级由一个基范畴 C 及其上的容器函子 FC 构成
record Layer (o h e s p : Level) : Set (lsuc (o ⊔ h ⊔ e ⊔ s ⊔ p)) where
  field
    C  : Category o h e
    -- The container-valued functor over C, whose unfolding defines
    -- the next layer
    --
    -- C 上的容器值函子，其展开定义下一层
    FC : Functor C (ContCat s p)

open Layer public

-- Step to the next layer: C ↦ ShapeCat C FC, FC ↦ FC∘π FC
--
-- 步进到下一层：C 映为 ShapeCat C FC，FC 映为 FC∘π FC
step : ∀ {o h e s p} → Layer o h e s p → Layer (o ⊔ s) (h ⊔ s) e s p
step L = record
  { C  = ShapeCat (Layer.C L) (Layer.FC L)
  ; FC = FC∘π (Layer.FC L)
  }

-- The unfolding functor of the embedded cosmos: it forgets the outer shape
-- and keeps the inner one, mapping ((A, s), q) to (A, q)
--
-- 嵌入后宇宙的展开函子：遗忘外层形状，保留内层形状，
-- 将 ((A, s), q) 映到 (A, q)
embed-unfoldFunctor : ∀ {o h e s p} {C : Category o h e}
  → (FC : Functor C (ContCat s p))
  → Functor (ShapeCat (ShapeCat C FC) (FC∘π FC)) (ShapeCat C FC)
embed-unfoldFunctor {C = C} FC = record
  { F₀           = λ z → (proj₁ (proj₁ z) , proj₂ z)
  ; F₁           = λ f → (proj₁ (proj₁ f) , proj₂ f)
  ; identity     = λ {A} → Equiv.refl {proj₁ (proj₁ A)} {proj₁ (proj₁ A)}
  ; homomorphism = λ {X} {Y} {Z} {f} {g} →
                     Equiv.refl {proj₁ (proj₁ X)} {proj₁ (proj₁ Z)}
                                 {proj₁ (proj₁ g) ∘ proj₁ (proj₁ f)}
  ; F-resp-≈     = λ f≈g → f≈g
  }
  where open Category C

-- EmbeddingData packages, for a cosmos x, a retraction per shape together
-- with its naturality and the recursive data on next seeds
--
-- 嵌入数据为宇宙 x 打包：逐形状的收缩态射、其自然性、
-- 以及下一层种子上的递归数据
record EmbeddingData {o h e s p} {C : Category o h e} {FC : Functor C (ContCat s p)}
  (x : Cosmos C FC) : Set (o ⊔ h ⊔ e ⊔ s ⊔ p) where
  coinductive
  private
    module C  = Category C
    UX = out x
    module UX = Unfolding UX
  field
    -- Retraction: for each shape s, a C-morphism from the unfolded
    -- object back to the original object A
    --
    -- 收缩态射：对每个形状 s，给出从展开对象回到原对象 A 的 C-态射
    retract : ∀ {A} (s : ShapeOf FC A)
            → C._⇒_ (Functor.₀ UX.unfoldFunctor (A , s)) A

    -- Naturality of the retraction: pre-composing with f then retracting
    -- equals retracting then applying the functorial action of UX
    --
    -- 收缩态射的自然性：先与 f 前复合再收缩，等于先收缩再施加 UX 的函子作用
    retract-natural : ∀ {A B} {s : ShapeOf FC A} {t : ShapeOf FC B}
                    → (f : A C.⇒ B) (eq : actSOf FC f s ≡ t)
                    → C._≈_ (f C.∘ retract s)
                             (retract t C.∘ Functor.₁ UX.unfoldFunctor (f , eq))

    -- Recursive data: each next seed carries its own embedding data,
    -- making the construction coinductive
    --
    -- 递归数据：每个下一层种子携带其自身的嵌入数据，使该构造成为余归纳的
    next : ∀ {A} (s : ShapeOf FC A) → EmbeddingData (UX.unfold-next s)

-- In a shape category, composing with identity on either side agrees
--
-- 形状范畴中，任一侧与恒等复合都一致
ShapeCat-id-comm
  : ∀ {o h e s p} {C : Category o h e} {FC : Functor C (ContCat s p)}
  → (X Y : Category.Obj (ShapeCat C FC))
  → (g : Category._⇒_ (ShapeCat C FC) X Y)
  → Category._≈_ C
      (Category._∘_ C (proj₁ g) (Category.id C))
      (Category._∘_ C (Category.id C) (proj₁ g))
ShapeCat-id-comm {C = C} X Y g =
  C.Equiv.trans
    (C.identityʳ {f = proj₁ g})
    (C.Equiv.sym (C.identityˡ {f = proj₁ g}))
  where
    module C = Category C

-- Compatibility of pos-to-shape with the functorial action
-- Relies only on pos-actS-compat, FC's functoriality, and retract-natural
--
-- pos-to-shape 与函子作用的相容性
-- 仅依赖 pos-actS-compat、FC 函子性与 retract-natural
embed-compat :
  ∀ {o h e s p} {C : Category o h e} {FC : Functor C (ContCat s p)}
    {x : Cosmos C FC} (ed : EmbeddingData x)
    {A B : Category.Obj C} {s : ShapeOf FC A} {t : ShapeOf FC B}
  → (f : Category._⇒_ C A B) (eq : actSOf FC f s ≡ t)
  → (p : PosOf FC (actSOf FC f s))
  → actSOf FC (EmbeddingData.retract ed t)
      (Unfolding.pos-to-shape (out x) t (subst (PosOf FC) eq p))
    ≡ actSOf FC f
      (actSOf FC (EmbeddingData.retract ed s)
         (Unfolding.pos-to-shape (out x) s (actPOf FC f s p)))
embed-compat {C = C} {FC = FC} {x = x} ed {A} {B} {s} {t} f eq p =
  begin
    actSOf FC (retract t) (UX.pos-to-shape t (subst (PosOf FC) eq p))
      ≡⟨ cong (actSOf FC (retract t)) (UX.pos-actS-compat f eq p) ⟩
    actSOf FC (retract t) (actSOf FC g₁ x₀)
      ≡⟨ sym (_≈sr_.shape-eq
              (FC.homomorphism {X = X₀} {Y = Y₀} {Z = B}
                               {f = g₁} {g = retract t}) x₀) ⟩
    actSOf FC (retract t C.∘ g₁) x₀
      ≡⟨ sym (_≈sr_.shape-eq
              (FC.F-resp-≈ {A = X₀} {B = B}
                           {f = f C.∘ retract s}
                           {g = retract t C.∘ g₁}
                           (retract-natural f eq)) x₀) ⟩
    actSOf FC (f C.∘ retract s) x₀
      ≡⟨ _≈sr_.shape-eq
         (FC.homomorphism {X = X₀} {Y = A} {Z = B}
                          {f = retract s} {g = f}) x₀ ⟩
    actSOf FC f (actSOf FC (retract s) x₀)
  ∎
  where
    open EmbeddingData ed
    open ≡-Reasoning
    module C  = Category C
    module FC = Functor FC
    UX = out x
    module UX = Unfolding UX
    x₀ = UX.pos-to-shape s (actPOf FC f s p)
    g₁ = Functor.₁ UX.unfoldFunctor (f , eq)
    X₀ = Functor.₀ UX.unfoldFunctor (A , s)
    Y₀ = Functor.₀ UX.unfoldFunctor (B , t)

-- embed constructs the embedded cosmos from an EmbeddingData
--
-- embed 从 EmbeddingData 构造嵌入后的宇宙
embed : ∀ {o h e s p} {C : Category o h e} {FC : Functor C (ContCat s p)}
      → (x : Cosmos C FC) → EmbeddingData x
      → Cosmos (ShapeCat C FC) (FC∘π FC)
embed {C = C} {FC = FC} x ed .out = record
  { unfoldFunctor   = embed-unfoldFunctor FC
  ; unfold-next     = λ { {A , _} p → embed (UX.unfold-next p) (next p) }
  ; pos-to-shape    = λ { {A , _} p q → actSOf FC (retract p) (UX.pos-to-shape p q) }
  ; pos-actS-compat = λ { {A , _} {B , _} {s} {t} (f , _) eq p →
                        embed-compat ed f eq p }
  }
  where
    open EmbeddingData ed
    UX = out x
    module UX = Unfolding UX

-- An EmbeddingFamily assigns EmbeddingData to every cosmos
--
-- 嵌入族为每个宇宙分配嵌入数据
record EmbeddingFamily {o h e s p} {C : Category o h e} {FC : Functor C (ContCat s p)}
  : Set (lsuc (o ⊔ h ⊔ e ⊔ s ⊔ p)) where
  field
    getData : (x : Cosmos C FC) → EmbeddingData x

  embed′ : Cosmos C FC → Cosmos (ShapeCat C FC) (FC∘π FC)
  embed′ x = embed x (getData x)

-- A UniformEmbeddingFamily additionally requires the recursive data to be
-- consistent with the unfolding structure
--
-- 一致嵌入族额外要求递归数据与展开结构一致
record UniformEmbeddingFamily {o h e s p} {C : Category o h e} {FC : Functor C (ContCat s p)}
  : Set (lsuc (o ⊔ h ⊔ e ⊔ s ⊔ p)) where
  field
    -- The underlying (non-uniform) embedding family
    --
    -- 底层的（非一致）嵌入族
    family : EmbeddingFamily {C = C} {FC = FC}
  open EmbeddingFamily family public

  field
    -- Consistency: data assigned to x via shape s agrees with data
    -- assigned to the next seed of x directly
    --
    -- 一致性：经形状 s 分配给 x 的数据，
    -- 与直接分配给 x 的下一层种子的数据一致
    next-consistent : ∀ (x : Cosmos C FC) {A} (s : ShapeOf FC A)
                    → getData x .EmbeddingData.next s
                      ≡ getData (Unfolding.unfold-next (out x) s)

-- A FunctorialEmbeddingFamily ensures that the embedding preserves the
-- bisimulation _≈C_, turning it into a genuine functor between setoids
--
-- 函子性嵌入族保证嵌入保持互模拟 _≈C_，从而成为集合oid 之间的真正函子
record FunctorialEmbeddingFamily {o h e s p} {C : Category o h e} {FC : Functor C (ContCat s p)}
  : Set (lsuc (o ⊔ h ⊔ e ⊔ s ⊔ p)) where
  field
    -- The underlying uniform embedding family
    --
    -- 底层的一致嵌入族
    uniform : UniformEmbeddingFamily {C = C} {FC = FC}
  open UniformEmbeddingFamily uniform public
  field

    -- Turns embed′ into a genuine functor between setoids
    --
    -- 使 embed′ 成为 Setoid 之间的真正函子
    embed′-resp-≈C : ∀ {x y} → x ≈C y → embed′ x ≈C embed′ y

-- liftUnfolding packages the unfolding of an embedded cosmos
--
-- liftUnfolding 封装嵌入后宇宙的展开
liftUnfolding : ∀ {o h e s p} {C : Category o h e} {FC : Functor C (ContCat s p)}
  (x : Cosmos C FC) (ed : EmbeddingData x)
  → Unfolding (FC∘π FC) (Cosmos (ShapeCat C FC) (FC∘π FC))
liftUnfolding x ed = out (embed x ed)

-- For categories where all morphisms are equal (collapsible), an
-- EmbeddingData can be constructed from just a retraction and a proof
-- that all morphisms are equal
--
-- 对于所有态射均相等的退化范畴，仅需收缩态射和“所有态射相等”的证明即可构造 EmbeddingData
mkEmbeddingData : ∀ {o h e s p} {C : Category o h e} {FC : Functor C (ContCat s p)}
  → (retract : ∀ (x : Cosmos C FC) {A} (s : ShapeOf FC A)
             → Category._⇒_ C (Functor.₀ (Unfolding.unfoldFunctor (out x)) (A , s)) A)
  → (unique : ∀ {A B} (f g : Category._⇒_ C A B) → Category._≈_ C f g)
  → (x : Cosmos C FC) → EmbeddingData x
mkEmbeddingData retract unique x .EmbeddingData.retract = retract x
mkEmbeddingData retract unique x .EmbeddingData.retract-natural = λ _ _ → unique _ _
mkEmbeddingData retract unique x .EmbeddingData.next =
  λ s → mkEmbeddingData retract unique (Unfolding.unfold-next (out x) s)

-- Collapsible means that all parallel morphisms are equivalent
--
-- 退化范畴即任意两个平行态射等价
Collapsible : ∀ {o h e} → Category o h e → Set (o ⊔ h ⊔ e)
Collapsible C = ∀ {A B} (f g : Category._⇒_ C A B) → Category._≈_ C f g

-- Shape category of a collapsible category is again collapsible
--
-- 退化范畴的形状范畴仍是退化的
collapsible→ShapeCat-collapsible : ∀ {o h e s p}
  {C : Category o h e} {FC : Functor C (ContCat s p)}
  → Collapsible C → Collapsible (ShapeCat C FC)
collapsible→ShapeCat-collapsible collapse (f , _) (g , _) = collapse f g

-- LambekConsistency records how the embedding interacts with the
-- terminal-coalgebra structure (in-F/out weak isomorphism)
--
-- Lambek 一致性记录嵌入与终余代数结构（in-F/out 弱同构）的交互
record LambekConsistency {o h e s p} {C : Category o h e} {FC : Functor C (ContCat s p)}
  (fam : UniformEmbeddingFamily {C = C} {FC = FC})
  : Set (lsuc (o ⊔ h ⊔ e ⊔ s ⊔ p)) where
  open UniformEmbeddingFamily fam
  private
    C′ = ShapeCat C FC
    FC′ = FC∘π FC

    -- Lambek inverse of the embedded layer
    --
    -- 嵌入层的 Lambek 逆
    in-F′ : Unfolding FC′ (Cosmos C′ FC′) → Cosmos C′ FC′
    in-F′ = in-F {C = C′} {FC = FC′}
    
    -- Next-seed map of x, used to state out-consistency
    --
    -- x 的下一层种子映射，用于陈述 out-consistency
    UX-next : (x : Cosmos C FC) {A₀ : Category.Obj C} (s : ShapeOf FC A₀)
            → Cosmos C FC
    UX-next x {A₀} s = Unfolding.unfold-next (out x) {A = A₀} s
  
  field
    -- Consistency with in-F: embedding commutes with the Lambek inverse
    -- up to bisimulation
    --
    -- 与 in-F 的一致性：嵌入与 Lambek 逆在互模拟意义下交换
    in-F-consistency : ∀ (y : Unfolding FC (Cosmos C FC))
                     → in-F′ (out (embed′ (in-F y))) ≈C embed′ (in-F y)

    -- Consistency with out: embedding commutes with the next-seed map
    -- on the nose
    --
    -- 与 out 的一致性：嵌入与下一层种子映射严格交换
    out-consistency : ∀ (x : Cosmos C FC) {A₀ : Category.Obj C} (s : ShapeOf FC A₀)
                    → Unfolding.unfold-next (out (embed′ x)) {A = (A₀ , s)} s
                      ≡ embed′ (UX-next x s)

-- The laws follow directly from the Lambek lemma and next-consistent
--
-- 定律直接来自 Lambek 引理与 next-consistent 条件
mkLambekConsistency : ∀ {o h e s p} {C : Category o h e} {FC : Functor C (ContCat s p)}
  → (fam : UniformEmbeddingFamily {C = C} {FC = FC})
  → LambekConsistency fam
mkLambekConsistency {C = C} {FC = FC} fam =
  let
    open UniformEmbeddingFamily fam
    C′ = ShapeCat C FC
    FC′ = FC∘π FC
    in∘out≈id′ = in∘out≈id {C = C′} {FC = FC′}
    UX-next : (x : Cosmos C FC) {A₀ : Category.Obj C} (s : ShapeOf FC A₀)
            → Cosmos C FC
    UX-next x {A₀} s = Unfolding.unfold-next (out x) {A = A₀} s
  in record
    { in-F-consistency = λ y → in∘out≈id′ (embed′ (in-F y))
    ; out-consistency  = λ x {A₀} s → cong (λ ed → embed (UX-next x s) ed) (next-consistent x s)
    }
