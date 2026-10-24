------------------------------------------------------------------------
-- Structural lemmas about the FinCat n tower (n ≥ 2)
--
-- Collects results depending only on the base layer FinCatN m,
-- independent of any limit construction: shape-set inhabitation and
-- singleton property at every layer, bijection between layer objects
-- and Fin n, canonical morphism between any two layer objects (hom),
-- collapsibility of every layer (nTower-collapsible), and canonical
-- retraction of a Cosmos into its base layer (nTower-retract).
-- The parameter m encodes n = suc (suc m), so that n ≥ 2 holds
-- definitionally
--
-- FinCat n 塔（n ≥ 2）的结构引理
--
-- 汇集只依赖基层 FinCatN m、不依赖任何极限构造的结果：每层形状集的
-- 可居留性与单点性、层对象与 Fin n 的双射、任意两个层对象之间的规范
-- 态射（hom）、每层的可坍缩性（nTower-collapsible）、从 Cosmos 到其
-- 基层的规范收缩（nTower-retract）。
-- 参数 m 编码 n = suc (suc m)，使 n ≥ 2 定义性成立
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module SecondPass.FinCatNTowerLemmas where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Level using (Lift; lift; lower)
open import Relation.Binary.PropositionalEquality.Core using (sym; cong; trans)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Fin using (Fin)
open import Data.Unit.Polymorphic.Base using (tt)
open import Data.Product.Base using (_,_; proj₁; proj₂)
open import Function.Bundles using (_⇔_; mk⇔)
open import Function.Base using (id)

open import Categories.Category.Core using (Category)
open import Categories.Functor.Core using (Functor)

open import Cosmos.ContCategoryLemmas using (ShapeOf; PosOf; actSOf)
open import SecondPass.Unfolding using (Unfolding)
open import SecondPass.Cosmos using (Cosmos; out)
open import SecondPass.StrictLift using (StrictLayer)
open import SecondPass.CumulativeHierarchy
  using (Collapsible; collapsible→ShapeCat-collapsible)
open import SecondPass.CumulativeHierarchyLimit using (Tower)
open import SecondPass.FinCatNWitness

open Function.Bundles.Equivalence using (to; from)
open StrictLayer
open Tower

-- Parameterised tower lemmas over FinCatN m
-- FinCatN m 上的参数化塔引理
module FinCatNTowerLemmas (m : ℕ) where

  open FinCatN m

  -- Shape set inhabitation at every layer
  -- Layer 0: lift tt; layer suc k: lift of the layer-k inhabitant
  -- 每层形状集的可居留性
  -- 第 0 层：lift tt；第 suc k 层：第 k 层居民的 lift
  shape-inhabited-at
    : ∀ k (A : Category.Obj (C (layer nTower k)))
    → ShapeOf (FC (layer nTower k)) A
  shape-inhabited-at zero    A       = lift tt
  shape-inhabited-at (suc k) (A , s) = lift (shape-inhabited-at k A)

  -- Shape set singleton property at every layer
  -- Layer 0: refl on lift tt; layer suc k: cong lift of the layer-k proof
  -- 每层形状集的单点性
  -- 第 0 层：lift tt 上的 refl；第 suc k 层：第 k 层证明的 cong lift
  shape-singleton-at
    : ∀ k (A : Category.Obj (C (layer nTower k)))
    → (s t : ShapeOf (FC (layer nTower k)) A) → s ≡ t
  shape-singleton-at zero    A       (lift tt) (lift tt) = refl
  shape-singleton-at (suc k) (A , _) (lift u)  (lift v)  =
    cong lift (shape-singleton-at k A u v)

  -- Object projection C_k → Fin n by iterated proj₁
  -- proj-obj k is a retraction of embed-obj k
  -- 对象投影 C_k → Fin n，反复取 proj₁
  -- proj-obj k 是 embed-obj k 的收缩
  proj-obj : ∀ k → Category.Obj (C (layer nTower k)) → Fin n
  proj-obj zero    A       = A
  proj-obj (suc k) (A , _) = proj-obj k A

  -- Object embedding Fin n → C_k, mutually recursive with embed-shape,
  -- which supplies the required shape component
  -- 对象嵌入 Fin n → C_k，与 embed-shape 互递归，
  -- 后者提供所需的形状分量
  mutual
    embed-obj : ∀ k → Fin n → Category.Obj (C (layer nTower k))
    embed-obj zero    A = A
    embed-obj (suc k) A = (embed-obj k A , embed-shape k (embed-obj k A))

    -- Shape component of an embedded object
    -- 嵌入对象的形状分量
    embed-shape : ∀ k (A : Category.Obj (C (layer nTower k)))
                → ShapeOf (FC (layer nTower k)) A
    embed-shape zero    _       = lift tt
    embed-shape (suc k) (A , _) = lift (embed-shape k A)

  -- Bijection between layer objects and Fin n
  -- Layer 0: identity; layer suc k: inherited, shape component from
  -- shape-inhabited-at
  -- 层对象与 Fin n 的双射
  -- 第 0 层：恒等；第 suc k 层：继承自第 k 层，
  -- 形状分量由 shape-inhabited-at 提供
  layer-obj-bijection
    : ∀ k → Category.Obj (C (layer nTower k)) ⇔ Fin n
  layer-obj-bijection zero    = mk⇔ id id
  layer-obj-bijection (suc k) =
    mk⇔ (λ { (A , _) → to (layer-obj-bijection k) A })
         (λ A → from (layer-obj-bijection k) A
                , shape-inhabited-at k (from (layer-obj-bijection k) A))

  -- Canonical morphism between any two layer objects
  -- Every layer is collapsible, so the morphism is unique up to _≈_
  -- Layer 0: tt (Indiscrete (Fin n))
  -- Layer suc k: pair (hom k A B , eq), eq from shape-singleton-at
  -- 任意两个层对象之间的规范态射
  -- 每层可坍缩，故态射在 _≈_ 意义下唯一
  -- 第 0 层：tt（Indiscrete (Fin n)）
  -- 第 suc k 层：(hom k A B , eq) 对，eq 由 shape-singleton-at 提供
  hom : (k : ℕ) (X Y : Category.Obj (StrictLayer.C (Tower.layer nTower k)))
      → Category._⇒_ (StrictLayer.C (Tower.layer nTower k)) X Y
  hom zero    X Y = tt
  hom (suc k) (A , s) (B , t) = (hom k A B , eq)
    where
      FC_k = StrictLayer.FC (Tower.layer nTower k)
      eq   = shape-singleton-at k B (actSOf FC_k (hom k A B) s) t

  -- Collapsibility of every layer: any two parallel morphisms are
  -- _≈_-equivalent
  -- Layer 0: refl; layer suc k: inherited via
  -- collapsible→ShapeCat-collapsible
  -- 每层的可坍缩性：任意两个平行态射 _≈_ 等价
  -- 第 0 层：refl；第 suc k 层：经 collapsible→ShapeCat-collapsible 继承
  nTower-collapsible : (k : ℕ)
    → Collapsible (StrictLayer.C (Tower.layer nTower k))
  nTower-collapsible zero    = λ _ _ → refl
  nTower-collapsible (suc k) =
    collapsible→ShapeCat-collapsible
      {C  = StrictLayer.C (Tower.layer nTower k)}
      {FC = StrictLayer.FC (Tower.layer nTower k)}
      (nTower-collapsible k)

  -- Canonical retraction of a Cosmos into its base layer
  -- For x at layer k and shape s at object A, the retraction is the
  -- unique morphism x.F₀ (A , s) → A, obtained via hom
  -- Used as the retract argument of mkEmbeddingData downstream
  -- 从 Cosmos 到其基层的规范收缩
  -- 对第 k 层的 x 与对象 A 上的形状 s，收缩是唯一态射
  -- x.F₀ (A , s) → A，由 hom 给出
  -- 在下游用作 mkEmbeddingData 的 retract 参数
  nTower-retract : (k : ℕ)
    (x : Cosmos (StrictLayer.C (Tower.layer nTower k))
                (StrictLayer.FC (Tower.layer nTower k)))
    {A : Category.Obj (StrictLayer.C (Tower.layer nTower k))}
    (s : ShapeOf (StrictLayer.FC (Tower.layer nTower k)) A)
    → Category._⇒_ (StrictLayer.C (Tower.layer nTower k))
        (Functor.₀ (Unfolding.unfoldFunctor (out x)) (A , s)) A
  nTower-retract k x {A} s =
    hom k (Functor.₀ (Unfolding.unfoldFunctor (out x)) (A , s)) A

  -- x.pos-to-shape collapses to the second component of x.F₀
  -- x.pos-to-shape 塌缩为 x.F₀ 的第二分量
  x-pos-eq : ∀ k
    (x : Cosmos (StrictLayer.C (Tower.layer nTower (suc k)))
                (StrictLayer.FC (Tower.layer nTower (suc k))))
    (A : Category.Obj (StrictLayer.C (Tower.layer nTower k)))
    (s : ShapeOf (StrictLayer.FC (Tower.layer nTower k)) A)
    (s' : ShapeOf (StrictLayer.FC (Tower.layer nTower (suc k))) (A , s))
    (p : PosOf (StrictLayer.FC (Tower.layer nTower (suc k))) {A = (A , s)} s')
    → Unfolding.pos-to-shape (out x) {A = (A , s)} s' p
    ≡ lift (proj₂ (Unfolding.unfoldFunctor (out x) .Functor.F₀ ((A , s) , s')))
  x-pos-eq k x A s s' p =
    trans (sym (lower-lift-eq (Unfolding.pos-to-shape (out x) {A = (A , s)} s' p)))
          (cong lift (shape-singleton-at k
            (proj₁ (Unfolding.unfoldFunctor (out x) .Functor.F₀ ((A , s) , s')))
            (lower (Unfolding.pos-to-shape (out x) {A = (A , s)} s' p))
            (proj₂ (Unfolding.unfoldFunctor (out x) .Functor.F₀ ((A , s) , s')))))
    where
      lower-lift-eq : ∀ {a b} {A : Set a} (u : Lift b A) → lift (lower u) ≡ u
      lower-lift-eq (lift _) = refl
