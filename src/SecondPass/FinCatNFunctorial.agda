------------------------------------------------------------------------
-- Functoriality of the FinCat n tower at every layer
-- FinCat n 塔每一层上的函子性
--
-- The default uniform embedding family of the FinCat n tower is
-- functorial at every layer: for each k, embed′ k preserves _≈C_, and
-- strictEmbed preserves _≈C_. The proof rests on two tower-intrinsic
-- facts: F₀ of the layer container functor is invariant under arbitrary
-- morphisms, and actSOf coincides with substitution along that
-- invariance proof. These yield the EmbedFamily at every layer and the
-- EnrichedTower instance along the outer-preserving rule. The parameter
-- m encodes n = suc (suc m), so n ≥ 2 holds definitionally
-- FinCat n 塔的默认一致嵌入族在每一层上均函子性：对每个 k，
-- embed′ k 保持 _≈C_，且 strictEmbed 保持 _≈C_。证明依赖两个塔的
-- 固有事实：层容器函子的 F₀ 在任意态射下不变，且 actSOf 与沿该
-- 不变性证明的替换重合。由此给出每一层的 EmbedFamily 与沿保外层
-- 规则的 EnrichedTower 实例。参数 m 编码 n = suc (suc m)，
-- 使 n ≥ 2 定义性成立
------------------------------------------------------------------------
{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module SecondPass.FinCatNFunctorial where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality.Core using (sym; cong; subst; trans)
open import Relation.Binary.PropositionalEquality.Properties
  using (module ≡-Reasoning; subst-∘; subst-subst)
open ≡-Reasoning
open import Level using (lift; lower)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product.Base using (proj₁; _,_)
open import Data.Container.Core using (Container; Shape)
open import Categories.Category.Core using (Category)
open import Categories.Functor.Core using (Functor)

open import Cosmos.ContCategoryLemmas using (ShapeOf; actSOf)
open import Cosmos.ContCatEquiv using (ShapeCat)
open import SecondPass.Unfolding using (Unfolding)
open import SecondPass.Cosmos using (Cosmos; out)
open import SecondPass.Terminal using (_≈C_)
open import SecondPass.CumulativeHierarchy
  using (UniformEmbeddingFamily; EmbeddingData; FC∘π)
open import SecondPass.StrictLift
  using (StrictLayer; LiftContainer; strictEmbed; strictStep-suc; outer-rule; EmbedFamily)
open import SecondPass.CumulativeHierarchyLimit using (Tower; EnrichedTower)
open import SecondPass.FinCatNWitness
open import SecondPass.FinCatNColimitWithDep
open import SecondPass.FinCatNDefaultUnif

-- Substitution commutes with lift along LiftContainer-equality
-- 沿 LiftContainer 等式的替换与 lift 交换
subst-Shape-LiftContainer : ∀ {s p s′ p′} {X Y : Container s p}
  (eq : X ≡ Y) (u : Shape X)
  → subst Shape (cong (LiftContainer s′ p′) eq) (lift u)
    ≡ lift (subst Shape eq u)
subst-Shape-LiftContainer refl u = refl

-- Parameterised construction over FinCatN m
-- FinCatN m 上的参数化构造
module FinCatNFunctorial (m : ℕ) where

  open FinCatN m
  open FinCatNColimitWithDep m using (UniformEmbeddingFamilyForTower)
  open FinCatNDefaultUnif m using (default-unif)

  -- F₀ of the layer container functor is invariant under morphisms
  -- 层容器函子的 F₀ 在态射下不变
  tower-F₀-irrelevant : ∀ k →
    let L   = Tower.layer nTower k
        CN  = StrictLayer.C L
        FCN = StrictLayer.FC L
    in
    ∀ {A B} (f : Category._⇒_ CN A B)
    → Functor.F₀ FCN A ≡ Functor.F₀ FCN B
  tower-F₀-irrelevant zero    f       = refl
  tower-F₀-irrelevant (suc k) (f , _) =
    cong (LiftContainer _ _) (tower-F₀-irrelevant k f)

  -- actSOf coincides with substitution along F₀-invariance
  -- actSOf 与沿 F₀ 不变性的替换重合
  tower-actSOf-id : ∀ k →
    let L   = Tower.layer nTower k
        CN  = StrictLayer.C L
        FCN = StrictLayer.FC L
    in
    ∀ {A B} (f : Category._⇒_ CN A B)
    (s : ShapeOf FCN A)
    → actSOf FCN f s ≡ subst Shape (tower-F₀-irrelevant k f) s
  tower-actSOf-id zero    f       s         = refl
  tower-actSOf-id (suc k) (f , _) (lift s) =
    trans (cong lift (tower-actSOf-id k f s))
          (sym (subst-Shape-LiftContainer (tower-F₀-irrelevant k f) s))

  -- The F₀-invariance proof is independent of the morphism
  -- F₀ 不变性证明与态射无关
  tower-F₀-irrelevant-irrelevant : ∀ k →
    let L   = Tower.layer nTower k
        CN  = StrictLayer.C L
        FCN = StrictLayer.FC L
    in
    ∀ {A B} (f g : Category._⇒_ CN A B)
    → tower-F₀-irrelevant k f ≡ tower-F₀-irrelevant k g
  tower-F₀-irrelevant-irrelevant zero    f       g       = refl
  tower-F₀-irrelevant-irrelevant (suc k) (f , _) (g , _) =
    cong (cong (LiftContainer _ _))
         (tower-F₀-irrelevant-irrelevant k f g)

  -- Decomposition of F₀-invariance along an object equality
  -- F₀ 不变性沿对象等式的分解
  tower-F₀-irrelevant-decomp : ∀ k →
    let L   = Tower.layer nTower k
        CN  = StrictLayer.C L
        FCN = StrictLayer.FC L
    in
    ∀ {X Y A₀ : Category.Obj CN}
    (eq₀ : X ≡ Y)
    (retract-x : Category._⇒_ CN X A₀)
    (retract-y : Category._⇒_ CN Y A₀)
    → tower-F₀-irrelevant k retract-x
      ≡ trans (cong (Functor.F₀ FCN) eq₀)
              (tower-F₀-irrelevant k retract-y)
  tower-F₀-irrelevant-decomp k refl rx ry =
    tower-F₀-irrelevant-irrelevant k rx ry

  -- Functorial embedding family at every layer
  -- 每一层上的函子性嵌入族
  record FunctorialEmbeddingFamilyForTower : Setω where
    field
      -- The underlying uniform embedding family
      -- 底层一致嵌入族
      uniform : UniformEmbeddingFamilyForTower

    module Fam (k : ℕ) = UniformEmbeddingFamily (uniform k)

    field
      -- Functoriality of the single-step embedding at every layer
      -- 单步嵌入在每一层上的函子性
      embed′-resp-≈C : ∀ k →
        let L   = Tower.layer nTower k
            CN  = StrictLayer.C L
            FCN = StrictLayer.FC L
        in
        ∀ {x y : Cosmos CN FCN}
        → _≈C_ {C = CN} {FC = FCN} x y
        → _≈C_ {C = ShapeCat CN FCN} {FC = FC∘π FCN}
             (Fam.embed′ k x) (Fam.embed′ k y)

  -- Functoriality of the default family
  -- 默认族的函子性
  module _ (k : ℕ) where
    private
      L   = Tower.layer nTower k
      CN  = StrictLayer.C L
      FCN = StrictLayer.FC L
      CN1 = ShapeCat CN FCN
      FCN1 = FC∘π FCN
      embed′-default = UniformEmbeddingFamily.embed′ (default-unif k)

    -- The default single-step embedding preserves _≈C_
    -- 默认单步嵌入保持 _≈C_
    default-resp-≈C : ∀ {x y : Cosmos CN FCN}
      → _≈C_ {C = CN} {FC = FCN} x y
      → _≈C_ {C = CN1} {FC = FCN1} (embed′-default x) (embed′-default y)
    default-resp-≈C {x} {y} = go x y
      where
      go : (x y : Cosmos CN FCN)
         → _≈C_ {C = CN} {FC = FCN} x y
         → _≈C_ {C = CN1} {FC = FCN1} (embed′-default x) (embed′-default y)

      go x y x≈y ._≈C_.unfoldFunctor₀-eq {A} s = refl
      go x y x≈y ._≈C_.pos-to-shape-eq {A} s p =
        begin
          Unfolding.pos-to-shape (out (embed′-default x)) {A = A} s p
            ≡⟨ refl ⟩
          actSOf FCN retract-x x-pts
            ≡⟨ tower-actSOf-id k retract-x x-pts ⟩
          subst Shape (tower-F₀-irrelevant k retract-x) x-pts
            ≡⟨ cong (λ q → subst Shape q x-pts)
                     (tower-F₀-irrelevant-decomp k eq₀ retract-x retract-y) ⟩
          subst Shape
            (trans (cong (Functor.F₀ FCN) eq₀) (tower-F₀-irrelevant k retract-y))
            x-pts
            ≡⟨ sym (subst-subst (cong (Functor.F₀ FCN) eq₀)
                                {y≡z = tower-F₀-irrelevant k retract-y}
                                {p = x-pts}) ⟩
          subst Shape (tower-F₀-irrelevant k retract-y)
            (subst Shape (cong (Functor.F₀ FCN) eq₀) x-pts)
            ≡⟨ cong (λ z → subst Shape (tower-F₀-irrelevant k retract-y) z)
                     (sym (subst-∘ {P = Shape} {f = Functor.F₀ FCN}
                                   eq₀ {p = x-pts})) ⟩
          subst Shape (tower-F₀-irrelevant k retract-y)
            (subst (ShapeOf FCN) eq₀ x-pts)
            ≡⟨ cong (λ z → subst Shape (tower-F₀-irrelevant k retract-y) z) pts-eq ⟩
          subst Shape (tower-F₀-irrelevant k retract-y) y-pts
            ≡⟨ sym (tower-actSOf-id k retract-y y-pts) ⟩
          actSOf FCN retract-y y-pts
            ≡⟨ sym refl ⟩
          Unfolding.pos-to-shape (out (embed′-default y)) {A = A} s p
        ∎
        where
          A₀     = proj₁ A
          eq₀    = _≈C_.unfoldFunctor₀-eq x≈y {A = A₀} s
          pts-eq = _≈C_.pos-to-shape-eq x≈y {A = A₀} s p
          x-pts  = Unfolding.pos-to-shape (out x) {A = A₀} s p
          y-pts  = Unfolding.pos-to-shape (out y) {A = A₀} s p
          retract-x = EmbeddingData.retract
                        (UniformEmbeddingFamily.getData (default-unif k) x) s
          retract-y = EmbeddingData.retract
                        (UniformEmbeddingFamily.getData (default-unif k) y) s

      -- Corecursive descent: unfold both sides, recurse on the next seeds
      -- 余递归下降：展开两侧，在下一层种子上递归
      go x y x≈y ._≈C_.unfold-next-eq {A} s =
        go (Unfolding.unfold-next (out x) {A = proj₁ A} s)
           (Unfolding.unfold-next (out y) {A = proj₁ A} s)
           (_≈C_.unfold-next-eq x≈y {A = proj₁ A} s)

    -- strictEmbed preserves _≈C_, reusing default-resp-≈C
    -- strictEmbed 保持 _≈C_，复用 default-resp-≈C
    default-strictEmbed-resp-≈C : ∀ {x y : Cosmos CN FCN}
      → _≈C_ {C = CN} {FC = FCN} x y
      → _≈C_ {C = StrictLayer.C (strictStep-suc L)}
             {FC = StrictLayer.FC (strictStep-suc L)}
           (strictEmbed L x
              (UniformEmbeddingFamily.getData (default-unif k) x))
           (strictEmbed L y
              (UniformEmbeddingFamily.getData (default-unif k) y))
    default-strictEmbed-resp-≈C {x} {y} = go x y
      where
      go : (x y : Cosmos CN FCN)
         → _≈C_ {C = CN} {FC = FCN} x y
         → _≈C_ {C = StrictLayer.C (strictStep-suc L)}
                {FC = StrictLayer.FC (strictStep-suc L)}
              (strictEmbed L x
                 (UniformEmbeddingFamily.getData (default-unif k) x))
              (strictEmbed L y
                 (UniformEmbeddingFamily.getData (default-unif k) y))

      -- Both strictEmbeddings share strictEmbed-unfoldFunctor L, independent of x/y
      -- 两个 strictEmbed 共用 strictEmbed-unfoldFunctor L，不依赖于 x/y
      go x y x≈y ._≈C_.unfoldFunctor₀-eq {A} s = refl

      -- Lower the lifted shape/position, apply default-resp-≈C's pos-to-shape-eq,
      -- then re-lift the result
      -- 对提升后的形状/位置做 lower，应用 default-resp-≈C 的 pos-to-shape-eq，再 re-lift
      go x y x≈y ._≈C_.pos-to-shape-eq {A} s p =
        cong lift
          (default-resp-≈C x≈y ._≈C_.pos-to-shape-eq {A = A} (lower s) (lower p))

      -- Corecursive descent: lower the lifted shape, unfold both sides, recurse
      -- 余递归下降：对提升后的形状做 lower，展开两侧，递归
      go x y x≈y ._≈C_.unfold-next-eq {A} s =
        go (Unfolding.unfold-next (out x) {A = proj₁ A} (lower s))
           (Unfolding.unfold-next (out y) {A = proj₁ A} (lower s))
           (_≈C_.unfold-next-eq x≈y {A = proj₁ A} (lower s))

  -- The default uniform embedding family is functorial at every layer
  -- 默认一致嵌入族在每一层上均函子性
  functorial-default : FunctorialEmbeddingFamilyForTower
  functorial-default = record
    { uniform        = default-unif
    ; embed′-resp-≈C = λ k → default-resp-≈C k
    }

  -- fams-default k: uniform from default-unif k; resp-≈C from
  -- default-strictEmbed-resp-≈C k (which reuses default-resp-≈C)
  -- fams-default k：uniform 来自 default-unif k；resp-≈C 来自
  -- default-strictEmbed-resp-≈C k（复用 default-resp-≈C）
  fams-default : ∀ k → EmbedFamily outer-rule (Tower.layer nTower k)
  fams-default k = record
    { uniform = default-unif k
    ; resp-≈C = λ {x} {y} x≈y → default-strictEmbed-resp-≈C k x≈y
    }

  -- The FinCat n tower enriched along the outer-preserving rule
  -- FinCat n 塔沿保外层规则的丰富塔实例
  enriched-default : EnrichedTower outer-rule nIdx
  enriched-default = record
    { tower = nTower
    ; fams  = fams-default
    }
