------------------------------------------------------------------------
-- ALMA — infinite, unbounded, self-referential dynamic Cosmos
--
-- Built with type theory, category theory, containers, and coalgebraic unfolding
-- Cosmos is the terminal coalgebra of a polynomial functor internalized in type theory
--
-- ALMA —— 无穷、无界、自指的动态宇宙
--
-- 基于类型论、范畴论、容器与余代数展开构建；
-- Cosmos 是内化于类型论中的多项式函子的终余代数
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module SecondPass.Cosmos where

open import Agda.Primitive using (Level; _⊔_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Sigma using (_,_)
open import Relation.Binary.PropositionalEquality.Core using (sym; trans; cong; subst)
open import Relation.Binary.PropositionalEquality.Properties using (setoid)
open import Function.Bundles using (Func)
open import Data.Unit.Polymorphic.Base using (⊤; tt)
open import Data.Product.Base using (proj₁; proj₂)

open import Categories.Category.Core using (Category)
open import Categories.Category.Instance.Setoids using (Setoids)
open import Categories.Category.Instance.Sets using (Sets)
open import Categories.Category.Instance.One using (One)
open import Categories.Functor.Core using (Functor)
open import Categories.Functor using (id; _∘F_)

open import Cosmos.ContCategory using (≈sr-refl; ContCat)
open import Cosmos.ContCategoryLemmas using (ShapeOf; PosOf; actSOf; actPOf)
open import Cosmos.ContCatEquiv using (ShapeCat)
open import SecondPass.Unfolding using (Unfolding; module UnfoldingSetoid)
open import SecondPass.MorphismObject using (MorphismObject; idMorphismObject; compMorphismObject)
open import SecondPass.MorphismMorphism
  using (MorphismMorphism; idMorphismMorphism; actP-from-S; compMorphismMorphism)

-- Core Definitions: Cosmos as Terminal Coalgebra
-- One-layer unfolding of Cosmos: a container-shaped functorial structure
-- over a parameter X
-- Cosmos: the terminal coalgebra of the polynomial functor Unfolding
-- Defined coinductively: out : Cosmos → Unfolding (Cosmos)
--
-- 核心定义：Cosmos 作为终余代数
-- Cosmos 的单层展开：参数 X 上的容器形状函子结构
-- Cosmos：多项式函子 Unfolding 的终余代数
-- 以余归纳定义：out : Cosmos → Unfolding (Cosmos)
record Cosmos {o h e s p : Level}
              (C : Category o h e)
              (FC : Functor C (ContCat s p))
              : Set (o ⊔ h ⊔ e ⊔ s ⊔ p) where
  coinductive
  field
    out : Unfolding FC (Cosmos C FC)
open Cosmos public

-- Universe Morphisms: Coalgebra Homomorphisms
-- Generalized homomorphism _⇒ℱ[_]_ parameterized by a shape functor S
-- S : Functor (ShapeCat C FC) (ShapeCat C FC) controls how shape indices
-- are transported from source to target
--
-- 宇宙态射：余代数同态
-- 广义同态 _⇒ℱ[_]_ 以形状函子 S 为参数
-- S 控制形状索引从源到目标的传输
mutual
  record _⇒ℱ[_]_ {o h e s p : Level} {C : Category o h e} {FC : Functor C (ContCat s p)}
                  (F : Cosmos C FC)
                  (S : Functor (ShapeCat C FC) (ShapeCat C FC))
                  (G : Cosmos C FC)
                  : Set (o ⊔ h ⊔ s ⊔ p) where
    coinductive
    field
      out : ⇒ℱLayer[ S ] F G

  record ⇒ℱLayer[_] {o h e s p : Level} {C : Category o h e} {FC : Functor C (ContCat s p)}
                    (S : Functor (ShapeCat C FC) (ShapeCat C FC))
                    (F G : Cosmos C FC)
                    : Set (o ⊔ h ⊔ s ⊔ p) where
    inductive
    private
      module S = Functor S
      UF = out F
      UG = out G
    field

      -- Shape translation: maps positions of source to shapes of target
      --
      -- 形状翻译：将源的位置映射为目标宇宙的形状
      shapeTrans  : ∀ {A} {s : ShapeOf FC A}
                  → PosOf FC s
                  → ShapeOf FC (Functor.₀ (Unfolding.unfoldFunctor UG) (S.₀ (A , s)))

      -- Morphism object compatibility
      --
      -- 态射对象相容性
      morphismObj : MorphismObject UF UG S shapeTrans

      -- Morphism morphism compatibility
      --
      -- 态射间态射相容性
      morphismMor : MorphismMorphism UF UG S shapeTrans morphismObj

      -- Recursive universe morphism on next seeds
      --
      -- 下一层种子上的递归宇宙态射
      onunfold-next : ∀ {A} (s : ShapeOf FC A)
                    → Unfolding.unfold-next UF s ⇒ℱ[ S ]
                      Unfolding.unfold-next UG (proj₂ (S.₀ (A , s)))

open _⇒ℱ[_]_ public
open ⇒ℱLayer[_] public

-- S = id specialization
--
-- S = id 特化
_⇒ℱ_ : ∀ {o h e s p} {C : Category o h e} {FC : Functor C (ContCat s p)}
     → Cosmos C FC → Cosmos C FC → Set (o ⊔ h ⊔ s ⊔ p)
_⇒ℱ_ {C = C} {FC = FC} F G = F ⇒ℱ[ id ] G

-- Identity homomorphism exists only at S = id:
-- onunfold-next target = unfold-next UF (proj₂ (id.₀ (A,s))) = unfold-next UF s,
-- so id⇒ℱ applies recursively. For S ≠ id source and target differ, no canonical map
--
-- 恒等同态仅在 S = id 存在：
-- onunfold-next 目标 = unfold-next UF s，与源相同，可递归应用 id⇒ℱ
id⇒ℱ : ∀ {o h e s p} {C : Category o h e} {FC : Functor C (ContCat s p)}
     → {F : Cosmos C FC} → F ⇒ℱ F
id⇒ℱ {F = F} .out = record
  { shapeTrans    = λ p → Unfolding.pos-to-shape UF _ p
  ; morphismObj   = idMorphismObject UF
  ; morphismMor   = idMorphismMorphism UF
  ; onunfold-next = λ _ → id⇒ℱ
  }
  where UF = out F

-- Generalized composition: S₂ ∘F S₁, morphismMor via compMorphismMorphism
-- Non-mixfix name because composite S is determined by argument types
--
-- 广义复合：S 按 S₂ ∘F S₁ 封闭，morphismMor 由 compMorphismMorphism 自动导出
-- 使用非 mixfix 名称，因为复合 S 由参数类型决定
comp⇒ℱ : ∀ {o h e s p} {C : Category o h e} {FC : Functor C (ContCat s p)}
       {S₁ S₂ : Functor (ShapeCat C FC) (ShapeCat C FC)}
       {F G H : Cosmos C FC}
       → G ⇒ℱ[ S₂ ] H → F ⇒ℱ[ S₁ ] G → F ⇒ℱ[ S₂ ∘F S₁ ] H
comp⇒ℱ {S₁ = S₁} {S₂ = S₂} {F = F} {G = G} {H = H} g f .out = record
  { shapeTrans    = λ p → shapeTrans (g .out) (onPos moF p)
  ; morphismObj   = compMorphismObject UF UG UH S₁ S₂ stF stG moF moG
  ; morphismMor   = compMorphismMorphism UF UG UH S₁ S₂ stF stG mmF mmG
  ; onunfold-next = λ {A} s′ →
      let A′ = proj₁ (S₁.₀ (A , s′))
          s″ = proj₂ (S₁.₀ (A , s′))
      in  comp⇒ℱ (onunfold-next (g .out) {A = A′} s″)
                 (onunfold-next (f .out) s′)
  }
  where
    open MorphismObject
    module S₁ = Functor S₁
    UF  = out F
    UG  = out G
    UH  = out H
    stF = shapeTrans (f .out)
    stG = shapeTrans (g .out)
    moF = morphismObj (f .out)
    moG = morphismObj (g .out)
    mmF = morphismMor (f .out)
    mmG = morphismMor (g .out)

-- S = id specialization of composition
--
-- S = id 特化的复合
_∘⇒ℱ_ : ∀ {o h e s p} {C : Category o h e} {FC : Functor C (ContCat s p)}
       {F G H : Cosmos C FC}
       → G ⇒ℱ H → F ⇒ℱ G → F ⇒ℱ H
_∘⇒ℱ_ {C = C} {FC = FC} {F = F} {G = G} {H = H} g f .out = record
  { shapeTrans    = λ p → shapeTrans (g .out) (onPos moF p)
  ; morphismObj   = record
      { onPos      = λ p → onPos moG (onPos moF p)
      ; pts-compat = λ p → pts-compat moG (onPos moF p)
      }
  ; morphismMor   = record { onActP = coh }
  ; onunfold-next = λ s → (onunfold-next (g .out) s) ∘⇒ℱ (onunfold-next (f .out) s)
  }
  where
    open MorphismObject
    open MorphismMorphism
    moF = morphismObj (f .out)
    moG = morphismObj (g .out)
    mmF = morphismMor (f .out)
    mmG = morphismMor (g .out)
    coh : ∀ {A B} (f′ : Category._⇒_ C A B) {s : ShapeOf FC A} {t : ShapeOf FC B}
        → (p : actSOf FC f′ s ≡ t) (q : PosOf FC t)
        → onPos moG (onPos moF (actPOf FC f′ s (subst (PosOf FC) (sym p) q)))
          ≡ actP-from-S FC FC id f′ p (onPos moG (onPos moF q))
    coh f′ p q = trans (cong (onPos moG) (onActP mmF f′ p q))
                       (onActP mmG f′ p (onPos moF q))

-- The terminal category with one object and one morphism
--
-- 只有一个对象和一个态射的终范畴
UnitCat : ∀ {ℓ} → Category ℓ ℓ ℓ
UnitCat {ℓ} = One

-- The constant functor picking the unit container (⊤, λ _ → ⊤)
--
-- 选取单位容器 (⊤, λ _ → ⊤) 的常值函子
UnitContainerFunctor : ∀ {ℓ} → Functor (UnitCat {ℓ}) (ContCat ℓ ℓ)
UnitContainerFunctor = record
  { F₀ = λ _ → record { Shape = ⊤; Position = λ _ → ⊤ }
  ; F₁ = λ _ → record { shape = λ _ → tt; position = λ _ → tt }
  ; identity = ≈sr-refl
  ; homomorphism = ≈sr-refl
  ; F-resp-≈ = λ _ → ≈sr-refl
  }

-- The trivial Cosmos: a single point unfolding into itself forever
--
-- 平凡宇宙：一个永远展开为自身的单点
UnitCosmos : ∀ {ℓ} → Cosmos (UnitCat {ℓ}) UnitContainerFunctor
UnitCosmos .out = record
  { unfoldFunctor = record
    { F₀ = proj₁
    ; F₁ = proj₁
    ; identity = Category.Equiv.refl UnitCat
    ; homomorphism = Category.Equiv.refl UnitCat
    ; F-resp-≈ = λ p → p
    }
  ; unfold-next = λ _ → UnitCosmos
  ; pos-to-shape = λ _ _ → tt
  ; pos-actS-compat = λ _ _ _ → refl
  }

-- Unfolding Functor: Sets → Setoids
--
-- Unfolding 函子：Sets → Setoids
module CosmosFFunctor {o h e s p : Level}
                      {C : Category o h e}
                      {FC : Functor C (ContCat s p)} where
  private

    -- Instantiate the unfolding setoid module for the current container functor
    --
    -- 为当前容器函子实例化展开集合模块
    module US = UnfoldingSetoid
      {o = o} {h = h} {e = e} {s = s} {p = p} {C = C} {F = FC}

  -- The Unfolding functor: Sets u → Setoids
  --
  -- Unfolding 函子：Sets u → Setoids
  toStdFunc : {u : Level} {X Y : Set u} → (X → Y) → Func (setoid X) (setoid Y)
  toStdFunc f = record { to = f ; cong = cong f }

  cosmosFFunctor : (u : Level)
    → Functor (Sets u)
              (Setoids (o ⊔ h ⊔ e ⊔ s ⊔ p ⊔ u)
                       (o ⊔ s ⊔ p ⊔ u))
  cosmosFFunctor u = record
    { F₀           = λ X → US.unfoldingSetoid (setoid X)
    ; F₁           = λ f → US.mapUnfolding-resp (toStdFunc f)
    ; identity     = λ {X} → US.≈U-refl {X = setoid X}
    ; homomorphism = λ {X Y Z} {f g} → US.≈U-refl {X = setoid Z}
    ; F-resp-≈ = λ {X Y} {f g} f≈g {c} →
        US.mapUnfolding-resp-≈ X Y f g (λ {x} → f≈g x) US.≈U-refl
    }
