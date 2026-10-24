------------------------------------------------------------------------
-- CumulativeHierarchyInner — the inner-preserving embedding direction
--
-- Provides the inner-preserving direction of the unfold functor,
-- F₀ ((A, s₀), s₁) = (A, s₀), i.e. the fibration projection π' of the
-- Elements construction. Since F₀ is definitionally the first-component
-- projection, retract reduces to the identity, so EmbeddingData is
-- unconditionally constructible at any shape type — in contrast to the
-- outer direction of CumulativeHierarchy, whose obstruction demands
-- s₁ ≡ s₀
--
-- 累积层级内层 —— 保内层方向的嵌入
--
-- 给出展开函子的保内层方向 F₀ ((A, s₀), s₁) = (A, s₀)，即 Elements
-- 构造的纤维化投影 π'。因 F₀ 定义性等于第一分量投影，retract 退化为
-- 恒等，EmbeddingData 对任意形状类型无条件成立；这与 CumulativeHierarchy
-- 中外层方向的障碍（要求 s₁ ≡ s₀）形成对比
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module SecondPass.CumulativeHierarchyInner where

open import Agda.Primitive using (Level)
open import Agda.Builtin.Sigma using (_,_)
open import Data.Product.Base using (proj₁)

open import Categories.Category.Core using (Category)
open import Categories.Functor.Core using (Functor)

open import Cosmos.ContCategory using (ContCat)
open import Cosmos.ContCategoryLemmas using (actSOf)
open import Cosmos.ContCatEquiv using (ShapeCat)
open import SecondPass.Unfolding using (Unfolding)
open import SecondPass.Cosmos using (Cosmos; out)
open import SecondPass.CumulativeHierarchy
  using (FC∘π; EmbeddingData; embed-compat; ShapeCat-id-comm)

-- The inner-preserving unfold functor: F₀ is the first-component
-- projection π' of the Elements construction
-- 保内层展开函子：F₀ 为 Elements 构造的第一分量投影 π'
embed-unfoldFunctor-inner
  : ∀ {o h e s p} {C : Category o h e}
  → (FC : Functor C (ContCat s p))
  → Functor (ShapeCat (ShapeCat C FC) (FC∘π FC)) (ShapeCat C FC)
embed-unfoldFunctor-inner {C = C} FC = record
  { F₀           = proj₁
  ; F₁           = proj₁
  ; identity     = λ {A} → Equiv.refl {proj₁ (proj₁ A)} {proj₁ (proj₁ A)}
  ; homomorphism = λ {X} {Y} {Z} {f} {g} →
                     Equiv.refl {proj₁ (proj₁ X)} {proj₁ (proj₁ Z)}
                                 {proj₁ (proj₁ g) ∘ proj₁ (proj₁ f)}
  ; F-resp-≈     = λ f≈g → f≈g
  }
  where open Category C

-- Inner-preserving embed, with embed-unfoldFunctor-inner as the unfold
-- functor. The compatibility of pos-to-shape depends only on
-- retract-natural and the functoriality of FC, hence coincides with
-- that of CumulativeHierarchy.embed
-- 保内层嵌入，以 embed-unfoldFunctor-inner 为展开函子
-- pos-to-shape 的相容性仅依赖 retract-natural 与 FC 的函子性，
-- 故与 CumulativeHierarchy.embed 相同
embed-inner
  : ∀ {o h e s p} {C : Category o h e} {FC : Functor C (ContCat s p)}
  → (x : Cosmos C FC) → EmbeddingData x
  → Cosmos (ShapeCat C FC) (FC∘π FC)
embed-inner {C = C} {FC = FC} x ed .out = record
  { unfoldFunctor   = embed-unfoldFunctor-inner FC
  ; unfold-next     = λ { {A , _} p → embed-inner (UX.unfold-next p) (next p) }
  ; pos-to-shape    = λ { {A , _} p q → actSOf FC (retract p) (UX.pos-to-shape p q) }
  ; pos-actS-compat = λ { {A , _} {B , _} {s} {t} (f , _) eq p →
                        embed-compat ed f eq p }
  }
  where
    open EmbeddingData ed
    UX = out x
    module UX = Unfolding UX

-- The inner embed is self-iterable
-- 内层嵌入自可迭代
module _ {o h e s p : Level}
         {C : Category o h e}
         {FC : Functor C (ContCat s p)} where

  private
    module SCat = Category (ShapeCat C FC)

  -- Since F₀ (A', s) = A' definitionally, retract = id is well-typed and
  -- retract-natural is discharged by the unit laws of SCat
  -- 因 F₀ (A', s) = A' 定义性成立，retract = id 类型正确，
  -- retract-natural 由 SCat 的单位律给出
  inner-self-embedding
    : (x : Cosmos C FC) (ed : EmbeddingData x)
    → EmbeddingData (embed-inner x ed)
  inner-self-embedding x ed .EmbeddingData.retract =
    λ _ → SCat.id
  inner-self-embedding x ed .EmbeddingData.retract-natural
    {A} {B} {s} {t} f' eq' =
    ShapeCat-id-comm {C = C} {FC = FC} A B f'
  inner-self-embedding x ed .EmbeddingData.next =
    λ s → inner-self-embedding (Unfolding.unfold-next (out x) s)
                               (EmbeddingData.next ed s)
