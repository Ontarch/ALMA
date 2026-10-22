------------------------------------------------------------------------
-- Inner-preserving strict embedding over an arbitrary strict layer
-- 任意严格层上的保内层严格嵌入
--
-- Provides the inner-preserving unfold functor F₀ ((A, s), u) = A, the
-- inner-preserving strict embedding strictEmbed-inner, the unconditional
-- propagation of EmbeddingData along it, and the inner rule. The
-- constructions are generic over any StrictLayer and independent of any
-- concrete tower; the FinCatN tower instance is instantiated in
-- FinCatNInnerObstruction
-- 提供保内层展开函子 F₀ ((A, s), u) = A、保内层严格嵌入
-- strictEmbed-inner、EmbeddingData 沿其无条件传播，以及内层规则。
-- 所有构造对任意 StrictLayer 泛型，且独立于具体塔；
-- FinCatN 塔实例在 FinCatNInnerObstruction 中实例化
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module SecondPass.FinCatNInnerSewing where

open import Agda.Primitive using (Level)
open import Agda.Builtin.Equality using (_≡_)
open import Level using (lift; lower)
open import Relation.Binary.PropositionalEquality.Core using (cong; subst)
open import Relation.Binary.PropositionalEquality.Properties using (module ≡-Reasoning)
open ≡-Reasoning
open import Data.Product.Base using (proj₁)

open import Categories.Category.Core using (Category)
open import Categories.Functor.Core using (Functor)

open import Cosmos.ContCategoryLemmas using (ShapeOf; PosOf; actSOf; actPOf)
open import Cosmos.ContCatEquiv using (ShapeCat)
open import SecondPass.Unfolding using (Unfolding)
open import SecondPass.Cosmos using (Cosmos; out)
open import SecondPass.CumulativeHierarchy using (EmbeddingData; ShapeCat-id-comm)
open import SecondPass.StrictLift
  using (StrictLayer; strictStep-suc; EmbeddingRule; strictEmbed-bridge; strictEmbed-compat)

-- Local helpers for the inner-direction compatibility proofs
-- 内层方向相容性证明的局部辅助
private
  module InnerStrict
    {o h e s p : Level} {L : StrictLayer o h e s p}
    {x : Cosmos (StrictLayer.C L) (StrictLayer.FC L)}
    (ed : EmbeddingData x) where

    C_L  = StrictLayer.C L
    FC_L = StrictLayer.FC L
    FC'  = StrictLayer.FC (strictStep-suc L)
    UXv  = out x
    module UX   = Unfolding UXv
    module SCat = Category (ShapeCat C_L FC_L)

    -- pos-to-shape compatibility at the lifted layer
    -- 提升层的 pos-to-shape 相容性
    pos-compat
      : ∀ {A B : SCat.Obj}
          {s : ShapeOf FC' A} {t : ShapeOf FC' B}
          (g : A SCat.⇒ B) (p : actSOf FC' {A = A} {B = B} g s ≡ t)
          (p₁ : PosOf FC' {A = B} (actSOf FC' {A = A} {B = B} g s))
        → actSOf FC_L (EmbeddingData.retract ed (lower t))
            (UX.pos-to-shape (lower t)
               (lower (subst (PosOf FC' {A = B}) p p₁)))
          ≡ actSOf FC_L (proj₁ g)
              (actSOf FC_L (EmbeddingData.retract ed (lower s))
                 (UX.pos-to-shape (lower s)
                    (actPOf FC_L (proj₁ g) (lower s) (lower p₁))))
    pos-compat {A} {B} {s} {t} g p p₁ = begin
        actSOf FC_L (EmbeddingData.retract ed (lower t))
          (UX.pos-to-shape (lower t)
             (lower (subst (PosOf FC' {A = B}) p p₁)))
          ≡⟨ cong (actSOf FC_L (EmbeddingData.retract ed (lower t)))
                  (cong (UX.pos-to-shape (lower t))
                        (strictEmbed-bridge L x ed g p p₁)) ⟩
        actSOf FC_L (EmbeddingData.retract ed (lower t))
          (UX.pos-to-shape (lower t)
             (subst (PosOf FC_L) (cong lower p) (lower p₁)))
          ≡⟨ strictEmbed-compat L x ed (proj₁ g) (cong lower p) (lower p₁) ⟩
        actSOf FC_L (proj₁ g)
          (actSOf FC_L (EmbeddingData.retract ed (lower s))
             (UX.pos-to-shape (lower s)
                (actPOf FC_L (proj₁ g) (lower s) (lower p₁))))
      ∎

-- The inner-preserving unfold functor: F₀ = π' (first-component projection)
-- 保内层展开函子：F₀ = π'（第一分量投影）
strictEmbed-unfoldFunctor-inner
  : ∀ {o h e s p}
  → (L : StrictLayer o h e s p)
  → Functor (ShapeCat (StrictLayer.C (strictStep-suc L))
                      (StrictLayer.FC (strictStep-suc L)))
            (ShapeCat (StrictLayer.C L) (StrictLayer.FC L))
strictEmbed-unfoldFunctor-inner L = record
  { F₀           = proj₁
  ; F₁           = proj₁
  ; identity     = Category.Equiv.refl (StrictLayer.C L)
  ; homomorphism = λ {X} {Y} {Z} {f} {g} →
                     Category.Equiv.refl (StrictLayer.C L)
  ; F-resp-≈     = λ ff≈gg → ff≈gg
  }

-- Inner-preserving strict embedding
-- 保内层严格嵌入
strictEmbed-inner
  : ∀ {o h e s p}
  → (L : StrictLayer o h e s p)
  → (x : Cosmos (StrictLayer.C L) (StrictLayer.FC L))
  → EmbeddingData x
  → Cosmos (StrictLayer.C (strictStep-suc L))
           (StrictLayer.FC (strictStep-suc L))
strictEmbed-inner L x ed .out = record
  { unfoldFunctor   = strictEmbed-unfoldFunctor-inner L
  ; unfold-next     = λ { {A} u →
      strictEmbed-inner L
        (UX.unfold-next {A = proj₁ A} (lower u))
        (EmbeddingData.next ed {A = proj₁ A} (lower u)) }
  ; pos-to-shape    = λ {A} s p →
      lift (actSOf FC_L (EmbeddingData.retract ed (lower s))
                   (UX.pos-to-shape (lower s) (lower p)))
  ; pos-actS-compat = λ {A} {B} {s} {t} f p p₁ →
      cong lift (InnerStrict.pos-compat {L = L} {x = x} ed f p p₁)
  }
  where
    FC_L = StrictLayer.FC L
    UXv  = out x
    module UX = Unfolding UXv

-- EmbeddingData propagates along the inner strict embedding
-- EmbeddingData 沿内层严格嵌入传播
module _ {o h e s p : Level} (L : StrictLayer o h e s p) where
  private
    C_L  = StrictLayer.C L
    FC_L = StrictLayer.FC L
    module C' = Category (ShapeCat C_L FC_L)

  -- Since F₀ (A, s) = A definitionally, retract = C'.id is well-typed,
  -- and retract-natural reduces to the unit laws of C'
  -- 因 F₀ (A, s) = A 定义性成立，retract = C'.id 类型正确，
  -- retract-natural 归约为 C' 的单位律
  strictEmbed-inner-self-embedding
    : (x : Cosmos C_L FC_L)
    → (ed : EmbeddingData x)
    → EmbeddingData (strictEmbed-inner L x ed)
  strictEmbed-inner-self-embedding x ed .EmbeddingData.retract =
    λ _ → C'.id
  strictEmbed-inner-self-embedding x ed
    .EmbeddingData.retract-natural {A} {B} {s} {t} f eq =
    ShapeCat-id-comm {C = C_L} {FC = FC_L} A B f
  strictEmbed-inner-self-embedding x ed
    .EmbeddingData.next {A} s =
    strictEmbed-inner-self-embedding
      (Unfolding.unfold-next (out x) {A = proj₁ A} (lower s))
      (EmbeddingData.next ed {A = proj₁ A} (lower s))

-- The inner-preserving rule
-- 保内层规则
inner-rule : EmbeddingRule
inner-rule .EmbeddingRule.Embed = strictEmbed-inner
