------------------------------------------------------------------------
-- MorphLift: lifting morphisms to unfolded cosmoi
--
-- A coinductive structure assigning to each hom and shape a morphism
-- between the corresponding unfolded cosmoi, together with compatibility
-- with identity and composition.
--
-- MorphLift：将态射提升到展开宇宙
--
-- 余归纳结构，为每个 hom 与 shape 指派对应展开宇宙之间的态射，
-- 并要求其与恒等和复合相容。
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module Wellspring.Properties.MorphLift where

open import Wellspring.Properties.Cong public

-- A lifting of homomorphisms to the unfolded cosmoi, compatible with
-- id and comp
--
-- 把同态提升到展开宇宙，并与 id 和 comp 相容
record MorphLift {ℓ} (C : Cosmos ℓ) : Set (lsuc (lsuc ℓ)) where
  coinductive
  private
    module C = Cosmos C
  field
    morphLift  : {A B : C.Obj} (f : C.Hom A B) (s : C.Shape A) → C.unfold s ⇒ℱ C.unfold (C.actS f s)
    morphLift-id : ∀ {A : C.Obj} (s : C.Shape A)
                 → morphLift C.idHom s
                 ≃⇒ℱ subst (λ X → C.unfold s ⇒ℱ C.unfold X)
                           (sym (C.actS-id s))
                           id⇒ℱ
    morphLift-comp : ∀ {A B D : C.Obj} (f : C.Hom A B) (g : C.Hom B D) (s : C.Shape A)
                   → morphLift (C.comp f g) s
                   ≃⇒ℱ subst (λ X → C.unfold s ⇒ℱ C.unfold X)
                             (sym (C.actS-comp f g s))
                             (morphLift g (C.actS f s) ∘⇒ℱ morphLift f s)
open MorphLift public

-- The unit cosmos carries a canonical MorphLift
--
-- 单位宇宙带有典范的 MorphLift
UnitCosmosMorphLift : ∀ {ℓ} → MorphLift (UnitCosmos {ℓ})
UnitCosmosMorphLift .morphLift _ _ = id⇒ℱ
UnitCosmosMorphLift .morphLift-id _ = refl-≃⇒ℱ
UnitCosmosMorphLift .morphLift-comp _ _ _ = sym-≃⇒ℱ (id-l-≃⇒ℱ id⇒ℱ)
