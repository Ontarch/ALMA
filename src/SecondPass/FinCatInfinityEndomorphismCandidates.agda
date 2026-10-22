------------------------------------------------------------------------
-- Candidate endomorphisms on towerColimit
--
-- Experimental. C-1 and C-2 place id⇒ℱX at the head; C-3 and C-4
-- recurse into the subtower without mediation. Whether any of these is
-- non-trivial under _≈⇒ℱX_ is open.
--
-- towerColimit 上的候选自同态
--
-- 实验性内容。C-1 与 C-2 在头部使用恒等态射或其复合；C-3 与 C-4
-- 不经过中介直接递归进入 subtower。其中是否有在 _≈⇒ℱX_ 下非平凡者，
-- 尚无定论。
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module SecondPass.FinCatInfinityEndomorphismCandidates where

open import Agda.Builtin.Equality using (refl)
open import Level using (Lift; lift)
open import Data.Nat using (ℕ)
open import Data.Unit.Polymorphic.Base using (⊤; tt)

open import Categories.Functor using (id)

open import SecondPass.Cosmos using (Cosmos; out)
open import SecondPass.MorphismObject using (MorphismObject)
open import SecondPass.MorphismMorphism using (MorphismMorphism)
open import SecondPass.FinCatNWitness using (module FinCatN)
open import SecondPass.FinCatInfinity using (FinCat∞; TrivialFC∞; n-at)
open import SecondPass.FinCatInfinityColimit using
  (CompatibleTower; subtower; towerColimit; _⇒ℱX[_]_; ⇒ℱXLayer[_]; comp⇒ℱX; id⇒ℱX)
open import SecondPass.FinCatInfinityColimitUniversal using (comp⇒ℱX-id-left)

open _⇒ℱX[_]_
open ⇒ℱXLayer[_]
open CompatibleTower

-- Candidate C-1: identity at the head
--
-- 候选 C-1：头部放置恒等态射
C-1 : ∀ (tower : CompatibleTower)
  → towerColimit tower ⇒ℱX[ id ] towerColimit tower
C-1 tower .out .shapeTrans _ = lift tt
C-1 tower .out .morphismObj .MorphismObject.onPos _ = lift tt
C-1 tower .out .morphismObj .MorphismObject.pts-compat _ = refl
C-1 tower .out .morphismMor .MorphismMorphism.onActP _ _ _ = refl
C-1 tower .out .onunfold-next {A = k} (lift tt) =
  id⇒ℱX {F = towerColimit (subtower tower k)}

-- Candidate C-2: composite of two identities at the head
--
-- 候选 C-2：头部放置两个恒等态射的复合
C-2 : ∀ (tower : CompatibleTower)
  → towerColimit tower ⇒ℱX[ id ] towerColimit tower
C-2 tower .out .shapeTrans _ = lift tt
C-2 tower .out .morphismObj .MorphismObject.onPos _ = lift tt
C-2 tower .out .morphismObj .MorphismObject.pts-compat _ = refl
C-2 tower .out .morphismMor .MorphismMorphism.onActP _ _ _ = refl
C-2 tower .out .onunfold-next {A = k} (lift tt) =
  comp⇒ℱX-id-left
    (id⇒ℱX {F = towerColimit (subtower tower k)})
    (id⇒ℱX {F = towerColimit (subtower tower k)})

-- Candidate C-3: recurse into the subtower without mediation
--
-- 候选 C-3：不经过中介直接递归进入 subtower
C-3 : ∀ (tower : CompatibleTower)
  → towerColimit tower ⇒ℱX[ id ] towerColimit tower
C-3 tower .out .shapeTrans _ = lift tt
C-3 tower .out .morphismObj .MorphismObject.onPos _ = lift tt
C-3 tower .out .morphismObj .MorphismObject.pts-compat _ = refl
C-3 tower .out .morphismMor .MorphismMorphism.onActP _ _ _ = refl
C-3 tower .out .onunfold-next {A = k} (lift tt) =
  C-3 (subtower tower k)

-- Candidate C-4: recurse twice into nested subtowers
--
-- 候选 C-4：两层递归进入嵌套 subtower
C-4 : ∀ (tower : CompatibleTower)
  → towerColimit tower ⇒ℱX[ id ] towerColimit tower
C-4 tower .out .shapeTrans _ = lift tt
C-4 tower .out .morphismObj .MorphismObject.onPos _ = lift tt
C-4 tower .out .morphismObj .MorphismObject.pts-compat _ = refl
C-4 tower .out .morphismMor .MorphismMorphism.onActP _ _ _ = refl
C-4 tower .out .onunfold-next {A = k} (lift tt) .out .shapeTrans _ = lift tt
C-4 tower .out .onunfold-next {A = k} (lift tt) .out .morphismObj .MorphismObject.onPos _ = lift tt
C-4 tower .out .onunfold-next {A = k} (lift tt) .out .morphismObj .MorphismObject.pts-compat _ = refl
C-4 tower .out .onunfold-next {A = k} (lift tt) .out .morphismMor .MorphismMorphism.onActP _ _ _ = refl
C-4 tower .out .onunfold-next {A = k} (lift tt) .out .onunfold-next {A = j} (lift tt) =
  C-4 (subtower (subtower tower k) j)
