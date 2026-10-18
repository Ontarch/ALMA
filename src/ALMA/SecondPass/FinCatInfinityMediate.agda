------------------------------------------------------------------------
-- The mediating morphism and the triangle equation
--
-- mediate is defined coinductively from a cocone g. Its onunfold-next
-- recurses into the sub-tower. mediate-triangle states that mediate
-- composed with the colimit cocone is the cocone g.
--
-- 中介态射与三角等式
--
-- mediate 由余锥 g 余归纳地定义，其 onunfold-next 递归进入子塔。
-- mediate-triangle 陈述 mediate 与余极限余锥的复合等于余锥 g。
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module ALMA.SecondPass.FinCatInfinityMediate where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Level using (Lift; lift)
open import Data.Nat using (ℕ)
open import Data.Fin.Base using (Fin; toℕ)
open import Data.Unit.Polymorphic.Base using (⊤; tt)
open import Relation.Binary.PropositionalEquality.Core using (cong; sym; trans; subst)

open import Categories.Category.Core using (Category)
open import Categories.Functor using (id)

open import ALMA.Cosmos.ContCategoryLemmas using (ShapeOf; PosOf)
open import ALMA.SecondPass.Unfolding using (Unfolding)
open Unfolding using (unfold-next)
open import ALMA.SecondPass.Cosmos using (Cosmos; out)
open import ALMA.SecondPass.MorphismObject using (MorphismObject)
open import ALMA.SecondPass.MorphismMorphism using (MorphismMorphism)
open import ALMA.SecondPass.FinCatNWitness using (module FinCatN)
open import ALMA.SecondPass.FinCatInfinity using (FinCat∞; TrivialFC∞; n-at)
open import ALMA.SecondPass.FinCatInfinityColimit using
  (CompatibleTower; subtower; towerColimit; _⇒ℱX[_]_; ⇒ℱXLayer[_]; comp⇒ℱX
  ; id⇒ℱX; module TowerShapeFunctors)
open import ALMA.SecondPass.FinCatInfinityColimitUniversal using
  (colimitCocone; _≈⇒ℱX_; ≈⇒ℱXLayer; ≈⇒ℱX-refl; ≈⇒ℱX-sym; ≈⇒ℱX-trans
  ; ≡-to-≈⇒ℱX; comp⇒ℱX-cong-≈⇒ℱX)
open import ALMA.SecondPass.FinCatInfinitySubstitution
open import ALMA.SecondPass.FinCatInfinityProjectionUnfold using
  (defaultFin-src-eq; colimitCocone-onunfold-next)
open import ALMA.SecondPass.FinCatInfinitySubCocone

open _⇒ℱX[_]_
open ⇒ℱXLayer[_]
open _≈⇒ℱX_
open ≈⇒ℱXLayer
open CompatibleTower
open MorphismObject
open MorphismMorphism

-- Mediating morphism from the colimit to Y, given a cocone g
--
-- Coinductively defined; its onunfold-next recurses into the sub-tower.
-- The triangle equation below concerns this morphism.
--
-- 给定余锥 g，从余极限到 Y 的中介态射
--
-- 余归纳定义；其 onunfold-next 递归进入子塔。
-- 下方的三角等式关于该态射。
mediate : ∀ (tower : CompatibleTower) (Y : Cosmos FinCat∞ TrivialFC∞)
  → (g : ∀ m → CompatibleTower.seq tower m
        ⇒ℱX[ TowerShapeFunctors.S-proj m ] Y)
  → towerColimit tower ⇒ℱX[ id ] Y
mediate tower Y g .out .shapeTrans _ = lift tt
mediate tower Y g .out .morphismObj .MorphismObject.onPos _ = lift tt
mediate tower Y g .out .morphismObj .MorphismObject.pts-compat _ = refl
mediate tower Y g .out .morphismMor .MorphismMorphism.onActP _ _ _ = refl
mediate tower Y g .out .onunfold-next {A = k} (lift tt) =
  mediate (subtower tower k)
          (unfold-next (out Y) {A = k} (lift tt))
          (sub-cocone tower Y g k)

-- shapeTrans component of the triangle equation
--
-- 三角等式的 shapeTrans 分量
mt-go-shapeTrans : (tower : CompatibleTower) (Y : Cosmos FinCat∞ TrivialFC∞)
  (g : ∀ m → CompatibleTower.seq tower m
       ⇒ℱX[ TowerShapeFunctors.S-proj m ] Y)
  (m : ℕ)
  {A : Category.Obj (FinCatN.FinCatN m)}
  {s : ShapeOf (FinCatN.TrivialFCN m) A}
  (p : PosOf (FinCatN.TrivialFCN m) {A = A} s)
  → (comp⇒ℱX (mediate tower Y g) (colimitCocone tower m))
      .out .shapeTrans {A = A} {s = s} p
    ≡ (g m).out .shapeTrans {A = A} {s = s} p
mt-go-shapeTrans _ _ _ _ _ = ≡-Lift-⊤ _ _

-- onPos component of the triangle equation
--
-- 三角等式的 onPos 分量
mt-go-onPos : (tower : CompatibleTower) (Y : Cosmos FinCat∞ TrivialFC∞)
  (g : ∀ m → CompatibleTower.seq tower m
       ⇒ℱX[ TowerShapeFunctors.S-proj m ] Y)
  (m : ℕ)
  {A : Category.Obj (FinCatN.FinCatN m)}
  {s : ShapeOf (FinCatN.TrivialFCN m) A}
  (p : PosOf (FinCatN.TrivialFCN m) {A = A} s)
  → MorphismObject.onPos
      ((comp⇒ℱX (mediate tower Y g) (colimitCocone tower m)).out .morphismObj)
      {A = A} p
    ≡ MorphismObject.onPos
        ((g m).out .morphismObj) {A = A} p
mt-go-onPos _ _ _ _ _ = ≡-Lift-⊤ _ _

-- Unfolding of the composite via onunfold-next of mediate and cocone
--
-- 复合的展开通过 mediate 与余锥的 onunfold-next 表达
mt-go-step1 : (tower : CompatibleTower) (Y : Cosmos FinCat∞ TrivialFC∞)
  (g : ∀ m → CompatibleTower.seq tower m
       ⇒ℱX[ TowerShapeFunctors.S-proj m ] Y)
  (m : ℕ) (A : Fin (n-at m))
  → comp⇒ℱX (mediate tower Y g) (colimitCocone tower m)
      .out .onunfold-next {A = A} (lift tt)
    ≡ comp⇒ℱX (mediate tower Y g .out .onunfold-next {A = toℕ A} (lift tt))
              (colimitCocone tower m .out .onunfold-next {A = A} (lift tt))
mt-go-step1 _ _ _ _ _ = refl

-- Rewriting the two factors by their unfold-next descriptions
--
-- 用展开描述重写两个因子
mt-go-step3 : (tower : CompatibleTower) (Y : Cosmos FinCat∞ TrivialFC∞)
  (g : ∀ m → CompatibleTower.seq tower m
       ⇒ℱX[ TowerShapeFunctors.S-proj m ] Y)
  (m : ℕ) (A : Fin (n-at m))
  → comp⇒ℱX (mediate tower Y g .out .onunfold-next {A = toℕ A} (lift tt))
            (colimitCocone tower m .out .onunfold-next {A = A} (lift tt))
    ≈⇒ℱX
    comp⇒ℱX (mediate (subtower tower (toℕ A))
                     (unfold-next (out Y) {A = toℕ A} (lift tt))
                     (sub-cocone tower Y g (toℕ A)))
            (subst-src-FinCatN (sym (defaultFin-src-eq tower A))
               (colimitCocone (subtower tower (toℕ A)) m))
mt-go-step3 tower Y g m A =
  comp⇒ℱX-cong-≈⇒ℱX
    {S₁ = TowerShapeFunctors.S-proj m}
    {S₂ = id}
    {f  = colimitCocone tower m .out .onunfold-next {A = A} (lift tt)}
    {f′ = subst-src-FinCatN (sym (defaultFin-src-eq tower A))
            (colimitCocone (subtower tower (toℕ A)) m)}
    {g  = mediate tower Y g .out .onunfold-next {A = toℕ A} (lift tt)}
    {g′ = mediate (subtower tower (toℕ A))
                  (unfold-next (out Y) {A = toℕ A} (lift tt))
                  (sub-cocone tower Y g (toℕ A))}
    (≈⇒ℱX-sym (colimitCocone-onunfold-next tower m A))
    ≈⇒ℱX-refl

-- Moving source substitution out of the composite
--
-- 将源端替换移出复合
mt-go-step4 : (tower : CompatibleTower) (Y : Cosmos FinCat∞ TrivialFC∞)
  (g : ∀ m → CompatibleTower.seq tower m
       ⇒ℱX[ TowerShapeFunctors.S-proj m ] Y)
  (m : ℕ) (A : Fin (n-at m))
  → comp⇒ℱX (mediate (subtower tower (toℕ A))
                     (unfold-next (out Y) {A = toℕ A} (lift tt))
                     (sub-cocone tower Y g (toℕ A)))
            (subst-src-FinCatN (sym (defaultFin-src-eq tower A))
               (colimitCocone (subtower tower (toℕ A)) m))
    ≡ subst-src-FinCatN (sym (defaultFin-src-eq tower A))
        (comp⇒ℱX (mediate (subtower tower (toℕ A))
                          (unfold-next (out Y) {A = toℕ A} (lift tt))
                          (sub-cocone tower Y g (toℕ A)))
                 (colimitCocone (subtower tower (toℕ A)) m))
mt-go-step4 tower Y g m A =
  sym (comp⇒ℱX-subst-src (sym (defaultFin-src-eq tower A)))

-- Lifting _≈⇒ℱX_ through source substitution
--
-- 将 _≈⇒ℱX_ 沿源端替换提升
mt-go-step6 : (tower : CompatibleTower) (Y : Cosmos FinCat∞ TrivialFC∞)
  (g : ∀ m → CompatibleTower.seq tower m
       ⇒ℱX[ TowerShapeFunctors.S-proj m ] Y)
  (m : ℕ) (A : Fin (n-at m))
  (ih : comp⇒ℱX (mediate (subtower tower (toℕ A))
                          (unfold-next (out Y) {A = toℕ A} (lift tt))
                          (sub-cocone tower Y g (toℕ A)))
                 (colimitCocone (subtower tower (toℕ A)) m)
        ≈⇒ℱX sub-cocone tower Y g (toℕ A) m)
  → subst-src-FinCatN (sym (defaultFin-src-eq tower A))
      (comp⇒ℱX (mediate (subtower tower (toℕ A))
                        (unfold-next (out Y) {A = toℕ A} (lift tt))
                        (sub-cocone tower Y g (toℕ A)))
               (colimitCocone (subtower tower (toℕ A)) m))
    ≈⇒ℱX subst-src-FinCatN (sym (defaultFin-src-eq tower A))
           (sub-cocone tower Y g (toℕ A) m)
mt-go-step6 tower Y g m A ih =
  subst-src-≈ (sym (defaultFin-src-eq tower A)) ih

-- sub-cocone correctness
--
-- sub-cocone 的正确性
mt-go-step7 : (tower : CompatibleTower) (Y : Cosmos FinCat∞ TrivialFC∞)
  (g : ∀ m → CompatibleTower.seq tower m
       ⇒ℱX[ TowerShapeFunctors.S-proj m ] Y)
  (m : ℕ) (A : Fin (n-at m))
  → subst-src-FinCatN (sym (defaultFin-src-eq tower A))
      (sub-cocone tower Y g (toℕ A) m)
    ≈⇒ℱX g m .out .onunfold-next {A = A} (lift tt)
mt-go-step7 tower Y g m A = sub-cocone-correct tower Y g m A

-- onunfold-next component of the triangle equation
--
-- 三角等式的 onunfold-next 分量
mt-go-onunfold : (tower : CompatibleTower) (Y : Cosmos FinCat∞ TrivialFC∞)
  (g : ∀ m → CompatibleTower.seq tower m
       ⇒ℱX[ TowerShapeFunctors.S-proj m ] Y)
  (m : ℕ)
  (rec : (A : Fin (n-at m))
       → comp⇒ℱX (mediate (subtower tower (toℕ A))
                           (unfold-next (out Y) {A = toℕ A} (lift tt))
                           (sub-cocone tower Y g (toℕ A)))
                  (colimitCocone (subtower tower (toℕ A)) m)
         ≈⇒ℱX sub-cocone tower Y g (toℕ A) m)
  (A : Fin (n-at m))
  → comp⇒ℱX (mediate tower Y g) (colimitCocone tower m)
      .out .onunfold-next {A = A} (lift tt)
    ≈⇒ℱX g m .out .onunfold-next {A = A} (lift tt)
mt-go-onunfold tower Y g m rec A =
  ≈⇒ℱX-trans (≡-to-≈⇒ℱX (mt-go-step1 tower Y g m A))
    (≈⇒ℱX-trans (mt-go-step3 tower Y g m A)
      (≈⇒ℱX-trans (≡-to-≈⇒ℱX (mt-go-step4 tower Y g m A))
        (≈⇒ℱX-trans (mt-go-step6 tower Y g m A (rec A))
          (mt-go-step7 tower Y g m A))))

-- Assembling the coinductive comparison at layer m
--
-- 在第 m 层组装余归纳比较
mt-go-cons : (tower : CompatibleTower) (Y : Cosmos FinCat∞ TrivialFC∞)
  (g : ∀ m → CompatibleTower.seq tower m
       ⇒ℱX[ TowerShapeFunctors.S-proj m ] Y)
  (m : ℕ)
  (rec : (A : Fin (n-at m))
       → comp⇒ℱX (mediate (subtower tower (toℕ A))
                           (unfold-next (out Y) {A = toℕ A} (lift tt))
                           (sub-cocone tower Y g (toℕ A)))
                  (colimitCocone (subtower tower (toℕ A)) m)
         ≈⇒ℱX sub-cocone tower Y g (toℕ A) m)
  → comp⇒ℱX (mediate tower Y g) (colimitCocone tower m) ≈⇒ℱX g m
mt-go-cons tower Y g m rec .out .shapeTrans-eq {A} {s} p =
  mt-go-shapeTrans tower Y g m {A = A} {s = s} p
mt-go-cons tower Y g m rec .out .onPos-eq {A} {s} p =
  mt-go-onPos tower Y g m {A = A} {s = s} p
mt-go-cons tower Y g m rec .out .onunfold-next-eq {A = A} (lift tt) =
  mt-go-onunfold tower Y g m rec A

-- Generalised triangle: the source cosmos X is left implicit so that
-- f .out .onunfold-next {A = A} can be passed directly to the recursive
-- call. The recursive call is at the head of the copattern clause,
-- guarded by --guardedness (same pattern as mediate / left-id-law).
--
-- 广义三角等式：源宇宙 X 留为隐式参数，使 f .out .onunfold-next {A = A}
-- 可直接传入递归调用。递归调用位于 copattern 子句头部，受 --guardedness
-- 保护（与 mediate / left-id-law 同构）。
mt-go-gen : ∀ (tower : CompatibleTower) (Y : Cosmos FinCat∞ TrivialFC∞)
  (g : ∀ m' → CompatibleTower.seq tower m'
       ⇒ℱX[ TowerShapeFunctors.S-proj m' ] Y)
  (m : ℕ)
  {X : Cosmos (FinCatN.FinCatN m) (FinCatN.TrivialFCN m)}
  (f : X ⇒ℱX[ TowerShapeFunctors.S-proj m ] towerColimit tower)
  (h : X ⇒ℱX[ TowerShapeFunctors.S-proj m ] Y)
  → comp⇒ℱX (mediate tower Y g) f ≈⇒ℱX h
mt-go-gen tower Y g m f h .out .shapeTrans-eq {A} {s} p =
  ≡-Lift-⊤ _ _
mt-go-gen tower Y g m f h .out .onPos-eq {A} {s} p =
  ≡-Lift-⊤ _ _
mt-go-gen tower Y g m f h .out .onunfold-next-eq {A = A} (lift tt) =
  mt-go-gen (subtower tower (toℕ A))
            (unfold-next (out Y) {A = toℕ A} (lift tt))
            (sub-cocone tower Y g (toℕ A))
            m
            (f .out .onunfold-next {A = A} (lift tt))
            (h .out .onunfold-next {A = A} (lift tt))

-- Layer-m triangle equation
--
-- 第 m 层的三角等式
mt-go : (tower : CompatibleTower) (Y : Cosmos FinCat∞ TrivialFC∞)
  (g : ∀ m → CompatibleTower.seq tower m
       ⇒ℱX[ TowerShapeFunctors.S-proj m ] Y)
  (m : ℕ)
  → comp⇒ℱX (mediate tower Y g) (colimitCocone tower m) ≈⇒ℱX g m
mt-go tower Y g m =
  mt-go-gen tower Y g m (colimitCocone tower m) (g m)

-- Triangle equation: mediate composed with the cocone is the cocone
--
-- 三角等式：mediate 与余锥的复合等于余锥
mediate-triangle : ∀ (tower : CompatibleTower) (Y : Cosmos FinCat∞ TrivialFC∞)
  → (g : ∀ m → CompatibleTower.seq tower m
        ⇒ℱX[ TowerShapeFunctors.S-proj m ] Y)
  → ∀ m
  → comp⇒ℱX (mediate tower Y g) (colimitCocone tower m) ≈⇒ℱX g m
mediate-triangle tower Y g m = mt-go tower Y g m
