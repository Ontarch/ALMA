------------------------------------------------------------------------
-- Unfolding lemmas for projection cosmoi and colimit cocones
--
-- The defaultFin normalisation, the projCosmos-morphism unfold-next
-- identities, and the packaged forms consumed by mediate.
--
-- 投影宇宙与余极限余锥的展开引理
--
-- defaultFin 正规化、projCosmos-morphism 的 unfold-next 恒等式，
-- 以及 mediate 所使用的打包形式。
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module SecondPass.FinCatInfinityProjectionUnfold where

open import Agda.Primitive using (Level)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Level using (Lift; lift)
open import Data.Nat using (ℕ; zero; suc; _+_; _∸_; _≤_; _≤?_; z≤n; s≤s; ≤-pred)
open import Data.Fin.Base using (Fin; toℕ)
open import Data.Fin.Properties using (toℕ<n)
open import Data.Unit.Polymorphic.Base using (⊤; tt)
open import Relation.Binary.PropositionalEquality.Core using
  (cong; cong₂; sym; trans; subst)
open import Relation.Binary.PropositionalEquality.Properties using
  (J; subst-∘; subst-sym-subst; trans-symˡ; module ≡-Reasoning)

open import Categories.Functor using (id)

open import SecondPass.Unfolding using (Unfolding)
open Unfolding using (unfold-next)
open import SecondPass.Cosmos using (Cosmos; out)
open import SecondPass.FinCatNWitness using (module FinCatN)
open import SecondPass.FinCatInfinity using (FinCat∞; TrivialFC∞; n-at)
open import SecondPass.FinCatInfinityProjection using
  (module FinCatNColimitProjection)
open FinCatNColimitProjection using
  (defaultFin; defaultFin-toℕ-self; projCosmos; projCosmos-F₀-spec)
open import SecondPass.FinCatInfinityColimit using
  (CompatibleTower; subtower; towerColimit; _⇒ℱX[_]_; ⇒ℱXLayer[_]; comp⇒ℱX
  ; module TowerShapeFunctors; module ProjCosmosMorphism)
open import SecondPass.FinCatInfinityColimitUniversal using
  (colimitCocone; _≈⇒ℱX_; ≈⇒ℱXLayer; ≈⇒ℱX-refl; ≈⇒ℱX-sym; ≈⇒ℱX-trans
  ; ≡-to-≈⇒ℱX; comp⇒ℱX-cong-≈⇒ℱX)
open import SecondPass.FinCatInfinitySubstitution

open _⇒ℱX[_]_
open ⇒ℱXLayer[_]
open _≈⇒ℱX_
open CompatibleTower

-- defaultFin-src-eq: the unfold-next at A equals that at
-- defaultFin m (toℕ A)
--
-- defaultFin-src-eq：A 处的 unfold-next 等于 defaultFin m (toℕ A) 处的 unfold-next
defaultFin-src-eq : ∀ {m} (tower : CompatibleTower) (A : Fin (n-at m))
  → unfold-next (out (seq tower m)) {A = A} (lift tt)
  ≡ unfold-next (out (seq tower m)) {A = defaultFin m (toℕ A)} (lift tt)
defaultFin-src-eq {m} tower A =
  cong (λ z → unfold-next (out (seq tower m)) {A = z} (lift tt))
       (sym (FinCatNColimitProjection.defaultFin-toℕ-self m A))

-- Every layer-m position is in range for the defaultFin bound:
-- toℕ A ≤ n-at m ∸ 1
--
-- 第 m 层的每个位置都在 defaultFin 的界内：toℕ A ≤ n-at m ∸ 1
toℕ≤n∸1 : ∀ m (A : Fin (n-at m)) → toℕ A ≤ n-at m ∸ 1
toℕ≤n∸1 m A = ≤-pred (toℕ<n A)

-- Source and target substitutions agree on projCosmos-morphism
--
-- 源端与目标端替换在 projCosmos-morphism 上一致
subst-src-vs-subst-dst : ∀ (tower : CompatibleTower) m (A : Fin (n-at m))
  → let x0 = unfold-next (out (seq tower m)) {A = A} (lift tt)
        x1 = unfold-next (out (seq tower m)) {A = defaultFin m (toℕ A)} (lift tt)
        S  = TowerShapeFunctors.S-proj m
    in  subst-src-FinCatN (sym (defaultFin-src-eq tower A))
          (ProjCosmosMorphism.projCosmos-morphism m x1)
      ≡ subst (λ z → x0 ⇒ℱX[ S ] projCosmos m z) (defaultFin-src-eq tower A)
              (ProjCosmosMorphism.projCosmos-morphism m x0)
subst-src-vs-subst-dst tower m A =
  let x0 = unfold-next (out (seq tower m)) {A = A} (lift tt)
      S  = TowerShapeFunctors.S-proj m
  in  J {x = x0} (λ y (e : x0 ≡ y) →
         subst (λ z → z ⇒ℱX[ S ] projCosmos m y) (sym e)
               (ProjCosmosMorphism.projCosmos-morphism m y)
         ≡ subst (λ z → x0 ⇒ℱX[ S ] projCosmos m z) e
               (ProjCosmosMorphism.projCosmos-morphism m x0))
      (defaultFin-src-eq tower A)
      refl

-- Unfold-next of projCosmos-morphism, related by source and target
-- substitutions
--
-- projCosmos-morphism 的 unfold-next，通过源端与目标端替换相关联
projCosmos-morphism-onunfold-next : ∀ (tower : CompatibleTower) m (A : Fin (n-at m))
  → let k = toℕ A
        x = unfold-next (out (seq tower m)) {A = A} (lift tt)
        x' = unfold-next (out (seq tower m)) {A = defaultFin m k} (lift tt)
        eq = defaultFin-src-eq tower A
        S = TowerShapeFunctors.S-proj m
    in  subst-src-FinCatN (sym eq) (ProjCosmosMorphism.projCosmos-morphism m x')
        ≡ subst (λ z → x ⇒ℱX[ S ] projCosmos m z) eq
                (ProjCosmosMorphism.projCosmos-morphism m x)
projCosmos-morphism-onunfold-next tower m A =
  let x  = unfold-next (out (seq tower m)) {A = A} (lift tt)
      S  = TowerShapeFunctors.S-proj m
      eq = defaultFin-src-eq tower A
  in  J {x = x} (λ y (e : x ≡ y) →
         subst (λ z → z ⇒ℱX[ S ] projCosmos m y) (sym e)
               (ProjCosmosMorphism.projCosmos-morphism m y)
         ≡ subst (λ z → x ⇒ℱX[ S ] projCosmos m z) e
               (ProjCosmosMorphism.projCosmos-morphism m x))
      eq
      refl

-- _≈⇒ℱX_ version of the previous statement
--
-- 前一陈述的 _≈⇒ℱX_ 版本
projCosmos-morphism-onunfold-next-≈ :
  ∀ (tower : CompatibleTower) m (A : Fin (n-at m))
  → let k = toℕ A
        x  = unfold-next (out (seq tower m)) {A = A} (lift tt)
        x' = unfold-next (out (seq tower m)) {A = defaultFin m k} (lift tt)
        eq = defaultFin-src-eq tower A
        S  = TowerShapeFunctors.S-proj m
    in  subst-src-FinCatN (sym eq) (ProjCosmosMorphism.projCosmos-morphism m x')
        ≈⇒ℱX
        subst (λ z → x ⇒ℱX[ S ] projCosmos m z) eq
              (ProjCosmosMorphism.projCosmos-morphism m x)
projCosmos-morphism-onunfold-next-≈ tower m A =
  ≡-to-≈⇒ℱX (projCosmos-morphism-onunfold-next tower m A)

-- Reverse direction: target substitution corresponds to source
-- substitution
--
-- 反方向：目标端替换对应源端替换
subst-dst-≈⇒ℱX :
  ∀ (tower : CompatibleTower) m (A : Fin (n-at m))
  → let k = toℕ A
        x  = unfold-next (out (seq tower m)) {A = A} (lift tt)
        x' = unfold-next (out (seq tower m)) {A = defaultFin m k} (lift tt)
        eq = defaultFin-src-eq tower A
        S  = TowerShapeFunctors.S-proj m
    in  subst (λ z → x ⇒ℱX[ S ] projCosmos m z) eq
              (ProjCosmosMorphism.projCosmos-morphism m x)
        ≈⇒ℱX
        subst-src-FinCatN (sym eq)
          (ProjCosmosMorphism.projCosmos-morphism m x')
subst-dst-≈⇒ℱX tower m A =
  ≈⇒ℱX-sym (projCosmos-morphism-onunfold-next-≈ tower m A)

-- Unfold-next of projCosmos-morphism expressed by target substitution
--
-- projCosmos-morphism 的 unfold-next 用目标端替换表示
f-onunfold-next-eq :
  ∀ (tower : CompatibleTower) m (A : Fin (n-at m))
  → let k  = toℕ A
        x  = unfold-next (out (seq tower m)) {A = A} (lift tt)
        x' = unfold-next (out (seq tower m)) {A = defaultFin m k} (lift tt)
        eq = defaultFin-src-eq tower A
        S  = TowerShapeFunctors.S-proj m
        f  = ProjCosmosMorphism.projCosmos-morphism m (CompatibleTower.seq tower m)
    in  f .out .onunfold-next {A = A} (lift tt)
        ≡ subst (λ z → x ⇒ℱX[ S ] projCosmos m z) eq
                (ProjCosmosMorphism.projCosmos-morphism m x)
f-onunfold-next-eq tower m A
  with FinCatNColimitProjection.defaultFin m (toℕ A)
     | FinCatNColimitProjection.defaultFin-toℕ-self m A
... | .A | refl = refl

-- Inverse direction of the previous statement
--
-- 前一陈述的反方向
subst-src-projCosmos-eq-onunfold :
  ∀ (tower : CompatibleTower) m (A : Fin (n-at m))
  → let k  = toℕ A
        x' = unfold-next (out (seq tower m)) {A = defaultFin m k} (lift tt)
        eq = defaultFin-src-eq tower A
        S  = TowerShapeFunctors.S-proj m
        f  = ProjCosmosMorphism.projCosmos-morphism m (CompatibleTower.seq tower m)
    in  subst-src-FinCatN (sym eq)
          (ProjCosmosMorphism.projCosmos-morphism m x')
        ≡ f .out .onunfold-next {A = A} (lift tt)
subst-src-projCosmos-eq-onunfold tower m A
  with FinCatNColimitProjection.defaultFin m (toℕ A)
     | FinCatNColimitProjection.defaultFin-toℕ-self m A
... | .A | refl = refl

-- Symmetric form of projCosmos-morphism's unfold-next equality
--
-- projCosmos-morphism 的 unfold-next 等式的对称形式
projCosmos-morphism-unfold-sym : ∀ (tower : CompatibleTower) m (A : Fin (n-at m))
  → let src-A = unfold-next (out (seq tower m)) {A = A} (lift tt)
        x'    = unfold-next (out (seq tower m)) {A = defaultFin m (toℕ A)} (lift tt)
        eq    = defaultFin-src-eq tower A
        S     = TowerShapeFunctors.S-proj m
    in  ProjCosmosMorphism.projCosmos-morphism m (seq tower m)
          .out .onunfold-next {A = A} (lift tt)
        ≡ subst-src-FinCatN (sym eq)
            (ProjCosmosMorphism.projCosmos-morphism m x')
projCosmos-morphism-unfold-sym tower m A =
  trans (f-onunfold-next-eq tower m A)
        (J {x = src-A}
           (λ x' eq →
             subst (λ z → src-A ⇒ℱX[ S ] projCosmos m z) eq
                   (ProjCosmosMorphism.projCosmos-morphism m src-A)
             ≡ subst-src-FinCatN (sym eq)
                   (ProjCosmosMorphism.projCosmos-morphism m x'))
           eq
           refl)
  where
    src-A = unfold-next (out (seq tower m)) {A = A} (lift tt)
    eq    = defaultFin-src-eq tower A
    S     = TowerShapeFunctors.S-proj m

-- colimitCocone's unfold-next at A, packaged with source substitution
--
-- colimitCocone 在 A 处的 unfold-next，配合源端替换打包
colimitCocone-unfold : ∀ (tower : CompatibleTower) m (A : Fin (n-at m))
  → unfold-next (out (CompatibleTower.seq tower m)) {A = A} (lift tt)
    ⇒ℱX[ TowerShapeFunctors.S-proj m ]
    towerColimit (subtower tower (toℕ A))
colimitCocone-unfold tower m A =
  subst-src-FinCatN (sym (defaultFin-src-eq tower A))
    (colimitCocone (subtower tower (toℕ A)) m)

-- colimitCocone-unfold agrees with colimitCocone's onunfold-next
--
-- colimitCocone-unfold 与 colimitCocone 的 onunfold-next 一致
colimitCocone-unfold-eq' : ∀ (tower : CompatibleTower) m (A : Fin (n-at m))
  → colimitCocone-unfold tower m A
    ≡ colimitCocone tower m .out .onunfold-next {A = A} (lift tt)
colimitCocone-unfold-eq' tower m A =
  trans (comp⇒ℱX-subst-src (sym eq))
        (cong₂ comp⇒ℱX
          refl
          (sym (projCosmos-morphism-unfold-sym tower m A)))
  where
    eq = defaultFin-src-eq tower A

-- View an unfolding as a cosmos by taking out
--
-- 将展开视为宇宙（取 out）
cosmos-from-unfolding :
  Unfolding TrivialFC∞ (Cosmos FinCat∞ TrivialFC∞)
  → Cosmos FinCat∞ TrivialFC∞
cosmos-from-unfolding u .out = u

-- Unfold-next of colimitCocone, related to the subtower's colimitCocone
-- by source substitution
--
-- colimitCocone 的 unfold-next，通过源端替换与子塔的 colimitCocone 关联
colimitCocone-onunfold-next : ∀ (tower : CompatibleTower) m (A : Fin (n-at m))
  → let k = toℕ A
        Y = towerColimit (subtower tower k)
    in  subst-src-FinCatN (sym (defaultFin-src-eq tower A))
          (colimitCocone (subtower tower k) m)
        ≈⇒ℱX
        (colimitCocone tower m .out .onunfold-next {A = A} (lift tt))
colimitCocone-onunfold-next tower m A =
  let k  = toℕ A
      eq = defaultFin-src-eq tower A
  in ≈⇒ℱX-trans
       (≡-to-≈⇒ℱX (comp⇒ℱX-subst-src (sym eq)))
       (comp⇒ℱX-cong-≈⇒ℱX
          (≡-to-≈⇒ℱX (subst-src-projCosmos-eq-onunfold tower m A))
          ≈⇒ℱX-refl)
