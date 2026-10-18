------------------------------------------------------------------------
-- Sub-cocones and their correctness for the mediating morphism
--
-- The layer-k component of a cocone restricted to a subtower, its
-- construction by decidable cases on k and m, and the proof that it
-- agrees with the original cocone component after source substitution.
--
-- 子余锥及其对中介态射的正确性
--
-- 余锥的第 k 层分量限制到子塔，按 k 与 m 的可判定情形构造，
-- 并证明其在源端替换后与原余锥分量一致。
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module ALMA.SecondPass.FinCatInfinitySubCocone where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Level using (Lift; lift)
open import Data.Empty using (⊥-elim)
open import Data.Nat using (ℕ; zero; suc; _+_; _∸_; _≤_)
open import Data.Nat.Properties using
  (≤-total; m+[n∸m]≡n; ≤-refl; ≤-trans; m≤n⇒m≤1+n; 1+n≰n; ≡-irrelevant)
open import Data.Fin.Base using (Fin; toℕ)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Unit.Polymorphic.Base using (⊤; tt)
open import Relation.Binary.PropositionalEquality.Core using (cong; sym; trans; subst)
open import Relation.Binary.PropositionalEquality.Properties using (J)

open import Categories.Functor.Core using (Functor)

open import ALMA.Cosmos.ContCatEquiv using (ShapeCat)
open import ALMA.SecondPass.Unfolding using (Unfolding)
open Unfolding using (unfold-next)
open import ALMA.SecondPass.Cosmos using (Cosmos; out)
open import ALMA.SecondPass.FinCatNWitness using (module FinCatN)
open import ALMA.SecondPass.FinCatInfinity using (FinCat∞; TrivialFC∞; n-at)
open import ALMA.SecondPass.FinCatInfinityProjection using
  (module FinCatNColimitProjection)
open FinCatNColimitProjection using (defaultFin; defaultFin-toℕ-self)
open import ALMA.SecondPass.FinCatInfinityColimit using
  (CompatibleTower; subtower; _⇒ℱX[_]_; ⇒ℱXLayer[_]; comp⇒ℱX
  ; module TowerShapeFunctors)
open import ALMA.SecondPass.FinCatInfinityColimitUniversal using
  (_≈⇒ℱX_; ≈⇒ℱX-sym; ≈⇒ℱX-trans; ≡-to-≈⇒ℱX; lift-subtower
  ; transport-to-S-proj; toℕ-defaultFin; split≤)
open import ALMA.SecondPass.FinCatInfinitySubstitution
open import ALMA.SecondPass.FinCatInfinityProjectionUnfold using
  (toℕ≤n∸1; defaultFin-src-eq)

open _⇒ℱX[_]_
open ⇒ℱXLayer[_]
open CompatibleTower
open _≈⇒ℱX_

-- Sub-cocone component in the case k ≤ m
--
-- 情形 k ≤ m 下的子余锥分量
sub-cocone-k≤m
  : (tower : CompatibleTower) (Y : Cosmos FinCat∞ TrivialFC∞)
    (g : ∀ m' → CompatibleTower.seq tower m'
             ⇒ℱX[ TowerShapeFunctors.S-proj m' ] Y)
    (k m : ℕ) (k≤m : k ≤ m)
  → CompatibleTower.seq (subtower tower k) m
    ⇒ℱX[ TowerShapeFunctors.S-proj m ]
      unfold-next (out Y) {A = k} (lift tt)
sub-cocone-k≤m tower Y g k m k≤m =
  subst (λ Y' → CompatibleTower.seq (subtower tower k) m
              ⇒ℱX[ TowerShapeFunctors.S-proj m ] Y')
        (cong (λ k' → unfold-next (out Y) {A = k'} (lift tt))
              (toℕ-defaultFin m k
                (≤-trans k≤m (m≤n⇒m≤1+n ≤-refl))))
        (g m .out .onunfold-next {A = defaultFin m k} (lift tt))

-- Sub-cocone component in the case m ≤ k ≤ suc m
--
-- 情形 m ≤ k ≤ suc m 下的子余锥分量
sub-cocone-m≤k≤sucm
  : (tower : CompatibleTower) (Y : Cosmos FinCat∞ TrivialFC∞)
    (g : ∀ m' → CompatibleTower.seq tower m'
             ⇒ℱX[ TowerShapeFunctors.S-proj m' ] Y)
    (k m : ℕ) (m≤k : m ≤ k) (k≤sucm : k ≤ suc m)
  → CompatibleTower.seq (subtower tower k) m
    ⇒ℱX[ TowerShapeFunctors.S-proj m ]
      unfold-next (out Y) {A = k} (lift tt)
sub-cocone-m≤k≤sucm tower Y g k m m≤k k≤sucm =
  subst (λ Y' → CompatibleTower.seq (subtower tower k) m
              ⇒ℱX[ TowerShapeFunctors.S-proj m ] Y')
        (cong (λ k' → unfold-next (out Y) {A = k'} (lift tt))
              (toℕ-defaultFin m k k≤sucm))
        (g m .out .onunfold-next {A = defaultFin m k} (lift tt))

-- Sub-cocone component in the far case suc (suc m) ≤ k
--
-- 远端情形 suc (suc m) ≤ k 下的子余锥分量
sub-cocone-far
  : (tower : CompatibleTower) (Y : Cosmos FinCat∞ TrivialFC∞)
    (g : ∀ m' → CompatibleTower.seq tower m'
             ⇒ℱX[ TowerShapeFunctors.S-proj m' ] Y)
    (k m : ℕ) (m≤k : m ≤ k) (ssucm≤k : suc (suc m) ≤ k)
  → CompatibleTower.seq (subtower tower k) m
    ⇒ℱX[ TowerShapeFunctors.S-proj m ]
      unfold-next (out Y) {A = k} (lift tt)
sub-cocone-far tower Y g k m m≤k ssucm≤k =
  let d          = k ∸ m
      k≡m+d      = sym (m+[n∸m]≡n m≤k)
      k≤m+d      : k ≤ m + d
      k≤m+d      = subst (λ x → k ≤ x) k≡m+d ≤-refl
      k≤suc-m+d  : k ≤ suc (m + d)
      k≤suc-m+d  = m≤n⇒m≤1+n k≤m+d
      emb        = lift-subtower tower k m d
      gk         = subst (λ Y' → CompatibleTower.seq (subtower tower k) (m + d)
                             ⇒ℱX[ TowerShapeFunctors.S-proj (m + d) ] Y')
                         (cong (λ k' → unfold-next (out Y) {A = k'} (lift tt))
                               (toℕ-defaultFin (m + d) k k≤suc-m+d))
                         (g (m + d) .out .onunfold-next
                            {A = defaultFin (m + d) k} (lift tt))
      comp       = comp⇒ℱX gk emb
  in transport-to-S-proj comp

-- Sub-cocone component dispatched on the relations between k and m
--
-- 按 k 与 m 的关系分派的子余锥分量
sub-cocone-with-dec
  : (tower : CompatibleTower) (Y : Cosmos FinCat∞ TrivialFC∞)
    (g : ∀ m' → CompatibleTower.seq tower m'
             ⇒ℱX[ TowerShapeFunctors.S-proj m' ] Y)
    (k m : ℕ)
    (d₁ : m ≤ k ⊎ k ≤ m)
    (d₂ : k ≤ suc m ⊎ suc (suc m) ≤ k)
  → CompatibleTower.seq (subtower tower k) m
    ⇒ℱX[ TowerShapeFunctors.S-proj m ]
      unfold-next (out Y) {A = k} (lift tt)
sub-cocone-with-dec tower Y g k m (inj₂ k≤m) _ =
  sub-cocone-k≤m tower Y g k m k≤m
sub-cocone-with-dec tower Y g k m (inj₁ m≤k) (inj₁ k≤sucm) =
  sub-cocone-m≤k≤sucm tower Y g k m m≤k k≤sucm
sub-cocone-with-dec tower Y g k m (inj₁ m≤k) (inj₂ ssucm≤k) =
  sub-cocone-far tower Y g k m m≤k ssucm≤k

-- Sub-cocone component in the case k = 0
--
-- 情形 k = 0 下的子余锥分量
sub-cocone-zero
  : (tower : CompatibleTower) (Y : Cosmos FinCat∞ TrivialFC∞)
    (g : ∀ m' → CompatibleTower.seq tower m'
              ⇒ℱX[ TowerShapeFunctors.S-proj m' ] Y)
    (m : ℕ)
  → CompatibleTower.seq (subtower tower 0) m
    ⇒ℱX[ TowerShapeFunctors.S-proj m ]
      unfold-next (out Y) {A = 0} (lift tt)
sub-cocone-zero tower Y g m =
  g m .out .onunfold-next {A = defaultFin m 0} (lift tt)

-- Sub-cocone: the layer-k component of a cocone, restricted to a
-- subtower. This is the local data out of which mediate is built
--
-- 子余锥：余锥的第 k 层分量限制到子塔。这是构造 mediate 的局部数据
sub-cocone
  : ∀ (tower : CompatibleTower) (Y : Cosmos FinCat∞ TrivialFC∞)
  → (g : ∀ m' → CompatibleTower.seq tower m'
             ⇒ℱX[ TowerShapeFunctors.S-proj m' ] Y)
  → ∀ k m
  → CompatibleTower.seq (subtower tower k) m
    ⇒ℱX[ TowerShapeFunctors.S-proj m ]
      unfold-next (out Y) {A = k} (lift tt)
sub-cocone tower Y g k m =
  sub-cocone-with-dec tower Y g k m
    (≤-total m k) (split≤ k (suc m))

-- g's unfold-next at A, packaged with source substitution
--
-- g 在 A 处的 unfold-next，配合源端替换打包
g-unfold : ∀ (tower : CompatibleTower) (Y : Cosmos FinCat∞ TrivialFC∞)
  (g : ∀ m → CompatibleTower.seq tower m
         ⇒ℱX[ TowerShapeFunctors.S-proj m ] Y)
  m (A : Fin (n-at m))
  → unfold-next (out (CompatibleTower.seq tower m)) {A = A} (lift tt)
    ⇒ℱX[ TowerShapeFunctors.S-proj m ]
    unfold-next (out Y) {A = toℕ A} (lift tt)
g-unfold tower Y g m A =
  subst-src-FinCatN (sym (defaultFin-src-eq tower A))
    (sub-cocone tower Y g (toℕ A) m)

-- Correctness of sub-cocone when k = toℕ A is in range
--
-- 当 k = toℕ A 在范围内时，sub-cocone 的正确性
sub-cocone-correct-k≤m :
  (tower : CompatibleTower)
  (Y : Cosmos FinCat∞ TrivialFC∞)
  (g : ∀ m → CompatibleTower.seq tower m
           ⇒ℱX[ TowerShapeFunctors.S-proj m ] Y)
  (m : ℕ)
  (A : Fin (n-at m))
  (k≤n∸1 : toℕ A ≤ n-at m ∸ 1)
  → let k    = toℕ A
        B    = defaultFin m k
        p    = toℕ-defaultFin m k k≤n∸1
        S    = TowerShapeFunctors.S-proj m
        src  = CompatibleTower.seq (subtower tower k) m
        Tgt  = λ (Z : Cosmos FinCat∞ TrivialFC∞) → src ⇒ℱX[ S ] Z
        Yk   = λ (j : ℕ) →
          unfold-next (out Y) {A = j} (lift tt)
    in  subst-src-FinCatN (sym (defaultFin-src-eq tower A))
          (subst Tgt (cong Yk p)
             (g m .out .onunfold-next {A = B} (lift tt)))
        ≈⇒ℱX g m .out .onunfold-next {A = A} (lift tt)
sub-cocone-correct-k≤m tower Y g m A k≤n∸1 =
  J {A = Fin (n-at m)} {x = B}
    (λ A' e' → (p' : toℕ B ≡ toℕ A') → motive A' e' p')
    {y = A}
    e
    base
    p
  where
    k : ℕ
    k = toℕ A
    B : Fin (n-at m)
    B = defaultFin m k
    e : B ≡ A
    e = defaultFin-toℕ-self m A
    p : toℕ B ≡ toℕ A
    p = toℕ-defaultFin m k k≤n∸1

    S : Functor (ShapeCat (FinCatN.FinCatN m) (FinCatN.TrivialFCN m))
                (ShapeCat FinCat∞ TrivialFC∞)
    S = TowerShapeFunctors.S-proj m

    src : Cosmos (FinCatN.FinCatN m) (FinCatN.TrivialFCN m)
    src = CompatibleTower.seq (subtower tower k) m

    Tgt : Cosmos FinCat∞ TrivialFC∞ → Set _
    Tgt = λ Z → src ⇒ℱX[ S ] Z

    Yk : ℕ → Cosmos FinCat∞ TrivialFC∞
    Yk = λ j → unfold-next (out Y) {A = j} (lift tt)

    unfold-src : Fin (n-at m) → Cosmos (FinCatN.FinCatN m) (FinCatN.TrivialFCN m)
    unfold-src = λ z →
      unfold-next (out (CompatibleTower.seq tower m)) {A = z} (lift tt)

    src-eq : ∀ (A' : Fin (n-at m)) (e' : B ≡ A') → unfold-src B ≡ unfold-src A'
    src-eq = λ A' e' → sym (cong unfold-src (sym e'))

    motive : (A' : Fin (n-at m)) (e' : B ≡ A')
             (p' : toℕ B ≡ toℕ A') → Set _
    motive A' e' p' =
      _≈⇒ℱX_
        {S = S}
        {x = unfold-src A'} {y = Yk (toℕ A')}
        (subst-src-FinCatN
          {m = m} {x = unfold-src B} {x' = unfold-src A'}
          {Y = Yk (toℕ A')}
          (src-eq A' e')
          (subst (λ Z → unfold-src B ⇒ℱX[ S ] Z) (cong Yk p')
             (g m .out .onunfold-next {A = B} (lift tt))))
        (g m .out .onunfold-next {A = A'} (lift tt))

    base : (p' : toℕ B ≡ toℕ B) → motive B refl p'
    base p' =
      ≡-to-≈⇒ℱX
        {S = S}
        {x = unfold-src B} {y = Yk (toℕ B)}
        (cong
           (λ p0 → subst (λ Z → unfold-src B ⇒ℱX[ S ] Z) (cong Yk p0)
                     (g m .out .onunfold-next {A = B} (lift tt)))
           (≡-irrelevant p' refl))

-- Correctness of sub-cocone in general
--
-- sub-cocone 的一般正确性
sub-cocone-correct
  : ∀ tower Y g m A
  → subst-src-FinCatN (sym (defaultFin-src-eq tower A))
      (sub-cocone tower Y g (toℕ A) m)
    ≈⇒ℱX g m .out .onunfold-next {A = A} (lift tt)
sub-cocone-correct tower Y g m A
  with ≤-total m (toℕ A) | split≤ (toℕ A) (suc m)
... | inj₂ k≤m | _ =
      sub-cocone-correct-k≤m tower Y g m A
        (≤-trans k≤m (m≤n⇒m≤1+n ≤-refl))
... | inj₁ m≤k | inj₁ k≤sucm =
      sub-cocone-correct-k≤m tower Y g m A k≤sucm
... | inj₁ m≤k | inj₂ ssucm≤k =
      ⊥-elim (1+n≰n (≤-trans ssucm≤k (toℕ≤n∸1 m A)))
