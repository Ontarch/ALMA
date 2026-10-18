------------------------------------------------------------------------
-- Evaluation, evolution, and dynamics steps
--
-- Coinductive evaluation of shapes (EvalH) and of homs (EvalV), their
-- functorial maps along a morphism of cosmoi, evolution along a hom,
-- preservation of evolution under bisimulation, and the dynamics-step
-- record bundling current and next evaluations.
--
-- 求值、演化与动力学步
--
-- shape 的余归纳求值（EvalH）与 hom 的余归纳求值（EvalV）、
-- 它们沿宇宙态射的函子映射、沿 hom 的演化、演化在互模拟下的保持，
-- 以及打包当前与下一时刻求值的动力学步记录。
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module ALMA.Prototype.Properties.Dynamics where

open import ALMA.Prototype.Properties.Bisim public

-- Coinductive evaluation of a shape: values at objects and recursive
-- evaluation at positions
--
-- shape 的余归纳求值：对象处的值，以及位置处的递归求值
record EvalH {ℓ} (F : Cosmos ℓ) {A : Obj F} (s : Shape F A) : Set (lsuc (lsuc ℓ)) where
  coinductive
  field
    valH : (X : Obj F) → Set (lsuc ℓ)
    subH : (p : Pos F s) → EvalH F (pos-to-shape F s p)

-- Coinductive evaluation of a hom: values at homs and recursive
-- evaluation at positions
--
-- hom 的余归纳求值：hom 处的值，以及位置处的递归求值
record EvalV {ℓ} (F : Cosmos ℓ) {A : Obj F} (s : Shape F A) : Set (lsuc (lsuc ℓ)) where
  coinductive
  field
    valV : ∀ {B : Obj F} → Hom F A B → Set (lsuc ℓ)
    subV : (p : Pos F s) → EvalV F (pos-to-shape F s p)
open EvalH public
open EvalV public

-- Pull back an evaluation of H along a morphism F ⇒ℱ G
--
-- 沿态射 F ⇒ℱ G 拉回 H 上的求值
mapEvalH : {ℓ : Level} {F G : Cosmos ℓ} (m : F ⇒ℱ G)
         → {A : Obj F} {s : Shape F A}
         → EvalH G (onShape m s)
         → EvalH F s
mapEvalH {ℓ} {F} {G} m {A} {s} e .valH X = valH e (onObj m X)
mapEvalH {ℓ} {F} {G} m {A} {s} e .subH p =
  let eqB = onunfold-obj m s
      eqT = onPos-to-shape m p
      eqT' : subst (Shape G) (sym eqB) (pos-to-shape G (onShape m s) (onPos m p)) ≡ onShape m (pos-to-shape F s p)
      eqT' = trans (cong (subst (Shape G) (sym eqB)) (sym eqT)) (subst-inv eqB)
      P : (B : Obj G) → Shape G B → Set (lsuc (lsuc ℓ))
      P B t = EvalH G {B} t
      e' = dsubst₂ P (sym eqB) eqT' (subH e (onPos m p))
  in mapEvalH m e'

mapEvalV : {ℓ : Level} {F G : Cosmos ℓ} (m : F ⇒ℱ G)
         → {A : Obj F} {s : Shape F A}
         → EvalV G (onShape m s)
         → EvalV F s
mapEvalV {ℓ} {F} {G} m {A} {s} e .valV f = valV e (onHom m f)
mapEvalV {ℓ} {F} {G} m {A} {s} e .subV p =
  let eqB = onunfold-obj m s
      eqT = onPos-to-shape m p
      eqT' : subst (Shape G) (sym eqB) (pos-to-shape G (onShape m s) (onPos m p))
             ≡ onShape m (pos-to-shape F s p)
      eqT' = trans (cong (subst (Shape G) (sym eqB)) (sym eqT)) (subst-inv eqB)
      P : (B : Obj G) → Shape G B → Set (lsuc (lsuc ℓ))
      P B t = EvalV G {B} t
      e' = dsubst₂ P (sym eqB) eqT' (subV e (onPos m p))
  in mapEvalV m e'

-- Cast an evaluation along an equality of shapes
--
-- 沿 shape 等式 cast 求值
cast-EvalH : {ℓ : Level} (C : Cosmos ℓ) {X : Obj C} {s1 s2 : Shape C X}
           → s1 ≡ s2 → EvalH C s1 → EvalH C s2
cast-EvalH C refl e .valH X = valH e X
cast-EvalH C refl e .subH p = subH e p

cast-EvalV : {ℓ : Level} (C : Cosmos ℓ) {X : Obj C} {s1 s2 : Shape C X}
           → s1 ≡ s2 → EvalV C s1 → EvalV C s2
cast-EvalV C refl e .valV f = valV e f
cast-EvalV C refl e .subV p = subV e p

-- Evolution of an evaluation along a hom
--
-- 沿 hom 演化求值
evolveH : {ℓ : Level} (C : Cosmos ℓ)
        → {A B : Obj C} (τ : Hom C A B) {s : Shape C A}
        → EvalH C s → EvalH C (actS C τ s)
evolveH C τ {s} old .valH X = valH old X
evolveH C τ {s} old .subH p rewrite pos-actS-compat C τ s p =
  evolveH C (unfold-hom C τ s) (subH old (actP C τ s p))

evolveV : {ℓ : Level} (C : Cosmos ℓ)
        → {A B : Obj C} (τ : Hom C A B) {s : Shape C A}
        → EvalV C s → EvalV C (actS C τ s)
evolveV C τ {s} old .valV f = valV old (comp C τ f)
evolveV C τ {s} old .subV p rewrite pos-actS-compat C τ s p =
  evolveV C (unfold-hom C τ s) (subV old (actP C τ s p))

-- Bisimulation preserves the type of evolved evaluations
--
-- 互模拟保持演化后求值的类型
bisim-preserves-evolveH : {ℓ : Level} {C : Cosmos ℓ} {ml : MorphLift C}
                        → {A B : Obj C} {f g : Hom C A B}
                        → Bisim ml f g
                        → ∀ {s : Shape C A} (e : EvalH C s)
                        → EvalH C (actS C f s) ≡ EvalH C (actS C g s)
bisim-preserves-evolveH {C = C} bisim {s} e =
  cong (λ x → EvalH C x) (shape-eq bisim s)

bisim-preserves-evolveV : {ℓ : Level} {C : Cosmos ℓ} {ml : MorphLift C}
                        → {A B : Obj C} {f g : Hom C A B}
                        → Bisim ml f g
                        → ∀ {s : Shape C A} (e : EvalV C s)
                        → EvalV C (actS C f s) ≡ EvalV C (actS C g s)
bisim-preserves-evolveV {C = C} bisim {s} e =
  cong (λ x → EvalV C x) (shape-eq bisim s)

-- A dynamics step: current and next evaluations of a shape along a hom
--
-- 动力学步：shape 沿 hom 的当前与下一时刻求值
record DynamicsStep {ℓ : Level} (C : Cosmos ℓ) {A B : Obj C} (τ : Hom C A B) (s : Shape C A) : Set (lsuc (lsuc ℓ)) where
  coinductive
  private
    module C = Cosmos C
  field
    curr : EvalH C s × EvalV C s
    next : EvalH C (C.actS τ s) × EvalV C (C.actS τ s)
    eqH : evolveH C τ (curr .proj₁) ≡ (next .proj₁)
    eqV : evolveV C τ (curr .proj₂) ≡ (next .proj₂)
