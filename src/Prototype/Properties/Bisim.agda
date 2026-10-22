------------------------------------------------------------------------
-- Bisim: coinductive bisimulation of morphisms
--
-- A bisimulation between two parallel morphisms records equality of
-- their shapes and positions, compatibility of their lifted morphisms,
-- and recursive bisimulation of their unfoldings. Includes reflexivity,
-- symmetry, transitivity, and substitution under shape equality.
--
-- Bisim：态射的余归纳互模拟
--
-- 两条平行态射之间的互模拟记录它们的 shape 与 position 相等、
-- 提升态射相容，以及展开的递归互模拟。包含自反、对称、传递，
-- 以及沿 shape 等式的替换。
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module Prototype.Properties.Bisim where

open import Prototype.Properties.MorphLift public

-- Bisimulation of parallel morphisms, coinductively
--
-- 平行态射的互模拟，余归纳定义
record Bisim {ℓ : Level} {F : Cosmos ℓ} (ml : MorphLift F) {A B : Obj F} (f g : Hom F A B) : Set (lsuc ℓ) where
  coinductive
  private
    module F = Cosmos F
    module ML = MorphLift ml
  field
    shape-eq    : (s : F.Shape A) → F.actS f s ≡ F.actS g s
    pos-eq      : (s : F.Shape A) (p : F.Pos (F.actS f s))
                → F.actP f s p ≡ F.actP g s (subst F.Pos (shape-eq s) p)
    morph-bisim : ∀ (s : F.Shape A)
                → let liftF = ML.morphLift {A} {B} f s
                      liftG = ML.morphLift {A} {B} g s
                      liftG' = subst (λ X → F.unfold s ⇒ℱ F.unfold X) (sym (shape-eq s)) liftG
                  in liftF ≃⇒ℱ liftG'
    unfold-bisim : (s : F.Shape A)
                → let chF = F.unfold-hom f s
                      chG = F.unfold-hom g s
                      chG' = subst (λ X → F.Hom (F.unfold-obj s) (F.unfold-obj X)) (sym (shape-eq s)) chG
                  in Bisim ml {A = F.unfold-obj s} {B = F.unfold-obj (F.actS f s)} chF chG'
open Bisim public

module _ {ℓ} {F : Cosmos ℓ} {ml : MorphLift F} where
  -- Reflexivity of bisimulation
  --
  -- 互模拟的自反性
  refl-bisim : ∀ {A B : Obj F} (f : Hom F A B) → Bisim ml f f
  refl-bisim {A} {B} f = go A B f
    where
    go : ∀ A B (f : Hom F A B) → Bisim ml f f
    go A B f .Bisim.shape-eq s = refl
    go A B f .Bisim.pos-eq s p = refl
    go A B f .Bisim.morph-bisim s = refl-≃⇒ℱ
    go A B f .Bisim.unfold-bisim s =
      go (unfold-obj F s)
         (unfold-obj F (actS F f s))
         (unfold-hom F f s)

  -- Equality implies bisimulation
  --
  -- 相等蕴含互模拟
  ≡→bisim : ∀ {A B : Obj F} {f g : Hom F A B} → f ≡ g → Bisim ml f g
  ≡→bisim refl = refl-bisim _

  -- Substitution under shape equality preserves ≃⇒ℱ
  --
  -- 沿 shape 等式的替换保持 ≃⇒ℱ
  subst-≃⇒ℱ-shape : ∀ {X : Obj F} {s1 s2 : Shape F X}
                    → (eq : s1 ≡ s2)
                    → {C : Cosmos ℓ}
                    → {m1 m2 : C ⇒ℱ unfold F s1}
                    → m1 ≃⇒ℱ m2
                    → subst (λ s' → C ⇒ℱ unfold F s') eq m1
                      ≃⇒ℱ
                      subst (λ s' → C ⇒ℱ unfold F s') eq m2
  subst-≃⇒ℱ-shape refl h = h

  -- Symmetry of bisimulation
  --
  -- 互模拟的对称性
  sym-bisim : ∀ {A B} {f g : Hom F A B} → Bisim ml f g → Bisim ml g f
  sym-bisim {A} {B} {f} {g} b = go A B f g b
    where
    mutual
      go : ∀ Aₒ Bₒ (f g : Hom F Aₒ Bₒ) → Bisim ml f g → Bisim ml g f
      go Aₒ Bₒ f g b .Bisim.shape-eq s = sym (Bisim.shape-eq b s)
      go Aₒ Bₒ f g b .Bisim.pos-eq s p =
        let eqS  = Bisim.shape-eq b s
            p'   = subst (Pos F) (sym eqS) p
            orig = Bisim.pos-eq b s p'
            cancel : subst (Pos F) eqS p' ≡ p
            cancel = subst-inv' (Pos F) eqS {b = p}
        in sym (trans orig (cong (actP F g s) cancel))
      go Aₒ Bₒ f g b .Bisim.morph-bisim s =
        let eqS      = Bisim.shape-eq b s
            P : Shape F Bₒ → Set (lsuc ℓ)
            P X       = unfold F s ⇒ℱ unfold F X
            liftF     = morphLift ml f s
            liftG     = morphLift ml g s
            orig      = Bisim.morph-bisim b s
            symOrig   : subst P (sym eqS) liftG ≃⇒ℱ liftF
            symOrig   = sym-≃⇒ℱ orig
            substSym  : subst P eqS (subst P (sym eqS) liftG) ≃⇒ℱ subst P eqS liftF
            substSym  = subst-≃⇒ℱ-shape eqS symOrig
            cancel    : subst P eqS (subst P (sym eqS) liftG) ≡ liftG
            cancel    = subst-inv' P eqS {b = liftG}
            eq1       : liftG ≃⇒ℱ subst P eqS liftF
            eq1       = ≡-left-≃⇒ℱ (sym cancel) substSym
            eq2       : liftG ≃⇒ℱ subst P (sym (sym eqS)) liftF
            eq2       = ≡-right-≃⇒ℱ eq1 (cong (λ e → subst P e liftF) (sym-sym eqS))
        in eq2
      go Aₒ Bₒ f g b .Bisim.unfold-bisim s =
        let eqS  = Bisim.shape-eq b s
            f'   = unfold-hom F f s
            g'   = unfold-hom F g s
            orig = Bisim.unfold-bisim b s
        in aux Aₒ Bₒ s (actS F f s) (actS F g s) eqS f' g' orig
      aux : ∀ (A' B' : Obj F) (s : Shape F A') (X Y : Shape F B') (eq : X ≡ Y)
            (u : Hom F (unfold-obj F s) (unfold-obj F X))
            (v : Hom F (unfold-obj F s) (unfold-obj F Y))
          → Bisim ml u (subst (λ Z → Hom F (unfold-obj F s) (unfold-obj F Z)) (sym eq) v)
          → Bisim ml v (subst (λ Z → Hom F (unfold-obj F s) (unfold-obj F Z)) (sym (sym eq)) u)
      aux A' B' s X .X refl u v h = go (unfold-obj F s) (unfold-obj F X) u v h

  -- Transitivity of bisimulation
  --
  -- 互模拟的传递性
  trans-bisim : ∀ {A B} {f g h : Hom F A B}
              → Bisim ml f g → Bisim ml g h → Bisim ml f h
  trans-bisim {A} {B} {f} {g} {h} b1 b2 = go A B f g h b1 b2
    where
    mutual
      go : ∀ Aₒ Bₒ (f g h : Hom F Aₒ Bₒ)
         → Bisim ml f g → Bisim ml g h → Bisim ml f h
      go Aₒ Bₒ f g h b1 b2 .Bisim.shape-eq s =
        trans (Bisim.shape-eq b1 s) (Bisim.shape-eq b2 s)
      go Aₒ Bₒ f g h b1 b2 .Bisim.pos-eq s p =
        let
          eq1 = Bisim.shape-eq b1 s
          eq2 = Bisim.shape-eq b2 s
          eq  = trans eq1 eq2
          pos1 = Bisim.pos-eq b1 s p
          pos2 = Bisim.pos-eq b2 s (subst (Pos F) eq1 p)
          step = trans pos1 pos2
          comp = subst-comp eq1 eq2 {b = p}
        in trans step (cong (actP F h s) comp)
      go Aₒ Bₒ f g h b1 b2 .Bisim.morph-bisim s =
        let
          eq1 = Bisim.shape-eq b1 s
          eq2 = Bisim.shape-eq b2 s
          eq  = trans eq1 eq2
          P : Shape F Bₒ → Set (lsuc ℓ)
          P X = unfold F s ⇒ℱ unfold F X
          liftF = morphLift ml f s
          liftG = morphLift ml g s
          liftH = morphLift ml h s
          mor1 = Bisim.morph-bisim b1 s
          mor2 = Bisim.morph-bisim b2 s
          mor2' = subst-≃⇒ℱ-shape (sym eq1) mor2
          step = trans-≃⇒ℱ mor1 mor2'
          comp : subst P (sym eq1) (subst P (sym eq2) liftH)
               ≡ subst P (sym eq) liftH
          comp =
            trans
              (subst-comp (sym eq2) (sym eq1) {b = liftH})
              (cong (λ e → subst P e liftH) (sym (sym-trans eq1 eq2)))
        in ≡-right-≃⇒ℱ step comp
      go Aₒ Bₒ f g h b1 b2 .Bisim.unfold-bisim s =
        let
          eq1 = Bisim.shape-eq b1 s
          eq2 = Bisim.shape-eq b2 s
          f' = unfold-hom F f s
          g' = unfold-hom F g s
          h' = unfold-hom F h s
          orig1 = Bisim.unfold-bisim b1 s
          orig2 = Bisim.unfold-bisim b2 s
        in aux Aₒ Bₒ s (actS F f s) (actS F g s) (actS F h s)
               eq1 eq2 f' g' h' orig1 orig2
      aux : ∀ (A' B' : Obj F) (s : Shape F A')
            (X Y Z : Shape F B')
            (eq1 : X ≡ Y) (eq2 : Y ≡ Z)
            (u : Hom F (unfold-obj F s) (unfold-obj F X))
            (v : Hom F (unfold-obj F s) (unfold-obj F Y))
            (w : Hom F (unfold-obj F s) (unfold-obj F Z))
          → Bisim ml u (subst (λ Q → Hom F (unfold-obj F s) (unfold-obj F Q)) (sym eq1) v)
          → Bisim ml v (subst (λ Q → Hom F (unfold-obj F s) (unfold-obj F Q)) (sym eq2) w)
          → Bisim ml u (subst (λ Q → Hom F (unfold-obj F s) (unfold-obj F Q)) (sym (trans eq1 eq2)) w)
      aux A' B' s X .X .X refl refl u v w h1 h2 =
        go (unfold-obj F s) (unfold-obj F X) u v w h1 h2
