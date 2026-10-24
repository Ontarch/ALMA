------------------------------------------------------------------------
-- Composition congruence: hom layer
--
-- The hom-level congruence lemmas, including the pointwise hom-proof
-- and the full hom-combine used by comp-cong-≃⇒ℱ.
--
-- 复合同余：同态层
--
-- 同态层面同余引理，包括逐点 hom-proof 与 comp-cong-≃⇒ℱ 所用的
-- 完整 hom-combine。
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module Wellspring.Properties.CongHom where

open import Wellspring.Properties.CongPos public

subst-comp-tgt : ∀ {ℓ} {A B C1 C2 : Cosmos ℓ} (eq : C1 ≡ C2)
                → (f : A ⇒ℱ B) (g : B ⇒ℱ C1)
                → subst (λ C → A ⇒ℱ C) eq (g ∘⇒ℱ f)
                  ≡ subst (λ C → B ⇒ℱ C) eq g ∘⇒ℱ f
subst-comp-tgt refl f g = refl

-- Hom-level proof used by the .onHom-eq component of comp-cong
--
-- comp-cong 的 .onHom-eq 分支所用的 hom 层面证明
hom-proof : ∀ {ℓ} {S' S1 H : Cosmos ℓ} {f1 f2 : S' ⇒ℱ S1}
            (g : S1 ⇒ℱ H) (f-eq : f1 ≃⇒ℱ f2)
            {X Y : Obj S'} (h : Hom S' X Y) →
            onHom g (onHom f1 h) ≡
            subst₂ (Hom H) (sym (cong (onObj g) (f-eq .onObj-eq X)))
                           (sym (cong (onObj g) (f-eq .onObj-eq Y)))
                           (onHom g (onHom f2 h))
hom-proof {ℓ} {S'} {S1} {H} {f1} {f2} g f-eq {X} {Y} h =
  let
    objX  = f-eq .onObj-eq X
    objY  = f-eq .onObj-eq Y
    hom-eq = f-eq .onHom-eq h
    step1  = cong (onHom g) hom-eq
    step2  = onHom-subst-comm g (onObj f2 X) (onObj f2 Y) (onObj f1 X) (onObj f1 Y)
              (sym objX) (sym objY) (onHom f2 h)
    step3  = cong₂ (λ p q → subst₂ (Hom H) p q (onHom g (onHom f2 h)))
                   (cong-sym (onObj g) objX)
                   (cong-sym (onObj g) objY)
  in trans step1 (trans step2 step3)

-- Full hom-level congruence for composition
--
-- 复合的完整 hom 层面同余
hom-combine :
  ∀ {ℓ} (F G H : Cosmos ℓ) (f1 f2 : F ⇒ℱ G) (g1 g2 : G ⇒ℱ H)
    (f-eq : f1 ≃⇒ℱ f2) (g-eq : g1 ≃⇒ℱ g2)
    {A B : Obj F} (h : Hom F A B)
  → onHom (g1 ∘⇒ℱ f1) h ≡
    subst₂ (Hom H)
      (sym (comp-obj-eq F G H f1 f2 g1 g2 f-eq g-eq A))
      (sym (comp-obj-eq F G H f1 f2 g1 g2 f-eq g-eq B))
      (onHom (g2 ∘⇒ℱ f2) h)
hom-combine {ℓ} F G H f1 f2 g1 g2 f-eq g-eq {A} {B} h =
  let
    eqO-f-X : onObj f1 A ≡ onObj f2 A
    eqO-f-X = onObj-eq f-eq A
    eqO-f-Y : onObj f1 B ≡ onObj f2 B
    eqO-f-Y = onObj-eq f-eq B
    eqHom-f : onHom f1 h ≡ subst₂ (Hom G) (sym eqO-f-X) (sym eqO-f-Y) (onHom f2 h)
    eqHom-f = onHom-eq f-eq h
    O2f-X : Obj G
    O2f-X = onObj f2 A
    O2f-Y : Obj G
    O2f-Y = onObj f2 B
    eqO-g-X : onObj g1 O2f-X ≡ onObj g2 O2f-X
    eqO-g-X = onObj-eq g-eq O2f-X
    eqO-g-Y : onObj g1 O2f-Y ≡ onObj g2 O2f-Y
    eqO-g-Y = onObj-eq g-eq O2f-Y
    eqHom-g : onHom g1 (onHom f2 h)
            ≡ subst₂ (Hom H) (sym eqO-g-X) (sym eqO-g-Y) (onHom g2 (onHom f2 h))
    eqHom-g = onHom-eq g-eq (onHom f2 h)
    p-obj-X : onObj g1 O2f-X ≡ onObj g1 (onObj f1 A)
    p-obj-X = cong (onObj g1) (sym eqO-f-X)
    p-obj-Y : onObj g1 O2f-Y ≡ onObj g1 (onObj f1 B)
    p-obj-Y = cong (onObj g1) (sym eqO-f-Y)
    eqO-total-X : onObj g1 (onObj f1 A) ≡ onObj g2 O2f-X
    eqO-total-X = trans (cong (onObj g1) eqO-f-X) (onObj-eq g-eq O2f-X)
    eqO-total-Y : onObj g1 (onObj f1 B) ≡ onObj g2 O2f-Y
    eqO-total-Y = trans (cong (onObj g1) eqO-f-Y) (onObj-eq g-eq O2f-Y)
    final-path-X : trans (sym eqO-g-X) p-obj-X ≡ sym eqO-total-X
    final-path-X = sym-trans-cong-sym {ℓ} F G H f1 f2 g1 g2 f-eq g-eq A
    final-path-Y : trans (sym eqO-g-Y) p-obj-Y ≡ sym eqO-total-Y
    final-path-Y = sym-trans-cong-sym {ℓ} F G H f1 f2 g1 g2 f-eq g-eq B
  in
  begin
    onHom (g1 ∘⇒ℱ f1) h
      ≡⟨ refl ⟩
    onHom g1 (onHom f1 h)
      ≡⟨ cong (onHom g1) eqHom-f ⟩
    onHom g1 (subst₂ (Hom G) (sym eqO-f-X) (sym eqO-f-Y) (onHom f2 h))
      ≡⟨ onHom-subst-comm g1 O2f-X O2f-Y (onObj f1 A) (onObj f1 B)
           (sym eqO-f-X) (sym eqO-f-Y) (onHom f2 h) ⟩
    subst₂ (Hom H) p-obj-X p-obj-Y (onHom g1 (onHom f2 h))
      ≡⟨ cong (subst₂ (Hom H) p-obj-X p-obj-Y) eqHom-g ⟩
    subst₂ (Hom H) p-obj-X p-obj-Y
      (subst₂ (Hom H) (sym eqO-g-X) (sym eqO-g-Y) (onHom g2 (onHom f2 h)))
      ≡⟨ subst₂-trans (sym eqO-g-X) p-obj-X (sym eqO-g-Y) p-obj-Y
           (onHom g2 (onHom f2 h)) ⟩
    subst₂ (Hom H) (trans (sym eqO-g-X) p-obj-X) (trans (sym eqO-g-Y) p-obj-Y)
      (onHom g2 (onHom f2 h))
      ≡⟨ cong₂ (λ p q → subst₂ (Hom H) p q (onHom g2 (onHom f2 h)))
           final-path-X final-path-Y ⟩
    subst₂ (Hom H) (sym eqO-total-X) (sym eqO-total-Y) (onHom g2 (onHom f2 h))
      ≡⟨ refl ⟩
    subst₂ (Hom H) (sym eqO-total-X) (sym eqO-total-Y) (onHom (g2 ∘⇒ℱ f2) h)
  ∎
