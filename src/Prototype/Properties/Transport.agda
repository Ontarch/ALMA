------------------------------------------------------------------------
-- Transport lemmas for Pos, Hom, and Shape
--
-- Transport of Pos and Hom along an equality of cosmoi, the
-- shape/position/hom substitution lemmas, and the interaction between
-- unfold and shape substitution. These are the low-level path
-- manipulations used by the equivalence and composition reasoning.
--
-- Pos 与 Hom 的运输引理
--
-- 沿宇宙等式运输 Pos 与 Hom，shape/position/hom 替换引理，以及
-- unfold 与 shape 替换之间的交互。这些是等价推理与复合推理所依赖的
-- 底层路径操作。
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module Prototype.Properties.Transport where

open import Prototype.Properties.SubstCore public

-- Transport of Pos/Hom and related lemmas
--
-- 运输 Pos/Hom 及相关引理
transport-Pos : ∀ ℓ (C₁ C₂ : Cosmos ℓ) (eq : C₁ ≡ C₂)
              → {o : Obj C₁} {s : Shape C₁ o}
              → Pos C₁ s → Pos C₂ (subst (ShapeSubstP ℓ) (ShapeEq ℓ C₁ C₂ eq o) s)
transport-Pos ℓ C₁ .C₁ refl p = p

transport-Hom : ∀ ℓ (C₁ C₂ : Cosmos ℓ) (eq : C₁ ≡ C₂) {a b : Obj C₁}
              → Hom C₁ a b → Hom C₂ (ObjSubst ℓ C₁ C₂ eq a) (ObjSubst ℓ C₁ C₂ eq b)
transport-Hom ℓ C₁ .C₁ refl f = f

shape-subst-lemma : ∀ ℓ (C₁ C₂ : Cosmos ℓ) (eq : C₁ ≡ C₂)
  {o1 o2 : Obj C₁} (eO : o1 ≡ o2)
  (s2 : Shape C₁ o2)
  → subst (ShapeSubstP ℓ) (ShapeEq ℓ C₁ C₂ eq o1) (subst (Shape C₁) (sym eO) s2)
  ≡ subst (Shape C₂) (sym (cong (ObjSubst ℓ C₁ C₂ eq) eO))
    (subst (ShapeSubstP ℓ) (ShapeEq ℓ C₁ C₂ eq o2) s2)
shape-subst-lemma ℓ C₁ .C₁ refl {o1} {o2} eO s2 =
  begin
    subst (ShapeSubstP ℓ) (ShapeEq ℓ C₁ C₁ refl o1) (subst (Shape C₁) (sym eO) s2)
      ≡⟨ refl ⟩
    subst (Shape C₁) (sym eO) s2
      ≡⟨ cong (λ (eq : o1 ≡ o2) → subst (Shape C₁) (sym eq) s2)
              (sym (cong-id eO)) ⟩
    subst (Shape C₁) (sym (cong (ObjSubst ℓ C₁ C₁ refl) eO)) s2
      ≡⟨ refl ⟩
    subst (Shape C₁) (sym (cong (ObjSubst ℓ C₁ C₁ refl) eO))
          (subst (ShapeSubstP ℓ) (ShapeEq ℓ C₁ C₁ refl o2) s2)
  ∎

pos-subst-lemma :
  ∀ ℓ (C₁ C₂ : Cosmos ℓ) (eq : C₁ ≡ C₂)
  {o1 o2 : Obj C₁} (eO : o1 ≡ o2)
  {s2 : Shape C₁ o2}
  (p2 : Pos C₁ {o2} s2)
  → transport-Pos ℓ C₁ C₂ eq {o1} {subst (Shape C₁) (sym eO) s2}
      (subst {A = ObjShape ℓ C₁} {ℓ = lsuc ℓ} (PosSubstP ℓ C₁)
        (sym (same-C-PosEq ℓ C₁ eO s2)) p2)
  ≡ subst {A = Shape C₂ (ObjSubst ℓ C₁ C₂ eq o1)} {ℓ = lsuc ℓ}
      (Pos C₂ {ObjSubst ℓ C₁ C₂ eq o1})
      (sym (shape-subst-lemma ℓ C₁ C₂ eq eO s2))
      (subst {A = ObjShape ℓ C₂} {ℓ = lsuc ℓ} (PosSubstP ℓ C₂)
        (sym (same-C-PosEq ℓ C₂
          (cong (ObjSubst ℓ C₁ C₂ eq) eO)
          (subst (ShapeSubstP ℓ) (ShapeEq ℓ C₁ C₂ eq o2) s2)))
        (transport-Pos ℓ C₁ C₂ eq {o2} {s2} p2))
pos-subst-lemma ℓ C₁ C₂ eq {o1} {o2} eO {s2} p2 =
  J (λ C₂' eq' →
       transport-Pos ℓ C₁ C₂' eq' {o1} {subst (Shape C₁) (sym eO) s2}
         (subst (PosSubstP ℓ C₁) (sym (same-C-PosEq ℓ C₁ eO s2)) p2)
       ≡ subst (Pos C₂' {ObjSubst ℓ C₁ C₂' eq' o1})
           (sym (shape-subst-lemma ℓ C₁ C₂' eq' eO s2))
           (subst (PosSubstP ℓ C₂')
             (sym (same-C-PosEq ℓ C₂'
               (cong (ObjSubst ℓ C₁ C₂' eq') eO)
               (subst (ShapeSubstP ℓ) (ShapeEq ℓ C₁ C₂' eq' o2) s2)))
             (transport-Pos ℓ C₁ C₂' eq' {o2} {s2} p2)))
    eq
    ((J (λ o2' eO' → (s2' : Shape C₁ o2') → (p2' : Pos C₁ {o2'} s2') →
           transport-Pos ℓ C₁ C₁ refl {o1} {subst (Shape C₁) (sym eO') s2'}
             (subst (PosSubstP ℓ C₁) (sym (same-C-PosEq ℓ C₁ eO' s2')) p2')
           ≡ subst (Pos C₁ {o1})
               (sym (shape-subst-lemma ℓ C₁ C₁ refl eO' s2'))
               (subst (PosSubstP ℓ C₁)
                 (sym (same-C-PosEq ℓ C₁ (cong (ObjSubst ℓ C₁ C₁ refl) eO')
                   (subst (ShapeSubstP ℓ) (ShapeEq ℓ C₁ C₁ refl o2') s2')))
                 (transport-Pos ℓ C₁ C₁ refl {o2'} {s2'} p2')))
        eO
        (λ s2' p2' → refl))
     s2 p2)

hom-subst-lemma : ∀ ℓ (C₁ C₂ : Cosmos ℓ) (eq : C₁ ≡ C₂)
                → {a1 a2 : Obj C₁} {b1 b2 : Obj C₁}
                → (eA : a1 ≡ a2) (eB : b1 ≡ b2)
                → (f2 : Hom C₁ a2 b2)
                → transport-Hom ℓ C₁ C₂ eq (subst₂ (Hom C₁) (sym eA) (sym eB) f2)
                ≡ subst₂ (Hom C₂) (cong (ObjSubst ℓ C₁ C₂ eq) (sym eA))
                                 (cong (ObjSubst ℓ C₁ C₂ eq) (sym eB))
                                 (transport-Hom ℓ C₁ C₂ eq f2)
hom-subst-lemma ℓ C₁ C₂ eq {a1} {a2} {b1} {b2} eA eB f2 =
  J (λ C₂' eq' →
       transport-Hom ℓ C₁ C₂' eq' (subst₂ (Hom C₁) (sym eA) (sym eB) f2)
       ≡ subst₂ (Hom C₂') (cong (ObjSubst ℓ C₁ C₂' eq') (sym eA))
                          (cong (ObjSubst ℓ C₁ C₂' eq') (sym eB))
                          (transport-Hom ℓ C₁ C₂' eq' f2))
    eq
    ( ( J (λ a2' eA' → (b2' : Obj C₁) → (eB' : b1 ≡ b2') → (f2' : Hom C₁ a2' b2') →
               transport-Hom ℓ C₁ C₁ refl (subst₂ (Hom C₁) (sym eA') (sym eB') f2')
               ≡ subst₂ (Hom C₁) (cong (ObjSubst ℓ C₁ C₁ refl) (sym eA'))
                                (cong (ObjSubst ℓ C₁ C₁ refl) (sym eB'))
                                (transport-Hom ℓ C₁ C₁ refl f2'))
          eA
          (λ b2' eB' f2' →
             ( J (λ b2'' eB'' → (f2'' : Hom C₁ a1 b2'') →
                   transport-Hom ℓ C₁ C₁ refl (subst₂ (Hom C₁) (sym refl) (sym eB'') f2'')
                   ≡ subst₂ (Hom C₁) (cong (ObjSubst ℓ C₁ C₁ refl) (sym refl))
                                    (cong (ObjSubst ℓ C₁ C₁ refl) (sym eB''))
                                    (transport-Hom ℓ C₁ C₁ refl f2''))
                 eB'
                 (λ f2'' → refl)
             ) f2'
          )
      )
      b2 eB f2
    )

-- Direct equivalences derived from onunfold-eq
--
-- 从 onunfold-eq 导出的直接等价
unfold-subst-shape : ∀ {ℓ} {C : Cosmos ℓ} {o₁ o₂ : Obj C} (eq : o₁ ≡ o₂) (s : Shape C o₁)
                  → unfold C (subst (Shape C) eq s) ≡ unfold C s
unfold-subst-shape refl s = refl

lemma-unfold-subst-shape-sym : ∀ {ℓ} (C : Cosmos ℓ) {o₁ o₂} (eq : o₁ ≡ o₂) (s : Shape C o₁)
  → sym (unfold-subst-shape {C = C} eq s) ≡ subst-unfold C eq s
lemma-unfold-subst-shape-sym C refl s = refl

subst-unfold-eq-conv : ∀ {ℓ} (C : Cosmos ℓ) {o1 o2 : Obj C}
  (eq1 eq2 : o1 ≡ o2) (s : Shape C o1) (eq : eq1 ≡ eq2)
  → trans (subst-unfold C eq1 s) (cong (unfold C) (cong (λ p → subst (Shape C) p s) eq))
  ≡ subst-unfold C eq2 s
subst-unfold-eq-conv C eq1 .eq1 s refl = trans-reflʳ (subst-unfold C eq1 s)

subst-unfold-shape-conv : ∀ {ℓ} (C : Cosmos ℓ) {o1 o2 : Obj C}
  (eq1 eq2 : o1 ≡ o2) (s : Shape C o1) (eq : eq1 ≡ eq2)
  {x : Shape C o2}
  (p1 : x ≡ subst (Shape C) eq1 s)
  (p2 : x ≡ subst (Shape C) eq2 s)
  (r : p2 ≡ trans p1 (cong (λ p → subst (Shape C) p s) eq))
  → trans (subst-unfold C eq1 s) (cong (unfold C) (sym p1))
  ≡ trans (subst-unfold C eq2 s) (cong (unfold C) (sym p2))
subst-unfold-shape-conv C eq1 eq2 s eq {x} p1 p2 r =
  let
    eq-sub : subst (Shape C) eq1 s ≡ subst (Shape C) eq2 s
    eq-sub = cong (λ p → subst (Shape C) p s) eq
    eq-sub-unfold : unfold C (subst (Shape C) eq1 s) ≡ unfold C (subst (Shape C) eq2 s)
    eq-sub-unfold = cong (unfold C) eq-sub
    h : trans (subst-unfold C eq1 s) eq-sub-unfold ≡ subst-unfold C eq2 s
    h = subst-unfold-eq-conv C eq1 eq2 s eq
    step1 : subst-unfold C eq1 s ≡ trans (subst-unfold C eq2 s) (sym eq-sub-unfold)
    step1 =
      begin
        subst-unfold C eq1 s
          ≡⟨ sym (trans-reflʳ (subst-unfold C eq1 s)) ⟩
        trans (subst-unfold C eq1 s) refl
          ≡⟨ cong (trans (subst-unfold C eq1 s)) (sym (trans-symʳ eq-sub-unfold)) ⟩
        trans (subst-unfold C eq1 s) (trans eq-sub-unfold (sym eq-sub-unfold))
          ≡⟨ sym (trans-assoc' (subst-unfold C eq1 s) eq-sub-unfold (sym eq-sub-unfold)) ⟩
        trans (trans (subst-unfold C eq1 s) eq-sub-unfold) (sym eq-sub-unfold)
          ≡⟨ cong (λ e → trans e (sym eq-sub-unfold)) h ⟩
        trans (subst-unfold C eq2 s) (sym eq-sub-unfold)
      ∎
    sym-p2-eq : sym p2 ≡ trans (sym eq-sub) (sym p1)
    sym-p2-eq =
      begin
        sym p2
          ≡⟨ cong sym r ⟩
        sym (trans p1 eq-sub)
          ≡⟨ sym-trans p1 eq-sub ⟩
        trans (sym eq-sub) (sym p1)
      ∎
    cong-unfold-eq : cong (unfold C) (sym p2)
                    ≡ trans (sym eq-sub-unfold) (cong (unfold C) (sym p1))
    cong-unfold-eq =
      begin
        cong (unfold C) (sym p2)
          ≡⟨ cong (cong (unfold C)) sym-p2-eq ⟩
        cong (unfold C) (trans (sym eq-sub) (sym p1))
          ≡⟨ cong-trans (unfold C) (sym eq-sub) (sym p1) ⟩
        trans (cong (unfold C) (sym eq-sub)) (cong (unfold C) (sym p1))
          ≡⟨ cong (λ e → trans e (cong (unfold C) (sym p1))) (cong-sym (unfold C) eq-sub) ⟩
        trans (sym eq-sub-unfold) (cong (unfold C) (sym p1))
      ∎
  in
  begin
    trans (subst-unfold C eq1 s) (cong (unfold C) (sym p1))
      ≡⟨ cong (λ e → trans e (cong (unfold C) (sym p1))) step1 ⟩
    trans (trans (subst-unfold C eq2 s) (sym eq-sub-unfold)) (cong (unfold C) (sym p1))
      ≡⟨ trans-assoc' (subst-unfold C eq2 s) (sym eq-sub-unfold) (cong (unfold C) (sym p1)) ⟩
    trans (subst-unfold C eq2 s) (trans (sym eq-sub-unfold) (cong (unfold C) (sym p1)))
      ≡⟨ cong (trans (subst-unfold C eq2 s)) (sym cong-unfold-eq) ⟩
    trans (subst-unfold C eq2 s) (cong (unfold C) (sym p2))
  ∎

unfold-onShape-subst : ∀ {ℓ} (B C : Cosmos ℓ) (g : B ⇒ℱ C) {o1 o2 : Obj B} (eq : o1 ≡ o2) (s : Shape B o1)
                    → unfold C (onShape g (subst (Shape B) eq s)) ≡ unfold C (onShape g s)
unfold-onShape-subst B C g eq s =
  trans (cong (unfold C) (onShape-subst-comm g eq s))
        (unfold-subst-shape {C = C} (cong (onObj g) eq) (onShape g s))

onunfold-subst-comm : ∀ {ℓ} (B C : Cosmos ℓ) (g : B ⇒ℱ C) {o1 o2 : Obj B} (eq : o1 ≡ o2) (s : Shape B o1)
                    → onunfold g (subst (Shape B) eq s)
                      ≡ subst₂ (λ A C' → A ⇒ℱ C')
                              (sym (unfold-subst-shape {C = B} eq s))
                              (sym (unfold-onShape-subst B C g eq s))
                              (onunfold g s)
onunfold-subst-comm B C g refl s = refl

subst-pos-obj : ∀ {ℓ} {F : Cosmos ℓ} {X Y : Obj F}
  (p : X ≡ Y) {s : Shape F Y} (pos : Pos F s)
  → Pos F (subst (Shape F) (sym p) s)
subst-pos-obj refl pos = pos

subst-hom-obj : ∀ {ℓ} {F : Cosmos ℓ} {X1 X2 Y1 Y2 : Obj F}
  (pX : X1 ≡ X2) (pY : Y1 ≡ Y2) {h : Hom F X2 Y2}
  → Hom F X1 Y1
subst-hom-obj refl refl {h} = h

subst-pos-onPos : ∀ {ℓ} {F G : Cosmos ℓ} (g : F ⇒ℱ G)
  → ∀ {X Y : Obj F} (p : X ≡ Y) (s : Shape F X) (pos : Pos F s)
  → subst (Pos G) (onShape-subst-comm g p s) (onPos g (subst-pos F p s pos))
    ≡ subst-pos G (cong (onObj g) p) (onShape g s) (onPos g pos)
subst-pos-onPos g refl s pos = refl
