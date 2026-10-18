------------------------------------------------------------------------
-- Composition congruence
--
-- All pointwise congruence lemmas and path algebra for composition
-- under ≃⇒ℱ.
--
-- 复合同余
--
-- 复合在 ≃⇒ℱ 下的全部逐点同余引理与路径代数。
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module ALMA.Prototype.Properties.CongBase where

open import ALMA.Prototype.Properties.Composition public

-- Unfold path along a ≃⇒ℱ witness
--
-- 沿 ≃⇒ℱ 见证的 unfold 路径
unfold-onShape-eq : ∀ {ℓ} {F G : Cosmos ℓ} {f1 f2 : F ⇒ℱ G}
  (f-eq : f1 ≃⇒ℱ f2) {A : Obj F} (s : Shape F A)
  → unfold G (onShape f2 s) ≡ unfold G (onShape f1 s)
unfold-onShape-eq {G = G} {f2 = f2} f-eq {A} s =
  trans (subst-unfold G (sym (onObj-eq f-eq A)) (onShape f2 s))
        (cong (unfold G) (sym (onShape-eq f-eq s)))

-- subst₂ with a refl on the target reduces to a single subst
--
-- 目标为 refl 的 subst₂ 退化为单次 subst
subst₂-refl-right : ∀ {ℓ} {A1 A2 B : Cosmos ℓ}
  (pA : A2 ≡ A1) (f : A2 ⇒ℱ B)
  → subst₂ (λ A B' → A ⇒ℱ B') pA refl f ≡ subst (λ A → A ⇒ℱ B) pA f
subst₂-refl-right {B = B} pA f =
  trans (subst₂-⇒ℱ pA refl f)
        (subst-refl-id (λ A → A ⇒ℱ B) (subst (λ M → M ⇒ℱ B) pA f))

-- Composite of subst₂ on the left with subst on the source
--
-- subst₂ 在左侧与源端 subst 的复合
subst₂-comp-eq : ∀ {ℓ} {S M1 M2 T1 T2 : Cosmos ℓ}
  (pM : M2 ≡ M1) (pT : T2 ≡ T1)
  (g : M2 ⇒ℱ T2) (f : S ⇒ℱ M2)
  → subst₂ (λ A B → A ⇒ℱ B) pM pT g ∘⇒ℱ subst (λ C → S ⇒ℱ C) pM f
    ≡ subst (λ C → S ⇒ℱ C) pT (g ∘⇒ℱ f)
subst₂-comp-eq {S = S} pM pT g f =
  trans
    (cong (λ g' → g' ∘⇒ℱ subst (λ C → S ⇒ℱ C) pM f) (subst₂-⇒ℱ pM pT g))
    (subst-∘-comm pM pT g f)

-- Object-level congruence for composition
--
-- 复合的对象层面同余
comp-obj-eq : ∀ {ℓ} (F G H : Cosmos ℓ) (f1 f2 : F ⇒ℱ G) (g1 g2 : G ⇒ℱ H)
  → f1 ≃⇒ℱ f2 → g1 ≃⇒ℱ g2
  → ∀ (X : Obj F) → onObj (g1 ∘⇒ℱ f1) X ≡ onObj (g2 ∘⇒ℱ f2) X
comp-obj-eq F G H f1 f2 g1 g2 f-eq g-eq X =
  trans (cong (onObj g1) (onObj-eq f-eq X)) (onObj-eq g-eq (onObj f2 X))

-- Position-level proof used by the .onPos-eq component of comp-cong
--
-- comp-cong 的 .onPos-eq 分支所用的位置层面证明
pos-proof : ∀ {ℓ} {S' S1 H : Cosmos ℓ} {f1 f2 : S' ⇒ℱ S1}
            (g : S1 ⇒ℱ H) (f-eq : f1 ≃⇒ℱ f2)
            {X : Obj S'} {s : Shape S' X} (pos : Pos S' s) →
            onPos g (onPos f1 pos) ≡
            subst (Pos H) (sym (shape-transport-lemma g f-eq s))
              (subst-pos H (sym (cong (onObj g) (f-eq .onObj-eq X)))
                (onShape g (onShape f2 s))
                (onPos g (onPos f2 pos)))
pos-proof {ℓ} {S'} {S1} {H} {f1} {f2} g f-eq {X} {s} pos = final
  where
    obj-eq   = f-eq .onObj-eq X
    shape-eq = f-eq .onShape-eq s
    s2       = onShape f2 s
    p2       = onPos f2 pos
    inner-pos = subst-pos S1 (sym obj-eq) s2 p2
    total-obj = cong (onObj g) obj-eq
    shape-eq' = onShape-subst-comm g (sym obj-eq) s2
    shape-comp-eq = shape-transport-lemma g f-eq s
    step3-shape : subst (Shape H) (cong (onObj g) (sym obj-eq)) (onShape g s2)
                ≡ subst (Shape H) (sym total-obj) (onShape g s2)
    step3-shape = cong (λ p → subst (Shape H) p (onShape g s2))
                       (cong-sym (onObj g) obj-eq)
    C1 = subst-pos H (cong (onObj g) (sym obj-eq)) (onShape g s2) (onPos g p2)
    C2 = subst-pos H (sym total-obj) (onShape g s2) (onPos g p2)
    step3-C-eq : subst (Pos H) step3-shape C1 ≡ C2
    step3-C-eq = subst-pos-eq H (onPos g p2) (cong-sym (onObj g) obj-eq)
    eq2 : subst (Pos H) shape-eq' (onPos g inner-pos) ≡ C1
    eq2 = subst-pos-onPos g (sym obj-eq) s2 p2
    eq3 : onPos g inner-pos ≡ subst (Pos H) (sym shape-eq') C1
    eq3 =
      begin
        onPos g inner-pos
          ≡⟨ refl ⟩
        subst (Pos H) refl (onPos g inner-pos)
          ≡⟨ cong (λ p → subst (Pos H) p (onPos g inner-pos))
                  (sym (trans-symʳ shape-eq')) ⟩
        subst (Pos H) (trans shape-eq' (sym shape-eq')) (onPos g inner-pos)
          ≡⟨ sym (subst-comp shape-eq' (sym shape-eq')) ⟩
        subst (Pos H) (sym shape-eq') (subst (Pos H) shape-eq' (onPos g inner-pos))
          ≡⟨ cong (subst (Pos H) (sym shape-eq')) eq2 ⟩
        subst (Pos H) (sym shape-eq') C1
      ∎
    step1      = cong (onPos g) (f-eq .onPos-eq pos)
    step2      = onPos-subst-comm g (sym shape-eq) inner-pos
    step3-cast = cong (subst (Pos H) (cong (onShape g) (sym shape-eq))) eq3
    step4-merge = subst-comp (sym shape-eq') (cong (onShape g) (sym shape-eq))
    P = trans (sym shape-eq') (cong (onShape g) (sym shape-eq))
    step5 : onPos g (onPos f1 pos) ≡ subst (Pos H) P C1
    step5 = trans step1 (trans step2 (trans step3-cast step4-merge))
    path-eq : trans step3-shape (sym shape-comp-eq) ≡ P
    path-eq =
      begin
        trans step3-shape (sym shape-comp-eq)
          ≡⟨ cong (trans step3-shape)
                  (sym-trans (cong (onShape g) shape-eq)
                             (trans shape-eq' step3-shape)) ⟩
        trans step3-shape
              (trans (sym (trans shape-eq' step3-shape))
                     (sym (cong (onShape g) shape-eq)))
          ≡⟨ cong (trans step3-shape)
                  (cong (λ q → trans q (sym (cong (onShape g) shape-eq)))
                        (sym-trans shape-eq' step3-shape)) ⟩
        trans step3-shape
              (trans (trans (sym step3-shape) (sym shape-eq'))
                     (sym (cong (onShape g) shape-eq)))
          ≡⟨ sym (trans-assoc step3-shape) ⟩
        trans (trans step3-shape (trans (sym step3-shape) (sym shape-eq')))
              (sym (cong (onShape g) shape-eq))
          ≡⟨ cong (λ q → trans q (sym (cong (onShape g) shape-eq)))
                  (sym (trans-assoc step3-shape)) ⟩
        trans (trans (trans step3-shape (sym step3-shape)) (sym shape-eq'))
              (sym (cong (onShape g) shape-eq))
          ≡⟨ cong (λ q → trans (trans q (sym shape-eq'))
                               (sym (cong (onShape g) shape-eq)))
                  (trans-symʳ step3-shape) ⟩
        trans (trans refl (sym shape-eq'))
              (sym (cong (onShape g) shape-eq))
          ≡⟨ cong (λ q → trans q (sym (cong (onShape g) shape-eq)))
                  (transReflˡ (sym shape-eq')) ⟩
        trans (sym shape-eq') (sym (cong (onShape g) shape-eq))
          ≡⟨ cong (trans (sym shape-eq')) (sym (cong-sym (onShape g) shape-eq)) ⟩
        trans (sym shape-eq') (cong (onShape g) (sym shape-eq))
          ≡⟨ refl ⟩
        P
      ∎
    step6 : subst (Pos H) P C1 ≡ subst (Pos H) (sym shape-comp-eq) C2
    step6 =
      begin
        subst (Pos H) P C1
          ≡⟨ cong (λ p → subst (Pos H) p C1) (sym path-eq) ⟩
        subst (Pos H) (trans step3-shape (sym shape-comp-eq)) C1
            ≡⟨ sym (subst-comp {A = Shape H (onObj g (onObj f1 X))} {B = Pos H} step3-shape (sym shape-comp-eq) {b = C1}) ⟩
        subst (Pos H) (sym shape-comp-eq) (subst (Pos H) step3-shape C1)
          ≡⟨ cong (subst (Pos H) (sym shape-comp-eq)) step3-C-eq ⟩
        subst (Pos H) (sym shape-comp-eq) C2
      ∎
    final = trans step5 step6

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

-- Right-composition congruence: g1 ∘ f ≃⇒ℱ g2 ∘ f
--
-- 右侧复合同余：g1 ∘ f ≃⇒ℱ g2 ∘ f
comp-cong-r-≃⇒ℱ-gen : ∀ {ℓ} {S S' T1 T2 : Cosmos ℓ}
  {g1 : S ⇒ℱ T1} {g2 : S ⇒ℱ T2}
  (p : T2 ≡ T1)
  (g-eq : g1 ≃⇒ℱ subst (λ C → S ⇒ℱ C) p g2)
  (f : S' ⇒ℱ S)
  → g1 ∘⇒ℱ f ≃⇒ℱ subst (λ C → S' ⇒ℱ C) p (g2 ∘⇒ℱ f)
comp-cong-r-≃⇒ℱ-gen refl g-eq f .onObj-eq X   = g-eq .onObj-eq (onObj f X)
comp-cong-r-≃⇒ℱ-gen refl g-eq f .onShape-eq s = g-eq .onShape-eq (onShape f s)
comp-cong-r-≃⇒ℱ-gen refl g-eq f .onPos-eq pos = g-eq .onPos-eq (onPos f pos)
comp-cong-r-≃⇒ℱ-gen refl g-eq f .onHom-eq h   = g-eq .onHom-eq (onHom f h)
comp-cong-r-≃⇒ℱ-gen refl g-eq f .onunfold-eq s =
  comp-cong-r-≃⇒ℱ-gen
    _
    (g-eq .onunfold-eq (onShape f s))
    (onunfold f s)

comp-cong-r-≃⇒ℱ : ∀ {ℓ} {F G H : Cosmos ℓ}
  {g1 g2 : G ⇒ℱ H} (g-eq : g1 ≃⇒ℱ g2)
  (f : F ⇒ℱ G)
  → (g1 ∘⇒ℱ f) ≃⇒ℱ (g2 ∘⇒ℱ f)
comp-cong-r-≃⇒ℱ g-eq f = comp-cong-r-≃⇒ℱ-gen refl g-eq f

-- Shape-level congruence for composition
--
-- 复合的 shape 层面同余
sym-trans-cong-sym : ∀ {ℓ} (F G H : Cosmos ℓ)
                   (f1 f2 : F ⇒ℱ G) (g1 g2 : G ⇒ℱ H)
                   (f-eq : f1 ≃⇒ℱ f2) (g-eq : g1 ≃⇒ℱ g2)
                   (X : Obj F)
                 → trans (sym (g-eq .onObj-eq (onObj f2 X)))
                         (cong (onObj g1) (sym (f-eq .onObj-eq X)))
                 ≡ sym (trans (cong (onObj g1) (f-eq .onObj-eq X))
                              (g-eq .onObj-eq (onObj f2 X)))
sym-trans-cong-sym {ℓ} F G H f1 f2 g1 g2 f-eq g-eq X =
  let eqO-f = f-eq .onObj-eq X
      eqO-g = g-eq .onObj-eq (onObj f2 X)
  in
  begin
    trans (sym eqO-g) (cong (onObj g1) (sym eqO-f))
      ≡⟨ cong (trans (sym eqO-g)) (cong-sym (onObj g1) eqO-f) ⟩
    trans (sym eqO-g) (sym (cong (onObj g1) eqO-f))
      ≡⟨ sym (sym-trans (cong (onObj g1) eqO-f) eqO-g) ⟩
    sym (trans (cong (onObj g1) eqO-f) eqO-g)
  ∎

comp-shape-eq : ∀ {ℓ} (F G H : Cosmos ℓ) (f1 f2 : F ⇒ℱ G) (g1 g2 : G ⇒ℱ H)
  (f-eq : f1 ≃⇒ℱ f2) (g-eq : g1 ≃⇒ℱ g2)
  {A : Obj F} (s : Shape F A)
  → onShape (g1 ∘⇒ℱ f1) s ≡ subst (Shape H) (sym (comp-obj-eq F G H f1 f2 g1 g2 f-eq g-eq A)) (onShape (g2 ∘⇒ℱ f2) s)
comp-shape-eq F G H f1 f2 g1 g2 f-eq g-eq {A} s =
  let
    eqO : onObj f1 A ≡ onObj f2 A
    eqO = onObj-eq f-eq A
    eqS : onShape f1 s ≡ subst (Shape G) (sym eqO) (onShape f2 s)
    eqS = onShape-eq f-eq s
    eqO-total = comp-obj-eq F G H f1 f2 g1 g2 f-eq g-eq A
    final-path-eq : trans (sym (onObj-eq g-eq (onObj f2 A))) (cong (onObj g1) (sym eqO)) ≡ sym eqO-total
    final-path-eq = sym-trans-cong-sym F G H f1 f2 g1 g2 f-eq g-eq A
  in
  begin
    onShape g1 (onShape f1 s)
      ≡⟨ cong (onShape g1) eqS ⟩
    onShape g1 (subst (Shape G) (sym eqO) (onShape f2 s))
      ≡⟨ onShape-subst-comm g1 (sym eqO) (onShape f2 s) ⟩
    subst (Shape H) (cong (onObj g1) (sym eqO)) (onShape g1 (onShape f2 s))
      ≡⟨ cong (subst (Shape H) (cong (onObj g1) (sym eqO))) (onShape-eq g-eq (onShape f2 s)) ⟩
    subst (Shape H) (cong (onObj g1) (sym eqO))
          (subst (Shape H) (sym (onObj-eq g-eq (onObj f2 A))) (onShape g2 (onShape f2 s)))
      ≡⟨ subst-comp (sym (onObj-eq g-eq (onObj f2 A))) (cong (onObj g1) (sym eqO)) ⟩
    subst (Shape H) (trans (sym (onObj-eq g-eq (onObj f2 A))) (cong (onObj g1) (sym eqO)))
          (onShape g2 (onShape f2 s))
      ≡⟨ cong (λ p → subst (Shape H) p (onShape g2 (onShape f2 s))) final-path-eq ⟩
    subst (Shape H) (sym eqO-total) (onShape g2 (onShape f2 s))
  ∎

comp-unfold-path : ∀ {ℓ} (F G H : Cosmos ℓ) (f1 f2 : F ⇒ℱ G) (g1 g2 : G ⇒ℱ H)
  (f-eq : f1 ≃⇒ℱ f2) (g-eq : g1 ≃⇒ℱ g2)
  {A : Obj F} (s : Shape F A)
  → unfold H (onShape (g2 ∘⇒ℱ f2) s) ≡ unfold H (onShape (g1 ∘⇒ℱ f1) s)
comp-unfold-path F G H f1 f2 g1 g2 f-eq g-eq {A} s =
  trans
    (subst-unfold H (sym (comp-obj-eq F G H f1 f2 g1 g2 f-eq g-eq A)) (onShape (g2 ∘⇒ℱ f2) s))
    (cong (unfold H) (sym (comp-shape-eq F G H f1 f2 g1 g2 f-eq g-eq s)))

-- Position-level equality of the substituted evaluations
--
-- 替换后求值的位置层面等式
apply-g-eq-to-substed-pos : (ℓ : Level) (B C : Cosmos ℓ)
                          → (g1 g2 : B ⇒ℱ C)
                          → (O1 O2 : Obj B) (eqO : O1 ≡ O2)
                          → (S1 : Shape B O1) (S2 : Shape B O2) (eqS : S1 ≡ subst (Shape B) (sym eqO) S2)
                          → (P1 : Pos B S1) (P2 : Pos B S2)
                          → (eqP : P1 ≡ subst (Pos B) (sym eqS) (subst-pos B (sym eqO) S2 P2))
                          → onPos g1 P1
                            ≡ subst (Pos C)
                                (trans (sym (onShape-subst-comm g1 (sym eqO) S2)) (cong (onShape g1) (sym eqS)))
                                (subst-pos C
                                  (cong (onObj g1) (sym eqO))
                                  (onShape g1 S2)
                                  (onPos g1 P2))
apply-g-eq-to-substed-pos ℓ B C g1 g2 O1 O2 eqO S1 S2 eqS P1 P2 eqP =
  J (λ O2' eqO' →
       ∀ (S2' : Shape B O2') (eqS' : S1 ≡ subst (Shape B) (sym eqO') S2')
         (P2' : Pos B S2') (eqP' : P1 ≡ subst (Pos B) (sym eqS') (subst-pos B (sym eqO') S2' P2')) →
       onPos g1 P1
       ≡ subst (Pos C)
           (trans (sym (onShape-subst-comm g1 (sym eqO') S2')) (cong (onShape g1) (sym eqS')))
           (subst-pos C (cong (onObj g1) (sym eqO')) (onShape g1 S2') (onPos g1 P2')))
    eqO
    (λ S2' eqS' P2' eqP' →
       let
         goal : onPos g1 P1 ≡ subst (Pos C) (cong (onShape g1) (sym eqS')) (onPos g1 P2')
         goal =
           begin
             onPos g1 P1
           ≡⟨ cong (onPos g1) eqP' ⟩
             onPos g1 (subst (Pos B) (sym eqS') P2')
           ≡⟨ onPos-subst-comm g1 (sym eqS') P2' ⟩
             subst (Pos C) (cong (onShape g1) (sym eqS')) (onPos g1 P2')
           ∎
       in goal)
    S2 eqS P2 eqP

subst-pos-eq-cong : ∀ {ℓ} {C : Cosmos ℓ} {O O' : Obj C} {p q : O ≡ O'}
  → (e : p ≡ q) (S : Shape C O) (x : Pos C S)
  → subst (Pos C) (cong (λ r → subst (Shape C) r S) e) (subst-pos C p S x)
    ≡ subst-pos C q S x
subst-pos-eq-cong refl S x = refl

subst-pos-trans : (ℓ : Level) (C : Cosmos ℓ) {O O' O'' : Obj C}
                → (eqA : O ≡ O') (eqB : O' ≡ O'') (S : Shape C O) (p : Pos C S)
                → subst-pos C eqB (subst (Shape C) eqA S) (subst-pos C eqA S p)
                  ≡ subst (Pos C) (sym (subst-comp eqA eqB {b = S}))
                          (subst-pos C (trans eqA eqB) S p)
subst-pos-trans ℓ C refl refl S p = refl

subst-pos-cong : ∀ {ℓ} (C : Cosmos ℓ) {X Y : Obj C} (eqO : X ≡ Y) {S S' : Shape C X} (eqS : S ≡ S') {p : Pos C S}
               → subst-pos C eqO S' (subst (Pos C) eqS p)
               ≡ subst (Pos C) (cong (subst (Shape C) eqO) eqS) (subst-pos C eqO S p)
subst-pos-cong C eqO refl {p} = refl

subst-pos-apply-g-eq : (ℓ : Level) (B C : Cosmos ℓ)
  (g1 g2 : B ⇒ℱ C) (g-eq : g1 ≃⇒ℱ g2)
  {O1 : Obj B} (O2 : Obj B) (eqO : O1 ≡ O2) (S2 : Shape B O2) (P2 : Pos B S2)
  → subst-pos C (cong (onObj g1) (sym eqO)) (onShape g1 S2) (onPos g1 P2)
    ≡ subst (Pos C)
        (sym
          (trans
            (cong (subst (Shape C) (cong (onObj g1) (sym eqO))) (onShape-eq g-eq S2))
            (subst-comp (sym (onObj-eq g-eq O2)) (cong (onObj g1) (sym eqO)))))
        (subst-pos C
          (trans (sym (onObj-eq g-eq O2)) (cong (onObj g1) (sym eqO)))
          (onShape g2 S2) (onPos g2 P2))
subst-pos-apply-g-eq ℓ B C g1 g2 g-eq {O1} O2 eqO S2 P2 =
  begin
    subst-pos C p-obj (onShape g1 S2) (onPos g1 P2)
      ≡⟨ cong (subst-pos C p-obj (onShape g1 S2)) (onPos-eq g-eq P2) ⟩
    subst-pos C p-obj (onShape g1 S2)
      (subst (Pos C) (sym eqS-g)
        (subst-pos C (sym eqO-g) (onShape g2 S2) (onPos g2 P2)))
      ≡⟨ subst-pos-cong C p-obj (sym eqS-g) ⟩
    subst (Pos C) (cong (subst (Shape C) p-obj) (sym eqS-g))
      (subst-pos C p-obj
        (subst (Shape C) (sym eqO-g) (onShape g2 S2))
        (subst-pos C (sym eqO-g) (onShape g2 S2) (onPos g2 P2)))
      ≡⟨ cong (subst (Pos C) (cong (subst (Shape C) p-obj) (sym eqS-g)))
               (subst-pos-trans ℓ C (sym eqO-g) p-obj (onShape g2 S2) (onPos g2 P2)) ⟩
    subst (Pos C) (cong (subst (Shape C) p-obj) (sym eqS-g))
      (subst (Pos C) (sym (subst-comp (sym eqO-g) p-obj))
        (subst-pos C (trans (sym eqO-g) p-obj) (onShape g2 S2) (onPos g2 P2)))
      ≡⟨ subst-comp (sym (subst-comp (sym eqO-g) p-obj)) (cong (subst (Shape C) p-obj) (sym eqS-g)) ⟩
    subst (Pos C) (trans
      (sym (subst-comp (sym eqO-g) p-obj))
      (cong (subst (Shape C) p-obj) (sym eqS-g)))
      (subst-pos C (trans (sym eqO-g) p-obj) (onShape g2 S2) (onPos g2 P2))
      ≡⟨ cong (λ p → subst (Pos C) p (subst-pos C (trans (sym eqO-g) p-obj) (onShape g2 S2) (onPos g2 P2)))
               path-eq-helper ⟩
    subst (Pos C)
      (sym
        (trans
          (cong (subst (Shape C) p-obj) eqS-g)
          (subst-comp (sym eqO-g) p-obj)))
      (subst-pos C (trans (sym eqO-g) p-obj) (onShape g2 S2) (onPos g2 P2))
  ∎
  where
    p-obj = cong (onObj g1) (sym eqO)
    eqO-g = onObj-eq g-eq O2
    eqS-g = onShape-eq g-eq S2
    cong-sym-helper : ∀ {a b} {X : Set a} {Y : Set b} (f : X → Y) {x y : X} (p : x ≡ y)
                    → cong f (sym p) ≡ sym (cong f p)
    cong-sym-helper f refl = refl
    path-eq-helper : trans (sym (subst-comp (sym eqO-g) p-obj)) (cong (subst (Shape C) p-obj) (sym eqS-g))
                   ≡ sym (trans (cong (subst (Shape C) p-obj) eqS-g) (subst-comp (sym eqO-g) p-obj))
    path-eq-helper =
      begin
        trans (sym p2) (cong f (sym p1))
          ≡⟨ cong (trans (sym p2)) (cong-sym-helper f p1) ⟩
        trans (sym p2) (sym (cong f p1))
          ≡⟨ sym (sym-trans (cong f p1) p2) ⟩
        sym (trans (cong f p1) p2)
      ∎
      where
        p1 = eqS-g
        p2 = subst-comp (sym eqO-g) p-obj
        f = subst (Shape C) p-obj

subst-comp-tgt : ∀ {ℓ} {A B C1 C2 : Cosmos ℓ} (eq : C1 ≡ C2)
                → (f : A ⇒ℱ B) (g : B ⇒ℱ C1)
                → subst (λ C → A ⇒ℱ C) eq (g ∘⇒ℱ f)
                  ≡ subst (λ C → B ⇒ℱ C) eq g ∘⇒ℱ f
subst-comp-tgt refl f g = refl

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

-- Full position-level congruence for composition
--
-- 复合的完整位置层面同余
pos-combine :
  ∀ {ℓ} (F G H : Cosmos ℓ) (f1 f2 : F ⇒ℱ G) (g1 g2 : G ⇒ℱ H)
    (f-eq : f1 ≃⇒ℱ f2) (g-eq : g1 ≃⇒ℱ g2)
    {A : Obj F} {s : Shape F A} (p : Pos F s)
  → onPos (g1 ∘⇒ℱ f1) p ≡
    subst (Pos H) (sym (comp-shape-eq F G H f1 f2 g1 g2 f-eq g-eq s))
      (subst-pos H (sym (comp-obj-eq F G H f1 f2 g1 g2 f-eq g-eq A))
        (onShape (g2 ∘⇒ℱ f2) s)
        (onPos (g2 ∘⇒ℱ f2) p))
pos-combine {ℓ} F G H f1 f2 g1 g2 f-eq g-eq {A} {s} p =
  let
    O1f : Obj G
    O1f = onObj f1 A
    O2f : Obj G
    O2f = onObj f2 A
    eqO-f : O1f ≡ O2f
    eqO-f = onObj-eq f-eq A
    S1f : Shape G O1f
    S1f = onShape f1 s
    S2f : Shape G O2f
    S2f = onShape f2 s
    eqS-f : S1f ≡ subst (Shape G) (sym eqO-f) S2f
    eqS-f = onShape-eq f-eq s
    P1f : Pos G S1f
    P1f = onPos f1 p
    P2f : Pos G S2f
    P2f = onPos f2 p
    eqP-f : P1f ≡ subst (Pos G) (sym eqS-f) (subst-pos G (sym eqO-f) S2f P2f)
    eqP-f = onPos-eq f-eq p
    O1g : Obj H
    O1g = onObj g1 O1f
    O2g : Obj H
    O2g = onObj g2 O2f
    eqO-g : onObj g1 O2f ≡ O2g
    eqO-g = onObj-eq g-eq O2f
    p-obj : onObj g1 O2f ≡ O1g
    p-obj = cong (onObj g1) (sym eqO-f)
    S1g : Shape H O1g
    S1g = onShape g1 S1f
    S2g : Shape H O2g
    S2g = onShape g2 S2f
    P2g : Pos H S2g
    P2g = onPos g2 P2f
    eqO-total : O1g ≡ O2g
    eqO-total = trans (cong (onObj g1) eqO-f) (onObj-eq g-eq O2f)
    eqS-total : S1g ≡ subst (Shape H) (sym eqO-total) S2g
    eqS-total = comp-shape-eq F G H f1 f2 g1 g2 f-eq g-eq s
    final-path-eq : trans (sym eqO-g) p-obj ≡ sym eqO-total
    final-path-eq = sym-trans-cong-sym {ℓ} F G H f1 f2 g1 g2 f-eq g-eq A
    shape-endpoint-eq : subst (Shape H) (trans (sym eqO-g) p-obj) S2g ≡ subst (Shape H) (sym eqO-total) S2g
    shape-endpoint-eq = cong (λ q → subst (Shape H) q S2g) final-path-eq
    step1-shape : S1g ≡ onShape g1 (subst (Shape G) (sym eqO-f) S2f)
    step1-shape = cong (onShape g1) eqS-f
    step2-shape : onShape g1 (subst (Shape G) (sym eqO-f) S2f)
                ≡ subst (Shape H) p-obj (onShape g1 S2f)
    step2-shape = onShape-subst-comm g1 (sym eqO-f) S2f
    step3-shape : subst (Shape H) p-obj (onShape g1 S2f)
                ≡ subst (Shape H) p-obj (subst (Shape H) (sym eqO-g) S2g)
    step3-shape = cong (subst (Shape H) p-obj) (onShape-eq g-eq S2f)
    step4-shape : subst (Shape H) p-obj (subst (Shape H) (sym eqO-g) S2g)
                ≡ subst (Shape H) (trans (sym eqO-g) p-obj) S2g
    step4-shape = subst-comp (sym eqO-g) p-obj {b = S2g}
    path-shape : subst (Shape H) (trans (sym eqO-g) p-obj) S2g ≡ S1g
    path-shape = trans (sym step4-shape)
               (trans (sym step3-shape)
                (trans (sym step2-shape) (sym step1-shape)))
    eqS-unfold : eqS-total ≡ trans step1-shape (trans step2-shape (trans step3-shape (trans step4-shape shape-endpoint-eq)))
    eqS-unfold =
      begin
        eqS-total
          ≡⟨ cong (λ p → trans step1-shape (trans step2-shape (trans step3-shape (trans step4-shape p))))
                  (trans-reflʳ shape-endpoint-eq) ⟩
        trans step1-shape (trans step2-shape (trans step3-shape (trans step4-shape shape-endpoint-eq)))
      ∎
    path-shape-lemma : path-shape ≡ trans shape-endpoint-eq (sym eqS-total)
    path-shape-lemma = sym (begin
      trans shape-endpoint-eq (sym eqS-total)
        ≡⟨ cong (trans shape-endpoint-eq) (cong sym eqS-unfold) ⟩
      trans shape-endpoint-eq (sym (trans step1-shape (trans step2-shape (trans step3-shape (trans step4-shape shape-endpoint-eq)))))
        ≡⟨ cong (trans shape-endpoint-eq)
                (sym-trans step1-shape (trans step2-shape (trans step3-shape (trans step4-shape shape-endpoint-eq)))) ⟩
      trans shape-endpoint-eq (trans (sym (trans step2-shape (trans step3-shape (trans step4-shape shape-endpoint-eq)))) (sym step1-shape))
        ≡⟨ cong (trans shape-endpoint-eq)
                (cong (λ p → trans p (sym step1-shape))
                  (sym-trans step2-shape (trans step3-shape (trans step4-shape shape-endpoint-eq)))) ⟩
      trans shape-endpoint-eq (trans (trans (sym (trans step3-shape (trans step4-shape shape-endpoint-eq))) (sym step2-shape)) (sym step1-shape))
        ≡⟨ cong (trans shape-endpoint-eq)
                (cong (λ p → trans p (sym step1-shape))
                  (cong (λ p → trans p (sym step2-shape))
                    (sym-trans step3-shape (trans step4-shape shape-endpoint-eq)))) ⟩
      trans shape-endpoint-eq (trans (trans (trans (sym (trans step4-shape shape-endpoint-eq)) (sym step3-shape)) (sym step2-shape)) (sym step1-shape))
        ≡⟨ cong (trans shape-endpoint-eq)
                (cong (λ p → trans p (sym step1-shape))
                  (cong (λ p → trans p (sym step2-shape))
                    (cong (λ p → trans p (sym step3-shape))
                      (sym-trans step4-shape shape-endpoint-eq)))) ⟩
      trans shape-endpoint-eq (trans (trans (trans (trans (sym shape-endpoint-eq) (sym step4-shape)) (sym step3-shape)) (sym step2-shape)) (sym step1-shape))
        ≡⟨ sym (trans-assoc shape-endpoint-eq) ⟩
      trans (trans shape-endpoint-eq (trans (trans (trans (sym shape-endpoint-eq) (sym step4-shape)) (sym step3-shape)) (sym step2-shape))) (sym step1-shape)
        ≡⟨ cong (λ p → trans p (sym step1-shape)) (sym (trans-assoc shape-endpoint-eq)) ⟩
      trans (trans (trans shape-endpoint-eq (trans (trans (sym shape-endpoint-eq) (sym step4-shape)) (sym step3-shape))) (sym step2-shape)) (sym step1-shape)
        ≡⟨ cong (λ p → trans (trans p (sym step2-shape)) (sym step1-shape)) (sym (trans-assoc shape-endpoint-eq)) ⟩
      trans (trans (trans (trans shape-endpoint-eq (trans (sym shape-endpoint-eq) (sym step4-shape))) (sym step3-shape)) (sym step2-shape)) (sym step1-shape)
        ≡⟨ cong (λ p → trans (trans (trans p (sym step3-shape)) (sym step2-shape)) (sym step1-shape)) (sym (trans-assoc shape-endpoint-eq)) ⟩
      trans (trans (trans (trans (trans shape-endpoint-eq (sym shape-endpoint-eq)) (sym step4-shape)) (sym step3-shape)) (sym step2-shape)) (sym step1-shape)
        ≡⟨ cong (λ p → trans (trans (trans (trans p (sym step4-shape)) (sym step3-shape)) (sym step2-shape)) (sym step1-shape)) (trans-symʳ shape-endpoint-eq) ⟩
      trans (trans (trans (trans refl (sym step4-shape)) (sym step3-shape)) (sym step2-shape)) (sym step1-shape)
        ≡⟨ refl ⟩
      trans (trans (trans (sym step4-shape) (sym step3-shape)) (sym step2-shape)) (sym step1-shape)
        ≡⟨ trans-assoc (trans (sym step4-shape) (sym step3-shape)) ⟩
      trans (trans (sym step4-shape) (sym step3-shape)) (trans (sym step2-shape) (sym step1-shape))
        ≡⟨ trans-assoc (sym step4-shape) ⟩
      trans (sym step4-shape) (trans (sym step3-shape) (trans (sym step2-shape) (sym step1-shape)))
        ≡⟨ refl ⟩
      path-shape
      ∎)
    pos1 : Pos G S1f
    pos1 = subst (Pos G) (sym eqS-f) (subst-pos G (sym eqO-f) S2f P2f)
    pos2 : Pos H (subst (Shape H) p-obj (onShape g1 S2f))
    pos2 = subst-pos H p-obj (onShape g1 S2f) (onPos g1 P2f)
    pos3 : Pos H (subst (Shape H) p-obj (onShape g1 S2f))
    pos3 = subst-pos H p-obj (onShape g1 S2f)
             (subst (Pos H) (sym (onShape-eq g-eq S2f))
               (subst-pos H (sym eqO-g) S2g P2g))
    path4-lemma : cong (onShape g1) (sym eqS-f) ≡ sym step1-shape
    path4-lemma = sym (sym-cong eqS-f)
    path3-lemma : trans (sym step4-shape) (cong (subst (Shape H) p-obj) (sym (onShape-eq g-eq S2f)))
                ≡ trans (sym step4-shape) (sym step3-shape)
    path3-lemma = cong₂ trans refl (sym (sym-cong (onShape-eq g-eq S2f)))
    path3-total : trans
                    (trans (sym step4-shape)
                      (cong (subst (Shape H) p-obj)
                        (sym (onShape-eq g-eq S2f))))
                    (trans (sym step2-shape) (sym step1-shape))
                  ≡ path-shape
    path3-total =
      begin
        trans
          (trans (sym step4-shape)
            (cong (subst (Shape H) p-obj) (sym (onShape-eq g-eq S2f))))
          (trans (sym step2-shape) (sym step1-shape))
          ≡⟨ cong (λ p → trans p (trans (sym step2-shape) (sym step1-shape))) path3-lemma ⟩
        trans (trans (sym step4-shape) (sym step3-shape)) (trans (sym step2-shape) (sym step1-shape))
          ≡⟨ trans-assoc (sym step4-shape) ⟩
        trans (sym step4-shape) (trans (sym step3-shape) (trans (sym step2-shape) (sym step1-shape)))
          ≡⟨ refl ⟩
        path-shape
      ∎
    apply-g-result : onPos g1 P1f
                   ≡ subst (Pos H) (trans (sym step2-shape) (cong (onShape g1) (sym eqS-f))) pos2
    apply-g-result = apply-g-eq-to-substed-pos ℓ G H g1 g2 O1f O2f eqO-f S1f S2f eqS-f P1f P2f eqP-f
    pos5-lemma : onPos g1 pos1
               ≡ subst (Pos H) (trans (sym step2-shape) (cong (onShape g1) (sym eqS-f))) pos2
    pos5-lemma = trans (cong (onPos g1) (sym eqP-f)) apply-g-result
  in
  begin
    onPos g1 P1f
      ≡⟨ cong (onPos g1) eqP-f ⟩
    onPos g1 pos1
      ≡⟨ pos5-lemma ⟩
    subst (Pos H) (trans (sym step2-shape) (cong (onShape g1) (sym eqS-f))) pos2
      ≡⟨ cong (λ q → subst (Pos H) q pos2) (cong₂ trans refl path4-lemma) ⟩
    subst (Pos H) (trans (sym step2-shape) (sym step1-shape)) pos2
      ≡⟨ cong (subst (Pos H) (trans (sym step2-shape) (sym step1-shape)))
              (cong (subst-pos H p-obj (onShape g1 S2f)) (onPos-eq g-eq P2f)) ⟩
    subst (Pos H) (trans (sym step2-shape) (sym step1-shape)) pos3
      ≡⟨ cong (subst (Pos H) (trans (sym step2-shape) (sym step1-shape)))
              (subst-pos-cong H p-obj
                {S = subst (Shape H) (sym eqO-g) S2g}
                {S' = onShape g1 S2f}
                (sym (onShape-eq g-eq S2f))
                {p = subst-pos H (sym eqO-g) S2g P2g}) ⟩
    subst (Pos H) (trans (sym step2-shape) (sym step1-shape))
      (subst (Pos H) (cong (subst (Shape H) p-obj) (sym (onShape-eq g-eq S2f)))
        (subst-pos H p-obj (subst (Shape H) (sym eqO-g) S2g)
          (subst-pos H (sym eqO-g) S2g P2g)))
      ≡⟨ cong (subst (Pos H) (trans (sym step2-shape) (sym step1-shape)))
              (cong (subst (Pos H) (cong (subst (Shape H) p-obj) (sym (onShape-eq g-eq S2f))))
                    (subst-pos-trans ℓ H (sym eqO-g) p-obj S2g P2g)) ⟩
    subst (Pos H) (trans (sym step2-shape) (sym step1-shape))
      (subst (Pos H) (cong (subst (Shape H) p-obj) (sym (onShape-eq g-eq S2f)))
        (subst (Pos H) (sym step4-shape)
          (subst-pos H (trans (sym eqO-g) p-obj) S2g P2g)))
      ≡⟨ cong (subst (Pos H) (trans (sym step2-shape) (sym step1-shape)))
              (subst-subst {P = Pos H} (sym step4-shape)
                            {y≡z = cong (subst (Shape H) p-obj) (sym (onShape-eq g-eq S2f))}) ⟩
    subst (Pos H) (trans (sym step2-shape) (sym step1-shape))
      (subst (Pos H)
        (trans (sym step4-shape)
          (cong (subst (Shape H) p-obj) (sym (onShape-eq g-eq S2f))))
        (subst-pos H (trans (sym eqO-g) p-obj) S2g P2g))
      ≡⟨ subst-subst {P = Pos H}
                      (trans (sym step4-shape)
                        (cong (subst (Shape H) p-obj) (sym (onShape-eq g-eq S2f))))
                      {y≡z = trans (sym step2-shape) (sym step1-shape)} ⟩
    subst (Pos H)
      (trans
        (trans (sym step4-shape)
          (cong (subst (Shape H) p-obj) (sym (onShape-eq g-eq S2f))))
        (trans (sym step2-shape) (sym step1-shape)))
      (subst-pos H (trans (sym eqO-g) p-obj) S2g P2g)
      ≡⟨ cong (λ q → subst (Pos H) q
               (subst-pos H (trans (sym eqO-g) p-obj) S2g P2g))
             path3-total ⟩
    subst (Pos H) path-shape
      (subst-pos H (trans (sym eqO-g) p-obj) S2g P2g)
      ≡⟨ cong (λ q → subst (Pos H) q
               (subst-pos H (trans (sym eqO-g) p-obj) S2g P2g))
             path-shape-lemma ⟩
    subst (Pos H) (trans shape-endpoint-eq (sym eqS-total))
      (subst-pos H (trans (sym eqO-g) p-obj) S2g P2g)
      ≡⟨ sym (subst-subst {P = Pos H} shape-endpoint-eq {y≡z = sym eqS-total}) ⟩
    subst (Pos H) (sym eqS-total)
      (subst (Pos H) shape-endpoint-eq
        (subst-pos H (trans (sym eqO-g) p-obj) S2g P2g))
      ≡⟨ cong (subst (Pos H) (sym eqS-total))
              (subst-pos-eq-cong final-path-eq S2g P2g) ⟩
    subst (Pos H) (sym eqS-total)
      (subst-pos H (sym eqO-total) S2g P2g)
  ∎
