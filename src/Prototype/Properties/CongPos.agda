------------------------------------------------------------------------
-- Composition congruence: position layer
--
-- The position-level congruence lemmas, including the pointwise
-- pos-proof and the full pos-combine used by comp-cong-≃⇒ℱ.
--
-- 复合同余：位置层
--
-- 位置层面同余引理，包括逐点 pos-proof 与 comp-cong-≃⇒ℱ 所用的
-- 完整 pos-combine。
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module Prototype.Properties.CongPos where

open import Prototype.Properties.CongPaths public

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
