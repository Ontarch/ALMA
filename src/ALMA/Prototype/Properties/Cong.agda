------------------------------------------------------------------------
-- Composition congruence for ≃⇒ℱ: the top-level assembly
--
-- 复合在 ≃⇒ℱ 下的同余：顶层组装
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module ALMA.Prototype.Properties.Cong where

open import ALMA.Prototype.Properties.CongBase public

-- Full composition congruence: the .onunfold-eq component is a hole
--
-- 完整的复合同余：.onunfold-eq 分支是洞
comp-cong-≃⇒ℱ : ∀ {ℓ} (F G H : Cosmos ℓ) (f1 f2 : F ⇒ℱ G) (g1 g2 : G ⇒ℱ H)
              → f1 ≃⇒ℱ f2 → g1 ≃⇒ℱ g2
              → (g1 ∘⇒ℱ f1) ≃⇒ℱ (g2 ∘⇒ℱ f2)
comp-cong-≃⇒ℱ {ℓ} F G H f1 f2 g1 g2 f-eq g-eq .onObj-eq X =
  comp-obj-eq F G H f1 f2 g1 g2 f-eq g-eq X
comp-cong-≃⇒ℱ {ℓ} F G H f1 f2 g1 g2 f-eq g-eq .onShape-eq {A} s =
  comp-shape-eq F G H f1 f2 g1 g2 f-eq g-eq s
comp-cong-≃⇒ℱ F G H f1 f2 g1 g2 f-eq g-eq .onPos-eq {A} {s} p =
  pos-combine F G H f1 f2 g1 g2 f-eq g-eq p
comp-cong-≃⇒ℱ {ℓ} F G H f1 f2 g1 g2 f-eq g-eq .onHom-eq {A} {B} h =
  hom-combine F G H f1 f2 g1 g2 f-eq g-eq h
comp-cong-≃⇒ℱ {ℓ} F G H f1 f2 g1 g2 f-eq g-eq .onunfold-eq {A} s =
  let
    eqO-f : onObj f1 A ≡ onObj f2 A
    eqO-f = onObj-eq f-eq A
    eqS-f : onShape f1 s ≡ subst (Shape G) (sym eqO-f) (onShape f2 s)
    eqS-f = onShape-eq f-eq s
    t1 : Shape G (onObj f1 A)
    t1 = onShape f1 s
    t2 : Shape G (onObj f2 A)
    t2 = onShape f2 s
    O1-f : Obj G
    O1-f = onObj f1 A
    O2-f : Obj G
    O2-f = onObj f2 A
    eqO-g : onObj g1 O2-f ≡ onObj g2 O2-f
    eqO-g = onObj-eq g-eq O2-f
    eqS-g : onShape g1 t2 ≡ subst (Shape H) (sym eqO-g) (onShape g2 t2)
    eqS-g = onShape-eq g-eq t2
    s1-g : Shape H (onObj g1 O1-f)
    s1-g = onShape g1 t1
    s_mid-g : Shape H (onObj g1 O2-f)
    s_mid-g = onShape g1 t2
    s3-g : Shape H (onObj g2 O2-f)
    s3-g = onShape g2 t2
    eqO-g1 : onObj g1 O1-f ≡ onObj g1 O2-f
    eqO-g1 = cong (onObj g1) eqO-f
    shape-transport : s1-g ≡ subst (Shape H) (sym eqO-g1) s_mid-g
    shape-transport = shape-transport-lemma {F = F} {G = G} {H = H} {f1 = f1} {f2 = f2} g1 f-eq s
    path-f-G : unfold G t2 ≡ unfold G t1
    path-f-G = unfold-onShape-eq f-eq s
    path-f-H : unfold H s_mid-g ≡ unfold H s1-g
    path-f-H = trans (subst-unfold H (sym eqO-g1) s_mid-g)
                     (cong (unfold H) (sym shape-transport))
    path-g-H : unfold H s3-g ≡ unfold H s_mid-g
    path-g-H = unfold-onShape-eq g-eq t2
    path-g-total : unfold H s3-g ≡ unfold H s1-g
    path-g-total = trans path-g-H path-f-H
    P-f : Cosmos ℓ → Set (lsuc ℓ)
    P-f C = unfold F s ⇒ℱ C
    P-g : Cosmos ℓ → Set (lsuc ℓ)
    P-g C = unfold G t2 ⇒ℱ C
    Q-g : Cosmos ℓ → Set (lsuc ℓ)
    Q-g C = C ⇒ℱ unfold H s_mid-g
    f-bisim : onunfold f1 s ≃⇒ℱ subst (λ C → unfold F s ⇒ℱ C) path-f-G (onunfold f2 s)
    f-bisim = onunfold-eq f-eq s
    g-bisim : onunfold g1 t2 ≃⇒ℱ subst (λ C → unfold G t2 ⇒ℱ C) path-g-H (onunfold g2 t2)
    g-bisim = onunfold-eq g-eq t2
    g-bisim-trans-raw : subst₂ (λ A B → A ⇒ℱ B) path-f-G refl (onunfold g1 t2)
      ≃⇒ℱ subst₂ (λ A B → A ⇒ℱ B) path-f-G refl (subst P-g path-g-H (onunfold g2 t2))
    g-bisim-trans-raw = subst₂-≃⇒ℱ path-f-G refl g-bisim
    merge-eq : ∀ (f : unfold G t2 ⇒ℱ unfold H s_mid-g) →
      subst₂ (λ A B → A ⇒ℱ B) path-f-G refl f
      ≡ subst Q-g path-f-G f
    merge-eq f = subst₂-refl-right path-f-G f
    g-bisim-trans : subst Q-g path-f-G (onunfold g1 t2)
      ≃⇒ℱ subst Q-g path-f-G (subst P-g path-g-H (onunfold g2 t2))
    g-bisim-trans = ≡-left-≃⇒ℱ (sym (merge-eq (onunfold g1 t2))) $
      ≡-right-≃⇒ℱ g-bisim-trans-raw (merge-eq (subst P-g path-g-H (onunfold g2 t2)))
    eqSub-g : subst Q-g path-f-G (subst P-g path-g-H (onunfold g2 t2))
      ≡ subst₂ (λ A B → A ⇒ℱ B) path-f-G path-g-H (onunfold g2 t2)
    eqSub-g = subst-target-source≡subst₂ path-f-G path-g-H (onunfold g2 t2)
    g-bisim-comb : subst Q-g path-f-G (onunfold g1 t2)
                  ≃⇒ℱ
                  subst₂ (λ A B → A ⇒ℱ B) path-f-G path-g-H (onunfold g2 t2)
    g-bisim-comb = ≡-right-≃⇒ℱ g-bisim-trans eqSub-g
    left-merge : subst (λ C → unfold G t1 ⇒ℱ C) path-f-H (subst Q-g path-f-G (onunfold g1 t2))
               ≡ subst₂ (λ A B → A ⇒ℱ B) path-f-G path-f-H (onunfold g1 t2)
    left-merge = subst-source-target≡subst₂ path-f-G path-f-H (onunfold g1 t2)
    right-merge : subst (λ C → unfold G t1 ⇒ℱ C) path-f-H (subst₂ (λ A B → A ⇒ℱ B) path-f-G path-g-H (onunfold g2 t2))
                ≡ subst₂ (λ A B → A ⇒ℱ B) path-f-G (trans path-g-H path-f-H) (onunfold g2 t2)
    right-merge = subst₂-subst-right (onunfold g2 t2) path-f-G path-g-H path-f-H
    g-left-transport : onunfold g1 t1 ≃⇒ℱ subst₂ (λ A B → A ⇒ℱ B) path-f-G path-f-H (onunfold g1 t2)
    g-left-transport =
      let
        step1 : onunfold g1 t1 ≃⇒ℱ
                subst₂ (λ A B → A ⇒ℱ B)
                      (sym (cong (unfold G) eqS-f))
                      (sym (cong (unfold H) (cong (onShape g1) eqS-f)))
                      (onunfold g1 (subst (Shape G) (sym eqO-f) t2))
        step1 = onunfold-subst-shape {G = G} {H = H} {g = g1} eqS-f
        step2 : onunfold g1 (subst (Shape G) (sym eqO-f) t2) ≡
                subst₂ (λ A C' → A ⇒ℱ C')
                      (sym (unfold-subst-shape {C = G} (sym eqO-f) t2))
                      (sym (unfold-onShape-subst G H g1 (sym eqO-f) t2))
                      (onunfold g1 t2)
        step2 = onunfold-subst-comm G H g1 (sym eqO-f) t2
        step3 : subst₂ _⇒ℱ_
                    (sym (cong (unfold G) eqS-f))
                    (sym (cong (unfold H) (cong (onShape g1) eqS-f)))
                    (onunfold g1 (subst (Shape G) (sym eqO-f) t2))
              ≡
                subst₂ _⇒ℱ_
                    (sym (cong (unfold G) eqS-f))
                    (sym (cong (unfold H) (cong (onShape g1) eqS-f)))
                    (subst₂ _⇒ℱ_
                          (sym (unfold-subst-shape {C = G} (sym eqO-f) t2))
                          (sym (unfold-onShape-subst G H g1 (sym eqO-f) t2))
                          (onunfold g1 t2))
        step3 = cong (λ z → subst₂ _⇒ℱ_
                              (sym (cong (unfold G) eqS-f))
                              (sym (cong (unfold H) (cong (onShape g1) eqS-f)))
                              z)
                    step2
        eqA1 : unfold G (subst (Shape G) (sym eqO-f) t2) ≡ unfold G t2
        eqA1 = unfold-subst-shape {C = G} {o₁ = onObj f2 A} {o₂ = onObj f1 A} (sym eqO-f) t2
        eqA2 : unfold G t2 ≡ unfold G t1
        eqA2 = trans (sym (unfold-subst-shape {C = G} {o₁ = onObj f2 A} {o₂ = onObj f1 A} (sym eqO-f) t2))
                    (sym (cong (unfold G) eqS-f))
        eqB1 : unfold H (onShape g1 (subst (Shape G) (sym eqO-f) t2)) ≡ unfold H (onShape g1 t2)
        eqB1 = unfold-onShape-subst G H g1 (sym eqO-f) t2
        eqB2 : unfold H (onShape g1 t2) ≡ unfold H (onShape g1 t1)
        eqB2 = trans (sym eqB1) (sym (cong (unfold H) (cong (onShape g1) eqS-f)))
        step4 : subst₂ _⇒ℱ_
                      (sym (cong (unfold G) eqS-f))
                      (sym (cong (unfold H) (cong (onShape g1) eqS-f)))
                      (subst₂ _⇒ℱ_ (sym eqA1) (sym eqB1) (onunfold g1 t2))
                ≡ subst₂ _⇒ℱ_ eqA2 eqB2 (onunfold g1 t2)
        step4 =
          let
            p1 = sym eqA1
            p2 = sym (cong (unfold G) eqS-f)
            q1 = sym eqB1
            q2 = sym (cong (unfold H) (cong (onShape g1) eqS-f))
            r  = onunfold g1 t2
            base : subst₂ _⇒ℱ_ p2 q2 (subst₂ _⇒ℱ_ p1 q1 r)
                 ≡ subst₂ _⇒ℱ_ (trans p1 p2) (trans q1 q2) r
            base = subst₂-comp {A = Cosmos ℓ} {B = Cosmos ℓ} {C = _⇒ℱ_}
                              p1 p2 q1 q2
            tr1 : trans p1 p2 ≡ eqA2
            tr1 = refl
            tr2 : trans q1 q2 ≡ eqB2
            tr2 = refl
            replace : subst₂ _⇒ℱ_ (trans p1 p2) (trans q1 q2) r ≡ subst₂ _⇒ℱ_ eqA2 eqB2 r
            replace = trans (cong (λ p → subst₂ _⇒ℱ_ p (trans q1 q2) r) tr1)
                            (cong (λ q → subst₂ _⇒ℱ_ eqA2 q r) tr2)
          in trans base replace
        path-eq-G : trans (sym (unfold-subst-shape {C = G} (sym eqO-f) t2))
                          (sym (cong (unfold G) eqS-f))
                    ≡ path-f-G
        path-eq-G = path-eq-source-lemma {G = G} {o₁ = O1-f} {o₂ = O2-f} eqO-f {s₁ = t1} {s₂ = t2} eqS-f
        path-eq-H : trans (sym (unfold-onShape-subst G H g1 (sym eqO-f) t2))
                          (sym (cong (unfold H) (cong (onShape g1) eqS-f)))
                    ≡ path-f-H
        path-eq-H = path-eq-target-lemma {F = F} {G = G} {H = H} {f1 = f1} {f2 = f2} g1 f-eq s
        step5 : subst₂ (λ A B → A ⇒ℱ B)
                      (trans (sym (unfold-subst-shape {C = G} (sym eqO-f) t2))
                              (sym (cong (unfold G) eqS-f)))
                      (trans (sym (unfold-onShape-subst G H g1 (sym eqO-f) t2))
                              (sym (cong (unfold H) (cong (onShape g1) eqS-f))))
                      (onunfold g1 t2)
                ≡ subst₂ (λ A B → A ⇒ℱ B) path-f-G path-f-H (onunfold g1 t2)
        step5 = cong₂ (λ p q → subst₂ (λ A B → A ⇒ℱ B) p q (onunfold g1 t2)) path-eq-G path-eq-H
        step6 : subst₂ (λ A B → A ⇒ℱ B)
                      (sym (cong (unfold G) eqS-f))
                      (sym (cong (unfold H) (cong (onShape g1) eqS-f)))
                      (onunfold g1 (subst (Shape G) (sym eqO-f) t2))
                ≃⇒ℱ
                subst₂ (λ A B → A ⇒ℱ B)
                      path-f-G
                      path-f-H
                      (onunfold g1 t2)
        step6 = ≡→≃⇒ℱ (trans step3 (trans step4 step5))
      in
      trans-≃⇒ℱ step1 step6
    g-right-combine : subst₂ (λ A B → A ⇒ℱ B) path-f-G path-f-H (onunfold g1 t2)
                    ≃⇒ℱ
                    subst₂ (λ A B → A ⇒ℱ B) path-f-G path-g-total (onunfold g2 t2)
    g-right-combine =
      let
        eq1 = sym (subst-source-target≡subst₂ path-f-G path-f-H (onunfold g1 t2))
        eq2 = subst₂-subst-right (onunfold g2 t2) path-f-G path-g-H path-f-H
        mid = subst-≃⇒ℱ ℓ (unfold G t1) _ _ path-f-H g-bisim-comb
      in
      ≡-left-≃⇒ℱ eq1 (≡-right-≃⇒ℱ mid eq2)
    g-bisim-final : onunfold g1 t1 ≃⇒ℱ subst₂ (λ A B → A ⇒ℱ B) path-f-G path-g-total (onunfold g2 t2)
    g-bisim-final = trans-≃⇒ℱ g-left-transport g-right-combine
    comp-subst-comm : (subst₂ (λ A B → A ⇒ℱ B) path-f-G path-g-total (onunfold g2 t2)) ∘⇒ℱ (subst (λ C → unfold F s ⇒ℱ C) path-f-G (onunfold f2 s))
                    ≡ subst (λ C → unfold F s ⇒ℱ C) path-g-total (onunfold g2 t2 ∘⇒ℱ onunfold f2 s)
    comp-subst-comm = subst₂-comp-eq path-f-G path-g-total (onunfold g2 t2) (onunfold f2 s)
  in
    {!   !}
