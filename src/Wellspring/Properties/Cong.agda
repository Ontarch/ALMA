------------------------------------------------------------------------
-- Composition congruence for ≃⇒ℱ: the top-level assembly
--
-- The full congruence theorem comp-cong-≃⇒ℱ, assembled from the
-- pointwise lemmas in CongPaths, CongPos, and CongHom. The
-- .onunfold-eq component uses the auxiliary comp-cong-≃⇒ℱ-aux, whose
-- recursive call sits directly at the copattern clause head and is
-- accepted by the guardedness checker.
--
-- 复合在 ≃⇒ℱ 下的同余：顶层组装
--
-- 完整的同余定理 comp-cong-≃⇒ℱ，由 CongPaths、CongPos、CongHom 中的
-- 逐点引理组装。其 .onunfold-eq 分支通过辅助函数 comp-cong-≃⇒ℱ-aux
-- 实现，递归调用直接位于 copattern 子句头部，被 guardedness 检查器接受。
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module Wellspring.Properties.Cong where

open import Wellspring.Properties.CongHom public

-- Auxiliary: composition congruence with an explicit cast on the RHS.
-- Pattern-matches on rhs-eq = refl so the recursive call in onunfold-eq
-- is directly at the clause head (termination checker can see it).
--
-- 辅助函数：带显式右端强制转换的复合同余。对 rhs-eq = refl 进行模式匹配，
-- 使 onunfold-eq 中的递归调用直接位于子句头部（终止检查器可识别）。
comp-cong-≃⇒ℱ-aux : ∀ {ℓ} (F G H : Cosmos ℓ) (f1 f2 : F ⇒ℱ G) (g1 g2 : G ⇒ℱ H)
                  → f1 ≃⇒ℱ f2 → g1 ≃⇒ℱ g2
                  → {b : F ⇒ℱ H} (rhs-eq : (g2 ∘⇒ℱ f2) ≡ b)
                  → (g1 ∘⇒ℱ f1) ≃⇒ℱ b
comp-cong-≃⇒ℱ-aux {ℓ} F G H f1 f2 g1 g2 f-eq g-eq refl .onObj-eq X =
  comp-obj-eq F G H f1 f2 g1 g2 f-eq g-eq X
comp-cong-≃⇒ℱ-aux {ℓ} F G H f1 f2 g1 g2 f-eq g-eq refl .onShape-eq {A} s =
  comp-shape-eq F G H f1 f2 g1 g2 f-eq g-eq s
comp-cong-≃⇒ℱ-aux F G H f1 f2 g1 g2 f-eq g-eq refl .onPos-eq {A} {s} p =
  pos-combine F G H f1 f2 g1 g2 f-eq g-eq p
comp-cong-≃⇒ℱ-aux {ℓ} F G H f1 f2 g1 g2 f-eq g-eq refl .onHom-eq {A} {B} h =
  hom-combine F G H f1 f2 g1 g2 f-eq g-eq h
comp-cong-≃⇒ℱ-aux {ℓ} F G H f1 f2 g1 g2 f-eq g-eq refl .onunfold-eq {A} s =
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
    -- path-g-total ≡ comp-unfold-path ... s (the goal path)
    --
    -- path-g-total 与目标路径 comp-unfold-path 相等
    path-eq : path-g-total ≡ comp-unfold-path F G H f1 f2 g1 g2 f-eq g-eq s
    path-eq = comp-unfold-path≡trans F G H f1 f2 g1 g2 f-eq g-eq s
    -- The recursive call's RHS ≡ goal's RHS (at the unfolded level)
    --
    -- 递归调用的右端 ≡ 目标右端（在展开层）
    rhs-eq' : (subst₂ (λ A B → A ⇒ℱ B) path-f-G path-g-total (onunfold g2 t2))
             ∘⇒ℱ
             (subst (λ C → unfold F s ⇒ℱ C) path-f-G (onunfold f2 s))
           ≡ subst (λ C → unfold F s ⇒ℱ C) (comp-unfold-path F G H f1 f2 g1 g2 f-eq g-eq s)
                   (onunfold (g2 ∘⇒ℱ f2) s)
    rhs-eq' = trans comp-subst-comm
               (cong (λ p → subst (λ C → unfold F s ⇒ℱ C) p (onunfold (g2 ∘⇒ℱ f2) s)) path-eq)
  in
    comp-cong-≃⇒ℱ-aux (unfold F s) (unfold G t1) (unfold H s1-g)
      (onunfold f1 s)
      (subst (λ C → unfold F s ⇒ℱ C) path-f-G (onunfold f2 s))
      (onunfold g1 t1)
      (subst₂ (λ A B → A ⇒ℱ B) path-f-G path-g-total (onunfold g2 t2))
      f-bisim g-bisim-final
      rhs-eq'

-- Full composition congruence: calls the auxiliary with refl.
--
-- 完整的复合同余：以 refl 调用辅助函数。
comp-cong-≃⇒ℱ : ∀ {ℓ} (F G H : Cosmos ℓ) (f1 f2 : F ⇒ℱ G) (g1 g2 : G ⇒ℱ H)
              → f1 ≃⇒ℱ f2 → g1 ≃⇒ℱ g2
              → (g1 ∘⇒ℱ f1) ≃⇒ℱ (g2 ∘⇒ℱ f2)
comp-cong-≃⇒ℱ F G H f1 f2 g1 g2 f-eq g-eq =
  comp-cong-≃⇒ℱ-aux F G H f1 f2 g1 g2 f-eq g-eq refl
