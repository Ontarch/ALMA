------------------------------------------------------------------------
-- Path composition and composition congruence infrastructure
--
-- Composition of unfold paths, shape transport along an equality of
-- morphisms, and the basic ≃⇒ℱ-congruence for composition up to
-- source/target substitution. This module provides the low-level path
-- algebra consumed by Cong.
--
-- 路径复合与复合同余的基础设施
--
-- unfold 路径的复合、沿态射等式的 shape 运输，以及复合在源/目标替换下
-- 的 ≃⇒ℱ-同余基础。本模块提供 Cong 所消费的底层路径代数。
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module Wellspring.Properties.Composition where

open import Wellspring.Properties.Equiv public

-- Composition equations and paths
--
-- 复合等式与路径
combine-hom-eq : ∀ {ℓ} {F G : Cosmos ℓ} {m₁ m₂ m₃ : F ⇒ℱ G}
               → (h1 : m₁ ≃⇒ℱ m₂) (h2 : m₂ ≃⇒ℱ m₃) {A B : Obj F} (f : Hom F A B)
               → onHom m₁ f ≡ subst₂ (Hom G) (sym (trans (onObj-eq h1 A) (onObj-eq h2 A)))
                                      (sym (trans (onObj-eq h1 B) (onObj-eq h2 B)))
                                      (onHom m₃ f)
combine-hom-eq {G = G} h1 h2 {A} {B} f =
  let
    pO1A = onObj-eq h1 A
    pO1B = onObj-eq h1 B
    pO2A = onObj-eq h2 A
    pO2B = onObj-eq h2 B
    eqH1 = onHom-eq h1 f
    eqH2 = onHom-eq h2 f
  in
  trans eqH1 (trans (cong (subst₂ (Hom G) (sym pO1A) (sym pO1B)) eqH2)
                    (subst₂-sym-comp pO1A pO1B pO2A pO2B))

trans-unfold-path : ∀ {ℓ} (G : Cosmos ℓ) (X Y Z : Obj G)
                    (eqO1 : X ≡ Y) (eqO2 : Y ≡ Z)
                    (s1 : Shape G X) (s2 : Shape G Y) (s3 : Shape G Z)
                    (eqS1 : s1 ≡ subst (Shape G) (sym eqO1) s2)
                    (eqS2 : s2 ≡ subst (Shape G) (sym eqO2) s3) →
                    trans (trans (subst-unfold G (sym eqO2) s3) (cong (unfold G) (sym eqS2)))
                          (trans (subst-unfold G (sym eqO1) s2) (cong (unfold G) (sym eqS1)))
                    ≡ trans (subst-unfold G (sym (trans eqO1 eqO2)) s3)
                            (cong (unfold G)
                              (sym (trans eqS1
                                     (trans (cong (subst (Shape G) (sym eqO1)) eqS2)
                                            (trans (subst-comp (sym eqO2) (sym eqO1))
                                                   (cong (λ e → subst (Shape G) e s3)
                                                         (sym (sym-trans eqO1 eqO2))))))))
trans-unfold-path G X .X .X refl refl s1 .s1 .s1 refl refl = refl

-- Additional properties under MorphLift
--
-- MorphLift 下的额外性质
actP-subst-shape : ∀ {ℓ} (F : Cosmos ℓ) {B C : Obj F} {s1 s2 : Shape F B}
                  → (g : Hom F B C) (eq : s1 ≡ s2)
                  → (p : Pos F (actS F g s1))
                  → actP F g s2 (subst (Pos F) (cong (actS F g) eq) p)
                    ≡ subst (Pos F) eq (actP F g s1 p)
actP-subst-shape F g refl p = refl

-- Composition of substitutions on source and target
--
-- 源与目标上替换的复合
subst-∘-comm : ∀ {ℓ : Level} {S M1 M2 T1 T2 : Cosmos ℓ}
  (eqM : M2 ≡ M1) (eqT : T2 ≡ T1)
  (g : M2 ⇒ℱ T2) (f : S ⇒ℱ M2)
  → subst (λ D → M1 ⇒ℱ D) eqT (subst (λ M → M ⇒ℱ T2) eqM g)
    ∘⇒ℱ
    subst (λ D → S ⇒ℱ D) eqM f
    ≡
    subst (λ D → S ⇒ℱ D) eqT (g ∘⇒ℱ f)
subst-∘-comm refl refl g f = refl

transport-onunfold : ∀ {ℓ} {A B : Cosmos ℓ} {m₁ m₂ : A ⇒ℱ B} (m-eq : m₁ ≃⇒ℱ m₂)
                     (X : Obj A) (s : Shape A X)
                   → subst (λ C → unfold A s ⇒ℱ C)
                           (sym (trans (subst-unfold B (sym (onObj-eq m-eq X)) (onShape m₂ s))
                                       (cong (unfold B) (sym (onShape-eq m-eq s)))))
                           (onunfold m₁ s)
                     ≃⇒ℱ
                     onunfold m₂ s
transport-onunfold {ℓ} {A} {B} {m₁} {m₂} m-eq X s =
  let
    P : Cosmos ℓ → Set (lsuc ℓ)
    P C = unfold A s ⇒ℱ C
    thePath : unfold B (onShape m₂ s) ≡ unfold B (onShape m₁ s)
    thePath = trans (subst-unfold B (sym (onObj-eq m-eq X)) (onShape m₂ s))
                    (cong (unfold B) (sym (onShape-eq m-eq s)))
    eq0 : onunfold m₁ s ≃⇒ℱ subst P thePath (onunfold m₂ s)
    eq0 = onunfold-eq m-eq s
    eq1 : subst P (sym thePath) (onunfold m₁ s)
        ≃⇒ℱ subst P (sym thePath) (subst P thePath (onunfold m₂ s))
    eq1 = subst-≃⇒ℱ ℓ (unfold A s) _ _ (sym thePath) eq0
    subst-cancel : subst P (sym thePath) (subst P thePath (onunfold m₂ s))
                 ≡ onunfold m₂ s
    subst-cancel =
      begin
        subst P (sym thePath) (subst P thePath (onunfold m₂ s))
      ≡⟨ subst-comp thePath (sym thePath) ⟩
        subst P (trans thePath (sym thePath)) (onunfold m₂ s)
      ≡⟨ cong (λ e → subst P e (onunfold m₂ s)) (trans-symʳ thePath) ⟩
        subst P refl (onunfold m₂ s)
      ≡⟨ subst-refl-id P (onunfold m₂ s) ⟩
        onunfold m₂ s
      ∎
  in subst (λ n → subst P (sym thePath) (onunfold m₁ s) ≃⇒ℱ n) subst-cancel eq1

subst-≃⇒ℱ-path : ∀ {ℓ} {F C D : Cosmos ℓ} {m : F ⇒ℱ C}
                 {p q : C ≡ D}
               → p ≡ q
               → subst (λ X → F ⇒ℱ X) p m ≃⇒ℱ subst (λ X → F ⇒ℱ X) q m
subst-≃⇒ℱ-path refl = refl-≃⇒ℱ

subst-comp-⇒ℱ-tgt : ∀ {ℓ} {S M T1 T2 : Cosmos ℓ} (p : T1 ≡ T2)
  → (f : S ⇒ℱ M) (g : M ⇒ℱ T1)
  → subst (λ Y → M ⇒ℱ Y) p g ∘⇒ℱ f
    ≃⇒ℱ
    subst (λ Y → S ⇒ℱ Y) p (g ∘⇒ℱ f)
subst-comp-⇒ℱ-tgt refl f g = refl-≃⇒ℱ

subst-right-cancel-≃⇒ℱ : ∀ {ℓ} {F : Cosmos ℓ} {C D : Cosmos ℓ} (eq : C ≡ D)
                       → {m : F ⇒ℱ C} {n : F ⇒ℱ D}
                       → m ≃⇒ℱ subst (λ X → F ⇒ℱ X) (sym eq) n
                       → subst (λ X → F ⇒ℱ X) eq m ≃⇒ℱ n
subst-right-cancel-≃⇒ℱ refl h = h

subst₂-≃⇒ℱ : ∀ {ℓ} {A1 A2 B1 B2 : Cosmos ℓ} (pA : A1 ≡ A2) (pB : B1 ≡ B2)
  → {f g : A1 ⇒ℱ B1} → f ≃⇒ℱ g
  → subst₂ (λ X Y → X ⇒ℱ Y) pA pB f ≃⇒ℱ subst₂ (λ X Y → X ⇒ℱ Y) pA pB g
subst₂-≃⇒ℱ refl refl h = h

onunfold-subst-shape : ∀ {ℓ} {G H : Cosmos ℓ} {g : G ⇒ℱ H}
                       {O : Obj G} {s1 s2 : Shape G O}
                     → (p : s1 ≡ s2)
                     → onunfold g s1
                       ≃⇒ℱ subst₂ (λ A B → A ⇒ℱ B)
                                   (sym (cong (unfold G) p))
                                   (sym (cong (unfold H) (cong (onShape g) p)))
                                   (onunfold g s2)
onunfold-subst-shape refl = refl-≃⇒ℱ

subst₂-⇒ℱ : ∀ {ℓ} {A1 A2 B1 B2 : Cosmos ℓ} (pA : A2 ≡ A1) (pB : B2 ≡ B1) (g : A2 ⇒ℱ B2)
  → subst₂ (λ A B → A ⇒ℱ B) pA pB g
    ≡ subst (λ D → A1 ⇒ℱ D) pB (subst (λ M → M ⇒ℱ B2) pA g)
subst₂-⇒ℱ refl refl g = refl

onunfold-shape-cong : ∀ {ℓ} {F G : Cosmos ℓ} {m : F ⇒ℱ G} {A} {s1 s2 : Shape F A}
  → (eq : s1 ≡ s2)
  → subst₂ (λ X Y → X ⇒ℱ Y) (cong (unfold F) eq) (cong (unfold G) (cong (onShape m) eq)) (onunfold m s1)
    ≡ onunfold m s2
onunfold-shape-cong refl = refl

subst₂-subst-right : ∀ {ℓ} {A2 A1 B2 B1 B3 : Cosmos ℓ}
  (x : A2 ⇒ℱ B2) (pA : A2 ≡ A1) (pB1 : B2 ≡ B1) (pB2 : B1 ≡ B3)
  → subst (λ B → A1 ⇒ℱ B) pB2 (subst₂ (λ A B → A ⇒ℱ B) pA pB1 x)
    ≡ subst₂ (λ A B → A ⇒ℱ B) pA (trans pB1 pB2) x
subst₂-subst-right x refl refl refl = refl

shape-transport-lemma : ∀ {ℓ} {F G H : Cosmos ℓ}
  {f1 f2 : F ⇒ℱ G} (g1 : G ⇒ℱ H)
  (f-eq : f1 ≃⇒ℱ f2)
  {A : Obj F} (s : Shape F A)
  → onShape g1 (onShape f1 s)
  ≡ subst (Shape H) (sym (cong (onObj g1) (onObj-eq f-eq A))) (onShape g1 (onShape f2 s))
shape-transport-lemma {ℓ} {F} {G} {H} {f1} {f2} g1 f-eq {A} s =
  trans
    (cong (onShape g1) (onShape-eq f-eq s))
    (trans
      (onShape-subst-comm g1 (sym (onObj-eq f-eq A)) (onShape f2 s))
      (cong (λ p → subst (Shape H) p (onShape g1 (onShape f2 s)))
            (cong-sym (onObj g1) (onObj-eq f-eq A))))

unfold-onShape-sym-lemma : ∀ {ℓ} {G H : Cosmos ℓ} (g : G ⇒ℱ H)
  {o₁ o₂ : Obj G} (eq : o₁ ≡ o₂) (s : Shape G o₁)
  → sym (unfold-onShape-subst G H g eq s)
  ≡ trans (subst-unfold H (cong (onObj g) eq) (onShape g s))
          (cong (unfold H) (sym (onShape-subst-comm g eq s)))
unfold-onShape-sym-lemma {ℓ} {G} {H} g {o₁} {o₂} eq s =
  let
    mid-shape : Shape H (onObj g o₂)
    mid-shape = subst (Shape H) (cong (onObj g) eq) (onShape g s)
    p : unfold H (onShape g (subst (Shape G) eq s)) ≡ unfold H mid-shape
    p = cong (unfold H) (onShape-subst-comm g eq s)
    q : unfold H mid-shape ≡ unfold H (onShape g s)
    q = unfold-subst-shape {C = H} (cong (onObj g) eq) (onShape g s)
    def : unfold-onShape-subst G H g eq s ≡ trans p q
    def = refl
  in
  begin
    sym (unfold-onShape-subst G H g eq s)
      ≡⟨ cong sym def ⟩
    sym (trans p q)
      ≡⟨ sym-trans p q ⟩
    trans (sym q) (sym p)
      ≡⟨ cong (λ e → trans e (sym p))
              (lemma-unfold-subst-shape-sym H (cong (onObj g) eq) (onShape g s)) ⟩
    trans (subst-unfold H (cong (onObj g) eq) (onShape g s)) (sym p)
      ≡⟨ cong (trans (subst-unfold H (cong (onObj g) eq) (onShape g s)))
              (sym-cong {f = unfold H} (onShape-subst-comm g eq s)) ⟩
    trans (subst-unfold H (cong (onObj g) eq) (onShape g s))
          (cong (unfold H) (sym (onShape-subst-comm g eq s)))
  ∎

path-eq-target-lemma : ∀ {ℓ} {F G H : Cosmos ℓ}
  {f1 f2 : F ⇒ℱ G} (g1 : G ⇒ℱ H)
  (f-eq : f1 ≃⇒ℱ f2)
  {A : Obj F} (s : Shape F A)
  → trans (sym (unfold-onShape-subst G H g1 (sym (onObj-eq f-eq A)) (onShape f2 s)))
          (sym (cong (unfold H) (cong (onShape g1) (onShape-eq f-eq s))))
  ≡ trans (subst-unfold H (sym (cong (onObj g1) (onObj-eq f-eq A))) (onShape g1 (onShape f2 s)))
          (cong (unfold H) (sym (shape-transport-lemma {F = F} {G = G} {H = H} g1 f-eq s)))
path-eq-target-lemma {ℓ} {F} {G} {H} {f1} {f2} g1 f-eq {A} s =
  let
    eqO = onObj-eq f-eq A
    eqS = onShape-eq f-eq s
    s2 = onShape f2 s
    mid-shape = onShape g1 s2
    a : onShape g1 (onShape f1 s) ≡ onShape g1 (subst (Shape G) (sym eqO) s2)
    a = cong (onShape g1) eqS
    b : onShape g1 (subst (Shape G) (sym eqO) s2) ≡ subst (Shape H) (cong (onObj g1) (sym eqO)) mid-shape
    b = onShape-subst-comm {G = G} {H = H} g1 (sym eqO) s2
    p1 : onShape g1 (onShape f1 s) ≡ subst (Shape H) (cong (onObj g1) (sym eqO)) mid-shape
    p1 = trans a b
    eq-p : cong (onObj g1) (sym eqO) ≡ sym (cong (onObj g1) eqO)
    eq-p = cong-sym (onObj g1) eqO
    eq-sub : subst (Shape H) (cong (onObj g1) (sym eqO)) mid-shape
           ≡ subst (Shape H) (sym (cong (onObj g1) eqO)) mid-shape
    eq-sub = cong (λ p → subst (Shape H) p mid-shape) eq-p
    shape-conv : shape-transport-lemma {F = F} {G = G} {H = H} g1 f-eq s ≡ trans p1 eq-sub
    shape-conv = sym (trans-assoc' a b eq-sub)
    p2 : onShape g1 (onShape f1 s) ≡ subst (Shape H) (sym (cong (onObj g1) eqO)) mid-shape
    p2 = shape-transport-lemma {F = F} {G = G} {H = H} g1 f-eq s
    p2' = sym b
    p3' = sym a
    shape-merge' : trans p2' p3' ≡ sym p1
    shape-merge' = sym (sym-trans a b)
    cong-unfold-merge : cong (unfold H) (trans p2' p3')
                      ≡ trans (cong (unfold H) p2') (cong (unfold H) p3')
    cong-unfold-merge = cong-trans (unfold H) p2' p3'
    h = unfold-onShape-subst G H g1 (sym eqO) s2
    q = unfold-subst-shape {C = H} (cong (onObj g1) (sym eqO)) mid-shape
    h-def : h ≡ trans (cong (unfold H) b) q
    h-def = refl
    sym-h-step1 : sym h ≡ trans (sym q) (sym (cong (unfold H) b))
    sym-h-step1 =
      begin
        sym h
          ≡⟨ cong sym h-def ⟩
        sym (trans (cong (unfold H) b) q)
          ≡⟨ sym-trans (cong (unfold H) b) q ⟩
        trans (sym q) (sym (cong (unfold H) b))
      ∎
    sym-q-eq : sym q ≡ subst-unfold H (cong (onObj g1) (sym eqO)) mid-shape
    sym-q-eq = lemma-unfold-subst-shape-sym H (cong (onObj g1) (sym eqO)) mid-shape
    sym-cong-b : sym (cong (unfold H) b) ≡ cong (unfold H) (sym b)
    sym-cong-b = sym (cong-sym (unfold H) b)
    sym-cong-a : sym (cong (unfold H) a) ≡ cong (unfold H) (sym a)
    sym-cong-a = sym (cong-sym (unfold H) a)
    sym-h-final : sym h ≡ trans (subst-unfold H (cong (onObj g1) (sym eqO)) mid-shape)
                               (cong (unfold H) (sym b))
    sym-h-final =
      begin
        sym h
          ≡⟨ sym-h-step1 ⟩
        trans (sym q) (sym (cong (unfold H) b))
          ≡⟨ cong₂ trans sym-q-eq sym-cong-b ⟩
        trans (subst-unfold H (cong (onObj g1) (sym eqO)) mid-shape)
              (cong (unfold H) (sym b))
      ∎
  in
  begin
    trans (sym h) (sym (cong (unfold H) a))
      ≡⟨ cong (λ e → trans e (sym (cong (unfold H) a))) sym-h-final ⟩
    trans (trans (subst-unfold H (cong (onObj g1) (sym eqO)) mid-shape)
                 (cong (unfold H) (sym b)))
          (sym (cong (unfold H) a))
      ≡⟨ trans-assoc' (subst-unfold H (cong (onObj g1) (sym eqO)) mid-shape)
                      (cong (unfold H) (sym b))
                      (sym (cong (unfold H) a)) ⟩
    trans (subst-unfold H (cong (onObj g1) (sym eqO)) mid-shape)
          (trans (cong (unfold H) (sym b)) (sym (cong (unfold H) a)))
      ≡⟨ cong (trans (subst-unfold H (cong (onObj g1) (sym eqO)) mid-shape))
              (cong (trans (cong (unfold H) (sym b))) sym-cong-a) ⟩
    trans (subst-unfold H (cong (onObj g1) (sym eqO)) mid-shape)
          (trans (cong (unfold H) (sym b)) (cong (unfold H) (sym a)))
      ≡⟨ cong (trans (subst-unfold H (cong (onObj g1) (sym eqO)) mid-shape))
              (sym cong-unfold-merge) ⟩
    trans (subst-unfold H (cong (onObj g1) (sym eqO)) mid-shape)
          (cong (unfold H) (trans p2' p3'))
      ≡⟨ cong (trans (subst-unfold H (cong (onObj g1) (sym eqO)) mid-shape))
              (cong (cong (unfold H)) shape-merge') ⟩
    trans (subst-unfold H (cong (onObj g1) (sym eqO)) mid-shape)
          (cong (unfold H) (sym p1))
      ≡⟨ subst-unfold-shape-conv H
           (cong (onObj g1) (sym eqO))
           (sym (cong (onObj g1) eqO))
           mid-shape eq-p
           p1 p2 shape-conv ⟩
    trans (subst-unfold H (sym (cong (onObj g1) eqO)) mid-shape)
          (cong (unfold H) (sym p2))
  ∎

path-eq-source-lemma : ∀ {ℓ} {G : Cosmos ℓ} {o₁ o₂ : Obj G}
  (eqO : o₁ ≡ o₂) {s₁ : Shape G o₁} {s₂ : Shape G o₂}
  (eqS : s₁ ≡ subst (Shape G) (sym eqO) s₂)
  → trans (sym (unfold-subst-shape {C = G} (sym eqO) s₂))
          (sym (cong (unfold G) eqS))
  ≡ trans (subst-unfold G (sym eqO) s₂)
          (cong (unfold G) (sym eqS))
path-eq-source-lemma {ℓ} {G} {o₁} {o₂} eqO {s₁} {s₂} eqS =
  cong₂ trans
    (lemma-unfold-subst-shape-sym G (sym eqO) s₂)
    (sym-cong {f = unfold G {o₁}} eqS)

subst₂-comp-≃⇒ℱ : ∀ {ℓ} {S M1 M2 T1 T2 : Cosmos ℓ}
  (eqM : M2 ≡ M1) (eqT : T2 ≡ T1)
  (g : M2 ⇒ℱ T2) (f : S ⇒ℱ M2)
  → (subst₂ (λ A B → A ⇒ℱ B) eqM eqT g) ∘⇒ℱ (subst (λ C → S ⇒ℱ C) eqM f)
    ≃⇒ℱ
    subst (λ C → S ⇒ℱ C) eqT (g ∘⇒ℱ f)
subst₂-comp-≃⇒ℱ {S = S} eqM eqT g f =
  ≡→≃⇒ℱ $
    trans
      (cong (λ g' → g' ∘⇒ℱ subst (λ C → S ⇒ℱ C) eqM f) (subst₂-⇒ℱ eqM eqT g))
      (subst-∘-comm eqM eqT g f)

onObj-cong-≡ : ∀ {ℓ} {S T : Cosmos ℓ} {h1 h2 : S ⇒ℱ T} {X : Obj S}
             → h1 ≡ h2 → onObj h1 X ≡ onObj h2 X
onObj-cong-≡ refl = refl

subst-∘⇒ℱ-comm : ∀ {ℓ} {S M T1 T2 : Cosmos ℓ}
                → (p : T2 ≡ T1)
                → (f : S ⇒ℱ M)
                → (g : M ⇒ℱ T2)
                → subst (λ C → M ⇒ℱ C) p g ∘⇒ℱ f
                  ≡ subst (λ C → S ⇒ℱ C) p (g ∘⇒ℱ f)
subst-∘⇒ℱ-comm refl f g = refl

subst₂-trans : ∀ {a b p} {A : Set a} {B : Set b} {P : A → B → Set p}
  {x1 x2 x3 : A} {y1 y2 y3 : B}
  (p1 : x1 ≡ x2) (p2 : x2 ≡ x3)
  (q1 : y1 ≡ y2) (q2 : y2 ≡ y3)
  (z : P x1 y1)
  → subst₂ P p2 q2 (subst₂ P p1 q1 z) ≡ subst₂ P (trans p1 p2) (trans q1 q2) z
subst₂-trans refl p2 refl q2 z = refl

onHom-subst-comm : ∀ {ℓ} {G H : Cosmos ℓ} (g : G ⇒ℱ H)
                   (X Y X' Y' : Obj G) (p : X ≡ X') (q : Y ≡ Y') (f : Hom G X Y)
                 → onHom g (subst₂ (Hom G) p q f)
                   ≡ subst₂ (Hom H) (cong (onObj g) p) (cong (onObj g) q) (onHom g f)
onHom-subst-comm g X Y .X .Y refl refl f = refl

subst₂-tgt-merge : ∀ {ℓ} {A A' B B' B'' : Cosmos ℓ}
                   (p : A ≡ A') (r : B ≡ B') (q : B' ≡ B'') (f : A ⇒ℱ B)
                 → subst₂ _⇒ℱ_ p q (subst (λ C → A ⇒ℱ C) r f)
                   ≡ subst₂ _⇒ℱ_ p (trans r q) f
subst₂-tgt-merge refl refl refl f = refl

comp-standard-unfold-path : ∀ {ℓ} {C : Cosmos ℓ} {o1 o2 o3 : Obj C}
  (p12 : o1 ≡ o2) {s1 : Shape C o1} {s2 : Shape C o2} (eq12 : s2 ≡ subst (Shape C) p12 s1)
  (p23 : o2 ≡ o3) {s3 : Shape C o3} (eq23 : s3 ≡ subst (Shape C) p23 s2)
  → trans
      (trans (subst-unfold C p12 s1) (cong (unfold C) (sym eq12)))
      (trans (subst-unfold C p23 s2) (cong (unfold C) (sym eq23)))
    ≡ trans
      (subst-unfold C (trans p12 p23) s1)
      (cong (unfold C) (sym (trans eq23 (trans (cong (subst (Shape C) p23) eq12) (subst-comp p12 p23 {b = s1})))))
comp-standard-unfold-path refl refl refl refl = refl
