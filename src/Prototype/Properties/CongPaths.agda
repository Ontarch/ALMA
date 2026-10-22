------------------------------------------------------------------------
-- Composition congruence: path algebra and object/shape layer
--
-- The unfold-path algebra for composition under ≃⇒ℱ, object- and
-- shape-level congruence, right-composition congruence, and the square
-- lemmas used to relate comp-unfold-path to the two-step unfold path.
--
-- 复合同余：路径代数与对象/形状层
--
-- 复合在 ≃⇒ℱ 下的 unfold-路径代数、对象与形状层面同余、
-- 右复合同余，以及把 comp-unfold-path 与两步展开路径联系起来的
-- 方块引理。
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module Prototype.Properties.CongPaths where

open import Prototype.Properties.Composition public

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

-- Generic square lemma: transporting u along a 2-path then applying eq
-- equals applying eq then transporting.
--
-- 通用方块引理：沿 2-路径传输 u 再应用 eq 等于先应用 eq 再传输。
subst-square : ∀ {a b} {A : Set a} {B : A → Set b} {x y : A} {p q : x ≡ y}
  (cs : p ≡ q) {u v : B x} (eq : u ≡ v)
  → trans (cong (λ z → subst B z u) cs) (cong (subst B q) eq)
    ≡ trans (cong (subst B p) eq) (cong (λ z → subst B z v) cs)
subst-square refl eq = sym (trans-reflʳ (cong (subst _ _) eq))

-- Generic square lemma for subst-comp
--
-- 用于 subst-comp 的通用方块引理
subst-square2 : ∀ {a b} {A : Set a} {B : A → Set b} {x y z : A}
  {p q : y ≡ x} (cs : p ≡ q) (r : z ≡ y) {w : B z}
  → trans (cong (λ t → subst B t (subst B r w)) cs) (subst-comp r q)
    ≡ trans (subst-comp r p) (cong (λ t → subst B t w) (cong (trans r) cs))
subst-square2 refl r = sym (trans-reflʳ (subst-comp r _))

-- Equality between the two-step unfold path and comp-unfold-path
--
-- 两步展开路径与 comp-unfold-path 之间的等式
comp-unfold-path≡trans : ∀ {ℓ} (F G H : Cosmos ℓ) (f1 f2 : F ⇒ℱ G) (g1 g2 : G ⇒ℱ H)
  (f-eq : f1 ≃⇒ℱ f2) (g-eq : g1 ≃⇒ℱ g2) {A : Obj F} (s : Shape F A)
  → let eqO-f = onObj-eq f-eq A
        eqS-f = onShape-eq f-eq s
        t1 = onShape f1 s
        t2 = onShape f2 s
        O1-f = onObj f1 A
        O2-f = onObj f2 A
        eqO-g = onObj-eq g-eq O2-f
        eqS-g = onShape-eq g-eq t2
        s1-g = onShape g1 t1
        s_mid-g = onShape g1 t2
        s3-g = onShape g2 t2
        eqO-g1 = cong (onObj g1) eqO-f
        shape-transport = shape-transport-lemma g1 f-eq s
        path-f-H = trans (subst-unfold H (sym eqO-g1) s_mid-g) (cong (unfold H) (sym shape-transport))
        path-g-H = unfold-onShape-eq g-eq t2
    in trans path-g-H path-f-H ≡ comp-unfold-path F G H f1 f2 g1 g2 f-eq g-eq s
comp-unfold-path≡trans F G H f1 f2 g1 g2 f-eq g-eq {A} s =
  let
    eqO-f = onObj-eq f-eq A
    eqS-f = onShape-eq f-eq s
    t1 = onShape f1 s
    t2 = onShape f2 s
    O1-f = onObj f1 A
    O2-f = onObj f2 A
    eqO-g = onObj-eq g-eq O2-f
    eqS-g = onShape-eq g-eq t2
    s1-g = onShape g1 t1
    s_mid-g = onShape g1 t2
    s3-g = onShape g2 t2
    eqO-g1 = cong (onObj g1) eqO-f
    shape-transport = shape-transport-lemma g1 f-eq s
    path-f-H = trans (subst-unfold H (sym eqO-g1) s_mid-g) (cong (unfold H) (sym shape-transport))
    path-g-H = unfold-onShape-eq g-eq t2
    -- The combined shape produced by trans-unfold-path
    --
    -- trans-unfold-path 产生的组合形状
    combined-shape : s1-g ≡ subst (Shape H) (sym (trans eqO-g1 eqO-g)) s3-g
    combined-shape =
      trans shape-transport
        (trans (cong (subst (Shape H) (sym eqO-g1)) eqS-g)
               (trans (subst-comp (sym eqO-g) (sym eqO-g1))
                      (cong (λ e → subst (Shape H) e s3-g) (sym (sym-trans eqO-g1 eqO-g)))))
    -- Collapse via trans-unfold-path
    --
    -- 通过 trans-unfold-path 合并
    step1 : trans path-g-H path-f-H
          ≡ trans (subst-unfold H (sym (trans eqO-g1 eqO-g)) s3-g)
                  (cong (unfold H) (sym combined-shape))
    step1 = trans-unfold-path H (onObj g1 O1-f) (onObj g1 O2-f) (onObj g2 O2-f)
              eqO-g1 eqO-g s1-g s_mid-g s3-g shape-transport eqS-g
    -- Prove combined-shape ≡ comp-shape-eq ... s
    --
    -- 证明组合形状等于 comp-shape-eq
    cs : cong (onObj g1) (sym eqO-f) ≡ sym eqO-g1
    cs = cong-sym (onObj g1) eqO-f
    p1 = cong (onShape g1) eqS-f
    p2 = onShape-subst-comm g1 (sym eqO-f) t2
    q = cong (λ p → subst (Shape H) p s_mid-g) cs
    r3 = cong (subst (Shape H) (sym eqO-g1)) eqS-g
    r4 = subst-comp (sym eqO-g) (sym eqO-g1)
    r5 = cong (λ e → subst (Shape H) e s3-g) (sym (sym-trans eqO-g1 eqO-g))
    p3 = cong (subst (Shape H) (cong (onObj g1) (sym eqO-f))) eqS-g
    p4 = subst-comp (sym eqO-g) (cong (onObj g1) (sym eqO-f))
    final-path-eq = sym-trans-cong-sym F G H f1 f2 g1 g2 f-eq g-eq A
    p5 = cong (λ p → subst (Shape H) p s3-g) final-path-eq
    q' = cong (λ p → subst (Shape H) p (subst (Shape H) (sym eqO-g) s3-g)) cs
    q'' = cong (λ p → subst (Shape H) p s3-g) (cong (trans (sym eqO-g)) cs)
    -- Square 1: transporting s_mid-g then applying eqS-g equals applying eqS-g then transporting
    --
    -- 方块 1：先传输 s_mid-g 再应用 eqS-g 等于先应用 eqS-g 再传输
    square1 : trans q r3 ≡ trans p3 q'
    square1 = subst-square cs eqS-g
    square2 : trans q' r4 ≡ trans p4 q''
    square2 = subst-square2 cs (sym eqO-g)
    -- Step 3: q'' ∘ r5 = p5  (by definition of final-path-eq)
    --
    -- 第三步：q'' ∘ r5 = p5（由 final-path-eq 的定义）
    step3 : trans q'' r5 ≡ p5
    step3 =
      let
        s2 = sym (sym-trans eqO-g1 eqO-g)
        pre = cong (trans (sym eqO-g)) cs
        f : (p : onObj g2 O2-f ≡ onObj g1 O1-f) → Shape H (onObj g1 O1-f)
        f p = subst (Shape H) p s3-g
        a = trans (sym eqO-g) (cong (onObj g1) (sym eqO-f))
        c = sym (trans eqO-g1 eqO-g)
        cf : (x : a ≡ c) → f a ≡ f c
        cf x = cong f x
        path-eq : trans pre s2 ≡ trans pre (trans s2 refl)
        path-eq = cong (λ (x : trans (sym eqO-g) (sym eqO-g1) ≡ sym (trans eqO-g1 eqO-g)) → trans pre x)
                       (sym (trans-reflʳ s2))
        cong-f-cong : cf (trans pre s2) ≡ cf (trans pre (trans s2 refl))
        cong-f-cong = cong cf path-eq
      in
      begin
        trans q'' r5
          ≡⟨ sym (cong-trans f pre s2) ⟩
        cf (trans pre s2)
          ≡⟨ cong-f-cong ⟩
        cf (trans pre (trans s2 refl))
          ≡⟨ refl ⟩
        p5
      ∎
    -- Inner equality: trans q (trans r3 (trans r4 r5)) ≡ trans p3 (trans p4 (trans p5 refl))
    --
    -- 内层等式
    inner-eq : trans q (trans r3 (trans r4 r5)) ≡ trans p3 (trans p4 (trans p5 refl))
    inner-eq =
      begin
        trans q (trans r3 (trans r4 r5))
          ≡⟨ sym (trans-assoc q) ⟩
        trans (trans q r3) (trans r4 r5)
          ≡⟨ cong (λ x → trans x (trans r4 r5)) square1 ⟩
        trans (trans p3 q') (trans r4 r5)
          ≡⟨ trans-assoc p3 ⟩
        trans p3 (trans q' (trans r4 r5))
          ≡⟨ cong (trans p3) (sym (trans-assoc q')) ⟩
        trans p3 (trans (trans q' r4) r5)
          ≡⟨ cong (λ x → trans p3 (trans x r5)) square2 ⟩
        trans p3 (trans (trans p4 q'') r5)
          ≡⟨ cong (trans p3) (trans-assoc p4) ⟩
        trans p3 (trans p4 (trans q'' r5))
          ≡⟨ cong (λ x → trans p3 (trans p4 x)) step3 ⟩
        trans p3 (trans p4 p5)
          ≡⟨ cong (λ x → trans p3 (trans p4 x)) (sym (trans-reflʳ p5)) ⟩
        trans p3 (trans p4 (trans p5 refl))
      ∎
    -- combined-shape = trans p1 (trans p2 (trans q (trans r3 (trans r4 r5))))
    -- comp-shape-eq  = trans p1 (trans p2 (trans p3 (trans p4 (trans p5 refl))))
    shape-eq : combined-shape ≡ comp-shape-eq F G H f1 f2 g1 g2 f-eq g-eq s
    shape-eq =
      begin
        combined-shape
          ≡⟨ refl ⟩
        trans (trans p1 (trans p2 q)) (trans r3 (trans r4 r5))
          ≡⟨ trans-assoc p1 ⟩
        trans p1 (trans (trans p2 q) (trans r3 (trans r4 r5)))
          ≡⟨ cong (trans p1) (trans-assoc p2) ⟩
        trans p1 (trans p2 (trans q (trans r3 (trans r4 r5))))
          ≡⟨ cong (λ x → trans p1 (trans p2 x)) inner-eq ⟩
        trans p1 (trans p2 (trans p3 (trans p4 (trans p5 refl))))
          ≡⟨ refl ⟩
        comp-shape-eq F G H f1 f2 g1 g2 f-eq g-eq s
      ∎
  in
  trans step1
    (cong (λ sh → trans (subst-unfold H (sym (trans eqO-g1 eqO-g)) s3-g) (cong (unfold H) (sym sh)))
          shape-eq)
