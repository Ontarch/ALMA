{-
ALMA — Infinite, Unbounded, Self-Referential Dynamic Cosmos
ALMA —— 无限、无界、自指的动态宇宙

Built with type theory, category theory, containers, and coalgebraic unfolding
基于类型论、范畴论、容器（containers）和余代数展开（coalgebraic unfolding）构建

Cosmos is the terminal coalgebra of a polynomial functor internalized in type theory
Cosmos 是在类型论中内部化的多项式函子的终余代数
-}

{-# OPTIONS --safe --cubical-compatible --exact-split --guardedness --double-check #-}

module Prototype.Cosmos where

open import Prototype.Prelude public

-- The core record: Cosmos is the largest universe-like structure closed under unfolding
-- 核心记录：Cosmos 是一个在展开运算下封闭的最大的类宇宙结构
record Cosmos (ℓ : Level) : Set (lsuc (lsuc ℓ)) where
  coinductive
  field
    Obj        : Set (lsuc ℓ)
    Shape      : Obj → Set (lsuc ℓ)
    Pos        : {A : Obj} → Shape A → Set (lsuc ℓ)
    Hom        : (A B : Obj) → Set (lsuc ℓ)
    idHom      : {A : Obj} → Hom A A
    comp       : {A B C : Obj} → Hom A B → Hom B C → Hom A C
    comp-assoc : {A B C D : Obj} (f : Hom A B) (g : Hom B C) (h : Hom C D)
                → comp (comp f g) h ≡ comp f (comp g h)
    id-comp-l  : {A B : Obj} (f : Hom A B) → comp idHom f ≡ f
    id-comp-r  : {A B : Obj} (f : Hom A B) → comp f idHom ≡ f
    actS       : {A B : Obj} → Hom A B → Shape A → Shape B
    actP       : {A B : Obj} (f : Hom A B) (s : Shape A) → Pos (actS f s) → Pos s
    actS-id    : {A : Obj} (s : Shape A) → actS idHom s ≡ s
    actS-comp  : {A B C : Obj} (f : Hom A B) (g : Hom B C) (s : Shape A)
                → actS (comp f g) s ≡ actS g (actS f s)
    actP-id    : {A : Obj} (s : Shape A) (p : Pos (actS idHom s))
                → actP idHom s p ≡ subst Pos (actS-id s) p
    actP-comp  : {A B C : Obj} (f : Hom A B) (g : Hom B C) (s : Shape A) (p : Pos (actS (comp f g) s))
                → actP (comp f g) s p ≡ actP f s (actP g (actS f s) (subst Pos (actS-comp f g s) p))
    unfold      : {A : Obj} → (s : Shape A) → Cosmos ℓ
    unfold-obj  : {A : Obj} → Shape A → Obj
    unfold-hom  : {A B : Obj} (f : Hom A B) (s : Shape A) → Hom (unfold-obj s) (unfold-obj (actS f s))
    unfold-hom-id : {A : Obj} (s : Shape A)
                  → unfold-hom idHom s 
                  ≡ subst (λ X → Hom (unfold-obj s) (unfold-obj X)) 
                          (sym (actS-id s))
                          (idHom {A = unfold-obj s})
    unfold-hom-comp : {A B C : Obj} (f : Hom A B) (g : Hom B C) (s : Shape A)
                    → unfold-hom (comp f g) s 
                    ≡ subst (λ X → Hom (unfold-obj s) (unfold-obj X)) 
                            (sym (actS-comp f g s))
                            (comp (unfold-hom f s) (unfold-hom g (actS f s)))
    pos-to-shape : {A : Obj} (s : Shape A) → Pos s → Shape (unfold-obj s)
    pos-actS-compat : {A B : Obj} (f : Hom A B) (s : Shape A) (p : Pos (actS f s))
                    → pos-to-shape (actS f s) p ≡ actS (unfold-hom f s) (pos-to-shape s (actP f s p))
open Cosmos public

-- Functor between Cosmos: a homomorphism of these coinductive structures
-- Cosmos 之间的函子：这些余归纳结构的同态
record _⇒ℱ_ {ℓ} (F G : Cosmos ℓ) : Set (lsuc ℓ) where
  coinductive
  private
    module F = Cosmos F
    module G = Cosmos G
  field
    onObj    : F.Obj → G.Obj
    onShape  : ∀ {A} → F.Shape A → G.Shape (onObj A)
    onPos    : ∀ {A} {s : F.Shape A} → F.Pos s → G.Pos (onShape s)
    onHom    : ∀ {A B} → F.Hom A B → G.Hom (onObj A) (onObj B)
    onActS   : ∀ {A B} (f : F.Hom A B) (s : F.Shape A) →
                onShape (F.actS f s) ≡ G.actS (onHom f) (onShape s)
    onActP   : ∀ {A B} (f : F.Hom A B) (s : F.Shape A) (p : F.Pos (F.actS f s)) →
                onPos (F.actP f s p) ≡ G.actP (onHom f) (onShape s) (subst G.Pos (onActS f s) (onPos p))
    onComp   : ∀ {A B C} (f : F.Hom A B) (g : F.Hom B C) →
                onHom (F.comp f g) ≡ G.comp (onHom f) (onHom g)
    onId     : ∀ {A} → onHom (F.idHom {A}) ≡ G.idHom {onObj A}
    onunfold  : ∀ {A} (s : F.Shape A) → F.unfold s ⇒ℱ G.unfold (onShape s)
    onunfold-obj : ∀ {A} (s : F.Shape A) →
                  onObj (F.unfold-obj s) ≡ G.unfold-obj (onShape s)
    onPos-to-shape : ∀ {A} {s : F.Shape A} (p : F.Pos s) →
                      subst G.Shape (onunfold-obj s) (onShape (F.pos-to-shape s p)) ≡ G.pos-to-shape (onShape s) (onPos p)
open _⇒ℱ_ public

-- The unit Cosmos: the trivial one-object Cosmos
-- 单位 Cosmos：平凡的单对象 Cosmos
UnitCosmos : ∀ {ℓ} → Cosmos ℓ
UnitCosmos {ℓ} = λ where
  .Obj → ⊤
  .Shape _ → ⊤
  .Pos _ → ⊤
  .Hom _ _ → ⊤
  .idHom → tt
  .comp _ _ → tt
  .comp-assoc _ _ _ → refl
  .id-comp-l _ → refl
  .id-comp-r _ → refl
  .actS _ _ → tt
  .actP _ _ p → p
  .actS-id _ → refl
  .actS-comp _ _ _ → refl
  .actP-id _ _ → refl
  .actP-comp _ _ _ _ → refl
  .unfold _ → UnitCosmos {ℓ}
  .unfold-obj _ → tt
  .unfold-hom _ _ → tt
  .unfold-hom-id _ → refl
  .unfold-hom-comp _ _ _ → refl
  .pos-to-shape _ _ → tt
  .pos-actS-compat _ _ _ → refl

-- Identity morphism F ⇒ℱ F
-- 恒等态射 F ⇒ℱ F
id⇒ℱ : ∀ {ℓ} {F : Cosmos ℓ} → F ⇒ℱ F
id⇒ℱ {ℓ} {F} = λ where
  .onObj x → x
  .onShape s → s
  .onPos p → p
  .onHom f → f
  .onActS _ _ → refl
  .onActP _ _ _ → refl
  .onComp _ _ → refl
  .onId → refl
  .onunfold s → id⇒ℱ {F = unfold F s}
  .onunfold-obj _ → refl
  .onPos-to-shape _ → refl

-- Vertical composition of Cosmos homomorphisms and associated transport lemmas
-- Cosmos 同态的垂直复合及相关的传输引理
infixr 9 _∘⇒ℱ_
_∘⇒ℱ_ : ∀ {ℓ} {F G H : Cosmos ℓ} → G ⇒ℱ H → F ⇒ℱ G → F ⇒ℱ H
onPos-subst-comm : ∀ {ℓ} {G H : Cosmos ℓ} (m : G ⇒ℱ H)
                → ∀ {B : Obj G} {s1 s2 : Shape G B} (eq : s1 ≡ s2) (p : Pos G s1)
                → onPos m (subst (Pos G) eq p)
                ≡ subst (Pos H) (cong (onShape m) eq) (onPos m p)
onPos-subst-comm m refl p = refl
onActP-proof : ∀ {ℓ} {F G H : Cosmos ℓ} (m : G ⇒ℱ H) (n : F ⇒ℱ G)
              → ∀ {A B} (f : Hom F A B) (s : Shape F A) (p : Pos F (actS F f s))
              → onPos m (onPos n (actP F f s p)) 
              ≡ actP H (onHom m (onHom n f)) (onShape m (onShape n s)) 
                      (subst (Pos H) (trans (cong (onShape m) (onActS n f s)) (onActS m (onHom n f) (onShape n s))) 
                              (onPos m (onPos n p)))
onActP-proof {ℓ} {F} {G} {H} m n f s p =
  begin
    onPos m (onPos n (actP F f s p))
  ≡⟨ cong (onPos m) (onActP n f s p) ⟩
    onPos m (actP G (onHom n f) (onShape n s) (subst (Pos G) (onActS n f s) (onPos n p)))
  ≡⟨ onActP m (onHom n f) (onShape n s) _ ⟩
    actP H (onHom m (onHom n f)) (onShape m (onShape n s))
      (subst (Pos H) (onActS m (onHom n f) (onShape n s))
        (onPos m (subst (Pos G) (onActS n f s) (onPos n p))))
  ≡⟨ cong (λ x → actP H (onHom m (onHom n f)) (onShape m (onShape n s))
                    (subst (Pos H) (onActS m (onHom n f) (onShape n s)) x))
          (onPos-subst-comm m (onActS n f s) (onPos n p)) ⟩
    actP H (onHom m (onHom n f)) (onShape m (onShape n s))
      (subst (Pos H) (onActS m (onHom n f) (onShape n s))
        (subst (Pos H) (cong (onShape m) (onActS n f s)) (onPos m (onPos n p))))
  ≡⟨ cong (actP H (onHom m (onHom n f)) (onShape m (onShape n s)))
          (subst-comp (cong (onShape m) (onActS n f s)) (onActS m (onHom n f) (onShape n s))) ⟩
    actP H (onHom m (onHom n f)) (onShape m (onShape n s))
      (subst (Pos H) (trans (cong (onShape m) (onActS n f s)) (onActS m (onHom n f) (onShape n s)))
        (onPos m (onPos n p)))
  ∎
onShape-subst-comm : ∀ {ℓ} {G H : Cosmos ℓ} (m : G ⇒ℱ H)
                  → ∀ {B B' : Obj G} (eq : B ≡ B') (t : Shape G B)
                  → onShape m (subst (Shape G) eq t)
                  ≡ subst (Shape H) (cong (onObj m) eq) (onShape m t)
onShape-subst-comm m refl t = refl
onPos-to-shape-proof : ∀ {ℓ} {F G H : Cosmos ℓ} (m : G ⇒ℱ H) (n : F ⇒ℱ G)
                      → ∀ {A} {s : Shape F A} (p : Pos F s)
                      → subst (Shape H) (trans (cong (onObj m) (onunfold-obj n s)) (onunfold-obj m (onShape n s))) 
                              (onShape m (onShape n (pos-to-shape F s p)))
                      ≡ pos-to-shape H (onShape m (onShape n s)) (onPos m (onPos n p))
onPos-to-shape-proof {ℓ} {F} {G} {H} m n {A} {s} p =
  begin
    subst (Shape H) (trans (cong (onObj m) (onunfold-obj n s)) (onunfold-obj m (onShape n s)))
      (onShape m (onShape n (pos-to-shape F s p)))
  ≡⟨ sym (subst-comp (cong (onObj m) (onunfold-obj n s)) (onunfold-obj m (onShape n s))) ⟩
    subst (Shape H) (onunfold-obj m (onShape n s))
      (subst (Shape H) (cong (onObj m) (onunfold-obj n s))
        (onShape m (onShape n (pos-to-shape F s p))))
  ≡⟨ cong (subst (Shape H) (onunfold-obj m (onShape n s)))
          (sym (onShape-subst-comm m (onunfold-obj n s) (onShape n (pos-to-shape F s p)))) ⟩
    subst (Shape H) (onunfold-obj m (onShape n s))
      (onShape m (subst (Shape G) (onunfold-obj n s) (onShape n (pos-to-shape F s p))))
  ≡⟨ cong (λ x → subst (Shape H) (onunfold-obj m (onShape n s)) (onShape m x))
          (onPos-to-shape n p) ⟩
    subst (Shape H) (onunfold-obj m (onShape n s))
      (onShape m (pos-to-shape G (onShape n s) (onPos n p)))
  ≡⟨ onPos-to-shape m (onPos n p) ⟩
    pos-to-shape H (onShape m (onShape n s)) (onPos m (onPos n p))
  ∎
_∘⇒ℱ_ m n .onObj A = onObj m (onObj n A)
_∘⇒ℱ_ m n .onShape s = onShape m (onShape n s)
_∘⇒ℱ_ m n .onPos p = onPos m (onPos n p)
_∘⇒ℱ_ m n .onHom f = onHom m (onHom n f)
_∘⇒ℱ_ m n .onActS f s = trans (cong (onShape m) (onActS n f s)) (onActS m (onHom n f) (onShape n s))
_∘⇒ℱ_ m n .onActP f s p = onActP-proof m n f s p
_∘⇒ℱ_ m n .onComp f g = trans (cong (onHom m) (onComp n f g)) (onComp m (onHom n f) (onHom n g))
_∘⇒ℱ_ m n .onId {A} = trans (cong (onHom m) (onId n {A})) (onId m)
_∘⇒ℱ_ m n .onunfold s = onunfold m (onShape n s) ∘⇒ℱ onunfold n s
_∘⇒ℱ_ m n .onunfold-obj s = trans (cong (onObj m) (onunfold-obj n s)) (onunfold-obj m (onShape n s))
_∘⇒ℱ_ m n .onPos-to-shape {A} {s} p = onPos-to-shape-proof m n {A} {s} p

-- Transport operation for positions
-- 位置的传输操作
subst-pos : ∀ {ℓ} (C : Cosmos ℓ) {X Y : Obj C} (eq : X ≡ Y) (s : Shape C X)
          → Pos C s → Pos C (subst (Shape C) eq s)
subst-pos C refl s p = p
-- Transport compatibility for unfold
-- 展开操作的传输一致性
subst-unfold : ∀ {ℓ} (C : Cosmos ℓ) {X Y : Obj C} (eq : X ≡ Y) (s : Shape C X)
            → unfold C s ≡ unfold C (subst (Shape C) eq s)
subst-unfold C refl s = refl

-- 2-cells of the bicategory: equivalences between homomorphisms F ⇒ℱ G
-- 双范畴的2-胞腔：同态 F ⇒ℱ G 之间的等价关系
infix 4 _≃⇒ℱ_
record _≃⇒ℱ_ {ℓ} {F G : Cosmos ℓ} (m₁ m₂ : F ⇒ℱ G) : Set (lsuc ℓ) where
  coinductive
  private
    module F = Cosmos F
    module G = Cosmos G
    module M₁ = _⇒ℱ_ m₁
    module M₂ = _⇒ℱ_ m₂
  field
    onObj-eq   : ∀ (A : F.Obj) → M₁.onObj A ≡ M₂.onObj A
    onShape-eq : ∀ {A : F.Obj} (s : F.Shape A) 
               → M₁.onShape s ≡ subst G.Shape (sym (onObj-eq A)) (M₂.onShape s)
    onPos-eq   : ∀ {A : F.Obj} {s : F.Shape A} (p : F.Pos s)
               → M₁.onPos p ≡ subst (G.Pos {M₁.onObj A}) (sym (onShape-eq s)) 
                                   (subst-pos G (sym (onObj-eq A)) (M₂.onShape s) (M₂.onPos p))
    onHom-eq   : ∀ {A B : F.Obj} (f : F.Hom A B)
               → M₁.onHom f ≡ subst₂ G.Hom (sym (onObj-eq A)) (sym (onObj-eq B)) (M₂.onHom f)
    onunfold-eq : ∀ {A : F.Obj} (s : F.Shape A)
               → _≃⇒ℱ_ {ℓ = ℓ} {F = F.unfold s} {G = G.unfold (M₁.onShape s)}
                   (M₁.onunfold s)
                   (subst (λ C → F.unfold s ⇒ℱ C)
                       (trans (subst-unfold G (sym (onObj-eq A)) (M₂.onShape s))
                              (cong G.unfold (sym (onShape-eq s))))
                       (M₂.onunfold s))
open _≃⇒ℱ_ public

-- Reflexivity
-- 自反性
refl-≃⇒ℱ : ∀ {ℓ} {F G : Cosmos ℓ} {m : F ⇒ℱ G} → m ≃⇒ℱ m
refl-≃⇒ℱ .onObj-eq A = refl
refl-≃⇒ℱ .onShape-eq s = refl
refl-≃⇒ℱ .onPos-eq p = refl
refl-≃⇒ℱ .onHom-eq f = refl
refl-≃⇒ℱ .onunfold-eq s = refl-≃⇒ℱ

-- Strict equality implies equivalence
-- 严格相等蕴含等价
≡→≃⇒ℱ : ∀ {ℓ} {F G : Cosmos ℓ} {m₁ m₂ : F ⇒ℱ G} → m₁ ≡ m₂ → m₁ ≃⇒ℱ m₂
≡→≃⇒ℱ refl = refl-≃⇒ℱ

-- Symmetry
-- 对称性
sym-≃⇒ℱ : ∀ {ℓ} {F G : Cosmos ℓ} {m₁ m₂ : F ⇒ℱ G}
        → m₁ ≃⇒ℱ m₂ → m₂ ≃⇒ℱ m₁
sym-Field₁ : ∀ {ℓ} {F G : Cosmos ℓ} {m₁ m₂ : F ⇒ℱ G}
             (e : m₁ ≃⇒ℱ m₂)
             {O₁ O₂ : Cosmos.Obj G}
             (eqO : O₁ ≡ O₂)
             (P : Cosmos.Obj G → Set (lsuc ℓ))
             {x : P O₁} {y : P O₂}
           → x ≡ subst P (sym eqO) y
           → y ≡ subst P (sym (sym eqO)) x
sym-Field₁ e eqO P {x} {y} h =
  trans (sym ( trans (cong (subst P eqO) h) (subst-inv' P eqO) ))
        (cong (λ p → subst P p x) (sym-sym eqO))
shape-sym-lemma : ∀ {ℓ} {F G : Cosmos ℓ} {m₁ m₂ : F ⇒ℱ G} (e : m₁ ≃⇒ℱ m₂)
                → ∀ {A} (s : Shape F A)
                → onShape m₂ s ≡ subst (Shape G) (sym (sym (onObj-eq e A))) (onShape m₁ s)
shape-sym-lemma {ℓ} {F} {G} {m₁} {m₂} e {A} s = sym-Field₁ e (onObj-eq e _) (Shape G) (onShape-eq e s)
subst-shape-sym-sym : ∀ {ℓ} {F G : Cosmos ℓ} {m₁ m₂ : F ⇒ℱ G} {e : m₁ ≃⇒ℱ m₂} {A : Obj F} {s : Shape F A}
                    → subst (Shape G) (sym (sym (onObj-eq e A))) (onShape m₁ s) 
                    ≡ subst (Shape G) (onObj-eq e A) (onShape m₁ s)
subst-shape-sym-sym {ℓ} {F} {G} {m₁} {m₂} {e} {A} {s} =
  let
    eqO = onObj-eq e A
    S1 = onShape m₁ s
  in
  cong (λ x → subst (Shape G) x S1) (sym (sym-sym eqO))
cong-bridge-eq : ∀ {ℓ} {F G : Cosmos ℓ} {m₁ m₂ : F ⇒ℱ G} {e : m₁ ≃⇒ℱ m₂} {A : Obj F} {s : Shape F A}
                → let eqO = onObj-eq e A
                      f = λ (x : onObj m₁ A ≡ onObj m₂ A) → subst (Shape G) x (onShape m₁ s)
                  in cong f (sym (sym (sym-sym eqO))) ≡ cong f (sym-sym eqO)
cong-bridge-eq {ℓ} {F} {G} {m₁} {m₂} {e} {A} {s} =
  let
    eqO = onObj-eq e A
    f = λ (x : onObj m₁ A ≡ onObj m₂ A) → subst (Shape G) x (onShape m₁ s)
    inner-eq : sym (sym (sym-sym eqO)) ≡ sym-sym eqO
    inner-eq = sym (sym-sym (sym-sym eqO))
  in
  cong (λ x → cong f x) inner-eq
shape-lemma-def : ∀ {ℓ} {F G : Cosmos ℓ} {m₁ m₂ : F ⇒ℱ G} {e : m₁ ≃⇒ℱ m₂} {A : Obj F} {s : Shape F A}
                → shape-sym-lemma e s ≡ trans (sym (trans (cong (subst (Shape G) (onObj-eq e A)) (onShape-eq e s)) (subst-inv' (Shape G) (onObj-eq e A)))) (sym (subst-shape-sym-sym {ℓ} {F} {G} {m₁} {m₂} {e} {A} {s}))
shape-lemma-def {ℓ} {F} {G} {m₁} {m₂} {e} {A} {s} =
  let
    eqO = onObj-eq e A
    eqSh = onShape-eq e s
    base = trans (cong (subst (Shape G) eqO) eqSh) (subst-inv' (Shape G) eqO)
    bridge = cong (λ x → subst (Shape G) x (onShape m₁ s)) (sym-sym eqO)
    f = λ x → subst (Shape G) x (onShape m₁ s)
    bridge-eq : bridge ≡ sym (subst-shape-sym-sym {ℓ} {F} {G} {m₁} {m₂} {e} {A} {s})
    bridge-eq =
      let
        step1 : sym (subst-shape-sym-sym {ℓ} {F} {G} {m₁} {m₂} {e} {A} {s}) 
              ≡ sym (cong f (sym (sym-sym eqO)))
        step1 = refl
        step2 : sym (cong f (sym (sym-sym eqO)))
              ≡ cong f (sym (sym (sym-sym eqO)))
        step2 = sym-cong (sym (sym-sym eqO))
        step3 : cong f (sym (sym (sym-sym eqO))) ≡ bridge
        step3 = cong-bridge-eq {ℓ} {F} {G} {m₁} {m₂} {e} {A} {s}
        combined : sym (subst-shape-sym-sym {ℓ} {F} {G} {m₁} {m₂} {e} {A} {s}) ≡ bridge
        combined = trans step1 (trans step2 step3)
      in
      sym combined
  in
  cong (λ x → trans (sym base) x) bridge-eq
subst-pos-sym-sym : ∀ {ℓ} {G : Cosmos ℓ} {O1 O2 : Obj G} (eqO : O1 ≡ O2) (S1 : Shape G O1) (P1 : Pos G S1)
                 → subst (Pos G {O2}) (cong (λ x → subst (Shape G) x S1) (sym (sym-sym eqO)))
                       (subst-pos G (sym (sym eqO)) S1 P1)
                 ≡ subst-pos G eqO S1 P1
subst-pos-sym-sym {ℓ} {G} {O1} {O2} eqO S1 P1 = J (λ O2 eqO → subst (Pos G {O2}) (cong (λ x → subst (Shape G) x S1) (sym (sym-sym eqO))) (subst-pos G (sym (sym eqO)) S1 P1) ≡ subst-pos G eqO S1 P1) eqO refl
subst-pos-cancel : ∀ {ℓ} (C : Cosmos ℓ) {O1 O2 : Obj C} (eqO : O1 ≡ O2)
                 → {S1 : Shape C O1} {S2 : Shape C O2} (eqSh : S1 ≡ subst (Shape C) (sym eqO) S2)
                 → (p : Pos C S2)
                 → subst (Pos C) (trans (cong (subst (Shape C) eqO) eqSh) (subst-inv' (Shape C) eqO))
                     (subst-pos C eqO S1 (subst (Pos C {O1}) (sym eqSh) (subst-pos C (sym eqO) S2 p)))
                   ≡ p
subst-pos-cancel {ℓ} C {O1} {.O1} refl {S1} {S2} eqSh p =
  let
    step1 : trans (cong (subst (Shape C) refl) eqSh) (subst-inv' (Shape C) refl) 
          ≡ cong (subst (Shape C) refl) eqSh
    step1 = trans-reflʳ (cong (subst (Shape C) refl) eqSh)
    step2 : subst-pos C refl S1 (subst (Pos C {O1}) (sym eqSh) (subst-pos C refl S2 p))
          ≡ subst (Pos C {O1}) (sym eqSh) (subst (Pos C {O1}) refl p)
    step2 = refl
    step3 : cong (subst (Shape C) refl) eqSh ≡ eqSh
    step3 = cong-id eqSh
    step4 : subst (Pos C {O1}) eqSh (subst (Pos C {O1}) (sym eqSh) (subst (Pos C {O1}) refl p)) 
          ≡ subst (Pos C {O1}) refl p
    step4 = subst-inv' (Pos C {O1}) eqSh
    step5 : subst (Pos C {O1}) refl p ≡ p
    step5 = refl
  in
  trans (cong₂ (λ eq x → subst (Pos C) eq x) step1 step2)
        (trans (cong (λ eq → subst (Pos C) eq (subst (Pos C {O1}) (sym eqSh) (subst (Pos C {O1}) refl p))) step3)
               (trans step4 step5))
pos-step1-correct : ∀ {ℓ} {F G : Cosmos ℓ} {m₁ m₂ : F ⇒ℱ G} {e : m₁ ≃⇒ℱ m₂} {A : Obj F} {s : Shape F A} {p : Pos F s}
                  → let eqO = onObj-eq e A
                        eqSh = onShape-eq e s
                        S-eq = trans (cong (subst (Shape G) eqO) eqSh) (subst-inv' (Shape G) eqO)
                        O1 = onObj m₁ A
                        O2 = onObj m₂ A
                        S1 = onShape m₁ s
                        S2 = onShape m₂ s
                        P1 = onPos m₁ p
                        P2 = onPos m₂ p
                    in subst (Pos G) S-eq (subst-pos G eqO S1 P1) ≡ P2
pos-step1-correct {G = G} {m₁ = m₁} {m₂ = m₂} {e = e} {A} {s} {p} =
  let
    eqO = onObj-eq e A
    eqSh = onShape-eq e s
    S-eq = trans (cong (subst (Shape G) eqO) eqSh) (subst-inv' (Shape G) eqO)
    O1 = onObj m₁ A
    O2 = onObj m₂ A
    S1 = onShape m₁ s
    S2 = onShape m₂ s
    P1 = onPos m₁ p
    P2 = onPos m₂ p
    step1 : subst (Pos G) S-eq (subst-pos G eqO S1 P1) 
          ≡ subst (Pos G) S-eq (subst-pos G eqO S1 (subst (Pos G {O1}) (sym eqSh) (subst-pos G (sym eqO) S2 P2)))
    step1 = cong (λ x → subst (Pos G) S-eq (subst-pos G eqO S1 x)) (onPos-eq e p)
    step2 : subst (Pos G) S-eq (subst-pos G eqO S1 (subst (Pos G {O1}) (sym eqSh) (subst-pos G (sym eqO) S2 P2))) ≡ P2
    step2 = subst-pos-cancel G eqO eqSh P2
  in
  trans step1 step2
pos-sym-lemma : ∀ {ℓ} {F G : Cosmos ℓ} {m₁ m₂ : F ⇒ℱ G} (e : m₁ ≃⇒ℱ m₂)
              → ∀ {A} {s : Shape F A} (p : Pos F s)
              → onPos m₂ p ≡ subst (Pos G {onObj m₂ A}) (sym (shape-sym-lemma e s)) 
                                  (subst-pos G (sym (sym (onObj-eq e A))) (onShape m₁ s) (onPos m₁ p))
pos-sym-lemma {ℓ} {F} {G} {m₁} {m₂} e {A} {s} p =
  let
    O1 = onObj m₁ A
    O2 = onObj m₂ A
    eqO = onObj-eq e A
    S1 = onShape m₁ s
    P1 = onPos m₁ p
    P2 = onPos m₂ p
    shape-lemma = shape-sym-lemma e s
    S-eq = trans (cong (subst (Shape G) eqO) (onShape-eq e s)) (subst-inv' (Shape G) eqO)
    subst-shape = subst-shape-sym-sym {e = e} {A} {s}
    X : Pos G {O2} (subst (Shape G) (sym (sym eqO)) S1)
    X = subst-pos G (sym (sym eqO)) S1 P1
    sym-lemma-eq : sym shape-lemma ≡ trans subst-shape S-eq
    sym-lemma-eq =
      let
        sh-def = shape-lemma-def {e = e} {A} {s}
        step1 = cong sym sh-def
        step2 = sym-trans (sym S-eq) (sym subst-shape)
        step3 = cong₂ trans (sym (sym-sym subst-shape)) (sym (sym-sym S-eq))
      in trans step1 (trans step2 step3)
    step1 : subst (Pos G {O2}) (sym shape-lemma) X
          ≡ subst (Pos G {O2}) S-eq (subst (Pos G {O2}) subst-shape X)
    step1 = trans (cong (λ eq → subst (Pos G {O2}) eq X) sym-lemma-eq)
                  (sym (subst-comp {A = Shape G O2} {B = Pos G {O2}} subst-shape S-eq {b = X}))
    step2 : subst (Pos G {O2}) subst-shape X ≡ subst-pos G eqO S1 P1
    step2 = subst-pos-sym-sym {G = G} eqO S1 P1
    step3 : subst (Pos G {O2}) (sym shape-lemma) X
          ≡ subst (Pos G {O2}) S-eq (subst-pos G eqO S1 P1)
    step3 = trans step1 (cong (λ x → subst (Pos G {O2}) S-eq x) step2)
    step4 : subst (Pos G {O2}) S-eq (subst-pos G eqO S1 P1) ≡ P2
    step4 = pos-step1-correct {e = e} {A} {s} {p}
    all : subst (Pos G {O2}) (sym shape-lemma) X ≡ P2
    all = trans step3 step4
  in sym all
sym-Field₂ : ∀ {ℓ} {F G : Cosmos ℓ} {m₁ m₂ : F ⇒ℱ G}
             (e : m₁ ≃⇒ℱ m₂)
             {O₁A O₂A O₁B O₂B : Cosmos.Obj G}
             (eqOA : O₁A ≡ O₂A) (eqOB : O₁B ≡ O₂B)
             (P : Cosmos.Obj G → Cosmos.Obj G → Set (lsuc ℓ))
             {x : P O₁A O₁B} {y : P O₂A O₂B}
           → x ≡ subst₂ P (sym eqOA) (sym eqOB) y
           → y ≡ subst₂ P (sym (sym eqOA)) (sym (sym eqOB)) x
sym-Field₂ e eqOA eqOB P {x} {y} h =
  trans (sym (trans (cong (subst₂ P eqOA eqOB) h)
                    (subst-inv₂' eqOA eqOB {c = y})))
        (cong₂ (λ p q → subst₂ P p q x) (sym-sym eqOA) (sym-sym eqOB))
hom-sym-lemma : ∀ {ℓ} {F G : Cosmos ℓ} {m₁ m₂ : F ⇒ℱ G} (e : m₁ ≃⇒ℱ m₂)
              → ∀ {A B} (f : Hom F A B)
              → onHom m₂ f ≡ subst₂ (Hom G) (sym (sym (onObj-eq e A))) (sym (sym (onObj-eq e B))) (onHom m₁ f)
hom-sym-lemma {ℓ} {F} {G} {m₁} {m₂} e {A} {B} f = sym-Field₂ e (onObj-eq e _) (onObj-eq e _) (Hom G) (onHom-eq e f)
subst-inv'-refl : ∀ {ℓ} {G : Cosmos ℓ} {O : Obj G} {s : Shape G O}
                → subst-inv' (Shape G) refl {b = s} ≡ refl
subst-inv'-refl = refl
cong-subst-refl : ∀ {ℓ} {G : Cosmos ℓ} {O1 : Obj G} {S1 S2 : Shape G O1} (eq : S1 ≡ S2)
                → cong (subst (Shape G) refl) eq ≡ eq
cong-subst-refl {ℓ} {G} {O1} {S1} {.S1} refl = refl
S-eq-base-eq : ∀ {ℓ} {G : Cosmos ℓ} {O1 : Obj G} {S1 S2 : Shape G O1} (eqSh : S1 ≡ S2)
             → trans (cong (subst (Shape G) refl) eqSh) (subst-inv' (Shape G) refl) ≡ eqSh
S-eq-base-eq {G = G} {O1 = O1} {S2 = S2} eqSh =
  let lemma : subst-inv' (Shape G) refl ≡ refl
      lemma = subst-inv'-refl {G = G} {O = O1} {s = S2}
  in
  trans (cong (λ z → trans (cong (subst (Shape G) refl) eqSh) z) lemma)
        (trans (cong (λ x → trans x refl) (cong-subst-refl {G = G} {O1 = O1} eqSh))
               (trans-reflʳ eqSh))
unfold-trans-sym : ∀ {ℓ} (G : Cosmos ℓ) (O1 O2 : Obj G) (eqO : O1 ≡ O2) 
                → (S1 : Shape G O1) (S2 : Shape G O2)
                → (eqSh : S1 ≡ subst (Shape G) (sym eqO) S2)
                → let S-eq = trans (cong (subst (Shape G) eqO) eqSh) (subst-inv' (Shape G) eqO)
                  in sym (trans (subst-unfold G (sym eqO) S2) (cong (unfold G {O1}) (sym eqSh)))
                  ≡ trans (subst-unfold G eqO S1) (cong (unfold G {O2}) S-eq)
unfold-trans-sym G O1 .O1 refl S1 S2 eqSh =
  let
    S-eq = trans (cong (subst (Shape G) refl) eqSh) (subst-inv' (Shape G) refl)
    step1 : sym (trans (subst-unfold G refl S2) (cong (unfold G {O1}) (sym eqSh)))
          ≡ sym (cong (unfold G {O1}) (sym eqSh))
    step1 = cong sym (transReflˡ (cong (unfold G {O1}) (sym eqSh)))
    step2 : sym (cong (unfold G {O1}) (sym eqSh))
          ≡ cong (unfold G {O1}) (sym (sym eqSh))
    step2 = sym-cong {f = unfold G {O1}} (sym eqSh)
    step3 : cong (unfold G {O1}) (sym (sym eqSh))
          ≡ cong (unfold G {O1}) eqSh
    step3 = cong (cong (unfold G {O1})) (sym (sym-sym eqSh))
    left-final : sym (trans (subst-unfold G refl S2) (cong (unfold G {O1}) (sym eqSh)))
               ≡ cong (unfold G {O1}) eqSh
    left-final = trans step1 (trans step2 step3)
    step4 : trans (subst-unfold G refl S1) (cong (unfold G {O1}) S-eq)
          ≡ cong (unfold G {O1}) S-eq
    step4 = transReflˡ (cong (unfold G {O1}) S-eq)
    step5 : S-eq ≡ eqSh
    step5 = S-eq-base-eq {G = G} {O1 = O1} {S1 = S1} {S2 = S2} eqSh
    step6 : cong (unfold G {O1}) S-eq ≡ cong (unfold G {O1}) eqSh
    step6 = cong (cong (unfold G {O1})) step5
    right-final : trans (subst-unfold G refl S1) (cong (unfold G {O1}) S-eq)
                ≡ cong (unfold G {O1}) eqSh
    right-final = trans step4 step6
  in
  trans left-final (sym right-final)
subst-unfold-sym-sym : ∀ {ℓ} (C : Cosmos ℓ) {X Y : Obj C} (eq : X ≡ Y) (s : Shape C X)
                    → subst-unfold C (sym (sym eq)) s 
                    ≡ trans (subst-unfold C eq s) 
                            (cong (unfold C) (cong (λ x → subst (Shape C) x s) (sym-sym eq)))
subst-unfold-sym-sym C {X} {Y} eq s =
  J {x = X} (λ Y' eq' → 
      subst-unfold C (sym (sym eq')) s 
      ≡ trans (subst-unfold C eq' s) 
              (cong (unfold C) (cong (λ x → subst (Shape C) x s) (sym-sym eq'))))
    eq refl
shape-lemma-is-sym : ∀ {ℓ} {F G : Cosmos ℓ} {m₁ m₂ : F ⇒ℱ G} {e : m₁ ≃⇒ℱ m₂} {A : Obj F} {s : Shape F A}
                    → let eqO = onObj-eq e A
                          S-eq = trans (cong (subst (Shape G) eqO) (onShape-eq e s)) (subst-inv' (Shape G) eqO)
                          subst-shape = subst-shape-sym-sym {e = e} {A} {s}
                      in shape-sym-lemma e s ≡ sym (trans subst-shape S-eq)
shape-lemma-is-sym {ℓ} {F} {G} {m₁} {m₂} {e} {A} {s} =
  let
    eqO = onObj-eq e A
    S-eq = trans (cong (subst (Shape G) eqO) (onShape-eq e s)) (subst-inv' (Shape G) eqO)
    subst-shape = subst-shape-sym-sym {e = e} {A} {s}
  in
  trans (shape-lemma-def {e = e} {A} {s})
        (sym (sym-trans subst-shape S-eq))
unfold-path-eq : ∀ {ℓ} {F G : Cosmos ℓ} {m₁ m₂ : F ⇒ℱ G} (e : m₁ ≃⇒ℱ m₂) {A : Obj F} (s : Shape F A)
              → let eqO = onObj-eq e A
                    eqSh = onShape-eq e s
                    shape-lem = shape-sym-lemma e s
                    path1 = trans (subst-unfold G (sym eqO) (onShape m₂ s)) (cong (unfold G) (sym eqSh))
                    path2 = trans (subst-unfold G (sym (sym eqO)) (onShape m₁ s)) (cong (unfold G) (sym shape-lem))
                in sym path1 ≡ path2
unfold-path-eq {ℓ} {F} {G} {m₁} {m₂} e {A} s =
  let
      O1 = onObj m₁ A
      O2 = onObj m₂ A
      eqO = onObj-eq e A
      S1 = onShape m₁ s
      S2 = onShape m₂ s
      eqSh = onShape-eq e s
      shape-lem = shape-sym-lemma e s
      S-eq : subst (Shape G) eqO S1 ≡ S2
      S-eq = trans (cong (subst (Shape G) eqO) eqSh) (subst-inv' (Shape G) eqO)
      subst-shape : subst (Shape G) (sym (sym eqO)) S1 ≡ subst (Shape G) eqO S1
      subst-shape = subst-shape-sym-sym {e = e} {A = A} {s = s}
      step1 : sym (trans (subst-unfold G (sym eqO) S2) (cong (unfold G) (sym eqSh))) 
            ≡ trans (subst-unfold G eqO S1) (cong (unfold G) S-eq)
      step1 = unfold-trans-sym G O1 O2 eqO S1 S2 eqSh
      shape-eq : subst (Shape G) (sym (sym eqO)) S1 ≡ subst (Shape G) eqO S1
      shape-eq = cong (λ x → subst (Shape G) x S1) (sym (sym-sym eqO))
      f : (O1 ≡ O2) → Shape G O2
      f x = subst (Shape G) x S1
      eq1 : cong f (sym-sym eqO) ≡ sym shape-eq
      eq1 = sym (begin
        sym shape-eq
          ≡⟨ refl ⟩
        sym (cong f (sym (sym-sym eqO)))
          ≡⟨ sym-cong (sym (sym-sym eqO)) ⟩
        cong f (sym (sym (sym-sym eqO)))
          ≡⟨ cong (cong f) (sym (sym-sym (sym-sym eqO))) ⟩
        cong f (sym-sym eqO)
        ∎)
      step2a : cong (unfold G) (cong f (sym-sym eqO)) ≡ cong (unfold G) (sym shape-eq)
      step2a = cong (cong (unfold G)) eq1
      step2 : subst-unfold G (sym (sym eqO)) S1 
            ≡ trans (subst-unfold G eqO S1) (cong (unfold G) (sym shape-eq))
      step2 = begin
        subst-unfold G (sym (sym eqO)) S1
          ≡⟨ subst-unfold-sym-sym G eqO S1 ⟩
        trans (subst-unfold G eqO S1) (cong (unfold G) (cong f (sym-sym eqO)))
          ≡⟨ cong (trans (subst-unfold G eqO S1)) step2a ⟩
        trans (subst-unfold G eqO S1) (cong (unfold G) (sym shape-eq))
        ∎
      step3 : shape-lem ≡ sym (trans subst-shape S-eq)
      step3 = shape-lemma-is-sym {e = e} {A = A} {s = s}
      step4 : sym shape-lem ≡ trans subst-shape S-eq
      step4 = trans (cong sym step3) (sym (sym-sym (trans subst-shape S-eq)))
      step4a : trans (sym shape-eq) (trans subst-shape S-eq) ≡ S-eq
      step4a = begin
        trans (sym shape-eq) (trans subst-shape S-eq)
          ≡⟨ sym (trans-assoc' (sym shape-eq) subst-shape S-eq) ⟩
        trans (trans (sym shape-eq) subst-shape) S-eq
          ≡⟨ cong (λ x → trans x S-eq) (trans-symˡ shape-eq) ⟩
        trans refl S-eq
          ≡⟨ transReflˡ S-eq ⟩
        S-eq
        ∎
      step5 : trans (subst-unfold G (sym (sym eqO)) S1) (cong (unfold G) (sym shape-lem)) 
            ≡ trans (subst-unfold G eqO S1) (cong (unfold G) S-eq)
      step5 = begin
        trans (subst-unfold G (sym (sym eqO)) S1) (cong (unfold G) (sym shape-lem))
          ≡⟨ cong (λ x → trans x (cong (unfold G) (sym shape-lem))) step2 ⟩
        trans (trans (subst-unfold G eqO S1) (cong (unfold G) (sym shape-eq))) (cong (unfold G) (sym shape-lem))
          ≡⟨ trans-assoc' (subst-unfold G eqO S1) (cong (unfold G) (sym shape-eq)) (cong (unfold G) (sym shape-lem)) ⟩
        trans (subst-unfold G eqO S1) (trans (cong (unfold G) (sym shape-eq)) (cong (unfold G) (sym shape-lem)))
          ≡⟨ cong (trans (subst-unfold G eqO S1)) (trans-cong {f = unfold G} (sym shape-eq) {q = sym shape-lem}) ⟩
        trans (subst-unfold G eqO S1) (cong (unfold G) (trans (sym shape-eq) (sym shape-lem)))
          ≡⟨ cong (λ x → trans (subst-unfold G eqO S1) (cong (unfold G) (trans (sym shape-eq) x))) step4 ⟩
        trans (subst-unfold G eqO S1) (cong (unfold G) (trans (sym shape-eq) (trans subst-shape S-eq)))
          ≡⟨ cong (λ x → trans (subst-unfold G eqO S1) (cong (unfold G) x)) step4a ⟩
        trans (subst-unfold G eqO S1) (cong (unfold G) S-eq)
        ∎
  in begin
    sym (trans (subst-unfold G (sym eqO) S2) (cong (unfold G) (sym eqSh))) 
      ≡⟨ step1 ⟩
    trans (subst-unfold G eqO S1) (cong (unfold G) S-eq)
      ≡⟨ sym step5 ⟩
    trans (subst-unfold G (sym (sym eqO)) S1) (cong (unfold G) (sym shape-lem))
    ∎
subst-≃⇒ℱ-cancel : ∀ (ℓ : Level) (F : Cosmos ℓ) (C D : Cosmos ℓ) (eq : C ≡ D)
                   → {m : F ⇒ℱ D} {n : F ⇒ℱ C}
                   → m ≃⇒ℱ subst (λ X → F ⇒ℱ X) eq n
                   → subst (λ X → F ⇒ℱ X) (sym eq) m ≃⇒ℱ n
subst-≃⇒ℱ-cancel ℓ F C .C refl h = h
≡-left-≃⇒ℱ : ∀ {ℓ} {F G : Cosmos ℓ} {a b c : F ⇒ℱ G}
           → a ≡ b → b ≃⇒ℱ c → a ≃⇒ℱ c
≡-left-≃⇒ℱ eq h = subst (λ x → x ≃⇒ℱ _) (sym eq) h
sym-≃⇒ℱ {ℓ} {F} {G} {m₁} {m₂} h .onObj-eq A = sym (h .onObj-eq A)
sym-≃⇒ℱ {ℓ} {F} {G} {m₁} {m₂} h .onShape-eq {A} s = shape-sym-lemma h s
sym-≃⇒ℱ {ℓ} {F} {G} {m₁} {m₂} h .onPos-eq {A} {s} p = pos-sym-lemma h p
sym-≃⇒ℱ {ℓ} {F} {G} {m₁} {m₂} h .onHom-eq {A} {B} f = hom-sym-lemma h f
sym-≃⇒ℱ {ℓ} {F} {G} {m₁} {m₂} h .onunfold-eq {A} s =
  let
    eqO = h .onObj-eq A
    eqSh = h .onShape-eq s
    shape-lem = shape-sym-lemma h s
    path' : unfold G (m₂ .onShape s) ≡ unfold G (m₁ .onShape s)
    path' = trans (subst-unfold G (sym eqO) (m₂ .onShape s))
                  (cong (unfold G) (sym eqSh))
    path : unfold G (m₁ .onShape s) ≡ unfold G (m₂ .onShape s)
    path = trans (subst-unfold G (sym (sym eqO)) (m₁ .onShape s))
                 (cong (unfold G) (sym shape-lem))
    path-eq : sym path' ≡ path
    path-eq = unfold-path-eq h s
    orig : _≃⇒ℱ_ {ℓ = ℓ} {F = unfold F s} {G = unfold G (m₁ .onShape s)}
             (m₁ .onunfold s)
             (subst (λ C → unfold F s ⇒ℱ C) path' (m₂ .onunfold s))
    orig = h .onunfold-eq s
    step1 : _≃⇒ℱ_ {ℓ = ℓ} {F = unfold F s} {G = unfold G (m₂ .onShape s)}
              (subst (λ C → unfold F s ⇒ℱ C) (sym path') (m₁ .onunfold s))
              (m₂ .onunfold s)
    step1 = subst-≃⇒ℱ-cancel ℓ
            (unfold F s)
            (unfold G (m₂ .onShape s))
            (unfold G (m₁ .onShape s))
            path'
            orig
    morph-eq : subst (λ C → unfold F s ⇒ℱ C) (sym path') (m₁ .onunfold s)
             ≡ subst (λ C → unfold F s ⇒ℱ C) path (m₁ .onunfold s)
    morph-eq = cong (λ p → subst (λ C → unfold F s ⇒ℱ C) p (m₁ .onunfold s)) path-eq
    step3 : _≃⇒ℱ_ {ℓ = ℓ} {F = unfold F s} {G = unfold G (m₂ .onShape s)}
              (subst (λ C → unfold F s ⇒ℱ C) path (m₁ .onunfold s))
              (m₂ .onunfold s)
    step3 = ≡-left-≃⇒ℱ (sym morph-eq) step1
  in
    sym-≃⇒ℱ {ℓ = ℓ} {F = unfold F s} {G = unfold G (m₂ .onShape s)} step3

-- Transitivity
-- 传递性
trans-≃⇒ℱ : ∀ {ℓ} {F G : Cosmos ℓ} {m₁ m₂ m₃ : F ⇒ℱ G}
          → m₁ ≃⇒ℱ m₂ → m₂ ≃⇒ℱ m₃ → m₁ ≃⇒ℱ m₃
-- Combination lemma for shape/position/unfold path equations
-- 形状/位置/展开路径等式的组合引理
combine-shape-eqs : ∀ {ℓ} (G : Cosmos ℓ) {O1 O2 O3 : Obj G}
                    {S1 : Shape G O1} {S2 : Shape G O2} {S3 : Shape G O3}
                    {pO1 : O1 ≡ O2} {pO2 : O2 ≡ O3}
                    (eqS1 : S1 ≡ subst (Shape G) (sym pO1) S2)
                    (eqS2 : S2 ≡ subst (Shape G) (sym pO2) S3)
                  → S1 ≡ subst (Shape G) (sym (trans pO1 pO2)) S3
combine-shape-eqs G {pO1 = pO1} {pO2 = pO2} eqS1 eqS2 =
  trans eqS1
    (trans (cong (subst (Shape G) (sym pO1)) eqS2)
           (subst-sym-comp pO1 pO2))
subst-pos-subst : ∀ {ℓ} (C : Cosmos ℓ) {X Y : Obj C} (eqO : X ≡ Y)
                → {s1 s2 : Shape C X} (eqSh : s1 ≡ s2) (p : Pos C s2)
                → subst-pos C eqO s1 (subst (Pos C {X}) (sym eqSh) p)
                ≡ subst (Pos C {Y}) (sym (cong (subst (Shape C) eqO) eqSh)) (subst-pos C eqO s2 p)
subst-pos-subst C refl refl p = refl
combine-pos-step1 : ∀ {ℓ} {G : Cosmos ℓ} {O1 O2 O3 : Obj G}
                  {S1 : Shape G O1} {S2 : Shape G O2} {S3 : Shape G O3}
                  {pO1 : O1 ≡ O2} {pO2 : O2 ≡ O3}
                  {eqS1 : S1 ≡ subst (Shape G) (sym pO1) S2}
                  {eqS2 : S2 ≡ subst (Shape G) (sym pO2) S3}
                  {p1 : Pos G S1} {p2 : Pos G S2} {p3 : Pos G S3}
                  → (eqP1 : p1 ≡ subst (Pos G {O1}) (sym eqS1) (subst-pos G (sym pO1) S2 p2))
                  → (eqP2 : p2 ≡ subst (Pos G {O2}) (sym eqS2) (subst-pos G (sym pO2) S3 p3))
                  → p1 ≡ subst (Pos G {O1}) (sym eqS1) 
                          (subst (Pos G {O1}) (sym (cong (subst (Shape G) (sym pO1)) eqS2))
                            (subst-pos G (sym pO1) (subst (Shape G) (sym pO2) S3) 
                              (subst-pos G (sym pO2) S3 p3)))
combine-pos-step1 {G = G} {O1 = O1} {O2 = O2} {O3 = O3}
                  {S1 = S1} {S2 = S2} {S3 = S3}
                  {pO1 = pO1} {pO2 = pO2}
                  {eqS1 = eqS1} {eqS2 = eqS2}
                  {p1 = p1} {p2 = p2} {p3 = p3} eqP1 eqP2 =
  trans eqP1
    (cong (subst (Pos G {O1}) (sym eqS1))
      (trans (cong (subst-pos G (sym pO1) S2) eqP2)
        (subst-pos-subst G (sym pO1) eqS2 (subst-pos G (sym pO2) S3 p3))))
subst-pos-comp : ∀ {ℓ} (D : Cosmos ℓ) {A B C : Obj D} (eq1 : A ≡ B) (eq2 : B ≡ C) (s : Shape D A) (p : Pos D s)
               → subst-pos D eq2 (subst (Shape D) eq1 s) (subst-pos D eq1 s p)
               ≡ subst (Pos D) (sym (subst-comp eq1 eq2)) (subst-pos D (trans eq1 eq2) s p)
subst-pos-comp D refl refl s p = refl
subst-pos-eq : ∀ {ℓ} (C : Cosmos ℓ) {X Y : Obj C} {eq1 eq2 : X ≡ Y} {s : Shape C X} (p : Pos C s)
             → (eq' : eq1 ≡ eq2)
             → subst (Pos C {Y}) (cong (λ eq → subst (Shape C) eq s) eq') 
                 (subst-pos C eq1 s p)
               ≡ subst-pos C eq2 s p
subst-pos-eq _ p refl = refl
combine-pos-step2 : ∀ {ℓ} {G : Cosmos ℓ} {O1 O2 O3 : Obj G}
                  {S3 : Shape G O3}
                  {pO1 : O1 ≡ O2} {pO2 : O2 ≡ O3}
                  {pO : O1 ≡ O3}
                  (sym-trans-eq : sym pO ≡ trans (sym pO2) (sym pO1))
                  (p3 : Pos G S3)
                  → subst-pos G (sym pO1) (subst (Shape G) (sym pO2) S3) (subst-pos G (sym pO2) S3 p3)
                  ≡ subst (Pos G {O1}) (sym (subst-comp (sym pO2) (sym pO1) {b = S3}))
                      (subst (Pos G {O1}) (cong (λ eq → subst (Shape G) eq S3) sym-trans-eq)
                        (subst-pos G (sym pO) S3 p3))
combine-pos-step2 {G = G} {O1 = O1} {O2 = O2} {O3 = O3}
                  {S3 = S3} {pO1 = pO1} {pO2 = pO2} {pO = pO} sym-trans-eq p3 =
  let
    eq' = sym sym-trans-eq
    f   = λ eq → subst (Shape G) eq S3
    eq1 = trans (sym pO2) (sym pO1)
    eq2 = sym pO
    pos-eq' : subst-pos G eq1 S3 p3 ≡ subst (Pos G {O1}) (sym (cong f eq')) (subst-pos G eq2 S3 p3)
    pos-eq' = subst-sym-swap (Pos G {O1}) (cong f eq') (subst-pos-eq G p3 eq')
    step1 : sym (cong (λ eq → subst (Shape G) eq S3) (sym sym-trans-eq)) 
          ≡ cong (λ eq → subst (Shape G) eq S3) (sym (sym sym-trans-eq))
    step1 = sym-cong {f = λ eq → subst (Shape G) eq S3} (sym sym-trans-eq)
    step2 : sym (sym sym-trans-eq) ≡ sym-trans-eq
    step2 = sym (sym-sym sym-trans-eq)
    simp : sym (cong (λ eq → subst (Shape G) eq S3) (sym sym-trans-eq)) 
         ≡ cong (λ eq → subst (Shape G) eq S3) sym-trans-eq
    simp = trans step1 (cong (cong (λ eq → subst (Shape G) eq S3)) step2)
  in
  trans (subst-pos-comp G (sym pO2) (sym pO1) S3 p3)
    (cong (subst (Pos G {O1}) (sym (subst-comp (sym pO2) (sym pO1) {b = S3})))
      (trans pos-eq'
             (cong (λ eq → subst (Pos G {O1}) eq (subst-pos G (sym pO) S3 p3)) simp)))
subst-sym-comp-bridge : ∀ {ℓ} {G : Cosmos ℓ} {O1 O2 O3 : Obj G}
                       {S3 : Shape G O3}
                       {pO1 : O1 ≡ O2} {pO2 : O2 ≡ O3}
                       (p3 : Pos G S3)
                     → subst (Pos G {O1}) (sym (subst-comp (sym pO2) (sym pO1) {b = S3}))
                          (subst (Pos G {O1}) (cong (λ eq → subst (Shape G) eq S3) (sym-trans pO1 pO2))
                            (subst-pos G (sym (trans pO1 pO2)) S3 p3))
                     ≡ subst (Pos G {O1}) (sym (subst-sym-comp pO1 pO2 {s = S3}))
                          (subst-pos G (sym (trans pO1 pO2)) S3 p3)
subst-sym-comp-bridge {ℓ} {G} {O1} {O2} {O3} {S3} {pO1} {pO2} p3 =
  let
    x : Pos G (subst (Shape G) (sym (trans pO1 pO2)) S3)
    x = subst-pos G (sym (trans pO1 pO2)) S3 p3
    eq1 : sym (trans pO1 pO2) ≡ trans (sym pO2) (sym pO1)
    eq1 = sym-trans pO1 pO2
    eq2 : subst (Shape G) (sym pO1) (subst (Shape G) (sym pO2) S3) 
        ≡ subst (Shape G) (trans (sym pO2) (sym pO1)) S3
    eq2 = subst-comp (sym pO2) (sym pO1) {b = S3}
    B : subst (Shape G) (sym (trans pO1 pO2)) S3 
      ≡ subst (Shape G) (trans (sym pO2) (sym pO1)) S3
    B = cong (λ eq → subst (Shape G) eq S3) eq1
    A : subst (Shape G) (trans (sym pO2) (sym pO1)) S3
      ≡ subst (Shape G) (sym pO1) (subst (Shape G) (sym pO2) S3)
    A = sym eq2
  in
  begin
    subst (Pos G {O1}) A (subst (Pos G {O1}) B x)
  ≡⟨ subst-comp B A {b = x} ⟩
    subst (Pos G {O1}) (trans B A) x
  ≡⟨ cong (λ eq → subst (Pos G {O1}) eq x) 
          (sym (sym-subst-sym-comp {f = Shape G} pO1 pO2 {s = S3})) ⟩
    subst (Pos G {O1}) (sym (subst-sym-comp pO1 pO2 {s = S3})) x
  ∎
combine-pos-eqs : ∀ {ℓ} (G : Cosmos ℓ) {O1 O2 O3 : Obj G}
                  {S1 : Shape G O1} {S2 : Shape G O2} {S3 : Shape G O3}
                  {pO1 : O1 ≡ O2} {pO2 : O2 ≡ O3}
                  (eqS1 : S1 ≡ subst (Shape G) (sym pO1) S2)
                  (eqS2 : S2 ≡ subst (Shape G) (sym pO2) S3)
                  (p3 : Pos G S3)
                → subst (Pos G) (sym eqS1)
                    (subst (Pos G) (sym (cong (subst (Shape G) (sym pO1)) eqS2))
                      (subst (Pos G) (sym (subst-sym-comp pO1 pO2))
                        (subst-pos G (sym (trans pO1 pO2)) S3 p3)))
                ≡ subst (Pos G) (sym (combine-shape-eqs G eqS1 eqS2))
                    (subst-pos G (sym (trans pO1 pO2)) S3 p3)
combine-pos-eqs G {pO1 = pO1} {pO2 = pO2} eqS1 eqS2 p3 =
  subst-sym-comp3 eqS1
                  (cong (subst (Shape G) (sym pO1)) eqS2)
                  (subst-sym-comp pO1 pO2)
                  {b = subst-pos G (sym (trans pO1 pO2)) _ p3}
combine-pos-eq : ∀ {ℓ} {F G : Cosmos ℓ} {m₁ m₂ m₃ : F ⇒ℱ G}
               → (h1 : m₁ ≃⇒ℱ m₂) (h2 : m₂ ≃⇒ℱ m₃)
               → ∀ {A : Obj F} {s : Shape F A} (p : Pos F s)
               → onPos m₁ p ≡ subst (Pos G {onObj m₁ A}) (sym (combine-shape-eqs G (h1 .onShape-eq s) (h2 .onShape-eq s)))
                                   (subst-pos G (sym (trans (onObj-eq h1 A) (onObj-eq h2 A)))
                                               (onShape m₃ s) (onPos m₃ p))
combine-pos-eq {ℓ} {F} {G} {m₁} {m₂} {m₃} h1 h2 {A} {s} p =
  let
    pO1  = onObj-eq h1 A
    pO2  = onObj-eq h2 A
    eqS1 = onShape-eq h1 s
    eqS2 = onShape-eq h2 s
    O1   = onObj m₁ A
    O2   = onObj m₂ A
    O3   = onObj m₃ A
    S1   = onShape m₁ s
    S2   = onShape m₂ s
    S3   = onShape m₃ s
    p1   = onPos m₁ p
    p2   = onPos m₂ p
    p3   = onPos m₃ p
    Z    = subst-pos G (sym (trans pO1 pO2)) S3 p3
    X    = subst-pos G (sym pO1) (subst (Shape G) (sym pO2) S3) (subst-pos G (sym pO2) S3 p3)
    step1 : p1 ≡ subst (Pos G) (sym eqS1)
                 (subst (Pos G) (sym (cong (subst (Shape G) (sym pO1)) eqS2)) X)
    step1 = combine-pos-step1 {ℓ = ℓ} {G = G}
              {O1 = O1} {O2 = O2} {O3 = O3}
              {S1 = S1} {S2 = S2} {S3 = S3}
              {pO1 = pO1} {pO2 = pO2}
              {eqS1 = eqS1} {eqS2 = eqS2}
              {p1 = p1} {p2 = p2} {p3 = p3}
              (onPos-eq h1 p) (onPos-eq h2 p)
    step2 : X ≡ subst (Pos G) (sym (subst-sym-comp pO1 pO2)) Z
    step2 = trans
              (combine-pos-step2 {ℓ = ℓ} {G = G}
                 {O1 = O1} {O2 = O2} {O3 = O3} {S3 = S3}
                 {pO1 = pO1} {pO2 = pO2} {pO = trans pO1 pO2}
                 (sym-trans pO1 pO2) p3)
              (subst-sym-comp-bridge {ℓ = ℓ} {G = G}
                 {O1 = O1} {O2 = O2} {O3 = O3} {S3 = S3}
                 {pO1 = pO1} {pO2 = pO2} p3)
    step3 : p1 ≡ subst (Pos G) (sym eqS1)
                 (subst (Pos G) (sym (cong (subst (Shape G) (sym pO1)) eqS2))
                   (subst (Pos G) (sym (subst-sym-comp pO1 pO2)) Z))
    step3 = trans step1
              (cong (λ x → subst (Pos G) (sym eqS1)
                           (subst (Pos G) (sym (cong (subst (Shape G) (sym pO1)) eqS2)) x))
               step2)
  in
  trans step3
    (combine-pos-eqs G
      {O1 = O1} {O2 = O2} {O3 = O3}
      {S1 = S1} {S2 = S2} {S3 = S3}
      {pO1 = pO1} {pO2 = pO2}
      eqS1 eqS2 p3)
subst-≃⇒ℱ : ∀ ℓ (F : Cosmos ℓ) (C₁ C₂ : Cosmos ℓ) (eq : C₁ ≡ C₂)
          → {m₁ m₂ : F ⇒ℱ C₁} → m₁ ≃⇒ℱ m₂
          → subst (λ C → F ⇒ℱ C) eq m₁ ≃⇒ℱ subst (λ C → F ⇒ℱ C) eq m₂
subst-≃⇒ℱ ℓ F C₁ C₂ eq {m₁} {m₂} e =
  J (λ C₂' eq' → subst (λ C → F ⇒ℱ C) eq' m₁ ≃⇒ℱ subst (λ C → F ⇒ℱ C) eq' m₂)
    eq
        e
≡-right-≃⇒ℱ : ∀ {ℓ} {F G : Cosmos ℓ} {a b c : F ⇒ℱ G}
            → a ≃⇒ℱ b → b ≡ c → a ≃⇒ℱ c
≡-right-≃⇒ℱ {a = a} h eq = subst (λ x → a ≃⇒ℱ x) eq h
combine-unfold-path : ∀ {ℓ} {F G : Cosmos ℓ} {m₁ m₂ m₃ : F ⇒ℱ G}
                   → (h1 : m₁ ≃⇒ℱ m₂) (h2 : m₂ ≃⇒ℱ m₃)
                   → ∀ {A : Obj F} (s : Shape F A)
                   → let O₁ = onObj m₁ A
                         O₂ = onObj m₂ A
                         O₃ = onObj m₃ A
                         S₁ = onShape m₁ s
                         S₂ = onShape m₂ s
                         S₃ = onShape m₃ s
                         eqO₁ = onObj-eq h1 A
                         eqO₂ = onObj-eq h2 A
                         eqS₁ = onShape-eq h1 s
                         eqS₂ = onShape-eq h2 s
                         path₁ = trans (subst-unfold G (sym eqO₁) S₂) 
                                       (cong (unfold G {O₁}) (sym eqS₁))
                         path₂ = trans (subst-unfold G (sym eqO₂) S₃) 
                                       (cong (unfold G {O₂}) (sym eqS₂))
                         path₁₂ = trans (subst-unfold G (sym (trans eqO₁ eqO₂)) S₃) 
                                        (cong (unfold G {O₁}) (sym (combine-shape-eqs G (h1 .onShape-eq s) (h2 .onShape-eq s))))
                     in trans path₂ path₁ ≡ path₁₂
combine-unfold-path {ℓ} {F} {G} {m₁} {m₂} {m₃} h1 h2 {A} s = 
  helper (onObj-eq h1 A) (onObj-eq h2 A) (onShape-eq h1 s) (onShape-eq h2 s)
  where
  helper : ∀ {O₁ O₂ O₃ : Obj G} {S₁ : Shape G O₁} {S₂ : Shape G O₂} {S₃ : Shape G O₃}
         → (eqO₁ : O₁ ≡ O₂) (eqO₂ : O₂ ≡ O₃)
         → (eqS₁ : S₁ ≡ subst (Shape G) (sym eqO₁) S₂)
         → (eqS₂ : S₂ ≡ subst (Shape G) (sym eqO₂) S₃)
         → let path₁ = trans (subst-unfold G (sym eqO₁) S₂) (cong (unfold G {O₁}) (sym eqS₁))
               path₂ = trans (subst-unfold G (sym eqO₂) S₃) (cong (unfold G {O₂}) (sym eqS₂))
               combine-shape = trans eqS₁ (trans (cong (subst (Shape G) (sym eqO₁)) eqS₂) (subst-sym-comp eqO₁ eqO₂ {s = S₃}))
               path₁₂ = trans (subst-unfold G (sym (trans eqO₁ eqO₂)) S₃) (cong (unfold G {O₁}) (sym combine-shape))
           in trans path₂ path₁ ≡ path₁₂
  helper refl refl refl refl = refl
trans-≃⇒ℱ {ℓ} {F} {G} {m₁} {m₂} {m₃} h1 h2 .onObj-eq A =
  trans (h1 .onObj-eq A) (h2 .onObj-eq A)
trans-≃⇒ℱ {ℓ} {F} {G} {m₁} {m₂} {m₃} h1 h2 .onShape-eq {A} s =
  subst-sym-eq-trans (Shape G)
                     (h1 .onObj-eq A) (h2 .onObj-eq A)
                     (h1 .onShape-eq s) (h2 .onShape-eq s)
trans-≃⇒ℱ {ℓ} {F} {G} {m₁} {m₂} {m₃} h1 h2 .onPos-eq {A} {s} p =
  combine-pos-eq h1 h2 p
trans-≃⇒ℱ {ℓ} {F} {G} {m₁} {m₂} {m₃} h1 h2 .onHom-eq {A} {B} f =
  subst₂-sym-eq-trans (Hom G)
                      (h1 .onObj-eq A) (h1 .onObj-eq B)
                      (h2 .onObj-eq A) (h2 .onObj-eq B)
                      (h1 .onHom-eq f) (h2 .onHom-eq f)
trans-≃⇒ℱ {ℓ} {F} {G} {m₁} {m₂} {m₃} h1 h2 .onunfold-eq {A} s =
  let
    eqO1 = h1 .onObj-eq A
    eqO2 = h2 .onObj-eq A
    eqS1 = h1 .onShape-eq s
    eqS2 = h2 .onShape-eq s
    path1 = trans (subst-unfold G (sym eqO1) (m₂ .onShape s)) (cong (unfold G) (sym eqS1))
    path2 = trans (subst-unfold G (sym eqO2) (m₃ .onShape s)) (cong (unfold G) (sym eqS2))
    P = λ C → unfold F s ⇒ℱ C
    bisim1 : _≃⇒ℱ_ {ℓ = ℓ} {F = unfold F s} {G = unfold G (m₁ .onShape s)}
               (m₁ .onunfold s)
               (subst P path1 (m₂ .onunfold s))
    bisim1 = h1 .onunfold-eq s
    bisim2 : _≃⇒ℱ_ {ℓ = ℓ} {F = unfold F s} {G = unfold G (m₂ .onShape s)}
               (m₂ .onunfold s)
               (subst P path2 (m₃ .onunfold s))
    bisim2 = h2 .onunfold-eq s
    bisim2_trans : _≃⇒ℱ_ {ℓ = ℓ} {F = unfold F s} {G = unfold G (m₁ .onShape s)}
                     (subst P path1 (m₂ .onunfold s))
                     (subst P path1 (subst P path2 (m₃ .onunfold s)))
    bisim2_trans = subst-≃⇒ℱ ℓ (unfold F s) _ _ path1 bisim2
    eqSub : subst P (trans path2 path1) (m₃ .onunfold s) ≡ subst P path1 (subst P path2 (m₃ .onunfold s))
    eqSub = subst-comb P path2 path1 (m₃ .onunfold s)
    bisim2_comb : _≃⇒ℱ_ {ℓ = ℓ} {F = unfold F s} {G = unfold G (m₁ .onShape s)}
                    (subst P path1 (m₂ .onunfold s))
                    (subst P (trans path2 path1) (m₃ .onunfold s))
    bisim2_comb = ≡-right-≃⇒ℱ bisim2_trans (sym eqSub)
    path₁₂ : unfold G (m₃ .onShape s) ≡ unfold G (m₁ .onShape s)
    path₁₂ = trans (subst-unfold G (sym (trans eqO1 eqO2)) (m₃ .onShape s)) 
                   (cong (unfold G) (sym (combine-shape-eqs G (h1 .onShape-eq s) (h2 .onShape-eq s))))
    path-eq : trans path2 path1 ≡ path₁₂
    path-eq = combine-unfold-path h1 h2 s
    bisim2_final : _≃⇒ℱ_ {ℓ = ℓ} {F = unfold F s} {G = unfold G (m₁ .onShape s)}
                     (subst P path1 (m₂ .onunfold s))
                     (subst P path₁₂ (m₃ .onunfold s))
    bisim2_final = ≡-right-≃⇒ℱ bisim2_comb (cong (λ p → subst P p (m₃ .onunfold s)) path-eq)
  in
    trans-≃⇒ℱ {ℓ = ℓ} {F = unfold F s} {G = unfold G (m₁ .onShape s)} bisim1 bisim2_final

-- Associativity of homomorphism composition (up to equivalence)
-- 同态复合的结合律（up to equivalence）
assoc-⇒ℱ : ∀ {ℓ} {F G H I : Cosmos ℓ} 
           (f : F ⇒ℱ G) (g : G ⇒ℱ H) (h : H ⇒ℱ I)
         → ((h ∘⇒ℱ g) ∘⇒ℱ f) ≃⇒ℱ (h ∘⇒ℱ (g ∘⇒ℱ f))
assoc-⇒ℱ {ℓ} {F} {G} {H} {I} f g h .onObj-eq A = refl
assoc-⇒ℱ {ℓ} {F} {G} {H} {I} f g h .onShape-eq s = refl
assoc-⇒ℱ {ℓ} {F} {G} {H} {I} f g h .onPos-eq p = refl
assoc-⇒ℱ {ℓ} {F} {G} {H} {I} f g h .onHom-eq k = refl
assoc-⇒ℱ {ℓ} {F} {G} {H} {I} f g h .onunfold-eq s = 
  assoc-⇒ℱ {ℓ} 
    {F = unfold F s} 
    {G = unfold G (onShape f s)} 
    {H = unfold H (onShape g (onShape f s))} 
    {I = unfold I (onShape h (onShape g (onShape f s)))}
    (onunfold f s) 
    (onunfold g (onShape f s)) 
    (onunfold h (onShape g (onShape f s)))

-- Left/Right unit law (up to equivalence)
-- 左/右单位律（up to equivalence）
id-l-≃⇒ℱ : ∀ {ℓ} {F G : Cosmos ℓ} (f : F ⇒ℱ G)
         → id⇒ℱ ∘⇒ℱ f ≃⇒ℱ f
id-l-≃⇒ℱ f .onObj-eq A   = refl
id-l-≃⇒ℱ f .onShape-eq s = refl
id-l-≃⇒ℱ f .onPos-eq p   = refl
id-l-≃⇒ℱ f .onHom-eq h   = refl
id-l-≃⇒ℱ f .onunfold-eq s = id-l-≃⇒ℱ (onunfold f s)

id-r-≃⇒ℱ : ∀ {ℓ} {F G : Cosmos ℓ} (f : F ⇒ℱ G)
         → f ∘⇒ℱ id⇒ℱ ≃⇒ℱ f
id-r-≃⇒ℱ f .onObj-eq A   = refl
id-r-≃⇒ℱ f .onShape-eq s = refl
id-r-≃⇒ℱ f .onPos-eq p   = refl
id-r-≃⇒ℱ f .onHom-eq h   = refl
id-r-≃⇒ℱ f .onunfold-eq s = id-r-≃⇒ℱ (onunfold f s)

-- Bisimulation equivalence between Cosmos structures
-- Cosmos 之间的双模拟等价关系
record _≃_ {ℓ} (C D : Cosmos ℓ) : Set (lsuc (lsuc ℓ)) where
  coinductive
  field
    Obj-R : Obj C → Obj D → Set (lsuc ℓ)
    Shape-R : (A : Obj C) (A' : Obj D)
            → Obj-R A A'
            → Shape C A → Shape D A' → Set (lsuc ℓ)
    Pos-R : (A : Obj C) (A' : Obj D)
          → (Rₒ : Obj-R A A')
          → (s : Shape C A) (s' : Shape D A')
          → Shape-R A A' Rₒ s s'
          → Pos C s → Pos D s' → Set (lsuc ℓ)
    Hom-R : (A : Obj C) (A' : Obj D) (B : Obj C) (B' : Obj D)
          → Obj-R A A'
          → Obj-R B B'
          → Hom C A B → Hom D A' B' → Set (lsuc ℓ)
    id-preserve : (A : Obj C) (A' : Obj D) (Rₒ : Obj-R A A')
                → Hom-R A A' A A' Rₒ Rₒ (idHom C {A}) (idHom D {A = A'})
    comp-preserve : (A : Obj C) (A' : Obj D) (B : Obj C) (B' : Obj D) (X : Obj C) (X' : Obj D)
                  → (R₁ : Obj-R A A')
                  → (R₂ : Obj-R B B')
                  → (R₃ : Obj-R X X')
                  → (f : Hom C A B) (f' : Hom D A' B')
                  → (g : Hom C B X) (g' : Hom D B' X')
                  → (hf : Hom-R A A' B B' R₁ R₂ f f')
                  → (hg : Hom-R B B' X X' R₂ R₃ g g')
                  → Hom-R A A' X X' R₁ R₃ (comp C f g) (comp D f' g')
    actS-preserve : (A : Obj C) (A' : Obj D) (B : Obj C) (B' : Obj D)
                  → (R₁ : Obj-R A A')
                  → (R₂ : Obj-R B B')
                  → (f : Hom C A B) (f' : Hom D A' B')
                  → (s : Shape C A) (s' : Shape D A')
                  → (hf : Hom-R A A' B B' R₁ R₂ f f')
                  → (hs : Shape-R A A' R₁ s s')
                  → Shape-R B B' R₂ (actS C f s) (actS D f' s')
    actP-preserve : (A : Obj C) (A' : Obj D) (B : Obj C) (B' : Obj D)
                  → (R₁ : Obj-R A A')
                  → (R₂ : Obj-R B B')
                  → (f : Hom C A B) (f' : Hom D A' B')
                  → (s : Shape C A) (s' : Shape D A')
                  → (p : Pos C (actS C f s)) (p' : Pos D (actS D f' s'))
                  → (hf : Hom-R A A' B B' R₁ R₂ f f')
                  → (hs : Shape-R A A' R₁ s s')
                  → (hp : Pos-R B B' R₂ (actS C f s) (actS D f' s') 
                          (actS-preserve A A' B B' R₁ R₂ f f' s s' hf hs) p p')
                  → Pos-R A A' R₁ s s' hs (actP C f s p) (actP D f' s' p')
    unfold-obj-preserve : (A : Obj C) (A' : Obj D)
                        → (Rₒ : Obj-R A A')
                        → (s : Shape C A) (s' : Shape D A')
                        → (hs : Shape-R A A' Rₒ s s')
                        → Obj-R (unfold-obj C s) (unfold-obj D s')
    pos-to-shape-preserve : (A : Obj C) (A' : Obj D)
                          → (Rₒ : Obj-R A A')
                          → (s : Shape C A) (s' : Shape D A')
                          → (hs : Shape-R A A' Rₒ s s')
                          → (p : Pos C s) (p' : Pos D s')
                          → (hp : Pos-R A A' Rₒ s s' hs p p')
                          → Shape-R (unfold-obj C s) (unfold-obj D s')
                                     (unfold-obj-preserve A A' Rₒ s s' hs)
                                     (pos-to-shape C s p)
                                     (pos-to-shape D s' p')
    unfold-bisim : (A : Obj C) (A' : Obj D)
                 → (Rₒ : Obj-R A A')
                 → (s : Shape C A) (s' : Shape D A')
                 → (hs : Shape-R A A' Rₒ s s')
                 → unfold C s ≃ unfold D s'
open _≃_ public

-- Reflexivity / Symmetry / Transitivity of bisimulation equivalence
-- 双模拟等价的自反性 / 对称性 / 传递性
refl-≃ : ∀ {ℓ} (C : Cosmos ℓ) → C ≃ C
refl-≃ C = λ where
  .Obj-R                A  A' → A ≡ A'
  .Shape-R              A .A refl s s' → s ≡ s'
  .Pos-R                A .A refl s .s refl p p' → p ≡ p'
  .Hom-R                A .A B .B refl refl f f' → f ≡ f'
  .id-preserve          A .A refl → refl
  .comp-preserve        A .A B .B X .X refl refl refl f .f g .g refl refl → refl
  .actS-preserve        A .A B .B refl refl f .f s .s refl refl → refl
  .actP-preserve        A .A B .B refl refl f .f s .s p .p refl refl refl → refl
  .unfold-obj-preserve  A .A refl s .s refl → refl
  .pos-to-shape-preserve A .A refl s .s refl p .p refl → refl
  .unfold-bisim         A .A refl s .s refl → refl-≃ (unfold C s)

≡→≃ : ∀ {ℓ} {C D : Cosmos ℓ} → C ≡ D → C ≃ D
≡→≃ refl = refl-≃ _

sym-≃ : ∀ {ℓ} {C D : Cosmos ℓ} → C ≃ D → D ≃ C
sym-≃ h .Obj-R                A' A = h .Obj-R A A'
sym-≃ h .Shape-R              A' A Rₒ s' s = h .Shape-R A A' Rₒ s s'
sym-≃ h .Pos-R                A' A Rₒ s' s Rₛ p' p = h .Pos-R A A' Rₒ s s' Rₛ p p'
sym-≃ h .Hom-R                A' A B' B R₁ R₂ f' f = h .Hom-R A A' B B' R₁ R₂ f f'
sym-≃ h .id-preserve          A' A Rₒ = h .id-preserve A A' Rₒ
sym-≃ h .comp-preserve        A' A B' B X' X R₁ R₂ R₃ f' f g' g hf hg = h .comp-preserve A A' B B' X X' R₁ R₂ R₃ f f' g g' hf hg
sym-≃ h .actS-preserve        A' A B' B R₁ R₂ f' f s' s hf hs = h .actS-preserve A A' B B' R₁ R₂ f f' s s' hf hs
sym-≃ h .actP-preserve        A' A B' B R₁ R₂ f' f s' s p' p hf hs hp = h .actP-preserve A A' B B' R₁ R₂ f f' s s' p p' hf hs hp
sym-≃ h .unfold-obj-preserve  A' A Rₒ s' s hs = h .unfold-obj-preserve A A' Rₒ s s' hs
sym-≃ h .pos-to-shape-preserve A' A Rₒ s' s hs p' p hp = h .pos-to-shape-preserve A A' Rₒ s s' hs p p' hp
sym-≃ h .unfold-bisim         A' A Rₒ s' s hs = sym-≃ (h .unfold-bisim A A' Rₒ s s' hs)

trans-≃ : ∀ {ℓ} {C D E : Cosmos ℓ} → C ≃ D → D ≃ E → C ≃ E
Rel : ∀ {ℓ} (C D E : Cosmos ℓ) (h1 : C ≃ D) (h2 : D ≃ E) → Obj C → Obj E → Set (lsuc ℓ)
Rel C D E h1 h2 A A' = Σ[ B ∈ Obj D ] (h1 .Obj-R A B × h2 .Obj-R B A')
shape-R-trans : {ℓ : Level} (C D E : Cosmos ℓ) (h1 : C ≃ D) (h2 : D ≃ E)
                (A : Obj C) (A' : Obj E) (R : Rel C D E h1 h2 A A')
              → Shape C A → Shape E A' → Set (lsuc ℓ)
shape-R-trans C D E h1 h2 A A' (B , rel1 , rel2) s s' =
  Σ[ t ∈ Shape D B ] (h1 .Shape-R A B rel1 s t × h2 .Shape-R B A' rel2 t s')
pos-R-trans : {ℓ : Level} (C D E : Cosmos ℓ) (h1 : C ≃ D) (h2 : D ≃ E)
              (A : Obj C) (A' : Obj E) (R : Rel C D E h1 h2 A A')
              (s : Shape C A) (s' : Shape E A') (hs : shape-R-trans C D E h1 h2 A A' R s s')
              (p : Pos C s) (p' : Pos E s') → Set (lsuc ℓ)
pos-R-trans C D E h1 h2 A A' (B , rel1 , rel2) s s' (t , Rs1 , Rs2) p p' =
  Σ[ q ∈ Pos D t ] (h1 .Pos-R A B rel1 s t Rs1 p q × h2 .Pos-R B A' rel2 t s' Rs2 q p')
hom-R-trans : {ℓ : Level} (C D E : Cosmos ℓ) (h1 : C ≃ D) (h2 : D ≃ E)
              (A : Obj C) (A' : Obj E) (B : Obj C) (B' : Obj E)
              (R₁ : Rel C D E h1 h2 A A') (R₂ : Rel C D E h1 h2 B B')
              (f : Hom C A B) (f' : Hom E A' B') → Set (lsuc ℓ)
hom-R-trans C D E h1 h2 A A' B B' (B1 , rel1 , rel2) (B2 , rel3 , rel4) f f' =
  Σ[ g ∈ Hom D B1 B2 ] (h1 .Hom-R A B1 B B2 rel1 rel3 f g × h2 .Hom-R B1 A' B2 B' rel2 rel4 g f')
id-preserve-trans : {ℓ : Level} (C D E : Cosmos ℓ) (h1 : C ≃ D) (h2 : D ≃ E)
                    (A : Obj C) (A' : Obj E) (R : Rel C D E h1 h2 A A')
                  → hom-R-trans C D E h1 h2 A A' A A' R R (idHom C) (idHom E)
id-preserve-trans C D E h1 h2 A A' (B , rel1 , rel2) =
  (idHom D {B} , h1 .id-preserve A B rel1 , h2 .id-preserve B A' rel2)
comp-preserve-trans : {ℓ : Level} (C D E : Cosmos ℓ) (h1 : C ≃ D) (h2 : D ≃ E)
                      (A : Obj C) (A' : Obj E) (B : Obj C) (B' : Obj E) (X : Obj C) (X' : Obj E)
                      (R₁ : Rel C D E h1 h2 A A') (R₂ : Rel C D E h1 h2 B B') (R₃ : Rel C D E h1 h2 X X')
                      (f : Hom C A B) (f' : Hom E A' B')
                      (g : Hom C B X) (g' : Hom E B' X')
                      (hf : hom-R-trans C D E h1 h2 A A' B B' R₁ R₂ f f')
                      (hg : hom-R-trans C D E h1 h2 B B' X X' R₂ R₃ g g')
                    → hom-R-trans C D E h1 h2 A A' X X' R₁ R₃ (comp C f g) (comp E f' g')
comp-preserve-trans C D E h1 h2 A A' B B' X X' (B1 , rel1 , rel2) (B2 , rel3 , rel4) (Bx , rel5 , rel6)
                     f f' g g' (gf , hf1 , hf2) (gg , hg1 , hg2) =
  ( comp D gf gg
  , h1 .comp-preserve A B1 B B2 X Bx rel1 rel3 rel5 f gf g gg hf1 hg1
  , h2 .comp-preserve B1 A' B2 B' Bx X' rel2 rel4 rel6 gf f' gg g' hf2 hg2
  )
actS-preserve-trans : {ℓ : Level} (C D E : Cosmos ℓ) (h1 : C ≃ D) (h2 : D ≃ E)
                      (A : Obj C) (A' : Obj E) (B : Obj C) (B' : Obj E)
                      (R₁ : Rel C D E h1 h2 A A') (R₂ : Rel C D E h1 h2 B B')
                      (f : Hom C A B) (f' : Hom E A' B')
                      (s : Shape C A) (s' : Shape E A')
                      (hf : hom-R-trans C D E h1 h2 A A' B B' R₁ R₂ f f')
                      (hs : shape-R-trans C D E h1 h2 A A' R₁ s s')
                    → shape-R-trans C D E h1 h2 B B' R₂ (actS C f s) (actS E f' s')
actS-preserve-trans C D E h1 h2 A A' B B' (B1 , rel1 , rel2) (B2 , rel3 , rel4) f f' s s'
                     (gf , hf1 , hf2) (t , Rs1 , Rs2) =
  ( actS D gf t
  , h1 .actS-preserve A B1 B B2 rel1 rel3 f gf s t hf1 Rs1
  , h2 .actS-preserve B1 A' B2 B' rel2 rel4 gf f' t s' hf2 Rs2
  )
actP-preserve-trans : {ℓ : Level} (C D E : Cosmos ℓ) (h1 : C ≃ D) (h2 : D ≃ E)
                      (A : Obj C) (A' : Obj E) (B : Obj C) (B' : Obj E)
                      (R₁ : Rel C D E h1 h2 A A') (R₂ : Rel C D E h1 h2 B B')
                      (f : Hom C A B) (f' : Hom E A' B')
                      (s : Shape C A) (s' : Shape E A')
                      (p : Pos C (actS C f s)) (p' : Pos E (actS E f' s'))
                      (hf : hom-R-trans C D E h1 h2 A A' B B' R₁ R₂ f f')
                      (hs : shape-R-trans C D E h1 h2 A A' R₁ s s')
                      (hp : pos-R-trans C D E h1 h2 B B' R₂ (actS C f s) (actS E f' s')
                              (actS-preserve-trans C D E h1 h2 A A' B B' R₁ R₂ f f' s s' hf hs) p p')
                    → pos-R-trans C D E h1 h2 A A' R₁ s s' hs (actP C f s p) (actP E f' s' p')
actP-preserve-trans C D E h1 h2 A A' B B' (B1 , rel1 , rel2) (B2 , rel3 , rel4) f f' s s' p p'
                     (gf , hf1 , hf2) (t , Rs1 , Rs2) (q , hp1 , hp2) =
  ( actP D gf t q
  , h1 .actP-preserve A B1 B B2 rel1 rel3 f gf s t p q hf1 Rs1 hp1
  , h2 .actP-preserve B1 A' B2 B' rel2 rel4 gf f' t s' q p' hf2 Rs2 hp2
  )
unfold-obj-preserve-trans : {ℓ : Level} (C D E : Cosmos ℓ) (h1 : C ≃ D) (h2 : D ≃ E)
                            (A : Obj C) (A' : Obj E) (R : Rel C D E h1 h2 A A')
                            (s : Shape C A) (s' : Shape E A')
                            (hs : shape-R-trans C D E h1 h2 A A' R s s')
                          → Rel C D E h1 h2 (unfold-obj C s) (unfold-obj E s')
unfold-obj-preserve-trans C D E h1 h2 A A' (B , rel1 , rel2) s s' (t , Rs1 , Rs2) =
  ( unfold-obj D t
  , h1 .unfold-obj-preserve A B rel1 s t Rs1
  , h2 .unfold-obj-preserve B A' rel2 t s' Rs2
  )
pos-to-shape-preserve-trans : {ℓ : Level} (C D E : Cosmos ℓ) (h1 : C ≃ D) (h2 : D ≃ E)
                              (A : Obj C) (A' : Obj E) (R : Rel C D E h1 h2 A A')
                              (s : Shape C A) (s' : Shape E A')
                              (hs : shape-R-trans C D E h1 h2 A A' R s s')
                              (p : Pos C s) (p' : Pos E s')
                              (hp : pos-R-trans C D E h1 h2 A A' R s s' hs p p')
                            → shape-R-trans C D E h1 h2 (unfold-obj C s) (unfold-obj E s')
                                  (unfold-obj-preserve-trans C D E h1 h2 A A' R s s' hs)
                                  (pos-to-shape C s p) (pos-to-shape E s' p')
pos-to-shape-preserve-trans C D E h1 h2 A A' (B , rel1 , rel2) s s' (t , Rs1 , Rs2) p p' (q , hp1 , hp2) =
  ( pos-to-shape D t q
  , h1 .pos-to-shape-preserve A B rel1 s t Rs1 p q hp1
  , h2 .pos-to-shape-preserve B A' rel2 t s' Rs2 q p' hp2
  )
trans-≃ {C = C} {D = D} {E = E} h1 h2 .Obj-R = Rel C D E h1 h2
trans-≃ {C = C} {D = D} {E = E} h1 h2 .Shape-R = shape-R-trans C D E h1 h2
trans-≃ {C = C} {D = D} {E = E} h1 h2 .Pos-R = pos-R-trans C D E h1 h2
trans-≃ {C = C} {D = D} {E = E} h1 h2 .Hom-R = hom-R-trans C D E h1 h2
trans-≃ {C = C} {D = D} {E = E} h1 h2 .id-preserve = id-preserve-trans C D E h1 h2
trans-≃ {C = C} {D = D} {E = E} h1 h2 .comp-preserve = comp-preserve-trans C D E h1 h2
trans-≃ {C = C} {D = D} {E = E} h1 h2 .actS-preserve = actS-preserve-trans C D E h1 h2
trans-≃ {C = C} {D = D} {E = E} h1 h2 .actP-preserve = actP-preserve-trans C D E h1 h2
trans-≃ {C = C} {D = D} {E = E} h1 h2 .unfold-obj-preserve = unfold-obj-preserve-trans C D E h1 h2
trans-≃ {C = C} {D = D} {E = E} h1 h2 .pos-to-shape-preserve = pos-to-shape-preserve-trans C D E h1 h2
trans-≃ {C = C} {D = D} {E = E} h1 h2 .unfold-bisim A A' (B , rel1 , rel2) s s' (t , Rs1 , Rs2) =
  trans-≃ (h1 .unfold-bisim A B rel1 s t Rs1)
          (h2 .unfold-bisim B A' rel2 t s' Rs2)

-- Base functor definition for Cosmos
-- Cosmos 的基础函子定义
module CosmosF-Definition where
  record CosmosF (ℓ : Level) (X : Set (lsuc (lsuc ℓ))) : Set (lsuc (lsuc ℓ)) where
    field
      Obj        : Set (lsuc ℓ)
      Shape      : Obj → Set (lsuc ℓ)
      Pos        : {A : Obj} → Shape A → Set (lsuc ℓ)
      Hom        : (A B : Obj) → Set (lsuc ℓ)
      idHom      : {A : Obj} → Hom A A
      comp       : {A B C : Obj} → Hom A B → Hom B C → Hom A C
      comp-assoc : {A B C D : Obj} (f : Hom A B) (g : Hom B C) (h : Hom C D)
                 → comp (comp f g) h ≡ comp f (comp g h)
      id-comp-l  : {A B : Obj} (f : Hom A B) → comp idHom f ≡ f
      id-comp-r  : {A B : Obj} (f : Hom A B) → comp f idHom ≡ f
      actS       : {A B : Obj} → Hom A B → Shape A → Shape B
      actP       : {A B : Obj} (f : Hom A B) (s : Shape A) → Pos (actS f s) → Pos s
      actS-id    : {A : Obj} (s : Shape A) → actS idHom s ≡ s
      actS-comp  : {A B C : Obj} (f : Hom A B) (g : Hom B C) (s : Shape A)
                 → actS (comp f g) s ≡ actS g (actS f s)
      actP-id    : {A : Obj} (s : Shape A) (p : Pos (actS idHom s))
                 → actP idHom s p ≡ subst Pos (actS-id s) p
      actP-comp  : {A B C : Obj} (f : Hom A B) (g : Hom B C) (s : Shape A) (p : Pos (actS (comp f g) s))
                 → actP (comp f g) s p ≡ actP f s (actP g (actS f s) (subst Pos (actS-comp f g s) p))
      unfold      : {A : Obj} → Shape A → X
      unfold-obj  : {A : Obj} → Shape A → Obj
      unfold-hom  : {A B : Obj} (f : Hom A B) (s : Shape A)
                  → Hom (unfold-obj s) (unfold-obj (actS f s))
      unfold-hom-id : {A : Obj} (s : Shape A)
                    → unfold-hom idHom s
                    ≡ subst (λ Y → Hom (unfold-obj s) (unfold-obj Y))
                            (sym (actS-id s))
                            (idHom {A = unfold-obj s})
      unfold-hom-comp : {A B C : Obj} (f : Hom A B) (g : Hom B C) (s : Shape A)
                      → unfold-hom (comp f g) s
                      ≡ subst (λ Y → Hom (unfold-obj s) (unfold-obj Y))
                              (sym (actS-comp f g s))
                              (comp (unfold-hom f s) (unfold-hom g (actS f s)))
      pos-to-shape : {A : Obj} (s : Shape A) → Pos s → Shape (unfold-obj s)
      pos-actS-compat : {A B : Obj} (f : Hom A B) (s : Shape A) (p : Pos (actS f s))
                      → pos-to-shape (actS f s) p ≡ actS (unfold-hom f s) (pos-to-shape s (actP f s p))
  open CosmosF public

  subst-Pos : ∀ (ℓ : Level) (X : Set (lsuc (lsuc ℓ))) (C : CosmosF ℓ X) (A A' : Obj C) (eq : A ≡ A') (s : Shape C A) (p : Pos C s)
            → Pos C (subst (Shape C) eq s)
  subst-Pos ℓ X C A .A refl s p = p
  subst-cong-actP : ∀ (ℓ : Level) (X : Set (lsuc (lsuc ℓ))) (C : CosmosF ℓ X) (A B : Obj C) (f : Hom C A B) (s s' : Shape C A)
                  → (eq : s ≡ s') (p : Pos C (actS C f s))
                  → subst (Pos C {A}) eq (actP C f s p) ≡ actP C f s' (subst (Pos C {B}) (cong (actS C f) eq) p)
  subst-cong-actP ℓ X C A B f s .s refl p = refl
  subst-cong-actP-f : ∀ (ℓ : Level) (X : Set (lsuc (lsuc ℓ))) (C : CosmosF ℓ X) (A B : Obj C) (f f' : Hom C A B) (s : Shape C A)
                    → (eq : f ≡ f') (p : Pos C (actS C f s))
                    → actP C f s p ≡ actP C f' s (subst (Pos C {B}) (cong (λ g → actS C g s) eq) p)
  subst-cong-actP-f ℓ X C A B f .f s refl p = refl

  -- Mapping operation on CosmosF
  -- CosmosF 上的映射操作
  imap-cosmosF : ∀ {ℓ X Y} → (X → Y) → CosmosF ℓ X → CosmosF ℓ Y
  imap-cosmosF f fx = record
    { Obj = Obj fx
    ; Shape = Shape fx
    ; Pos = Pos fx
    ; Hom = Hom fx
    ; idHom = idHom fx
    ; comp = comp fx
    ; comp-assoc = comp-assoc fx
    ; id-comp-l = id-comp-l fx
    ; id-comp-r = id-comp-r fx
    ; actS = actS fx
    ; actP = actP fx
    ; actS-id = actS-id fx
    ; actS-comp = actS-comp fx
    ; actP-id = actP-id fx
    ; actP-comp = actP-comp fx
    ; unfold = f ∘ unfold fx
    ; unfold-obj = unfold-obj fx
    ; unfold-hom = unfold-hom fx
    ; unfold-hom-id = unfold-hom-id fx
    ; unfold-hom-comp = unfold-hom-comp fx
    ; pos-to-shape = pos-to-shape fx
    ; pos-actS-compat = pos-actS-compat fx
    }
  imap-cosmosF-id : ∀ {ℓ X} → imap-cosmosF {ℓ} {X} id ≡ id
  imap-cosmosF-id = refl
  imap-cosmosF-comp : ∀ {ℓ X Y Z} {f : X → Y} {g : Y → Z}
                    → imap-cosmosF {ℓ} (g ∘ f) ≡ imap-cosmosF g ∘ imap-cosmosF f
  imap-cosmosF-comp = refl

  -- Extract one layer of structure from Cosmos (Out map)
  -- 从 Cosmos 提取一层结构（Out 映射）
  out : ∀ {ℓ} → Cosmos ℓ → CosmosF ℓ (Cosmos ℓ)
  out C = record
    { Obj = Obj C
    ; Shape = Shape C
    ; Pos = Pos C
    ; Hom = Hom C
    ; idHom = idHom C
    ; comp = comp C
    ; comp-assoc = comp-assoc C
    ; id-comp-l = id-comp-l C
    ; id-comp-r = id-comp-r C
    ; actS = actS C
    ; actP = actP C
    ; actS-id = actS-id C
    ; actS-comp = actS-comp C
    ; actP-id = actP-id C
    ; actP-comp = actP-comp C
    ; unfold = unfold C
    ; unfold-obj = unfold-obj C
    ; unfold-hom = unfold-hom C
    ; unfold-hom-id = unfold-hom-id C
    ; unfold-hom-comp = unfold-hom-comp C
    ; pos-to-shape = pos-to-shape C
    ; pos-actS-compat = pos-actS-compat C
    }

  -- Embed one layer of structure as Cosmos (In map)
  -- 将一层结构嵌入为 Cosmos（In 映射）
  inF : ∀ {ℓ} → CosmosF ℓ (Cosmos ℓ) → Cosmos ℓ
  inF F = record
    { Obj = Obj F
    ; Shape = Shape F
    ; Pos = Pos F
    ; Hom = Hom F
    ; idHom = idHom F
    ; comp = comp F
    ; comp-assoc = comp-assoc F
    ; id-comp-l = id-comp-l F
    ; id-comp-r = id-comp-r F
    ; actS = actS F
    ; actP = actP F
    ; actS-id = actS-id F
    ; actS-comp = actS-comp F
    ; actP-id = actP-id F
    ; actP-comp = actP-comp F
    ; unfold = unfold F
    ; unfold-obj = unfold-obj F
    ; unfold-hom = unfold-hom F
    ; unfold-hom-id = unfold-hom-id F
    ; unfold-hom-comp = unfold-hom-comp F
    ; pos-to-shape = pos-to-shape F
    ; pos-actS-compat = pos-actS-compat F
    }

  out∘inF : ∀ {ℓ} (fx : CosmosF ℓ (Cosmos ℓ)) → out (inF fx) ≡ fx
  out∘inF _ = refl

  -- Coalgebraic unfolding (Anamorphism): generate Cosmos from seed
  -- 余代数展开（Anamorphism）：从种子生成 Cosmos
  module _ {ℓ : Level} where
    ana : ∀ {X : Set (lsuc (lsuc ℓ))}
        → (α : X → CosmosF ℓ X)
        → X → Cosmos ℓ
    ana α x .Obj = Obj (α x)
    ana α x .Shape = Shape (α x)
    ana α x .Pos = Pos (α x)
    ana α x .Hom = Hom (α x)
    ana α x .idHom = idHom (α x)
    ana α x .comp = comp (α x)
    ana α x .comp-assoc = comp-assoc (α x)
    ana α x .id-comp-l = id-comp-l (α x)
    ana α x .id-comp-r = id-comp-r (α x)
    ana α x .actS = actS (α x)
    ana α x .actP = actP (α x)
    ana α x .actS-id = actS-id (α x)
    ana α x .actS-comp = actS-comp (α x)
    ana α x .actP-id = actP-id (α x)
    ana α x .actP-comp = actP-comp (α x)
    ana α x .unfold s = ana α (unfold (α x) s)
    ana α x .unfold-obj = unfold-obj (α x)
    ana α x .unfold-hom = unfold-hom (α x)
    ana α x .unfold-hom-id = unfold-hom-id (α x)
    ana α x .unfold-hom-comp = unfold-hom-comp (α x)
    ana α x .pos-to-shape = pos-to-shape (α x)
    ana α x .pos-actS-compat = pos-actS-compat (α x)

  shape-cong : ∀ (ℓ : Level) (X : Set (lsuc (lsuc ℓ))) (cf1 cf2 : CosmosF ℓ X) (eq : cf1 ≡ cf2)
              → (A : Obj cf1)
              → Shape cf1 A ≡ Shape cf2 (subst id (cong Obj eq) A)
  shape-cong ℓ X cf1 .cf1 refl A = refl
  pos-cong : ∀ (ℓ : Level) (X : Set (lsuc (lsuc ℓ))) (cf1 cf2 : CosmosF ℓ X) (eq : cf1 ≡ cf2)
            → (A : Obj cf1) (s : Shape cf1 A)
            → Pos cf1 s ≡ Pos cf2 (subst id (shape-cong ℓ X cf1 cf2 eq A) s)
  pos-cong ℓ X cf1 .cf1 refl A s = refl
  hom-cong : ∀ (ℓ : Level) (X : Set (lsuc (lsuc ℓ))) (cf1 cf2 : CosmosF ℓ X) (eq : cf1 ≡ cf2)
            → (A B : Obj cf1)
            → Hom cf1 A B ≡ Hom cf2 (subst id (cong Obj eq) A) (subst id (cong Obj eq) B)
  hom-cong ℓ X cf1 .cf1 refl A B = refl
  idHom-cong : ∀ (ℓ : Level) (X : Set (lsuc (lsuc ℓ))) (cf1 cf2 : CosmosF ℓ X) (eq : cf1 ≡ cf2)
              → (A : Obj cf1)
              → subst id (hom-cong ℓ X cf1 cf2 eq A A) (idHom cf1 {A}) ≡ idHom cf2 {A = subst id (cong Obj eq) A}
  idHom-cong ℓ X cf1 .cf1 refl A = refl
  comp-cong : ∀ (ℓ : Level) (X : Set (lsuc (lsuc ℓ))) (cf1 cf2 : CosmosF ℓ X) (eq : cf1 ≡ cf2)
            → (A B C : Obj cf1) (f : Hom cf1 A B) (g : Hom cf1 B C)
            → subst id (hom-cong ℓ X cf1 cf2 eq A C) (comp cf1 f g) ≡ comp cf2 (subst id (hom-cong ℓ X cf1 cf2 eq A B) f) (subst id (hom-cong ℓ X cf1 cf2 eq B C) g)
  comp-cong ℓ X cf1 .cf1 refl A B C f g = refl
  actS-cong : ∀ (ℓ : Level) (X : Set (lsuc (lsuc ℓ))) (cf1 cf2 : CosmosF ℓ X) (eq : cf1 ≡ cf2)
            → (A B : Obj cf1) (f : Hom cf1 A B) (s : Shape cf1 A)
            → subst id (shape-cong ℓ X cf1 cf2 eq B) (actS cf1 f s) ≡ actS cf2 (subst id (hom-cong ℓ X cf1 cf2 eq A B) f) (subst id (shape-cong ℓ X cf1 cf2 eq A) s)
  actS-cong ℓ X cf1 .cf1 refl A B f s = refl
  actP-cong : ∀ (ℓ : Level) (X : Set (lsuc (lsuc ℓ))) (cf1 cf2 : CosmosF ℓ X) (eq : cf1 ≡ cf2)
            → (A B : Obj cf1) (f : Hom cf1 A B) (s : Shape cf1 A) (p : Pos cf1 (actS cf1 f s))
            → subst id (pos-cong ℓ X cf1 cf2 eq A s) (actP cf1 f s p)
              ≡ actP cf2 (subst id (hom-cong ℓ X cf1 cf2 eq A B) f) (subst id (shape-cong ℓ X cf1 cf2 eq A) s) 
                        (subst (Pos cf2) (actS-cong ℓ X cf1 cf2 eq A B f s) (subst id (pos-cong ℓ X cf1 cf2 eq B (actS cf1 f s)) p))
  actP-cong ℓ X cf1 .cf1 refl A B f s p = refl
  unfold-obj-cong : ∀ (ℓ : Level) (X : Set (lsuc (lsuc ℓ))) (cf1 cf2 : CosmosF ℓ X) (eq : cf1 ≡ cf2)
                  → (A : Obj cf1) (s : Shape cf1 A)
                  → subst id (cong Obj eq) (unfold-obj cf1 s) ≡ unfold-obj cf2 (subst id (shape-cong ℓ X cf1 cf2 eq A) s)
  unfold-obj-cong ℓ X cf1 .cf1 refl A s = refl
  pos-to-shape-cong : ∀ (ℓ : Level) (X : Set (lsuc (lsuc ℓ))) (cf1 cf2 : CosmosF ℓ X) (eq : cf1 ≡ cf2)
                    → (A : Obj cf1) (s : Shape cf1 A) (p : Pos cf1 s)
                    → subst (Shape cf2) (unfold-obj-cong ℓ X cf1 cf2 eq A s)
                              (subst id (shape-cong ℓ X cf1 cf2 eq (unfold-obj cf1 s)) (pos-to-shape cf1 s p))
                      ≡ pos-to-shape cf2 (subst id (shape-cong ℓ X cf1 cf2 eq A) s)
                                          (subst id (pos-cong ℓ X cf1 cf2 eq A s) p)
  pos-to-shape-cong ℓ X cf1 .cf1 refl A s p = refl

  module _ {ℓ : Level} where
    -- Homomorphism condition for CosmosF-algebras
    -- CosmosF-代数的同态条件
    record CosmosHomo
             {X : Set (lsuc (lsuc ℓ))}
             (α : X → CosmosF ℓ X)
             (φ : X → Cosmos ℓ)
             : Set (lsuc (lsuc ℓ)) where
      field
        comm : ∀ x → out (φ x) ≡ imap-cosmosF φ (α x)
    open CosmosHomo public
    ana-homo : ∀ {X : Set (lsuc (lsuc ℓ))} (α : X → CosmosF ℓ X)
             → CosmosHomo α (ana α)
    ana-homo α .comm x = refl
    unfold-cong : ∀ {ℓ X} {C1 C2 : CosmosF ℓ X} (p : C1 ≡ C2) {A : C1 .Obj} (s : C1 .Shape A)
      → C1 .unfold s ≡ C2 .unfold (subst id (shape-cong ℓ X C1 C2 p A) s)
    unfold-cong refl s = refl

    -- Uniqueness theorem for homomorphisms
    -- 同态的唯一性定理
    unique-homo : ∀ {X : Set (lsuc (lsuc ℓ))}
                  (α : X → CosmosF ℓ X)
                  (φ : X → Cosmos ℓ)
                  → CosmosHomo α φ
                  → ∀ x → φ x ≃ ana α x
    unique-homo α φ h = aux
      where
      aux : ∀ x → φ x ≃ ana α x
      aux x = proof
        where
        eqF : out (φ x) ≡ imap-cosmosF φ (α x)
        eqF = h .comm x
        cast-obj : Obj (φ x) → Obj (ana α x)
        cast-obj = subst id (cong Obj eqF)
        cast-shape : (A : Obj (φ x)) → Shape (φ x) A → Shape (ana α x) (cast-obj A)
        cast-shape A = subst id (shape-cong ℓ (Cosmos ℓ) (out (φ x)) (imap-cosmosF φ (α x)) eqF A)
        cast-pos : (A : Obj (φ x)) (s : Shape (φ x) A) → Pos (φ x) s → Pos (ana α x) (cast-shape A s)
        cast-pos A s = subst id (pos-cong ℓ (Cosmos ℓ) (out (φ x)) (imap-cosmosF φ (α x)) eqF A s)
        cast-hom : (A B : Obj (φ x)) → Hom (φ x) A B → Hom (ana α x) (cast-obj A) (cast-obj B)
        cast-hom A B = subst id (hom-cong ℓ (Cosmos ℓ) (out (φ x)) (imap-cosmosF φ (α x)) eqF A B)
        Obj-R' : Obj (φ x) → Obj (ana α x) → Set (lsuc ℓ)
        Obj-R' A A' = cast-obj A ≡ A'
        Shape-R' : (A : Obj (φ x)) (A' : Obj (ana α x))
                → Obj-R' A A'
                → Shape (φ x) A → Shape (ana α x) A' → Set (lsuc ℓ)
        Shape-R' A A' R₁ s s' = subst (Shape (ana α x)) R₁ (cast-shape A s) ≡ s'
        Pos-R' : (A : Obj (φ x)) (A' : Obj (ana α x))
              → (R₁ : Obj-R' A A')
              → (s : Shape (φ x) A) (s' : Shape (ana α x) A')
              → Shape-R' A A' R₁ s s'
              → Pos (φ x) s → Pos (ana α x) s' → Set (lsuc ℓ)
        Pos-R' A A' R₁ s s' Rₛ p p' = 
          subst (Pos (ana α x)) Rₛ 
                (subst-pos (ana α x) R₁ (cast-shape A s) (cast-pos A s p)) ≡ p'
        Hom-R' : (A : Obj (φ x)) (A' : Obj (ana α x)) (B : Obj (φ x)) (B' : Obj (ana α x))
              → Obj-R' A A'
              → Obj-R' B B'
              → Hom (φ x) A B → Hom (ana α x) A' B' → Set (lsuc ℓ)
        Hom-R' A A' B B' R₁ R₂ f f' = subst₂ (Hom (ana α x)) R₁ R₂ (cast-hom A B f) ≡ f'
        id-preserve' : (A : Obj (φ x)) (A' : Obj (ana α x)) (R₁ : Obj-R' A A')
                    → Hom-R' A A' A A' R₁ R₁ (idHom (φ x) {A}) (idHom (ana α x) {A = A'})
        id-preserve' A .(cast-obj A) refl =
          trans refl (idHom-cong ℓ (Cosmos ℓ) (out (φ x)) (imap-cosmosF φ (α x)) eqF A)
        comp-preserve' : (A : Obj (φ x)) (A' : Obj (ana α x)) (B : Obj (φ x)) (B' : Obj (ana α x)) (X : Obj (φ x)) (X' : Obj (ana α x))
                      → (R₁ : Obj-R' A A')
                      → (R₂ : Obj-R' B B')
                      → (R₃ : Obj-R' X X')
                      → (f : Hom (φ x) A B) (f' : Hom (ana α x) A' B')
                      → (g : Hom (φ x) B X) (g' : Hom (ana α x) B' X')
                      → (hf : Hom-R' A A' B B' R₁ R₂ f f')
                      → (hg : Hom-R' B B' X X' R₂ R₃ g g')
                      → Hom-R' A A' X X' R₁ R₃ (comp (φ x) f g) (comp (ana α x) f' g')
        comp-preserve' A .(cast-obj A) B .(cast-obj B) X .(cast-obj X) refl refl refl f f' g g' refl refl =
          trans refl (comp-cong ℓ (Cosmos ℓ) (out (φ x)) (imap-cosmosF φ (α x)) eqF A B X f g)
        actS-preserve' : (A : Obj (φ x)) (A' : Obj (ana α x)) (B : Obj (φ x)) (B' : Obj (ana α x))
                      → (R₁ : Obj-R' A A')
                      → (R₂ : Obj-R' B B')
                      → (f : Hom (φ x) A B) (f' : Hom (ana α x) A' B')
                      → (s : Shape (φ x) A) (s' : Shape (ana α x) A')
                      → (hf : Hom-R' A A' B B' R₁ R₂ f f')
                      → (hs : Shape-R' A A' R₁ s s')
                      → Shape-R' B B' R₂ (actS (φ x) f s) (actS (ana α x) f' s')
        actS-preserve' A .(cast-obj A) B .(cast-obj B) refl refl f .(cast-hom A B f) s .(cast-shape A s) refl refl =
          actS-cong ℓ (Cosmos ℓ) (out (φ x)) (imap-cosmosF φ (α x)) eqF A B f s
        actP-preserve' : (A : Obj (φ x)) (A' : Obj (ana α x)) (B : Obj (φ x)) (B' : Obj (ana α x))
                      → (R₁ : Obj-R' A A')
                      → (R₂ : Obj-R' B B')
                      → (f : Hom (φ x) A B) (f' : Hom (ana α x) A' B')
                      → (s : Shape (φ x) A) (s' : Shape (ana α x) A')
                      → (p : Pos (φ x) (actS (φ x) f s)) (p' : Pos (ana α x) (actS (ana α x) f' s'))
                      → (hf : Hom-R' A A' B B' R₁ R₂ f f')
                      → (hs : Shape-R' A A' R₁ s s')
                      → (hp : Pos-R' B B' R₂ (actS (φ x) f s) (actS (ana α x) f' s') 
                              (actS-preserve' A A' B B' R₁ R₂ f f' s s' hf hs) p p')
                      → Pos-R' A A' R₁ s s' hs (actP (φ x) f s p) (actP (ana α x) f' s' p')
        actP-preserve' A .(cast-obj A) B .(cast-obj B) refl refl f .(cast-hom A B f) s .(cast-shape A s) p p' refl refl hp =
          let
            eqActS = actS-cong ℓ (Cosmos ℓ) (out (φ x)) (imap-cosmosF φ (α x)) eqF A B f s
            eq1 = actP-cong ℓ (Cosmos ℓ) (out (φ x)) (imap-cosmosF φ (α x)) eqF A B f s p
            eq2 = hp
            eq3 = cong (actP (ana α x) (cast-hom A B f) (cast-shape A s)) eq2
          in trans eq1 eq3
        unfold-obj-preserve' : (A : Obj (φ x)) (A' : Obj (ana α x))
                            → (R₁ : Obj-R' A A')
                            → (s : Shape (φ x) A) (s' : Shape (ana α x) A')
                            → (hs : Shape-R' A A' R₁ s s')
                            → Obj-R' (unfold-obj (φ x) s) (unfold-obj (ana α x) s')
        unfold-obj-preserve' A .(cast-obj A) refl s s' refl =
          unfold-obj-cong ℓ (Cosmos ℓ) (out (φ x)) (imap-cosmosF φ (α x)) eqF A s
        pos-to-shape-preserve' : (A : Obj (φ x)) (A' : Obj (ana α x))
                              → (R₁ : Obj-R' A A')
                              → (s : Shape (φ x) A) (s' : Shape (ana α x) A')
                              → (hs : Shape-R' A A' R₁ s s')
                              → (p : Pos (φ x) s) (p' : Pos (ana α x) s')
                              → (hp : Pos-R' A A' R₁ s s' hs p p')
                              → Shape-R' (unfold-obj (φ x) s) (unfold-obj (ana α x) s')
                                          (unfold-obj-preserve' A A' R₁ s s' hs)
                                          (pos-to-shape (φ x) s p)
                                          (pos-to-shape (ana α x) s' p')
        pos-to-shape-preserve' A .(cast-obj A) refl s s' refl p p' refl =
          pos-to-shape-cong ℓ (Cosmos ℓ) (out (φ x)) (imap-cosmosF φ (α x)) eqF A s p
        proof : φ x ≃ ana α x
        proof .Obj-R = Obj-R'
        proof .Shape-R = Shape-R'
        proof .Pos-R = Pos-R'
        proof .Hom-R = Hom-R'
        proof .id-preserve = id-preserve'
        proof .comp-preserve = comp-preserve'
        proof .actS-preserve = actS-preserve'
        proof .actP-preserve = actP-preserve'
        proof .unfold-obj-preserve = unfold-obj-preserve'
        proof .pos-to-shape-preserve = pos-to-shape-preserve'
        proof .unfold-bisim A .(cast-obj A) refl s s' hs
          rewrite unfold-cong eqF s | sym hs
          = aux (unfold (α x) (cast-shape A s))

-- Final coalgebra property module
-- 终余代数性质模块
module Finality where
  open CosmosF-Definition renaming (out to outF; ana to anaF; unique-homo to unique-homoF)
  -- Formal definition of final coalgebra
  -- 终余代数的形式化定义
  record IsFinal (ℓ : Level) : Set (lsuc (lsuc (lsuc ℓ))) where
    field
      out    : Cosmos ℓ → CosmosF ℓ (Cosmos ℓ)
      ana    : {X : Set (lsuc (lsuc ℓ))} (α : X → CosmosF ℓ X) → X → Cosmos ℓ
      unique : {X : Set (lsuc (lsuc ℓ))} (α : X → CosmosF ℓ X) (φ : X → Cosmos ℓ)
             → (∀ x → out (φ x) ≡ imap-cosmosF φ (α x))
             → ∀ x → φ x ≃ ana α x
  -- Proof that Cosmos is the final coalgebra of CosmosF
  -- 证明 Cosmos 是 CosmosF 的终余代数
  Cosmos-is-final : ∀ {ℓ} → IsFinal ℓ
  Cosmos-is-final = record
    { out   = outF
    ; ana   = anaF
    ; unique = λ α φ h → unique-homoF α φ (record { comm = h })
    }
open Finality public
