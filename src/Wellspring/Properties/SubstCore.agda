------------------------------------------------------------------------
-- Substitution core for cross-cosmos morphisms
--
-- Basic subst laws on ⇒ℱ, together with type aliases for Σ-types over
-- Cosmos. These are the lemmas on which transport, equivalence
-- reasoning, and composition congruence all rest.
--
-- 跨宇宙态射的替换内核
--
-- ⇒ℱ 上的基本 subst 法则，以及 Cosmos 上 Σ-类型 的类型别名。
-- 这些是 transport、等价推理与复合同余共同依赖的基础引理。
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module Wellspring.Properties.SubstCore where

open import Wellspring.Cosmos public

-- Basic homotopy equations
--
-- 基本的同伦等式
unfold-hom-id' : ∀ {ℓ} (C : Cosmos ℓ) {A : Obj C} {s : Shape C A}
               → subst (λ X → Hom C (unfold-obj C s) (unfold-obj C X))
                       (actS-id C {A = A} s)
                       (unfold-hom C (idHom C) s)
               ≡ idHom C {A = unfold-obj C s}
unfold-hom-id' C {A} {s} =
  let
    P : _
    P X = Hom C (unfold-obj C s) (unfold-obj C X)
    eq = actS-id C {A = A} s
    idH = idHom C {A = unfold-obj C s}
  in
  trans
    (cong (subst P eq) (unfold-hom-id C {A = A} s))
    (subst-inv' P eq {b = idH})

unfold-hom-comp' : ∀ {ℓ} (C : Cosmos ℓ) {A B D : Obj C}
                 → (f : Hom C A B) (g : Hom C B D) {s : Shape C A}
                 → subst (λ X → Hom C (unfold-obj C s) (unfold-obj C X))
                         (actS-comp C f g s)
                         (unfold-hom C (comp C f g) s)
                 ≡ comp C (unfold-hom C f s) (unfold-hom C g (actS C f s))
unfold-hom-comp' C f g {s} =
  let
    P : _
    P X = Hom C (unfold-obj C s) (unfold-obj C X)
    eq = actS-comp C f g s
    compH = comp C (unfold-hom C f s) (unfold-hom C g (actS C f s))
  in
  trans
    (cong (subst P eq) (unfold-hom-comp C f g s))
    (subst-inv' P eq {b = compH})

-- Properties of subst on ⇒ℱ
--
-- subst 在 ⇒ℱ 上的性质
subst-⇒ℱ-onObj : ∀ (ℓ) (F C D : Cosmos ℓ) (eq : C ≡ D) (m : F ⇒ℱ C) (X : Obj F)
                → onObj (subst (λ C → F ⇒ℱ C) eq m) X ≡ subst (λ Y → Obj Y) eq (onObj m X)
subst-⇒ℱ-onObj _ _ _ _ refl _ _ = refl

subst-⇒ℱ-onShape : ∀ (ℓ) (F C D : Cosmos ℓ) (eq : C ≡ D) (m : F ⇒ℱ C) (X : Obj F) (t : Shape F X)
                  → onShape (subst (λ C' → F ⇒ℱ C') eq m) t
                  ≡ subst (λ (p : Σ (Cosmos ℓ) (λ C' → Obj C')) → Shape (p .proj₁) (p .proj₂))
                          (Σ-≡ eq (sym (subst-⇒ℱ-onObj ℓ F C D eq m X)))
                          (onShape m t)
subst-⇒ℱ-onShape _ _ _ _ refl _ _ _ = refl

subst-⇒ℱ-onObjShape : ∀ (ℓ) (F C D : Cosmos ℓ) (eq : C ≡ D) (m : F ⇒ℱ C) (X : Obj F) (t : Shape F X)
  → subst (λ C' → Σ (Obj C') (λ o → Shape C' o)) eq (onObj m X , onShape m t)
    ≡ ( onObj (subst (λ C' → F ⇒ℱ C') eq m) X
      , onShape (subst (λ C' → F ⇒ℱ C') eq m) t )
subst-⇒ℱ-onObjShape ℓ F C D refl m X t = refl

subst-⇒ℱ-onObj2 : ∀ (ℓ) (F C D : Cosmos ℓ) (eq : C ≡ D) (m : F ⇒ℱ C) (X Y : Obj F)
  → subst (λ C' → Obj C' × Obj C') eq (onObj m X , onObj m Y)
    ≡ ( onObj (subst (λ C' → F ⇒ℱ C') eq m) X
      , onObj (subst (λ C' → F ⇒ℱ C') eq m) Y )
subst-⇒ℱ-onObj2 ℓ F C D refl m X Y = refl

subst-⇒ℱ-onHom : ∀ (ℓ) (F C D : Cosmos ℓ) (eq : C ≡ D) (m : F ⇒ℱ C) (X Y : Obj F) (f : Hom F X Y)
  → onHom (subst (λ C' → F ⇒ℱ C') eq m) f
  ≡ subst (λ (p : Σ (Cosmos ℓ) (λ C' → Obj C' × Obj C'))
            → Hom (p .proj₁) (p .proj₂ .proj₁) (p .proj₂ .proj₂))
          (Σ-≡ eq (subst-⇒ℱ-onObj2 ℓ F C D eq m X Y))
          (onHom m f)
subst-⇒ℱ-onHom ℓ F C D refl m X Y f = refl

subst-⇒ℱ-onPos : ∀ (ℓ) (F C D : Cosmos ℓ) (eq : C ≡ D) (m : F ⇒ℱ C) (X : Obj F) {t : Shape F X} (p : Pos F t)
  → onPos (subst (λ C' → F ⇒ℱ C') eq m) p
  ≡ subst (λ (p : Σ (Cosmos ℓ) (λ C' → Σ (Obj C') (λ o → Shape C' o)))
            → Pos (p .proj₁) (p .proj₂ .proj₂))
          (Σ-≡ eq (subst-⇒ℱ-onObjShape ℓ F C D eq m X t))
          (onPos m p)
subst-⇒ℱ-onPos ℓ F C D refl m X {t} p = refl

subst-⇒ℱ-onunfold : ∀ (ℓ) (F C D : Cosmos ℓ) (eq : C ≡ D) (m : F ⇒ℱ C) (X : Obj F) (t : Shape F X)
  → onunfold (subst (λ C' → F ⇒ℱ C') eq m) t
  ≡ subst (λ (p : Σ (Cosmos ℓ) (λ C' → Σ (Obj C') (λ o → Shape C' o)))
            → unfold F t ⇒ℱ unfold (p .proj₁) (p .proj₂ .proj₂))
          (Σ-≡ eq (subst-⇒ℱ-onObjShape ℓ F C D eq m X t))
          (onunfold m t)
subst-⇒ℱ-onunfold ℓ F C D refl m X t = refl

-- Compatibility of subst with composition for ≃⇒ℱ
--
-- subst 与复合的 ≃⇒ℱ 相容性
subst-comp-⇒ℱ-both : ∀ {ℓ} {A B B' C : Cosmos ℓ} (p : B ≡ B')
  → (f : A ⇒ℱ B) (g : B ⇒ℱ C)
  → subst (λ D → D ⇒ℱ C) p g ∘⇒ℱ subst (λ D → A ⇒ℱ D) p f
    ≃⇒ℱ
    g ∘⇒ℱ f
subst-comp-⇒ℱ-both refl f g = refl-≃⇒ℱ

-- Auxiliary type aliases and equality constructors
--
-- 辅助类型别名与等式构造器
ObjShape : (ℓ : Level) (C : Cosmos ℓ) → Set (lsuc ℓ)
ObjShape ℓ C = Σ (Obj C) (Shape C)

ObjPair : (ℓ : Level) (C : Cosmos ℓ) → Set (lsuc ℓ)
ObjPair ℓ C = Obj C × Obj C

ObjSubst : (ℓ : Level) (C₁ C₂ : Cosmos ℓ) → C₁ ≡ C₂ → Obj C₁ → Obj C₂
ObjSubst ℓ C₁ C₂ eq o = subst (λ Y → Obj Y) eq o

ShapeSubstP : (ℓ : Level) → Σ (Cosmos ℓ) (λ Y → Obj Y) → Set (lsuc ℓ)
ShapeSubstP ℓ p = Shape (p .proj₁) (p .proj₂)

PosSubstP : (ℓ : Level) (C : Cosmos ℓ) → ObjShape ℓ C → Set (lsuc ℓ)
PosSubstP ℓ C (o , s) = Pos C s

HomSubstP : (ℓ : Level) (C : Cosmos ℓ) → ObjPair ℓ C → Set (lsuc ℓ)
HomSubstP ℓ C (o1 , o2) = Hom C o1 o2

ShapeEq : (ℓ : Level) (C₁ C₂ : Cosmos ℓ) (eq : C₁ ≡ C₂) (o : Obj C₁)
        → _≡_ {A = Σ (Cosmos ℓ) (λ Y → Obj Y)}
            (C₁ , o)
            (C₂ , ObjSubst ℓ C₁ C₂ eq o)
ShapeEq ℓ C₁ .C₁ refl o = refl

HomEq : (ℓ : Level) (C₁ C₂ : Cosmos ℓ) (eq : C₁ ≡ C₂) (o1 o2 : Obj C₁)
      → _≡_ {A = Σ (Cosmos ℓ) (λ Y → Obj Y × Obj Y)}
          (C₁ , (o1 , o2))
          (C₂ , (ObjSubst ℓ C₁ C₂ eq o1 , ObjSubst ℓ C₁ C₂ eq o2))
HomEq ℓ C₁ .C₁ refl o1 o2 = refl

PosEq : (ℓ : Level) (C₁ C₂ : Cosmos ℓ) (eq : C₁ ≡ C₂) (o : Obj C₁) (s : Shape C₁ o)
      → _≡_ {A = Σ (Cosmos ℓ) (λ Y → Σ (Obj Y) (Shape Y))}
          (C₁ , (o , s))
          (C₂ , (ObjSubst ℓ C₁ C₂ eq o , subst (ShapeSubstP ℓ) (ShapeEq ℓ C₁ C₂ eq o) s))
PosEq ℓ C₁ .C₁ refl o s = refl

same-C-PosEq : ∀ ℓ (C : Cosmos ℓ) {o1 o2 : Obj C} (eO : o1 ≡ o2) (s2 : Shape C o2)
             → (o1 , subst (Shape C) (sym eO) s2) ≡ (o2 , s2)
same-C-PosEq ℓ C {o1} {.o1} refl s2 = refl

PosAt : (ℓ : Level) (C : Cosmos ℓ) (o : Obj C) → Shape C o → Set (lsuc ℓ)
PosAt ℓ C o s = Pos C {o} s

PosOfShape : (ℓ : Level) (C : Cosmos ℓ) → ObjShape ℓ C → Set (lsuc ℓ)
PosOfShape ℓ C (o , s) = PosAt ℓ C o s
