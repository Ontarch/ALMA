------------------------------------------------------------------------
-- Basic reasoning for ≃⇒ℱ
--
-- Transport of Pos across shape equalities, symmetrization of the
-- evidence of ≃⇒ℱ, and the elementary position-exchange lemmas.
-- These are the direct manipulations of ≃⇒ℱ that do not depend on
-- composition congruence.
--
-- ≃⇒ℱ 的基础推理
--
-- 沿 shape 等式运输 Pos、把 ≃⇒ℱ 的证据反过来，以及基本的位置交换引理。
-- 这些是 ≃⇒ℱ 的直接操作，不依赖复合同余。
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module Wellspring.Properties.Equiv where

open import Wellspring.Properties.Transport public

-- Shape/position reasoning related to ≃⇒ℱ
--
-- 与 ≃⇒ℱ 相关的形状/位置推理
eqSh-base-simp : ∀ {ℓ} {G : Cosmos ℓ} {O1 : Obj G} {S1 S2' : Shape G O1}
                → (eqSh' : S1 ≡ subst (Shape G) refl S2')
                → S1 ≡ S2'
eqSh-base-simp {G = G} {O1} {S1} {S2'} eqSh' =
  trans eqSh' (subst-refl-id (Shape G) S2')

shape-lemma-eq-base : ∀ {ℓ} {G : Cosmos ℓ} {O1 : Obj G} {S1 S2' : Shape G O1}
                    → (eqSh' : S1 ≡ subst (Shape G) refl S2')
                    → (shape-lemma' : S2' ≡ subst (Shape G) refl S1)
                    → (shape-lemma-eq : shape-lemma' ≡ sym (trans (cong (subst (Shape G) refl) eqSh') (subst-inv' (Shape G) refl)))
                    → sym shape-lemma' ≡ eqSh'
shape-lemma-eq-base {G = G} {O1} {S1} {S2'} eqSh' shape-lemma' shape-lemma-eq =
  let
    step1 : sym shape-lemma' ≡ trans (cong (subst (Shape G) refl) eqSh') (subst-inv' (Shape G) refl)
    step1 = trans (cong sym shape-lemma-eq) (sym (sym-sym (trans (cong (subst (Shape G) refl) eqSh') (subst-inv' (Shape G) refl))))
    step2 : trans (cong (subst (Shape G) refl) eqSh') (subst-inv' (Shape G) refl) ≡ eqSh'
    step2 = J (λ S2'' eqSh'' → trans (cong (subst (Shape G) refl) eqSh'') (subst-inv' (Shape G) refl) ≡ eqSh'')
              eqSh'
              refl
  in
  trans step1 step2

eq2-base-prop : ∀ {ℓ} {G : Cosmos ℓ} {O1 : Obj G} {S1 S2' : Shape G O1}
              → (eqSh' : S1 ≡ subst (Shape G) refl S2')
              → (shape-lemma' : S2' ≡ subst (Shape G) refl S1)
              → (shape-lemma-eq : shape-lemma' ≡ sym (trans (cong (subst (Shape G) refl) eqSh') (subst-inv' (Shape G) refl)))
              → trans (subst-unfold G refl S1) (cong (unfold G {O1}) (sym shape-lemma'))
              ≡ cong (unfold G {O1}) (eqSh-base-simp {G = G} {O1 = O1} {S1 = S1} {S2' = S2'} eqSh')
eq2-base-prop {G = G} {O1 = O1} {S1 = S1} {S2' = S2'} eqSh' shape-lemma' shape-lemma-eq =
  let
    step1 : trans (subst-unfold G refl S1) (cong (unfold G {O1}) (sym shape-lemma'))
          ≡ cong (unfold G {O1}) (sym shape-lemma')
    step1 = transReflˡ _
    step2 : sym shape-lemma' ≡ eqSh'
    step2 = shape-lemma-eq-base {G = G} {O1 = O1} {S1 = S1} {S2' = S2'} eqSh' shape-lemma' shape-lemma-eq
    step3 : eqSh' ≡ eqSh-base-simp {G = G} {O1 = O1} {S1 = S1} {S2' = S2'} eqSh'
    step3 = sym (trans-reflʳ eqSh')
    step4 : sym shape-lemma' ≡ eqSh-base-simp {G = G} {O1 = O1} {S1 = S1} {S2' = S2'} eqSh'
    step4 = trans step2 step3
    step5 : cong (unfold G {O1}) (sym shape-lemma') ≡ cong (unfold G {O1}) (eqSh-base-simp {G = G} {O1 = O1} {S1 = S1} {S2' = S2'} eqSh')
    step5 = cong (cong (unfold G {O1})) step4
  in
  trans step1 step5

sym-sym-eqO : ∀ {ℓ} {F G : Cosmos ℓ} {m₁ m₂ : F ⇒ℱ G} {e : m₁ ≃⇒ℱ m₂} {A : Obj F}
            → let eqO = onObj-eq e A
              in sym (sym eqO) ≡ eqO
sym-sym-eqO {e = e} {A} = sym (sym-sym (onObj-eq e A))

S-eq-correct : ∀ {ℓ} {F G : Cosmos ℓ} {m₁ m₂ : F ⇒ℱ G} {e : m₁ ≃⇒ℱ m₂} {A : Obj F} {s : Shape F A}
             → let eqO = onObj-eq e A
                   eqSh = onShape-eq e s
                   S1 = onShape m₁ s
                   S2 = onShape m₂ s
               in subst (Shape G) eqO S1 ≡ S2
S-eq-correct {ℓ} {F} {G} {m₁} {m₂} {e} {A} {s} =
  trans (cong (subst (Shape G) (onObj-eq e A)) (onShape-eq e s)) (subst-inv' (Shape G) (onObj-eq e A))

subst-pos-exchange-refl : ∀ {ℓ} {G : Cosmos ℓ} {O1 : Obj G} {S1 S2 : Shape G O1}
                           (eqSh : S1 ≡ S2) (P2 : Pos G S2)
                         → subst (Pos G)
                                 (trans (cong (subst (Shape G) refl) eqSh) (subst-inv' (Shape G) refl))
                                 (subst (Pos G) (sym eqSh) P2)
                           ≡ P2
subst-pos-exchange-refl {G = G} {O1 = O1} eqSh P2 =
  subst (λ S → subst (Pos G) S (subst (Pos G) (sym eqSh) P2) ≡ P2)
        (sym (S-eq-base-eq {G = G} {O1 = O1} eqSh))
        (subst-inv' (Pos G) eqSh)

subst-pos-exchange : ∀ {ℓ} {F G : Cosmos ℓ} {m₁ m₂ : F ⇒ℱ G} {e : m₁ ≃⇒ℱ m₂} {A : Obj F} {s : Shape F A} {p : Pos F s}
                   → let eqO = onObj-eq e A
                         eqSh = onShape-eq e s
                         S1 = onShape m₁ s
                         S2 = onShape m₂ s
                         P2 = onPos m₂ p
                         L = subst-pos G eqO S1 (subst (Pos G {onObj m₁ A}) (sym eqSh) (subst-pos G (sym eqO) S2 P2))
                     in subst (Pos G) (S-eq-correct {ℓ} {F} {G} {m₁} {m₂} {e} {A} {s}) L ≡ P2
subst-pos-exchange {ℓ} {F} {G} {m₁} {m₂} {e} {A} {s} {p} =
  let
    O1 = onObj m₁ A
    S1 = onShape m₁ s
    eqO = onObj-eq e A
    eqSh = onShape-eq e s
    S2 = onShape m₂ s
    P2 = onPos m₂ p
    P : (O2 : Obj G) → O1 ≡ O2 → Set (lsuc ℓ)
    P O2 eqO' = ∀ (S2 : Shape G O2)
                  (eqSh' : S1 ≡ subst (Shape G) (sym eqO') S2)
                  (P2' : Pos G S2) →
                  subst (Pos G)
                        (trans (cong (subst (Shape G) eqO') eqSh') (subst-inv' (Shape G) eqO'))
                        (subst-pos G eqO' S1
                          (subst (Pos G) (sym eqSh') (subst-pos G (sym eqO') S2 P2')))
                  ≡ P2'
    base : P O1 refl
    base S2' eqSh' P2' = subst-pos-exchange-refl {G = G} {O1 = O1} eqSh' P2'
  in J P eqO base S2 eqSh P2

pos-step1 : ∀ {ℓ} {F G : Cosmos ℓ} {m₁ m₂ : F ⇒ℱ G} {e : m₁ ≃⇒ℱ m₂} {A : Obj F} {s : Shape F A} {p : Pos F s}
          → let eqO = onObj-eq e A
                eqSh = onShape-eq e s
                S-eq = trans (cong (subst (Shape G) eqO) eqSh) (subst-inv' (Shape G) eqO)
                S1 = onShape m₁ s
                P1 = onPos m₁ p
                P2 = onPos m₂ p
            in subst-pos G eqO S1 P1 ≡ subst (Pos G) (sym S-eq) P2
pos-step1 {G = G} {m₁ = m₁} {m₂ = m₂} {e = e} {A} {s} {p} =
  let
    eqO = onObj-eq e A
    S-eq = trans (cong (subst (Shape G) eqO) (onShape-eq e s)) (subst-inv' (Shape G) eqO)
    step = pos-step1-correct {G = G} {m₁ = m₁} {m₂ = m₂} {e = e} {A} {s} {p}
  in
  subst-sym-swap (Pos G) S-eq step

subst-cancel-pos : ∀ {ℓ} {F G : Cosmos ℓ} {m₁ m₂ : F ⇒ℱ G} {e : m₁ ≃⇒ℱ m₂} {A : Obj F} {s : Shape F A} {p : Pos G (onShape m₂ s)}
                 → let eqO = onObj-eq e A
                       eqSh = onShape-eq e s
                       S-eq = trans (cong (subst (Shape G) eqO) eqSh) (subst-inv' (Shape G) eqO)
                       shape-lemma = shape-sym-lemma e s
                       subst-shape = subst-shape-sym-sym {ℓ} {F} {G} {m₁} {m₂} {e} {A} {s}
                       combined-eq = trans shape-lemma (trans subst-shape S-eq)
                   in subst (Pos G) combined-eq p ≡ p
subst-cancel-pos {ℓ} {F} {G} {m₁} {m₂} {e} {A} {s} {p} =
  let
    eqO = onObj-eq e A
    eqSh = onShape-eq e s
    S-eq = trans (cong (subst (Shape G) eqO) eqSh) (subst-inv' (Shape G) eqO)
    shape-lemma = shape-sym-lemma e s
    subst-shape = subst-shape-sym-sym {ℓ} {F} {G} {m₁} {m₂} {e} {A} {s}
    shape-lemma-is-sym' : shape-lemma ≡ sym (trans subst-shape S-eq)
    shape-lemma-is-sym' =
      trans (shape-lemma-def {ℓ} {F} {G} {m₁} {m₂} {e} {A} {s})
            (sym (sym-trans subst-shape S-eq))
    combined-eq-is-refl : trans shape-lemma (trans subst-shape S-eq) ≡ refl
    combined-eq-is-refl =
      trans (cong (λ x → trans x (trans subst-shape S-eq)) shape-lemma-is-sym')
            (trans-symˡ (trans subst-shape S-eq))
  in
  cong (λ eq → subst (Pos G) eq p) combined-eq-is-refl

cancel-shape-eq : ∀ {ℓ} {F G : Cosmos ℓ} {m₁ m₂ : F ⇒ℱ G} {e : m₁ ≃⇒ℱ m₂} {A : Obj F} {s : Shape F A} {p : Pos G (onShape m₂ s)}
                → let eqO = onObj-eq e A
                      eqSh = onShape-eq e s
                      S-eq = trans (cong (subst (Shape G) eqO) eqSh) (subst-inv' (Shape G) eqO)
                      shape-lemma = shape-sym-lemma e s
                      subst-shape = subst-shape-sym-sym {ℓ} {F} {G} {m₁} {m₂} {e} {A} {s}
                      correct-combined-eq = trans shape-lemma (trans subst-shape S-eq)
                  in subst (Pos G {onObj m₂ A}) correct-combined-eq p ≡ p
cancel-shape-eq {ℓ} {F} {G} {m₁} {m₂} {e} {A} {s} {p} =
  subst-cancel-pos {ℓ} {F} {G} {m₁} {m₂} {e} {A} {s} {p}

-- Symmetrization of equations (reversing the evidence of ≃⇒ℱ)
--
-- 对称化等式（将 ≃⇒ℱ 的证据反过来）
onShape-eq-sym : ∀ {ℓ} {F G : Cosmos ℓ} {m₁ m₂ : F ⇒ℱ G}
               → (h : m₁ ≃⇒ℱ m₂) {A : Obj F} (s : Shape F A)
               → onShape m₂ s ≡ subst (Shape G) (onObj-eq h A) (onShape m₁ s)
onShape-eq-sym {G = G} h {A} s =
  let
    eqO = onObj-eq h A
    eqSh = onShape-eq h s
  in
  trans (sym (subst-inv' (Shape G) eqO))
        (cong (subst (Shape G) eqO) (sym eqSh))

onHom-eq-sym : ∀ {ℓ} {F G : Cosmos ℓ} {m₁ m₂ : F ⇒ℱ G}
             → (h : m₁ ≃⇒ℱ m₂) {A B : Obj F} (f : Hom F A B)
             → onHom m₂ f ≡ subst₂ (Hom G) (onObj-eq h A) (onObj-eq h B) (onHom m₁ f)
onHom-eq-sym {G = G} h {A} {B} f =
  let
    eqOA = onObj-eq h A
    eqOB = onObj-eq h B
    eqH = onHom-eq h f
  in
  trans (sym (subst-inv₂' eqOA eqOB))
        (cong (subst₂ (Hom G) eqOA eqOB) (sym eqH))
