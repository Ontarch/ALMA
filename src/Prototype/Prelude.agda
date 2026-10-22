{-
Semantic Bridge between Agda and ALMA
Agda 与 ALMA 之间的语义桥梁

Self-referential closure of the type system -- Epistemic cycle (transcendental framework)
类型系统的自指闭包 -- 认识论循环（先验框架）

The self-evident ground of the judgment form Γ ⊢ t : A -- Being (abstract logic)
判断形式 Γ ⊢ t : A 的自明基础 -- 存在（抽象逻辑）

The postulation of the type universe Set -- Cosmos (dynamic whole)
类型宇宙 Set 的公设 -- 宇宙（动态整体）

Closed term t : A -- Beings (concrete forms)
封闭项 t : A -- 存在者（具体形式）

Dependent sum type Σ A B -- Existential quantifier (encapsulates a being and its proof)
依赖和类型 Σ A B -- 存在量词（封装了一个存在者及其证明）

The empty type ⊥ has no closed terms -- Nothingness
空类型 ⊥ 没有封闭项 -- 虚无

Identity type constructor refl : t ≡ t -- Law of Identity
同一性类型构造子 refl : t ≡ t -- 同一律

Empty type elimination ⊥-elim -- Law of Non-Contradiction
空类型消去 ⊥-elim -- 矛盾律
-}

{-# OPTIONS --safe --cubical-compatible --exact-split --guardedness --double-check #-}

module Prototype.Prelude where

open import Agda.Primitive using (lsuc; Setω; _⊔_; Level) public
open import Level using (Lift; lift; 0ℓ) public
open import Data.Empty.Polymorphic using (⊥; ⊥-elim) public
open import Data.Unit.Polymorphic.Base using (⊤; tt) public
open import Data.Bool.Base using (Bool; false; true; _∧_; _∨_; if_then_else_; not; T) public
open import Data.Nat.Base using (_≤_; ℕ; _+_; _∸_; _*_; _≡ᵇ_; _<ᵇ_; s≤s; suc; z≤n; zero; _≤ᵇ_; _≥_; _<_; _>_; _≯_; pred) public
open import Data.Nat.Properties using (_≟_; _<?_; _>?_; ≡ᵇ⇒≡; ≡⇒≡ᵇ; <⇒<ᵇ; <ᵇ⇒<; ≮⇒≥; +-assoc; +-∸-assoc; +-comm; +-identityˡ; +-identityʳ; ≡-irrelevant; m≤n+m; m≤n⇒m≤1+n; m≤n⇒m∸n≡0; m+n∸m≡n; +-mono-<; +-mono-≤; n≤1+n; ≤-pred; ≤-refl; +-suc; ≤-trans) public
open import Data.Fin.Base using (Fin; suc; zero; fromℕ; splitAt; toℕ) public
open import Data.Fin.Properties using (suc-injective; toℕ-injective; toℕ<n) public
open import Data.Product.Base using (Σ; _,_; proj₁; proj₂; _×_; Σ-syntax; ∃; ∃-syntax) public
open import Data.Product.Properties using (≡-dec; ,-injective) public
open import Data.Sum.Base using (_⊎_; inj₁; inj₂; [_,_]) public
open import Data.Sum.Properties using (inj₁-injective; inj₂-injective) public
open import Data.Maybe.Base using (Maybe; just; nothing; map; maybe) public
open import Data.List.Base using (List; []; _∷_; _++_; any; all; foldl; foldr) public
open import Data.List.Membership.Propositional using (_∈_) public
open import Data.List.Relation.Unary.Any using (here; there) public
open import Function.Base using (_∘_; _$_; _|>_; case_of_; const; flip; id) public
open import Relation.Binary.PropositionalEquality using (_≡_; [_]; refl; cong; cong₂; J; inspect; subst; subst₂; sym; trans) public
open import Relation.Binary.PropositionalEquality.Properties public
open Relation.Binary.PropositionalEquality.Properties.≡-Reasoning public
open import Relation.Binary.Construct.Closure.ReflexiveTransitive using (Star; ε; _◅_; _◅◅_; _▻_; _▻▻_; reverse; fold; gfold; gfoldl; concat) public
open import Relation.Nullary using (Dec; no; yes; contradiction; Irrelevant) public
open import Relation.Nullary.Decidable using (does; ⌊_⌋; False; isYes; map′; toWitness; toWitnessFalse; True) public
open import Relation.Binary using (IsEquivalence) public

open import Categories.Category public
open import Categories.Adjoint public
open import Categories.Morphism.Reasoning public
open import Categories.Yoneda public
open import Categories.Functor using (Functor; _∘F_) public

-- Polymorphic negation and inequality
-- 多态否定与不等关系
¬_ : ∀ {ℓ} → Set ℓ → Set ℓ
¬_ {ℓ} A = A → ⊥ {ℓ}
infix 4 _≢_
_≢_ : ∀ {ℓ} {A : Set ℓ} → A → A → Set ℓ
x ≢ y = ¬ (x ≡ y)

-- Ex nihilo creation and reduction to nothingness are logically excluded
-- 逻辑上排除了无中生有与归于虚无
noExNihilo : ∀ {ℓ} → ¬ (⊥ {ℓ})
noExNihilo ()
noAnnihilation : ∀ {ℓ} {A : Set ℓ} → Σ A (λ _ → ⊤ {ℓ}) → ¬ (A → ⊥ {ℓ})
noAnnihilation (a , _) f = f a

-- Basic equational tools
-- 基础等式推理工具
transReflˡ : ∀ {ℓ} {A : Set ℓ} {x y : A} (eq : x ≡ y) → trans refl eq ≡ eq
transReflˡ refl = refl
trans-assoc' : ∀ {ℓ} {A : Set ℓ} {x y z w : A} (eq1 : x ≡ y) (eq2 : y ≡ z) (eq3 : z ≡ w)
             → trans (trans eq1 eq2) eq3 ≡ trans eq1 (trans eq2 eq3)
trans-assoc' refl refl refl = refl
sym-sym : ∀ {ℓ} {A : Set ℓ} {x y : A} (eq : x ≡ y) → eq ≡ sym (sym eq)
sym-sym refl = refl
sym-trans : ∀ {ℓ} {A : Set ℓ} {x y z : A} (eq1 : x ≡ y) (eq2 : y ≡ z)
          → sym (trans eq1 eq2) ≡ trans (sym eq2) (sym eq1)
sym-trans refl refl = refl
cong-sym : ∀ {a b} {A : Set a} {B : Set b} (f : A → B) {x y : A} (p : x ≡ y)
          → cong f (sym p) ≡ sym (cong f p)
cong-sym f refl = refl
cong-sym-sym : ∀ {ℓA ℓB} {A : Set ℓA} {B : Set ℓB} (f : A → B)
             → ∀ {x y} (eq : x ≡ y)
             → cong f (sym (sym eq)) ≡ cong f eq
cong-sym-sym f eq = sym (cong (cong f) (sym-sym eq))
Σ-≡ : ∀ {a b} {A : Set a} {B : A → Set b} {p q : Σ A B}
    → (eq₁ : proj₁ p ≡ proj₁ q)
    → (eq₂ : subst B eq₁ (proj₂ p) ≡ proj₂ q)
    → p ≡ q
Σ-≡ refl refl = refl

-- Basic properties of subst
-- subst 的基础性质
subst-refl-id : ∀ {ℓA ℓB} {A : Set ℓA} (B : A → Set ℓB) {x : A} → (b : B x) → subst B refl b ≡ b
subst-refl-id B b = refl
subst-inv : ∀ {ℓA ℓB} {A : Set ℓA} {B : A → Set ℓB} {a1 a2 : A} (eq : a1 ≡ a2) {b : B a1}
          → subst B (sym eq) (subst B eq b) ≡ b
subst-inv refl = refl
subst-inv' : ∀ {ℓA ℓB} {A : Set ℓA} (B : A → Set ℓB) {a1 a2 : A} (eq : a1 ≡ a2) {b : B a2}
           → subst B eq (subst B (sym eq) b) ≡ b
subst-inv' B refl = refl
subst-comp : ∀ {ℓA ℓB} {A : Set ℓA} {B : A → Set ℓB} {x y z : A} 
           (eq1 : x ≡ y) (eq2 : y ≡ z) {b : B x}
           → subst B eq2 (subst B eq1 b) ≡ subst B (trans eq1 eq2) b
subst-comp refl refl = refl
subst-comb : ∀ {i j : Level} {A : Set i} (Q : A → Set j) {x y z : A} (p : x ≡ y) (q : y ≡ z) (a : Q x)
            → subst Q (trans p q) a ≡ subst Q q (subst Q p a)
subst-comb Q refl refl a = refl
subst-sym-swap : ∀ {ℓ} {A : Set ℓ} (P : A → Set ℓ) {x y : A} (eq : x ≡ y) {px : P x} {py : P y}
               → subst P eq px ≡ py
               → px ≡ subst P (sym eq) py
subst-sym-swap P refl refl = refl
subst-sym-comp : ∀ {ℓA ℓB} {A : Set ℓA} {f : A → Set ℓB} {x y z : A}
               → (p : x ≡ y) (q : y ≡ z) {s : f z}
               → subst f (sym p) (subst f (sym q) s) 
               ≡ subst f (sym (trans p q)) s
subst-sym-comp {f = f} p q {s} =
  trans
    (subst-comp {B = f} (sym q) (sym p))
    (cong (λ eq → subst f eq s) (sym (sym-trans p q)))
subst-sym-comp3 : ∀ {ℓA ℓB} {A : Set ℓA} {B : A → Set ℓB} {x y z w : A}
                  (p : x ≡ y) (q : y ≡ z) (r : z ≡ w) {b : B w}
                → subst B (sym p) (subst B (sym q) (subst B (sym r) b))
                ≡ subst B (sym (trans p (trans q r))) b
subst-sym-comp3 refl refl refl = refl
subst-sym-eq-trans : ∀ {ℓA ℓB} {A : Set ℓA} (P : A → Set ℓB)
                     {x y z : A} (eq1 : x ≡ y) (eq2 : y ≡ z)
                     {u : P x} {v : P y} {w : P z}
                   → u ≡ subst P (sym eq1) v
                   → v ≡ subst P (sym eq2) w
                   → u ≡ subst P (sym (trans eq1 eq2)) w
subst-sym-eq-trans P eq1 eq2 h1 h2 =
  trans h1 (trans (cong (subst P (sym eq1)) h2)
                  (subst-sym-comp eq1 eq2))
transport-Shape-obj : ∀ {ℓ} (Obj : Set (lsuc ℓ)) (Shape : Obj → Set (lsuc ℓ))
                    → {X Y : Obj} → X ≡ Y → Shape X → Shape Y
transport-Shape-obj _ _ refl s = s
transport-Hom-obj : ∀ {ℓ} (Obj : Set (lsuc ℓ)) (Hom : Obj → Obj → Set (lsuc ℓ))
                  → {A₁ A₂ B₁ B₂ : Obj} → A₁ ≡ A₂ → B₁ ≡ B₂ → Hom A₁ B₁ → Hom A₂ B₂
transport-Hom-obj _ _ refl refl f = f
sym-subst-sym-comp : ∀ {ℓA ℓB} {A : Set ℓA} {f : A → Set ℓB} {x y z : A} 
                   → (p : x ≡ y) (q : y ≡ z) {s : f z}
                   → sym (subst-sym-comp p q {s = s})
                   ≡ trans (cong (λ eq → subst f eq s) (sym-trans p q))
                           (sym (subst-comp (sym q) (sym p) {b = s}))
sym-subst-sym-comp {f = f} p q {s} =
  begin
    sym (trans (subst-comp {B = f} (sym q) (sym p))
               (cong (λ eq → subst f eq s) (sym (sym-trans p q))))
  ≡⟨ sym-trans (subst-comp {B = f} (sym q) (sym p))
                (cong (λ eq → subst f eq s) (sym (sym-trans p q))) ⟩
    trans (sym (cong (λ eq → subst f eq s) (sym (sym-trans p q))))
          (sym (subst-comp {B = f} (sym q) (sym p)))
  ≡⟨ cong (λ x → trans x (sym (subst-comp {B = f} (sym q) (sym p))))
          (sym-cong {f = λ eq → subst f eq s} (sym (sym-trans p q))) ⟩
    trans (cong (λ eq → subst f eq s) (sym (sym (sym-trans p q))))
          (sym (subst-comp {B = f} (sym q) (sym p)))
  ≡⟨ cong (λ x → trans x (sym (subst-comp {B = f} (sym q) (sym p))))
          (cong-sym-sym (λ eq → subst f eq s) (sym-trans p q)) ⟩
    trans (cong (λ eq → subst f eq s) (sym-trans p q))
          (sym (subst-comp {B = f} (sym q) (sym p)))
  ∎

-- Binary subst tools
-- 二元 subst 工具
subst-target-source≡subst₂ : ∀ {a b p} {A : Set a} {B : Set b} {P : A → B → Set p}
  {a₁ a₂ : A} {b₁ b₂ : B}
  (eqA : a₁ ≡ a₂) (eqB : b₁ ≡ b₂)
  (x : P a₁ b₁)
  → subst (λ a → P a b₂) eqA (subst (λ b → P a₁ b) eqB x)
    ≡ subst₂ P eqA eqB x
subst-target-source≡subst₂ refl refl x = refl
subst-source-target≡subst₂ : ∀ {a b p} {A : Set a} {B : Set b} {P : A → B → Set p}
  {a₁ a₂ : A} {b₁ b₂ : B}
  (eqA : a₁ ≡ a₂) (eqB : b₁ ≡ b₂) (x : P a₁ b₁)
  → subst (λ b → P a₂ b) eqB (subst (λ a → P a b₁) eqA x)
    ≡ subst₂ P eqA eqB x
subst-source-target≡subst₂ refl refl x = refl
subst-inv₂' : ∀ {ℓA ℓB ℓC} {A : Set ℓA} {B : Set ℓB} {C : A → B → Set ℓC} 
            {a1 a2 : A} {b1 b2 : B} (eqA : a1 ≡ a2) (eqB : b1 ≡ b2) {c : C a2 b2}
            → subst₂ C eqA eqB (subst₂ C (sym eqA) (sym eqB) c) ≡ c
subst-inv₂' refl refl = refl
subst₂-comp : ∀ {ℓA ℓB ℓC} {A : Set ℓA} {B : Set ℓB} {C : A → B → Set ℓC}
            {a1 a2 a3 : A} {b1 b2 b3 : B}
            (eqA1 : a1 ≡ a2) (eqA2 : a2 ≡ a3)
            (eqB1 : b1 ≡ b2) (eqB2 : b2 ≡ b3)
            {c : C a1 b1}
            → subst₂ C eqA2 eqB2 (subst₂ C eqA1 eqB1 c) ≡ subst₂ C (trans eqA1 eqA2) (trans eqB1 eqB2) c
subst₂-comp refl refl refl refl = refl
subst₂-sym-comp : ∀ {ℓA ℓB ℓC} {A : Set ℓA} {B : Set ℓB} {f : A → B → Set ℓC} 
                  {x₁ y₁ z₁ : A} {x₂ y₂ z₂ : B}
                → (p₁ : x₁ ≡ y₁) (p₂ : x₂ ≡ y₂)
                → (q₁ : y₁ ≡ z₁) (q₂ : y₂ ≡ z₂)
                → {h : f z₁ z₂}
                → subst₂ f (sym p₁) (sym p₂) (subst₂ f (sym q₁) (sym q₂) h) 
                  ≡ subst₂ f (sym (trans p₁ q₁)) (sym (trans p₂ q₂)) h
subst₂-sym-comp {f = f} p₁ p₂ q₁ q₂ {h} =
  trans
    (subst₂-comp {C = f} (sym q₁) (sym p₁) (sym q₂) (sym p₂))
    (cong₂ (λ eq₁ eq₂ → subst₂ f eq₁ eq₂ h)
           (sym (sym-trans p₁ q₁))
           (sym (sym-trans p₂ q₂)))
subst₂-sym-eq-trans : ∀ {ℓA ℓB ℓC} {A : Set ℓA} {B : Set ℓB} (C : A → B → Set ℓC)
                      {a₁ a₂ a₃ : A} {b₁ b₂ b₃ : B}
                      (p1 : a₁ ≡ a₂) (q1 : b₁ ≡ b₂)
                      (p2 : a₂ ≡ a₃) (q2 : b₂ ≡ b₃)
                      {x : C a₁ b₁} {y : C a₂ b₂} {z : C a₃ b₃}
                    → x ≡ subst₂ C (sym p1) (sym q1) y
                    → y ≡ subst₂ C (sym p2) (sym q2) z
                    → x ≡ subst₂ C (sym (trans p1 p2)) (sym (trans q1 q2)) z
subst₂-sym-eq-trans C p1 q1 p2 q2 h1 h2 =
  trans h1 (trans (cong (λ t → subst₂ C (sym p1) (sym q1) t) h2)
                  (subst₂-sym-comp p1 q1 p2 q2))
cong-trans : ∀ {a b} {A : Set a} {B : Set b} {x y z : A} (f : A → B)
  → (p : x ≡ y) (q : y ≡ z)
  → cong f (trans p q) ≡ trans (cong f p) (cong f q)
cong-trans f refl refl = refl

-- General combinators
-- 通用组合子
iter : ∀ {ℓ : Level} {A : Set ℓ} → ℕ → (A → A) → A → A
iter zero f x = x
iter (suc n) f x = f (iter n f x)
comb : ∀ {ℓ₁ ℓ₂ ℓ₃ ℓ₄} {O₁ : Set ℓ₁} {C₁ : Set ℓ₂} {O₂ : Set ℓ₃} {C₂ : Set ℓ₄}
     → (O₁ → O₂) → (C₁ → C₂) → (O₁ × C₁) → (O₂ × C₂)
comb f-O f-C (o , c) = (f-O o , f-C c)

-- Polymorphic constructor inequality
-- 多态构造子不等关系
true≢false : true ≢ false
true≢false eq = subst (λ { true → ⊤ ; false → ⊥ }) eq tt

-- Natural number properties
-- 自然数性质
zero≢suc : ∀ {n : ℕ} → 0 ≢ suc n
zero≢suc ()
¬zero→suc : ∀ {i} → i ≢ 0 → i > 0
¬zero→suc {zero} ¬0 = ⊥-elim (¬0 refl)
¬zero→suc {suc _} _ = s≤s z≤n
n≢sucn : ∀ (n : ℕ) → n ≢ suc n
n≢sucn zero ()
n≢sucn (suc n) eq = n≢sucn n (cong pred eq)
suc≤→≤ : ∀ {m n} → suc m ≤ n → m ≤ n
suc≤→≤ p = ≤-trans (n≤1+n _) p
<⇒<ᵇ-eq : ∀ {m n : ℕ} → m < n → (m <ᵇ n) ≡ true
<⇒<ᵇ-eq {zero} {suc n} _ = refl
<⇒<ᵇ-eq {suc m} {suc n} p = <⇒<ᵇ-eq (≤-pred p)
≮⇒≥-poly : ∀ {m n : ℕ} → ¬ (m < n) → m ≥ n
≮⇒≥-poly {m} {zero} ¬m<0 = z≤n
≮⇒≥-poly {zero} {suc n} ¬0<suc = ⊥-elim (¬0<suc (s≤s z≤n))
≮⇒≥-poly {suc m} {suc n} ¬sucm<sucn = 
  s≤s (≮⇒≥-poly (λ m'<n → ¬sucm<sucn (s≤s m'<n)))
m≤n→n≡m+n∸m : ∀ {m n} → m ≤ n → n ≡ m + (n ∸ m)
m≤n→n≡m+n∸m {zero} {n} _ = sym (+-identityˡ n)
m≤n→n≡m+n∸m {suc m} {suc n} p = cong suc (m≤n→n≡m+n∸m (≤-pred p))
+-four-rearrange : ∀ a b c d → (a + b) + (c + d) ≡ (a + c) + (b + d)
+-four-rearrange a b c d =
  begin
    (a + b) + (c + d)
      ≡⟨ sym (+-assoc (a + b) c d) ⟩
    ((a + b) + c) + d
      ≡⟨ cong (λ x → x + d) (+-assoc a b c) ⟩
    (a + (b + c)) + d
      ≡⟨ cong (λ x → x + d) (cong (a +_) (+-comm b c)) ⟩
    (a + (c + b)) + d
      ≡⟨ cong (λ x → x + d) (sym (+-assoc a c b)) ⟩
    ((a + c) + b) + d
      ≡⟨ +-assoc (a + c) b d ⟩
    (a + c) + (b + d)
  ∎
0<ᵇn≡false : ∀ n → (n <ᵇ 0) ≡ false
0<ᵇn≡false zero = refl
0<ᵇn≡false (suc n) = refl
<ᵇ-self-false : ∀ n → (n <ᵇ n) ≡ false
<ᵇ-self-false zero = refl
<ᵇ-self-false (suc n) = <ᵇ-self-false n
subst-inequality : {a b n m : ℕ} → a ≡ n → b ≡ m → n > m → a > b
subst-inequality a≡n b≡m n>m =
  subst (λ x → x > _) (sym a≡n) (subst (λ x → _ > x) (sym b≡m) n>m)

-- Finite set properties
-- 有限集性质
toFin : ∀ {n} → ℕ → Maybe (Fin n)
toFin {zero} _ = nothing
toFin {suc n} zero = just zero
toFin {suc n} (suc i) with toFin {n} i
... | just x = just (suc x)
... | nothing = nothing
toFin-suc : ∀ {n} (k : ℕ) → toFin {suc n} (suc k) ≡ map suc (toFin {n} k)
toFin-suc {n} k with toFin {n} k
... | just x = refl
... | nothing = refl
toFin-toℕ : ∀ {n} (i : Fin n) → toFin (toℕ i) ≡ just i
toFin-toℕ zero = refl
toFin-toℕ (suc i) = trans (toFin-suc (toℕ i)) (cong (map suc) (toFin-toℕ i))
