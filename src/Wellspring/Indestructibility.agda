------------------------------------------------------------------------
-- Eternity and indestructibility
--
-- Fundamental forms of existence → two construction modes → process
-- identity → core ontological theorem → uniqueness theorem →
-- historical paths and ontological process identity → distinction
-- between epistemic equivalence and ontological identity.
--
-- 永恒性与不可消减性
--
-- 基础存在形式 → 两种构造模式 → 过程同一性 → 核心存在论定理 → 唯一
-- 性定理 → 历史路径与本体论过程同一 → 认识论等价与本体论同一的区分。
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --exact-split --guardedness --double-check #-}

module Wellspring.Indestructibility where

open import Wellspring.Properties.Dynamics public

-- Fundamental forms of existence: Eternal streams and persistence predicates
-- 基础存在形式：永恒流与持存谓词
record Stream {ℓ} (A : Set ℓ) : Set ℓ where
  coinductive
  field head : A
        tail : Stream A
open Stream public

record Always {ℓ ℓ'} {A : Set ℓ} (P : A → Set ℓ') (s : Stream A) : Set (ℓ ⊔ ℓ') where
  coinductive
  field head : P (Stream.head s)
        tail : Always P (Stream.tail s)
open Always public

-- Construction Mode 1: Epistemic perspective — Direct coinductive definition of constant streams
-- 构造模式一：认识论视角 —— 直接余归纳定义常量流
constStream : ∀ {ℓ} {A : Set ℓ} → A → Stream A
constStream a .Stream.head = a
constStream a .Stream.tail = constStream a
constStream-always-gen : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {P : A → Set ℓ₂} (a : A) → P a → Always P (constStream a)
constStream-always-gen a p .head = p
constStream-always-gen a p .tail = constStream-always-gen a p

-- Construction Mode 2: Ontological perspective — Coalgebra + anamorphism
-- 构造模式二：本体论视角 —— 余代数 + ana
StreamF : ∀ {ℓ₁ ℓ₂} → Set ℓ₁ → Set ℓ₂ → Set (ℓ₁ ⊔ ℓ₂)
StreamF A X = A × X
ana : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {X : Set ℓ₂} → (X → StreamF A X) → X → Stream A
ana α x .head = proj₁ (α x)
ana α x .tail = ana α (proj₂ (α x))

-- Functor structure and ana fusion law (technical foundation)
-- 函子结构与 ana 融合律（技术基础）
record Functor' {ℓ₁ ℓ₂} (F : Set ℓ₁ → Set ℓ₂) : Set (lsuc ℓ₁ ⊔ ℓ₂) where
  field
    imap : ∀ {A B : Set ℓ₁} → (A → B) → F A → F B
    imap-id : ∀ {A : Set ℓ₁} → imap {A} id ≡ id
    imap-comp : ∀ {A B C : Set ℓ₁} {f : A → B} {g : B → C} → imap (g ∘ f) ≡ imap g ∘ imap f
open Functor' ⦃...⦄ public using (imap)
instance
  StreamF-Functor : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} → Functor' {ℓ₁ = ℓ₂} {ℓ₂ = ℓ₁ ⊔ ℓ₂} (StreamF A)
  StreamF-Functor {ℓ₁} {ℓ₂} {A} = record
    { imap = λ { f (a , x) → (a , f x) }
    ; imap-id = refl
    ; imap-comp = refl
    }

-- Stream equivalence relation (bisimulation)
-- 流等价关系（互模拟）
record _≈_ {ℓ} {A : Set ℓ} (s t : Stream A) : Set ℓ where
  coinductive
  field head≈ : Stream.head s ≡ Stream.head t
        tail≈ : Stream.tail s ≈ Stream.tail t
open _≈_ public

IsBisimulation : ∀ {ℓ} {A : Set ℓ} → (Stream A → Stream A → Set ℓ) → Set ℓ
IsBisimulation R = ∀ {s t} → R s t → 
  (Stream.head s ≡ Stream.head t) × R (Stream.tail s) (Stream.tail t)
bisimulation-principle : ∀ {ℓ} {A : Set ℓ} {R : Stream A → Stream A → Set ℓ}
                       → IsBisimulation R
                       → ∀ {s t} → R s t → s ≈ t
bisimulation-principle {A = A} {R = R} isBisim {s} {t} r = aux s t r
  where
    aux : (s' t' : Stream A) → R s' t' → s' ≈ t'
    aux s' t' r' ._≈_.head≈ = proj₁ (isBisim r')
    aux s' t' r' ._≈_.tail≈ = aux (Stream.tail s') (Stream.tail t') (proj₂ (isBisim r'))

≈-refl : ∀ {ℓ} {A : Set ℓ} {s : Stream A} → s ≈ s
≈-refl .head≈ = refl
≈-refl .tail≈ = ≈-refl

≈-sym : ∀ {ℓ} {A : Set ℓ} {s t : Stream A} → s ≈ t → t ≈ s
≈-sym s≈t .head≈ = sym (s≈t .head≈)
≈-sym s≈t .tail≈ = ≈-sym (s≈t .tail≈)

≈-trans : ∀ {ℓ} {A : Set ℓ} {s t u : Stream A} → s ≈ t → t ≈ u → s ≈ u
≈-trans s≈t t≈u .head≈ = trans (s≈t .head≈) (t≈u .head≈)
≈-trans s≈t t≈u .tail≈ = ≈-trans (s≈t .tail≈) (t≈u .tail≈)

record ≈-hetero {ℓ₁ ℓ₂} {A : Set ℓ₁} {B : Set ℓ₂} (s₁ : Stream A) (s₂ : Stream B) (f : A → B) : Set (ℓ₁ ⊔ ℓ₂) where
  coinductive
  field
    head≈ : f (Stream.head s₁) ≡ Stream.head s₂
    tail≈ : ≈-hetero (Stream.tail s₁) (Stream.tail s₂) f
open ≈-hetero public

IsHeteroBisimulation : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {B : Set ℓ₂}
                     → (A → B) → (Stream A → Stream B → Set (ℓ₁ ⊔ ℓ₂)) → Set (ℓ₁ ⊔ ℓ₂)
IsHeteroBisimulation f R = ∀ {s t} → R s t →
  (f (Stream.head s) ≡ Stream.head t) × R (Stream.tail s) (Stream.tail t)
hetero-bisimulation-principle : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {B : Set ℓ₂} {f : A → B}
                               {R : Stream A → Stream B → Set (ℓ₁ ⊔ ℓ₂)}
                               → IsHeteroBisimulation f R
                               → ∀ {s t} → R s t → ≈-hetero s t f
hetero-bisimulation-principle {A = A} {B = B} {f = f} {R = R} isHeteroBisim {s} {t} r = aux s t r
  where
    aux : (s' : Stream A) (t' : Stream B) → R s' t' → ≈-hetero s' t' f
    aux s' t' r' .≈-hetero.head≈ = proj₁ (isHeteroBisim r')
    aux s' t' r' .≈-hetero.tail≈ = aux (Stream.tail s') (Stream.tail t') (proj₂ (isHeteroBisim r'))

-- Basic stream operations
-- 流的基础操作
stream-tail-n : ∀ {ℓ} {A : Set ℓ} → Stream A → ℕ → Stream A
stream-tail-n s zero    = s
stream-tail-n s (suc n) = stream-tail-n (s .tail) n
stream-tail-n-add : ∀ {ℓ} {A : Set ℓ} (m n : ℕ) (s : Stream A)
  → stream-tail-n s (m + n) ≈ stream-tail-n (stream-tail-n s m) n
stream-tail-n-add zero n s = ≈-refl
stream-tail-n-add (suc m) n s = stream-tail-n-add m n (s .tail)
stream-tail-n-cong : ∀ {ℓ} {A : Set ℓ} {s t : Stream A} (n : ℕ)
  → s ≈ t → stream-tail-n s n ≈ stream-tail-n t n
stream-tail-n-cong zero eq = eq
stream-tail-n-cong (suc n) eq = stream-tail-n-cong n (eq .tail≈)
obsS : ∀ {ℓ₁ ℓ₂} {O : Set ℓ₁} {C : Set ℓ₂} → Stream (O × C) → ℕ → O
obsS s n = proj₁ (head (stream-tail-n s n))
WeakHomS : ∀ {ℓ₁ ℓ₂} {O : Set ℓ₁} {C : Set ℓ₂} → Stream (O × C) → Set ℓ₁
WeakHomS s = ∀ n m → obsS s n ≡ obsS s m
ChangesS : ∀ {ℓ₁ ℓ₂} {O : Set ℓ₁} {C : Set ℓ₂} → Stream (O × C) → Set ℓ₁
ChangesS s = ∃ λ n → obsS s n ≢ obsS s (suc n)
ΔS : ∀ {ℓ₁ ℓ₂} {O : Set ℓ₁} {C : Set ℓ₂} → Stream (O × C) → Set ℓ₁
ΔS s = ∃ λ n → ∃ λ m → obsS s n ≢ obsS s m
constStream-tail-n : ∀ {ℓ} {A : Set ℓ} (a : A) (n : ℕ)
                   → stream-tail-n (constStream a) n ≡ constStream a
constStream-tail-n a zero    = refl
constStream-tail-n a (suc n) = constStream-tail-n a n
constStream-obsS-constant : ∀ {ℓ₁ ℓ₂} {O : Set ℓ₁} {C : Set ℓ₂} (a : O × C) (n : ℕ)
                          → obsS (constStream a) n ≡ proj₁ a
constStream-obsS-constant a n =
  begin
    obsS (constStream a) n
      ≡⟨ refl ⟩
    proj₁ (head (stream-tail-n (constStream a) n))
      ≡⟨ cong (λ s → proj₁ (head s)) (constStream-tail-n a n) ⟩
    proj₁ (head (constStream a))
      ≡⟨ refl ⟩
    proj₁ a
  ∎
map-stream : ∀ {A B : Set} → (A → B) → Stream A → Stream B
map-stream f s .head = f (head s)
map-stream f s .tail = map-stream f (tail s)
map-stream-tail-n : ∀ {A B : Set} (f : A → B) (s : Stream A) (n : ℕ)
                  → head (stream-tail-n (map-stream f s) n) ≡ f (head (stream-tail-n s n))
map-stream-tail-n f s zero = refl
map-stream-tail-n f s (suc n) = map-stream-tail-n f (tail s) n

-- Transitivity of heterogeneous bisimulation
-- 异质互模拟传递性
≈-hetero-trans : ∀ {ℓ₁ ℓ₂ ℓ₃} {A : Set ℓ₁} {B : Set ℓ₂} {C : Set ℓ₃} (f : A → B) (g : B → C)
                → (s₁ : Stream A) (s₂ : Stream B) (s₃ : Stream C)
                → ≈-hetero s₁ s₂ f
                → ≈-hetero s₂ s₃ g
                → ≈-hetero s₁ s₃ (g ∘ f)
≈-hetero-trans f g s₁ s₂ s₃ eq1 eq2 = aux eq1 eq2
  where
    aux : ∀ {s1 s2 s3} → ≈-hetero s1 s2 f → ≈-hetero s2 s3 g → ≈-hetero s1 s3 (g ∘ f)
    aux eq1' eq2' .≈-hetero.head≈ = trans (cong g (eq1' .head≈)) (eq2' .head≈)
    aux eq1' eq2' .≈-hetero.tail≈ = aux (eq1' .tail≈) (eq2' .tail≈)

-- Bisimulation relation for heterogeneous bisimulation proofs
-- 异质互模拟证明的互模拟关系
record _≈ₚᵣₒₒբ_ {ℓ₁ ℓ₂} {A : Set ℓ₁} {B : Set ℓ₂} {f : A → B} {s : Stream A} {t : Stream B}
                (e1 e2 : ≈-hetero s t f) : Set (ℓ₁ ⊔ ℓ₂) where
  coinductive
  field
    head≈ₚ : ≈-hetero.head≈ e1 ≡ ≈-hetero.head≈ e2
    tail≈ₚ : (≈-hetero.tail≈ e1) ≈ₚᵣₒₒբ (≈-hetero.tail≈ e2)
open _≈ₚᵣₒₒբ_ public

≈ₚᵣₒₒբ-refl : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {B : Set ℓ₂} {f : A → B} {s : Stream A} {t : Stream B}
             → {e : ≈-hetero s t f}
             → e ≈ₚᵣₒₒբ e
≈ₚᵣₒₒբ-refl .head≈ₚ = refl
≈ₚᵣₒₒբ-refl .tail≈ₚ = ≈ₚᵣₒₒբ-refl
≈ₚᵣₒₒբ-sym : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {B : Set ℓ₂} {f : A → B} {s : Stream A} {t : Stream B}
            → {e1 e2 : ≈-hetero s t f}
            → e1 ≈ₚᵣₒₒբ e2
            → e2 ≈ₚᵣₒₒբ e1
≈ₚᵣₒₒբ-sym eq .head≈ₚ = sym (eq .head≈ₚ)
≈ₚᵣₒₒբ-sym eq .tail≈ₚ = ≈ₚᵣₒₒբ-sym (eq .tail≈ₚ)
≈ₚᵣₒₒբ-trans : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {B : Set ℓ₂} {f : A → B} {s : Stream A} {t : Stream B}
             → {e1 e2 e3 : ≈-hetero s t f}
             → e1 ≈ₚᵣₒₒբ e2
             → e2 ≈ₚᵣₒₒբ e3
             → e1 ≈ₚᵣₒₒբ e3
≈ₚᵣₒₒբ-trans eq1 eq2 .head≈ₚ = trans (eq1 .head≈ₚ) (eq2 .head≈ₚ)
≈ₚᵣₒₒբ-trans eq1 eq2 .tail≈ₚ = ≈ₚᵣₒₒբ-trans (eq1 .tail≈ₚ) (eq2 .tail≈ₚ)

≈-hetero-trans-assoc-head
  : ∀ {ℓ₁ ℓ₂ ℓ₃ ℓ₄}
    {A : Set ℓ₁} {B : Set ℓ₂} {C : Set ℓ₃} {D : Set ℓ₄}
  → (f : A → B) (g : B → C) (h : C → D)
  → {x : A} {y : B} {z : C} {w : D}
  → (eq1 : f x ≡ y)
  → (eq2 : g y ≡ z)
  → (eq3 : h z ≡ w)
  → trans (cong h (trans (cong g eq1) eq2)) eq3
    ≡ trans (cong (h ∘ g) eq1) (trans (cong h eq2) eq3)
≈-hetero-trans-assoc-head f g h eq1 eq2 eq3 =
  trans
    (cong (λ p → trans p eq3)
      (sym (trans-cong (cong g eq1))))
    (trans
      (trans-assoc' (cong h (cong g eq1)) (cong h eq2) eq3)
      (cong (λ p → trans p (trans (cong h eq2) eq3))
        (sym (cong-∘ eq1))))

-- Associativity of heterogeneous bisimulation transitivity
-- 异质互模拟传递性的结合律
≈-hetero-trans-assoc
  : ∀ {ℓ₁ ℓ₂ ℓ₃ ℓ₄}
    {A : Set ℓ₁} {B : Set ℓ₂} {C : Set ℓ₃} {D : Set ℓ₄}
  → (f : A → B) (g : B → C) (h : C → D)
  → (s : Stream A) (t : Stream B) (u : Stream C) (v : Stream D)
  → (e1 : ≈-hetero s t f) (e2 : ≈-hetero t u g) (e3 : ≈-hetero u v h)
  → ≈-hetero-trans (g ∘ f) h s u v (≈-hetero-trans f g s t u e1 e2) e3
    ≈ₚᵣₒₒբ
    ≈-hetero-trans f (h ∘ g) s t v e1 (≈-hetero-trans g h t u v e2 e3)
≈-hetero-trans-assoc f g h s t u v e1 e2 e3 .head≈ₚ =
  ≈-hetero-trans-assoc-head f g h (head≈ e1) (head≈ e2) (head≈ e3)
≈-hetero-trans-assoc f g h s t u v e1 e2 e3 .tail≈ₚ =
  ≈-hetero-trans-assoc f g h
    (Stream.tail s) (Stream.tail t) (Stream.tail u) (Stream.tail v)
    (≈-hetero.tail≈ e1) (≈-hetero.tail≈ e2) (≈-hetero.tail≈ e3)

-- Unit laws of heterogeneous bisimulation
-- 异质互模拟的单位律
≈-hetero-refl : ∀ {ℓ} {A : Set ℓ} (s : Stream A) → ≈-hetero s s id
≈-hetero-refl s .head≈ = refl
≈-hetero-refl s .tail≈ = ≈-hetero-refl (Stream.tail s)
≈-hetero-trans-left-unit : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {B : Set ℓ₂}
    {f : A → B} {s : Stream A} {t : Stream B}
    (eq : ≈-hetero s t f)
    → ≈-hetero-trans f id s t t eq (≈-hetero-refl t) ≈ₚᵣₒₒբ eq
≈-hetero-trans-left-unit eq .head≈ₚ = 
  trans (trans-reflʳ _) (cong-id _)
≈-hetero-trans-left-unit eq .tail≈ₚ = ≈-hetero-trans-left-unit (eq .tail≈)
≈-hetero-trans-right-unit : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {B : Set ℓ₂}
    {f : A → B} {s : Stream A} {t : Stream B}
    (eq : ≈-hetero s t f)
    → ≈-hetero-trans id f s s t (≈-hetero-refl s) eq ≈ₚᵣₒₒբ eq
≈-hetero-trans-right-unit eq .head≈ₚ = transReflˡ _
≈-hetero-trans-right-unit eq .tail≈ₚ = ≈-hetero-trans-right-unit (eq .tail≈)

-- Category of heterogeneous bisimulations
-- 异质互模拟范畴
HeteroObj : ∀ ℓ → Set (lsuc ℓ)
HeteroObj ℓ = Σ (Set ℓ) (λ A → Stream A)
HeteroHom : ∀ {ℓ₁ ℓ₂} → HeteroObj ℓ₁ → HeteroObj ℓ₂ → Set (ℓ₁ ⊔ ℓ₂)
HeteroHom (A , s) (B , t) = Σ (A → B) (λ f → ≈-hetero s t f)
hetero-id : ∀ {ℓ} {X : HeteroObj ℓ} → HeteroHom X X
hetero-id {X = (A , s)} = (id , ≈-hetero-refl s)
hetero-comp : ∀ {ℓ₁ ℓ₂ ℓ₃} {X : HeteroObj ℓ₁} {Y : HeteroObj ℓ₂} {Z : HeteroObj ℓ₃}
            → HeteroHom Y Z → HeteroHom X Y → HeteroHom X Z
hetero-comp {X = (A , s)} {Y = (B , t)} {Z = (C , u)} (g , eq2) (f , eq1) =
  (g ∘ f , ≈-hetero-trans f g s t u eq1 eq2)
hetero-eq : ∀ {ℓ₁ ℓ₂} {X : HeteroObj ℓ₁} {Y : HeteroObj ℓ₂}
          → HeteroHom X Y → HeteroHom X Y → Set (ℓ₁ ⊔ ℓ₂)
hetero-eq {X = (A , s)} {Y = (B , t)} (f₁ , eq1) (f₂ , eq2) =
  Σ (f₁ ≡ f₂) (λ { refl → eq1 ≈ₚᵣₒₒբ eq2 })
hetero-comp-assoc : ∀ {ℓ₁ ℓ₂ ℓ₃ ℓ₄}
                  → {X : HeteroObj ℓ₁} {Y : HeteroObj ℓ₂} {Z : HeteroObj ℓ₃} {W : HeteroObj ℓ₄}
                  → (h : HeteroHom Z W) (g : HeteroHom Y Z) (f : HeteroHom X Y)
                  → hetero-eq (hetero-comp (hetero-comp h g) f) (hetero-comp h (hetero-comp g f))
hetero-comp-assoc {X = (A , s)} {Y = (B , t)} {Z = (C , u)} {W = (D , v)}
                  (h , eq3) (g , eq2) (f , eq1) =
  (refl , ≈ₚᵣₒₒբ-sym (≈-hetero-trans-assoc f g h s t u v eq1 eq2 eq3))
hetero-comp-left-unit : ∀ {ℓ₁ ℓ₂} {X : HeteroObj ℓ₁} {Y : HeteroObj ℓ₂}
                      → (f : HeteroHom X Y)
                      → hetero-eq (hetero-comp hetero-id f) f
hetero-comp-left-unit {X = (A , s)} {Y = (B , t)} (f , eq) =
  (refl , ≈-hetero-trans-left-unit eq)
hetero-comp-right-unit : ∀ {ℓ₁ ℓ₂} {X : HeteroObj ℓ₁} {Y : HeteroObj ℓ₂}
                       → (f : HeteroHom X Y)
                       → hetero-eq (hetero-comp f hetero-id) f
hetero-comp-right-unit {X = (A , s)} {Y = (B , t)} (f , eq) =
  (refl , ≈-hetero-trans-right-unit eq)

-- Indexed streams + Terminal coalgebra section
-- 索引流 + 终结余代数部分
anaH : ∀ {ℓA ℓB ℓX : Level} {A : Set ℓA} {B : Set ℓB} {X : Set ℓX}
       → (α : X → A × X) → (f : A → B) → X → Stream B
anaH α f x .head = f (proj₁ (α x))
anaH α f x .tail = anaH α f (proj₂ (α x))
stream-β : ∀ {ℓB : Level} {B : Set ℓB} → Stream B → B × Stream B
stream-β s = head s , tail s
record Homo {ℓA ℓB ℓX : Level} {A : Set ℓA} {B : Set ℓB} {X : Set ℓX}
            (α : X → A × X) (f : A → B) (φ : X → Stream B) : Set (ℓA ⊔ ℓB ⊔ ℓX) where
  constructor homo
  field
    comm : ∀ x → stream-β (φ x) ≡ (f (proj₁ (α x)) , φ (proj₂ (α x)))
open Homo public
anaH-homo : ∀ {ℓA ℓB ℓX : Level} {A : Set ℓA} {B : Set ℓB} {X : Set ℓX}
            → (α : X → A × X) → (f : A → B) → Homo α f (anaH α f)
anaH-homo α f .comm x = refl
unique-hom : ∀ {ℓA ℓB ℓX : Level} {A : Set ℓA} {B : Set ℓB} {X : Set ℓX}
             → (α : X → A × X) → (f : A → B) → (φ : X → Stream B)
             → Homo α f φ → ∀ x → φ x ≈ anaH α f x
unique-hom α f φ h x = aux x
  where
    aux : ∀ x → φ x ≈ anaH α f x
    aux x .head≈ = cong proj₁ (h .comm x)
    aux x .tail≈ with tail (φ x) | cong proj₂ (h .comm x)
    ... | .(φ (proj₂ (α x))) | refl = aux (proj₂ (α x))
terminal : ∀ {ℓA ℓB ℓX : Level} {A : Set ℓA} {B : Set ℓB} {X : Set ℓX}
           → (α : X → A × X) → (f : A → B)
           → Σ (X → Stream B) λ h →
             Homo α f h × (∀ φ → Homo α f φ → ∀ x → φ x ≈ h x)
terminal α f = anaH α f , anaH-homo α f , unique-hom α f

-- Indexed streams
-- 索引流
record IStream {ℓI ℓF : Level}
               (I : Set ℓI)
               (F : I → Set ℓF)
               (next : I → I)
               (i : I)
               : Set (ℓI ⊔ ℓF) where
  coinductive
  field
    hd : F i
    tl : IStream I F next (next i)
open IStream public

-- Indexed stream bisimulation
-- 索引流互模拟
record _≈ᵢ_ {ℓI ℓF : Level}
            {I : Set ℓI}
            {F : I → Set ℓF}
            {next : I → I}
            {i : I}
            (s t : IStream I F next i)
            : Set (ℓI ⊔ ℓF) where
  coinductive
  field
    hd≈ : hd s ≡ hd t
    tl≈ : _≈ᵢ_ (tl s) (tl t)
open _≈ᵢ_ public

-- Indexed stream destructor
-- 索引流析构函数
IStream-β : ∀ {ℓI ℓF : Level}
            → (I : Set ℓI)
            → (F : I → Set ℓF)
            → (next : I → I)
            → (i : I)
            → IStream I F next i
            → F i × IStream I F next (next i)
IStream-β I F next i s = hd s , tl s

-- Indexed coalgebras
-- 索引余代数
record ICoalgebra {ℓI ℓF ℓX : Level}
                  (I : Set ℓI)
                  (F : I → Set ℓF)
                  (next : I → I)
                  (X : I → Set ℓX)
                  : Set (ℓI ⊔ ℓF ⊔ ℓX) where
  field
    𝛂 : (i : I) → X i → F i × X (next i)
open ICoalgebra public

-- Indexed coalgebra homomorphisms
-- 索引余代数同态
record IHomo {ℓI ℓF ℓX : Level}
             (I : Set ℓI)
             (F : I → Set ℓF)
             (next : I → I)
             (X : I → Set ℓX)
             (C : ICoalgebra I F next X)
             (φ : (i : I) → X i → IStream I F next i)
             : Set (ℓI ⊔ ℓF ⊔ ℓX) where
  field
    comm : (i : I) (x : X i)
         → IStream-β I F next i (φ i x)
         ≡ (proj₁ (𝛂 C i x) , φ (next i) (proj₂ (𝛂 C i x)))
open IHomo public

-- Indexed stream anamorphism anaᵢ
-- 索引流展开函数anaᵢ
anaᵢ : ∀ {ℓI ℓF ℓX : Level}
       → (I : Set ℓI)
       → (F : I → Set ℓF)
       → (next : I → I)
       → (X : I → Set ℓX)
       → (C : ICoalgebra I F next X)
       → (i : I)
       → X i
       → IStream I F next i
anaᵢ I F next X C i x .hd = proj₁ (𝛂 C i x)
anaᵢ I F next X C i x .tl = anaᵢ I F next X C (next i) (proj₂ (𝛂 C i x))

-- anaᵢ is a homomorphism
-- anaᵢ是同态
anaᵢ-ihomo : ∀ {ℓI ℓF ℓX : Level}
             → (I : Set ℓI)
             → (F : I → Set ℓF)
             → (next : I → I)
             → (X : I → Set ℓX)
             → (C : ICoalgebra I F next X)
             → IHomo I F next X C (anaᵢ I F next X C)
anaᵢ-ihomo I F next X C .comm i x = refl

-- Uniqueness of indexed stream homomorphisms
-- 索引流同态唯一性
unique-ihom : ∀ {ℓI ℓF ℓX : Level}
              → (I : Set ℓI)
              → (F : I → Set ℓF)
              → (next : I → I)
              → (X : I → Set ℓX)
              → (C : ICoalgebra I F next X)
              → (φ : (i : I) → X i → IStream I F next i)
              → IHomo I F next X C φ
              → (i : I) (x : X i)
              → _≈ᵢ_ (φ i x) (anaᵢ I F next X C i x)
unique-ihom I F next X C φ h i x = aux i x
  where
    aux : (i : I) (x : X i) → _≈ᵢ_ (φ i x) (anaᵢ I F next X C i x)
    aux i x .hd≈ = cong proj₁ (comm h i x)
    aux i x .tl≈ with tl (φ i x) | cong proj₂ (comm h i x)
    ... | .(φ (next i) (proj₂ (𝛂 C i x))) | refl = aux (next i) (proj₂ (𝛂 C i x))
terminal-istream : ∀ {ℓI ℓF ℓX : Level}
                   → (I : Set ℓI)
                   → (F : I → Set ℓF)
                   → (next : I → I)
                   → (X : I → Set ℓX)
                   → (C : ICoalgebra I F next X)
                   → Σ ((i : I) → X i → IStream I F next i) λ h →
                     IHomo I F next X C h ×
                     (∀ φ → IHomo I F next X C φ → ∀ i x → _≈ᵢ_ (φ i x) (h i x))
terminal-istream I F next X C = anaᵢ I F next X C , anaᵢ-ihomo I F next X C , unique-ihom I F next X C

module _ {ℓ} {A : Set ℓ} (a : A) where
  private
    ≈-constStream-aux : ∀ (s : Stream A) → Always {ℓ = ℓ} {ℓ' = ℓ} (λ x → x ≡ a) s → s ≈ constStream a
    ≈-constStream-aux s s-always-a .head≈ = s-always-a .head
    ≈-constStream-aux s s-always-a .tail≈ = ≈-constStream-aux (s .tail) (s-always-a .tail)
  always-const-implies-≈-constStream :
    ∀ (s : Stream A) → Always {ℓ = ℓ} {ℓ' = ℓ} (λ x → x ≡ a) s → s ≈ constStream a
  always-const-implies-≈-constStream = ≈-constStream-aux

module Constructions {ℓ₁ ℓ₂} {O : Set ℓ₁} {C : Set ℓ₂} (o : O) (c : C) where
  const-coalg : ⊤ {0ℓ} → StreamF (O × C) (⊤ {0ℓ})
  const-coalg _ = ((o , c) , tt {0ℓ})
  const-stream-via-ana : Stream (O × C)
  const-stream-via-ana = ana const-coalg (tt {0ℓ})
  -- Streams constructed via coalgebras also fully satisfy constancy
  -- 余代数构造的流也完全满足恒常性
  private
    const-stream-always-element-constant : Always (λ oc → oc ≡ (o , c)) const-stream-via-ana
    const-stream-always-element-constant .head = refl
    const-stream-always-element-constant .tail = const-stream-always-element-constant
  const-stream-always-constant : Always (λ oc → proj₂ oc ≡ c) const-stream-via-ana
  const-stream-always-constant .head = refl
  const-stream-always-constant .tail = const-stream-always-constant
  -- Process identity: Streams produced by the two construction modes are equivalent
  -- 过程同一性：两种构造模式产生的流是等价的
  const-stream-≈ : const-stream-via-ana ≈ constStream (o , c)
  const-stream-≈ = always-const-implies-≈-constStream (o , c)
    const-stream-via-ana
    const-stream-always-element-constant
open Constructions public
private
  module AnaFusion {ℓ₁ ℓ₂} {A : Set ℓ₁} where
    ana-fusion : ∀ {X Y : Set ℓ₂} (α : X → StreamF A X) (β : Y → StreamF A Y) (f : X → Y) →
                 (∀ x → imap f (α x) ≡ β (f x)) →
                 ∀ x → ana α x ≈ ana β (f x)
    ana-fusion α β f comm x ._≈_.head≈ = cong proj₁ (comm x)
    ana-fusion α β f comm x ._≈_.tail≈ rewrite sym (cong proj₂ (comm x))
      = ana-fusion α β f comm (proj₂ (α x))
open AnaFusion public using (ana-fusion)

-- Core ontological theorem: Indestructibility (two equivalent proofs)
-- 核心存在论定理：不可消减性（两种等价证明）
record Indestructibility-Theorem : Setω where
  field
    law-noExNihilo : ∀ {ℓ} → ¬ (⊥ {ℓ})
    law-noAnnihilation : ∀ {ℓ} {A : Set ℓ} → Σ A (λ _ → ⊤ {ℓ}) → ¬ (A → ⊥ {ℓ})
    eternal-existence : ∀ {ℓ₁ ℓ₂} (O : Set ℓ₁) (C : Set ℓ₂)
                       → Σ O (λ _ → ⊤ {ℓ₁}) → Σ C (λ _ → ⊤ {ℓ₂})
                       → Σ (Stream (O × C)) λ stream
                       → Always (λ oc → proj₂ oc ≡ proj₂ (stream .head)) stream
mkIndestructibility :
  (∀ {ℓ₁ ℓ₂} {O : Set ℓ₁} {C : Set ℓ₂} (o : O) (c : C)
   → Σ (Stream (O × C)) (λ s → Always (λ oc → proj₂ oc ≡ proj₂ (s .head)) s))
  → Indestructibility-Theorem
mkIndestructibility buildStream = record
  { law-noExNihilo = noExNihilo
  ; law-noAnnihilation = noAnnihilation
  ; eternal-existence = λ O C (o , _) (c , _) → buildStream o c
  }
indestructibility-proof : Indestructibility-Theorem
indestructibility-proof = mkIndestructibility λ o c →
  constStream (o , c) , constStream-always-gen (o , c) refl
indestructibility-proof-via-coalgebra : Indestructibility-Theorem
indestructibility-proof-via-coalgebra = mkIndestructibility λ o c →
  const-stream-via-ana o c , const-stream-always-constant o c

-- Streams generated by the two proofs are equivalent: Unification of epistemic and ontological perspectives
-- 两个证明生成的流是等价的：认识论视角与本体论视角的统一
indestructibility-proofs-equivalent : ∀ {ℓ₁ ℓ₂} {O : Set ℓ₁} {C : Set ℓ₂} (o : O) (c : C) →
  constStream (o , c) ≈ const-stream-via-ana o c
indestructibility-proofs-equivalent o c = ≈-sym (const-stream-≈ o c)

-- Uniqueness theorem: Streams with both components constant are uniquely bisimilar to the constant construction
-- 唯一性定理：双分量皆恒常的流唯一互模拟等价于常量构造
BothComponentsConstant : ∀ {ℓ₁ ℓ₂} {O : Set ℓ₁} {C : Set ℓ₂} → O → C → Stream (O × C) → Set (ℓ₁ ⊔ ℓ₂)
BothComponentsConstant o c s = Always (λ oc → proj₁ oc ≡ o) s × Always (λ oc → proj₂ oc ≡ c) s
both-const-implies-element-const : ∀ {ℓ₁ ℓ₂} {O : Set ℓ₁} {C : Set ℓ₂} (o : O) (c : C) (s : Stream (O × C))
                                 → BothComponentsConstant o c s → Always (λ x → x ≡ (o , c)) s
both-const-implies-element-const o c s (p₁ , p₂) .Always.head = cong₂ _,_ (p₁ .Always.head) (p₂ .Always.head)
both-const-implies-element-const o c s (p₁ , p₂) .Always.tail = both-const-implies-element-const o c (Stream.tail s) (p₁ .Always.tail , p₂ .Always.tail)

both-const-implies-≈-constStream : ∀ {ℓ₁ ℓ₂} {O : Set ℓ₁} {C : Set ℓ₂} (o : O) (c : C) (s : Stream (O × C))
                                 → BothComponentsConstant o c s → s ≈ constStream (o , c)
both-const-implies-≈-constStream o c s both-const =
  let element-const : Always (λ x → x ≡ (o , c)) s
      element-const = both-const-implies-element-const o c s both-const
  in always-const-implies-≈-constStream (o , c) s element-const
record Indestructibility-Uniqueness : Setω where
  field
    law-noExNihilo : ∀ {ℓ} → ¬ (⊥ {ℓ})
    law-noAnnihilation : ∀ {ℓ} {A : Set ℓ} → Σ A (λ _ → ⊤ {ℓ}) → ¬ (A → ⊥ {ℓ})
    unique-eternity : ∀ {ℓ₁ ℓ₂} (O : Set ℓ₁) (C : Set ℓ₂)
                     → Σ O (λ _ → ⊤ {ℓ₁}) → Σ C (λ _ → ⊤ {ℓ₂})
                     → Σ O λ o
                     → Σ C λ c
                     → let stream = constStream (o , c)
                       in BothComponentsConstant o c stream
                       × (∀ s → BothComponentsConstant o c s → s ≈ stream)
indestructibility-uniqueness-proof : Indestructibility-Uniqueness
indestructibility-uniqueness-proof = record
  { law-noExNihilo = noExNihilo
  ; law-noAnnihilation = noAnnihilation
  ; unique-eternity = λ O C (o , _) (c , _) →
      let
        stream = constStream (o , c)
        component-const : ∀ {ℓ} {A : Set ℓ} (proj : (O × C) → A) (val : A) (eq : proj (o , c) ≡ val)
                         → Always (λ x → proj x ≡ val) stream
        component-const _ _ eq = constStream-always-gen (o , c) eq
        both-const = (component-const proj₁ o refl , component-const proj₂ c refl)
        uniqueness s bc = both-const-implies-≈-constStream o c s bc
      in (o , c , both-const , uniqueness)
  }

-- Invariant projection: Extracting core values of fixed type C from states F i at each index i
-- 不变投影：从每个索引i的状态F i中提取固定类型C的核心值
InvariantProjection : ∀ {ℓI ℓF ℓC} 
                    → (I : Set ℓI) 
                    → (F : I → Set ℓF) 
                    → (C : Set ℓC) 
                    → Set (ℓI ⊔ ℓF ⊔ ℓC)
InvariantProjection I F C = (i : I) → F i → C

-- Core-preserving indexed coalgebras: Core values output at each step are always equal to the initially given c
-- 保持核心的索引余代数：每一步输出的核心值恒等于初始给定的c
record CorePreservingCoalgebra 
         {ℓI ℓF ℓX ℓC} 
         {I : Set ℓI} 
         {F : I → Set ℓF} 
         {X : I → Set ℓX} 
         {C : Set ℓC}
         (next : I → I)
         (π : InvariantProjection I F C)
         (c : C)
         : Set (ℓI ⊔ ℓF ⊔ ℓX ⊔ ℓC) where
  field
    coalg : ICoalgebra I F next X
    core-preservation : ∀ {i : I} (x : X i) 
                      → π i (proj₁ (ICoalgebra.𝛂 coalg i x)) ≡ c
open CorePreservingCoalgebra public

-- Generalized constancy predicate: Core values at all positions of indexed stream s under projection π are equal to c
-- 广义恒常性谓词：索引流s在投影π下所有位置的核心值都等于c
record IAlwaysVia 
         {ℓI ℓF ℓC} 
         {I : Set ℓI} 
         {F : I → Set ℓF} 
         {C : Set ℓC}
         (next : I → I)
         (π : InvariantProjection I F C)
         (c : C)
         {i : I}
         (s : IStream I F next i)
         : Set (ℓI ⊔ ℓF ⊔ ℓC) where
  coinductive
  field
    head-const : π i (IStream.hd s) ≡ c
    tail-const : IAlwaysVia next π c (IStream.tl s)
open IAlwaysVia public

-- Generalized indestructible existence theorem: Given a core-preserving coalgebra and initial state, an eternal core stream necessarily exists
-- 广义不可消减存在性定理：给定保持核心的余代数和初始状态，必然存在永恒核心流
eternal-core-existence : ∀ {ℓI ℓF ℓX ℓC} 
                       → {I : Set ℓI} 
                       → {F : I → Set ℓF} 
                       → {X : I → Set ℓX} 
                       → {C : Set ℓC}
                       → (next : I → I)
                       → (π : InvariantProjection I F C)
                       → (c : C)
                       → (cp-coalg : CorePreservingCoalgebra next π c)
                       → {i₀ : I}
                       → (x₀ : X i₀)
                       → Σ (IStream I F next i₀) 
                           (λ s → IAlwaysVia next π c s)
eternal-core-existence {I = I} {F = F} {X = X} next π c cp-coalg {i₀} x₀ = (s , s-always-c)
  where
    local-coalg = cp-coalg .coalg
    -- Generate indexed stream by unfolding the coalgebra with anaᵢ
    -- 用anaᵢ展开余代数生成索引流
    s : IStream I F next i₀
    s = anaᵢ I F next X local-coalg i₀ x₀
    -- Helper function directly proving that all streams generated by anaᵢ satisfy constancy
    -- 辅助函数直接证明所有anaᵢ生成的流都满足恒常性
    aux : ∀ {i : I} (x : X i) → IAlwaysVia next π c (anaᵢ I F next X local-coalg i x)
    aux {i} x .head-const = cp-coalg .core-preservation x
    aux {i} x .tail-const = aux (proj₂ (ICoalgebra.𝛂 local-coalg i x))
    -- Directly apply the helper function to prove constancy of the current stream
    -- 直接应用辅助函数证明当前流的恒常性
    s-always-c : IAlwaysVia next π c s
    s-always-c = aux x₀

-- Theorem 1: Core value uniqueness (holds unconditionally)
-- 定理1：核心值唯一性（无条件成立）
core-value-uniqueness : ∀ {ℓI ℓF ℓC} 
                      → {I : Set ℓI} 
                      → {F : I → Set ℓF} 
                      → {C : Set ℓC}
                      → {next : I → I}
                      → {i : I}
                      → (s₁ s₂ : IStream I F next i)
                      → (π : InvariantProjection I F C)
                      → (c : C)
                      → IAlwaysVia next π c s₁
                      → IAlwaysVia next π c s₂
                      → π i (IStream.hd s₁) ≡ π i (IStream.hd s₂)
core-value-uniqueness s₁ s₂ π c always₁ always₂ = 
  trans (always₁ .head-const) (sym (always₂ .head-const))

-- Theorem 2: State uniqueness (requires the additional condition that π is injective)
-- 定理2：状态唯一性（需附加π是单射的条件）
state-uniqueness : ∀ {ℓI ℓF ℓC} 
                 → {I : Set ℓI} 
                 → {F : I → Set ℓF} 
                 → {C : Set ℓC}
                 → {next : I → I}
                 → (π : InvariantProjection I F C)
                 → (c : C)
                 → (π-injective : ∀ {i} {x y : F i} → π i x ≡ π i y → x ≡ y)
                 → {i : I}
                 → (s₁ s₂ : IStream I F next i)
                 → IAlwaysVia {ℓI = ℓI} {ℓF = ℓF} {ℓC = ℓC} next π c {i = i} s₁
                 → IAlwaysVia {ℓI = ℓI} {ℓF = ℓF} {ℓC = ℓC} next π c {i = i} s₂
                 → s₁ ≈ᵢ s₂
state-uniqueness π c π-inj s₁ s₂ always₁ always₂ .hd≈ = 
  π-inj (trans (always₁ .head-const) (sym (always₂ .head-const)))
state-uniqueness π c π-inj s₁ s₂ always₁ always₂ .tl≈ = 
  state-uniqueness π c π-inj 
    (tl s₁) (tl s₂) 
    (always₁ .tail-const) (always₂ .tail-const)

-- Simple stream indestructibility theorem as a strict corollary of the generalized theorem
-- 简单流不可消减定理是广义定理的严格推论
forget-index-simple : ∀ {ℓO ℓC} {O : Set ℓO} {C : Set ℓC}
                    → {next : ⊤ → ⊤}
                    → IStream {ℓI = 0ℓ} {ℓF = ℓO ⊔ ℓC} ⊤ (λ _ → O × C) next tt
                    → Stream (O × C)
forget-index-simple s .Stream.head = IStream.hd s
forget-index-simple s .Stream.tail = forget-index-simple (IStream.tl s)
forget-index-preserves-always-simple : ∀ {ℓO ℓC} {O : Set ℓO} {C : Set ℓC}
                                     → {next : ⊤ → ⊤}
                                     → {c : C}
                                     → {s : IStream {ℓI = 0ℓ} {ℓF = ℓO ⊔ ℓC} ⊤ (λ _ → O × C) next tt}
                                     → IAlwaysVia {ℓI = 0ℓ} {ℓF = ℓO ⊔ ℓC} {ℓC = ℓC} next (λ _ → proj₂) c s
                                     → Always {ℓ = ℓO ⊔ ℓC} {ℓ' = ℓC} (λ oc → proj₂ oc ≡ c) (forget-index-simple s)
forget-index-preserves-always-simple always .Always.head = always .head-const
forget-index-preserves-always-simple always .Always.tail = forget-index-preserves-always-simple (always .tail-const)
simple-eternity-as-corollary : ∀ {ℓO ℓC} 
                             → (O : Set ℓO) 
                             → (C : Set ℓC)
                             → Σ O (λ _ → ⊤ {ℓO}) 
                             → Σ C (λ _ → ⊤ {ℓC})
                             → Σ (Stream (O × C)) 
                                 (λ s → Always {ℓ = ℓO ⊔ ℓC} {ℓ' = ℓC} (λ oc → proj₂ oc ≡ proj₂ (Stream.head s)) s)
simple-eternity-as-corollary {ℓO = ℓO} {ℓC = ℓC} O C (o , _) (c , _) = 
  (forget-index-simple {ℓO = ℓO} {ℓC = ℓC} indexed-s , 
   forget-index-preserves-always-simple {ℓO = ℓO} {ℓC = ℓC} {c = c} indexed-always)
  where
    next : ⊤ → ⊤
    next _ = tt
    X : ⊤ → Set 0ℓ
    X _ = ⊤ {0ℓ}
    local-coalg : ICoalgebra {ℓI = 0ℓ} {ℓF = ℓO ⊔ ℓC} {ℓX = 0ℓ} ⊤ (λ _ → O × C) next X
    local-coalg .ICoalgebra.𝛂 _ _ = ((o , c) , tt {0ℓ})
    cp-coalg : CorePreservingCoalgebra {ℓI = 0ℓ} {ℓF = ℓO ⊔ ℓC} {ℓX = 0ℓ} {ℓC = ℓC} next (λ _ → proj₂) c
    cp-coalg .coalg = local-coalg
    cp-coalg .core-preservation _ = refl
    indexed-result = eternal-core-existence 
                       {ℓI = 0ℓ} {ℓF = ℓO ⊔ ℓC} {ℓX = 0ℓ} {ℓC = ℓC} 
                       next (λ _ → proj₂) c cp-coalg {i₀ = tt} (tt {0ℓ})
    indexed-s = indexed-result .proj₁
    indexed-always = indexed-result .proj₂

-- Helper function: Combining two invariant projections into a product projection
-- 辅助函数：将两个不变投影组合成乘积投影
pair-proj : ∀ {ℓI ℓF ℓC ℓD}
          → {I : Set ℓI}
          → {F : I → Set ℓF}
          → {C : Set ℓC}
          → {D : Set ℓD}
          → (π₁ : InvariantProjection I F C)
          → (π₂ : InvariantProjection I F D)
          → InvariantProjection I F (C × D)
pair-proj π₁ π₂ = λ i state → (π₁ i state , π₂ i state)

-- Composition of core-preserving coalgebras: Two invariant cores can be combined into a product core
-- Prerequisite: The two core-preserving coalgebras must share the exact same underlying ICoalgebra
-- 核心保持余代数的组合：两个不变核心可以组合成一个乘积核心
-- 前提：两个核心保持余代数必须共享完全相同的底层ICoalgebra
compose-core-preserving : ∀ {ℓI ℓF ℓX ℓC ℓD}
                        → {C : Set ℓC}
                        → {D : Set ℓD}
                        → {I : Set ℓI}
                        → {F : I → Set ℓF}
                        → {X : I → Set ℓX}
                        → {next : I → I}
                        → {π₁ : InvariantProjection I F C}
                        → {π₂ : InvariantProjection I F D}
                        → {c : C}
                        → {d : D}
                        → (cp1 : CorePreservingCoalgebra next π₁ c)
                        → (cp2 : CorePreservingCoalgebra next π₂ d)
                        → (cp1 .coalg ≡ cp2 .coalg)
                        → CorePreservingCoalgebra next (pair-proj π₁ π₂) (c , d)
compose-core-preserving 
  {C = C} {D = D} {I = I} {F = F} {X = X} {next = next} {π₁ = π₁} {π₂ = π₂} {c = c} {d = d} 
  cp1 cp2 refl = record
  { coalg = cp1 .coalg
  ; core-preservation = proof
  }
  where
    proof : ∀ {i : I} (state : X i) → pair-proj π₁ π₂ i (proj₁ (ICoalgebra.𝛂 (cp1 .coalg) i state)) ≡ (c , d)
    proof {i} state = 
      let
        p1 = cp1 .core-preservation state
        p2 = cp2 .core-preservation state
      in
      cong₂ (λ a b → (a , b)) p1 p2

-- History path type (ontological record of the generation process)
-- 历史路径类型（生成过程的本体论记录）
record History {ℓ₁ ℓ₂} {A : Set ℓ₁} {X : Set ℓ₂} (α : X → StreamF A X) (init : X) : Set (ℓ₁ ⊔ ℓ₂) where
  coinductive
  field
    current-state : X
    next-state : History α (proj₂ (α current-state))
open History public
stream-has-unique-history : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {X : Set ℓ₂} (α : X → StreamF A X) (init : X)
  → ∃ λ (h : History α init) → ana α init ≈ ana α (h .current-state)
stream-has-unique-history α init = h , ≈-refl
  where
    h : History α init
    h .current-state = init
    h .next-state = proj₁ (stream-has-unique-history α (proj₂ (α init)))
record HistoricalStream {ℓ₁ ℓ₂} {A : Set ℓ₁} {X : Set ℓ₂} (α : X → StreamF A X) (init : X) : Set (ℓ₁ ⊔ ℓ₂) where
  field
    history : History α init
    stream : Stream A
    stream-correct : stream ≈ ana α init
open HistoricalStream public

-- Ontological process identity relation (continuous causal connection + historical identity)
-- 本体论过程同一关系（连续因果关联 + 历史同一性）
record _≡ₚ_ {ℓ₁ ℓ₂} {A : Set ℓ₁} {X : Set ℓ₂} {α : X → StreamF A X} {i : X}
  (hs1 hs2 : HistoricalStream α i) : Set (ℓ₁ ⊔ ℓ₂) where
  field
    step : ℕ
    stream-continuous : stream-tail-n (hs1 .stream) step ≈ hs2 .stream
    same-history : hs1 .history ≡ hs2 .history
infix 4 _≡ₚ_
≡ₚ-refl : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {X : Set ℓ₂} {α : X → StreamF A X} {i : X}
  {hs : HistoricalStream α i} → hs ≡ₚ hs
≡ₚ-refl = record
  { step = 0
  ; stream-continuous = ≈-refl
  ; same-history = refl
  }
≡ₚ-trans : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {X : Set ℓ₂} {α : X → StreamF A X} {i : X}
  {hs1 hs2 hs3 : HistoricalStream α i}
  → hs1 ≡ₚ hs2
  → hs2 ≡ₚ hs3
  → hs1 ≡ₚ hs3
≡ₚ-trans {hs1 = hs1} {hs2} {hs3} p12 p23 = record
  { step = p12 ._≡ₚ_.step + p23 ._≡ₚ_.step
  ; stream-continuous = ≈-trans
      (≈-trans
        (stream-tail-n-add (p12 ._≡ₚ_.step) (p23 ._≡ₚ_.step) (hs1 .stream))
        (stream-tail-n-cong (p23 ._≡ₚ_.step) (p12 ._≡ₚ_.stream-continuous)))
      (p23 ._≡ₚ_.stream-continuous)
  ; same-history = trans (p12 ._≡ₚ_.same-history) (p23 ._≡ₚ_.same-history)
  }
structure-same-history-different-implies-not-same-process :
  ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {X : Set ℓ₂} {α : X → StreamF A X} {i : X}
  {hs1 hs2 : HistoricalStream α i}
  → hs1 .history ≢ hs2 .history
  → hs1 .stream ≈ hs2 .stream
  → ¬ (hs1 ≡ₚ hs2)
structure-same-history-different-implies-not-same-process h-neq _ p =
  h-neq (p ._≡ₚ_.same-history)

-- General framework
-- 通用框架
module OntologicalFramework
  {ℓ₁ ℓ₂} {A : Set ℓ₁} {X : Set ℓ₂}
  (α : X → StreamF A X)
  (i : X)
  (h1 h2 : History α i)
  (h1≠h2 : h1 ≢ h2)
  (h1-correct : ana α (h1 .current-state) ≈ ana α i)
  (h2-correct : ana α (h2 .current-state) ≈ ana α i)
  where
  private
    streams-equal : ana α (h1 .current-state) ≈ ana α (h2 .current-state)
    streams-equal = ≈-trans h1-correct (≈-sym h2-correct)
  hs1 : HistoricalStream α i
  hs1 = record
    { history = h1
    ; stream = ana α (h1 .current-state)
    ; stream-correct = h1-correct
    }
  hs2 : HistoricalStream α i
  hs2 = record
    { history = h2
    ; stream = ana α (h2 .current-state)
    ; stream-correct = h2-correct
    }
  ≈-does-not-imply-≡ₚ :
    ∃ λ (hs1 : HistoricalStream α i) → ∃ λ (hs2 : HistoricalStream α i)
    → (hs1 .history ≢ hs2 .history) × (hs1 .stream ≈ hs2 .stream) × ¬ (hs1 ≡ₚ hs2)
  ≈-does-not-imply-≡ₚ = hs1 , (hs2 , (h1≠h2 , streams-equal , ¬hs1≡ₚhs2))
    where
      ¬hs1≡ₚhs2 : ¬ (hs1 ≡ₚ hs2)
      ¬hs1≡ₚhs2 = structure-same-history-different-implies-not-same-process h1≠h2 streams-equal

-- Concrete instance: Two-state constant-true coalgebra; identical structures can arise from different generation processes
-- 具体实例：双状态恒真余代数，相同结构可以来自不同的生成过程
module TwoStateConstantTrueInstance where
  X : Set
  X = Bool
  α : X → StreamF Bool X
  α _ = (true , true)
  h1 : History α true
  h1 .current-state = true
  h1 .next-state = h1
  h2 : History α true
  h2 .current-state = false
  h2 .next-state = h2
  h1≠h2 : h1 ≢ h2
  h1≠h2 eq = true≢false (cong current-state eq)
  ana-false≈ana-true : ana α false ≈ ana α true
  ana-false≈ana-true = ana-fusion α α (λ _ → true) (λ _ → refl) false
  open OntologicalFramework
    α
    true
    h1
    h2
    h1≠h2
    ≈-refl
    ana-false≈ana-true
    public

-- Any stream is a trivial instance of Cosmos
-- 任意流均为 Cosmos 的平凡实例
private
  record ⊤' (ℓ : Level) : Set (lsuc ℓ) where
    constructor tt'
  record ℕ' (ℓ : Level) : Set (lsuc ℓ) where
    constructor [_]
    field lower : ℕ
  open ⊤'
  open ℕ'
streamToCosmos : {ℓ₁ ℓ₂ : Level} {O : Set ℓ₁} {C : Set ℓ₂}
               → Stream (O × C) → O → C → Cosmos (ℓ₁ ⊔ ℓ₂)
streamToCosmos {ℓ₁} {ℓ₂} {O} {C} st o₀ c₀ .Cosmos.Obj = ⊤' (ℓ₁ ⊔ ℓ₂)
streamToCosmos {ℓ₁} {ℓ₂} {O} {C} st o₀ c₀ .Cosmos.Shape _ = ℕ' (ℓ₁ ⊔ ℓ₂)
streamToCosmos {ℓ₁} {ℓ₂} {O} {C} st o₀ c₀ .Cosmos.Pos _ = ⊤' (ℓ₁ ⊔ ℓ₂)
streamToCosmos {ℓ₁} {ℓ₂} {O} {C} st o₀ c₀ .Cosmos.Hom _ _ = ⊤' (ℓ₁ ⊔ ℓ₂)
streamToCosmos {ℓ₁} {ℓ₂} {O} {C} st o₀ c₀ .Cosmos.idHom = tt'
streamToCosmos {ℓ₁} {ℓ₂} {O} {C} st o₀ c₀ .Cosmos.comp _ _ = tt'
streamToCosmos {ℓ₁} {ℓ₂} {O} {C} st o₀ c₀ .Cosmos.comp-assoc _ _ _ = refl
streamToCosmos {ℓ₁} {ℓ₂} {O} {C} st o₀ c₀ .Cosmos.id-comp-l _ = refl
streamToCosmos {ℓ₁} {ℓ₂} {O} {C} st o₀ c₀ .Cosmos.id-comp-r _ = refl
streamToCosmos {ℓ₁} {ℓ₂} {O} {C} st o₀ c₀ .Cosmos.actS _ n = n
streamToCosmos {ℓ₁} {ℓ₂} {O} {C} st o₀ c₀ .Cosmos.actP f s p = tt'
streamToCosmos {ℓ₁} {ℓ₂} {O} {C} st o₀ c₀ .Cosmos.actS-id n = refl
streamToCosmos {ℓ₁} {ℓ₂} {O} {C} st o₀ c₀ .Cosmos.actS-comp f g n = refl
streamToCosmos {ℓ₁} {ℓ₂} {O} {C} st o₀ c₀ .Cosmos.actP-id n p = refl
streamToCosmos {ℓ₁} {ℓ₂} {O} {C} st o₀ c₀ .Cosmos.actP-comp f g n p = refl
streamToCosmos {ℓ₁} {ℓ₂} {O} {C} st o₀ c₀ .Cosmos.unfold-obj _ = tt'
streamToCosmos {ℓ₁} {ℓ₂} {O} {C} st o₀ c₀ .Cosmos.unfold-hom f s = tt'
streamToCosmos {ℓ₁} {ℓ₂} {O} {C} st o₀ c₀ .Cosmos.unfold-hom-id s = refl
streamToCosmos {ℓ₁} {ℓ₂} {O} {C} st o₀ c₀ .Cosmos.unfold-hom-comp f g s = refl
streamToCosmos {ℓ₁} {ℓ₂} {O} {C} st o₀ c₀ .Cosmos.pos-to-shape [ n ] p = [ 1 ]
streamToCosmos {ℓ₁} {ℓ₂} {O} {C} st o₀ c₀ .Cosmos.pos-actS-compat f n p = refl
streamToCosmos {ℓ₁} {ℓ₂} {O} {C} st o₀ c₀ .Cosmos.unfold [ n ] = 
  let stₙ = stream-tail-n st n
      oₙ  = proj₁ (Stream.head stₙ)
      cₙ  = proj₂ (Stream.head stₙ)
  in streamToCosmos stₙ oₙ cₙ
