------------------------------------------------------------------------
-- Fundamental structure and evolutionary irreversibility of dynamic beings
--
-- Fundamental structure, composition, and irreducible accidental
-- reconfiguration of dynamic beings; processes, tensor product
-- categorical structure, coherent patterns, evolution, and
-- irreversibility theorems.
--
-- 动态存在者的基本结构与演化不可逆性
--
-- 动态存在者基本结构、复合方式及本质不可消减的偶性形态重构与演化不
-- 可逆性；过程及其张量积范畴结构、相干模式、演化与不可逆定理。
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --exact-split --guardedness --double-check #-}

module Wellspring.Beings where

open import Wellspring.Indestructibility public

-- Process: Fundamental structure of dynamic beings (O: Accident, C: Essence)
-- 过程：动态存在者的基本结构（O：偶性，C：本质）
record Process {ℓ₁ ℓ₂} (O : Set ℓ₁) (C : Set ℓ₂) : Set (ℓ₁ ⊔ ℓ₂) where
  coinductive
  constructor mkProc
  field
    o               : O
    c               : C
    stream          : Stream (O × C)
    essence-const   : Always (λ x → proj₂ x ≡ c) stream
    init-consistent : proj₁ (Stream.head stream) ≡ o
open Process public
processToCosmos : {ℓ₁ ℓ₂ : Level} {O : Set ℓ₁} {C : Set ℓ₂}
                   → Process O C → Cosmos (ℓ₁ ⊔ ℓ₂)
processToCosmos p = streamToCosmos (stream p) (o p) (c p)
core : ∀ {ℓ₁ ℓ₂} {O : Set ℓ₁} {C : Set ℓ₂} → Process O C → C
core = c

-- Process equivalence: Stream bisimulation
-- 过程等价：流互模拟
_≈ₚ_ : ∀ {ℓ₁ ℓ₂} {O : Set ℓ₁} {C : Set ℓ₂} → Process O C → Process O C → Set (ℓ₁ ⊔ ℓ₂)
_≈ₚ_ p q = stream p ≈ stream q
infix 4 _≈ₚ_
≈ₚ-refl  : ∀ {ℓ₁ ℓ₂} {O : Set ℓ₁} {C : Set ℓ₂} {p : Process O C} → p ≈ₚ p
≈ₚ-refl = ≈-refl
≈ₚ-sym   : ∀ {ℓ₁ ℓ₂} {O : Set ℓ₁} {C : Set ℓ₂} {p q : Process O C} → p ≈ₚ q → q ≈ₚ p
≈ₚ-sym = ≈-sym
≈ₚ-trans : ∀ {ℓ₁ ℓ₂} {O : Set ℓ₁} {C : Set ℓ₂} {p q r : Process O C} → p ≈ₚ q → q ≈ₚ r → p ≈ₚ r
≈ₚ-trans = ≈-trans

-- Standard process construction (Epistemological perspective: Direct coinduction)
-- 标准过程构造（认识论视角：直接余归纳）
mkStandardProcess : ∀ {ℓ₁ ℓ₂} (O : Set ℓ₁) (C : Set ℓ₂) → O → C → Process O C
mkStandardProcess O C o c = mkProc o c standard-stream standard-essence-const refl
  where
    standard-stream : Stream (O × C)
    standard-stream = constStream (o , c)
    standard-essence-const : Always (λ x → proj₂ x ≡ c) standard-stream
    standard-essence-const = constStream-always-gen (o , c) refl

-- Standard process construction (Ontological perspective: Coalgebraic)
-- 标准过程构造（本体论视角：余代数式）
mkProcessViaAna : ∀ {ℓ₁ ℓ₂} (O : Set ℓ₁) (C : Set ℓ₂) → O → C → Process O C
mkProcessViaAna O C o c = mkProc o c ana-stream ana-essence-const refl
  where
    ana-stream : Stream (O × C)
    ana-stream = ana (const-coalg o c) tt
    ana-essence-const : Always (λ x → proj₂ x ≡ c) ana-stream
    ana-essence-const = const-stream-always-constant o c

-- Unification of epistemology and ontology
-- 认识论与本体论的统一
standard-processes-equivalent : ∀ {ℓ₁ ℓ₂} {O : Set ℓ₁} {C : Set ℓ₂} (o : O) (c : C) →
  mkStandardProcess O C o c ≈ₚ mkProcessViaAna O C o c
standard-processes-equivalent o c = ≈-sym (const-stream-≈ o c)

-- Finite observation and essence conservation
-- 有限观察与本质守恒
always-implies-all-n : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {P : A → Set ℓ₂} {s : Stream A} →
                       Always P s → ∀ (n : ℕ) → P (Stream.head (stream-tail-n s n))
always-implies-all-n alws zero    = Always.head alws
always-implies-all-n alws (suc n) = always-implies-all-n (Always.tail alws) n
observe : ∀ {ℓ₁ ℓ₂} {O : Set ℓ₁} {C : Set ℓ₂} → Process O C → ℕ → O
observe p n = proj₁ (Stream.head (stream-tail-n (stream p) n))
next : ∀ {ℓ₁ ℓ₂} {O : Set ℓ₁} {C : Set ℓ₂} → Process O C → Process O C
next p = mkProc o' (c p) stream' essence-const' init-consistent'
  where
    stream' = Stream.tail (stream p)
    o' = proj₁ (Stream.head stream')
    essence-const' = Always.tail (essence-const p)
    init-consistent' = refl
c-conservation : ∀ {ℓ₁ ℓ₂} {O : Set ℓ₁} {C : Set ℓ₂} (p : Process O C) → core (next p) ≡ core p
c-conservation p = refl
global-c-constancy : ∀ {ℓ₁ ℓ₂} {O : Set ℓ₁} {C : Set ℓ₂} (p : Process O C) (n : ℕ) →
                     proj₂ (Stream.head (stream-tail-n (stream p) n)) ≡ core p
global-c-constancy p n = always-implies-all-n (essence-const p) n
next-preserves-constancy : ∀ {ℓ₁ ℓ₂} {O : Set ℓ₁} {C : Set ℓ₂} (p : Process O C) → 
                            Always (λ x → proj₂ x ≡ core (next p)) (stream (next p))
next-preserves-constancy p = Always.tail (essence-const p)
core-preserves-≈ₚ : ∀ {ℓ₁ ℓ₂} {O : Set ℓ₁} {C : Set ℓ₂} {p q : Process O C} → p ≈ₚ q → core p ≡ core q
core-preserves-≈ₚ {p = p} {q = q} p≈q =
  trans (sym (global-c-constancy p 0))
        (trans (cong proj₂ (_≈_.head≈ p≈q))
               (global-c-constancy q 0))
observe-preserves-≈ₚ : ∀ {ℓ₁ ℓ₂} {O : Set ℓ₁} {C : Set ℓ₂} (p q : Process O C) (n : ℕ) →
                        p ≈ₚ q → observe p n ≡ observe q n
observe-preserves-≈ₚ p q n p≈q = aux-observe (stream p) (stream q) p≈q n
  where
    aux-observe : ∀ {ℓ₁ ℓ₂} {O : Set ℓ₁} {C : Set ℓ₂} (s1 s2 : Stream (O × C)) (e : s1 ≈ s2) (n : ℕ) →
                  proj₁ (Stream.head (stream-tail-n s1 n)) ≡ proj₁ (Stream.head (stream-tail-n s2 n))
    aux-observe s1 s2 e zero    = cong proj₁ (_≈_.head≈ e)
    aux-observe s1 s2 e (suc n) = aux-observe (Stream.tail s1) (Stream.tail s2) (_≈_.tail≈ e) n
next-preserves-≈ₚ : ∀ {ℓ₁ ℓ₂} {O : Set ℓ₁} {C : Set ℓ₂} {p q : Process O C} → p ≈ₚ q → next p ≈ₚ next q
next-preserves-≈ₚ p≈q = _≈_.tail≈ p≈q

-- Lemmas for the next operation
-- next 操作的引理
stream-tail-n-tail : ∀ {ℓ} {A : Set ℓ} (s : Stream A) (n : ℕ) →
                     Stream.tail (stream-tail-n s n) ≡ stream-tail-n (Stream.tail s) n
stream-tail-n-tail s zero = refl
stream-tail-n-tail s (suc n) = stream-tail-n-tail (Stream.tail s) n
next-iter : ∀ {ℓ₁ ℓ₂} {O : Set ℓ₁} {C : Set ℓ₂} (p : Process O C) (n : ℕ) →
            stream (iter n next p) ≡ stream-tail-n (stream p) n
next-iter p zero = refl
next-iter p (suc n) = 
  trans (cong Stream.tail (next-iter p n)) (stream-tail-n-tail (stream p) n)
observe-iter : ∀ {ℓ₁ ℓ₂} {O : Set ℓ₁} {C : Set ℓ₂} (p : Process O C) (n : ℕ) →
               observe p n ≡ observe (iter n next p) 0
observe-iter p n = cong (proj₁ ∘ Stream.head) (sym (next-iter p n))

-- Morphological reconfiguration: Accidents are mutable, essence is invariant
-- 形态重构：偶性可变，本质不变
AccidentalReconfiguration : ∀ {ℓ₁ ℓ₂} {O : Set ℓ₁} {C : Set ℓ₂} → Process O C → Set (ℓ₁ ⊔ ℓ₂)
AccidentalReconfiguration p =
  (∀ (n : ℕ) → proj₂ (Stream.head (stream-tail-n (stream p) n)) ≡ core p)
  × (Σ ℕ λ (n : ℕ) → observe p n ≢ observe p (suc n))
reconfiguration-theorem :
  ∀ {ℓ₁ ℓ₂} {O : Set ℓ₁} {C : Set ℓ₂} (p : Process O C)
  → (Σ ℕ λ (n : ℕ) → observe p n ≢ observe p (suc n))
  → AccidentalReconfiguration p
reconfiguration-theorem p morph-change =
  (global-c-constancy p , morph-change)

-- Alternating process example
-- 交替过程示例
mkAlternatingProcess : ∀ {ℓ} (C : Set ℓ) → C → Process Bool C
mkAlternatingProcess C c₀ = mkProc true c₀ alt-stream alt-essence-const refl
  where
    alt-stream : Stream (Bool × C)
    alt-stream .Stream.head = (true , c₀)
    alt-stream .Stream.tail = alt-step
      where
        alt-step : Stream (Bool × C)
        alt-step .Stream.head = (false , c₀)
        alt-step .Stream.tail = alt-stream
    alt-essence-const : Always (λ x → proj₂ x ≡ c₀) alt-stream
    alt-essence-const .Always.head = refl
    alt-essence-const .Always.tail = alt-step-const
      where
        alt-step-const : Always (λ x → proj₂ x ≡ c₀) (Stream.tail alt-stream)
        alt-step-const .Always.head = refl
        alt-step-const .Always.tail = alt-essence-const

-- Tensor product: Parallel composition of processes
-- 张量积：过程的并行复合
merge-state : ∀ {ℓ₁ ℓ₂ ℓ₃ ℓ₄} {O₁ : Set ℓ₁} {C₁ : Set ℓ₂} {O₂ : Set ℓ₃} {C₂ : Set ℓ₄}
            → (O₁ × C₁) → (O₂ × C₂) → ((O₁ × O₂) × (C₁ × C₂))
merge-state (o1 , c1) (o2 , c2) = ((o1 , o2) , (c1 , c2))
merge-stream : ∀ {ℓ₁ ℓ₂ ℓ₃ ℓ₄} {O₁ : Set ℓ₁} {C₁ : Set ℓ₂} {O₂ : Set ℓ₃} {C₂ : Set ℓ₄}
             → Stream (O₁ × C₁) → Stream (O₂ × C₂) → Stream ((O₁ × O₂) × (C₁ × C₂))
merge-stream s₁ s₂ .Stream.head = merge-state (Stream.head s₁) (Stream.head s₂)
merge-stream s₁ s₂ .Stream.tail = merge-stream (Stream.tail s₁) (Stream.tail s₂)
private
  merge-const-lemma : ∀ {ℓ₁ ℓ₂ ℓ₃ ℓ₄} {O₁ : Set ℓ₁} {C₁ : Set ℓ₂} {O₂ : Set ℓ₃} {C₂ : Set ℓ₄}
                    (a : O₁ × C₁) (b : O₂ × C₂) →
    merge-stream (constStream a) (constStream b) ≈ constStream (merge-state a b)
  merge-const-lemma a b ._≈_.head≈ = refl
  merge-const-lemma a b ._≈_.tail≈ = merge-const-lemma a b
merge-stream-observe : ∀ {ℓ₁ ℓ₂ ℓ₃ ℓ₄}
                     {O₁ : Set ℓ₁} {C₁ : Set ℓ₂} {O₂ : Set ℓ₃} {C₂ : Set ℓ₄}
                     (s₁ : Stream (O₁ × C₁)) (s₂ : Stream (O₂ × C₂)) (n : ℕ) →
                     proj₁ (Stream.head (stream-tail-n (merge-stream s₁ s₂) n)) ≡
                     (proj₁ (Stream.head (stream-tail-n s₁ n)) , proj₁ (Stream.head (stream-tail-n s₂ n)))
merge-stream-observe s₁ s₂ zero = refl
merge-stream-observe s₁ s₂ (suc n) = merge-stream-observe (Stream.tail s₁) (Stream.tail s₂) n
_⊗_ : ∀ {ℓ₁ ℓ₂ ℓ₃ ℓ₄} {O₁ : Set ℓ₁} {C₁ : Set ℓ₂} {O₂ : Set ℓ₃} {C₂ : Set ℓ₄}
    → Process O₁ C₁ → Process O₂ C₂ → Process (O₁ × O₂) (C₁ × C₂)
_⊗_ {O₁ = O₁} {C₁ = C₁} {O₂ = O₂} {C₂ = C₂} p₁ p₂ =
  mkProc (o p₁ , o p₂) (c p₁ , c p₂) combined-stream combined-const combined-init
  where
    combined-stream : Stream ((O₁ × O₂) × (C₁ × C₂))
    combined-stream = merge-stream (stream p₁) (stream p₂)
    merge-always : (s₁ : Stream (O₁ × C₁)) (s₂ : Stream (O₂ × C₂))
                   (alw₁ : Always (λ x → proj₂ x ≡ c p₁) s₁)
                   (alw₂ : Always (λ x → proj₂ x ≡ c p₂) s₂)
                   → Always (λ x → proj₂ x ≡ (c p₁ , c p₂)) (merge-stream s₁ s₂)
    merge-always s₁ s₂ alw₁ alw₂ .Always.head = cong₂ _,_ (Always.head alw₁) (Always.head alw₂)
    merge-always s₁ s₂ alw₁ alw₂ .Always.tail = merge-always (Stream.tail s₁) (Stream.tail s₂) (Always.tail alw₁) (Always.tail alw₂)
    combined-const : Always (λ x → proj₂ x ≡ (c p₁ , c p₂)) combined-stream
    combined-const = merge-always (stream p₁) (stream p₂) (essence-const p₁) (essence-const p₂)
    combined-init : proj₁ (Stream.head combined-stream) ≡ (o p₁ , o p₂)
    combined-init = cong₂ _,_ (init-consistent p₁) (init-consistent p₂)
infixl 6 _⊗_
⊗-preserves-standard : ∀ {ℓ₁ ℓ₂ ℓ₃ ℓ₄} {O₁ : Set ℓ₁} {C₁ : Set ℓ₂} {O₂ : Set ℓ₃} {C₂ : Set ℓ₄}
                      (o₁ : O₁) (c₁ : C₁) (o₂ : O₂) (c₂ : C₂) →
  (mkStandardProcess _ _ o₁ c₁ ⊗ mkStandardProcess _ _ o₂ c₂) ≈ₚ
  mkStandardProcess _ _ (o₁ , o₂) (c₁ , c₂)
⊗-preserves-standard o₁ c₁ o₂ c₂ = merge-const-lemma (o₁ , c₁) (o₂ , c₂)

-- Heterogeneous process bisimulation
-- 异类型过程互模拟
≈-hetero-sym : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {B : Set ℓ₂} (f : A → B) (g : B → A)
              → (∀ x → g (f x) ≡ x)
              → (s₁ : Stream A) (s₂ : Stream B)
              → ≈-hetero s₁ s₂ f
              → ≈-hetero s₂ s₁ g
≈-hetero-sym f g inv s₁ s₂ eq .head≈ =
  trans (cong g (sym (eq .head≈))) (inv (Stream.head s₁))
≈-hetero-sym f g inv s₁ s₂ eq .tail≈ =
  ≈-hetero-sym f g inv (Stream.tail s₁) (Stream.tail s₂) (eq .tail≈)
record ≈ₚ-hetero {ℓ₁ ℓ₂ ℓ₃ ℓ₄} {O₁ : Set ℓ₁} {C₁ : Set ℓ₂} {O₂ : Set ℓ₃} {C₂ : Set ℓ₄}
                  (p₁ : Process O₁ C₁) (p₂ : Process O₂ C₂)
                  (f-O : O₁ → O₂) (f-C : C₁ → C₂) : Set (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃ ⊔ ℓ₄) where
  field
    stream≈ : ≈-hetero (stream p₁) (stream p₂) (comb f-O f-C)
open ≈ₚ-hetero public
≈ₚ-hetero-refl : ∀ {ℓ₁ ℓ₂} {O : Set ℓ₁} {C : Set ℓ₂} (p : Process O C) → ≈ₚ-hetero p p id id
≈ₚ-hetero-refl p .stream≈ = ≈-hetero-refl (stream p)

-- Symmetric monoidal category structure (Isomorphisms)
-- 对称幺半范畴结构（同构）
UnitProcess : Process (⊤ {0ℓ}) (⊤ {0ℓ})
UnitProcess = mkStandardProcess (⊤ {0ℓ}) (⊤ {0ℓ}) (tt {0ℓ}) (tt {0ℓ})
assoc-iso-O : ∀ {ℓ₁ ℓ₂ ℓ₃} {A : Set ℓ₁} {B : Set ℓ₂} {C : Set ℓ₃} → ((A × B) × C) → (A × (B × C))
assoc-iso-O ((a , b) , c) = (a , (b , c))
assoc-iso-C : ∀ {ℓ₁ ℓ₂ ℓ₃} {A : Set ℓ₁} {B : Set ℓ₂} {C : Set ℓ₃} → ((A × B) × C) → (A × (B × C))
assoc-iso-C ((a , b) , c) = (a , (b , c))
merge-stream-assoc : ∀ {ℓ₁ ℓ₂ ℓ₃ ℓ₄ ℓ₅ ℓ₆}
                     {O₁ : Set ℓ₁} {C₁ : Set ℓ₂} {O₂ : Set ℓ₃} {C₂ : Set ℓ₄} {O₃ : Set ℓ₅} {C₃ : Set ℓ₆}
                     (s₁ : Stream (O₁ × C₁)) (s₂ : Stream (O₂ × C₂)) (s₃ : Stream (O₃ × C₃))
                     → ≈-hetero {ℓ₁ = ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃ ⊔ ℓ₄ ⊔ ℓ₅ ⊔ ℓ₆} {ℓ₂ = ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃ ⊔ ℓ₄ ⊔ ℓ₅ ⊔ ℓ₆}
                                (merge-stream (merge-stream s₁ s₂) s₃)
                                (merge-stream s₁ (merge-stream s₂ s₃))
                                (comb assoc-iso-O assoc-iso-C)
merge-stream-assoc s₁ s₂ s₃ .head≈ = refl
merge-stream-assoc s₁ s₂ s₃ .tail≈ = merge-stream-assoc (Stream.tail s₁) (Stream.tail s₂) (Stream.tail s₃)
⊗-assoc-hetero : ∀ {ℓ₁ ℓ₂ ℓ₃ ℓ₄ ℓ₅ ℓ₆}
                 {O₁ : Set ℓ₁} {C₁ : Set ℓ₂} {O₂ : Set ℓ₃} {C₂ : Set ℓ₄} {O₃ : Set ℓ₅} {C₃ : Set ℓ₆}
                 (p₁ : Process O₁ C₁) (p₂ : Process O₂ C₂) (p₃ : Process O₃ C₃)
                 → ≈ₚ-hetero ((p₁ ⊗ p₂) ⊗ p₃) (p₁ ⊗ (p₂ ⊗ p₃)) assoc-iso-O assoc-iso-C
⊗-assoc-hetero p₁ p₂ p₃ .stream≈ = merge-stream-assoc (stream p₁) (stream p₂) (stream p₃)
left-unit-O : ∀ {ℓ⊤ ℓO} {O : Set ℓO} → (⊤ {ℓ⊤} × O) → O
left-unit-O (tt , o) = o
left-unit-C : ∀ {ℓ⊤ ℓC} {C : Set ℓC} → (⊤ {ℓ⊤} × C) → C
left-unit-C (tt , c) = c
left-stream-bisim : ∀ {ℓ₁ ℓ₂} {O : Set ℓ₁} {C : Set ℓ₂} (s : Stream (O × C))
                    → ≈-hetero {ℓ₁ = ℓ₁ ⊔ ℓ₂} {ℓ₂ = ℓ₁ ⊔ ℓ₂}
                               (merge-stream (stream UnitProcess) s) s
                               (comb left-unit-O left-unit-C)
left-stream-bisim s .head≈ = refl
left-stream-bisim s .tail≈ = left-stream-bisim (Stream.tail s)
⊗-left-unit-hetero : ∀ {ℓ₁ ℓ₂} {O : Set ℓ₁} {C : Set ℓ₂} (p : Process O C)
                     → ≈ₚ-hetero (UnitProcess ⊗ p) p left-unit-O left-unit-C
⊗-left-unit-hetero p .stream≈ = left-stream-bisim (stream p)
right-unit-O : ∀ {ℓO ℓ⊤} {O : Set ℓO} → (O × ⊤ {ℓ⊤}) → O
right-unit-O (o , tt) = o
right-unit-C : ∀ {ℓC ℓ⊤} {C : Set ℓC} → (C × ⊤ {ℓ⊤}) → C
right-unit-C (c , tt) = c
right-stream-bisim : ∀ {ℓ₁ ℓ₂} {O : Set ℓ₁} {C : Set ℓ₂} (s : Stream (O × C))
                     → ≈-hetero {ℓ₁ = ℓ₁ ⊔ ℓ₂} {ℓ₂ = ℓ₁ ⊔ ℓ₂}
                                (merge-stream s (stream UnitProcess)) s
                                (comb right-unit-O right-unit-C)
right-stream-bisim s .head≈ = refl
right-stream-bisim s .tail≈ = right-stream-bisim (Stream.tail s)
⊗-right-unit-hetero : ∀ {ℓ₁ ℓ₂} {O : Set ℓ₁} {C : Set ℓ₂} (p : Process O C)
                      → ≈ₚ-hetero (p ⊗ UnitProcess) p right-unit-O right-unit-C
⊗-right-unit-hetero p .stream≈ = right-stream-bisim (stream p)
swap-O : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {B : Set ℓ₂} → (A × B) → (B × A)
swap-O (a , b) = (b , a)
swap-C : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {B : Set ℓ₂} → (A × B) → (B × A)
swap-C (a , b) = (b , a)
merge-stream-comm : ∀ {ℓ₁ ℓ₂ ℓ₃ ℓ₄}
                    {O₁ : Set ℓ₁} {C₁ : Set ℓ₂} {O₂ : Set ℓ₃} {C₂ : Set ℓ₄}
                    (s₁ : Stream (O₁ × C₁)) (s₂ : Stream (O₂ × C₂))
                    → ≈-hetero {ℓ₁ = ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃ ⊔ ℓ₄} {ℓ₂ = ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃ ⊔ ℓ₄}
                               (merge-stream s₁ s₂) (merge-stream s₂ s₁) (comb swap-O swap-C)
merge-stream-comm s₁ s₂ .head≈ = refl
merge-stream-comm s₁ s₂ .tail≈ = merge-stream-comm (Stream.tail s₁) (Stream.tail s₂)
⊗-comm-hetero : ∀ {ℓ₁ ℓ₂ ℓ₃ ℓ₄}
                {O₁ : Set ℓ₁} {C₁ : Set ℓ₂} {O₂ : Set ℓ₃} {C₂ : Set ℓ₄}
                (p₁ : Process O₁ C₁) (p₂ : Process O₂ C₂)
                → ≈ₚ-hetero (p₁ ⊗ p₂) (p₂ ⊗ p₁) swap-O swap-C
⊗-comm-hetero p₁ p₂ .stream≈ = merge-stream-comm (stream p₁) (stream p₂)

-- Process Uniqueness Theorem: Two processes with identical cores, identical initial observations, and respective constancy are necessarily bisimilar
-- 过程唯一性定理：核心相同、初始观察相同且各自恒常的两个过程必然互模拟等价
Process-Uniqueness : Setω
Process-Uniqueness =
  ∀ {ℓ₁ ℓ₂} {O : Set ℓ₁} {C : Set ℓ₂} (o₀ : O) (c₀ : C) →
  ∀ (p q : Process O C) →
  core p ≡ c₀ →
  core q ≡ c₀ →
  Process.o p ≡ o₀ →
  Process.o q ≡ o₀ →
  Always (λ x → proj₁ x ≡ o₀) (stream p) →
  Always (λ x → proj₁ x ≡ o₀) (stream q) →
  p ≈ₚ q
process-uniqueness-proof : Process-Uniqueness
process-uniqueness-proof {O = O} {C = C} o₀ c₀ p q cp≡c₀ cq≡c₀ op≡o₀ oq≡o₀ p-always-o₀ q-always-o₀ =
  let
    p-both-const : BothComponentsConstant o₀ c₀ (stream p)
    p-both-const = (p-always-o₀ , subst (λ x → Always (λ y → proj₂ y ≡ x) (stream p)) cp≡c₀ (essence-const p))
    q-both-const : BothComponentsConstant o₀ c₀ (stream q)
    q-both-const = (q-always-o₀ , subst (λ x → Always (λ y → proj₂ y ≡ x) (stream q)) cq≡c₀ (essence-const q))
    p≈const : stream p ≈ constStream (o₀ , c₀)
    p≈const = both-const-implies-≈-constStream o₀ c₀ (stream p) p-both-const
    q≈const : stream q ≈ constStream (o₀ , c₀)
    q≈const = both-const-implies-≈-constStream o₀ c₀ (stream q) q-both-const
  in
  ≈-trans p≈const (≈-sym q≈const)

-- Lemmas for the ⊗ tensor product
-- ⊗ 张量积的引理
private
  merge-stream-cong : ∀ {ℓ₁ ℓ₂ ℓ₃ ℓ₄}
                    {O₁ : Set ℓ₁} {C₁ : Set ℓ₂} {O₂ : Set ℓ₃} {C₂ : Set ℓ₄}
                    {s₁ s₁' : Stream (O₁ × C₁)} {s₂ s₂' : Stream (O₂ × C₂)}
                    → s₁ ≈ s₁' → s₂ ≈ s₂' → merge-stream s₁ s₂ ≈ merge-stream s₁' s₂'
  merge-stream-cong eq1 eq2 ._≈_.head≈ = cong₂ merge-state (_≈_.head≈ eq1) (_≈_.head≈ eq2)
  merge-stream-cong eq1 eq2 ._≈_.tail≈ = merge-stream-cong (_≈_.tail≈ eq1) (_≈_.tail≈ eq2)
⊗-functor : ∀ {ℓ₁ ℓ₂ ℓ₃ ℓ₄}
          {O₁ : Set ℓ₁} {C₁ : Set ℓ₂} {O₂ : Set ℓ₃} {C₂ : Set ℓ₄}
          {p₁ p₁' : Process O₁ C₁} {p₂ p₂' : Process O₂ C₂}
          → p₁ ≈ₚ p₁' → p₂ ≈ₚ p₂' → (p₁ ⊗ p₂) ≈ₚ (p₁' ⊗ p₂')
⊗-functor eq1 eq2 = merge-stream-cong eq1 eq2
⊗-core-comm : ∀ {ℓ₁ ℓ₂ ℓ₃ ℓ₄}
              {O₁ : Set ℓ₁} {C₁ : Set ℓ₂} {O₂ : Set ℓ₃} {C₂ : Set ℓ₄}
              (p₁ : Process O₁ C₁) (p₂ : Process O₂ C₂) →
              core (p₁ ⊗ p₂) ≡ (core p₁ , core p₂)
⊗-core-comm p₁ p₂ = refl
⊗-next-comm : ∀ {ℓ₁ ℓ₂ ℓ₃ ℓ₄}
              {O₁ : Set ℓ₁} {C₁ : Set ℓ₂} {O₂ : Set ℓ₃} {C₂ : Set ℓ₄}
              → (p1 : Process O₁ C₁) (p2 : Process O₂ C₂)
              → (next (p1 ⊗ p2)) ≈ₚ (next p1 ⊗ next p2)
⊗-next-comm p1 p2 ._≈_.head≈ = refl
⊗-next-comm p1 p2 ._≈_.tail≈ = ≈-refl
⊗-observe-comm : ∀ {ℓ₁ ℓ₂ ℓ₃ ℓ₄}
                 {O₁ : Set ℓ₁} {C₁ : Set ℓ₂} {O₂ : Set ℓ₃} {C₂ : Set ℓ₄}
                 (p₁ : Process O₁ C₁) (p₂ : Process O₂ C₂) (n : ℕ) →
                 observe (p₁ ⊗ p₂) n ≡ (observe p₁ n , observe p₂ n)
⊗-observe-comm p₁ p₂ n =
  begin
    observe (p₁ ⊗ p₂) n
      ≡⟨ refl ⟩
    proj₁ (Stream.head (stream-tail-n (merge-stream (stream p₁) (stream p₂)) n))
      ≡⟨ merge-stream-observe (stream p₁) (stream p₂) n ⟩
    (observe p₁ n , observe p₂ n)
  ∎

-- Symmetric monoidal category coherence theorems
-- 对称幺半范畴一致性定理
pentagon-theorem : ∀ {ℓ₁ ℓ₂ ℓ₃ ℓ₄ ℓ₅ ℓ₆ ℓ₇ ℓ₈}
                  {O₁ : Set ℓ₁} {C₁ : Set ℓ₂} {O₂ : Set ℓ₃} {C₂ : Set ℓ₄}
                  {O₃ : Set ℓ₅} {C₃ : Set ℓ₆} {O₄ : Set ℓ₇} {C₄ : Set ℓ₈}
                  (p₁ : Process O₁ C₁) (p₂ : Process O₂ C₂)
                  (p₃ : Process O₃ C₃) (p₄ : Process O₄ C₄)
                  → ≈ₚ-hetero
                      (((p₁ ⊗ p₂) ⊗ p₃) ⊗ p₄)
                      (p₁ ⊗ (p₂ ⊗ (p₃ ⊗ p₄)))
                      (assoc-iso-O ∘ assoc-iso-O)
                      (assoc-iso-C ∘ assoc-iso-C)
pentagon-theorem p₁ p₂ p₃ p₄ .stream≈ =
  ≈-hetero-trans
    (comb assoc-iso-O assoc-iso-C)
    (comb assoc-iso-O assoc-iso-C)
    (stream (((p₁ ⊗ p₂) ⊗ p₃) ⊗ p₄))
    (stream ((p₁ ⊗ p₂) ⊗ (p₃ ⊗ p₄)))
    (stream (p₁ ⊗ (p₂ ⊗ (p₃ ⊗ p₄))))
    (merge-stream-assoc (merge-stream (stream p₁) (stream p₂)) (stream p₃) (stream p₄))
    (merge-stream-assoc (stream p₁) (stream p₂) (merge-stream (stream p₃) (stream p₄)))
triangle-theorem : ∀ {ℓ₁ ℓ₂ ℓ₃ ℓ₄}
                  {O₁ : Set ℓ₁} {C₁ : Set ℓ₂} {O₂ : Set ℓ₃} {C₂ : Set ℓ₄}
                  (p₁ : Process O₁ C₁) (p₂ : Process O₂ C₂)
                  → ≈ₚ-hetero
                      (p₁ ⊗ (UnitProcess ⊗ p₂))
                      ((p₁ ⊗ UnitProcess) ⊗ p₂)
                      (λ (o1 , (tt , o2)) → ((o1 , tt) , o2))
                      (λ (c1 , (tt , c2)) → ((c1 , tt) , c2))
triangle-theorem p₁ p₂ .stream≈ .head≈ = refl
triangle-theorem p₁ p₂ .stream≈ .tail≈ =
  triangle-theorem (next p₁) (next p₂) .stream≈

-- Process category: Morphism composition and identity morphisms
-- 过程范畴：态射复合与恒等态射
_∘ₚ_ : ∀ {ℓ₁ ℓ₂ ℓ₃ ℓ₄ ℓ₅ ℓ₆}
        {O₁ : Set ℓ₁} {C₁ : Set ℓ₂}
        {O₂ : Set ℓ₃} {C₂ : Set ℓ₄}
        {O₃ : Set ℓ₅} {C₃ : Set ℓ₆}
        {p₁ : Process O₁ C₁} {p₂ : Process O₂ C₂} {p₃ : Process O₃ C₃}
        {f-O : O₁ → O₂} {f-C : C₁ → C₂}
        {g-O : O₂ → O₃} {g-C : C₂ → C₃}
      → ≈ₚ-hetero p₂ p₃ g-O g-C
      → ≈ₚ-hetero p₁ p₂ f-O f-C
      → ≈ₚ-hetero p₁ p₃ (g-O ∘ f-O) (g-C ∘ f-C)
_∘ₚ_ {p₁ = p₁} {p₂ = p₂} {p₃ = p₃} {f-O = f-O} {f-C = f-C} {g-O = g-O} {g-C = g-C} g f =
  record { stream≈ = ≈-hetero-trans (comb f-O f-C) (comb g-O g-C) (stream p₁) (stream p₂) (stream p₃) (stream≈ f) (stream≈ g) }
infixr 9 _∘ₚ_
idₚ : ∀ {ℓ₁ ℓ₂} {O : Set ℓ₁} {C : Set ℓ₂} {p : Process O C}
     → ≈ₚ-hetero p p id id
idₚ = ≈ₚ-hetero-refl _

-- Coherent pattern:阶段性 snapshots of processes
-- 相干模式：过程阶段性快照
record CoherentPattern {ℓ₁ ℓ₂} (O : Set ℓ₁) (C : Set ℓ₂) : Set (ℓ₁ ⊔ ℓ₂) where
  constructor mkPattern
  field
    base     : Process O C
    internal : ℕ
    external : ℕ
open CoherentPattern public
data CoherenceStage : Set where
  Alive  : CoherenceStage
  Broken : CoherenceStage
  Faded  : CoherenceStage
Alive≢Faded : Alive ≢ Faded
Alive≢Faded eq = subst P eq (tt {0ℓ})
  where
  P : CoherenceStage → Set 0ℓ
  P Alive = ⊤ {0ℓ}
  P Faded = ⊥ {0ℓ}
  P Broken = ⊤ {0ℓ}
Alive≢Broken : Alive ≢ Broken
Alive≢Broken eq = subst P eq (tt {0ℓ})
  where
  P : CoherenceStage → Set 0ℓ
  P Alive = ⊤ {0ℓ}
  P Faded = ⊤ {0ℓ}
  P Broken = ⊥ {0ℓ}
Faded≢Alive : Faded ≢ Alive
Faded≢Alive = Alive≢Faded ∘ sym
Faded≢Broken : Faded ≢ Broken
Faded≢Broken eq = subst P eq (tt {0ℓ})
  where
  P : CoherenceStage → Set 0ℓ
  P Alive = ⊤ {0ℓ}
  P Faded = ⊤ {0ℓ}
  P Broken = ⊥ {0ℓ}
Broken≢Alive : Broken ≢ Alive
Broken≢Alive = Alive≢Broken ∘ sym
Broken≢Faded : Broken ≢ Faded
Broken≢Faded = Faded≢Broken ∘ sym

-- Feedback gain: Difference between intrinsic drive and external resistance
-- 反馈增益：内禀驱动力与外部阻力之差
feedback-gain : ℕ → ℕ → ℕ
feedback-gain i e = i ∸ e
lemma-zero-feedback : ∀ e → feedback-gain 0 e ≡ 0
lemma-zero-feedback zero = refl
lemma-zero-feedback (suc e) = refl
lemma-positive-i-le-e-feedback-zero : ∀ {i e} → i > 0 → i ≤ e → feedback-gain i e ≡ 0
lemma-positive-i-le-e-feedback-zero _ i≤e = m≤n⇒m∸n≡0 i≤e
∸-additive : ∀ {i1 e1 i2 e2} → e1 ≤ i1 → e2 ≤ i2 → (i1 ∸ e1) + (i2 ∸ e2) ≡ (i1 + i2) ∸ (e1 + e2)
∸-additive {i1} {e1} {i2} {e2} e1≤i1 e2≤i2 =
  let
    a = i1 ∸ e1
    b = i2 ∸ e2
    p1 : i1 ≡ e1 + a
    p1 = m≤n→n≡m+n∸m e1≤i1
    p2 : i2 ≡ e2 + b
    p2 = m≤n→n≡m+n∸m e2≤i2
    add-rearrange : (e1 + a) + (e2 + b) ≡ (e1 + e2) + (a + b)
    add-rearrange =
      begin
        (e1 + a) + (e2 + b)
          ≡⟨ +-assoc e1 a (e2 + b) ⟩
        e1 + (a + (e2 + b))
          ≡⟨ cong (e1 +_) (cong (a +_) (+-comm e2 b)) ⟩
        e1 + (a + (b + e2))
          ≡⟨ cong (e1 +_) (sym (+-assoc a b e2)) ⟩
        e1 + ((a + b) + e2)
          ≡⟨ cong (e1 +_) (+-comm (a + b) e2) ⟩
        e1 + (e2 + (a + b))
          ≡⟨ sym (+-assoc e1 e2 (a + b)) ⟩
        (e1 + e2) + (a + b)
      ∎
    sum-eq : i1 + i2 ≡ (e1 + e2) + (a + b)
    sum-eq = trans (cong₂ _+_ p1 p2) add-rearrange
  in
  begin
    a + b
      ≡⟨ sym (m+n∸m≡n (e1 + e2) (a + b)) ⟩
    ((e1 + e2) + (a + b)) ∸ (e1 + e2)
      ≡⟨ cong (λ x → x ∸ (e1 + e2)) (sym sum-eq) ⟩
    (i1 + i2) ∸ (e1 + e2)
  ∎
feedback-gain-additive-coherent : ∀ {i1 e1 i2 e2}
                                → i1 > e1 → i2 > e2
                                → feedback-gain i1 e1 + feedback-gain i2 e2 ≡ feedback-gain (i1 + i2) (e1 + e2)
feedback-gain-additive-coherent {i1} {e1} {i2} {e2} i1>e1 i2>e2 =
  ∸-additive (suc≤→≤ i1>e1) (suc≤→≤ i2>e2)

-- Coherence determination and evolution progression
-- 相干性判定与演化推进
is-coherent : ∀ {ℓ₁ ℓ₂} {O : Set ℓ₁} {C : Set ℓ₂} → CoherentPattern O C → Set 0ℓ
is-coherent cp = internal cp > external cp
step-process : ∀ {ℓ₁ ℓ₂} {O : Set ℓ₁} {C : Set ℓ₂} → CoherentPattern O C → Process O C
step-process cp = next (base cp)
next-external : ∀ {ℓ} {O : Set ℓ} → (O → ℕ) → CoherentPattern O (⊤ {ℓ}) → ℕ
next-external env cp = env (observe (base cp) 0)
next-internal : ∀ {ℓ} {O : Set ℓ} → (O → ℕ) → CoherentPattern O (⊤ {ℓ}) → ℕ
next-internal env cp = internal cp + feedback-gain (internal cp) (external cp)
next-coherent : ∀ {ℓ} {O : Set ℓ} → (O → ℕ) → CoherentPattern O ⊤ → CoherentPattern O ⊤
next-coherent env cp = mkPattern
  (step-process cp)
  (next-internal env cp)
  (env (observe (step-process cp) 0))

-- Dynamic coherence: Local transition laws of evolution streams
-- 动态一致性：演化流的局部转换律
record DynamicCoherent {ℓ} {O : Set ℓ} (env : O → ℕ) (s : Stream (CoherentPattern O (⊤ {ℓ}))) : Set ℓ where
  coinductive
  field
    internal-step : Stream.head (Stream.tail s) .internal ≡ next-internal env (Stream.head s)
    external-step : Stream.head (Stream.tail s) .external ≡ env (observe (Stream.head (Stream.tail s) .base) 0)
    process-step  : Stream.head (Stream.tail s) .base     ≡ step-process (Stream.head s)
    tail-ok       : DynamicCoherent env (Stream.tail s)
open DynamicCoherent public
AlwaysCoherent : ∀ {ℓ} {O : Set ℓ} → Stream (CoherentPattern O (⊤ {ℓ})) → Set ℓ
AlwaysCoherent {ℓ = ℓ} s = Always {ℓ = ℓ} {ℓ' = 0ℓ} is-coherent s

-- Evolution coalgebra: Generating coherent streams from initial processes and internal drive (Ontological perspective)
-- 演化余代数：从初始过程与内部驱动力生成相干流（本体论视角）
module Evolution {ℓ} (O : Set ℓ) (env : O → ℕ) (init-proc : Process O (⊤ {ℓ})) (init-int : ℕ) where
  State = Process O (⊤ {ℓ}) × ℕ
  coalgebra : State → CoherentPattern O (⊤ {ℓ}) × State
  coalgebra (proc , i) =
    let e  = env (observe proc 0)
        cp = mkPattern proc i e
        i' = i + feedback-gain i e
        proc' = next proc
    in cp , (proc' , i')
  evolution : State → Stream (CoherentPattern O (⊤ {ℓ}))
  evolution = ana coalgebra
  start-stream : ℕ → Stream (CoherentPattern O (⊤ {ℓ}))
  start-stream i = evolution (init-proc , i)
module _ {ℓ} (O : Set ℓ) (env : O → ℕ) (init-proc : Process O (⊤ {ℓ})) (init-int : ℕ) where
  open Evolution O env init-proc init-int
  dynamic-consistent : ∀ st → DynamicCoherent env (evolution st)
  dynamic-consistent st .internal-step = refl
  dynamic-consistent st .external-step = refl
  dynamic-consistent st .process-step = refl
  dynamic-consistent st .tail-ok = dynamic-consistent (proj₂ (coalgebra st))

-- Coherence stage determination
-- 相干阶段判定
CoherentStage : ∀ {ℓ} {O : Set ℓ} → CoherentPattern O (⊤ {ℓ}) → CoherenceStage
CoherentStage cp =
  if external cp <ᵇ internal cp
    then Alive
    else if internal cp ≡ᵇ 0
      then Faded
      else Broken
faded→internal-zero : ∀ {ℓ} {O : Set ℓ} (cp : CoherentPattern O (⊤ {ℓ}))
                    → CoherentStage cp ≡ Faded
                    → internal cp ≡ 0
faded→internal-zero cp eq = helper (external cp <ᵇ internal cp) (internal cp ≡ᵇ 0) refl refl
  where
  helper : (b1 b2 : Bool)
         → b1 ≡ (external cp <ᵇ internal cp)
         → b2 ≡ (internal cp ≡ᵇ 0)
         → internal cp ≡ 0
  helper true _ eq1 _ =
    let
      b1≡true : (external cp <ᵇ internal cp) ≡ true
      b1≡true = sym eq1
      stage≡Alive : CoherentStage cp ≡ Alive
      stage≡Alive = cong (λ b → if b then Alive else if (internal cp ≡ᵇ 0) then Faded else Broken) b1≡true
      contradiction : Alive ≡ Faded
      contradiction = trans (sym stage≡Alive) eq
    in ⊥-elim (Alive≢Faded contradiction)
  helper false true _ eq2 with internal cp
  ... | zero = refl
  ... | suc n =
    let
      suc≡ᵇ0≡false : (suc n ≡ᵇ 0) ≡ false
      suc≡ᵇ0≡false = refl
      contradiction : true ≡ false
      contradiction = trans eq2 suc≡ᵇ0≡false
    in ⊥-elim (true≢false contradiction)
  helper false false eq1 eq2 =
    let
      b1≡false : (external cp <ᵇ internal cp) ≡ false
      b1≡false = sym eq1
      b2≡false : (internal cp ≡ᵇ 0) ≡ false
      b2≡false = sym eq2
      step1 : CoherentStage cp ≡ (if (internal cp ≡ᵇ 0) then Faded else Broken)
      step1 = cong (λ b1 → if b1 then Alive else if (internal cp ≡ᵇ 0) then Faded else Broken) b1≡false
      step2 : (if (internal cp ≡ᵇ 0) then Faded else Broken) ≡ Broken
      step2 = cong (λ b2 → if b2 then Faded else Broken) b2≡false
      stage≡Broken : CoherentStage cp ≡ Broken
      stage≡Broken = trans step1 step2
      contradiction : Broken ≡ Faded
      contradiction = trans (sym stage≡Broken) eq
    in ⊥-elim (Broken≢Faded contradiction)
internal-zero→faded : ∀ {ℓ} {O : Set ℓ} (cp : CoherentPattern O (⊤ {ℓ}))
                    → internal cp ≡ 0
                    → CoherentStage cp ≡ Faded
internal-zero→faded cp i≡0 =
  let
    i = internal cp
    e = external cp
    b1≡false : (e <ᵇ i) ≡ false
    b1≡false = subst (λ x → (e <ᵇ x) ≡ false) (sym i≡0) (0<ᵇn≡false e)
    b2≡true : (i ≡ᵇ 0) ≡ true
    b2≡true = subst (λ x → (x ≡ᵇ 0) ≡ true) (sym i≡0) refl
  in
    begin
      CoherentStage cp
        ≡⟨ refl ⟩
      (if e <ᵇ i then Alive else if (i ≡ᵇ 0) then Faded else Broken)
        ≡⟨ cong (λ b → if b then Alive else if (i ≡ᵇ 0) then Faded else Broken) b1≡false ⟩
      (if (i ≡ᵇ 0) then Faded else Broken)
        ≡⟨ cong (λ b → if b then Faded else Broken) b2≡true ⟩
      Faded
    ∎
faded-iff-internal-zero : ∀ {ℓ} {O : Set ℓ} (cp : CoherentPattern O (⊤ {ℓ}))
                        → (CoherentStage cp ≡ Faded → internal cp ≡ 0)
                        × (internal cp ≡ 0 → CoherentStage cp ≡ Faded)
faded-iff-internal-zero cp = faded→internal-zero cp , internal-zero→faded cp
mkFaded : ∀ {ℓ} {O : Set ℓ} (cp : CoherentPattern O (⊤ {ℓ})) → internal cp ≡ 0 → external cp ≡ 0 → CoherentStage cp ≡ Faded
mkFaded cp i≡0 _ = internal-zero→faded cp i≡0

-- Irreversibility theorem for the Faded stage
-- Faded 阶段的不可逆定理
module _ {ℓ} (O : Set ℓ) (env : O → ℕ) where
  zero-internal-persist : (cp : CoherentPattern O (⊤ {ℓ}))
                        → internal cp ≡ 0
                        → next-internal env cp ≡ 0
  zero-internal-persist cp refl =
    let e = external cp
    in begin
      0 + feedback-gain 0 e
        ≡⟨ +-identityˡ (feedback-gain 0 e) ⟩
      feedback-gain 0 e
        ≡⟨ lemma-zero-feedback e ⟩
      0
    ∎
  theorem-faded-irreversible : ∀ (s : Stream (CoherentPattern O (⊤ {ℓ})))
                             → DynamicCoherent env s
                             → CoherentStage (Stream.head s) ≡ Faded
                             → CoherentStage (Stream.head (Stream.tail s)) ≡ Faded
  theorem-faded-irreversible s dyn head-faded =
    let
      head-cp = Stream.head s
      i0≡0 = faded→internal-zero head-cp head-faded
      i1≡0 = trans (dyn .internal-step) (zero-internal-persist head-cp i0≡0)
      next-cp = Stream.head (Stream.tail s)
    in internal-zero→faded next-cp i1≡0

-- Auxiliary lemmas for the Broken stage
-- Broken 阶段的辅助引理
broken→¬i>e : ∀ {ℓ} {O : Set ℓ} (cp : CoherentPattern O (⊤ {ℓ}))
            → CoherentStage cp ≡ Broken
            → ¬ (internal cp > external cp)
broken→¬i>e cp broken i>e =
  let
    b1≡true : (external cp <ᵇ internal cp) ≡ true
    b1≡true = <⇒<ᵇ-eq i>e
    stage≡Alive : CoherentStage cp ≡ Alive
    stage≡Alive = cong (λ b → if b then Alive else if (internal cp ≡ᵇ 0) then Faded else Broken) b1≡true
    contradiction : Alive ≡ Broken
    contradiction = trans (sym stage≡Alive) broken
  in ⊥-elim (Alive≢Broken contradiction)
broken→¬i≡0 : ∀ {ℓ} {O : Set ℓ} (cp : CoherentPattern O (⊤ {ℓ}))
            → CoherentStage cp ≡ Broken
            → ¬ (internal cp ≡ 0)
broken→¬i≡0 cp broken i≡0 =
  let
    i = internal cp
    e = external cp
    b2≡true : (i ≡ᵇ 0) ≡ true
    b2≡true = subst (λ x → (x ≡ᵇ 0) ≡ true) (sym i≡0) refl
    b1≡false : (e <ᵇ i) ≡ false
    b1≡false = subst (λ x → (e <ᵇ x) ≡ false) (sym i≡0) (0<ᵇn≡false e)
    stage≡Faded : CoherentStage cp ≡ Faded
    stage≡Faded =
      begin
        CoherentStage cp
          ≡⟨ refl ⟩
        (if e <ᵇ i then Alive else if (i ≡ᵇ 0) then Faded else Broken)
          ≡⟨ cong (λ b → if b then Alive else if (i ≡ᵇ 0) then Faded else Broken) b1≡false ⟩
        (if (i ≡ᵇ 0) then Faded else Broken)
          ≡⟨ cong (λ b → if b then Faded else Broken) b2≡true ⟩
        Faded
      ∎
    contradiction : Faded ≡ Broken
    contradiction = trans (sym stage≡Faded) broken
  in ⊥-elim (Faded≢Broken contradiction)
broken-internal-non-increasing : ∀ {ℓ} {O : Set ℓ} {env : O → ℕ}
                               → (cp : CoherentPattern O (⊤ {ℓ}))
                               → CoherentStage cp ≡ Broken
                               → next-internal env cp ≤ internal cp
broken-internal-non-increasing {env = env} cp broken =
  let
    ¬i>e = broken→¬i>e cp broken
    ¬i≡0 = broken→¬i≡0 cp broken
    i = internal cp
    i>0 = ¬zero→suc ¬i≡0
    i≤e = ≮⇒≥-poly ¬i>e
    gain-zero = lemma-positive-i-le-e-feedback-zero i>0 i≤e
    eq : next-internal env cp ≡ i
    eq = trans (cong (i +_) gain-zero) (+-identityʳ i)
  in subst (λ x → x ≤ i) (sym eq) ≤-refl

-- Stream combinators and ⊤-tensor product
-- 流组合子与 ⊤-张量积
zipWith : ∀ {ℓ₁ ℓ₂ ℓ₃} {A : Set ℓ₁} {B : Set ℓ₂} {C : Set ℓ₃}
        → (A → B → C) → Stream A → Stream B → Stream C
zipWith f s1 s2 .Stream.head = f (Stream.head s1) (Stream.head s2)
zipWith f s1 s2 .Stream.tail = zipWith f (Stream.tail s1) (Stream.tail s2)
private
  simplify-stream : ∀ {ℓO ℓ₁ ℓ₂} {O : Set ℓO} 
                   → Stream {ℓ = ℓO ⊔ ℓ₁ ⊔ ℓ₂} (O × (⊤ {ℓ₁} × ⊤ {ℓ₂})) 
                   → Stream {ℓ = ℓO ⊔ ℓ₁ ⊔ ℓ₂} (O × ⊤ {ℓ₁ ⊔ ℓ₂})
  simplify-stream s .Stream.head = (proj₁ (Stream.head s) , tt)
  simplify-stream s .Stream.tail = simplify-stream (Stream.tail s)
  simplify-essence-always : ∀ {ℓO ℓ₁ ℓ₂} {O : Set ℓO} 
                           (s : Stream {ℓ = ℓO ⊔ ℓ₁ ⊔ ℓ₂} (O × (⊤ {ℓ₁} × ⊤ {ℓ₂})))
                           → Always {ℓ = ℓO ⊔ ℓ₁ ⊔ ℓ₂} {ℓ' = ℓ₁ ⊔ ℓ₂} 
                               (λ x → proj₂ x ≡ (tt {ℓ₁} , tt {ℓ₂})) s
                           → Always {ℓ = ℓO ⊔ ℓ₁ ⊔ ℓ₂} {ℓ' = ℓ₁ ⊔ ℓ₂} 
                               (λ x → proj₂ x ≡ tt {ℓ₁ ⊔ ℓ₂}) 
                               (simplify-stream {ℓO = ℓO} {ℓ₁ = ℓ₁} {ℓ₂ = ℓ₂} s)
  simplify-essence-always s alw .Always.head = refl
  simplify-essence-always s alw .Always.tail =
    simplify-essence-always (Stream.tail s) (Always.tail alw)
simplify-essence : ∀ {ℓO ℓ₁ ℓ₂} {O : Set ℓO} 
                  → Process O (⊤ {ℓ₁} × ⊤ {ℓ₂}) 
                  → Process O (⊤ {ℓ₁ ⊔ ℓ₂})
simplify-essence p = mkProc (o p) tt
  (simplify-stream (stream p))
  (simplify-essence-always (stream p) (essence-const p))
  (init-consistent p)

infixl 6 _⊗⊤_
_⊗⊤_ : ∀ {ℓO₁ ℓ₁ ℓO₂ ℓ₂} {O₁ : Set ℓO₁} {O₂ : Set ℓO₂}
     → Process O₁ (⊤ {ℓ₁}) → Process O₂ (⊤ {ℓ₂}) → Process (O₁ × O₂) (⊤ {ℓ₁ ⊔ ℓ₂})
_⊗⊤_ p1 p2 = simplify-essence (p1 ⊗ p2)

-- Tensor product composition of coherent patterns
-- 相干模式的张量积复合
infixl 6 _⊗coh_
_⊗coh_ : ∀ {ℓ₁ ℓ₂} {O₁ : Set ℓ₁} {O₂ : Set ℓ₂}
       → CoherentPattern O₁ (⊤ {ℓ₁}) → CoherentPattern O₂ (⊤ {ℓ₂}) → CoherentPattern (O₁ × O₂) (⊤ {ℓ₁ ⊔ ℓ₂})
_⊗coh_ {ℓ₁ = ℓ₁} {ℓ₂ = ℓ₂} cp₁ cp₂ = mkPattern
  (base cp₁ ⊗⊤ base cp₂)
  (internal cp₁ + internal cp₂)
  (external cp₁ + external cp₂)
⊗⊤-next-comm : ∀ {ℓ₁ ℓ₂} {O₁ : Set ℓ₁} {O₂ : Set ℓ₂}
             (p1 : Process O₁ (⊤ {ℓ₁})) (p2 : Process O₂ (⊤ {ℓ₂}))
             → next (p1) ⊗⊤ next (p2) ≡ next (p1 ⊗⊤ p2)
⊗⊤-next-comm p1 p2 = refl

-- Composition preserves coherence and dynamic consistency
-- 复合保持相干性与动态一致性
⊗coh-preserves-coherence : ∀ {ℓ₁ ℓ₂} {O₁ : Set ℓ₁} {O₂ : Set ℓ₂}
                         (cp₁ : CoherentPattern O₁ (⊤ {ℓ₁})) (cp₂ : CoherentPattern O₂ (⊤ {ℓ₂}))
                         → is-coherent cp₁ → is-coherent cp₂ → is-coherent (cp₁ ⊗coh cp₂)
⊗coh-preserves-coherence cp₁ cp₂ i1>e1 i2>e2 = +-mono-< i1>e1 i2>e2
⊗coh-preserves-always-coherent : ∀ {ℓ₁ ℓ₂} {O₁ : Set ℓ₁} {O₂ : Set ℓ₂}
                               (s₁ : Stream (CoherentPattern O₁ ⊤)) (s₂ : Stream (CoherentPattern O₂ ⊤))
                               → AlwaysCoherent s₁ → AlwaysCoherent s₂
                               → AlwaysCoherent (zipWith _⊗coh_ s₁ s₂)
⊗coh-preserves-always-coherent s₁ s₂ coh₁ coh₂ .Always.head =
  ⊗coh-preserves-coherence (Stream.head s₁) (Stream.head s₂) (coh₁ .Always.head) (coh₂ .Always.head)
⊗coh-preserves-always-coherent s₁ s₂ coh₁ coh₂ .Always.tail =
  ⊗coh-preserves-always-coherent (Stream.tail s₁) (Stream.tail s₂) (coh₁ .Always.tail) (coh₂ .Always.tail)
⊗coh-preserves-dynamic : ∀ {ℓ₁ ℓ₂} {O₁ : Set ℓ₁} {O₂ : Set ℓ₂}
                       (env₁ : O₁ → ℕ) (env₂ : O₂ → ℕ)
                       (s₁ : Stream (CoherentPattern O₁ (⊤ {ℓ₁}))) (s₂ : Stream (CoherentPattern O₂ (⊤ {ℓ₂})))
                       → DynamicCoherent env₁ s₁ → DynamicCoherent env₂ s₂
                       → AlwaysCoherent s₁ → AlwaysCoherent s₂
                       → DynamicCoherent (λ (o1 , o2) → env₁ o1 + env₂ o2) (zipWith _⊗coh_ s₁ s₂)
⊗coh-preserves-dynamic env₁ env₂ s₁ s₂ dyn₁ dyn₂ coh₁ coh₂ .internal-step =
  let
    left-eq = refl
    dyn1-eq = dyn₁ .internal-step
    dyn2-eq = dyn₂ .internal-step
    left-final = trans left-eq (cong₂ _+_ dyn1-eq dyn2-eq)
    cp1 = Stream.head s₁; cp2 = Stream.head s₂
    i1 = internal cp1; e1 = external cp1
    i2 = internal cp2; e2 = external cp2
    coh1 = coh₁ .Always.head; coh2 = coh₂ .Always.head
    g1 = feedback-gain i1 e1; g2 = feedback-gain i2 e2; g12 = feedback-gain (i1 + i2) (e1 + e2)
    p : g1 + g2 ≡ g12
    p = feedback-gain-additive-coherent coh1 coh2
    next1 = next-internal env₁ cp1; next2 = next-internal env₂ cp2
    next12 = next-internal (λ (o1 , o2) → env₁ o1 + env₂ o2) (cp1 ⊗coh cp2)
    right-eq : next1 + next2 ≡ next12
    right-eq =
      begin
        (i1 + g1) + (i2 + g2)
          ≡⟨ +-four-rearrange i1 g1 i2 g2 ⟩
        (i1 + i2) + (g1 + g2)
          ≡⟨ cong ((i1 + i2) +_) p ⟩
        (i1 + i2) + g12
      ∎
  in trans left-final right-eq
⊗coh-preserves-dynamic env₁ env₂ s₁ s₂ dyn₁ dyn₂ coh₁ coh₂ .external-step =
  cong₂ _+_ (dyn₁ .external-step) (dyn₂ .external-step)
⊗coh-preserves-dynamic env₁ env₂ s₁ s₂ dyn₁ dyn₂ coh₁ coh₂ .process-step =
  cong₂ _⊗⊤_ (dyn₁ .process-step) (dyn₂ .process-step)
⊗coh-preserves-dynamic env₁ env₂ s₁ s₂ dyn₁ dyn₂ coh₁ coh₂ .tail-ok =
  ⊗coh-preserves-dynamic env₁ env₂ (Stream.tail s₁) (Stream.tail s₂)
    (dyn₁ .tail-ok) (dyn₂ .tail-ok) (coh₁ .Always.tail) (coh₂ .Always.tail)

-- Bridge: Reduction of coherent patterns to processes
-- 桥梁：相干模式还原为过程
coherent-to-process : ∀ {ℓ₁ ℓ₂} {O : Set ℓ₁} {C : Set ℓ₂} → CoherentPattern O C → Process O C
coherent-to-process = base
coherent-core-conservation : ∀ {ℓ₁ ℓ₂} {O : Set ℓ₁} {C : Set ℓ₂} (cp : CoherentPattern O C)
                          → core (coherent-to-process cp) ≡ c (base cp)
coherent-core-conservation cp = refl

-- DynamicCoherent preservation and stepping lemmas
-- DynamicCoherent 保持性与步进引理
next-preserves-dynamic : ∀ {ℓ} {O : Set ℓ} {env : O → ℕ} {s : Stream (CoherentPattern O ⊤)}
                         → DynamicCoherent env s → DynamicCoherent env (Stream.tail s)
next-preserves-dynamic dyn = dyn .tail-ok
⊗-preserves-dynamic : ∀ {ℓ₁ ℓ₂} {O₁ : Set ℓ₁} {O₂ : Set ℓ₂}
                      {env₁ : O₁ → ℕ} {env₂ : O₂ → ℕ}
                      {s₁ : Stream (CoherentPattern O₁ ⊤)} {s₂ : Stream (CoherentPattern O₂ ⊤)}
                      → DynamicCoherent env₁ s₁ → DynamicCoherent env₂ s₂
                      → AlwaysCoherent s₁ → AlwaysCoherent s₂
                      → DynamicCoherent (λ (o1 , o2) → env₁ o1 + env₂ o2) (zipWith _⊗coh_ s₁ s₂)
⊗-preserves-dynamic {env₁ = env₁} {env₂ = env₂} {s₁ = s₁} {s₂ = s₂} dyn1 dyn2 coh1 coh2 =
  ⊗coh-preserves-dynamic env₁ env₂ s₁ s₂ dyn1 dyn2 coh1 coh2
dynamic-implies-steps : ∀ {ℓ} {O : Set ℓ} {env : O → ℕ} {s : Stream (CoherentPattern O ⊤)}
                        → DynamicCoherent env s
                        → (∀ n → (Stream.head (stream-tail-n (Stream.tail s) n)) .internal ≡
                               next-internal env (Stream.head (stream-tail-n s n)))
                        ×
                        (∀ n → (Stream.head (stream-tail-n (Stream.tail s) n)) .external ≡
                               env (observe ((Stream.head (stream-tail-n (Stream.tail s) n)) .base) 0))
dynamic-implies-steps {ℓ = ℓ} {O = O} {env = env} {s = s} dyn =
  ( go-internal s dyn
  , go-external s dyn
  )
  where
    go-internal : ∀ (s' : Stream (CoherentPattern O ⊤)) (dyn' : DynamicCoherent env s') n →
                  (Stream.head (stream-tail-n (Stream.tail s') n)) .internal ≡
                  next-internal env (Stream.head (stream-tail-n s' n))
    go-internal s' dyn' zero    = dyn' .internal-step
    go-internal s' dyn' (suc n) = go-internal (Stream.tail s') (dyn' .tail-ok) n
    go-external : ∀ (s' : Stream (CoherentPattern O ⊤)) (dyn' : DynamicCoherent env s') n →
                  (Stream.head (stream-tail-n (Stream.tail s') n)) .external ≡
                  env (observe ((Stream.head (stream-tail-n (Stream.tail s') n)) .base) 0)
    go-external s' dyn' zero    = dyn' .external-step
    go-external s' dyn' (suc n) = go-external (Stream.tail s') (dyn' .tail-ok) n

-- AlwaysCoherent preservation lemmas
-- AlwaysCoherent 保持性引理
next-preserves-always-coherent : ∀ {ℓ} {O : Set ℓ} {s : Stream (CoherentPattern O ⊤)}
                                 → AlwaysCoherent s → AlwaysCoherent (Stream.tail s)
next-preserves-always-coherent alw = alw .Always.tail
⊗-preserves-always-coherent : ∀ {ℓ₁ ℓ₂} {O₁ : Set ℓ₁} {O₂ : Set ℓ₂}
                              {s₁ : Stream (CoherentPattern O₁ ⊤)} {s₂ : Stream (CoherentPattern O₂ ⊤)}
                              → AlwaysCoherent s₁ → AlwaysCoherent s₂
                              → AlwaysCoherent (zipWith _⊗coh_ s₁ s₂)
⊗-preserves-always-coherent {s₁ = s₁} {s₂ = s₂} = ⊗coh-preserves-always-coherent s₁ s₂
always-coherent-implies-all : ∀ {ℓ} {O : Set ℓ} {s : Stream (CoherentPattern O ⊤)}
                              → AlwaysCoherent s → ∀ n → is-coherent (Stream.head (stream-tail-n s n))
always-coherent-implies-all alw n = always-implies-all-n alw n
