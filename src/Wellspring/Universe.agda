{-
An attempt to encode the arguments of the paper into Agda code,
before the philosophical thought of the paper fully converges
upon Cosmos as a new mathematical structure.

Retained to reflect the thinking process from attempting to express
philosophical thought in Agda to ultimately converging upon Cosmos.

在论文的哲学思想完全收敛于 Cosmos 这一新的数学结构之前，
将论文各个论证写成 Agda 代码的尝试。
予以保留，以体现从尝试用 Agda 表达哲学思想
并最终收敛于 Cosmos 的思考过程。

Dynamic correlation from beings to the totality of beings; the relationship between finite perspectives and infinite essence
从存在者到存在者整体的动态关联性，有限视角与无限本质的关系
--
Universe structure, projection and non-reconstruction theorem, inevitability of non-uniformity theorem, interaction, coupling, and common essence
宇宙结构、投影与不可重构定理、非均匀性必然定理、交互、耦合与共同本质
-}
{-# OPTIONS --safe --cubical-compatible --exact-split --guardedness --double-check #-}

module Wellspring.Universe where

open import Wellspring.Beings public

-- Irreducibility and fundamental definition of the universe
-- 不可消减性与宇宙的基本定义
record IsIndestructible {ℓ₁ ℓ₂ ℓ₃} {I : Set ℓ₁} {A : Set ℓ₂} {C : Set ℓ₃}
                       (essence : C) (stream : Stream ((I → A) × C)) : Set (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃) where
  field
    essencePermanent : Always (λ x → proj₂ x ≡ essence) stream
open IsIndestructible public
record Universe {ℓ₁ ℓ₂ ℓ₃} (I : Set ℓ₁) (A : Set ℓ₂) (C : Set ℓ₃) : Set (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃) where
  constructor mkUniverse
  field
    essence : C
    stream  : Stream ((I → A) × C)
    indestruct : IsIndestructible essence stream
open Universe public

infix 4 _≈ᵁ_
record _≈ᵁ_ {ℓ₁ ℓ₂ ℓ₃} {I : Set ℓ₁} {A : Set ℓ₂} {C : Set ℓ₃}
            (u v : Universe I A C) : Set (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃) where
  field
    essence≈ : essence u ≡ essence v
    stream≈  : stream u ≈ stream v
open _≈ᵁ_ public

≈ᵁ-refl : ∀ {ℓ₁ ℓ₂ ℓ₃} {I : Set ℓ₁} {A : Set ℓ₂} {C : Set ℓ₃} {u : Universe I A C} → u ≈ᵁ u
≈ᵁ-refl = record { essence≈ = refl ; stream≈ = ≈-refl }

≈ᵁ-sym : ∀ {ℓ₁ ℓ₂ ℓ₃} {I : Set ℓ₁} {A : Set ℓ₂} {C : Set ℓ₃} {u v : Universe I A C} → u ≈ᵁ v → v ≈ᵁ u
≈ᵁ-sym eq = record { essence≈ = sym (essence≈ eq) ; stream≈ = ≈-sym (stream≈ eq) }

≈ᵁ-trans : ∀ {ℓ₁ ℓ₂ ℓ₃} {I : Set ℓ₁} {A : Set ℓ₂} {C : Set ℓ₃} {u v w : Universe I A C}
          → u ≈ᵁ v → v ≈ᵁ w → u ≈ᵁ w
≈ᵁ-trans eq1 eq2 = record
  { essence≈ = trans (essence≈ eq1) (essence≈ eq2)
  ; stream≈  = ≈-trans (stream≈ eq1) (stream≈ eq2)
  }

-- Observation: Extracting concrete accidents from the universe
-- 观察：从宇宙中提取具体偶性
module _ {ℓ₁ ℓ₂ ℓ₃} {I : Set ℓ₁} {A : Set ℓ₂} {C : Set ℓ₃} where
  observeAccident : Universe I A C → ℕ → I → A
  observeAccident u n i = proj₁ (Stream.head (stream-tail-n (stream u) n)) i
  univ-core : Universe I A C → C
  univ-core = essence
  cosmicStep : Universe I A C → Universe I A C
  cosmicStep u = record
    { essence = essence u
    ; stream = Stream.tail (stream u)
    ; indestruct = record { essencePermanent = Always.tail (essencePermanent (indestruct u)) }
    }
  cosmicStep-preserves-core : ∀ u → univ-core (cosmicStep u) ≡ univ-core u
  cosmicStep-preserves-core u = refl
  univ-essence-constant : ∀ u n → proj₂ (Stream.head (stream-tail-n (stream u) n)) ≡ univ-core u
  univ-essence-constant u n = always-implies-all-n (essencePermanent (indestruct u)) n
  univ-deterministic-observation : ∀ u n i → Σ A (λ a → observeAccident u n i ≡ a)
  univ-deterministic-observation u n i = observeAccident u n i , refl

-- Generic projection: From infinite indexing to finite indexing
-- 通用投影：从无限索引到有限索引
Selector : ℕ → Set
Selector n = Fin n → ℕ
proj-stream : ∀ {ℓ₁ ℓ₂} (A : Set ℓ₁) (C : Set ℓ₂) n
            → Stream ((ℕ → A) × C) → Selector n → Stream ((Fin n → A) × C)
proj-stream A C n s sel .Stream.head = (λ i → proj₁ (Stream.head s) (sel i)) , proj₂ (Stream.head s)
proj-stream A C n s sel .Stream.tail = proj-stream A C n (Stream.tail s) sel
private
  core-const : ∀ {ℓ₁ ℓ₂} (A : Set ℓ₁) (C : Set ℓ₂) n s sel (c : C)
             → Always (λ x → proj₂ x ≡ c) s
             → Always (λ x → proj₂ x ≡ c) (proj-stream A C n s sel)
  core-const A C n s sel c al .Always.head = al .Always.head
  core-const A C n s sel c al .Always.tail = core-const A C n (Stream.tail s) sel c (al .Always.tail)
projGeneric : ∀ {ℓ} n {C : Set ℓ} → Selector n → Universe ℕ ℕ C → Universe (Fin n) ℕ C
projGeneric n {C} sel cos = record
  { essence = univ-core cos
  ; stream = proj-stream ℕ C n (stream cos) sel
  ; indestruct = record
      { essencePermanent = core-const ℕ C n (stream cos) sel (univ-core cos)
                             (essencePermanent (indestruct cos)) }
  }
proj-preserves-core : ∀ {ℓ} n {C : Set ℓ} sel (cos : Universe ℕ ℕ C) →
                      essence (projGeneric n sel cos) ≡ univ-core cos
proj-preserves-core n sel cos = refl
module MergeSelectors (n m : ℕ) where
  merge : (Fin n → ℕ) → (Fin m → ℕ) → Fin (n + m) → ℕ
  merge sel₁ sel₂ i = [_,_] sel₁ sel₂ (splitAt n i)
  merge-preserves-core : ∀ {ℓ} {C : Set ℓ} (cos : Universe ℕ ℕ C) (sel₁ : Fin n → ℕ) (sel₂ : Fin m → ℕ) →
                         essence (projGeneric (n + m) (merge sel₁ sel₂) cos) ≡ univ-core cos
  merge-preserves-core cos sel₁ sel₂ = refl

-- Cosmos: The universe with a unique essence
-- Cosmos：唯一本质的宇宙
data Cosmos-C : Set where
  CosmicEssence : Cosmos-C
open Cosmos-C public
StreamCosmos : Set
StreamCosmos = Universe ℕ ℕ Cosmos-C
proj-stream-cosmos : ∀ n → Stream ((ℕ → ℕ) × Cosmos-C) → Selector n → Stream ((Fin n → ℕ) × Cosmos-C)
proj-stream-cosmos = proj-stream ℕ Cosmos-C
private
  core-const-cosmos : ∀ n s sel (c : Cosmos-C) → Always (λ x → proj₂ x ≡ c) s →
                      Always (λ x → proj₂ x ≡ c) (proj-stream-cosmos n s sel)
  core-const-cosmos = core-const ℕ Cosmos-C

-- Projection: Reducing the infinite universe to a finite perspective (G)
-- 投影：将无限宇宙降维到有限视角（G）
projCosmos : ∀ n → Selector n → StreamCosmos → Universe (Fin n) ℕ Cosmos-C
projCosmos n sel cos = record
  { essence = univ-core cos
  ; stream = proj-stream-cosmos n (stream cos) sel
  ; indestruct = record
      { essencePermanent = core-const-cosmos n (stream cos) sel (univ-core cos)
                             (essencePermanent (indestruct cos)) }
  }
cos-observe : StreamCosmos → ℕ → ℕ → ℕ
cos-observe = observeAccident {I = ℕ} {A = ℕ} {C = Cosmos-C}

infix 4 _≈ᶜ_
record _≈ᶜ_ (x y : StreamCosmos) : Set where
  field
    essence≈ : essence x ≡ essence y
    stream≈  : stream x ≈ stream y
open _≈ᶜ_ public

≈ᶜ-refl  : ∀ {x} → x ≈ᶜ x
≈ᶜ-refl = record { essence≈ = refl ; stream≈ = ≈-refl }

≈ᶜ-sym   : ∀ {x y} → x ≈ᶜ y → y ≈ᶜ x
≈ᶜ-sym eq = record { essence≈ = sym (essence≈ eq) ; stream≈ = ≈-sym (stream≈ eq) }

≈ᶜ-trans : ∀ {x y z} → x ≈ᶜ y → y ≈ᶜ z → x ≈ᶜ z
≈ᶜ-trans eq1 eq2 = record
  { essence≈ = trans (essence≈ eq1) (essence≈ eq2)
  ; stream≈  = ≈-trans (stream≈ eq1) (stream≈ eq2)
  }

cosmos-essence-unique : ∀ (cos1 cos2 : StreamCosmos) → essence cos1 ≡ essence cos2
cosmos-essence-unique cos1 cos2 with essence cos1 | essence cos2
... | CosmicEssence | CosmicEssence = refl
cosmos-initial : (ℕ → ℕ) → StreamCosmos
cosmos-initial o = record
  { essence = CosmicEssence
  ; stream = constStream (o , CosmicEssence)
  ; indestruct = record { essencePermanent = constStream-always-gen (o , CosmicEssence) refl }
  }

-- Embedding: Lifting from a finite perspective back to the universe (F)
-- 嵌入：从有限视角回升到宇宙（F）
private
  extend-fun : ∀ {n} → (Fin n → ℕ) → (ℕ → ℕ)
  extend-fun f i = maybe f 0 (toFin i)
  embedToCosmos : ∀ {n} → Stream ((Fin n → ℕ) × Cosmos-C) → Stream ((ℕ → ℕ) × Cosmos-C)
  embedToCosmos s .Stream.head = (extend-fun (proj₁ (Stream.head s))) , proj₂ (Stream.head s)
  embedToCosmos s .Stream.tail = embedToCosmos (Stream.tail s)
  extend-always : ∀ {n} {s : Stream ((Fin n → ℕ) × Cosmos-C)} {c : Cosmos-C}
                  → Always (λ x → proj₂ x ≡ c) s
                  → Always (λ x → proj₂ x ≡ c) (embedToCosmos s)
  extend-always alw .Always.head = alw .Always.head
  extend-always alw .Always.tail = extend-always (alw .Always.tail)

-- Observational equivalence relation (between finite universe streams)
-- 观察等价关系（有限宇宙流之间）
private
  infix 4 _≈obs_
  record _≈obs_ {n} (s t : Stream ((Fin n → ℕ) × Cosmos-C)) : Set where
    coinductive
    field
      head-obs-equiv : ∀ (i : Fin n) → 
        proj₁ (Stream.head s) i ≡ proj₁ (Stream.head t) i
      head-essence-equiv : proj₂ (Stream.head s) ≡ proj₂ (Stream.head t)
      tail-equiv : Stream.tail s ≈obs Stream.tail t
  open _≈obs_

  ≈obs-refl : ∀ {n} {s : Stream ((Fin n → ℕ) × Cosmos-C)} → s ≈obs s
  ≈obs-refl .head-obs-equiv i = refl
  ≈obs-refl .head-essence-equiv = refl
  ≈obs-refl .tail-equiv = ≈obs-refl

  ≈obs-sym : ∀ {n} {s t : Stream ((Fin n → ℕ) × Cosmos-C)} → s ≈obs t → t ≈obs s
  ≈obs-sym eq .head-obs-equiv i = sym (eq .head-obs-equiv i)
  ≈obs-sym eq .head-essence-equiv = sym (eq .head-essence-equiv)
  ≈obs-sym eq .tail-equiv = ≈obs-sym (eq .tail-equiv)

  trans-≈obs : ∀ {n} {s t u : Stream ((Fin n → ℕ) × Cosmos-C)} → s ≈obs t → t ≈obs u → s ≈obs u
  trans-≈obs eq1 eq2 .head-obs-equiv i = trans (eq1 .head-obs-equiv i) (eq2 .head-obs-equiv i)
  trans-≈obs eq1 eq2 .head-essence-equiv = trans (eq1 .head-essence-equiv) (eq2 .head-essence-equiv)
  trans-≈obs eq1 eq2 .tail-equiv = trans-≈obs (eq1 .tail-equiv) (eq2 .tail-equiv)

  -- Core lemma for the unit law: Embedding followed by re-projection yields an observation equivalent to the original finite stream
  -- 单位律的核心引理：嵌入再投影回来，观察等价于原有限流
  proj-extend-obs-equiv : ∀ {n} (s : Stream ((Fin n → ℕ) × Cosmos-C))
                         → proj-stream-cosmos n (embedToCosmos s) (λ i → toℕ i) ≈obs s
  proj-extend-obs-equiv {n} s = helper
    where
      helper : proj-stream-cosmos n (embedToCosmos s) (λ i → toℕ i) ≈obs s
      helper .head-obs-equiv i =
        trans refl
        (trans refl
        (trans (cong (maybe (proj₁ (Stream.head s)) 0) (toFin-toℕ i))
        refl))
      helper .head-essence-equiv = refl
      helper .tail-equiv = proj-extend-obs-equiv (Stream.tail s)
open _≈obs_ public

-- Embedding: Lifting a finite universe to an infinite universe (F)
-- 嵌入：将有限宇宙提升为无限宇宙（F）
universe-to-cosmos : ∀ {n} → Universe (Fin n) ℕ Cosmos-C → StreamCosmos
universe-to-cosmos u = record
  { essence    = essence u
  ; stream     = embedToCosmos (stream u)
  ; indestruct = record { essencePermanent = extend-always (essencePermanent (indestruct u)) }
  }

-- Functorial properties and unit laws
-- 函子性质与单位律
embedToCosmos-preserves-≈ : ∀ {n_len} {s t : Stream ((Fin n_len → ℕ) × Cosmos-C)}
                          → s ≈ t → embedToCosmos s ≈ embedToCosmos t
embedToCosmos-preserves-≈ eq ._≈_.head≈ = 
  cong₂ _,_ (cong extend-fun (cong proj₁ (eq ._≈_.head≈))) (cong proj₂ (eq ._≈_.head≈))
embedToCosmos-preserves-≈ eq ._≈_.tail≈ = embedToCosmos-preserves-≈ (eq ._≈_.tail≈)
proj-≈ᵁ : ∀ {n} (sel : Fin n → ℕ) {cos1 cos2 : StreamCosmos} → cos1 ≈ᶜ cos2 → projCosmos n sel cos1 ≈ᵁ projCosmos n sel cos2
proj-≈ᵁ {n} sel {cos1} {cos2} eq = record
  { essence≈ = trans (proj-preserves-core n sel cos1)
                     (trans (essence≈ eq)
                            (sym (proj-preserves-core n sel cos2)))
  ; stream≈ = proj-stream-≈ (stream≈ eq)
  }
  where
    proj-stream-≈ : {s1 s2 : Stream ((ℕ → ℕ) × Cosmos-C)} → s1 ≈ s2 →
                    proj-stream-cosmos n s1 sel ≈ proj-stream-cosmos n s2 sel
    proj-stream-≈ eq ._≈_.head≈ = cong (λ x → (λ i → proj₁ x (sel i)) , proj₂ x) (_≈_.head≈ eq)
    proj-stream-≈ eq ._≈_.tail≈ = proj-stream-≈ (_≈_.tail≈ eq)
≈ᵁ-implies-≈obs : ∀ {n} {u1 u2 : Universe (Fin n) ℕ Cosmos-C} → u1 ≈ᵁ u2 → stream u1 ≈obs stream u2
≈ᵁ-implies-≈obs {n} eq = helper {n} (eq .stream≈)
  where
    helper : ∀ {n} {s t : Stream ((Fin n → ℕ) × Cosmos-C)} → s ≈ t → s ≈obs t
    helper eq .head-obs-equiv i = cong (λ f → f i) (cong proj₁ (eq ._≈_.head≈))
    helper eq .head-essence-equiv = cong proj₂ (eq ._≈_.head≈)
    helper eq .tail-equiv = helper (eq ._≈_.tail≈)
proj-embed-unit : ∀ {n} (u : Universe (Fin n) ℕ Cosmos-C) →
                  stream (projCosmos n (λ i → toℕ i) (universe-to-cosmos u)) ≈obs stream u
proj-embed-unit u = proj-extend-obs-equiv (stream u)
universe-embedding-uniqueness :
  ∀ {n} (u1 u2 : Universe (Fin n) ℕ Cosmos-C)
  → stream u1 ≈obs stream u2
  → Σ StreamCosmos (λ cos → 
      (Σ (Fin n → ℕ) (λ sel1 → stream (projCosmos n sel1 cos) ≈obs stream u1)) 
      × 
      (Σ (Fin n → ℕ) (λ sel2 → stream (projCosmos n sel2 cos) ≈obs stream u2))
    )
universe-embedding-uniqueness {n} u1 u2 stream-obs =
  (cos , ((sel1 , bisim1) , (sel2 , bisim2)))
  where
    cos : StreamCosmos
    cos = universe-to-cosmos u1
    sel1 : Fin n → ℕ
    sel1 i = toℕ i
    sel2 : Fin n → ℕ
    sel2 i = toℕ i
    bisim1 : stream (projCosmos n sel1 cos) ≈obs stream u1
    bisim1 = proj-extend-obs-equiv (stream u1)
    bisim2 : stream (projCosmos n sel2 cos) ≈obs stream u2
    bisim2 = trans-≈obs (proj-extend-obs-equiv (stream u1)) stream-obs

-- Weak adjunction: Pointwise stream equivalence and weak counit
-- 弱伴随：逐点流等价与弱余单位
infix 4 _≈∞_
record _≈∞_ (s t : Stream ((ℕ → ℕ) × Cosmos-C)) : Set where
  coinductive
  field
    head-pointwise : ∀ (k : ℕ) → proj₁ (Stream.head s) k ≡ proj₁ (Stream.head t) k
    head-essence : proj₂ (Stream.head s) ≡ proj₂ (Stream.head t)
    tail-pointwise : Stream.tail s ≈∞ Stream.tail t
open _≈∞_ public

-- After projecting from infinity and re-embedding, consistency with the original infinite universe at all observable points (weak triangle identity)
-- 从无限投影再嵌入后，在一切可观察点上与原无限宇宙一致（弱三角恒等式）
triangle1-pointwise : ∀ {n_len} (u : Universe (Fin n_len) ℕ Cosmos-C)
                    → stream (universe-to-cosmos (projCosmos n_len (λ i → toℕ i) (universe-to-cosmos u)))
                    ≈∞ stream (universe-to-cosmos u)
triangle1-pointwise {n_len} u = helper
  where
    f : Fin n_len → ℕ
    f = proj₁ (Stream.head (stream u))
    general-lemma : ∀ (m : Maybe (Fin n_len))
                  → maybe (λ i → maybe f 0 (toFin (toℕ i))) 0 m
                  ≡ maybe f 0 m
    general-lemma nothing = refl
    general-lemma (just i) = cong (λ x → maybe f 0 x) (toFin-toℕ i)
    helper : stream (universe-to-cosmos (projCosmos n_len (λ i → toℕ i) (universe-to-cosmos u)))
           ≈∞ stream (universe-to-cosmos u)
    helper .head-pointwise k = general-lemma (toFin k)
    helper .head-essence = refl
    helper .tail-pointwise = triangle1-pointwise (cosmicStep u)

-- General Non-Reconstruction Theorem: For any finite dimension, finite observations cannot reconstruct a unique infinite universe
-- 通用不可重构定理：对任意有限维度，有限观察无法重构唯一无限宇宙
module GeneralNoReconstruction (n : ℕ) where
  obs-selector : Fin n → ℕ
  obs-selector i = toℕ i
  cosmic-view-1 cosmic-view-2 : ℕ → ℕ
  cosmic-view-1 _ = 0
  cosmic-view-2 k = if k <ᵇ n then 0 else 1
  cosmos-instance-1 : StreamCosmos
  cosmos-instance-1 = cosmos-initial cosmic-view-1
  cosmos-instance-2 : StreamCosmos
  cosmos-instance-2 = cosmos-initial cosmic-view-2
  finite-obs-equiv : stream (projCosmos n obs-selector cosmos-instance-1) ≈obs 
                     stream (projCosmos n obs-selector cosmos-instance-2)
  finite-obs-equiv .head-obs-equiv i =
    sym (cong (λ b → if b then 0 else 1) (<⇒<ᵇ-eq (toℕ<n i)))
  finite-obs-equiv .head-essence-equiv = refl
  finite-obs-equiv .tail-equiv = finite-obs-equiv
  ¬cosmos1≈cosmos2 : ¬ (cosmos-instance-1 ≈ᶜ cosmos-instance-2)
  ¬cosmos1≈cosmos2 eq = 0≢1 (trans (f-eq n) view2-n-eq1)
    where
      head≡ : Stream.head (stream cosmos-instance-1) ≡ Stream.head (stream cosmos-instance-2)
      head≡ = stream≈ eq ._≈_.head≈
      view≡ : cosmic-view-1 ≡ cosmic-view-2
      view≡ = cong proj₁ head≡
      f-eq : ∀ (x : ℕ) → cosmic-view-1 x ≡ cosmic-view-2 x
      f-eq x = cong (λ f → f x) view≡
      view2-n-eq1 : cosmic-view-2 n ≡ 1
      view2-n-eq1 rewrite <ᵇ-self-false n = refl
      0≢1 : 0 ≢ 1
      0≢1 ()
  general-no-reconstruction :
    ¬ ( Σ[ recover ∈ (Universe (Fin n) ℕ Cosmos-C → StreamCosmos) ]
        ( (∀ u v → stream u ≈obs stream v → recover u ≈ᶜ recover v) ×
          (∀ cos → recover (projCosmos n obs-selector cos) ≈ᶜ cos) ) )
  general-no-reconstruction (f , pres , prop) =
    ¬cosmos1≈cosmos2 (≈ᶜ-trans (≈ᶜ-sym (prop cosmos-instance-1))
                             (≈ᶜ-trans (pres _ _ finite-obs-equiv)
                                       (prop cosmos-instance-2)))

-- Homogeneity and change at the cosmic level
-- 宇宙层面的同质与变化
module CosmosLevel where
  WeakHom-Cosmos : StreamCosmos → Set
  WeakHom-Cosmos cos = ∀ n m i → cos-observe cos n i ≡ cos-observe cos m i
  Changes-Cosmos : StreamCosmos → Set
  Changes-Cosmos cos = ∃ λ n → ∃ λ i → cos-observe cos n i ≢ cos-observe cos (suc n) i
Generator : (O C : Set) → Set₁
Generator O C = Σ Set (λ S → S × (S → (O × C) × S))
genStream : ∀ {O C} → Generator O C → Stream (O × C)
genStream (S , init , step) = ana step init
WeakHomG : ∀ {O C} → Generator O C → Set
WeakHomG g = WeakHomS (genStream g)
ChangesG : ∀ {O C} → Generator O C → Set
ChangesG g = ChangesS (genStream g)
module _ {O C : Set} where
  const-output→WeakHomG : (S : Set) (init : S) (step : S → (O × C) × S)
    → (∀ s → proj₁ (step s) ≡ proj₁ (step init))
    → WeakHomG (S , init , step)
  const-output→WeakHomG S init step const-out = weak
    where
    o₀ = proj₁ (proj₁ (step init))
    lemma : (s : S) → ∀ n → proj₁ (head (stream-tail-n (ana step s) n)) ≡ o₀
    lemma s zero    = cong proj₁ (const-out s)
    lemma s (suc n) = lemma (proj₂ (step s)) n
    weak : WeakHomS (ana step init)
    weak n m = trans (lemma init n) (sym (lemma init m))
WeakHomCoind : ∀ {ℓ₁ ℓ₂} {O : Set ℓ₁} {C : Set ℓ₂} → Stream (O × C) → Set (ℓ₁ ⊔ ℓ₂)
WeakHomCoind s = s ≈ constStream (head s)
coind-const→all-heads : ∀ {ℓ₁ ℓ₂} {O : Set ℓ₁} {C : Set ℓ₂} {s : Stream (O × C)} {a : O × C}
                      → s ≈ constStream a
                      → ∀ n → head (stream-tail-n s n) ≡ a
coind-const→all-heads eq zero    = _≈_.head≈ eq
coind-const→all-heads eq (suc n) = coind-const→all-heads (_≈_.tail≈ eq) n
coind→pointwise : ∀ {ℓ₁ ℓ₂} {O : Set ℓ₁} {C : Set ℓ₂} (s : Stream (O × C)) → WeakHomCoind s
                → ∀ n → head (stream-tail-n s n) ≡ head s
coind→pointwise s coind = coind-const→all-heads coind
LocalChangeCosmos : ℕ → StreamCosmos → Set
LocalChangeCosmos d cos = ∃ λ n → ∃ λ m → cos-observe cos n d ≢ cos-observe cos m d
GlobalChangeCosmos : StreamCosmos → Set
GlobalChangeCosmos cos = ∀ d → LocalChangeCosmos d cos
FrequentChangeCosmos : StreamCosmos → Set
FrequentChangeCosmos cos =
  ∀ n → ∃ λ m → n ≤ m × (∃ λ d → cos-observe cos m d ≢ cos-observe cos (suc m) d)
PeriodicCosmos : ℕ → StreamCosmos → Set
PeriodicCosmos k cos = ∀ n i → cos-observe cos n i ≡ cos-observe cos (n + k) i
open CosmosLevel

weakHomCosmos→¬localChange : ∀ cos → WeakHom-Cosmos cos → ∀ d → ¬ LocalChangeCosmos d cos
weakHomCosmos→¬localChange cos w d (n , m , neq) = neq (w n m d)
HomS : ∀ {ℓ₁ ℓ₂} {O : Set ℓ₁} {C : Set ℓ₂} → Stream (O × C) → Set (ℓ₁ ⊔ ℓ₂)
HomS {O = O} {C = C} s = ∀ (t : Stream (O × C)) n m → obsS s n ≡ obsS t m
homS→weakHomS : ∀ {ℓ₁ ℓ₂} {O : Set ℓ₁} {C : Set ℓ₂} {s : Stream (O × C)} → HomS s → WeakHomS s
homS→weakHomS {s = s} hom n m = hom s n m
altGen : (C : Set) → C → Generator Bool C
altGen C c = Bool , true , step
  where
  step : Bool → (Bool × C) × Bool
  step b = ((b , c) , not b)
altGen-changes : ∀ {C} (c : C) → ChangesS (genStream (altGen _ c))
altGen-changes c = 0 , λ eq → true≢false eq
no-possible-hom : ∀ {C : Set} (c : C) → ¬ (∃ λ (g : Generator Bool C) → HomS (genStream g))
no-possible-hom {C} c (g , hom) =
  let
    altStream = genStream (altGen _ c)
    (n , neq) = altGen-changes c
    eq1 : obsS (genStream g) n ≡ obsS altStream n
    eq1 = hom altStream n n
    eq2 : obsS (genStream g) n ≡ obsS altStream (suc n)
    eq2 = hom altStream n (suc n)
    eq : obsS altStream n ≡ obsS altStream (suc n)
    eq = trans (sym eq1) eq2
  in ⊥-elim (neq eq)
WeakHom : ∀ {ℓ₁ ℓ₂} {O : Set ℓ₁} {C : Set ℓ₂} → Process O C → Set ℓ₁
WeakHom p = WeakHomS (stream p)
Changes : ∀ {ℓ₁ ℓ₂} {O : Set ℓ₁} {C : Set ℓ₂} → Process O C → Set ℓ₁
Changes p = ChangesS (stream p)
Δ : ∀ {ℓ₁ ℓ₂} {O : Set ℓ₁} {C : Set ℓ₂} → Process O C → Set ℓ₁
Δ p = ΔS (stream p)
lemma-WeakHom→¬Changes : ∀ {ℓ₁ ℓ₂} {O : Set ℓ₁} {C : Set ℓ₂} (p : Process O C) → WeakHom p → ¬ Changes p
lemma-WeakHom→¬Changes p weak (n , neq) = neq (weak n (suc n))
lemma-WeakHom→¬Boundary : ∀ {ℓ₁ ℓ₂} {O : Set ℓ₁} {C : Set ℓ₂} (p : Process O C) → WeakHom p → ¬ Δ p
lemma-WeakHom→¬Boundary p weak (n , m , neq) = neq (weak n m)
lemma-SelfSubstantial→¬WeakHom : ∀ {ℓ₁ ℓ₂} {O : Set ℓ₁} {C : Set ℓ₂} (p : Process O C) → Δ p → ¬ WeakHom p
lemma-SelfSubstantial→¬WeakHom p delta weak = lemma-WeakHom→¬Boundary p weak delta
StrongHom : ∀ {ℓ₁ ℓ₂} {O : Set ℓ₁} {C : Set ℓ₂} → Process O C → Set (ℓ₁ ⊔ ℓ₂)
StrongHom {O = O} {C = C} p = ∀ (q : Process O C) n m → observe p n ≡ observe q m
hom→weakHom : ∀ {ℓ₁ ℓ₂} {O : Set ℓ₁} {C : Set ℓ₂} (p : Process O C) → StrongHom p → WeakHom p
hom→weakHom p hom-p n m = hom-p p n m
thm-Hom→¬Changes : ∀ {ℓ₁ ℓ₂} {O : Set ℓ₁} {C : Set ℓ₂} (p : Process O C) → StrongHom p → ¬ Changes p
thm-Hom→¬Changes p hom = lemma-WeakHom→¬Changes p (hom→weakHom p hom)
thm-Hom→¬Boundary : ∀ {ℓ₁ ℓ₂} {O : Set ℓ₁} {C : Set ℓ₂} (p : Process O C) → StrongHom p → ¬ Δ p
thm-Hom→¬Boundary p hom = lemma-WeakHom→¬Boundary p (hom→weakHom p hom)
thm-no-Hom-if-any-change :
  ∀ {ℓ₁ ℓ₂} {O : Set ℓ₁} {C : Set ℓ₂} (FB : Process O C) → Changes FB → ¬ (∃ λ (p : Process O C) → StrongHom p)
thm-no-Hom-if-any-change FB (n , neq) (p , hom-p) =
  ⊥-elim (neq (trans (sym (hom-p FB n n)) (hom-p FB n (suc n))))

-- Inevitability of non-uniformity: As long as there exists a changing process, there can be no absolutely homogeneous observer
-- 非均匀性必然：只要存在一个变化过程，就没有绝对同质的观察者
nonuniformity-inevitable :
  ∀ {ℓ₁ ℓ₂} {O : Set ℓ₁} {C : Set ℓ₂} (FB : Process O C) → Changes FB → (∀ p → ¬ StrongHom p)
nonuniformity-inevitable FB changes p hom-p =
  thm-no-Hom-if-any-change FB changes (p , hom-p)
module WithFact
  {ℓ₁ ℓ₂} {O : Set ℓ₁} {C : Set ℓ₂}
  (FB : Process O C)
  (fact-FB-changes : Changes FB)
  where
  concrete-nonuniformity : ∀ p → ¬ StrongHom p
  concrete-nonuniformity = nonuniformity-inevitable FB fact-FB-changes
lemma-Hom-Cosmos→¬Changes-Cosmos : (cos : StreamCosmos) → WeakHom-Cosmos cos → ¬ Changes-Cosmos cos
lemma-Hom-Cosmos→¬Changes-Cosmos cos hom (n , i , neq) = neq (hom n (suc n) i)

-- Ontological interaction: Process composition preserving the same essence
-- 本体论交互：过程组合并保持同一本质
module Ontological where
  transform : ∀ {O₁ O₂ C : Set} → ((O₁ × O₂) × (C × C)) → ((O₁ × O₂) × C)
  transform ((o12 , (c1 , c2))) = (o12 , c1)
  interact : ∀ {O₁ O₂ C : Set}
    → Process O₁ C
    → Process O₂ C
    → Process (O₁ × O₂) C
  interact {O₁} {O₂} {C} p1 p2 =
    mkProc
      (o p1 , o p2)
      (core p1)
      (map-stream transform (merge-stream (stream p1) (stream p2)))
      transformed-essence-const
      transformed-init-consistent
    where
      transformed-essence-const : Always (λ x → proj₂ x ≡ core p1) 
                                       (map-stream transform (merge-stream (stream p1) (stream p2)))
      transformed-essence-const = helper (stream p1) (stream p2) (essence-const p1)
        where
          helper : ∀ (s1 : Stream (O₁ × C)) (s2 : Stream (O₂ × C))
                 → Always (λ x → proj₂ x ≡ core p1) s1
                 → Always (λ x → proj₂ x ≡ core p1) (map-stream transform (merge-stream s1 s2))
          helper s1 s2 alw1 .Always.head =
            begin
              proj₂ (transform (head (merge-stream s1 s2)))
                ≡⟨ refl ⟩
              proj₂ (head s1)
                ≡⟨ Always.head alw1 ⟩
              core p1
            ∎
          helper s1 s2 alw1 .Always.tail =
            helper (tail s1) (tail s2) (Always.tail alw1)
      transformed-init-consistent : proj₁ (head (map-stream transform (merge-stream (stream p1) (stream p2)))) 
                                    ≡ (o p1 , o p2)
      transformed-init-consistent =
        begin
          proj₁ (transform (head (merge-stream (stream p1) (stream p2))))
            ≡⟨ refl ⟩
          (proj₁ (head (stream p1)) , proj₁ (head (stream p2)))
            ≡⟨ cong₂ _,_ (init-consistent p1) (init-consistent p2) ⟩
          (o p1 , o p2)
        ∎
  core-interact : ∀ {O₁ O₂ C : Set}
    (p1 : Process O₁ C)
    (p2 : Process O₂ C)
    → core (interact p1 p2) ≡ core p1
  core-interact p1 p2 = refl
  core-interact-sym : ∀ {O₁ O₂ C : Set}
    (p1 : Process O₁ C)
    (p2 : Process O₂ C)
    → core p1 ≡ core p2
    → core (interact p1 p2) ≡ core p2
  core-interact-sym p1 p2 eq = trans (core-interact p1 p2) eq
  observe-interact : ∀ {O₁ O₂ C : Set}
    (p1 : Process O₁ C)
    (p2 : Process O₂ C)
    → ∀ n → observe (interact p1 p2) n ≡ (observe p1 n , observe p2 n)
  observe-interact p1 p2 n =
    begin
      observe (interact p1 p2) n
        ≡⟨ refl ⟩
      proj₁ (head (stream-tail-n (map-stream transform (merge-stream (stream p1) (stream p2))) n))
        ≡⟨ cong proj₁ (map-stream-tail-n transform (merge-stream (stream p1) (stream p2)) n) ⟩
      proj₁ (transform (head (stream-tail-n (merge-stream (stream p1) (stream p2)) n)))
        ≡⟨ refl ⟩
      proj₁ (head (stream-tail-n (merge-stream (stream p1) (stream p2)) n))
        ≡⟨ merge-stream-observe (stream p1) (stream p2) n ⟩
      (proj₁ (head (stream-tail-n (stream p1) n)), proj₁ (head (stream-tail-n (stream p2) n)))
        ≡⟨ refl ⟩
      (observe p1 n , observe p2 n)
    ∎

-- Epistemic coupling: Abstract specification of interaction, essence conservation, and dual observation
-- 认识论耦合：交互的抽象规格，本质守恒与对偶观察
module Epistemic where
  open Ontological public
  Coupling : {O₁ O₂ C : Set} → Set
  Coupling {O₁} {O₂} {C} =
    (p1 : Process O₁ C)
    (p2 : Process O₂ C)
    → Σ (Process (O₁ × O₂) C)
        (λ p' → (core p' ≡ core p1)
              × (∀ n → observe p' n ≡ (observe p1 n , observe p2 n)))
  canonical-coupling : {O₁ O₂ C : Set} → Coupling {O₁} {O₂} {C}
  canonical-coupling p1 p2 =
    interact p1 p2 , core-interact p1 p2 , observe-interact p1 p2
  interact-with : {O₁ O₂ C : Set}
                → Coupling {O₁} {O₂} {C}
                → Process O₁ C
                → Process O₂ C
                → Process (O₁ × O₂) C
  interact-with coupling p1 p2 = proj₁ (coupling p1 p2)
  core-interact-epistemic : {O₁ O₂ C : Set}
                           → (coupling : Coupling {O₁} {O₂} {C})
                           → (p1 : Process O₁ C)
                           → (p2 : Process O₂ C)
                           → core (interact-with coupling p1 p2) ≡ core p1
  core-interact-epistemic coupling p1 p2 = proj₁ (proj₂ (coupling p1 p2))
  observe-interact-epistemic : {O₁ O₂ C : Set}
                               → (coupling : Coupling {O₁} {O₂} {C})
                               → (p1 : Process O₁ C)
                               → (p2 : Process O₂ C)
                               → ∀ n → observe (interact-with coupling p1 p2) n
                                      ≡ (observe p1 n , observe p2 n)
  observe-interact-epistemic coupling p1 p2 n = proj₂ (proj₂ (coupling p1 p2)) n
open Ontological public
open Epistemic public

-- Lemmas for the interact combinator
-- interact 组合子的引理
interact-functor₁ : ∀ {O₁ O₂ C} {p₁ p₁' : Process O₁ C} {p₂ : Process O₂ C} →
                    p₁ ≈ₚ p₁' → interact p₁ p₂ ≈ₚ interact p₁' p₂
interact-functor₁ {p₁ = p₁} {p₁'} {p₂} p₁≈p₁' = helper (stream p₁) (stream p₁') (stream p₂) p₁≈p₁'
  where
    helper : ∀ {O₁ O₂ C} (s₁ s₁' : Stream (O₁ × C)) (s₂ : Stream (O₂ × C)) →
             s₁ ≈ s₁' → map-stream transform (merge-stream s₁ s₂) ≈ map-stream transform (merge-stream s₁' s₂)
    helper s₁ s₁' s₂ eq ._≈_.head≈ = cong transform (cong (λ x → merge-state x (Stream.head s₂)) (_≈_.head≈ eq))
    helper s₁ s₁' s₂ eq ._≈_.tail≈ = helper (Stream.tail s₁) (Stream.tail s₁') (Stream.tail s₂) (_≈_.tail≈ eq)
interact-functor₂ : ∀ {O₁ O₂ C} {p₁ : Process O₁ C} {p₂ p₂' : Process O₂ C} →
                    p₂ ≈ₚ p₂' → interact p₁ p₂ ≈ₚ interact p₁ p₂'
interact-functor₂ {p₁ = p₁} {p₂} {p₂'} p₂≈p₂' = helper (stream p₁) (stream p₂) (stream p₂') p₂≈p₂'
  where
    helper : ∀ {O₁ O₂ C} (s₁ : Stream (O₁ × C)) (s₂ s₂' : Stream (O₂ × C)) →
             s₂ ≈ s₂' → map-stream transform (merge-stream s₁ s₂) ≈ map-stream transform (merge-stream s₁ s₂')
    helper s₁ s₂ s₂' eq ._≈_.head≈ = cong transform (cong (merge-state (Stream.head s₁)) (_≈_.head≈ eq))
    helper s₁ s₂ s₂' eq ._≈_.tail≈ = helper (Stream.tail s₁) (Stream.tail s₂) (Stream.tail s₂') (_≈_.tail≈ eq)
interact-functor : ∀ {O₁ O₂ C} {p₁ p₁' : Process O₁ C} {p₂ p₂' : Process O₂ C} →
                   p₁ ≈ₚ p₁' → p₂ ≈ₚ p₂' → interact p₁ p₂ ≈ₚ interact p₁' p₂'
interact-functor {O₁} {O₂} {C} {p₁} {p₁'} {p₂} {p₂'} eq1 eq2 =
  helper {O₁} {O₂} {C} (stream p₁) (stream p₁') (stream p₂) (stream p₂') eq1 eq2
  where
    helper : ∀ {O₁ O₂ C} (s₁ s₁' : Stream (O₁ × C)) (s₂ s₂' : Stream (O₂ × C)) →
             s₁ ≈ s₁' → s₂ ≈ s₂' →
             map-stream transform (merge-stream s₁ s₂) ≈ map-stream transform (merge-stream s₁' s₂')
    helper s₁ s₁' s₂ s₂' eq1 eq2 ._≈_.head≈ =
      cong transform (cong₂ merge-state (_≈_.head≈ eq1) (_≈_.head≈ eq2))
    helper s₁ s₁' s₂ s₂' eq1 eq2 ._≈_.tail≈ =
      helper (Stream.tail s₁) (Stream.tail s₁') (Stream.tail s₂) (Stream.tail s₂')
             (_≈_.tail≈ eq1) (_≈_.tail≈ eq2)
interact-core-comm : ∀ {O₁ O₂ C} (p₁ : Process O₁ C) (p₂ : Process O₂ C) →
                     core (interact p₁ p₂) ≡ core p₁
interact-core-comm = core-interact
interact-next-comm : ∀ {O₁ O₂ C} (p₁ : Process O₁ C) (p₂ : Process O₂ C) →
                     next (interact p₁ p₂) ≈ₚ interact (next p₁) (next p₂)
interact-next-comm p₁ p₂ = helper (stream p₁) (stream p₂)
  where
    helper : ∀ {O₁ O₂ C} (s₁ : Stream (O₁ × C)) (s₂ : Stream (O₂ × C)) →
             Stream.tail (map-stream transform (merge-stream s₁ s₂)) ≈
             map-stream transform (merge-stream (Stream.tail s₁) (Stream.tail s₂))
    helper s₁ s₂ ._≈_.head≈ = refl
    helper s₁ s₂ ._≈_.tail≈ = helper (Stream.tail s₁) (Stream.tail s₂)
interact-observe-comm : ∀ {O₁ O₂ C} (p₁ : Process O₁ C) (p₂ : Process O₂ C) (n : ℕ) →
                        observe (interact p₁ p₂) n ≡ (observe p₁ n , observe p₂ n)
interact-observe-comm = observe-interact

-- Algebraic lemmas for interact
-- interact 的代数引理
assoc-interact-O : ∀ {O₁ O₂ O₃ : Set} → ((O₁ × O₂) × O₃) → (O₁ × (O₂ × O₃))
assoc-interact-O ((o₁ , o₂) , o₃) = (o₁ , (o₂ , o₃))
interact-assoc : ∀ {O₁ O₂ O₃ C}
                 (p₁ : Process O₁ C) (p₂ : Process O₂ C) (p₃ : Process O₃ C) →
                 ≈ₚ-hetero (interact (interact p₁ p₂) p₃)
                           (interact p₁ (interact p₂ p₃))
                           assoc-interact-O id
interact-assoc p₁ p₂ p₃ = record { stream≈ = helper (stream p₁) (stream p₂) (stream p₃) }
  where
    helper : ∀ {O₁ O₂ O₃ C} (s₁ : Stream (O₁ × C)) (s₂ : Stream (O₂ × C)) (s₃ : Stream (O₃ × C)) →
             ≈-hetero (map-stream transform (merge-stream (map-stream transform (merge-stream s₁ s₂)) s₃))
                      (map-stream transform (merge-stream s₁ (map-stream transform (merge-stream s₂ s₃))))
                      (comb assoc-interact-O id)
    helper s₁ s₂ s₃ .head≈ = refl
    helper s₁ s₂ s₃ .tail≈ = helper (Stream.tail s₁) (Stream.tail s₂) (Stream.tail s₃)
interact-comm : ∀ {O₁ O₂ C} (p₁ : Process O₁ C) (p₂ : Process O₂ C) →
                core p₁ ≡ core p₂ →
                ≈ₚ-hetero (interact p₁ p₂) (interact p₂ p₁) swap-O id
interact-comm {O₁} {O₂} {C} p₁ p₂ eq =
  record { stream≈ = helper (stream p₁) (stream p₂) (essence-const p₁) (essence-const p₂) }
  where
    helper : (s₁ : Stream (O₁ × C)) (s₂ : Stream (O₂ × C)) →
             Always (λ x → proj₂ x ≡ core p₁) s₁ →
             Always (λ x → proj₂ x ≡ core p₂) s₂ →
             ≈-hetero (map-stream transform (merge-stream s₁ s₂))
                      (map-stream transform (merge-stream s₂ s₁))
                      (comb swap-O id)
    helper s₁ s₂ alw₁ alw₂ .head≈ =
      let c1≡c2 = trans (alw₁ .Always.head) (trans eq (sym (alw₂ .Always.head)))
      in cong₂ _,_ refl c1≡c2
    helper s₁ s₂ alw₁ alw₂ .tail≈ =
      helper (Stream.tail s₁) (Stream.tail s₂) (Always.tail alw₁) (Always.tail alw₂)
interact-from-⊗ : ∀ {O₁ O₂ C} (p₁ : Process O₁ C) (p₂ : Process O₂ C) →
                  ≈ₚ-hetero (p₁ ⊗ p₂) (interact p₁ p₂) id proj₁
interact-from-⊗ p₁ p₂ = record { stream≈ = helper (stream p₁) (stream p₂) }
  where
    helper : ∀ {O₁ O₂ C} (s₁ : Stream (O₁ × C)) (s₂ : Stream (O₂ × C)) →
             ≈-hetero (merge-stream s₁ s₂)
                      (map-stream transform (merge-stream s₁ s₂))
                      (comb id proj₁)
    helper s₁ s₂ .head≈ = refl
    helper s₁ s₂ .tail≈ = helper (Stream.tail s₁) (Stream.tail s₂)
