------------------------------------------------------------------------
-- Standard colimit of a forward ω-chain with propositional fibres
--
-- The propositional-fibre special case of the direct-limit construction:
-- each stage fibre is a plain set with propositional equality, and the
-- forward map need be neither injective nor surjective. A direct-limit
-- element is a stage-tagged fibre element, so comparing two threads
-- never compares across fibres, and no transport, K or function
-- extensionality is used. The general arbitrary-setoid, arbitrary-shape
-- colimit is the Σ-plus-equivalence-closure construction in
-- SameIndexColimitS, of which this is the propositional-fibre
-- specialisation. Collapsing the closure to propositional equality
-- remains independent of the flags.
--
-- 命题纤维前向 ω-链的标准余极限
--
-- 直接极限构造的命题纤维特例：每阶段纤维是带命题相等的普通集合，前向
-- 映射不必单射或满射。直接极限元素是带阶段标签的纤维元素，故比较两个
-- 线程从不跨纤维，且无传输、不用 K、不用函数外延性。一般任意 setoid、
-- 任意形状的余极限是 SameIndexColimitS 中的 Σ 加等价闭包构造，本模型
-- 即其在命题纤维上的特化。把闭包压成命题相等仍与开关独立。
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module ALMA.Cosmos.Carried.ChainColimitPropS where

open import Agda.Primitive using (Level; lsuc)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Nat.Base using (ℕ; zero; suc; _+_)
open import Data.Nat.Properties using (+-comm)
open import Relation.Binary.PropositionalEquality using
  (sym; cong; module ≡-Reasoning)
open ≡-Reasoning
open import ALMA.Base.MCorr using (M)
open import ALMA.Base.MCorrSetoid using (SysEq; EqOn; propEqOn; _≈Mˢ_)
open SysEq
open import ALMA.Cosmos.Carried.SameIndexCatS using
  (LabelSys; dsys; Idx⇒; idxi; compi; _≈i_; SameIndexCat; ≈i-refl; ≈i-sym
  ; ≈i-trans; ∘-resp-≈i; pointwise-i)

open import Categories.Category.Core using (Category)
open import Categories.Functor using (Functor)
open import ALMA.Cosmos.Carried.SeqColimitCat using (Chain⇒; ωCat; _∘ch_)
import ALMA.Cosmos.Carried.SeqColimitCat as SQC

module _ (d : ℕ → ℕ) {ℓ : Level} where

  ----------------------------------------------------------------------
  -- A growing chain
  --
  -- Stage label sets L m v and a forward map emb m. Stage setoids are
  -- propositional.
  --
  -- 增长链
  --
  -- 阶段标签集 L m v 与前向映射 emb m。阶段 setoid 为命题的。

  record ChainProp : Set (lsuc ℓ) where
    field
      L₀  : (m v : ℕ) → Set ℓ
      emb : (m v : ℕ) → L₀ m v → L₀ (suc m) v

  module Build (C : ChainProp) where

    open ChainProp C

    private
      s = d

    -- Stage label system with propositional fibre equality.
    --
    -- 命题纤维相等的阶段标签系统。
    stageLS : ℕ → LabelSys ℓ
    stageLS m = record { A₀ = L₀ m ; ≈A₀ = λ v → propEqOn (L₀ m v) }

    -- Forward identity-index arrow.
    --
    -- 前向索引恒等箭头。
    embIdx : (m : ℕ) → Idx⇒ s (stageLS m) (stageLS (suc m))
    embIdx m = record
      { shape      = λ v a → emb m v a
      ; shape-cong = λ {v} e → cong (emb m v) e
      }

    --------------------------------------------------------------------
    -- Direct-limit element
    --
    -- A stage-tagged fibre element.
    --
    -- 直接极限元素
    --
    -- 带阶段标签的纤维元素。
    record Thread (v : ℕ) : Set ℓ where
      inductive
      constructor mk
      field
        stage  : ℕ
        tlabel : L₀ stage v
    open Thread public

    -- One forward step at the fixed label v.
    --
    -- 固定标签 v 上的一步前向。
    extend : {v : ℕ} → Thread v → Thread v
    extend {v} (mk m a) = mk (suc m) (emb m v a)

    extend^ : {v : ℕ} → ℕ → Thread v → Thread v
    extend^ zero    t = t
    extend^ (suc n) t = extend (extend^ n t)

    -- Eventual coincidence: some forward iterates coincide as records.
    --
    -- 最终重合：某前向迭代作为记录重合。
    record _≈Thread_ {v : ℕ} (t u : Thread v) : Set ℓ where
      field
        dl   : ℕ
        dr   : ℕ
        same : extend^ dl t ≡ extend^ dr u
    open _≈Thread_

    extend^-comp : {v : ℕ} (a b : ℕ) (t : Thread v)
                 → extend^ a (extend^ b t) ≡ extend^ (a + b) t
    extend^-comp zero    b t = refl
    extend^-comp (suc a) b t = cong extend (extend^-comp a b t)

    iter-add-comm : {v : ℕ} (a b : ℕ) (t : Thread v)
                  → extend^ (a + b) t ≡ extend^ (b + a) t
    iter-add-comm a b t rewrite +-comm a b = refl

    ≈Thread-refl : {v : ℕ} {t : Thread v} → t ≈Thread t
    ≈Thread-refl = record { dl = zero ; dr = zero ; same = refl }

    ≈Thread-sym : {v : ℕ} {t u : Thread v} → t ≈Thread u → u ≈Thread t
    ≈Thread-sym p = record { dl = dr p ; dr = dl p ; same = sym (same p) }

    ≈Thread-trans : {v : ℕ} {t u w : Thread v}
                  → t ≈Thread u → u ≈Thread w → t ≈Thread w
    ≈Thread-trans {t = t} {u = u} {w = w} p q = record
      { dl = c + a
      ; dr = b + r
      ; same = begin
          extend^ (c + a) t
            ≡⟨ sym (extend^-comp c a t) ⟩
          extend^ c (extend^ a t)
            ≡⟨ cong (extend^ c) (same p) ⟩
          extend^ c (extend^ b u)
            ≡⟨ extend^-comp c b u ⟩
          extend^ (c + b) u
            ≡⟨ iter-add-comm c b u ⟩
          extend^ (b + c) u
            ≡⟨ sym (extend^-comp b c u) ⟩
          extend^ b (extend^ c u)
            ≡⟨ cong (extend^ b) (same q) ⟩
          extend^ b (extend^ r w)
            ≡⟨ extend^-comp b r w ⟩
          extend^ (b + r) w
          ∎
      }
      where
      a = dl p ; b = dr p ; c = dl q ; r = dr q

    ≈A∞ : (v : ℕ) → EqOn (Thread v)
    ≈A∞ v = record
      { _≈_ = _≈Thread_
      ; isEquivalence = record
        { refl  = ≈Thread-refl
        ; sym   = ≈Thread-sym
        ; trans = ≈Thread-trans
        }
      }

    -- Colimit apex label system.
    --
    -- 余极限顶点标签系统。
    apexLS : LabelSys ℓ
    apexLS = record { A₀ = Thread ; ≈A₀ = ≈A∞ }

    -- Injection: tag a stage element with its birth stage.
    --
    -- 注入：用诞生阶段标签化阶段元素。
    legIdx : (m : ℕ) → Idx⇒ s (stageLS m) apexLS
    legIdx m = record
      { shape      = λ v a → mk m a
      ; shape-cong = λ {v} {a} {a'} e →
          record { dl = zero ; dr = zero
                 ; same = cong (λ x → mk m x) e }
      }

    --------------------------------------------------------------------
    -- Chain as a functor ω → SameIndexCat
    --
    -- 链作为 ω → SameIndexCat 函子
    private
      cat : Category (lsuc ℓ) ℓ ℓ
      cat = SameIndexCat s {ℓ = ℓ}

      reflc : {X Y : LabelSys ℓ} {f : Idx⇒ s X Y} → _≈i_ s f f
      reflc {f = f} = ≈i-refl s {ℓ = ℓ} f
      symc : {X Y : LabelSys ℓ} {f g : Idx⇒ s X Y}
           → _≈i_ s f g → _≈i_ s g f
      symc {f = f} {g = g} p = ≈i-sym s {ℓ = ℓ} {f = f} {g = g} p
      transc : {X Y : LabelSys ℓ} {f g h : Idx⇒ s X Y}
             → _≈i_ s f g → _≈i_ s g h → _≈i_ s f h
      transc {f = f} {g = g} {h = h} p q =
        ≈i-trans s {ℓ = ℓ} {f = f} {g = g} {h = h} p q
      respc : {X Y Z : LabelSys ℓ}
                {F₁ F₂ : Idx⇒ s X Y} {G₁ G₂ : Idx⇒ s Y Z}
            → _≈i_ s F₁ F₂ → _≈i_ s G₁ G₂
            → _≈i_ s (compi s G₁ F₁) (compi s G₂ F₂)
      respc {X = X} {Y = Y} {Z = Z}
            {F₁ = F₁} {F₂ = F₂} {G₁ = G₁} {G₂ = G₂} p q =
        ∘-resp-≈i s {ℓ = ℓ} {X = X} {Y = Y} {Z = Z}
                    {F₁ = F₁} {F₂ = F₂} {G₁ = G₁} {G₂ = G₂} p q

    fold-emb : {m n : ℕ} → Chain⇒ m n
             → Idx⇒ s (stageLS m) (stageLS n)
    fold-emb SQC.stop          = idxi s (stageLS _)
    fold-emb (SQC.step {n = n} p) = compi s (embIdx n) (fold-emb p)

    fold-hom : {m y n : ℕ} (g : Chain⇒ y n) (f : Chain⇒ m y)
             → _≈i_ s (fold-emb (g ∘ch f))
                       (compi s (fold-emb g) (fold-emb f))
    fold-hom {m} {y} {.y} SQC.stop f =
      symc {X = stageLS m} {Y = stageLS y}
           {f = compi s (idxi s (stageLS y)) (fold-emb f)}
           {g = fold-emb f}
           (reflc {f = compi s (idxi s (stageLS y)) (fold-emb f)})
    fold-hom {m} {y} {.(suc t)} (SQC.step {n = t} g) f =
      transc {X = stageLS m} {Y = stageLS (suc t)}
        {f = compi s (embIdx t) (fold-emb (g ∘ch f))}
        {g = compi s (embIdx t) (compi s (fold-emb g) (fold-emb f))}
        {h = compi s (compi s (embIdx t) (fold-emb g)) (fold-emb f)}
        (respc {X = stageLS m} {Y = stageLS t} {Z = stageLS (suc t)}
           {F₁ = fold-emb (g ∘ch f)}
           {F₂ = compi s (fold-emb g) (fold-emb f)}
           {G₁ = embIdx t} {G₂ = embIdx t}
           (fold-hom g f) (reflc {f = embIdx t}))
        (reflc {f = compi s (embIdx t)
                  (compi s (fold-emb g) (fold-emb f))})

    fold-resp-i : {m n : ℕ} {p q : Chain⇒ m n} → p ≡ q
                → _≈i_ s (fold-emb p) (fold-emb q)
    fold-resp-i {p = p} refl = reflc {f = fold-emb p}

    chainFun : Functor ωCat cat
    chainFun = record
      { F₀          = stageLS
      ; F₁          = fold-emb
      ; identity    = λ {m} → reflc {f = fold-emb {m = m} SQC.stop}
      ; homomorphism = λ {m y n f g} → fold-hom g f
      ; F-resp-≈    = λ {m n p q} eq → fold-resp-i {p = p} {q = q} eq
      }

    open import Categories.Diagram.Cocone chainFun

    -- Tagging after one forward step equals one extend of the tagged
    -- thread, definitionally.
    --
    -- 前向一步后再标签化，等于对标签化线程做一次 extend，定义性成立。
    one-ray : (m v : ℕ) (a : L₀ m v)
            → mk (suc m) (emb m v a) ≈Thread mk m a
    one-ray m v a = record { dl = 0 ; dr = 1 ; same = refl }

    -- One-step leg coherence: leg (suc m) ∘ emb m ≈ leg m.
    --
    -- 一步腿相干：leg (suc m) ∘ emb m ≈ leg m。
    one-coh-i : (m : ℕ)
              → _≈i_ s (compi s (legIdx (suc m)) (embIdx m)) (legIdx m)
    one-coh-i m =
      pointwise-i s
        (compi s (legIdx (suc m)) (embIdx m)) (legIdx m)
        (λ v a → one-ray m v a)

    -- Path leg coherence.
    --
    -- 路径腿相干。
    leg-path : {m n : ℕ} (p : Chain⇒ m n)
             → _≈i_ s (compi s (legIdx n) (fold-emb p)) (legIdx m)
    leg-path {m} {.m} SQC.stop =
      reflc {f = compi s (legIdx m) (idxi s (stageLS m))}
    leg-path {m} {.(suc t)} (SQC.step {n = t} p) =
      transc {X = stageLS m} {Y = apexLS}
        {f = compi s (legIdx (suc t))
               (compi s (embIdx t) (fold-emb p))}
        {g = compi s (compi s (legIdx (suc t)) (embIdx t)) (fold-emb p)}
        {h = legIdx m}
        (reflc {f = compi s (legIdx (suc t))
                  (compi s (embIdx t) (fold-emb p))})
        (transc {X = stageLS m} {Y = apexLS}
           {f = compi s (compi s (legIdx (suc t)) (embIdx t)) (fold-emb p)}
           {g = compi s (legIdx t) (fold-emb p)}
           {h = legIdx m}
           (respc {X = stageLS m} {Y = stageLS t} {Z = apexLS}
              {F₁ = fold-emb p} {F₂ = fold-emb p}
              {G₁ = compi s (legIdx (suc t)) (embIdx t)} {G₂ = legIdx t}
              (reflc {f = fold-emb p}) (one-coh-i t))
           (leg-path p))

    -- The canonical direct-limit cocone (unconditional).
    --
    -- 规范直接极限余锥（无条件）。
    nCocone : Cocone
    nCocone = record
      { coapex = record { ψ = legIdx ; commute = λ {m n} p → leg-path p } }

    --------------------------------------------------------------------
    -- Pointwise cocones and the mediating functor
    --
    -- A competing cocone is a coapex Z with legs ψ m and one-step
    -- coherence ψ (suc m) (emb m a) ≈ ψ m a in the fibre setoid. The
    -- mediator evaluates a thread at its birth stage; invariance under
    -- extend makes it well-defined on _≈Thread_. No injectivity, root,
    -- isomorphism or global section is required at this pointwise
    -- level, and no transport, K or funExt is used.
    --
    -- 逐点余锥与 mediate 函子
    --
    -- 竞争余锥由余顶点 Z、腿 ψ m 与一步相干
    -- ψ (suc m)(emb m a) ≈ ψ m a 组成。mediate 在诞生阶段求值线程；
    -- extend 下不变性使其在 _≈Thread_ 上良定义。逐点层无需单射、根、
    -- 同构或全局截面，且无传输、不用 K 与函数外延性。
    record PFCocone (Z : LabelSys ℓ) : Set (lsuc ℓ) where
      field
        ψc  : (m : ℕ) → Idx⇒ s (stageLS m) Z
        coh : (m v : ℕ) (a : L₀ m v)
            → EqOn._≈_ (LabelSys.≈A₀ Z v)
                        (Idx⇒.shape (ψc (suc m)) v (emb m v a))
                        (Idx⇒.shape (ψc m) v a)
    open PFCocone

    module _ {Z : LabelSys ℓ} (K : PFCocone Z) where

      private ≈Z = LabelSys.≈A₀ Z

      -- Evaluate a stage-tagged thread at its birth stage.
      --
      -- 在诞生阶段求值阶段标签化线程。
      eval-ray : {v : ℕ} → Thread v → LabelSys.A₀ Z v
      eval-ray (mk m a) = Idx⇒.shape (ψc K m) _ a

      -- One forward extend leaves the evaluation unchanged.
      --
      -- 一次前向 extend 下求值不变。
      eval-ext : {v : ℕ} (τ : Thread v)
               → EqOn._≈_ (≈Z v) (eval-ray (extend τ)) (eval-ray τ)
      eval-ext (mk m a) = coh K m _ a

      eval-ext^ : (k : ℕ) {v : ℕ} (τ : Thread v)
                → EqOn._≈_ (≈Z v) (eval-ray (extend^ k τ)) (eval-ray τ)
      eval-ext^ zero    τ = EqOn.refl (≈Z _)
      eval-ext^ (suc k) τ =
        EqOn.trans (≈Z _) (eval-ext (extend^ k τ)) (eval-ext^ k τ)

      -- Same-ray threads evaluate to setoid-equal labels.
      --
      -- 同一射线的线程求值为 setoid 相等标签。
      med-shape-cong : {v : ℕ} {τ τ' : Thread v}
                     → τ ≈Thread τ'
                     → EqOn._≈_ (≈Z v) (eval-ray τ) (eval-ray τ')
      med-shape-cong {v = v} r =
        EqOn.trans (≈Z v)
          (EqOn.sym (≈Z v) (eval-ext^ (dl r) _))
          (EqOn.trans (≈Z v)
             (EqOn.reflexive (≈Z v) (cong eval-ray (same r)))
             (eval-ext^ (dr r) _))

      -- The mediator.
      --
      -- mediate。
      mediate : Idx⇒ s apexLS Z
      mediate = record
        { shape      = λ v τ → eval-ray τ
        ; shape-cong = med-shape-cong
        }

      -- Factorisation: mediate ∘ leg m is pointwise ψ m.
      --
      -- 因子分解：mediate ∘ leg m 逐点等于 ψ m。
      triangle : (m v : ℕ) (a : L₀ m v)
               → EqOn._≈_ (≈Z v)
                           (Idx⇒.shape (ψc K m) v a)
                           (Idx⇒.shape (ψc K m) v a)
      triangle m v a = EqOn.refl (≈Z v)

      -- Any other factorising mediator is pointwise equal to mediate.
      --
      -- 任何其他可因子分解的 mediate 与本 mediate 逐点相等。
      unique : (h : Idx⇒ s apexLS Z)
             → ((m v : ℕ) (a : L₀ m v)
                → EqOn._≈_ (≈Z v)
                            (Idx⇒.shape h v (mk m a))
                            (Idx⇒.shape (ψc K m) v a))
             → (v : ℕ) (τ : Thread v)
             → EqOn._≈_ (≈Z v)
                         (Idx⇒.shape h v τ) (eval-ray τ)
      unique h ht v (mk m a) = ht m v a

    --------------------------------------------------------------------
    -- Standard colimit, conditionally
    --
    -- A bisimulation cocone whose stage objects carry, at every label,
    -- a total label-tree rooted at that label (propositional fibres)
    -- admits a unique Cocone⇒ out of nCocone. The tree is used only to
    -- read the pointwise head coherence off the bisimulation commute;
    -- factorisation and uniqueness then lift by pointwise-i.
    --
    -- 条件性标准余极限
    --
    -- 若余锥的阶段对象在每个标签处带一棵以该标签为根的全总标签树
    -- （命题纤维），则存在从 nCocone 出发的唯一 Cocone⇒。树仅用于从
    -- 双模拟 commute 读出逐点头部相干；因子分解与唯一性随后由
    -- pointwise-i 提升。
    module StandardColimit where

      private
        succ-arrow : ∀ {m} → Chain⇒ m (suc m)
        succ-arrow = SQC.step SQC.stop

      module _ (K : Cocone)
               (tree : (m v : ℕ) (a : L₀ m v)
                     → M (A (dsys s (stageLS m)))
                         (E (dsys s (stageLS m))) v)
               (tree-here : (m v : ℕ) (a : L₀ m v)
                          → M.here (tree m v a) ≡ a)
        where

        private
          Zk = Cocone.N K
          ψk = Cocone.ψ K

          -- Move a head equation from the tree root M.here to the
          -- prescribed label a, along the propositional root equation.
          --
          -- 沿命题根等式把头部等式从树根 M.here 搬到指定标签 a。
          relocate : (m v : ℕ)
                     (F G : Idx⇒ s (stageLS m) Zk)
                     (a : L₀ m v)
                   → EqOn._≈_ (LabelSys.≈A₀ Zk v)
                               (Idx⇒.shape F v (M.here (tree m v a)))
                               (Idx⇒.shape G v (M.here (tree m v a)))
                   → EqOn._≈_ (LabelSys.≈A₀ Zk v)
                               (Idx⇒.shape F v a)
                               (Idx⇒.shape G v a)
          relocate m v F G a h0 =
            EqOn.trans (LabelSys.≈A₀ Zk v)
              (EqOn.sym (LabelSys.≈A₀ Zk v)
                 (Idx⇒.shape-cong F (tree-here m v a)))
              (EqOn.trans (LabelSys.≈A₀ Zk v)
                 h0
                 (Idx⇒.shape-cong G (tree-here m v a)))

          -- Forward cocone coherence as a head equation.
          --
          -- 前向余锥相干作为头部等式。
          kcoh : (m v : ℕ) (a : L₀ m v)
               → EqOn._≈_ (LabelSys.≈A₀ Zk v)
                   (Idx⇒.shape (ψk (suc m)) v (emb m v a))
                   (Idx⇒.shape (ψk m) v a)
          kcoh m v a =
            relocate m v
              (compi s (ψk (suc m)) (embIdx m)) (ψk m) a
              (_≈Mˢ_.here-eq
                (Cocone.commute K {X = m} {Y = suc m} succ-arrow
                              v (tree m v a)))

          Kpf : PFCocone Zk
          Kpf = record { ψc = ψk ; coh = kcoh }

        -- The unique mediator and its cocone factorisation.
        --
        -- 唯一 mediate 及其余锥因子分解。
        mediate-i : Idx⇒ s apexLS Zk
        mediate-i = mediate Kpf

        !K : Cocone⇒ nCocone K
        !K = record
          { arr     = mediate-i
          ; commute = λ {m} →
                        pointwise-i s
                          (compi s mediate-i (legIdx m)) (ψk m)
                          (triangle Kpf m)
          }

        -- Any other mediator is bisimulation-equal to mediate-i.
        --
        -- 任何其他 mediate 与 mediate-i 互模拟相等。
        !K-unique : (h : Cocone⇒ nCocone K)
                  → _≈i_ s (Cocone⇒.arr h) mediate-i
        !K-unique h =
          pointwise-i s (Cocone⇒.arr h) mediate-i
            (unique Kpf (Cocone⇒.arr h)
              (λ m v a →
                relocate m v
                  (compi s (Cocone⇒.arr h) (legIdx m)) (ψk m) a
                  (_≈Mˢ_.here-eq
                    (Cocone⇒.commute h {X = m} v (tree m v a)))))
