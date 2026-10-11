------------------------------------------------------------------------
-- Nontrivial-fibre Fin push tower, kernel
--
-- The trivial-fibre tower (LimitSystemS / FinPushColimitS) uses
-- TrivDetˢ, whose label fibre is ⊤. Here the deterministic Fin position
-- dynamics is kept (positions extended by inject₁, one deterministic
-- child per node) but labels are indexed by the STABLE GLOBAL ID ℕ, not
-- by the dependent Fin position. A stage-m label at position x is
-- L m (toℕ x); the forward label map l-emb m v stays at the same global
-- id v, so its type mentions no Fin. The apex label Thread v is a
-- stage-tagged element of L _ v; forward iteration changes only the
-- stage, never a Fin index. Consequently labels cross stages purely by
-- function passing: no retraction.
--
-- 非平凡纤维 Fin push 塔内核
--
-- 平凡纤维塔（LimitSystemS / FinPushColimitS）采用 TrivDetˢ，标签纤维为
-- ⊤。此处保留确定性 Fin 位置动力（位置经 inject₁ 扩展，每节点一个确定
-- 性子节点），但标签按稳定全局 id ℕ 索引，而非依赖的 Fin 位置。阶段 m
-- 位置 x 处的标签为 L m (toℕ x)；前向标签映射 l-emb m v 停留在同一全局
-- id v，故其类型不涉及 Fin。顶点标签 Thread v 是 L _ v 的阶段标签化元素；
-- 前向迭代只改阶段，不改 Fin 索引。因此标签跨阶段纯由函数传递：无需收缩。
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module ALMA.Cosmos.Carried.NontrivialPushTowerS where

open import Agda.Primitive using (Level; lzero; lsuc)
open import Agda.Builtin.Sigma using (Σ; _,_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Product.Base using (proj₁; proj₂)
open import Data.Nat.Base using (ℕ; zero; suc; _+_)
open import Data.Nat.Properties using (+-comm)
open import Data.Fin.Base using (Fin; zero; suc; inject₁; toℕ)
open import Data.Unit.Polymorphic.Base using (⊤; tt)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥)
open import Relation.Nullary.Negation using (¬_)
open import Relation.Binary.PropositionalEquality.Core using (cong; trans; sym)

open import Categories.Category.Core using (Category)
open import Categories.Functor using (Functor)

open import ALMA.Base.MCorr using (M)
open import ALMA.Base.MCorrSetoid using
  (SysEq; EqOn; propEqOn; _≈Mˢ_; ≈Mˢ-refl; ≈Mˢ-sym; ≈Mˢ-trans; idAdjˢ)
open import ALMA.Base.MCorrSetoidPush using (PushSimˢ)
open import ALMA.Base.MCorrSetoidCat using
  (FMapˢ; FMˢ; compFMˢ; compFˢ; mapFˢ-comp; _≈FM_; relocateˢ; relocate-resp-≈Mˢ)
open import ALMA.Cosmos.Carried.ColimitPolarity using (no-FM-nonsurjective)
open import ALMA.Cosmos.Carried.SeqColimitS using (Chainˢ; Coconeˢ; Limitˢ)
open import ALMA.Cosmos.Carried.SeqColimitCat using (Chain⇒; ωCat; _∘ch_)
import ALMA.Cosmos.Carried.SeqColimitCat as SQC
open import ALMA.Cosmos.Carried.SameIndexCatS using
  (LabelSys; dsys; Idx⇒; idxi; compi; _≈i_; ≈i-refl; ≈i-sym; ≈i-trans
  ; ∘-resp-≈i; assoc-i; identityˡ-i; identityʳ-i; SameIndexCat)
open import ALMA.Cosmos.Carried.LimitSystemS using (n-at)
import ALMA.Cosmos.Carried.LimitSystemS as LS

open SysEq

------------------------------------------------------------------------
-- One-position extension with definitional toℕ preservation
--
-- stdlib's inject₁ is defined via inject≤, so toℕ (inject₁ x) is only
-- propositionally toℕ x. The stage embedding below recurses directly on
-- Fin, giving toℕ (up x) = toℕ x definitionally; labels indexed by global
-- id then align across stages with no index transport. up is
-- propositionally inject₁.
--
-- 保持 toℕ 定义性不变的单位置扩展
--
-- 标准库 inject₁ 经 inject≤ 定义，toℕ (inject₁ x) 仅命题性等于 toℕ x。
-- 下面的阶段嵌入直接对 Fin 递归，使 toℕ (up x) 定义性等于 toℕ x；按全局
-- id 索引的标签因而跨阶段对齐，无需索引传输。up 命题性等于 inject₁。

up : ∀ {n} → Fin n → Fin (suc n)
up zero    = zero
up (suc i) = suc (up i)

up-toℕ : ∀ {n} (x : Fin n) → toℕ (up x) ≡ toℕ x
up-toℕ zero    = refl
up-toℕ (suc x) = cong suc (up-toℕ x)

up-inject₁ : ∀ {n} (x : Fin n) → up x ≡ inject₁ x
up-inject₁ zero    = refl
up-inject₁ (suc x) = cong suc (up-inject₁ x)

------------------------------------------------------------------------
-- A deterministic Fin tower with labels indexed by global id
--
-- t is the deterministic position transition; embed-compat is its
-- compatibility with the one-position extension inject₁. L m v is the
-- label at global id v as present at stage m (total over v; labels at
-- not-yet-born positions are free). l-emb carries a label at global id v
-- from stage m to stage m+1 at the SAME v.
--
-- 标签按全局 id 索引的确定性 Fin 塔
--
-- t 为确定性位置转移；embed-compat 是其与单位置扩展 inject₁ 的相容性。
-- L m v 是全局 id v 在阶段 m 的标签（对 v 全；未诞生位置的标签自由）。
-- l-emb 把全局 id v 的标签从阶段 m 携带到阶段 m+1，v 不变。

record LabeledFinTower (ℓ : Level) : Set (lsuc ℓ) where
  field
    t        : (m : ℕ) → Fin (n-at m) → Fin (n-at m)
    L        : (m : ℕ) → ℕ → Set ℓ
    l-emb    : (m v : ℕ) → L m v → L (suc m) v
    embed-compat :
      (m : ℕ) (x : Fin (n-at m))
      → t (suc m) (inject₁ x) ≡ inject₁ (t m x)

module Tower {ℓ : Level} (T : LabeledFinTower ℓ) where

  open LabeledFinTower T
  open LS.LimitSystemS t embed-compat using (s∞; read-coh)

  ----------------------------------------------------------------------
  -- Stage systems
  --
  -- Labels are pulled from the global-id family via toℕ; the edge fibre
  -- is the singleton proof y ≡ t m x (one child).
  --
  -- 阶段系统
  --
  -- 标签经 toℕ 取自全局 id 族；边纤维为单点证明 y ≡ t m x（唯一子节点）。

  LStage : (m : ℕ) → SysEq lzero ℓ lzero ℓ lzero
  LStage m = record
    { I  = Fin (n-at m)
    ; A  = λ x → L m (toℕ x)
    ; E  = λ x _ y → Σ (⊤ {lzero}) λ _ → y ≡ t m x
    ; ≈A = λ x → propEqOn (L m (toℕ x))
    ; ≈E = λ x _ y → propEqOn (Σ (⊤ {lzero}) λ _ → y ≡ t m x)
    }

  -- Deterministic orbit under a global labelling (lab by global id).
  --
  -- 全局标签族（按全局 id）下的确定性轨道。
  orbit : (m : ℕ) (x : Fin (n-at m)) (lab : ∀ v → L m v)
        → M (A (LStage m)) (E (LStage m)) x
  orbit m x lab .M.here      = lab (toℕ x)
  orbit m x lab .M.below y _ = orbit m y lab

  ----------------------------------------------------------------------
  -- One-step index embedding and the graph label correspondence
  --
  -- 一步索引嵌入与图标签对应

  -- Compatibility of t with up, derived from embed-compat for inject₁.
  --
  -- t 与 up 的相容性，由 inject₁ 的 embed-compat 导出。
  up-compat : (m : ℕ) (x : Fin (n-at m))
            → t (suc m) (up x) ≡ up (t m x)
  up-compat m x =
    trans (cong (t (suc m)) (up-inject₁ x))
    (trans (embed-compat m x) (sym (up-inject₁ (t m x))))

  R-emb : (m : ℕ) → Fin (n-at m) → Fin (n-at (suc m)) → Set lzero
  R-emb m x y = up x ≡ y

  -- At y = up x the two positions share global id toℕ x definitionally,
  -- so the label correspondence is the graph of l-emb m (toℕ x): no Fin
  -- in its type, no transport.
  --
  -- 在 y = up x 处两位置定义性共享全局 id toℕ x，故标签对应即
  -- l-emb m (toℕ x) 的图：类型中无 Fin，无传输。
  H-emb : (m : ℕ) (x : Fin (n-at m)) (y : Fin (n-at (suc m)))
        → R-emb m x y
        → A (LStage m) x → A (LStage (suc m)) y → Set ℓ
  H-emb m x .(up x) refl a b rewrite up-toℕ x =
    l-emb m (toℕ x) a ≡ b

  -- The embedding as a forward simulation. lab₁ is the next-stage
  -- global labelling, coherent with lab under l-emb.
  --
  -- 嵌入作为前向模拟。lab₁ 是下一阶段全局标签族，与 lab 经 l-emb 相干。
  emb-sim : (m : ℕ) (lab : ∀ v → L m v) (lab₁ : ∀ v → L (suc m) v)
          → (coh : ∀ v → l-emb m v (lab v) ≡ lab₁ v)
          → (x : Fin (n-at m))
          → PushSimˢ (LStage m) (LStage (suc m)) (R-emb m) (H-emb m)
                      refl (orbit m x lab) (orbit (suc m) (up x) lab₁)
  emb-sim m lab lab₁ coh x .PushSimˢ.here-eq rewrite up-toℕ x =
    coh (toℕ x)
  emb-sim m lab lab₁ coh x .PushSimˢ.push y (_ , eq) =
    up y , ((tt , edge) , (refl , emb-sim m lab lab₁ coh y))
    where
      edge : up y ≡ t (suc m) (up x)
      edge = trans (cong up eq) (sym (up-compat m x))

  ----------------------------------------------------------------------
  -- Eventual label at global id v
  --
  -- A stage-tagged element of L _ v. There is no Fin position in the
  -- carrier; extend changes only the stage and applies l-emb at the
  -- fixed v.
  --
  -- 全局 id v 处的最终标签
  --
  -- L _ v 的阶段标签化元素。载体中无 Fin 位置；extend 只改阶段并在固定
  -- v 上应用 l-emb。

  record Thread (v : ℕ) : Set ℓ where
    inductive
    constructor mk
    field
      stage  : ℕ
      tlabel : L stage v
  open Thread public

  extend : ∀ {v} → Thread v → Thread v
  extend {v} (mk m a) = mk (suc m) (l-emb m v a)

  extend^ : ∀ {v} → ℕ → Thread v → Thread v
  extend^ zero    t = t
  extend^ (suc n) t = extend (extend^ n t)

  thread-at : (v : ℕ) (m : ℕ) → L m v → Thread v
  thread-at v m a = mk m a

  ----------------------------------------------------------------------
  -- Finest carried equivalence
  --
  -- Two threads are the same ray when some forward iterates coincide as
  -- full records. Built from ℕ iteration arithmetic and cong only;
  -- labels always live in L _ v at the same v.
  --
  -- 最细携带等价
  --
  -- 当某前向迭代作为整条记录重合时，两线程为同一射线。仅由 ℕ 迭代算术
  -- 与 cong 构造；标签始终处于同一 v 的 L _ v 中。

  record _≈Thread_ {v : ℕ} (t u : Thread v) : Set ℓ where
    field
      dl   : ℕ
      dr   : ℕ
      same : extend^ dl t ≡ extend^ dr u
  open _≈Thread_

  extend^-comp : ∀ {v} (a b : ℕ) (t : Thread v)
               → extend^ a (extend^ b t) ≡ extend^ (a + b) t
  extend^-comp zero    b t = refl
  extend^-comp (suc a) b t = cong extend (extend^-comp a b t)

  iter-add-comm : ∀ {v} (a b : ℕ) (t : Thread v)
                → extend^ (a + b) t ≡ extend^ (b + a) t
  iter-add-comm a b t rewrite +-comm a b = refl

  ≈Thread-refl : ∀ {v} {t : Thread v} → t ≈Thread t
  ≈Thread-refl = record { dl = zero ; dr = zero ; same = refl }

  ≈Thread-sym : ∀ {v} {t u : Thread v} → t ≈Thread u → u ≈Thread t
  ≈Thread-sym p = record { dl = dr p ; dr = dl p ; same = sym (same p) }

  ≈Thread-trans : ∀ {v} {t u w : Thread v}
                → t ≈Thread u → u ≈Thread w → t ≈Thread w
  ≈Thread-trans {u = u} p q = record
    { dl = c + a
    ; dr = b + d
    ; same =
        trans (sym (extend^-comp c a _))
        (trans (cong (extend^ c) (same p))
        (trans (extend^-comp c b u)
        (trans (iter-add-comm c b u)
        (trans (sym (extend^-comp b c u))
        (trans (cong (extend^ b) (same q))
               (extend^-comp b d _))))))
    }
    where
    a = dl p ; b = dr p ; c = dl q ; d = dr q

  ≈A∞ : (v : ℕ) → EqOn {ℓ = ℓ} (Thread v)
  ≈A∞ v = record
    { _≈_ = _≈Thread_
    ; isEquivalence = record
      { refl  = ≈Thread-refl
      ; sym   = ≈Thread-sym
      ; trans = ≈Thread-trans
      }
    }

  ----------------------------------------------------------------------
  -- Apex system
  --
  -- ℕ index, deterministic dynamics s∞, Thread labels, singleton
  -- deterministic edges.
  --
  -- 顶点系统
  --
  -- ℕ 索引、确定性动力 s∞、Thread 标签、单点确定性边。

  -- Shared singleton-edge system over the fixed dynamics s∞. Every
  -- stage and the apex differ only in the label fibre and its EqOn; the
  -- index, edge fibre and edge EqOn are definitionally shared, so an
  -- identity-index carried functor reuses the source fibre adjunction in
  -- its map congruence with no edge transport.
  --
  -- 固定动力 s∞ 上共享单点边的系统。各阶段与顶点仅标签纤维及其 EqOn
  -- 不同；索引、边纤维与边 EqOn 定义性共享，故索引恒等的携带函子可在其
  -- map 同余中直接复用源纤维伴随，无边缘传输。
  nsys : (A₀ : ℕ → Set ℓ) → ((v : ℕ) → EqOn {ℓ = ℓ} (A₀ v))
       → SysEq lzero ℓ lzero ℓ lzero
  nsys A₀ ≈A₀ = record
    { I  = ℕ
    ; A  = A₀
    ; E  = λ v _ w → Σ (⊤ {lzero}) λ _ → w ≡ s∞ v
    ; ≈A = ≈A₀
    ; ≈E = λ v _ w → propEqOn (Σ (⊤ {lzero}) λ _ → w ≡ s∞ v)
    }

  L∞ : SysEq lzero ℓ lzero ℓ lzero
  L∞ = nsys Thread ≈A∞

  ----------------------------------------------------------------------
  -- ℕ-indexed stage chain on which the colimit universal property lives
  --
  -- Every stage shares the fixed apex dynamics s∞ and differs only in its
  -- label fibre L m. The stage embedding is identity on the global id
  -- (R = propositional equality, always refl), so labels across stages
  -- share a fibre definitionally: no Fin, no toℕ, no transport. The Fin
  -- tower above is one way to PRODUCE such a chain.
  --
  -- 余极限泛性质所在的 ℕ 索引阶段链
  --
  -- 每个阶段共享固定顶点动力 s∞，仅标签纤维 L m 不同。阶段嵌入在全局
  -- id 上恒等（R 为命题相等，恒取 refl），故跨阶段标签定义性共享纤维：
  -- 无 Fin、无 toℕ、无传输。上面的 Fin 塔是产生这种链的一种方式。

  NStage : (m : ℕ) → SysEq lzero ℓ lzero ℓ lzero
  NStage m = nsys (L m) (λ v → propEqOn (L m v))

  -- Identity-index layer relation between consecutive stages.
  --
  -- 相邻阶段间索引恒等的层关系。
  Rn : ℕ → ℕ → Set lzero
  Rn v w = v ≡ w

  -- Label correspondence at the refl layer: the graph of l-emb at the
  -- same global id.
  --
  -- refl 层处的标签对应：同一全局 id 上 l-emb 的图。
  Hn : (m v w : ℕ) → Rn v w → L m v → L (suc m) w → Set ℓ
  Hn m v .v refl a b = l-emb m v a ≡ b

  -- Identity-index layer relation from a stage to the apex.
  --
  -- 阶段到顶点的索引恒等层关系。
  Rl : ℕ → ℕ → Set lzero
  Rl v w = v ≡ w

  Hl : (m v w : ℕ) → Rl v w → L m v → Thread w → Set ℓ
  Hl m v .v refl a τ = τ ≈Thread mk m a

  ----------------------------------------------------------------------
  -- Identity-index deterministic carried functor between two nsys systems
  --
  -- u is the identity; the canonical source child of w is w; the fibre
  -- adjunction is the identity. The edge EqOn of any two nsys systems is
  -- definitionally the same propEqOn on the singleton edge, so the map
  -- congruence reuses the source bisimulation's adjunction unchanged: no
  -- edge transport.
  --
  -- 两个 nsys 系统间索引恒等的确定性携带函子
  --
  -- u 为恒等；w 的规范源子节点即 w；纤维伴随为恒等。任意两 nsys 系统的
  -- 边 EqOn 定义性同为单点边上的 propEqOn，故 map 同余直接复用源互模拟
  -- 的伴随：无边缘传输。

  idxFM : (A₀ : ℕ → Set ℓ) (≈A₀ : (v : ℕ) → EqOn {ℓ = ℓ} (A₀ v))
          (A₁ : ℕ → Set ℓ) (≈A₁ : (v : ℕ) → EqOn {ℓ = ℓ} (A₁ v))
          (sh : (v : ℕ) → A₀ v → A₁ v)
          (shc : ∀ {v : ℕ} {a a' : A₀ v}
               → EqOn._≈_ (≈A₀ v) a a'
               → EqOn._≈_ (≈A₁ v) (sh v a) (sh v a'))
          → FMˢ (nsys A₀ ≈A₀) (nsys A₁ ≈A₁)
  idxFM A₀ ≈A₀ A₁ ≈A₁ sh shc = record
    { mor        = fmor
    ; shape-cong = λ e → shc e
    ; map-cong   = go
    }
    where
    fmor : FMapˢ (nsys A₀ ≈A₀) (nsys A₁ ≈A₁)
    fmor = record
      { u      = λ v → v
      ; shape  = sh
      ; childF = λ v _ w → w , refl
      ; adjFˢ  = λ v a w → idAdjˢ (≈E (nsys A₁ ≈A₁) v (sh v a) w)
      }
    mutual
      go : ∀ {v : ℕ} {t s : M A₀ (E (nsys A₀ ≈A₀)) v}
         → _≈Mˢ_ ≈A₀ (≈E (nsys A₀ ≈A₀)) t s
         → _≈Mˢ_ ≈A₁ (≈E (nsys A₁ ≈A₁))
                  (FMapˢ.mapFˢ fmor v t) (FMapˢ.mapFˢ fmor v s)
      go p ._≈Mˢ_.here-eq = shc (_≈Mˢ_.here-eq p)
      go p ._≈Mˢ_.below-eq w =
        let adj , fs = _≈Mˢ_.below-eq p w
            fwd , bwd = fs
        in adj , ((λ e₁ → go (fwd e₁)) , (λ e₂ → go (bwd e₂)))

  -- Stage embedding FMˢ: identity index, l-emb on labels.
  --
  -- 阶段嵌入 FMˢ：索引恒等，标签经 l-emb。
  embFM : (m : ℕ) → FMˢ (NStage m) (NStage (suc m))
  embFM m =
    idxFM (L m) (λ v → propEqOn (L m v))
          (L (suc m)) (λ v → propEqOn (L (suc m) v))
          (λ v a → l-emb m v a) (λ {v} e → cong (l-emb m v) e)

  -- A propositional label equality maps to the same-ray relation at the
  -- fixed stage.
  --
  -- 命题性标签等式映射为固定阶段处的同一射线关系。
  leg-shc : ∀ {m v : ℕ} {a a' : L m v}
          → a ≡ a' → mk m a ≈Thread mk m a'
  leg-shc refl = ≈Thread-refl

  -- Stage-to-apex leg FMˢ: identity index, label to its stage-m thread.
  --
  -- 阶段到顶点的腿 FMˢ：索引恒等，标签映为其阶段 m 线程。
  legFM : (m : ℕ) → FMˢ (NStage m) L∞
  legFM m =
    idxFM (L m) (λ v → propEqOn (L m v)) Thread ≈A∞
          (λ v a → mk m a) leg-shc

  -- The ℕ-indexed nontrivial-fibre chain.
  --
  -- ℕ 索引非平凡纤维链。
  nchain : Chainˢ lzero ℓ lzero ℓ lzero
  nchain = record { X = NStage ; emb = embFM }

  -- Colimit apex existence data. The stage injection is the identity on
  -- the global id and sends a stage-m label to its stage-m thread; it is
  -- coherent definitionally. Every apex node v is represented at stage v.
  --
  -- 余极限顶点存在性数据。阶段注入在全局 id 上恒等，把阶段 m 标签送到其
  -- 阶段 m 线程；相干性定义性成立。每个顶点节点 v 由阶段 v 代表。
  nlimit : Limitˢ nchain
  nlimit = record
    { L         = L∞
    ; inj-u     = λ _ v → v
    ; inj-shape = λ m v a → mk m a
    ; inj-coh   = λ _ _ → refl
    ; rep       = λ v → v , v , refl
    }

  ----------------------------------------------------------------------
  -- Canonical cocone
  --
  -- Embedding then the stage m+1 leg advances a thread by one extend over
  -- the stage m leg; the two apex labels are the same ray definitionally,
  -- and the singleton child trees agree coinductively. The equality is
  -- behavioural (_≈FM_), never a label transport.
  --
  -- 规范余锥
  --
  -- 先嵌入再走阶段 m+1 腿，相对阶段 m 腿只多一次 extend；两个顶点标签
  -- 定义性为同一射线，单子树余归纳一致。相等是行为相等（_≈FM_），绝非
  -- 标签传输。

  -- One extend is the same ray (zero iterations on the left, one on the
  -- right), definitionally.
  --
  -- 一次 extend 即同一射线（左侧零次迭代、右侧一次），定义性成立。
  one-ray : ∀ (m v : ℕ) (a : L m v)
          → mk (suc m) (l-emb m v a) ≈Thread mk m a
  one-ray m v a = record { dl = zero ; dr = suc zero ; same = refl }

  mutual
    coh-go : ∀ (m v : ℕ) (t : M (A (NStage m)) (E (NStage m)) v)
           → _≈Mˢ_ (≈A L∞) (≈E L∞)
                    (FMapˢ.mapFˢ (FMˢ.mor
                       (compFMˢ (legFM (suc m)) (embFM m))) v t)
                    (FMapˢ.mapFˢ (FMˢ.mor (legFM m)) v t)
    coh-go m v t ._≈Mˢ_.here-eq = one-ray m v (M.here t)
    coh-go m v t ._≈Mˢ_.below-eq w =
        idAdjˢ (propEqOn (Σ (⊤ {lzero}) λ _ → w ≡ s∞ v))
      , ( (λ e₁ → coh-go m w (M.below t w e₁))
        , (λ e₂ → coh-go˘ m w (M.below t w e₂)) )

    coh-go˘ : ∀ (m v : ℕ) (t : M (A (NStage m)) (E (NStage m)) v)
            → _≈Mˢ_ (≈A L∞) (≈E L∞)
                     (FMapˢ.mapFˢ (FMˢ.mor (legFM m)) v t)
                     (FMapˢ.mapFˢ (FMˢ.mor
                        (compFMˢ (legFM (suc m)) (embFM m))) v t)
    coh-go˘ m v t ._≈Mˢ_.here-eq =
      EqOn.sym (≈A L∞ v) (one-ray m v (M.here t))
    coh-go˘ m v t ._≈Mˢ_.below-eq w =
        idAdjˢ (propEqOn (Σ (⊤ {lzero}) λ _ → w ≡ s∞ v))
      , ( (λ e₁ → coh-go˘ m w (M.below t w e₁))
        , (λ e₂ → coh-go m w (M.below t w e₂)) )

  -- One-step cocone coherence at behavioural equality.
  --
  -- 行为相等下的一步余锥相干性。
  leg-coh-one : (m : ℕ)
              → compFMˢ (legFM (suc m)) (embFM m) ≈FM legFM m
  leg-coh-one m v = refl , coh-go m v

  -- The canonical cocone over nchain with apex L∞.
  --
  -- 以 L∞ 为顶点、nchain 上的规范余锥。
  ncocone : Coconeˢ nchain L∞
  ncocone = record { leg = legFM ; coh = leg-coh-one }

  ----------------------------------------------------------------------
  -- Canonical legs from a coherent global labelling
  --
  -- lab (suc m) v is the forward image of lab m v under l-emb. The apex
  -- orbit at v carries the thread born at stage v. A leg's push returns
  -- the source child's own global id toℕ y as the target index; read-coh
  -- is used only as the apex edge witness, so every recursive simulation
  -- sits at r = refl with v = toℕ of the source position and labels share
  -- a fibre. No index transport.
  --
  -- 相干全局标签族下的规范腿
  --
  -- lab (suc m) v 是 lab m v 经 l-emb 的前向像。顶点轨道在 v 处携带阶段
  -- v 诞生的线程。腿的 push 把源子节点自身的全局 id toℕ y 作为目标索引
  -- 返回；read-coh 仅用作顶点边见证，故每个递归模拟都停在 r = refl、
  -- v = 源位置的 toℕ，标签共享纤维。无索引传输。

  module WithLabelling
    (lab     : (m v : ℕ) → L m v)
    (lab-coh : (m v : ℕ) → lab (suc m) v ≡ l-emb m v (lab m v))
    where

    -- Apex orbit: thread at v born at stage v.
    --
    -- 顶点轨道：v 处阶段 v 诞生的线程。
    orbit∞ : (v : ℕ) → M (A L∞) (E L∞) v
    orbit∞ v .M.here      = mk v (lab v v)
    orbit∞ v .M.below w _ = orbit∞ w

    -- Forward iteration of a stage label lands at the coherent label.
    --
    -- 阶段标签的前向迭代落在相干标签上。
    forward-to : (k m v : ℕ)
               → extend^ k (mk m (lab m v)) ≡ mk (k + m) (lab (k + m) v)
    forward-to zero    m v = refl
    forward-to (suc k) m v =
      trans (cong extend (forward-to k m v))
            (cong (mk (suc (k + m))) (sym (lab-coh (k + m) v)))

    -- The thread born at stage v and the stage-m label at v are the same
    -- ray: extend both to the common stage m + v.
    --
    -- 阶段 v 诞生的线程与 v 处阶段 m 标签是同一射线：二者都前向到共同
    -- 阶段 m + v。
    leg-here : (m v : ℕ) → mk v (lab v v) ≈Thread mk m (lab m v)
    leg-here m v = record { dl = m ; dr = v ; same = goal }
      where
        mk-eq : mk (m + v) (lab (m + v) v) ≡ mk (v + m) (lab (v + m) v)
        mk-eq rewrite +-comm m v = refl
        goal : extend^ m (mk v (lab v v)) ≡ extend^ v (mk m (lab m v))
        goal = trans (forward-to m v v)
                     (trans mk-eq (sym (forward-to v m v)))

    -- Layer relation: the apex node is the source global id.
    --
    -- 层关系：顶点节点即源全局 id。
    Rₙ : (m : ℕ) → Fin (n-at m) → ℕ → Set lzero
    Rₙ m x v = toℕ x ≡ v

    -- Label correspondence at the refl layer witness: the apex thread
    -- and the stage-m label are the same ray.
    --
    -- refl 层见证处的标签对应：顶点线程与阶段 m 标签是同一射线。
    Hₙ : (m : ℕ) (x : Fin (n-at m)) (v : ℕ) → Rₙ m x v
       → A (LStage m) x → Thread v → Set ℓ
    Hₙ m x .(toℕ x) refl a τ = τ ≈Thread mk m a

    -- The canonical leg at position x; every push stays at refl by
    -- targeting the child's own global id.
    --
    -- 位置 x 处的规范腿；每次 push 以子节点自身全局 id 为目标，停在 refl。
    legₙ : (m : ℕ) (x : Fin (n-at m))
         → PushSimˢ (LStage m) L∞ (Rₙ m) (Hₙ m) refl
                     (orbit m x (lab m)) (orbit∞ (toℕ x))
    legₙ m x .PushSimˢ.here-eq = leg-here m (toℕ x)
    legₙ m x .PushSimˢ.push y (_ , eq) =
      toℕ y , ((tt , edge) , (refl , legₙ m y))
      where
        edge : toℕ y ≡ s∞ (toℕ x)
        edge = trans (cong toℕ eq) (read-coh m x)

    --------------------------------------------------------------------
    -- ℕ-indexed chain
    --
    -- Deterministic orbits, the identity-index stage embedding, and the
    -- identity-index leg into the apex.
    --
    -- ℕ 索引链
    --
    -- 确定性轨道、索引恒等的阶段嵌入与索引恒等的顶点腿。

    norbit : (m v : ℕ) → M (A (NStage m)) (E (NStage m)) v
    norbit m v .M.here      = lab m v
    norbit m v .M.below w _ = norbit m w

    -- Total stage-m tree with an arbitrary head label a and canonical
    -- tails. Every head label (not only lab m v) is therefore reached by
    -- the stage-m leg at some total tree.
    --
    -- 任意头标签 a、规范尾的全总阶段 m 树。故每个头标签（不限于
    -- lab m v）都被阶段 m 腿在某棵全总树处到达。
    stage-ray : (m v : ℕ) (a : L m v)
              → M (A (NStage m)) (E (NStage m)) v
    stage-ray m v a .M.here      = a
    stage-ray m v a .M.below w _ = norbit m w

    -- Stage embedding: identity index, l-emb on labels.
    --
    -- 阶段嵌入：索引恒等，标签经 l-emb。
    n-sim : (m v : ℕ)
          → PushSimˢ (NStage m) (NStage (suc m)) Rn (Hn m) refl
                      (norbit m v) (norbit (suc m) v)
    n-sim m v .PushSimˢ.here-eq = sym (lab-coh m v)
    n-sim m v .PushSimˢ.push w (_ , eq) =
      w , ((tt , eq) , (refl , n-sim m w))

    -- Leg into the apex: identity index, same-ray label correspondence.
    --
    -- 顶点腿：索引恒等，标签为同一射线对应。
    nleg : (m v : ℕ)
         → PushSimˢ (NStage m) L∞ Rl (Hl m) refl
                     (norbit m v) (orbit∞ v)
    nleg m v .PushSimˢ.here-eq = leg-here m v
    nleg m v .PushSimˢ.push w (_ , eq) =
      w , ((tt , eq) , (refl , nleg m w))

    -- FMˢ-bisimulation form of nleg: the image of the canonical stage
    -- orbit under legFM m is bisimilar to the apex orbit orbit∞.
    --
    -- nleg 的 FMˢ 互模拟形式：legFM m 下规范阶段轨道的像与顶点轨道
    -- orbit∞ 互模拟。
    mutual
      legray-go : (m v : ℕ)
                → _≈Mˢ_ (≈A L∞) (≈E L∞)
                         (FMapˢ.mapFˢ (FMˢ.mor (legFM m)) v (norbit m v))
                         (orbit∞ v)
      legray-go m v ._≈Mˢ_.here-eq = ≈Thread-sym (leg-here m v)
      legray-go m v ._≈Mˢ_.below-eq w =
          idAdjˢ (≈E L∞ v (mk m (lab m v)) w)
        , ( (λ _ → legray-go   m w)
          , (λ _ → legray-go˘  m w) )

      legray-go˘ : (m v : ℕ)
                 → _≈Mˢ_ (≈A L∞) (≈E L∞)
                          (orbit∞ v)
                          (FMapˢ.mapFˢ (FMˢ.mor (legFM m)) v (norbit m v))
      legray-go˘ m v ._≈Mˢ_.here-eq = leg-here m v
      legray-go˘ m v ._≈Mˢ_.below-eq w =
          idAdjˢ (≈E L∞ v (mk v (lab v v)) w)
        , ( (λ _ → legray-go˘  m w)
          , (λ _ → legray-go   m w) )

    --------------------------------------------------------------------
    -- Same-index nontrivial mediating simulation
    --
    -- A competing cocone over the SAME index and dynamics (identity
    -- trajectory) carries an arbitrary label family ZL with its own
    -- EqOn, together with per-stage evaluation maps zm that are stable
    -- under l-emb. Every layer witness is then refl, so labels pass from
    -- a stage to the target purely by function application at a shared
    -- ℕ index: no fibre transport. The target fibre is non-trivial;
    -- uniqueness is relative to pointwise label agreement (carried
    -- data), never the automatic refl of the ⊤-fibre case.
    --
    -- 同索引非平凡 mediate 模拟
    --
    -- 同一索引与动力（恒等轨迹）上的竞争余锥携带任意标签族 ZL 及其
    -- EqOn，以及在 l-emb 下稳定的逐阶段求值映射 zm。所有层见证均为
    -- refl，故标签在共享 ℕ 索引上纯由函数作用传递：无纤维传输。目标
    -- 纤维非平凡；唯一性相对逐点标签一致（作为数据携带），绝非 ⊤ 纤维
    -- 情形下自动的 refl。

    module SameIndexMediate
      (ZL  : ℕ → Set ℓ)
      (≈ZL : (v : ℕ) → EqOn {ℓ = ℓ} (ZL v))
      (zm  : (m v : ℕ) → L m v → ZL v)
      (zm-coh : (m v : ℕ) (a : L m v)
              → EqOn._≈_ (≈ZL v)
                  (zm (suc m) v (l-emb m v a)) (zm m v a))
      where

      -- Target system: same ℕ index and s∞ dynamics, ZL labels.
      --
      -- 目标系统：同一 ℕ 索引与 s∞ 动力，标签为 ZL。
      Z : SysEq lzero ℓ lzero ℓ lzero
      Z = record
        { I  = ℕ
        ; A  = ZL
        ; E  = λ v _ w → Σ (⊤ {lzero}) λ _ → w ≡ s∞ v
        ; ≈A = ≈ZL
        ; ≈E = λ v _ w → propEqOn (Σ (⊤ {lzero}) λ _ → w ≡ s∞ v)
        }

      -- Deterministic orbit induced by a label family.
      --
      -- 标签族诱导的确定性轨道。
      orbit-of : (zl : (v : ℕ) → ZL v) (v : ℕ)
               → M (A Z) (E Z) v
      orbit-of zl v .M.here      = zl v
      orbit-of zl v .M.below w _ = orbit-of zl w

      -- Canonical evaluation of the thread born at v.
      --
      -- v 处诞生线程的规范求值。
      eval∞ : (v : ℕ) → ZL v
      eval∞ v = zm v v (lab v v)

      zorbit : (v : ℕ) → M (A Z) (E Z) v
      zorbit = orbit-of eval∞

      -- Stage-m target orbit and the identity-index label relation.
      --
      -- 阶段 m 目标轨道与索引恒等标签关系。
      zorbit-stage : (m v : ℕ) → M (A Z) (E Z) v
      zorbit-stage m = orbit-of (λ v → zm m v (lab m v))

      Rz : ℕ → ℕ → Set lzero
      Rz v w = v ≡ w

      Hz : (m v w : ℕ) → Rz v w → L m v → ZL w → Set ℓ
      Hz m v .v refl a b = EqOn._≈_ (≈ZL v) b (zm m v a)

      -- Each stage leg as a forward simulation into Z.
      --
      -- 每条阶段腿作为到 Z 的前向模拟。
      zleg : (m v : ℕ)
           → PushSimˢ (NStage m) Z Rz (Hz m) refl
                       (norbit m v) (zorbit-stage m v)
      zleg m v .PushSimˢ.here-eq = EqOn.refl (≈ZL v)
      zleg m v .PushSimˢ.push w (_ , eq) =
        w , ((tt , eq) , (refl , zleg m w))

      -- Evaluation of an arbitrary stage-tagged thread at its own index.
      --
      -- 任意阶段标签化线程在自身索引处的求值。
      eval-ray : ∀ {v : ℕ} → Thread v → ZL v
      eval-ray {v} (mk m a) = zm m v a

      H∞ : (v w : ℕ) → Rz v w → Thread v → ZL w → Set ℓ
      H∞ v .v refl τ b = EqOn._≈_ (≈ZL v) b (eval-ray τ)

      -- The mediating simulation from the apex to Z.
      --
      -- 从顶点到 Z 的 mediate 模拟。
      zmed : (v : ℕ)
           → PushSimˢ L∞ Z Rz H∞ refl (orbit∞ v) (zorbit v)
      zmed v .PushSimˢ.here-eq = EqOn.refl (≈ZL v)
      zmed v .PushSimˢ.push w (_ , eq) =
        w , ((tt , eq) , (refl , zmed w))

      -- Relative uniqueness: pointwise label agreement (explicit data)
      -- between two deterministic orbit families gives a bisimulation.
      -- This is not automatic: for a non-trivial fibre the agreement
      -- must be supplied at every node.
      --
      -- 相对唯一性：两个确定性轨道族逐点标签一致（显式数据）即给出互
      -- 模拟。它不是自动的：非平凡纤维下，一致必须在每个节点显式给出。
      mutual
        orb-bisim : (zl₁ zl₂ : (v : ℕ) → ZL v)
                  → (he : (v : ℕ) → EqOn._≈_ (≈ZL v) (zl₁ v) (zl₂ v))
                  → (v : ℕ)
                  → _≈Mˢ_ (≈A Z) (≈E Z)
                           (orbit-of zl₁ v) (orbit-of zl₂ v)
        orb-bisim zl₁ zl₂ he v ._≈Mˢ_.here-eq = he v
        orb-bisim zl₁ zl₂ he v ._≈Mˢ_.below-eq w =
            idAdjˢ (propEqOn (Σ (⊤ {lzero}) λ _ → w ≡ s∞ v))
          , ( (λ _ → orb-bisim zl₁ zl₂ he w)
            , (λ _ → orb-bisim˘ zl₁ zl₂ he w) )

        orb-bisim˘ : (zl₁ zl₂ : (v : ℕ) → ZL v)
                   → (he : (v : ℕ) → EqOn._≈_ (≈ZL v) (zl₁ v) (zl₂ v))
                   → (v : ℕ)
                   → _≈Mˢ_ (≈A Z) (≈E Z)
                            (orbit-of zl₂ v) (orbit-of zl₁ v)
        orb-bisim˘ zl₁ zl₂ he v ._≈Mˢ_.here-eq =
          EqOn.sym (≈ZL v) (he v)
        orb-bisim˘ zl₁ zl₂ he v ._≈Mˢ_.below-eq w =
            idAdjˢ (propEqOn (Σ (⊤ {lzero}) λ _ → w ≡ s∞ v))
          , ( (λ _ → orb-bisim˘ zl₁ zl₂ he w)
            , (λ _ → orb-bisim zl₁ zl₂ he w) )

      -- Any competing label family pointwise equal to the canonical
      -- evaluation induces the same target tree up to _≈Mˢ_.
      --
      -- 任何与规范求值逐点相等的竞争标签族诱导 _≈Mˢ_ 意义下相同的目标树。
      mediate-unique : (zl : (v : ℕ) → ZL v)
                     → (he : (v : ℕ) → EqOn._≈_ (≈ZL v) (zl v) (eval∞ v))
                     → (v : ℕ)
                     → _≈Mˢ_ (≈A Z) (≈E Z)
                              (orbit-of zl v) (zorbit v)
      mediate-unique zl he v = orb-bisim zl eval∞ he v

      ------------------------------------------------------------------
      -- Total-function FMˢ form
      --
      -- Because the index is shared (identity trajectory), evaluation
      -- lands in the fibre at the SAME index, so the shape maps are total
      -- and need no transport. These are the components from which the
      -- fixed Colimitˢ is assembled.
      --
      -- 全函数 FMˢ 形式
      --
      -- 索引共享（恒等轨迹），求值落在同一索引的纤维中，故 shape 映射为
      -- 全函数且无需传输。它们是装配固定 Colimitˢ 的组件。

      -- Stage leg as a total setoid functor.
      --
      -- 全函数 setoid 函子形式的阶段腿。
      legF : (m : ℕ) → FMapˢ (NStage m) Z
      legF m = record
        { u      = λ v → v
        ; shape  = λ v a → zm m v a
        ; childF = λ v _ w → w , refl
        ; adjFˢ  = λ v a w → idAdjˢ (≈E Z v (zm m v a) w)
        }

      leg-shape-cong : (m : ℕ) → ∀ {v : ℕ} {a a' : L m v}
                     → EqOn._≈_ (≈A (NStage m) v) a a'
                     → EqOn._≈_ (≈ZL v) (zm m v a) (zm m v a')
      leg-shape-cong m ea = EqOn.reflexive (≈ZL _) (cong (zm m _) ea)

      leg-map-cong : (m : ℕ) → ∀ {v : ℕ}
                       {t s : M (A (NStage m)) (E (NStage m)) v}
                   → _≈Mˢ_ (≈A (NStage m)) (≈E (NStage m)) t s
                   → _≈Mˢ_ (≈A Z) (≈E Z)
                            (FMapˢ.mapFˢ (legF m) v t)
                            (FMapˢ.mapFˢ (legF m) v s)
      leg-map-cong m h ._≈Mˢ_.here-eq =
        leg-shape-cong m (h ._≈Mˢ_.here-eq)
      leg-map-cong m {v} h ._≈Mˢ_.below-eq w =
        let adj , (fs , bs) = h ._≈Mˢ_.below-eq w
        in adj
         , ( (λ e₁ → leg-map-cong m (fs e₁))
           , (λ e₂ → leg-map-cong m (bs e₂)) )

      zlegFM : (m : ℕ) → FMˢ (NStage m) Z
      zlegFM m = record
        { mor        = legF m
        ; shape-cong = leg-shape-cong m
        ; map-cong   = leg-map-cong m
        }

      -- Evaluation is invariant under one forward extend, up to ≈ZL.
      --
      -- 求值在一次前向 extend 下不变（至 ≈ZL）。
      eval-ext : ∀ {v : ℕ} (τ : Thread v)
               → EqOn._≈_ (≈ZL v) (eval-ray (extend τ)) (eval-ray τ)
      eval-ext {v} (mk m a) = zm-coh m v a

      eval-ext^ : ∀ (k : ℕ) {v : ℕ} (τ : Thread v)
                → EqOn._≈_ (≈ZL v) (eval-ray (extend^ k τ)) (eval-ray τ)
      eval-ext^ zero    τ = EqOn.refl (≈ZL _)
      eval-ext^ (suc k) τ =
        EqOn.trans (≈ZL _) (eval-ext (extend^ k τ)) (eval-ext^ k τ)

      -- Same-ray threads evaluate to setoid-equal labels.
      --
      -- 同一射线的线程求值为 setoid 相等的标签。
      med-shape-cong : ∀ {v : ℕ} {τ τ' : Thread v}
                     → τ ≈Thread τ'
                     → EqOn._≈_ (≈ZL v) (eval-ray τ) (eval-ray τ')
      med-shape-cong {v} {τ} {τ'} r =
        EqOn.trans (≈ZL v)
          (EqOn.sym (≈ZL v) (eval-ext^ dl0 τ))
          (EqOn.trans (≈ZL v)
             (EqOn.reflexive (≈ZL v) (cong eval-ray same0))
             (eval-ext^ dr0 τ'))
        where
        dl0   = _≈Thread_.dl r
        dr0   = _≈Thread_.dr r
        same0 = _≈Thread_.same r

      medF : FMapˢ L∞ Z
      medF = record
        { u      = λ v → v
        ; shape  = λ v τ → eval-ray τ
        ; childF = λ v _ w → w , refl
        ; adjFˢ  = λ v τ w → idAdjˢ (≈E Z v (eval-ray τ) w)
        }

      med-map-cong : ∀ {v : ℕ} {t s : M (A L∞) (E L∞) v}
                   → _≈Mˢ_ (≈A L∞) (≈E L∞) t s
                   → _≈Mˢ_ (≈A Z) (≈E Z)
                            (FMapˢ.mapFˢ medF v t)
                            (FMapˢ.mapFˢ medF v s)
      med-map-cong h ._≈Mˢ_.here-eq =
        med-shape-cong (h ._≈Mˢ_.here-eq)
      med-map-cong {v} h ._≈Mˢ_.below-eq w =
        let adj , (fs , bs) = h ._≈Mˢ_.below-eq w
        in adj
         , ( (λ e₁ → med-map-cong (fs e₁))
           , (λ e₂ → med-map-cong (bs e₂)) )

      zmedFM : FMˢ L∞ Z
      zmedFM = record
        { mor        = medF
        ; shape-cong = med-shape-cong
        ; map-cong   = med-map-cong
        }

      ------------------------------------------------------------------
      -- The same-index competing cocone with the zlegFM legs, and the
      -- factorisation triangle zmedFM ∘ legFM m ≈ zlegFM m.
      --
      -- 以 zlegFM 为腿的同索引竞争余锥，以及因子分解三角
      -- zmedFM ∘ legFM m ≈ zlegFM m。

      comp-leg : (m : ℕ) → FMˢ (NStage m) Z
      comp-leg m = compFMˢ (zlegFM (suc m)) (embFM m)

      mutual
        coc-go : (m v : ℕ) (t : M (A (NStage m)) (E (NStage m)) v)
               → _≈Mˢ_ (≈A Z) (≈E Z)
                        (FMapˢ.mapFˢ (FMˢ.mor (comp-leg m)) v t)
                        (FMapˢ.mapFˢ (FMˢ.mor (zlegFM m)) v t)
        coc-go m v t ._≈Mˢ_.here-eq = zm-coh m v (M.here t)
        coc-go m v t ._≈Mˢ_.below-eq w =
            idAdjˢ (≈E Z v (zm m v (M.here t)) w)
          , ( (λ e → coc-go   m w (M.below t w e))
            , (λ e → coc-go˘  m w (M.below t w e)) )

        coc-go˘ : (m v : ℕ) (t : M (A (NStage m)) (E (NStage m)) v)
                → _≈Mˢ_ (≈A Z) (≈E Z)
                         (FMapˢ.mapFˢ (FMˢ.mor (zlegFM m)) v t)
                         (FMapˢ.mapFˢ (FMˢ.mor (comp-leg m)) v t)
        coc-go˘ m v t ._≈Mˢ_.here-eq =
          EqOn.sym (≈ZL v) (zm-coh m v (M.here t))
        coc-go˘ m v t ._≈Mˢ_.below-eq w =
            idAdjˢ (≈E Z v (zm m v (M.here t)) w)
          , ( (λ e → coc-go˘  m w (M.below t w e))
            , (λ e → coc-go   m w (M.below t w e)) )

      zcocone : Coconeˢ nchain Z
      zcocone = record
        { leg = zlegFM
        ; coh = λ m v → refl , λ t → coc-go m v t
        }

      -- Factorisation: mediating after the apex leg is the stage leg.
      -- Labels agree definitionally (eval-ray (mk m a) = zm m v a).
      --
      -- 因子分解：mediate 接顶点腿即阶段腿。标签定义性相等
      -- （eval-ray (mk m a) = zm m v a）。
      med-leg : (m : ℕ) → FMˢ (NStage m) Z
      med-leg m = compFMˢ zmedFM (legFM m)

      mutual
        tri-go : (m v : ℕ) (t : M (A (NStage m)) (E (NStage m)) v)
               → _≈Mˢ_ (≈A Z) (≈E Z)
                        (FMapˢ.mapFˢ (FMˢ.mor (med-leg m)) v t)
                        (FMapˢ.mapFˢ (FMˢ.mor (zlegFM m)) v t)
        tri-go m v t ._≈Mˢ_.here-eq = EqOn.refl (≈ZL v)
        tri-go m v t ._≈Mˢ_.below-eq w =
            idAdjˢ (≈E Z v (zm m v (M.here t)) w)
          , ( (λ e → tri-go   m w (M.below t w e))
            , (λ e → tri-go˘  m w (M.below t w e)) )

        tri-go˘ : (m v : ℕ) (t : M (A (NStage m)) (E (NStage m)) v)
                → _≈Mˢ_ (≈A Z) (≈E Z)
                         (FMapˢ.mapFˢ (FMˢ.mor (zlegFM m)) v t)
                         (FMapˢ.mapFˢ (FMˢ.mor (med-leg m)) v t)
        tri-go˘ m v t ._≈Mˢ_.here-eq = EqOn.refl (≈ZL v)
        tri-go˘ m v t ._≈Mˢ_.below-eq w =
            idAdjˢ (≈E Z v (zm m v (M.here t)) w)
          , ( (λ e → tri-go˘  m w (M.below t w e))
            , (λ e → tri-go   m w (M.below t w e)) )

      triangle : (m : ℕ) → med-leg m ≈FM zlegFM m
      triangle m v = refl , λ t → tri-go m v t

      -- Target-side ray coincidence: the stage-m canonical evaluation
      -- family and the canonical eval∞ family agree pointwise, by
      -- carrying both forward to their common stage (EqOn only, no
      -- transport across fibres).
      --
      -- 目标侧射线重合：阶段 m 规范求值族与规范 eval∞ 族逐点一致，方法
      -- 是把二者前向携带到共同阶段（仅用 EqOn，不跨纤维传输）。
      zfwd : (k m w : ℕ)
           → EqOn._≈_ (≈ZL w)
               (zm (k + m) w (lab (k + m) w)) (zm m w (lab m w))
      zfwd zero    m w = EqOn.refl (≈ZL w)
      zfwd (suc k) m w =
        EqOn.trans (≈ZL w) step (zfwd k m w)
        where
        eq : l-emb (k + m) w (lab (k + m) w) ≡ lab (suc (k + m)) w
        eq = sym (lab-coh (k + m) w)
        step : EqOn._≈_ (≈ZL w)
                 (zm (suc (k + m)) w (lab (suc (k + m)) w))
                 (zm (k + m) w (lab (k + m) w))
        step =
          EqOn.trans (≈ZL w)
            (EqOn.sym (≈ZL w)
               (EqOn.reflexive (≈ZL w)
                  (cong (zm (suc (k + m)) w) eq)))
            (zm-coh (k + m) w (lab (k + m) w))

      zray-he : (m w : ℕ)
              → EqOn._≈_ (≈ZL w) (zm m w (lab m w)) (eval∞ w)
      zray-he m w =
        EqOn.trans (≈ZL w)
          (EqOn.sym (≈ZL w) (zfwd w m w))
          (EqOn.trans (≈ZL w)
             (EqOn.reflexive (≈ZL w)
                (cong (λ k → zm k w (lab k w)) (+-comm w m)))
             (zfwd m w w))

      -- The stage-leg image of the canonical orbit is bisimilar to the
      -- mediating-functor image of the colimit orbit.
      --
      -- 阶段腿在规范轨道上的像与 mediate 函子在余极限轨道上的像互模拟。
      mutual
        zlegray-go : (m v : ℕ)
                   → _≈Mˢ_ (≈A Z) (≈E Z)
                            (FMapˢ.mapFˢ (legF m) v (norbit m v))
                            (FMapˢ.mapFˢ medF v (orbit∞ v))
        zlegray-go m v ._≈Mˢ_.here-eq = zray-he m v
        zlegray-go m v ._≈Mˢ_.below-eq w =
            idAdjˢ (≈E Z v (zm m v (lab m v)) w)
          , ( (λ _ → zlegray-go   m w)
            , (λ _ → zlegray-go˘  m w) )

        zlegray-go˘ : (m v : ℕ)
                    → _≈Mˢ_ (≈A Z) (≈E Z)
                             (FMapˢ.mapFˢ medF v (orbit∞ v))
                             (FMapˢ.mapFˢ (legF m) v (norbit m v))
        zlegray-go˘ m v ._≈Mˢ_.here-eq =
          EqOn.sym (≈ZL v) (zray-he m v)
        zlegray-go˘ m v ._≈Mˢ_.below-eq w =
            idAdjˢ (≈E Z v (eval∞ v) w)
          , ( (λ _ → zlegray-go˘  m w)
            , (λ _ → zlegray-go   m w) )

      zlegray : (m v : ℕ)
              → _≈Mˢ_ (≈A Z) (≈E Z)
                       (FMapˢ.mapFˢ (legF m) v (norbit m v))
                       (FMapˢ.mapFˢ medF v (orbit∞ v))
      zlegray = zlegray-go

      -- Relative uniqueness on the canonical colimit orbit. Any total
      -- functor h whose composites with every stage leg coincide with
      -- the stage legs (the triangles) agrees with zmedFM at orbit∞.
      -- Free fibre labels are not in any leg image and are therefore
      -- outside the hypothesis; uniqueness is asserted only on the ray
      -- the legs actually reach.
      --
      -- 规范余极限轨道上的相对唯一性。任何全函数函子 h，只要其与每条阶段
      -- 腿的复合等于该阶段腿（三角），就在 orbit∞ 处与 zmedFM 一致。
      -- 自由纤维标签不在任何腿的像中、超出假设范围，故唯一性仅陈述于腿
      -- 实际到达的射线上。
      unique-ray : (h : FMˢ L∞ Z)
        (tr : (m : ℕ) → compFMˢ h (legFM m) ≈FM zlegFM m)
        (v : ℕ)
        → Σ (FMapˢ.u (FMˢ.mor h) v ≡ v)
            (λ r → _≈Mˢ_ (≈A Z) (≈E Z)
                     (relocateˢ r
                        (FMapˢ.mapFˢ (FMˢ.mor h) v (orbit∞ v)))
                     (FMapˢ.mapFˢ medF v (orbit∞ v)))
      unique-ray h tr v = r , goal
        where
        hmor = FMˢ.mor h
        fmor = FMˢ.mor (legFM v)
        cf   = compFˢ hmor fmor
        r    = proj₁ (tr v v)
        hm   = proj₂ (tr v v)

        legImg = FMapˢ.mapFˢ fmor v (norbit v v)
        O    = orbit∞ v
        ZLg  = FMapˢ.mapFˢ (legF v) v (norbit v v)
        ZO   = FMapˢ.mapFˢ medF v (orbit∞ v)

        c1 : _≈Mˢ_ (≈A Z) (≈E Z)
               (FMapˢ.mapFˢ hmor v legImg) (FMapˢ.mapFˢ hmor v O)
        c1 = FMˢ.map-cong h (legray-go v v)

        c1r : _≈Mˢ_ (≈A Z) (≈E Z)
                (relocateˢ r (FMapˢ.mapFˢ hmor v legImg))
                (relocateˢ r (FMapˢ.mapFˢ hmor v O))
        c1r = relocate-resp-≈Mˢ (≈A Z) (≈E Z) r c1

        cmp : _≈Mˢ_ (≈A Z) (≈E Z)
                (relocateˢ r (FMapˢ.mapFˢ cf v (norbit v v)))
                (relocateˢ r (FMapˢ.mapFˢ hmor v legImg))
        cmp = relocate-resp-≈Mˢ (≈A Z) (≈E Z) r
                (mapFˢ-comp hmor fmor v (norbit v v))

        p0 : _≈Mˢ_ (≈A Z) (≈E Z)
               (relocateˢ r (FMapˢ.mapFˢ cf v (norbit v v))) ZLg
        p0 = hm (norbit v v)

        goal : _≈Mˢ_ (≈A Z) (≈E Z)
                 (relocateˢ r (FMapˢ.mapFˢ hmor v O)) ZO
        goal = ≈Mˢ-trans (≈A Z) (≈E Z)
                 (≈Mˢ-trans (≈A Z) (≈E Z)
                    (≈Mˢ-sym (≈A Z) (≈E Z) c1r)
                    (≈Mˢ-trans (≈A Z) (≈E Z)
                       (≈Mˢ-sym (≈A Z) (≈E Z) cmp) p0))
                 (zlegray-go v v)

      ------------------------------------------------------------------
      -- Full coinductive uniqueness in the identity-index range
      --
      -- A competing mediator is an identity-index functor hFM (u = id,
      -- singleton child refl, identity fibre adjunction) given by a head
      -- map H and its congruence, together with one triangle per stage.
      -- Every apex node carries an inductive stage tag mk m a; the stage-m
      -- triangle applied to stage-ray m v a forces H v (mk m a) = zm m v a
      -- at the head, while each child is an arbitrary apex tree whose own
      -- stage tag re-selects the leg and recurses guardedly. Hence the two
      -- mediators are pointwise bisimilar on EVERY total apex tree, not
      -- only on orbit∞. No index path and no transport are used.
      --
      -- 索引恒等范围内的完整余归纳唯一性
      --
      -- 竞争 mediate 是索引恒等函子 hFM（u=id、单子节点 refl、恒等纤维
      -- 伴随），由头映射 H 及其同余给出，并带逐阶段三角。每个顶点节点带
      -- 归纳阶段标签 mk m a；阶段 m 三角作用于 stage-ray m v a 在头部强制
      -- H v (mk m a) = zm m v a，每个子节点是任意顶点树，按其自身阶段标签
      -- 重新选腿并守卫递归。故两个 mediate 在每棵全总顶点树上逐点互模拟，
      -- 不限于 orbit∞。无索引路径、无传输。

      mkHFM : (H : (v : ℕ) → Thread v → ZL v)
              (Hc : ∀ {v : ℕ} {τ τ' : Thread v}
                  → τ ≈Thread τ'
                  → EqOn._≈_ (≈ZL v) (H v τ) (H v τ'))
            → FMˢ L∞ Z
      mkHFM H Hc = record
        { mor        = hF
        ; shape-cong = Hc
        ; map-cong   = hmc
        }
        where
        hF : FMapˢ L∞ Z
        hF = record
          { u      = λ v → v
          ; shape  = λ v τ → H v τ
          ; childF = λ v _ w → w , refl
          ; adjFˢ  = λ v τ w → idAdjˢ (≈E Z v (H v τ) w)
          }
        hmc : ∀ {v : ℕ} {t s : M (A L∞) (E L∞) v}
            → _≈Mˢ_ (≈A L∞) (≈E L∞) t s
            → _≈Mˢ_ (≈A Z) (≈E Z)
                     (FMapˢ.mapFˢ hF v t) (FMapˢ.mapFˢ hF v s)
        hmc p ._≈Mˢ_.here-eq = Hc (_≈Mˢ_.here-eq p)
        hmc {v = v} p ._≈Mˢ_.below-eq w =
          let adj , (fs , bs) = _≈Mˢ_.below-eq p w
          in adj , ((λ e → hmc (fs e)) , (λ e → hmc (bs e)))

      module FullUniqueness
        (H  : (v : ℕ) → Thread v → ZL v)
        (Hc : ∀ {v : ℕ} {τ τ' : Thread v}
            → τ ≈Thread τ'
            → EqOn._≈_ (≈ZL v) (H v τ) (H v τ'))
        (tr : (m v : ℕ) (t : M (A (NStage m)) (E (NStage m)) v)
            → _≈Mˢ_ (≈A Z) (≈E Z)
                     (FMapˢ.mapFˢ (FMˢ.mor (mkHFM H Hc)) v
                        (FMapˢ.mapFˢ (FMˢ.mor (legFM m)) v t))
                     (FMapˢ.mapFˢ (legF m) v t))
        where

        hFM : FMˢ L∞ Z
        hFM = mkHFM H Hc

        -- The stage-m triangle forces the head label at every thread.
        --
        -- 阶段 m 三角在每个线程处强制头标签。
        here-force : (m v : ℕ) (a : L m v)
                   → EqOn._≈_ (≈ZL v) (H v (mk m a)) (zm m v a)
        here-force m v a =
          _≈Mˢ_.here-eq (tr m v (stage-ray m v a))

        mutual
          uniq : (v : ℕ) (t : M (A L∞) (E L∞) v)
               → _≈Mˢ_ (≈A Z) (≈E Z)
                        (FMapˢ.mapFˢ (FMˢ.mor hFM) v t)
                        (FMapˢ.mapFˢ medF v t)
          uniq v t ._≈Mˢ_.here-eq with M.here t
          ... | mk m a = here-force m v a
          uniq v t ._≈Mˢ_.below-eq w =
              idAdjˢ (≈E Z v (H v (M.here t)) w)
            , ( (λ e₁ → uniq  w (M.below t w e₁))
              , (λ e₂ → uniq˘ w (M.below t w e₂)) )

          uniq˘ : (v : ℕ) (t : M (A L∞) (E L∞) v)
                → _≈Mˢ_ (≈A Z) (≈E Z)
                         (FMapˢ.mapFˢ medF v t)
                         (FMapˢ.mapFˢ (FMˢ.mor hFM) v t)
          uniq˘ v t ._≈Mˢ_.here-eq with M.here t
          ... | mk m a = EqOn.sym (≈ZL v) (here-force m v a)
          uniq˘ v t ._≈Mˢ_.below-eq w =
              idAdjˢ (≈E Z v (eval-ray (M.here t)) w)
            , ( (λ e₁ → uniq˘ w (M.below t w e₁))
              , (λ e₂ → uniq  w (M.below t w e₂)) )

        -- Full behavioural uniqueness of the identity-index mediator.
        --
        -- 索引恒等 mediate 的完整行为唯一性。
        unique-full : hFM ≈FM zmedFM
        unique-full v = refl , λ t → uniq v t

    --------------------------------------------------------------------
    -- Standard agda-categories Colimit of nchain in SameIndexCat
    --
    -- The stage systems and the apex are LabelSys over the fixed dynamics
    -- s∞; the embeddings and legs are Idx⇒ (definitionally identity
    -- index). A competing cocone supplies per-stage fibre maps zm and
    -- one-step coherence, which is exactly SameIndexMediate data; the
    -- mediator is eval-ray and FullUniqueness gives initiality on every
    -- total apex tree. This is the positive Colimit, confined to the
    -- identity-index wide subcategory where the polarity obstruction of
    -- Route 2 cannot arise.
    --
    -- SameIndexCat 中 nchain 的 agda-categories 标准 Colimit
    --
    -- 阶段系统与顶点是固定动力 s∞ 上的 LabelSys；嵌入与腿是 Idx⇒（定义性
    -- 索引恒等）。竞争余锥提供逐阶段纤维映射 zm 与一步相干性，恰为
    -- SameIndexMediate 数据；mediate 为 eval-ray，FullUniqueness 给出每棵
    -- 全总顶点树上的初始性。这是限制在索引恒等宽子范畴内的正面 Colimit，
    -- Route 2 的极性障碍在此不会出现。

    private
      cat = SameIndexCat s∞ {ℓ = ℓ}

      reflc : ∀ {X Y : LabelSys ℓ} {f : Idx⇒ s∞ X Y} → _≈i_ s∞ f f
      reflc {f = f} = ≈i-refl s∞ {ℓ = ℓ} f

      symc : ∀ {X Y : LabelSys ℓ} {f g : Idx⇒ s∞ X Y}
           → _≈i_ s∞ f g → _≈i_ s∞ g f
      symc {f = f} {g = g} p = ≈i-sym s∞ {ℓ = ℓ} {f = f} {g = g} p

      transc : ∀ {X Y : LabelSys ℓ} {f g h : Idx⇒ s∞ X Y}
             → _≈i_ s∞ f g → _≈i_ s∞ g h → _≈i_ s∞ f h
      transc {f = f} {g = g} {h = h} p q =
        ≈i-trans s∞ {ℓ = ℓ} {f = f} {g = g} {h = h} p q

      respc : ∀ {X Y Z : LabelSys ℓ}
                {F₁ F₂ : Idx⇒ s∞ X Y} {G₁ G₂ : Idx⇒ s∞ Y Z}
            → _≈i_ s∞ F₁ F₂ → _≈i_ s∞ G₁ G₂
            → _≈i_ s∞ (compi s∞ G₁ F₁) (compi s∞ G₂ F₂)
      respc {F₁ = F₁} {F₂ = F₂} {G₁ = G₁} {G₂ = G₂} p q =
        ∘-resp-≈i s∞ {ℓ = ℓ} {F₁ = F₁} {F₂ = F₂} {G₁ = G₁} {G₂ = G₂} p q

    stageLS : ℕ → LabelSys ℓ
    stageLS m = record { A₀ = L m ; ≈A₀ = λ v → propEqOn (L m v) }

    apexLS : LabelSys ℓ
    apexLS = record { A₀ = Thread ; ≈A₀ = ≈A∞ }

    embIdx : (m : ℕ) → Idx⇒ s∞ (stageLS m) (stageLS (suc m))
    embIdx m = record
      { shape      = λ v a → l-emb m v a
      ; shape-cong = λ {v} e → cong (l-emb m v) e
      }

    legIdx : (m : ℕ) → Idx⇒ s∞ (stageLS m) apexLS
    legIdx m = record
      { shape      = λ v a → mk m a
      ; shape-cong = λ {v} {a} {a'} e → leg-shc e
      }

    fold-emb : ∀ {m n : ℕ} → Chain⇒ m n
             → Idx⇒ s∞ (stageLS m) (stageLS n)
    fold-emb SQC.stop          = idxi s∞ (stageLS _)
    fold-emb (SQC.step {n = n} p) = compi s∞ (embIdx n) (fold-emb p)

    fold-hom : ∀ {m y n : ℕ} (g : Chain⇒ y n) (f : Chain⇒ m y)
             → _≈i_ s∞ (fold-emb (g ∘ch f))
                       (compi s∞ (fold-emb g) (fold-emb f))
    fold-hom {m} {y} {.y} SQC.stop f =
      symc {X = stageLS m} {Y = stageLS y}
           {f = compi s∞ (idxi s∞ (stageLS y)) (fold-emb f)}
           {g = fold-emb f}
           (reflc {f = compi s∞ (idxi s∞ (stageLS y)) (fold-emb f)})
    fold-hom {m} {y} {.(suc t)} (SQC.step {n = t} g) f =
      transc {X = stageLS m} {Y = stageLS (suc t)}
        {f = compi s∞ (embIdx t) (fold-emb (g ∘ch f))}
        {g = compi s∞ (embIdx t)
               (compi s∞ (fold-emb g) (fold-emb f))}
        {h = compi s∞ (compi s∞ (embIdx t) (fold-emb g)) (fold-emb f)}
        (respc {X = stageLS m} {Y = stageLS t} {Z = stageLS (suc t)}
           {F₁ = fold-emb (g ∘ch f)}
           {F₂ = compi s∞ (fold-emb g) (fold-emb f)}
           {G₁ = embIdx t} {G₂ = embIdx t}
           (fold-hom g f) (reflc {f = embIdx t}))
        (reflc {f = compi s∞ (embIdx t)
                  (compi s∞ (fold-emb g) (fold-emb f))})

    fold-resp-i : ∀ {m n : ℕ} {p q : Chain⇒ m n}
                → p ≡ q → _≈i_ s∞ (fold-emb p) (fold-emb q)
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
    open import Categories.Category.Construction.Cocones chainFun
      using (Cocones)
    open import Categories.Object.Initial Cocones
    open import Categories.Diagram.Colimit chainFun using (Colimit)

    -- One-step and path coherence of the canonical legs.
    --
    -- 规范腿的一步与路径相干性。
    one-coh-i : (m : ℕ)
              → _≈i_ s∞ (compi s∞ (legIdx (suc m)) (embIdx m)) (legIdx m)
    one-coh-i m v t = coh-go m v t

    leg-path : ∀ {m n : ℕ} (p : Chain⇒ m n)
             → _≈i_ s∞ (compi s∞ (legIdx n) (fold-emb p)) (legIdx m)
    leg-path {m} {.m} SQC.stop =
      reflc {f = compi s∞ (legIdx m) (idxi s∞ (stageLS m))}
    leg-path {m} {.(suc t)} (SQC.step {n = t} p) =
      transc {X = stageLS m} {Y = apexLS}
        {f = compi s∞ (legIdx (suc t))
               (compi s∞ (embIdx t) (fold-emb p))}
        {g = compi s∞ (compi s∞ (legIdx (suc t)) (embIdx t)) (fold-emb p)}
        {h = legIdx m}
        (reflc {f = compi s∞ (legIdx (suc t))
                  (compi s∞ (embIdx t) (fold-emb p))})
        (transc {X = stageLS m} {Y = apexLS}
           {f = compi s∞ (compi s∞ (legIdx (suc t)) (embIdx t)) (fold-emb p)}
           {g = compi s∞ (legIdx t) (fold-emb p)}
           {h = legIdx m}
           (respc {X = stageLS m} {Y = stageLS t} {Z = apexLS}
              {F₁ = fold-emb p} {F₂ = fold-emb p}
              {G₁ = compi s∞ (legIdx (suc t)) (embIdx t)} {G₂ = legIdx t}
              (reflc {f = fold-emb p}) (one-coh-i t))
           (leg-path p))

    nCocone : Cocone
    nCocone = record
      { coapex = record { ψ = legIdx ; commute = λ {m n} p → leg-path p } }

    -- Every restricted cocone factors uniquely through the apex.
    --
    -- 每个受限余锥唯一地经顶点因子分解。
    module _ (K : Cocone) where

      ψK : (m : ℕ) → Idx⇒ s∞ (stageLS m) (Cocone.N K)
      ψK = Cocone.ψ K

      private
        N  = Cocone.N K
        ZL = LabelSys.A₀ N
        ≈ZL = LabelSys.≈A₀ N

        zm : (m v : ℕ) → L m v → ZL v
        zm m v a = Idx⇒.shape (ψK m) v a

        zm-coh : (m v : ℕ) (a : L m v)
               → EqOn._≈_ (≈ZL v)
                   (zm (suc m) v (l-emb m v a)) (zm m v a)
        zm-coh m v a =
          _≈Mˢ_.here-eq
            (Cocone.commute K (SQC.succ {m = m}) v (stage-ray m v a))

      module Q = SameIndexMediate ZL ≈ZL zm zm-coh

      medArr : Idx⇒ s∞ apexLS N
      medArr = record
        { shape      = λ v τ → Q.eval-ray τ
        ; shape-cong = Q.med-shape-cong
        }

      med-comm : ∀ {m : ℕ}
               → _≈i_ s∞ (compi s∞ medArr (legIdx m)) (ψK m)
      med-comm {m} v t = Q.tri-go m v t

      mkMediate : Cocone⇒ nCocone K
      mkMediate = record { arr = medArr ; commute = λ {m} → med-comm {m} }

      unique : (f' : Cocone⇒ nCocone K)
             → _≈i_ s∞ medArr (Cocone⇒.arr f')
      unique f' = unique-i
        where
        farr : Idx⇒ s∞ apexLS N
        farr = Cocone⇒.arr f'

        H  : (v : ℕ) → Thread v → ZL v
        H = Idx⇒.shape farr

        Hc : ∀ {v : ℕ} {τ τ' : Thread v}
           → τ ≈Thread τ'
           → EqOn._≈_ (≈ZL v) (H v τ) (H v τ')
        Hc = Idx⇒.shape-cong farr

        -- Constructor form of farr; Idx⇒ eta makes farr ≡ farr′ and the
        -- latter unfolds under the category composition instead of
        -- staying stuck on the neutral Cocone⇒ projection.
        --
        -- farr 的构造式；Idx⇒ 的 eta 使 farr ≡ farr′，后者在范畴复合下
        -- 可归约，不会卡在中性的 Cocone⇒ 投影上。
        farr′ : Idx⇒ s∞ apexLS N
        farr′ = record { shape = H ; shape-cong = Hc }

        tr : (m v : ℕ) (t : M (A (NStage m)) (E (NStage m)) v)
           → _≈Mˢ_ (≈A (dsys s∞ N)) (≈E (dsys s∞ N))
                    (FMapˢ.mapFˢ (FMˢ.mor (Q.mkHFM H Hc)) v
                       (FMapˢ.mapFˢ (FMˢ.mor (legFM m)) v t))
                    (FMapˢ.mapFˢ (Q.legF m) v t)
        -- Re-home the neutral category composite (stuck on the Cocone⇒
        -- projection) onto the constructor composite, at the _≈i_ layer
        -- where identity/associativity are definitional; then read the
        -- triangle pointwise. Idx⇒ eta and the fact that mapF data depends
        -- only on the shape make both reindexings reflexive.
        --
        -- 在 _≈i_ 层（恒等/结合均定义性成立）把卡在 Cocone⇒ 投影上的中性
        -- 范畴复合归位到构造式复合，再逐点读取三角。Idx⇒ 的 eta 以及 mapF
        -- 数据只依赖 shape，使两处重索引均为自反。
        legEta : (m : ℕ)
               → _≈i_ s∞ (Cocone.ψ nCocone m) (legIdx m)
        legEta m = reflc {f = legIdx m}

        fEta : _≈i_ s∞ farr farr′
        fEta = reflc {f = farr′}

        -- commute reads  arr ∘ leg ≈ ψK  (composite on the left).
        --
        -- commute 读作 arr ∘ leg ≈ ψK（复合在左）。
        rdx : (m : ℕ)
            → _≈i_ s∞ (Category._∘_ cat farr (Cocone.ψ nCocone m))
                      (compi s∞ farr′ (legIdx m))
        rdx m = respc {X = stageLS m} {Y = apexLS} {Z = N}
                  {F₁ = Cocone.ψ nCocone m} {F₂ = legIdx m}
                  {G₁ = farr} {G₂ = farr′}
                  (legEta m) fEta

        tri : (m : ℕ)
            → _≈i_ s∞ (compi s∞ farr′ (legIdx m)) (ψK m)
        tri m =
          transc {X = stageLS m} {Y = N}
            {f = compi s∞ farr′ (legIdx m)}
            {g = Category._∘_ cat farr (Cocone.ψ nCocone m)}
            {h = ψK m}
            (symc {X = stageLS m} {Y = N}
               {f = Category._∘_ cat farr (Cocone.ψ nCocone m)}
               {g = compi s∞ farr′ (legIdx m)}
               (rdx m))
            (Cocone⇒.commute f' {m})

        tr m v t =
          ≈Mˢ-trans ≈AZ ≈EZ
            (≈Mˢ-trans ≈AZ ≈EZ c1 (≈Mˢ-sym ≈AZ ≈EZ c2))
            (≈Mˢ-trans ≈AZ ≈EZ (tri m v t) leg-b)
          where
          ≈AZ = ≈A (dsys s∞ N)
          ≈EZ = ≈E (dsys s∞ N)
          hmor = FMˢ.mor (Q.mkHFM H Hc)
          fmor = FMˢ.mor (legFM m)
          compFMor = compFˢ hmor fmor
          compImg = FMapˢ.mapFˢ (FMˢ.mor (Idx⇒.mor (compi s∞ farr′ (legIdx m)))) v t
          tgtImg = FMapˢ.mapFˢ (Q.legF m) v t

          -- Nested two-map image ≈ single composite image.
          --
          -- 嵌套两次 mapF 的像 ≈ 单一复合像。
          c1 : _≈Mˢ_ ≈AZ ≈EZ
                 (FMapˢ.mapFˢ hmor v (FMapˢ.mapFˢ fmor v t))
                 (FMapˢ.mapFˢ compFMor v t)
          c1 = ≈Mˢ-sym ≈AZ ≈EZ (mapFˢ-comp hmor fmor v t)

          -- compi fibre map and the kernel composite agree pointwise.
          --
          -- compi 纤维映射与内核复合逐点一致。
          c2 : _≈Mˢ_ ≈AZ ≈EZ compImg (FMapˢ.mapFˢ compFMor v t)
          c2 = ≈Mˢ-refl ≈AZ ≈EZ (FMapˢ.mapFˢ compFMor v t)

          leg-b : _≈Mˢ_ ≈AZ ≈EZ
                    (FMapˢ.mapFˢ (FMˢ.mor (Idx⇒.mor (ψK m))) v t) tgtImg
          leg-b = ≈Mˢ-refl ≈AZ ≈EZ tgtImg

        module QF = Q.FullUniqueness H Hc tr

        unique-i : _≈i_ s∞ medArr farr
        unique-i v t =
          ≈Mˢ-sym (≈A (dsys s∞ N)) (≈E (dsys s∞ N))
            (proj₂ (QF.unique-full v) t)

    nColimit : Colimit
    nColimit = record
      { initial = record
        { ⊥ = nCocone
        ; ⊥-is-initial = record
          { ! = λ {K} → mkMediate K
          ; !-unique = λ {K} f' → unique K f'
          }
        }
      }

    --------------------------------------------------------------------
    -- Route 2 (negative): the total-function Colimit is a pull notion
    --
    -- A perfectly valid competing push cocone may have a target index
    -- type not covered by the source trajectory. Take J = Nat ⊎ ⊤ with
    -- the extra point fixed under stepZ, and the trajectory q = inj₁;
    -- q (s∞ v) ≡ stepZ (q v) holds definitionally, so a forward
    -- simulation mediates (it never has to reach the extra point). But
    -- the mediating FMˢ demanded by the fixed IsColimitˢ would have
    -- index map q, which is not surjective: FMapˢ.childF forces every
    -- target index to have a source preimage, and inj₂ tt has none.
    -- Hence no total FMˢ mediate exists. The forward (push) colimit is
    -- the simulation of SameIndexMediate, not a total pull morphism.
    --
    -- 路线 2（否定性）：全函数余极限是 pull 概念
    --
    -- 完全合法的竞争 push 余锥其目标索引类型可以不被源轨迹覆盖。取
    -- J = ℕ ⊎ ⊤，额外点在 stepZ 下固定，轨迹 q = inj₁；q (s∞ v) ≡
    -- stepZ (q v) 定义性成立，故前向模拟可 mediate（永不需要到达额外
    -- 点）。但固定 IsColimitˢ 所要求的 mediate FMˢ 以 q 为索引映射，
    -- 而 q 不满：FMapˢ.childF 迫使每个目标索引都有源原像，inj₂ tt 无
    -- 原像。故不存在全函数 FMˢ mediate。前向（push）余极限是
    -- SameIndexMediate 的模拟，而非全函数 pull 态射。

    module ExtraPointObstruction where

      J : Set lzero
      J = ℕ ⊎ ⊤ {lzero}

      stepZ : J → J
      stepZ (inj₁ n) = inj₁ (s∞ n)
      stepZ (inj₂ _) = inj₂ tt

      q : ℕ → J
      q v = inj₁ v

      -- Trajectory coherence is definitional.
      --
      -- 轨迹相干性定义性成立。
      q-coh : (v : ℕ) → q (s∞ v) ≡ stepZ (q v)
      q-coh _ = refl

      -- Deterministic target system with trivial labels; the
      -- obstruction depends only on indices, hence holds a fortiori for
      -- any non-trivial label fibre.
      --
      -- 平凡标签的确定性目标系统；障碍只依赖索引，故对任意非平凡标签
      -- 纤维更成立。
      ZJ : SysEq lzero lzero lzero lzero lzero
      ZJ = record
        { I   = J
        ; A   = λ _ → ⊤ {lzero}
        ; E   = λ j _ j' → Σ (⊤ {lzero}) λ _ → j' ≡ stepZ j
        ; ≈A  = λ _ → propEqOn (⊤ {lzero})
        ; ≈E  = λ j _ j' → propEqOn (Σ (⊤ {lzero}) λ _ → j' ≡ stepZ j)
        }

      zj-orbit : (w : J) → M (A ZJ) (E ZJ) w
      zj-orbit w .M.here        = tt
      zj-orbit w .M.below w' _  = zj-orbit w'

      Rj : ℕ → J → Set lzero
      Rj v w = w ≡ q v

      Hj : (v : ℕ) (w : J) → Rj v w → Thread v → ⊤ {lzero} → Set lzero
      Hj _ _ _ _ _ = ⊤ {lzero}

      -- The forward simulation exists: it follows the inj₁ branch and
      -- never has to account for the unreachable inj₂ point.
      --
      -- 前向模拟存在：它沿 inj₁ 支推进，永不需要处理不可达的 inj₂ 点。
      medj : (v : ℕ)
           → PushSimˢ L∞ ZJ Rj Hj refl (orbit∞ v) (zj-orbit (q v))
      medj v .PushSimˢ.here-eq = tt
      medj v .PushSimˢ.push w (_ , eq) =
        q w , ((tt , cong inj₁ eq) , (refl , medj w))

      -- The extra point has no preimage under q.
      --
      -- 额外点在 q 下无原像。
      q-miss : ¬ Σ ℕ λ v → q v ≡ inj₂ tt
      q-miss (_ , ())

      -- No total FMˢ can mediate this cocone with index map q.
      --
      -- 不存在以 q 为索引映射的全函数 FMˢ mediate。
      no-FM-mediate : (g : FMˢ L∞ ZJ)
                    → ((x : ℕ) → FMapˢ.u (FMˢ.mor g) x ≡ q x)
                    → ⊥
      no-FM-mediate =
        no-FM-nonsurjective {X = L∞} {Y = ZJ}
          0 (M.here (orbit∞ 0)) q (inj₂ tt) q-miss
