------------------------------------------------------------------------
-- Non-trivial fibre inverse (pull / limit) system on identity-index
-- carried functors
--
-- The push tower only carries labels forward (l-emb). A cochain needs a
-- backward arrow, so an inverse system adds l-proj, the retraction of
-- l-emb on the already-born part (proj-emb : l-proj ∘ l-emb ≡ id).
-- Every arrow keeps the global id, hence is an identity-index Idx⇒ and
-- the construction lives in SameIndexCatS: the limit fibre carries
-- a pointwise setoid.
--
-- 同索引携带函子上的非平凡纤维逆向（pull / limit）系统
--
-- push 塔只向前携带标签（l-emb）。余链需要反向箭头，故逆向系统加入
-- l-proj，即 l-emb 在已诞生部分上的收缩
-- （proj-emb：l-proj ∘ l-emb ≡ id）。每条箭头保持全局 id，因而是索引
-- 恒等的 Idx⇒，构造落在 SameIndexCatS 中：极限纤维携带逐点 setoid。
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module ALMA.Cosmos.Carried.NontrivialPullTowerS where

open import Agda.Primitive using (Level; lzero; lsuc)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Sigma using (Σ; _,_)
open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Unit.Polymorphic.Base using (⊤; tt)
open import Data.Empty.Polymorphic using (⊥; ⊥-elim)
import Data.Empty
open import Relation.Nullary.Negation using (¬_)
open import Relation.Binary.PropositionalEquality.Core using (cong; sym; trans; _≢_)

open import Categories.Category.Core using (Category)
open import Categories.Functor using (Functor)

open import ALMA.Base.MCorr using (M)
open import ALMA.Base.MCorrSetoid using (SysEq; EqOn; propEqOn; idAdjˢ; _≈Mˢ_)
open import ALMA.Base.MCorrSetoidCat using (FMapˢ; FMˢ)
open import ALMA.Cosmos.Carried.SameIndexCatS using
  (LabelSys; dsys; Idx⇒; idxi; compi; _≈i_; SameIndexCat; ≈i-refl; ≈i-trans; ∘-resp-≈i)
open import ALMA.Cosmos.Carried.SeqColimitCat using (Chain⇒; stop; step; ωCat)
import ALMA.Cosmos.Carried.SeqColimitCat as SQC

open SysEq

------------------------------------------------------------------------
-- Inverse system of non-trivial label fibres
--
-- 非平凡标签纤维的逆向系统

record LabeledInverseTower (ℓ : Level) : Set (lsuc ℓ) where
  field
    d        : ℕ → ℕ
    L        : (m v : ℕ) → Set ℓ
    l-emb    : (m v : ℕ) → L m v → L (suc m) v
    l-proj   : (m v : ℕ) → L (suc m) v → L m v
    proj-emb : (m v : ℕ) (a : L m v) → l-proj m v (l-emb m v a) ≡ a

module PullTower {ℓ : Level} (T : LabeledInverseTower ℓ) where

  open LabeledInverseTower T

  private
    s = d
    sYS = dsys s

  -- Stage label family (propositional fibre setoid).
  --
  -- 阶段标签族（命题纤维 setoid）。
  stageLS : ℕ → LabelSys ℓ
  stageLS m = record
    { A₀  = L m
    ; ≈A₀ = λ v → propEqOn (L m v)
    }

  ----------------------------------------------------------------------
  -- Pointwise equality of two fibre maps into a propositional-fibre
  -- family
  --
  -- Written as a pointwise label-tree bisimulation. The source label
  -- family may carry any setoid; only the target is propositional. Both
  -- maps are identity-index, so the child index and child tree coincide:
  -- the head is the given equation and the children recurse guardedly.
  --
  -- 两个进入命题纤维族的纤维映射逐点相等
  --
  -- 写成逐点标签树互模拟。源标签族可带任意 setoid，仅目标为命题的。
  -- 两映射索引恒等，故子节点索引与子树重合：头部为所给等式，子节点
  -- 守卫递归。

  module _ (X : LabelSys ℓ) (Q : ℕ → Set ℓ) where
    private
      YQ : LabelSys ℓ
      YQ = record { A₀ = Q ; ≈A₀ = λ v → propEqOn (Q v) }
      sx = sYS X
      sy = sYS YQ
      edgeEQ : (v w : ℕ) → Set lzero
      edgeEQ v w = Σ (⊤ {lzero}) λ _ → w ≡ s v
      fmap : ((v : ℕ) → LabelSys.A₀ X v → Q v) → FMapˢ sx sy
      fmap sh = record
        { u      = λ z → z
        ; shape  = sh
        ; childF = λ z _ w → w , refl
        ; adjFˢ  = λ z _ w → idAdjˢ (propEqOn (edgeEQ z w))
        }
      img : ((v : ℕ) → LabelSys.A₀ X v → Q v)
          → (v : ℕ) → M (A sx) (E sx) v → M (A sy) (E sy) v
      img sh v t = FMapˢ.mapFˢ (fmap sh) v t

    pointwise→≈i
      : (shf shg : (v : ℕ) → LabelSys.A₀ X v → Q v)
      → ((v : ℕ) (a : LabelSys.A₀ X v) → shf v a ≡ shg v a)
      → (v : ℕ) (t : M (A sx) (E sx) v)
      → _≈Mˢ_ (≈A sy) (≈E sy) (img shf v t) (img shg v t)
    pointwise→≈i shf shg eq v t = go v t
      where
      edgeAdj : (v w : ℕ) → _
      edgeAdj v w = idAdjˢ (propEqOn (edgeEQ v w))
      mutual
        go : (v : ℕ) (u : M (A sx) (E sx) v)
           → _≈Mˢ_ (≈A sy) (≈E sy) (img shf v u) (img shg v u)
        go v u ._≈Mˢ_.here-eq = eq v (M.here u)
        go v u ._≈Mˢ_.below-eq w =
            edgeAdj v w
          , ( (λ e → go w (M.below u w e))
            , (λ e → go˘ w (M.below u w e)) )

        go˘ : (v : ℕ) (u : M (A sx) (E sx) v)
            → _≈Mˢ_ (≈A sy) (≈E sy) (img shg v u) (img shf v u)
        go˘ v u ._≈Mˢ_.here-eq = EqOn.sym (≈A sy v) (eq v (M.here u))
        go˘ v u ._≈Mˢ_.below-eq w =
            edgeAdj v w
          , ( (λ e → go˘ w (M.below u w e))
            , (λ e → go w (M.below u w e)) )

  ----------------------------------------------------------------------
  -- Generalised pointwise lifting
  --
  -- Head equations in the target's own setoid (any setoid, not only a
  -- propositional fibre) give morphism bisimilarity; child trees recurse
  -- guardedly along the identity index.
  --
  -- 广义逐点提升
  --
  -- 目标自身 setoid（任意 setoid，不限于命题纤维）中的头部等式给出
  -- 态射互模拟；子树沿恒等索引守卫递归。

  pointwise-i : {X Y : LabelSys ℓ} (f g : Idx⇒ s X Y)
    → (∀ (v : ℕ) (a : LabelSys.A₀ X v)
        → EqOn._≈_ (LabelSys.≈A₀ Y v)
                    (Idx⇒.shape f v a) (Idx⇒.shape g v a))
    → _≈i_ s f g
  pointwise-i {X = X} {Y = Y} f g eq v t = go v t
    where
    sx = sYS X
    sy = sYS Y
    edgeAdj : (v w : ℕ) → _
    edgeAdj v w =
      idAdjˢ (propEqOn (Σ (⊤ {lzero}) λ _ → w ≡ s v))
    mutual
      go : (v : ℕ) (u : M (A sx) (E sx) v)
         → _≈Mˢ_ (≈A sy) (≈E sy)
                  (FMapˢ.mapFˢ (FMˢ.mor (Idx⇒.mor f)) v u)
                  (FMapˢ.mapFˢ (FMˢ.mor (Idx⇒.mor g)) v u)
      go v u ._≈Mˢ_.here-eq = eq v (M.here u)
      go v u ._≈Mˢ_.below-eq w =
        edgeAdj v w
          , ( (λ e → go w (M.below u w e))
            , (λ e → go˘ w (M.below u w e)) )

      go˘ : (v : ℕ) (u : M (A sx) (E sx) v)
          → _≈Mˢ_ (≈A sy) (≈E sy)
                   (FMapˢ.mapFˢ (FMˢ.mor (Idx⇒.mor g)) v u)
                   (FMapˢ.mapFˢ (FMˢ.mor (Idx⇒.mor f)) v u)
      go˘ v u ._≈Mˢ_.here-eq =
        EqOn.sym (≈A sy v) (eq v (M.here u))
      go˘ v u ._≈Mˢ_.below-eq w =
        edgeAdj v w
          , ( (λ e → go˘ w (M.below u w e))
            , (λ e → go w (M.below u w e)) )

  ----------------------------------------------------------------------
  -- Forward embedding and backward restriction (the cochain arrow)
  --
  -- 前向嵌入与反向限制（余链箭头）

  embIdx : (m : ℕ) → Idx⇒ s (stageLS m) (stageLS (suc m))
  embIdx m = record
    { shape      = λ v a → l-emb m v a
    ; shape-cong = λ e → cong (l-emb m _) e
    }

  resIdx : (m : ℕ) → Idx⇒ s (stageLS (suc m)) (stageLS m)
  resIdx m = record
    { shape      = λ v b → l-proj m v b
    ; shape-cong = λ e → cong (l-proj m _) e
    }

  -- Retraction triangle: restriction after embedding is the identity.
  --
  -- 收缩三角：嵌入后限制为恒等。
  res-emb : (m : ℕ)
          → _≈i_ s (compi s (resIdx m) (embIdx m)) (idxi s (stageLS m))
  res-emb m =
    pointwise→≈i (stageLS m) (L m)
      (λ v a → l-proj m v (l-emb m v a))
      (λ v a → a)
      (λ v a → proj-emb m v a)

  ----------------------------------------------------------------------
  -- Limit apex
  --
  -- A compatible family of stage labels at each global id. Equality is
  -- pointwise over stages (a setoid), so uniqueness of the mediating
  -- morphism needs no function extensionality and no K.
  --
  -- 极限顶点
  --
  -- 每个全局 id 处阶段标签的相容族。相等按阶段逐点给出（一个 setoid），
  -- 故 mediate 态射的唯一性既不需函数外延性也不用 K。
  record LimLabel (v : ℕ) : Set ℓ where
    field
      at  : (m : ℕ) → L m v
      coh : (m : ℕ) → l-proj m v (at (suc m)) ≡ at m
  open LimLabel

  apex≈ : (v : ℕ) → EqOn (LimLabel v)
  apex≈ v = record
    { _≈_ = λ a b → (m : ℕ) → at a m ≡ at b m
    ; isEquivalence = record
      { refl  = λ m → refl
      ; sym   = λ h m → sym (h m)
      ; trans = λ h k m → trans (h m) (k m)
      }
    }

  apexLS : LabelSys ℓ
  apexLS = record
    { A₀  = LimLabel
    ; ≈A₀ = apex≈
    }

  -- Projection legs: read the stage-m component of the compatible
  -- family.
  --
  -- 投影锥腿：读取相容族的阶段 m 分量。
  projLeg : (m : ℕ) → Idx⇒ s apexLS (stageLS m)
  projLeg m = record
    { shape      = λ v a → at a m
    ; shape-cong = λ h → h m
    }

  -- Limit cone coherence: resIdx m ∘ projLeg (m+1) ≈ projLeg m.
  --
  -- 极限锥相干：resIdx m ∘ projLeg (m+1) ≈ projLeg m。
  cone-coh : (m : ℕ)
    → _≈i_ s (compi s (resIdx m) (projLeg (suc m))) (projLeg m)
  cone-coh m =
    pointwise→≈i apexLS (L m)
      (λ v a → l-proj m v (at a (suc m)))
      (λ v a → at a m)
      (λ v a → coh a m)

  ----------------------------------------------------------------------
  -- The cochain is the ω-chain functor on the opposite shape category
  --
  -- An ω^op arrow m→n is a forward path Chain⇒ n m, mapped to iterated
  -- restrictions from stage m down to stage n.
  --
  -- 余链即对偶形状范畴上的 ω 链函子
  --
  -- ω^op 箭头 m→n 是一条前向路径 Chain⇒ n m，被映为从阶段 m 向下到
  -- 阶段 n 的迭代限制。
  private
    cat = SameIndexCat s {ℓ = ℓ}

    reflc : ∀ {X Y : LabelSys ℓ} {f : Idx⇒ s X Y} → _≈i_ s f f
    reflc {f = f} = ≈i-refl s {ℓ = ℓ} f

    transc : ∀ {X Y : LabelSys ℓ} {f g h : Idx⇒ s X Y}
           → _≈i_ s f g → _≈i_ s g h → _≈i_ s f h
    transc {f = f} {g = g} {h = h} p q =
      ≈i-trans s {ℓ = ℓ} {f = f} {g = g} {h = h} p q

    respc : ∀ {X Y Z : LabelSys ℓ}
              {F₁ F₂ : Idx⇒ s X Y} {G₁ G₂ : Idx⇒ s Y Z}
          → _≈i_ s F₁ F₂ → _≈i_ s G₁ G₂
          → _≈i_ s (compi s G₁ F₁) (compi s G₂ F₂)
    respc {F₁ = F₁} {F₂ = F₂} {G₁ = G₁} {G₂ = G₂} p q =
      ∘-resp-≈i s {ℓ = ℓ} {F₁ = F₁} {F₂ = F₂} {G₁ = G₁} {G₂ = G₂} p q

  -- Iterated restriction along a backward path.
  --
  -- 沿反向路径迭代限制。
  fold-res : {n m : ℕ} → Chain⇒ n m → Idx⇒ s (stageLS m) (stageLS n)
  fold-res stop            = idxi s (stageLS _)
  fold-res (step {n = k} p) = compi s (fold-res p) (resIdx k)

  -- Folding a composite path is composing the folded restrictions.
  --
  -- 折叠复合路径等于复合折叠后的限制。
  fold-res-comp : {x y z : ℕ} (f : Chain⇒ y x) (g : Chain⇒ z y)
    → _≈i_ s (fold-res (f SQC.∘ch g))
             (compi s (fold-res g) (fold-res f))
  fold-res-comp {y = y} {z = z} f g = go f
    where
    go : ∀ {k : ℕ} (p : Chain⇒ y k)
       → _≈i_ s (fold-res (p SQC.∘ch g))
                (compi s (fold-res g) (fold-res p))
    go stop =
      reflc {X = stageLS y} {Y = stageLS z} {f = fold-res g}
    go (step {n = k} p) =
      transc {X = stageLS (suc k)} {Y = stageLS z}
        {f = compi s (fold-res (p SQC.∘ch g)) (resIdx k)}
        {g = compi s (compi s (fold-res g) (fold-res p)) (resIdx k)}
        {h = compi s (fold-res g) (compi s (fold-res p) (resIdx k))}
        (respc {X = stageLS (suc k)} {Y = stageLS k} {Z = stageLS z}
               {F₁ = resIdx k} {F₂ = resIdx k}
               {G₁ = fold-res (p SQC.∘ch g)}
               {G₂ = compi s (fold-res g) (fold-res p)}
               (reflc {X = stageLS (suc k)} {Y = stageLS k}
                      {f = resIdx k})
               (go p))
        (reflc {X = stageLS (suc k)} {Y = stageLS z}
               {f = compi s (fold-res g)
                            (compi s (fold-res p) (resIdx k))})

  private
    ωOp : Category lzero lzero lzero
    ωOp = Category.op ωCat

    subst-resp : ∀ {n m} {p q : Chain⇒ n m} → p ≡ q
               → _≈i_ s (fold-res p) (fold-res q)
    subst-resp {n = n} {m = m} {p = p} refl =
      reflc {X = stageLS m} {Y = stageLS n} {f = fold-res p}

  cochainFun : Functor ωOp cat
  cochainFun = record
    { F₀          = stageLS
    ; F₁          = λ {A} {B} p → fold-res p
    ; identity    = reflc {f = idxi s (stageLS _)}
    ; homomorphism = λ {X} {Y} {Z} {f} {g} → fold-res-comp f g
    ; F-resp-≈    = λ {_ _ p q} eq → subst-resp {p = p} {q = q} eq
    }

  -- Path-level cone coherence: F₁ p ∘ projLeg m ≈ projLeg n.
  --
  -- 路径级锥相干：F₁ p ∘ projLeg m ≈ projLeg n。
  projPath : {n m : ℕ} (p : Chain⇒ n m)
    → _≈i_ s (compi s (fold-res p) (projLeg m)) (projLeg n)
  projPath {n = n} stop =
    reflc {X = apexLS} {Y = stageLS n}
          {f = compi s (idxi s (stageLS n)) (projLeg n)}
  projPath {n = n} (step {n = k} p) =
    transc {X = apexLS} {Y = stageLS n}
      {f = compi s (compi s (fold-res p) (resIdx k)) (projLeg (suc k))}
      {g = compi s (fold-res p) (projLeg k)}
      {h = projLeg n}
      (respc {X = apexLS} {Y = stageLS k} {Z = stageLS n}
             {F₁ = compi s (resIdx k) (projLeg (suc k))}
             {F₂ = projLeg k}
             {G₁ = fold-res p} {G₂ = fold-res p}
             (cone-coh k)
             (reflc {X = stageLS k} {Y = stageLS n} {f = fold-res p}))
      (projPath p)

  open import Categories.Diagram.Cone cochainFun

  -- The limit cone: apex LimLabel, projections projLeg.
  --
  -- 极限锥：顶点 LimLabel，投影 projLeg。
  nCone : Cone
  nCone = record
    { apex = record
      { ψ       = projLeg
      ; commute = λ {X} {Y} f → projPath f
      }
    }

  ----------------------------------------------------------------------
  -- Pointwise (strong) pull limit
  --
  -- Cone coherence is a pointwise head equation, readable at a single
  -- label: no total tree, no transport. The compatible-family apex is
  -- terminal among such cones; mediator uniqueness is the pointwise
  -- apex setoid (no function extensionality).
  --
  -- 逐点（强）pull 极限
  --
  -- 锥相干是逐点头部等式，可在单个标签处读出，无需全总树、无传输。
  -- 相容族顶点在此类锥中终；mediate 唯一性为顶点逐点 setoid（无需函数
  -- 外延）。
  module PLimit where

    -- A pointwise pull cone over N.
    --
    -- N 上的逐点 pull 锥。
    record PCone (N : LabelSys ℓ) : Set (lsuc ℓ) where
      field
        ψ   : (m : ℕ) → Idx⇒ s N (stageLS m)
        coh : (m : ℕ) (v : ℕ) (a : LabelSys.A₀ N v)
            → l-proj m v (Idx⇒.shape (ψ (suc m)) v a)
            ≡ Idx⇒.shape (ψ m) v a
    open PCone public

    -- Pointwise head equality of two identity-index morphisms.
    --
    -- 两个同索引态射的逐点头部相等。
    _≈h_ : {X Y : LabelSys ℓ} (f g : Idx⇒ s X Y) → Set ℓ
    _≈h_ {X = X} f g =
      (v : ℕ) (a : LabelSys.A₀ X v)
      → Idx⇒.shape f v a ≡ Idx⇒.shape g v a

    -- The canonical pointwise limit cone.
    --
    -- 规范逐点极限锥。
    nPCone : PCone apexLS
    nPCone = record
      { ψ   = projLeg
      ; coh = λ m v a → coh a m
      }

    -- Leg heads form a compatible family, hence a mediator into apex.
    --
    -- 各腿头部构成相容族，从而给出进入顶点的 mediate。
    mediate : {N : LabelSys ℓ} (K : PCone N) → Idx⇒ s N apexLS
    mediate K = record
      { shape      = λ v a → record
        { at  = λ m → Idx⇒.shape (ψ K m) v a
        ; coh = λ m → coh K m v a
        }
      ; shape-cong = λ {v} {a} {b} e m →
                       Idx⇒.shape-cong (ψ K m) e
      }

    -- Factorisation: projLeg m ∘ mediate ≈h ψ K m, definitionally.
    --
    -- 因子分解：projLeg m ∘ mediate 逐点等于 ψ K m，定义性成立。
    triangle : {N : LabelSys ℓ} (K : PCone N) (m : ℕ)
             → _≈h_ (compi s (projLeg m) (mediate K)) (ψ K m)
    triangle K m v a = refl

    -- Uniqueness in the pointwise apex setoid.
    --
    -- 顶点逐点 setoid 下的唯一性。
    unique : {N : LabelSys ℓ} (h : Idx⇒ s N apexLS) (K : PCone N)
           → ((m : ℕ) → _≈h_ (compi s (projLeg m) h) (ψ K m))
           → (v : ℕ) (a : LabelSys.A₀ N v)
           → EqOn._≈_ (LabelSys.≈A₀ apexLS v)
                       (Idx⇒.shape h v a)
                       (Idx⇒.shape (mediate K) v a)
    unique h K ht v a m = ht m v a

    -- A pointwise cone over an inhabited point supplies a compatible
    -- thread through the tower. Contrapositive: a point with no thread
    -- cannot be the apex of a pointwise cone with a label there -- the
    -- structural obstruction to a pull limit (zero transport).
    --
    -- 有人点上的逐点锥给出一条穿过塔的相容线程。逆否：无线程点不可能在
    -- 该处带标签地成为逐点锥顶点——pull 极限的结构性障碍（零传输）。
    cone-thread : {N : LabelSys ℓ} (K : PCone N) (v : ℕ)
                (a : LabelSys.A₀ N v) → LimLabel v
    cone-thread K v a = Idx⇒.shape (mediate K) v a

  ----------------------------------------------------------------------
  -- Pull dual obstruction (negative)
  --
  -- If the root 0 has no compatible thread through the tower, the
  -- bisimulation limit cone is not terminal. Take a dead apex labelled
  -- only at 0 (everywhere else empty). No total label-tree is rooted
  -- anywhere, so the bisimulation cone commute is vacuously true
  -- regardless of the leg heads; yet a mediator into the limit apex
  -- would have to produce a LimLabel at 0, which is empty. Hypotheses:
  -- every stage is inhabited at 0, the dynamics leaves 0, and no
  -- compatible thread exists there.
  --
  -- pull 对偶障碍（否定性）
  --
  -- 若根 0 没有穿过塔的相容线程，则双模拟极限锥非终。取仅在 0 有标签
  -- （余处皆空）的死顶点：任何地方都没有全总标签树，故双模拟锥相干与腿
  -- 头部无关地空洞成立；但进入极限顶点的 mediate 必须在 0 处给出
  -- LimLabel，而其为空。假设：各阶段在 0 处有人、动力离开 0、该处无
  -- 相容线程。
  module NoThreadObstruction
    (b     : (m : ℕ) → L m 0)
    (d0≢0  : s 0 ≢ 0)
    (no-thread : ¬ LimLabel 0)
    where

    -- Fibre of the dead apex: inhabited only at 0.
    --
    -- 死顶点的纤维：仅在 0 处有人。
    deadA : ℕ → Set ℓ
    deadA zero    = ⊤ {ℓ}
    deadA (suc _) = ⊥ {ℓ}

    -- Dead apex: labelled only at 0.
    --
    -- 死顶点：仅在 0 处有标签。
    Ndead : LabelSys ℓ
    Ndead = record
      { A₀  = deadA
      ; ≈A₀ = λ w → propEqOn (deadA w)
      }

    private sysN = sYS Ndead

    noA0 : (w : ℕ) → w ≢ 0 → deadA w → ⊥ {ℓ}
    noA0 zero   ne tt = Data.Empty.⊥-elim (ne refl)
    noA0 (suc _) _ ()

    -- No total label-tree is rooted at any index.
    --
    -- 任何索引处都没有全总标签树。
    no-tree : (w : ℕ) → M (A sysN) (E sysN) w → ⊥ {ℓ}
    no-tree zero t =
      noA0 (s 0) d0≢0 (M.here (M.below t (s 0) (tt , refl)))
    no-tree (suc _) t = ⊥-elim (M.here t)

    -- Leg heads exist at 0 (b) and are impossible elsewhere.
    --
    -- 腿头部在 0 处为 b，余处不可能。
    legShape : (m w : ℕ) → deadA w → L m w
    legShape m zero tt = b m
    legShape m (suc _) ()

    legCong : (m : ℕ) {w : ℕ} {a a' : deadA w}
            → a ≡ a' → legShape m w a ≡ legShape m w a'
    legCong m {zero} {tt} {tt} refl = refl
    legCong m {suc _} {()}

    ψK : (m : ℕ) → Idx⇒ s Ndead (stageLS m)
    ψK m = record { shape = legShape m ; shape-cong = legCong m }

    -- Any two morphisms out of the dead apex are bisimulation-equal,
    -- since the pointwise quantification is over no trees.
    --
    -- 从死顶点出发的任意两个态射互模拟相等，因逐点量化的树集为空。
    vacuous-i : {Y : LabelSys ℓ} (f g : Idx⇒ s Ndead Y) → _≈i_ s f g
    vacuous-i f g w t with no-tree w t
    ... | ()

    -- A perfectly valid bisimulation cone over the dead apex.
    --
    -- 死顶点上完全合法的双模拟锥。
    deadCone : Cone
    deadCone = record
      { apex = record
        { ψ       = ψK
        ; commute = λ {X} {Y} f →
                      vacuous-i (compi s (fold-res f) (ψK X)) (ψK Y)
        }
      }

    -- No mediator from the dead cone into the canonical limit cone:
    -- its head at 0 would be a compatible thread, assumed absent.
    --
    -- 不存在从死锥到规范极限锥的 mediate：其在 0 处的头部将是一条相容
    -- 线程，而假设其不存在。
    no-mediate : Cone⇒ deadCone nCone → ⊥ {ℓ}
    no-mediate mk =
      Data.Empty.⊥-elim
        (no-thread (Idx⇒.shape (Cone⇒.arr mk) 0 tt))

  ----------------------------------------------------------------------
  -- Standard limit, conditionally
  --
  -- A bisimulation cone whose apex carries a total label-tree at every
  -- label admits a unique Cone⇒ into the canonical limit cone. The ray
  -- is needed only to read the pointwise head coherence off the
  -- bisimulation commute; the factorisation and uniqueness then lift by
  -- pointwise-i (no ray).
  --
  -- 条件性标准极限
  --
  -- 若一个双模拟锥的顶点在每个标签处都带一棵全总标签树，则存在进入规范
  -- 极限锥的唯一 Cone⇒。射线仅用于从双模拟 commute 读出逐点头部相干；
  -- 因子分解与唯一性随后由 pointwise-i 提升（无需射线）。
  module StandardLimit where

    open PLimit

    -- The op-arrow from stage m+1 back to stage m.
    --
    -- 从阶段 m+1 回到阶段 m 的 op 箭头。
    private res-arrow : ∀ {m} → SQC.Chain⇒ m (suc m)
            res-arrow = SQC.step SQC.stop

    module _ (K : Cone)
             (tree : (v : ℕ) (a : LabelSys.A₀ (Cone.N K) v)
                   → M (A (sYS (Cone.N K))) (E (sYS (Cone.N K))) v)
             (tree-here : (v : ℕ) (a : LabelSys.A₀ (Cone.N K) v)
                        → M.here (tree v a) ≡ a)
      where

      private Nk  = Cone.N K
              ψk  = Cone.ψ K

      -- Move a head equation from the tree root M.here (tree v a) to
      -- the prescribed label a along the root equation.
      --
      -- 沿根等式把头部等式从树根 M.here (tree v a) 搬到指定标签 a。
      private
        relocate : {Q : Set ℓ} (v : ℕ)
                   (f g : LabelSys.A₀ Nk v → Q)
                   (a : LabelSys.A₀ Nk v)
                 → f (M.here (tree v a)) ≡ g (M.here (tree v a))
                 → f a ≡ g a
        relocate v f g a h0 =
          trans (cong f (sym (tree-here v a)))
                (trans h0 (cong g (tree-here v a)))

      -- Read the restriction coherence as a head equation.
      --
      -- 将限制相干读为头部等式。
      kcoh : (m : ℕ) (v : ℕ) (a : LabelSys.A₀ Nk v)
           → l-proj m v (Idx⇒.shape (ψk (suc m)) v a)
           ≡ Idx⇒.shape (ψk m) v a
      kcoh m v a =
        relocate v
          (λ x → l-proj m v (Idx⇒.shape (ψk (suc m)) v x))
          (Idx⇒.shape (ψk m) v) a
          (_≈Mˢ_.here-eq
            (Cone.commute K {X = suc m} {Y = m} res-arrow
                          v (tree v a)))

      Kpc : PCone Nk
      Kpc = record { ψ = ψk ; coh = kcoh }

      -- The unique mediator and its cone factorisation.
      --
      -- 唯一 mediate 及其锥因子分解。
      mediate-i : Idx⇒ s Nk apexLS
      mediate-i = mediate Kpc

      !K : Cone⇒ K nCone
      !K = record
        { arr     = mediate-i
        ; commute = λ {X} →
                      pointwise-i (compi s (projLeg X) mediate-i) (ψk X)
                                  (triangle Kpc X)
        }

      -- Any other mediator is bisimulation-equal to mediate-i.
      --
      -- 任何其他 mediate 与 mediate-i 互模拟相等。
      !K-unique : (h : Cone⇒ K nCone)
                → _≈i_ s (Cone⇒.arr h) mediate-i
      !K-unique h =
        pointwise-i (Cone⇒.arr h) mediate-i
          (unique (Cone⇒.arr h) Kpc
            (λ X v a →
              relocate v
                (Idx⇒.shape (compi s (projLeg X) (Cone⇒.arr h)) v)
                (Idx⇒.shape (ψk X) v) a
                (_≈Mˢ_.here-eq
                  (Cone⇒.commute h {X = X} v (tree v a)))))
