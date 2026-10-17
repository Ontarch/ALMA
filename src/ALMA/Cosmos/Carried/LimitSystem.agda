------------------------------------------------------------------------
-- Carried limit system for the FinCat tower -- existence core
--
-- Zero subst. Finite stages are trivial-fibre deterministic systems on
-- Fin (n-at m), n-at m = suc (suc m); the coinductive limit L∞ is the
-- trivial-fibre system on ℕ. The only real datum is the deterministic
-- position transition, eliminated at the defining site:
--   s∞ v = toℕ (t v (natToFin v)),
-- with natToFin v always in range since n-at v > v. The coinductive
-- orbit is written in edge-indexed style, so recursion never matches
-- the successor equation and never transports.
--
-- FinCat 塔的携带式极限系统 —— 存在性核心
--
-- 零 subst。有限层是 Fin (n-at m)（n-at m = suc (suc m)）上的平凡纤维
-- 确定性系统；余归纳极限 L∞ 是 ℕ 上的平凡纤维系统。唯一真实数据是确定
-- 性位置转移，并在定义点即被消除：
--   s∞ v = toℕ (t v (natToFin v))，
-- 因 n-at v > v，natToFin v 永远在范围内。余归纳轨道以边索引风格书写，
-- 故递归绝不匹配后继等式、绝不传输。
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module ALMA.Cosmos.Carried.LimitSystem where

open import Agda.Primitive using (Level; lzero; _⊔_)
open import Agda.Builtin.Sigma using (Σ; _,_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Nat using (ℕ; zero; suc; _≤_; _<_; z≤n; s≤s)
open import Data.Nat.Properties using
  (≤-pred; ≤-refl; m≤n⇒m≤1+n; m≤n⇒m<n∨m≡n; n≤0⇒n≡0; m≥n⇒m⊓n≡n)
open import Data.Fin.Base using (Fin; zero; suc; toℕ; inject₁)
open import Data.Fin.Properties using (toℕ-injective; toℕ-inject₁; toℕ<n)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Unit.Polymorphic.Base using (⊤; tt)
open import Relation.Binary.PropositionalEquality.Core using (cong; trans; sym)

open import ALMA.Base.MCorr using (Sys; M; here; below; _≈M_; idAdj)
open Sys
open import ALMA.Cosmos.Carried.DetSys
open import ALMA.Cosmos.Carried.SeqColimit using (shift)
open import ALMA.Cosmos.Carried.FinProj using (clamp; clamp-val)

------------------------------------------------------------------------
-- Size of the object set of FinCatN m
--
-- n-at m = suc (suc m).
--
-- FinCatN m 对象集的大小
--
-- n-at m = suc (suc m)。

n-at : ℕ → ℕ
n-at m = suc (suc m)

-- Total, Cubical-safe strict dichotomy
--
-- No decidable / Bool-backed predicate is matched.
--
-- 全函数、Cubical 安全严格二分
--
-- 不匹配可判定 / Bool 支撑的谓词。
≤-or-> : ∀ (h k : ℕ) → (k ≤ h) ⊎ (h < k)
≤-or-> h       zero    = inj₁ z≤n
≤-or-> zero    (suc k) = inj₂ (s≤s z≤n)
≤-or-> (suc h) (suc k) with ≤-or-> h k
... | inj₁ p = inj₁ (s≤s p)
... | inj₂ p = inj₂ (s≤s p)

-- Canonical representative of natural position v in stage v
--
-- Always in range because n-at v > v.
--
-- 自然位置 v 在第 v 层的典范代表
--
-- 因 n-at v > v 而永远在范围内。
natToFin : (v : ℕ) → Fin (n-at v)
natToFin zero    = zero
natToFin (suc v) = suc (natToFin v)

toℕ-natToFin : (v : ℕ) → toℕ (natToFin v) ≡ v
toℕ-natToFin zero    = refl
toℕ-natToFin (suc v) = cong suc (toℕ-natToFin v)

-- Target size uses the same `shift` recursion as the carried chain
--
-- n-at (shift d m) reduces definitionally -- no subst Fin (+-suc), no
-- castCosmos.
--
-- 目标尺寸用与携带链相同的 `shift` 递归
--
-- n-at (shift d m) 定义性归约——无 subst Fin (+-suc)、无 castCosmos。
embFin : (d m : ℕ) → Fin (n-at m) → Fin (n-at (shift d m))
embFin zero    m x = x
embFin (suc d) m x = embFin d (suc m) (inject₁ x)

toℕ-embFin : ∀ d m (x : Fin (n-at m))
           → toℕ (embFin d m x) ≡ toℕ x
toℕ-embFin zero    m x = refl
toℕ-embFin (suc d) m x =
  trans (toℕ-embFin d (suc m) (inject₁ x)) (toℕ-inject₁ x)

-- Total clamp into Fin (n-at m)
--
-- For in-range k ≤ suc m its toℕ reading is exactly k. ℕ-recursive: no
-- Fin indexed pattern match, no absurd pattern on ≤ proofs.
--
-- 向 Fin (n-at m) 的全函数 clamp
--
-- 范围内 k ≤ suc m 时其 toℕ 读数恰为 k。ℕ 递归：无 Fin 索引模式匹配、
-- 无对 ≤ 证明的空模式。
cl : (m k : ℕ) → Fin (n-at m)
cl m k = clamp {k = suc m} k

cl-toℕ : ∀ m k (le : k ≤ suc m) → toℕ (cl m k) ≡ k
cl-toℕ m k le =
  trans (clamp-val {k = suc m} k) (m≥n⇒m⊓n≡n le)

------------------------------------------------------------------------
-- Push (forward / embedding) edge-following simulation
--
-- MCorr's Step / FMap are pull notions; a colimit leg points the other
-- way, from a finite stage into the limit. PushSim is the forward dual:
-- for every source edge it carries a target edge, a fresh index
-- correspondence and the child simulation; no totality over target
-- indices. Everything is carried data; no subst / cast.
--
-- 前向（push / 嵌入）边跟随互模拟
--
-- MCorr 的 Step / FMap 是 pull 概念；余极限腿方向相反，从有限层指向
-- 极限。PushSim 是其前向对偶：对每条源边携带一条目标边、一条新索引对应
-- 与子互模拟；不对目标索引要求满。一切皆携带数据；无 subst / cast。

record PushSim {i j a b c d ℓr ℓh : Level}
              {X : Sys i a b} {Y : Sys j c d}
              (R : I X → I Y → Set ℓr)
              (H : (x : I X) (v : I Y)
                 → R x v → A X x → A Y v → Set ℓh)
              {x : I X} {v : I Y} (r : R x v)
              (t : M (A X) (E X) x)
              (u : M (A Y) (E Y) v)
              : Set (i ⊔ j ⊔ a ⊔ b ⊔ c ⊔ d ⊔ ℓr ⊔ ℓh)
              where
  coinductive
  field
    here-eq : H x v r (here t) (here u)
    push : (y : I X) (e : E X x (here t) y)
         → Σ (I Y) λ w
           → Σ (E Y v (here u) w) λ e'
           → Σ (R y w) λ r'
           → PushSim {i = i} {j = j} {a = a} {b = b}
                     {c = c} {d = d} {ℓr = ℓr} {ℓh = ℓh}
                     {X = X} {Y = Y}
                     R H r' (below t y e) (below u w e')
open PushSim public

------------------------------------------------------------------------
-- The limit system
--
-- Parameterised by the per-stage transition
-- t m : Fin (n-at m) → Fin (n-at m) and the one-step embedding
-- compatibility, a bare homogeneous equation on Fin.
--
-- 极限系统
--
-- 以各层转移 t m : Fin (n-at m) → Fin (n-at m) 与一步嵌入相容性
-- （Fin 上的裸同质等式）为参数。

module LimitSystem
  (t : (m : ℕ) → Fin (n-at m) → Fin (n-at m))
  (embed-compat :
     (m : ℕ) (x : Fin (n-at m))
   → t (suc m) (inject₁ x) ≡ inject₁ (t m x))
  where

  -- Read at the stage that always contains v.
  --
  -- 在永远包含 v 的第 v 层读取。
  s∞ : ℕ → ℕ
  s∞ v = toℕ (t v (natToFin v))

  open TrivDet {i = lzero} ℕ s∞
    using (sys; DetM)

  L∞ = sys

  -- Child index y is carried by e, so the continuation is orbit y -- no
  -- successor equation is matched, and the call is guarded directly by
  -- `below`.
  --
  -- 子索引 y 由 e 携带，故连续项就是 orbit y —— 不匹配后继等式，递归
  -- 调用直接由 below 保护。
  orbit∞ : (x : ℕ) → DetM x
  orbit∞ x .here      = tt
  orbit∞ x .below y _ = orbit∞ y

  ----------------------------------------------------------------------
  -- In-range reading coherence
  --
  -- Every position present at stage m is read by s∞. The split
  -- "inherited vs new top" is the bounded disjunction
  -- k ≤ suc m → k < suc m ⊎ k ≡ suc m, not the unbounded ≤-total
  -- threshold.
  --
  -- 范围内读数相干性
  --
  -- 第 m 层存在的每个位置都被 s∞ 正确读取。拆分“继承 vs 新末位”是
  -- 有界析取 k ≤ suc m → k < suc m ⊎ k ≡ suc m，不是无界 ≤-total
  -- 阈值。

  private
    up-toℕ : ∀ m x → toℕ (t (suc m) (inject₁ x)) ≡ toℕ (t m x)
    up-toℕ m x =
      trans (cong toℕ (embed-compat m x)) (toℕ-inject₁ (t m x))

    inj-clamp : ∀ p k (le : k ≤ suc p)
              → cl (suc p) k ≡ inject₁ (cl p k)
    inj-clamp p k le =
      toℕ-injective
        (trans (cl-toℕ (suc p) k (m≤n⇒m≤1+n le))
          (sym (trans (toℕ-inject₁ (cl p k))
                      (cl-toℕ p k le))))

    inj-top : ∀ s → inject₁ (cl s (suc s)) ≡ natToFin (suc s)
    inj-top s =
      toℕ-injective
        (trans (trans (toℕ-inject₁ (cl s (suc s)))
                      (cl-toℕ s (suc s) ≤-refl))
               (sym (toℕ-natToFin (suc s))))

  top-read : ∀ s → toℕ (t s (cl s (suc s))) ≡ s∞ (suc s)
  top-read s =
    sym
      (trans (cong toℕ (cong (t (suc s)) (sym (inj-top s))))
        (trans (cong toℕ (embed-compat s (cl s (suc s))))
               (toℕ-inject₁ (t s (cl s (suc s))))))

  read-cl : ∀ m k (le : k ≤ suc m)
          → toℕ (t m (cl m k)) ≡ s∞ k
  read-cl zero k le
    with m≤n⇒m<n∨m≡n le
  ... | inj₂ eq rewrite eq = top-read zero
  ... | inj₁ lt rewrite n≤0⇒n≡0 (≤-pred lt) = refl
  read-cl (suc p) k le
    with m≤n⇒m<n∨m≡n le
  ... | inj₂ eq rewrite eq = top-read (suc p)
  ... | inj₁ lt =
    let le' : k ≤ suc p
        le' = ≤-pred lt
    in trans (cong toℕ (cong (t (suc p)) (inj-clamp p k le')))
             (trans (up-toℕ p (cl p k))
                    (read-cl p k le'))

  read-coh : ∀ m (x : Fin (n-at m))
           → toℕ (t m x) ≡ s∞ (toℕ x)
  read-coh m x =
    let le : toℕ x ≤ suc m
        le = ≤-pred (toℕ<n x)
        eqx : x ≡ cl m (toℕ x)
        eqx = toℕ-injective (sym (cl-toℕ m (toℕ x) le))
    in trans (cong toℕ (cong (t m) eqx))
             (read-cl m (toℕ x) le)

  ----------------------------------------------------------------------
  -- Colimit legs as push edge-following simulations
  --
  -- Each stage's deterministic orbit pushes to the limit orbit along
  -- the graph of toℕ. The single source edge is matched by the single
  -- limit edge, and read-coh carries the required index correspondence.
  --
  -- 余极限腿：前向边跟随互模拟
  --
  -- 每层确定性轨道沿 toℕ 的图前推到极限轨道。唯一源边对应唯一极限边，
  -- read-coh 携带所需索引对应。

  module Leg (m : ℕ) where
    open TrivDet {i = lzero} (Fin (n-at m)) (t m)
      renaming (DetM to DetMₘ)

    orbit-fin : (x : Fin (n-at m)) → DetMₘ x
    orbit-fin x .here      = tt
    orbit-fin x .below y _ = orbit-fin y

    Rₘ : Fin (n-at m) → ℕ → Set lzero
    Rₘ x v = toℕ x ≡ v

    Hₘ : (x : Fin (n-at m)) (v : ℕ)
       → Rₘ x v → ⊤ {lzero} → ⊤ {lzero} → Set lzero
    Hₘ _ _ _ _ _ = ⊤ {lzero}

    -- General over the limit index v and the carried graph witness.
    --
    -- 对极限索引 v 与携带的图见证一般化。
    leg : ∀ (x : Fin (n-at m)) (v : ℕ) (r : Rₘ x v)
        → PushSim {i = lzero} {j = lzero}
                  {a = lzero} {b = lzero}
                  {c = lzero} {d = lzero}
                  {ℓr = lzero} {ℓh = lzero}
                  Rₘ Hₘ r (orbit-fin x) (orbit∞ v)
    leg x v r .here-eq = tt
    leg x v r .push y (_ , eq) =
      s∞ v , ((tt , refl) , (r' , leg y (s∞ v) r'))
      where
        r' : toℕ y ≡ s∞ v
        r' = trans (cong toℕ eq)
                   (trans (read-coh m x) (cong s∞ r))

  ----------------------------------------------------------------------
  -- Uniqueness of the deterministic limit up to bisimulation
  --
  -- The trivial fibre has a unique label and a unique successor edge at
  -- every node. The two below-eq directions are bare guarded
  -- corecursive calls with the trees given in opposite argument order.
  --
  -- 确定性极限在互模拟意义下的唯一性
  --
  -- 平凡纤维在每个节点有唯一标签与唯一后继边。below-eq 两个方向均为
  -- 裸受保护余归纳调用，两棵树以相反参数顺序给出。

  det-unique : ∀ (x : ℕ) (t u : DetM x) → t ≈M u
  det-unique x t u ._≈M_.here-eq = refl
  det-unique x t u ._≈M_.below-eq y =
    idAdj (Sys.E L∞ x (here u) y) ,
      ( (λ e₁ → det-unique y (below t y e₁) (below u y e₁))
      , (λ e₂ → det-unique y (below u y e₂) (below t y e₂)) )
