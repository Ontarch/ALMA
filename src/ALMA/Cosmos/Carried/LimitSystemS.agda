------------------------------------------------------------------------
-- Trivial-fibre direct (co)limit system on setoid carried systems
--
-- With forward-simulation legs. Finite stages are trivial-fibre
-- deterministic systems on Fin (n-at m), n-at m = suc (suc m); the
-- coinductive limit is the trivial-fibre system on ℕ. Each stage leg is
-- a PushSimˢ along the graph of toℕ: the legs are forward simulations,
-- not pull morphisms (see ColimitPolarity). The deterministic limit is
-- unique up to the carried bisimulation _≈Mˢ_. The only equations are
-- homogeneous index/edge witnesses; no dependent transport, no K.
--
-- setoid 携带系统上的平凡纤维直接（余）极限系统
--
-- 腿为前向模拟。有限层是 Fin (n-at m)（n-at m = suc (suc m)）上的
-- 平凡纤维确定性系统；余归纳极限是 ℕ 上的平凡纤维系统。每条阶段腿
-- 是沿 toℕ 之图的 PushSimˢ：腿是前向模拟而非 pull 态射（见
-- ColimitPolarity）。确定性极限在携带互模拟 _≈Mˢ_ 意义下唯一。仅有
-- 的等式是同质索引/边见证；无依赖传输、不用 K。
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module ALMA.Cosmos.Carried.LimitSystemS where

open import Agda.Primitive using (Level; lzero)
open import Agda.Builtin.Sigma using (Σ; _,_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Nat.Base using (ℕ; zero; suc; _≤_)
open import Data.Nat.Properties using
  (≤-pred; ≤-refl; m≤n⇒m≤1+n; m≤n⇒m<n∨m≡n; n≤0⇒n≡0; m≥n⇒m⊓n≡n)
open import Data.Fin.Base using (Fin; zero; suc; toℕ; inject₁)
open import Data.Fin.Properties using (toℕ-injective; toℕ-inject₁; toℕ<n)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Unit.Polymorphic.Base using (⊤; tt)
open import Relation.Binary.PropositionalEquality.Core using (cong; trans; sym)

open import ALMA.Base.MCorr using (M)
open import ALMA.Base.MCorrSetoid using (SysEq; propEqOn; _≈Mˢ_; idAdjˢ)
open import ALMA.Base.MCorrSetoidPush using (PushSimˢ)
open import ALMA.Cosmos.Carried.FinProj using (clamp; clamp-val)

open SysEq

------------------------------------------------------------------------
-- Stage object-set size
--
-- n-at m = suc (suc m).
--
-- 每层对象集大小
--
-- n-at m = suc (suc m)。

n-at : ℕ → ℕ
n-at m = suc (suc m)

-- Canonical representative of v in stage v, always in range.
--
-- v 在第 v 层的典范代表，永远在范围内。
natToFin : (v : ℕ) → Fin (n-at v)
natToFin zero    = zero
natToFin (suc v) = suc (natToFin v)

toℕ-natToFin : (v : ℕ) → toℕ (natToFin v) ≡ v
toℕ-natToFin zero    = refl
toℕ-natToFin (suc v) = cong suc (toℕ-natToFin v)

------------------------------------------------------------------------
-- Trivial-fibre deterministic setoid system
--
-- One label, one position, edge fibre Σ ⊤ λ _ → y ≡ step x (singleton
-- at the successor).
--
-- 平凡纤维确定性 setoid 系统
--
-- 一个标签、一个位置，边纤维为 Σ ⊤ λ _ → y ≡ step x（后继处单点）。

TrivDetˢ : {i : Level} (I : Set i) (step : I → I)
         → SysEq i lzero i lzero i
TrivDetˢ {i = i} I step = record
  { I   = I
  ; A   = λ _ → ⊤ {lzero}
  ; E   = λ x _ y → Σ (⊤ {lzero}) λ _ → y ≡ step x
  ; ≈A  = λ _ → propEqOn (⊤ {lzero})
  ; ≈E  = λ { x _ y → propEqOn (Σ (⊤ {lzero}) λ _ → y ≡ step x) }
  }

------------------------------------------------------------------------
-- The limit system
--
-- Parameterised by the per-stage transition and the one-step embedding
-- compatibility (a homogeneous Fin equation).
--
-- 极限系统
--
-- 以各层转移与一步嵌入相容性（Fin 上的同质等式）为参数。

module LimitSystemS
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

  L∞ : SysEq lzero lzero lzero lzero lzero
  L∞ = TrivDetˢ ℕ s∞

  -- Child index y is carried by the edge, so the continuation is
  -- orbit y; no successor equation is matched.
  --
  -- 子索引 y 由边携带，故连续项即 orbit y；不匹配后继等式。
  orbit∞ : (x : ℕ) → M (A L∞) (E L∞) x
  orbit∞ x .M.here      = tt
  orbit∞ x .M.below y _ = orbit∞ y

  ----------------------------------------------------------------------
  -- Total clamp into stage m
  --
  -- In-range k ≤ suc m reads back as k.
  --
  -- 向第 m 层的全函数钳制
  --
  -- 范围内 k ≤ suc m 读数恰为 k。

  cl : (m k : ℕ) → Fin (n-at m)
  cl m k = clamp {k = suc m} k

  cl-toℕ : ∀ m k (le : k ≤ suc m) → toℕ (cl m k) ≡ k
  cl-toℕ m k le =
    trans (clamp-val {k = suc m} k) (m≥n⇒m⊓n≡n le)

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

  private
    read-cl : ∀ m k (le : k ≤ suc m) → toℕ (t m (cl m k)) ≡ s∞ k
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

  -- Every position present at stage m is read identically by s∞.
  --
  -- 第 m 层存在的每个位置都被 s∞ 恒等读取。
  read-coh : ∀ m (x : Fin (n-at m)) → toℕ (t m x) ≡ s∞ (toℕ x)
  read-coh m x =
    let le : toℕ x ≤ suc m
        le = ≤-pred (toℕ<n x)
        eqx : x ≡ cl m (toℕ x)
        eqx = toℕ-injective (sym (cl-toℕ m (toℕ x) le))
    in trans (cong toℕ (cong (t m) eqx))
             (read-cl m (toℕ x) le)

  ----------------------------------------------------------------------
  -- Stage legs as forward edge-following simulations along toℕ
  --
  -- 沿 toℕ 的前向边跟随模拟作为各阶段腿

  module Leg (m : ℕ) where

    Stage : SysEq lzero lzero lzero lzero lzero
    Stage = TrivDetˢ (Fin (n-at m)) (t m)

    orbit-fin : (x : Fin (n-at m)) → M (A Stage) (E Stage) x
    orbit-fin x .M.here      = tt
    orbit-fin x .M.below y _ = orbit-fin y

    Rₘ : Fin (n-at m) → ℕ → Set lzero
    Rₘ x v = toℕ x ≡ v

    Hₘ : (x : Fin (n-at m)) (v : ℕ) → Rₘ x v
       → A Stage x → A L∞ v → Set lzero
    Hₘ _ _ _ _ _ = ⊤ {lzero}

    leg : ∀ (x : Fin (n-at m)) (v : ℕ) (r : Rₘ x v)
        → PushSimˢ Stage L∞ Rₘ Hₘ r (orbit-fin x) (orbit∞ v)
    leg x v r .PushSimˢ.here-eq = tt
    leg x v r .PushSimˢ.push y (_ , eq) =
      s∞ v , ((tt , refl) , (r' , leg y (s∞ v) r'))
      where
        r' : toℕ y ≡ s∞ v
        r' = trans (cong toℕ eq)
                   (trans (read-coh m x) (cong s∞ r))

  ----------------------------------------------------------------------
  -- Uniqueness of the deterministic limit up to carried bisimulation
  --
  -- 确定性极限在携带互模拟意义下唯一

  det-unique : ∀ (x : ℕ) (t u : M (A L∞) (E L∞) x)
             → _≈Mˢ_ (≈A L∞) (≈E L∞) t u
  det-unique x t u ._≈Mˢ_.here-eq = refl
  det-unique x t u ._≈Mˢ_.below-eq y =
    idAdjˢ (≈E L∞ x (M.here u) y)
    , ( (λ e₁ → det-unique y (M.below t y e₁) (M.below u y e₁))
      , (λ e₂ → det-unique y (M.below u y e₂) (M.below t y e₂)) )
