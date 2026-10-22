------------------------------------------------------------------------
-- Canonical push cocone for the Fin tower on setoid carried systems
--
-- The one-step stage embedding inject₁ is a forward PushSim (not a pull
-- morphism); the canonical legs carry each finite stage into the
-- coinductive ℕ limit L∞ of LimitSystemS along the graph of toℕ. Each
-- leg factors through the embedding: the composite (emb-sim followed by
-- the next leg) is rescoped by the pure witness combinators push-comp
-- and push-map to a leg over the direct graph relation. The mediating
-- simulation for a competing cocone and its uniqueness are constructed
-- separately.
--
-- setoid 携带系统上 Fin 塔的规范 push 余锥
--
-- 一步层嵌入 inject₁ 是前向 PushSim（非 pull 态射）；规范腿沿 toℕ 之图
-- 把每个有限层送入 LimitSystemS 的余归纳 ℕ 极限 L∞。每条腿经嵌入分解：
-- 复合（emb-sim 再接下一层腿）由纯见证组合子 push-comp、push-map 重定域
-- 为直接图关系上的腿。竞争余锥的 mediate 模拟及其唯一性另行构造。
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module Cosmos.Carried.FinPushColimitS where

open import Agda.Primitive using (lzero)
open import Agda.Builtin.Sigma using (_,_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Nat.Base using (ℕ; suc)
open import Data.Fin.Base using (Fin; inject₁; toℕ)
open import Data.Fin.Properties using (toℕ-inject₁)
open import Data.Unit.Polymorphic.Base using (⊤; tt)
open import Relation.Binary.PropositionalEquality.Core using (cong; trans; sym)

open import Base.MCorr using (M; _⍮_)
open import Base.MCorr.Setoid using (SysEq)
open import Base.MCorr.SetoidPush using (PushSimˢ)
open import Base.MCorr.SetoidPushComp using (H∘G; push-comp)
open import Base.MCorr.SetoidPushMap using (push-map)
open import Cosmos.Carried.LimitSystemS using (TrivDetˢ; n-at)
import Cosmos.Carried.LimitSystemS as LS

open SysEq

module PushColimit
  (t : (m : ℕ) → Fin (n-at m) → Fin (n-at m))
  (embed-compat :
     (m : ℕ) (x : Fin (n-at m))
   → t (suc m) (inject₁ x) ≡ inject₁ (t m x))
  where

  open LS.LimitSystemS t embed-compat

  ----------------------------------------------------------------------
  -- Stage systems and their deterministic orbits
  --
  -- 各阶段系统及其确定性轨道

  Stage : ℕ → SysEq lzero lzero lzero lzero lzero
  Stage m = TrivDetˢ (Fin (n-at m)) (t m)

  orbit-fin : (m : ℕ) (x : Fin (n-at m))
            → M (A (Stage m)) (E (Stage m)) x
  orbit-fin m x .M.here      = tt
  orbit-fin m x .M.below y _ = orbit-fin m y

  ----------------------------------------------------------------------
  -- The one-step embedding inject₁ as a forward simulation
  --
  -- 一步嵌入 inject₁ 作为前向模拟

  R-emb : (m : ℕ) → Fin (n-at m) → Fin (n-at (suc m)) → Set lzero
  R-emb m x y = inject₁ x ≡ y

  H-emb : (m : ℕ) (x : Fin (n-at m)) (y : Fin (n-at (suc m)))
        → R-emb m x y → A (Stage m) x → A (Stage (suc m)) y → Set lzero
  H-emb _ _ _ _ _ _ = ⊤ {lzero}

  emb-sim : (m : ℕ) (x : Fin (n-at m))
          → PushSimˢ (Stage m) (Stage (suc m)) (R-emb m) (H-emb m)
                      refl (orbit-fin m x) (orbit-fin (suc m) (inject₁ x))
  emb-sim m x .PushSimˢ.here-eq = tt
  emb-sim m x .PushSimˢ.push y (_ , eq) =
    inject₁ y , ((tt , edge) , (refl , emb-sim m y))
    where
      edge : inject₁ y ≡ t (suc m) (inject₁ x)
      edge = trans (cong inject₁ eq) (sym (embed-compat m x))

  ----------------------------------------------------------------------
  -- Canonical stage legs into the ℕ limit
  --
  -- Along the graph of toℕ.
  --
  -- 进入 ℕ 极限的规范阶段腿
  --
  -- 沿 toℕ 之图。

  Rₘ : (m : ℕ) → Fin (n-at m) → ℕ → Set lzero
  Rₘ m x v = toℕ x ≡ v

  Hₘ : (m : ℕ) (x : Fin (n-at m)) (v : ℕ)
      → Rₘ m x v → A (Stage m) x → A L∞ v → Set lzero
  Hₘ _ _ _ _ _ _ = ⊤ {lzero}

  legₘ : (m : ℕ) (x : Fin (n-at m)) (v : ℕ) (r : Rₘ m x v)
       → PushSimˢ (Stage m) L∞ (Rₘ m) (Hₘ m)
                   r (orbit-fin m x) (orbit∞ v)
  legₘ m x v r .PushSimˢ.here-eq = tt
  legₘ m x v r .PushSimˢ.push y (_ , eq) =
    s∞ v , ((tt , refl) , (r' , legₘ m y (s∞ v) r'))
    where
      r' : toℕ y ≡ s∞ v
      r' = trans (cong toℕ eq)
                 (trans (read-coh m x) (cong s∞ r))

  ----------------------------------------------------------------------
  -- Cocone compatibility
  --
  -- The leg at stage m is the embedding followed by the leg at stage
  -- m+1, rescoped to the direct graph witness.
  --
  -- 余锥相容性
  --
  -- 第 m 层腿等于先嵌入再接第 m+1 层腿，重定域到直接图见证。

  module _ (m : ℕ) where
    private
      Rc = R-emb m ⍮ Rₘ (suc m)
      Hc = H∘G {X = Stage m} {Y = Stage (suc m)} {Z = L∞}
               (R-emb m) (Rₘ (suc m)) (H-emb m) (Hₘ (suc m))

    -- Project the composite layer witness (inject₁ x, refl, r) to the
    -- direct witness r; normalises to r since toℕ ∘ inject₁ is
    -- identity.
    --
    -- 把复合层见证（inject₁ x, refl, r）投影为直接见证 r；因
    -- toℕ ∘ inject₁ 为恒等而归一为 r。
    fR : ∀ {x : Fin (n-at m)} {v : ℕ} → Rc x v → Rₘ m x v
    fR {x = x} (y , e , r₁) =
      trans (sym (toℕ-inject₁ x)) (trans (cong toℕ e) r₁)

    fH : ∀ {x : Fin (n-at m)} {v : ℕ} (w : Rc x v)
           {a : A (Stage m) x} {c : A L∞ v}
       → Hc x v w a c → Hₘ m x v (fR w) a c
    fH _ _ = tt

    -- The factored leg lives at the projected witness fR w, a (possibly
    -- non-definitional) proof of the same graph proposition Rₘ m x v.
    --
    -- 因子分解腿停在投影见证 fR w 处，即同一图命题 Rₘ m x v 的一个
    -- （未必定义性的）证明。
    leg-factor : (x : Fin (n-at m)) (v : ℕ) (r : Rₘ m x v)
               → PushSimˢ (Stage m) L∞ (Rₘ m) (Hₘ m)
                   (fR {x = x} {v = v}
                       (inject₁ x , refl , trans (toℕ-inject₁ x) r))
                   (orbit-fin m x) (orbit∞ v)
    leg-factor x v r =
      push-map Rc (Rₘ m) Hc (Hₘ m) fR fH
        (push-comp (R-emb m) (Rₘ (suc m)) (H-emb m) (Hₘ (suc m))
                   (emb-sim m x)
                   (legₘ (suc m) (inject₁ x) v
                         (trans (toℕ-inject₁ x) r)))
