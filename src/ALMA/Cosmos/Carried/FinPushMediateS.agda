------------------------------------------------------------------------
-- Universal property of the Fin push colimit among deterministic
-- setoid systems
--
-- The tower is deterministic (one edge per node), so a competing
-- cocone is a deterministic system (TrivDetˢ J stepZ) with an index
-- trajectory q satisfying q (s∞ v) ≡ stepZ (q v). The mediating
-- forward simulation med follows the unique edges, generalised to an
-- arbitrary target index and graph witness. Its target tree is the
-- unique deterministic tree up to _≈Mˢ_.
--
-- Fin push 余极限在确定性 setoid 系统中的泛性质
--
-- 塔是确定性的（每节点一条边），故竞争余锥即一个确定性系统
-- （TrivDetˢ J stepZ）连同满足 q (s∞ v) ≡ stepZ (q v) 的索引轨迹 q。
-- mediate 前向模拟沿唯一边推进，并泛化到任意目标索引与图见证。其目标
-- 树在 _≈Mˢ_ 意义下唯一。
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module ALMA.Cosmos.Carried.FinPushMediateS where

open import Agda.Primitive using (Level; lzero)
open import Agda.Builtin.Sigma using (_,_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Nat.Base using (ℕ; suc)
open import Data.Fin.Base using (Fin; inject₁)
open import Data.Unit.Polymorphic.Base using (⊤; tt)
open import Relation.Binary.PropositionalEquality.Core using (cong; trans; sym)

open import ALMA.Base.MCorr using (M)
open import ALMA.Base.MCorrSetoid using (SysEq; _≈Mˢ_; idAdjˢ)
open import ALMA.Base.MCorrSetoidPush using (PushSimˢ)
open import ALMA.Cosmos.Carried.LimitSystemS using (TrivDetˢ; n-at)
import ALMA.Cosmos.Carried.LimitSystemS as LS

open SysEq

module Mediate
  (t : (m : ℕ) → Fin (n-at m) → Fin (n-at m))
  (embed-compat : (m : ℕ) (x : Fin (n-at m))
                → t (suc m) (inject₁ x) ≡ inject₁ (t m x))
  where

  open LS.LimitSystemS t embed-compat using (s∞; orbit∞; L∞)

  ----------------------------------------------------------------------
  -- A competing deterministic cocone
  --
  -- A target deterministic system on J with transition stepZ and an
  -- index trajectory q over the source dynamics s∞.
  --
  -- 竞争确定性余锥
  --
  -- J 上以 stepZ 为转移的目标确定性系统，以及覆盖源动力 s∞ 的索引轨迹
  -- q。

  module Cocone
    {j : Level} (J : Set j) (stepZ : J → J)
    (q : ℕ → J)
    (q-coh : (v : ℕ) → q (s∞ v) ≡ stepZ (q v))
    where

    Z : SysEq j lzero j lzero j
    Z = TrivDetˢ J stepZ

    -- Deterministic orbit in Z.
    --
    -- Z 中的确定性轨道。
    orbitZ : (w : J) → M (A Z) (E Z) w
    orbitZ w .M.here = tt
    orbitZ w .M.below w' (_ , eq) = orbitZ w'

    -- Layer relation: the target index is the q-image of the source.
    --
    -- 层关系：目标索引为源索引的 q 像。
    R : ℕ → J → Set j
    R v w = w ≡ q v

    H : (v : ℕ) (w : J) → R v w
      → A L∞ v → A Z w → Set lzero
    H _ _ _ _ _ = ⊤ {lzero}

    -- The mediating forward simulation, generalised to an arbitrary
    -- target index w with graph witness r.
    --
    -- mediate 前向模拟，泛化到带图见证 r 的任意目标索引 w。
    med : (v : ℕ) (w : J) (r : w ≡ q v)
        → PushSimˢ L∞ Z R H r (orbit∞ v) (orbitZ w)
    med v w r .PushSimˢ.here-eq = tt
    med v w r .PushSimˢ.push y (_ , eq) =
      stepZ w , ((tt , refl) , (r' , med y (stepZ w) r'))
      where
        -- stepZ w ≡ q y, from the graph witness r, the source edge and
        -- the cocone coherence.
        --
        -- stepZ w ≡ q y，由图见证 r、源边与余锥相容式得到。
        r' : stepZ w ≡ q y
        r' = trans (cong stepZ r)
              (trans (sym (q-coh v)) (sym (cong q eq)))

    -- The canonical mediating simulation at the q-image of each node.
    --
    -- 每个节点 q 像处的规范 mediate 模拟。
    mediate : (v : ℕ)
            → PushSimˢ L∞ Z R H refl (orbit∞ v) (orbitZ (q v))
    mediate v = med v (q v) refl

    --------------------------------------------------------------------
    -- Uniqueness
    --
    -- The deterministic Z-tree at w is unique up to _≈Mˢ_. The
    -- mediating simulation has no branch to choose; its layer and label
    -- witnesses are propositions.
    --
    -- 唯一性
    --
    -- w 处的确定性 Z-树在 _≈Mˢ_ 意义下唯一；mediate 模拟无分支可选，
    -- 其层与标签见证均为命题。
    det-unique-Z : (w : J) (u₁ u₂ : M (A Z) (E Z) w)
                 → _≈Mˢ_ (≈A Z) (≈E Z) u₁ u₂
    det-unique-Z w u₁ u₂ ._≈Mˢ_.here-eq = refl
    det-unique-Z w u₁ u₂ ._≈Mˢ_.below-eq w' =
      idAdjˢ (≈E Z w (M.here u₂) w') ,
        ( (λ e₁ → det-unique-Z w' (M.below u₁ w' e₁) (M.below u₂ w' e₁))
        , (λ e₂ → det-unique-Z w' (M.below u₂ w' e₂) (M.below u₁ w' e₂))
        )
