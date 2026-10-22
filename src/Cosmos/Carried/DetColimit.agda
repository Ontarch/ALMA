------------------------------------------------------------------------
-- Universal property of the deterministic trivial-fibre tower colimit
--
-- LimitSystem supplies the apex L∞, the forward edge-following legs
-- Leg.leg, and det-unique; this slice closes the universal property
-- with mediate / triangle / uniqueness.
--
-- 确定性平凡纤维塔余极限的泛性质
--
-- LimitSystem 已提供顶点 L∞、前向边跟随腿 Leg.leg 与 det-unique；
-- 本切片用 mediate / triangle / uniqueness 闭合泛性质。
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module Cosmos.Carried.DetColimit where

open import Agda.Primitive using (lzero)
open import Agda.Builtin.Sigma using (_,_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Nat using (ℕ; suc)
open import Data.Fin.Base using (Fin; toℕ; inject₁)
open import Data.Unit.Polymorphic.Base using (⊤; tt)
open import Relation.Binary.PropositionalEquality.Core using (trans; cong)

open import Base.MCorr using (here; below; _≈M_)
open import Cosmos.Carried.DetSys
open import Cosmos.Carried.LimitSystem using (n-at; PushSim; module LimitSystem)

------------------------------------------------------------------------
-- Deterministic colimit of a compatible tower of finite trivial
-- endofunctions, parameterised exactly as LimitSystem
--
-- 相容有限平凡自函数塔的确定性余极限，参数与 LimitSystem 一致

module DetColimit
  (t : (m : ℕ) → Fin (n-at m) → Fin (n-at m))
  (embed-compat :
     (m : ℕ) (x : Fin (n-at m))
   → t (suc m) (inject₁ x) ≡ inject₁ (t m x))
  where

  open LimitSystem t embed-compat
    using (s∞; L∞; orbit∞; det-unique; module Leg)

  open TrivDet {i = lzero} ℕ s∞ renaming (DetM to DetM∞)

  ----------------------------------------------------------------------
  -- mediate
  --
  -- Apex L∞, leg at stage m is Leg.leg at the natural reading toℕ x
  -- with graph witness refl.
  --
  -- mediate
  --
  -- 顶点 L∞，第 m 层的腿即在自然读数 toℕ x 处、以 refl 为图见证的
  -- Leg.leg。

  mediate-apex = L∞

  mediate-leg : (m : ℕ) (x : Fin (n-at m))
    → PushSim {i = lzero} {j = lzero}
              {a = lzero} {b = lzero}
              {c = lzero} {d = lzero}
              {ℓr = lzero} {ℓh = lzero}
              (Leg.Rₘ m) (Leg.Hₘ m) refl
              (Leg.orbit-fin m x) (orbit∞ (toℕ x))
  mediate-leg m x = Leg.leg m x (toℕ x) refl

  ----------------------------------------------------------------------
  -- Competing cocone apex
  --
  -- A trivial-fibre deterministic system on ℕ with transition sZ whose
  -- stage-v leg agrees with the limit reading. Stage v always contains
  -- v, so agreement is exactly sZ v ≡ s∞ v.
  --
  -- 竞争余锥顶点
  --
  -- ℕ 上转移为 sZ 的平凡纤维确定性系统，其第 v 层腿与极限读数一致。
  -- 第 v 层永远包含 v，故相容恰为 sZ v ≡ s∞ v。

  record DetCoconeApex : Set where
    field
      sZ      : ℕ → ℕ
      leg-coh : ∀ v → sZ v ≡ s∞ v
  open DetCoconeApex

  ----------------------------------------------------------------------
  -- triangle
  --
  -- The apex orbit pushes to the L∞ orbit along the identity index
  -- graph.
  --
  -- triangle
  --
  -- 顶点轨道沿恒等索引图前推到 L∞ 轨道。

  module _ (apex : DetCoconeApex) where
    private
      stepZ = sZ apex
      lc = leg-coh apex

      open TrivDet {i = lzero} ℕ stepZ
        renaming (sys to sysZ; DetM to DetMZ)

      R≡ : ℕ → ℕ → Set lzero
      R≡ x v = x ≡ v

      H⊤ : (x v : ℕ) → R≡ x v
         → ⊤ {lzero} → ⊤ {lzero} → Set lzero
      H⊤ _ _ _ _ _ = ⊤ {lzero}

      orbitZ : (x : ℕ) → DetMZ x
      orbitZ x .here      = tt
      orbitZ x .below y _ = orbitZ y

    -- Must stay general in both indices and in r: the guarded
    -- continuation recurses at the source child y, which equals stepZ x
    -- and only becomes s∞ v after r and leg-coh are carried through.
    --
    -- 必须对两个索引与 r 一般化：受保护连续项在源子节点 y 处递归，
    -- y 等于 stepZ x，只有在穿过 r 与 leg-coh 后才成为 s∞ v。
    factor-push : ∀ (x v : ℕ) (r : R≡ x v)
      → PushSim {i = lzero} {j = lzero}
                {a = lzero} {b = lzero}
                {c = lzero} {d = lzero}
                {ℓr = lzero} {ℓh = lzero}
                {X = sysZ} {Y = L∞}
                R≡ H⊤ r (orbitZ x) (orbit∞ v)
    factor-push x v r .PushSim.here-eq = tt
    factor-push x v r .PushSim.push y (tt , eq) =
      s∞ v ,
        ( (tt , refl)
        , ( r'
          , factor-push y (s∞ v) r' )
        )
      where
        -- y ≡ stepZ x ≡ stepZ v ≡ s∞ v, carrying r then leg-coh.
        --
        -- y ≡ stepZ x ≡ stepZ v ≡ s∞ v，先后穿过 r 与 leg-coh。
        r' : R≡ y (s∞ v)
        r' = trans eq (trans (cong stepZ r) (lc v))

    triangle : ∀ (v : ℕ)
      → PushSim {i = lzero} {j = lzero}
                {a = lzero} {b = lzero}
                {c = lzero} {d = lzero}
                {ℓr = lzero} {ℓh = lzero}
                {X = sysZ} {Y = L∞}
                R≡ H⊤ refl (orbitZ v) (orbit∞ v)
    triangle v = factor-push v v refl

  ----------------------------------------------------------------------
  -- uniqueness
  --
  -- At the transition level the leg coherence is by definition
  -- sZ v ≡ s∞ v; at the tree level det-unique pins any two L∞ trees at
  -- the same index.
  --
  -- 唯一性
  --
  -- 转移层腿相容按定义即 sZ v ≡ s∞ v；树层 det-unique 钉住同一索引处
  -- 任意两棵 L∞ 树。

  factor-transition : (apex : DetCoconeApex)
    → ∀ v → sZ apex v ≡ s∞ v
  factor-transition apex = leg-coh apex

  factor-unique : (x : ℕ) (t₁ t₂ : DetM∞ x) → t₁ ≈M t₂
  factor-unique = det-unique
