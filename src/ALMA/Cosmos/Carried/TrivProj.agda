------------------------------------------------------------------------
-- Surjective finite-projection correspondences between trivial-fibre
-- deterministic systems (the carried projCosmos)
--
-- A stage of the FinCat tower is a trivial-fibre system over
-- Fin (n-at m), and the limit L∞ is one over ℕ. The finite projection
-- projCosmos m : L∞ → stage m is a surjective index map u : I → J, hence
-- a child-surjective MCorr FMap. childF is edge-independent and uses
-- the section: the canonical source child of any target child v is
-- pre v with graph witness surj v. The edge fibres are index-equality
-- propositions, so the FiberAdj round-trips η / ε relate two proofs of
-- the SAME equality and are closed by UIP derived from decidable
-- equality (Hedberg).
--
-- 平凡纤维确定性系统之间的满射有限投影对应（携带式 projCosmos）
--
-- FinCat 塔的一层是 Fin (n-at m) 上的平凡纤维系统，极限 L∞ 是 ℕ 上的
-- 同类系统。有限投影 projCosmos m : L∞ → 第 m 层 是满射索引映射
-- u : I → J，故是子节点满的 MCorr FMap。childF 与边无关并用截面：目标
-- 子节点 v 的规范源子节点是 pre v，图见证为 surj v。边纤维是索引等式
-- 命题，故 FiberAdj 往返律 η / ε 联系同一等式的两份证明，由可判定等式
-- 导出的 UIP（Hedberg）闭合。
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module ALMA.Cosmos.Carried.TrivProj where

open import Agda.Primitive using (Level)
open import Agda.Builtin.Sigma using (_,_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Axiom.UniquenessOfIdentityProofs using (UIP)
open import Data.Unit.Polymorphic.Base using (tt)
open import Relation.Binary.PropositionalEquality.Core using (sym; trans; cong)

open import ALMA.Base.MCorr using (FMap; FiberAdj)
open import ALMA.Cosmos.Carried.DetSys

module SurjProj
  {i j : Level}
  (I : Set i) (s : I → I)
  (J : Set j) (t : J → J)
  (u : I → J)
  (pre : J → I)
  (surj : (v : J) → u (pre v) ≡ v)
  (sec-step : (x : I) → pre (t (u x)) ≡ s x)
  (uipI : UIP I)
  (uipJ : UIP J)
  where

  private
    module Src = TrivDet I s
    module Tgt = TrivDet J t

    -- next-comm derived from the section: u (s x) ≡ t (u x).
    --
    -- 由截面导出的 next-comm：u (s x) ≡ t (u x)。
    next-comm : (x : I) → u (s x) ≡ t (u x)
    next-comm x =
      trans (cong u (sym (sec-step x))) (surj (t (u x)))

    -- Bare edge-fibre maps on the underlying equality propositions.
    --
    -- 底层等式命题上的裸边纤维映射。
    to₀ : (x : I) (v : J)
        → (pre v ≡ s x) → (v ≡ t (u x))
    to₀ x v r =
      trans (sym (surj v)) (trans (cong u r) (next-comm x))

    fro₀ : (x : I) (v : J)
         → (v ≡ t (u x)) → (pre v ≡ s x)
    fro₀ x v p =
      trans (cong pre p) (sec-step x)

    -- Wrapped maps on the edge fibres (the unit level is pinned to
    -- lzero by the TrivDet systems, referenced as Src.E / Tgt.E).
    --
    -- 边纤维上的包裹映射（单位层级由 TrivDet 系统钉为 lzero，以
    -- Src.E / Tgt.E 引用）。
    toᵉ : (x : I) (v : J)
        → Src.E x tt (pre v) → Tgt.E (u x) tt v
    toᵉ x v (tt , r) = tt , to₀ x v r

    froᵉ : (x : I) (v : J)
         → Tgt.E (u x) tt v → Src.E x tt (pre v)
    froᵉ x v (tt , p) = tt , fro₀ x v p

    -- The round-trips are equalities of two proofs of the SAME
    -- proposition, closed by UIP on the discrete index types.
    --
    -- 往返律是同一命题两份证明间的等式，由离散索引类型上的 UIP 闭合。
    adjᵉ : (x : I) (v : J)
         → FiberAdj (Tgt.E (u x) tt v) (Src.E x tt (pre v))
    adjᵉ x v = record
      { to  = toᵉ x v
      ; fro = froᵉ x v
      ; η = λ { (tt , r) →
                cong (tt ,_) (uipI (fro₀ x v (to₀ x v r)) r) }
      ; ε = λ { (tt , p) →
                cong (tt ,_) (uipJ (to₀ x v (fro₀ x v p)) p) }
      }

  -- The surjective projection is a carried deterministic correspondence.
  --
  -- 满射投影是携带的确定性对应。
  projF : FMap Src.sys Tgt.sys
  projF = record
    { u     = u
    ; shape = λ { x tt → tt }
    ; childF = λ { x tt v → pre v , surj v }
    ; adjF   = λ { x tt v → adjᵉ x v }
    ; childF-coh = λ { x refl v → refl , refl }
    }
