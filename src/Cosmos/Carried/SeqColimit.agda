------------------------------------------------------------------------
-- Carried sequential colimit -- specification slice
--
-- Zero subst. A Chain is an ℕ-indexed sequence of edge-indexed systems
-- together with carried embedding FMap between successive layers. Two
-- design choices eliminate the two transport axes: layer arithmetic,
-- where the d-fold embedding iterates compF and its target stage shift
-- d m is defined by recursion on d, so shift (suc d) m ≡ shift d (suc m)
-- holds definitionally; and position, where a cocone leg is itself a
-- carried FMap and leg compatibility is behavioural equivalence _≈F_.
-- This slice fixes the interface and the carried iterated embedding;
-- the apex construction, mediate, the triangle equations and uniqueness
-- are filled in the following slices.
--
-- 携带式序列余极限 —— 规范切片
--
-- 零 subst。Chain 是以 ℕ 为索引的边索引系统序列，相邻两层间携带嵌入
-- FMap。两处设计消去了两条传输轴：层算术，d 次嵌入迭代 compF，其目标
-- 层 shift d m 对 d 递归，使 shift (suc d) m ≡ shift d (suc m) 定义性
-- 成立；位置，余锥腿本身就是携带 FMap，腿相容性是行为等价 _≈F_。本切片
-- 固定接口与携带的迭代嵌入；apex 构造、mediate、三角等式与唯一性在后续
-- 切片补齐。
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module Cosmos.Carried.SeqColimit where

open import Agda.Primitive using (Level; _⊔_; lsuc)
open import Agda.Builtin.Sigma using (Σ)
open import Agda.Builtin.Equality using (_≡_)
open import Data.Nat.Base using (ℕ; zero; suc)

open import Base.MCorr using
  (Sys; FMap; _≈F_; idF; compF; I; A; ≈F-refl; ≈F-trans; ∘-resp-≈
  ; sym-assoc-f; identityʳ-f)

------------------------------------------------------------------------
-- Stage shift by d successor edges
--
-- The layer-arithmetic equality shift (suc d) m ≡ shift d (suc m) is
-- baked into the recursion, so nothing is ever transported along it.
--
-- 沿 d 条后继边的层偏移
--
-- 层算术等式 shift (suc d) m ≡ shift d (suc m) 已烤进递归，无需沿之
-- 传输任何东西。

shift : ℕ → ℕ → ℕ
shift zero    m = m
shift (suc d) m = shift d (suc m)

------------------------------------------------------------------------
-- A carried chain
--
-- Systems X m and a carried embedding at each layer.
--
-- 携带式链
--
-- 系统 X m 与每层的携带嵌入。

record Chain (i a b : Level) : Set (lsuc (i ⊔ a ⊔ b)) where
  field
    X   : ℕ → Sys i a b
    emb : (m : ℕ) → FMap (X m) (X (suc m))

  -- Iteration of compF; the target stage computes via shift, so no
  -- arithmetic cast is needed at any step.
  --
  -- compF 的迭代；目标层经 shift 计算，任一步都无需算术 cast。
  emb^d : (m d : ℕ) → FMap (X m) (X (shift d m))
  emb^d m zero    = idF (X m)
  emb^d m (suc d) = compF (emb^d (suc m) d) (emb m)

open Chain public

------------------------------------------------------------------------
-- A carried cocone with apex Y
--
-- 以 Y 为 apex 的携带余锥

record Cocone {i a b : Level} (ch : Chain i a b) (Y : Sys i a b)
       : Set (lsuc (i ⊔ a ⊔ b)) where
  field
    leg : (m : ℕ) → FMap (X ch m) Y
    coh : (m : ℕ)
        → compF (leg (suc m)) (emb ch m) ≈F leg m

open Cocone public

------------------------------------------------------------------------
-- d-fold leg coherence
--
-- By induction on d from the one-step coh.
--
-- d 次腿相干性
--
-- 由一步 coh 对 d 归纳。

module _ {i a b : Level} {ch : Chain i a b} {L : Sys i a b}
         (coc : Cocone ch L) where

  leg-coh^d : (m d : ℕ)
            → compF (leg coc (shift d m)) (emb^d ch m d) ≈F leg coc m
  leg-coh^d m zero =
    identityʳ-f (leg coc m)
  leg-coh^d m (suc d) =
    ≈F-trans
      (sym-assoc-f
         (emb ch m)
         (emb^d ch (suc m) d)
         (leg coc (shift d (suc m))))
      (≈F-trans
         (∘-resp-≈
            (leg-coh^d (suc m) d)
            (≈F-refl (emb ch m)))
         (coh coc m))

------------------------------------------------------------------------
-- The colimit universal property
--
-- Expressed entirely with carried morphisms and behavioural equivalence.
--
-- 余极限泛性质
--
-- 完全用携带态射与行为等价表达。

record IsColimit {i a b : Level} {ch : Chain i a b}
                (Apex : Sys i a b) (coc : Cocone ch Apex)
       : Set (lsuc (i ⊔ a ⊔ b)) where
  field
    mediate  : {Y : Sys i a b} (k : Cocone ch Y) → FMap Apex Y
    triangle : {Y : Sys i a b} (k : Cocone ch Y) (m : ℕ)
             → compF (mediate k) (leg coc m) ≈F leg k m
    unique   : {Y : Sys i a b} (h : FMap Apex Y) (k : Cocone ch Y)
             → ((m : ℕ) → compF h (leg coc m) ≈F leg k m)
             → h ≈F mediate k

open IsColimit public

------------------------------------------------------------------------
-- A bundled colimit
--
-- Apex, its cocone and the universal property.
--
-- 打包的余极限
--
-- apex、其余锥与泛性质。

record Colimit (i a b : Level) (ch : Chain i a b)
       : Set (lsuc (i ⊔ a ⊔ b)) where
  field
    Apex : Sys i a b
    coc  : Cocone ch Apex
    has  : IsColimit Apex coc

open Colimit public

------------------------------------------------------------------------
-- Carried colimit limit structure (existence data)
--
-- Relative to a pre-given limit system L with unbounded positions. A
-- plain (non-FMap) position and label injection of each stage into L,
-- with inj-coh (the embedding preserves the injected position) and rep
-- (every limit point has a total finite-stage representative with a
-- homogeneous graph witness in I L). rep replaces the old partial
-- defaultFin, since positions are unbounded (ℕ).
--
-- 携带式余极限的极限结构（存在性数据）
--
-- 相对于预给的、位置无界的极限系统 L。每层到 L 有普通（非 FMap）
-- 位置与标签注入，附带 inj-coh（嵌入保持注入位置）与 rep（每个极限点
-- 有全函数有限层代表，含 I L 中的同质图见证）。rep 取代旧的偏函数
-- defaultFin，因位置无界（ℕ）。

record Limit {i a b : Level} (ch : Chain i a b)
       : Set (lsuc (i ⊔ a ⊔ b)) where

  field
    L : Sys i a b

    -- Stage→limit position injection. NOT an FMap: not
    -- child-surjective, hence no tree action.
    --
    -- 阶段→极限的位置注入。不是 FMap：不满足子节点满，故无树作用。
    inj-u : (m : ℕ) → I (X ch m) → I L

    inj-shape : (m : ℕ) (x : I (X ch m))
              → A (X ch m) x → A L (inj-u m x)

    inj-coh : (m : ℕ) (x : I (X ch m))
            → inj-u (suc m) (FMap.u (emb ch m) x) ≡ inj-u m x

    rep   : (v : I L)
          → Σ ℕ λ m →
            Σ (I (X ch m)) λ x →
            inj-u m x ≡ v

open Limit public
