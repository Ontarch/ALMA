------------------------------------------------------------------------
-- Sequential colimit over setoid carried systems
--
-- The MCorrSetoidCat counterpart of Carried.SeqColimit. A Chainˢ is an
-- ℕ-indexed family of SysEq with a carried setoid functor FMˢ between
-- successive layers. The d-fold embedding iterates compFMˢ and its
-- target stage shift d m is defined by recursion on d, so
-- shift (suc d) m ≡ shift d (suc m) holds definitionally; cocone legs
-- are themselves FMˢ and their compatibility is behavioural
-- equivalence _≈FM_.
--
-- setoid 携带系统上的序列余极限
--
-- Carried.SeqColimit 在 MCorrSetoidCat 上的对应物。Chainˢ 是以 ℕ 为
-- 索引的 SysEq 族，相邻层间为携带 setoid 函子 FMˢ。d 次嵌入迭代
-- compFMˢ，目标层 shift d m 对 d 递归，使 shift (suc d) m ≡
-- shift d (suc m) 定义性成立；余锥腿本身为 FMˢ，其相容性是行为等价
-- _≈FM_。
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module ALMA.Cosmos.Carried.SeqColimitS where

open import Agda.Primitive using (Level; _⊔_; lsuc)
open import Agda.Builtin.Sigma using (Σ; _,_)
open import Agda.Builtin.Equality using (_≡_)
open import Data.Nat.Base using (ℕ; zero; suc)

open import ALMA.Base.MCorrSetoid using (SysEq)
open import ALMA.Base.MCorrSetoidCat using
  (FMapˢ; FMˢ; idFMˢ; compFMˢ; _≈FM_; ≈FM-refl; ≈FM-trans
  ; ∘-resp-≈FM; sym-assocFM; identityʳFM)

open SysEq

------------------------------------------------------------------------
-- Stage shift by d successor edges
--
-- The layer-arithmetic equality is baked into the recursion.
--
-- 沿 d 条后继边的层偏移
--
-- 层算术等式已烤进递归。

shift : ℕ → ℕ → ℕ
shift zero    m = m
shift (suc d) m = shift d (suc m)

------------------------------------------------------------------------
-- A carried chain and its iterated embedding
--
-- 携带式链及其迭代嵌入

record Chainˢ (i a b ℓa ℓe : Level) : Set (lsuc (i ⊔ a ⊔ b ⊔ ℓa ⊔ ℓe)) where
  field
    X   : ℕ → SysEq i a b ℓa ℓe
    emb : (m : ℕ) → FMˢ (X m) (X (suc m))

  embˢ^d : (m d : ℕ) → FMˢ (X m) (X (shift d m))
  embˢ^d m zero    = idFMˢ
  embˢ^d m (suc d) = compFMˢ (embˢ^d (suc m) d) (emb m)

open Chainˢ public

------------------------------------------------------------------------
-- A carried cocone with apex L
--
-- 以 L 为 apex 的携带余锥

record Coconeˢ {i a b ℓa ℓe : Level} (ch : Chainˢ i a b ℓa ℓe)
               (L : SysEq i a b ℓa ℓe)
       : Set (lsuc (i ⊔ a ⊔ b ⊔ ℓa ⊔ ℓe)) where
  field
    leg : (m : ℕ) → FMˢ (X ch m) L
    coh : (m : ℕ)
        → compFMˢ (leg (suc m)) (emb ch m) ≈FM leg m

open Coconeˢ public

------------------------------------------------------------------------
-- d-fold leg coherence
--
-- By induction on d from the one-step coh.
--
-- d 次腿相干性
--
-- 由一步 coh 对 d 归纳。

module _ {i a b ℓa ℓe : Level} {ch : Chainˢ i a b ℓa ℓe}
         {L : SysEq i a b ℓa ℓe} (coc : Coconeˢ ch L) where

  leg-coh^dˢ : (m d : ℕ)
             → compFMˢ (leg coc (shift d m)) (embˢ^d ch m d) ≈FM leg coc m
  leg-coh^dˢ m zero =
    identityʳFM {f = leg coc m}
  leg-coh^dˢ m (suc d) =
    ≈FM-trans {X = X ch m} {Y = L}
      {f = compFMˢ (leg coc (shift d (suc m)))
                   (compFMˢ (embˢ^d ch (suc m) d) (emb ch m))}
      {g = compFMˢ (compFMˢ (leg coc (shift d (suc m)))
                             (embˢ^d ch (suc m) d))
                   (emb ch m)}
      {h = leg coc m}
      (sym-assocFM {W = X ch m} {X = X ch (suc m)}
                   {Y = X ch (shift d (suc m))} {Z = L}
                   {f = emb ch m} {g = embˢ^d ch (suc m) d}
                   {h = leg coc (shift d (suc m))})
      (≈FM-trans {X = X ch m} {Y = L}
        {f = compFMˢ (compFMˢ (leg coc (shift d (suc m)))
                              (embˢ^d ch (suc m) d))
                    (emb ch m)}
        {g = compFMˢ (leg coc (suc m)) (emb ch m)}
        {h = leg coc m}
        (∘-resp-≈FM {X = X ch m} {Y = X ch (suc m)} {Z = L}
                    {F₁ = emb ch m} {F₂ = emb ch m}
                    {G₁ = compFMˢ (leg coc (shift d (suc m)))
                                 (embˢ^d ch (suc m) d)}
                    {G₂ = leg coc (suc m)}
                    (≈FM-refl (emb ch m))
                    (leg-coh^dˢ (suc m) d))
        (coh coc m))

------------------------------------------------------------------------
-- The colimit universal property
--
-- Entirely in carried morphisms.
--
-- 余极限泛性质
--
-- 完全用携带态射表达。

record IsColimitˢ {i a b ℓa ℓe : Level} {ch : Chainˢ i a b ℓa ℓe}
                  (Apex : SysEq i a b ℓa ℓe) (coc : Coconeˢ ch Apex)
       : Set (lsuc (i ⊔ a ⊔ b ⊔ ℓa ⊔ ℓe)) where
  field
    mediate  : {Y : SysEq i a b ℓa ℓe} (k : Coconeˢ ch Y) → FMˢ Apex Y
    triangle : {Y : SysEq i a b ℓa ℓe} (k : Coconeˢ ch Y) (m : ℕ)
             → compFMˢ (mediate k) (leg coc m) ≈FM leg k m
    unique   : {Y : SysEq i a b ℓa ℓe} (h : FMˢ Apex Y) (k : Coconeˢ ch Y)
             → ((m : ℕ) → compFMˢ h (leg coc m) ≈FM leg k m)
             → h ≈FM mediate k

open IsColimitˢ public

------------------------------------------------------------------------
-- A bundled colimit
--
-- 打包的余极限

record Colimitˢ (i a b ℓa ℓe : Level) (ch : Chainˢ i a b ℓa ℓe)
       : Set (lsuc (i ⊔ a ⊔ b ⊔ ℓa ⊔ ℓe)) where
  field
    Apex : SysEq i a b ℓa ℓe
    coc  : Coconeˢ ch Apex
    has  : IsColimitˢ Apex coc

open Colimitˢ public

------------------------------------------------------------------------
-- Existence data for a carried colimit apex
--
-- A limit system L with a stage injection and a finite-stage
-- representative for every point. The injection is not an FMˢ (not
-- child-surjective); rep replaces any partial default since positions
-- are unbounded.
--
-- 携带余极限 apex 的存在性数据
--
-- 极限系统 L，带阶段注入与每点的有限层代表。注入不是 FMˢ（不满足
-- 子节点满）；位置无界，故用 rep 取代偏函数默认值。

record Limitˢ {i a b ℓa ℓe : Level} (ch : Chainˢ i a b ℓa ℓe)
       : Set (lsuc (i ⊔ a ⊔ b ⊔ ℓa ⊔ ℓe)) where
  field
    L : SysEq i a b ℓa ℓe

    inj-u : (m : ℕ) → I (X ch m) → I L

    inj-shape : (m : ℕ) (x : I (X ch m))
              → A (X ch m) x → A L (inj-u m x)

    inj-coh : (m : ℕ) (x : I (X ch m))
            → inj-u (suc m) (FMapˢ.u (FMˢ.mor (emb ch m)) x) ≡ inj-u m x

    rep : (v : I L)
        → Σ ℕ λ m → Σ (I (X ch m)) λ x → inj-u m x ≡ v

open Limitˢ public
