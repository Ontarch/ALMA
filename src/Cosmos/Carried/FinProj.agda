------------------------------------------------------------------------
-- Carried finite truncation projection: ℕ limit positions → Fin (suc k)
--
-- The concrete projCosmos m of the FinCat tower in carried form. The
-- index map is a total clamp ℕ → Fin (suc k) saturating at the top,
-- replacing the live code's partial finFromℕ-maybe / defaultFin. It is
-- surjective, with section toℕ and exact round-trip
-- clamp (toℕ v) ≡ v. The transitions s∞ and t-fin together with their
-- compatibility sec-step are parameters, supplied by the tower's
-- layer-independent limit reading. No dependent transport is used --
-- only the one homogeneous equation sec-step carried through SurjProj.
--
-- 携带式有限截断投影：ℕ 极限位置 → Fin (suc k)
--
-- 即 FinCat 塔的 projCosmos m 的携带形式。索引映射是全函数钳制
-- ℕ → Fin (suc k)，在末位饱和，取代真实代码中越界即塌缩的偏函数
-- finFromℕ-maybe / defaultFin。它是满射，截面为 toℕ，且有精确往返
-- clamp (toℕ v) ≡ v。转移 s∞ 与 t-fin 及其相容性 sec-step 在此为参数，
-- 由塔的层无关极限读数供给。无依赖传输——只有经 SurjProj 携带的一条
-- 同质等式 sec-step。
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module Cosmos.Carried.FinProj where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Nat using (ℕ; zero; suc; _⊓_)
open import Data.Nat.Properties using (m≥n⇒m⊓n≡n; <⇒≤pred)
open import Data.Fin.Base using (Fin; zero; suc; toℕ)
open import Data.Fin.Properties using (toℕ-injective; toℕ<n)
open import Relation.Binary.PropositionalEquality.Core using (cong; trans)

open import Cosmos.Carried.TrivProj
open import Cosmos.Carried.FinNatUIP

------------------------------------------------------------------------
-- Total clamp ℕ → Fin (suc k), saturating at the top
--
-- 全函数钳制 ℕ → Fin (suc k)，在末位饱和

clamp : ∀ {k : ℕ} → ℕ → Fin (suc k)
clamp {zero}  zero    = zero
clamp {zero}  (suc _) = zero
clamp {suc k} zero    = zero
clamp {suc k} (suc n) = suc (clamp {k} n)

-- Natural-number image of clamp is the minimum k ⊓ x
--
-- Proved by recursion on natural numbers only, with no Fin indexed
-- pattern match, so it is Cubical-Agda transport-safe.
--
-- clamp 的自然数像为最小值 k ⊓ x
--
-- 仅对自然数递归证明，不对 Fin 做索引模式匹配，故对 Cubical Agda
-- 传输安全。
clamp-val : ∀ {k : ℕ} (x : ℕ) → toℕ (clamp {k} x) ≡ k ⊓ x
clamp-val {zero}  zero    = refl
clamp-val {zero}  (suc _) = refl
clamp-val {suc k} zero    = refl
clamp-val {suc k} (suc x) = cong suc (clamp-val {k} x)

-- Exact section round-trip
--
-- clamp fixes every finite position. Equality of toℕ images is
-- established first, then reflected with toℕ-injective, avoiding any
-- indexed match on Fin.
--
-- 精确截面往返
--
-- clamp 固定每个有限位置。先建立 toℕ 像相等，再用 toℕ-injective
-- 反射回去，避免对 Fin 的任何索引匹配。
clamp-toℕ : ∀ {k : ℕ} (v : Fin (suc k)) → clamp {k} (toℕ v) ≡ v
clamp-toℕ {k} v =
  toℕ-injective
    (trans (clamp-val {k} (toℕ v))
           (m≥n⇒m⊓n≡n {m = k} {n = toℕ v} (<⇒≤pred (toℕ<n v))))

------------------------------------------------------------------------
-- The carried finite truncation correspondence L∞ → stage k
--
-- The transitions s∞ and t-fin together with their compatibility
-- sec-step are parameters; the FMap type is inherited from SurjProj
-- (trivial-fibre systems on ℕ and Fin (suc k)), so no explicit system
-- reference is needed.
--
-- 携带式有限截断对应 L∞ → 第 k 层
--
-- 转移 s∞ 与 t-fin 及其相容性 sec-step 为参数；FMap 类型继承自
-- SurjProj（ℕ 与 Fin (suc k) 上的平凡纤维系统），无需显式引用系统。

module FinProj
  (k : ℕ)
  (s∞ : ℕ → ℕ)
  (t-fin : Fin (suc k) → Fin (suc k))
  -- Finite transition commutes with truncation/embedding:
  -- toℕ (t-fin (clamp x)) ≡ s∞ x.
  --
  -- 有限转移与截断/嵌入交换：toℕ (t-fin (clamp x)) ≡ s∞ x。
  (sec-step : (x : ℕ) → toℕ (t-fin (clamp {k} x)) ≡ s∞ x)
  where

  open SurjProj ℕ s∞ (Fin (suc k)) t-fin
             (clamp {k}) toℕ (clamp-toℕ {k}) sec-step
             natUIP (finUIP {n = suc k})
    using (projF)

  projFin = projF
