------------------------------------------------------------------------
-- UIP for the discrete position index types ℕ and Fin n
--
-- SurjProj asks for UIP on its two index types, because the
-- deterministic edge fibres are index-equality propositions and the
-- FiberAdj round-trips relate two proofs of the same equality. Both ℕ
-- and Fin n carry decidable equality, hence UIP constructively by
-- Hedberg's theorem (Decidable⇒UIP); this does not invoke axiom K and
-- stays --safe / --cubical-compatible.
--
-- 离散位置索引类型 ℕ 与 Fin n 的 UIP
--
-- SurjProj 要求两个索引类型具备 UIP，因为确定性边纤维是索引等式命题，
-- FiberAdj 往返律联系同一等式的两份证明。ℕ 与 Fin n 都带可判定等式，
-- 故由 Hedberg 定理（Decidable⇒UIP）构造性地有 UIP；这不调用公理 K，
-- 仍为 --safe / --cubical-compatible。
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module Cosmos.Carried.FinNatUIP where

open import Axiom.UniquenessOfIdentityProofs using (UIP; module Decidable⇒UIP)
open import Data.Nat using (ℕ)
open import Data.Fin using (Fin)

import Data.Nat.Properties
import Data.Fin.Properties


------------------------------------------------------------------------
-- UIP for ℕ and for Fin n
--
-- Both instances go through Hedberg's theorem, fed with the decidable
-- equality of the respective index type.
--
-- ℕ 与 Fin n 的 UIP
--
-- 两个实例都经由 Hedberg 定理给出，喂以对应索引类型的可判定等式。

natUIP : UIP ℕ
natUIP = Decidable⇒UIP.≡-irrelevant Data.Nat.Properties._≟_

finUIP : ∀ {n} → UIP (Fin n)
finUIP {n} = Decidable⇒UIP.≡-irrelevant (Data.Fin.Properties._≟_ {n = n})
