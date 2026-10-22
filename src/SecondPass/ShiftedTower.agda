------------------------------------------------------------------------
-- Shifted compatible towers and level-cast utilities
--
-- A ShiftedTower m₀ lives at FinCatN (m₀ + m) at layer m, rather than
-- FinCatN m. Zero offset specialises back to CompatibleTower.
--
-- 偏移相容塔与层数 cast 工具
--
-- ShiftedTower m₀ 的第 m 层位于 FinCatN (m₀ + m) 而非 FinCatN m。
-- 零偏移特化回 CompatibleTower。
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module SecondPass.ShiftedTower where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Nat using (ℕ; suc; _+_)
open import Data.Nat.Properties using (+-suc)
open import Relation.Binary.PropositionalEquality.Core using (cong; trans; subst)

open import SecondPass.Cosmos using (Cosmos)
open import SecondPass.Terminal using (_≈C_)
open import SecondPass.FinCatNWitness using (module FinCatN)
open import SecondPass.FinCatInfinityTowerCompat using (module FinCatTowerCompat)
open import SecondPass.FinCatInfinityColimit using (CompatibleTower)

open FinCatN

-- Level transport on Cosmos: substitute along an equality of layer indices
--
-- 沿层数相等的 Cosmos 传输
castCosmos : ∀ {m n} → m ≡ n
           → Cosmos (FinCatN m) (TrivialFCN m)
           → Cosmos (FinCatN n) (TrivialFCN n)
castCosmos = subst (λ k → Cosmos (FinCatN k) (TrivialFCN k))

-- castCosmos preserves bisimulation
--
-- castCosmos 保持互模拟
castCosmos-resp-≈C : ∀ {m n} (eq : m ≡ n)
                       {x y : Cosmos (FinCatN m) (TrivialFCN m)}
                   → x ≈C y → castCosmos eq x ≈C castCosmos eq y
castCosmos-resp-≈C refl p = p

-- castCosmos composes: two successive casts equal one cast along the
-- composite equality
--
-- castCosmos 复合：两次连续 cast 等于沿复合等式的单次 cast
castCosmos-comp : ∀ {m n p} (eq₁ : m ≡ n) (eq₂ : n ≡ p)
                    (x : Cosmos (FinCatN m) (TrivialFCN m))
                → castCosmos eq₂ (castCosmos eq₁ x)
                  ≡ castCosmos (trans eq₁ eq₂) x
castCosmos-comp refl eq₂ x = refl

-- embedCosmos is natural in the level: casting before embedding equals
-- embedding before casting along the successor level shift
--
-- embedCosmos 在层数上自然：先 cast 再嵌入等于先嵌入再沿 suc 的层偏移 cast
embed-castCosmos : ∀ {m n} (eq : m ≡ n)
                     (x : Cosmos (FinCatN m) (TrivialFCN m))
                 → FinCatTowerCompat.embedCosmos n (castCosmos eq x)
                   ≡ castCosmos (cong suc eq)
                       (FinCatTowerCompat.embedCosmos m x)
embed-castCosmos refl x = refl

-- Shifted compatible tower with explicit starting layer m₀
-- The offset m₀ is carried as a type parameter, so layer m lives at
-- FinCatN (m₀ + m) rather than FinCatN m
--
-- 带显式起始层 m₀ 的偏移相容塔
-- 偏移 m₀ 作为类型参数携带，故第 m 层位于 FinCatN (m₀ + m) 而非 FinCatN m
record ShiftedTower (m₀ : ℕ) : Set₁ where
  field
    seq    : ∀ m → Cosmos (FinCatN (m₀ + m)) (TrivialFCN (m₀ + m))
    compat : ∀ m →
      castCosmos (+-suc m₀ m) (seq (suc m))
      ≈C FinCatTowerCompat.embedCosmos (m₀ + m) (seq m)
open ShiftedTower

-- Zero offset specialises to the core (unshifted) tower.
-- Since 0 + m ≡ m definitionally, the bridge is the identity.
--
-- 零偏移特化到核心（无偏移）tower。
-- 因 0 + m ≡ m 定义性成立，桥接即恒等。
fromShifted : ShiftedTower 0 → CompatibleTower
fromShifted T = record
  { seq    = λ m → seq T m
  ; compat = λ m → compat T m
  }

toShifted : CompatibleTower → ShiftedTower 0
toShifted T = record
  { seq    = λ m → CompatibleTower.seq T m
  ; compat = λ m → CompatibleTower.compat T m
  }
