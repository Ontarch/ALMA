------------------------------------------------------------------------
-- Zero-subst colimit of the finite stages Fin (n-at m)
--
-- With n-at m = suc (suc m), the family embeds by iterated inject₁ and
-- its colimit is ℕ via toℕ. This is the carried, zero-subst / zero-cast
-- replacement for the Set-level universal property of FinCatInfinity:
-- the d-fold embedding uses embFin, whose target size n-at (shift d m)
-- reduces definitionally; every position is read through the total
-- clamp cl with a single bounded split m≤n⇒m<n∨m≡n and structural
-- recursion on m.
--
-- 有限层 Fin (n-at m) 的零 subst 余极限
--
-- n-at m = suc (suc m) 时，该族经迭代 inject₁ 嵌入，余极限为经 toℕ
-- 的 ℕ。本模块是 FinCatInfinity 中 Set 层泛性质的携带式、零 subst /
-- 零 cast 替代：d 次嵌入用 embFin，其目标尺寸 n-at (shift d m) 定义性
-- 归约；每个位置经全函数 clamp cl 读取，只用一次有界拆分
-- m≤n⇒m<n∨m≡n，并对 m 结构递归。
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module ALMA.Cosmos.Carried.FinColimit where

open import Agda.Builtin.Sigma using (Σ; _,_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Nat using (ℕ; zero; suc; _≤_)
open import Data.Nat.Properties using
  ( ≤-pred; ≤-refl; m≤n⇒m≤1+n; m≤n⇒m<n∨m≡n; n≤0⇒n≡0 )
open import Data.Fin.Base using (Fin; zero; toℕ; inject₁)
open import Data.Fin.Properties using (toℕ-injective; toℕ-inject₁; toℕ<n)
open import Data.Sum.Base using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality.Core using (cong; sym; trans)

open import ALMA.Cosmos.Carried.SeqColimit using (shift)
open import ALMA.Cosmos.Carried.LimitSystem using
  (n-at; natToFin; toℕ-natToFin; embFin; cl; cl-toℕ)

------------------------------------------------------------------------
-- Pure Fin representatives, independent of the cone
--
-- One inject₁ reaches the canonical element of stage suc m with the
-- same natural reading.
--
-- 纯 Fin 代表，与锥无关
--
-- 一次 inject₁ 到达第 suc m 层具有相同自然读数的典范元素。

top-eq : ∀ m → inject₁ (cl m (suc m)) ≡ natToFin (suc m)
top-eq m =
  toℕ-injective
    (trans (toℕ-inject₁ (cl m (suc m)))
      (trans (cl-toℕ m (suc m) ≤-refl)
             (sym (toℕ-natToFin (suc m)))))

-- Below the top, the stage-(suc p) representative is one inject₁ of
-- the stage-p representative.
--
-- 顶端以下，第 suc p 层代表是第 p 层代表的一次 inject₁。
inj-cl : ∀ p k (le : k ≤ suc p)
       → cl (suc p) k ≡ inject₁ (cl p k)
inj-cl p k le =
  toℕ-injective
    (trans (cl-toℕ (suc p) k (m≤n⇒m≤1+n le))
      (sym (trans (toℕ-inject₁ (cl p k))
                  (cl-toℕ p k le))))

------------------------------------------------------------------------
-- Compatible cone over the finite stages
--
-- Valued in a set X, with at (suc m) (inject₁ x) ≡ at m x.
--
-- 有限层上的相容锥
--
-- 取值于集合 X，满足 at (suc m) (inject₁ x) ≡ at m x。

record FinCone (X : Set) : Set where

  field
    at     : ∀ m → Fin (n-at m) → X
    compat : ∀ m (x : Fin (n-at m))
           → at (suc m) (inject₁ x) ≡ at m x

  -- Target Fin size reduces definitionally via shift, so there is no
  -- subst Fin (+-suc).
  --
  -- 目标 Fin 尺寸经 shift 定义性归约，故无 subst Fin (+-suc)。
  compat-emb : ∀ d m (x : Fin (n-at m))
             → at (shift d m) (embFin d m x) ≡ at m x
  compat-emb zero    m x = refl
  compat-emb (suc d) m x =
    trans (compat-emb d (suc m) (inject₁ x))
          (compat m x)

  -- Structural recursion on m: the top case (k ≡ suc m) goes one stage
  -- up via compat; the inherited case (k ≤ suc p) descends via compat
  -- and the recursion at stage p.
  --
  -- 对 m 结构递归：顶端情形（k ≡ suc m）经 compat 上走一层；继承情形
  -- （k ≤ suc p）经 compat 下降并在第 p 层递归。
  at-cl : ∀ m k (le : k ≤ suc m)
        → at m (cl m k) ≡ at k (natToFin k)
  at-cl zero k le
    with m≤n⇒m<n∨m≡n le
  ... | inj₂ eq rewrite eq =
    sym (trans (cong (at (suc zero)) (sym (top-eq zero)))
               (compat zero (cl zero (suc zero))))
  ... | inj₁ lt rewrite n≤0⇒n≡0 (≤-pred lt) = refl
  at-cl (suc p) k le
    with m≤n⇒m<n∨m≡n le
  ... | inj₂ eq rewrite eq =
    sym (trans (cong (at (suc (suc p))) (sym (top-eq (suc p))))
               (compat (suc p) (cl (suc p) (suc (suc p)))))
  ... | inj₁ lt =
    let le' : k ≤ suc p
        le' = ≤-pred lt
    in trans (cong (at (suc p)) (inj-cl p k le'))
             (trans (compat p (cl p k))
                    (at-cl p k le'))

  -- Unique extension g∞ : ℕ → X reads the canonical element of the
  -- stage equal to the natural index.
  --
  -- 唯一扩展 g∞ : ℕ → X，读取等于自然索引那一层的典范元素。
  g∞ : ℕ → X
  g∞ k = at k (natToFin k)

  extends : ∀ m (x : Fin (n-at m)) → g∞ (toℕ x) ≡ at m x
  extends m x =
    let k  : ℕ
        k  = toℕ x
        le : k ≤ suc m
        le = ≤-pred (toℕ<n x)
        eqx : x ≡ cl m k
        eqx = toℕ-injective (sym (cl-toℕ m k le))
    in trans (sym (at-cl m k le))
             (cong (at m) (sym eqx))

  -- k equals toℕ (natToFin k) definitionally in value.
  --
  -- k 在值上即为 toℕ (natToFin k)。
  unique : (h : ℕ → X)
         → (∀ m (x : Fin (n-at m)) → h (toℕ x) ≡ at m x)
         → ∀ k → h k ≡ g∞ k
  unique h h-ext k =
    trans (cong h (sym (toℕ-natToFin k)))
          (h-ext k (natToFin k))

open FinCone public

------------------------------------------------------------------------
-- The Set-level universal property
--
-- 集合层泛性质

colimitUniv
  : ∀ {X : Set} (cone : FinCone X)
  → Σ (ℕ → X) λ g∞ →
      Σ (∀ m (x : Fin (n-at m)) → g∞ (toℕ x) ≡ at cone m x) λ _ →
        (∀ (h : ℕ → X)
         → (∀ m (x : Fin (n-at m)) → h (toℕ x) ≡ at cone m x)
         → ∀ k → h k ≡ g∞ k)
colimitUniv cone = g∞ cone , (extends cone , unique cone)
