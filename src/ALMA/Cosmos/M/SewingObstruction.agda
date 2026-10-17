------------------------------------------------------------------------
-- Sewing obstruction and direction dichotomy on the carried M base
--
-- The strict layer tower is absorbed by the M index (iterating
-- ShapeCat C FC is iterating MO.I = Σ (Obj C) (ShapeOf FC)), so there
-- is no per-step universe lifting and no PosOf subst. A carried
-- "retract" of a raised node back to its source shape is just an M
-- edge, whose target is pinned by a homogeneous refl; for an
-- object-preserving label with singleton positions and shape routing
-- r, a return edge exists iff r s ≡ s, so the sewing obstruction
-- collapses to the fixed-point condition of r. The dichotomy is the
-- category-free lemma
--   (∀ r s → r s ≡ s)  ⇔  (∀ x y → x ≡ y);
-- Fin n (n ≥ 2) is not a singleton, witnessed by the constant routing
-- rChg = const (fsuc fzero). All mismatches are absorbed by
-- constructive no-confusion.
--
-- 携带式 M 底座上的缝纫障碍与方向二分
--
-- 严格层塔被 M 索引吸收（迭代 ShapeCat C FC 即迭代
-- MO.I = Σ (Obj C) (ShapeOf FC)），故无逐层抬 universe、无 PosOf
-- subst。被提升节点回到源形状的携带式“retract”即一条 M 边，其目标由
-- 同质 refl 钉死；对对象保持、位置单点、形状路由为 r 的标签，回边存在
-- 当且仅当 r s ≡ s，故缝纫障碍塌缩为路由函数的不动点条件。二分即无
-- 范畴引理
--   （∀ r s → r s ≡ s） ⇔ （∀ x y → x ≡ y）；
-- Fin n（n ≥ 2）非单点，常值路由 rChg = const (fsuc fzero) 即为见证。
-- 所有失配由构造性无混淆吸收。
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module ALMA.Cosmos.M.SewingObstruction where

open import Agda.Primitive using (Level; lzero)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Sigma using (_,_)
open import Data.Unit.Polymorphic.Base using (⊤; tt)
open import Data.Nat using (ℕ; suc)
open import Data.Fin.Base using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.Product.Base using (proj₁; proj₂)
open import Data.Product.Properties using (Σ-≡,≡→≡)
open import Data.Container.Core using (Container)
open import Function.Base using (id; const)
open import Function.Bundles using (_⇔_; mk⇔)
open import Relation.Binary.PropositionalEquality.Core using (sym; cong; _≢_)
open import Relation.Nullary.Negation using (¬_)

open import Categories.Category.Core using (Category)
open import Categories.Category.Indiscrete using (Indiscrete)
open import Categories.Functor.Core using (Functor)

open import ALMA.Cosmos.ContCategory using (ContCat; ≈sr-refl)
open import ALMA.Cosmos.ContCatEquiv using (ShapeCat)
import ALMA.Cosmos.M.Object as MO

------------------------------------------------------------------------
-- Category-free core of the direction dichotomy
--
-- Every self-map r on P fixes every point iff P is a singleton.
--   to   : fixing the constant map const y at x gives y ≡ x.
--   from : r s is the unique element, hence r s ≡ s.
--
-- 方向二分的无范畴核心
--
-- P 上每个自映射 r 固定每个点当且仅当 P 单点。
--   to   ：把常值映射 const y 在 x 处固定得 y ≡ x。
--   from ：r s 即唯一元素，故 r s ≡ s。

routing-fixed-iff-singleton
  : ∀ {ℓ : Level} {P : Set ℓ}
  → (∀ (r : P → P) (s : P) → r s ≡ s)
    ⇔ (∀ (x y : P) → x ≡ y)
routing-fixed-iff-singleton {P = P} = mk⇔ to from
  where
    to : (∀ (r : P → P) (s : P) → r s ≡ s)
       → ∀ (x y : P) → x ≡ y
    to h x y = sym (h (const y) x)

    from : (∀ (x y : P) → x ≡ y)
         → ∀ (r : P → P) (s : P) → r s ≡ s
    from u r s = u (r s) s

------------------------------------------------------------------------
-- FinCat n stage
--
-- Parameterised by m with n = suc (suc m), so n ≥ 2 holds
-- definitionally.
--
-- FinCat n 塔层
--
-- 以 m 为参数，n = suc (suc m)，故 n ≥ 2 定义性成立。

module SewingObstruction (m : ℕ) where

  n : ℕ
  n = suc (suc m)

  Cn : Category lzero lzero lzero
  Cn = Indiscrete (Fin n)

  -- Non-singleton-shape container with singleton positions; the
  -- container functor is the identity on shapes (rigid), so rigidity
  -- is built into the M index rather than assumed.
  --
  -- 非单点形状容器，位置单点；容器函子在形状上恒等作用（刚性），故
  -- 刚性内建于 M 索引而非另行假设。
  FinContainer : Container lzero lzero
  FinContainer = record { Shape = Fin n ; Position = λ _ → ⊤ }

  FinFC : Functor Cn (ContCat lzero lzero)
  FinFC = record
    { F₀           = λ _ → FinContainer
    ; F₁           = λ _ → record { shape = id ; position = λ _ → tt }
    ; identity     = ≈sr-refl
    ; homomorphism = ≈sr-refl
    ; F-resp-≈     = λ _ → ≈sr-refl
    }

  ufId : Functor (ShapeCat Cn FinFC) Cn
  ufId = record
    { F₀           = proj₁
    ; F₁           = proj₁
    ; identity     = refl
    ; homomorphism = refl
    ; F-resp-≈     = λ p → p
    }

  -- Object-preserving label with shape routing r : Fin n → Fin n;
  -- positions are singleton, so pts d s tt = r s.
  --
  -- 形状路由为 r 的对象保持标签；位置单点，故 pts d s tt = r s。
  label : (r : Fin n → Fin n) → MO.CosmosData Cn FinFC
  label r = record { uf = ufId ; pts = λ s _ → r s }

  ----------------------------------------------------------------------
  -- Return edges
  --
  -- The M edge pins the target index by a homogeneous refl. For the
  -- label r, an edge from (A,s) back to (A,s) exists iff r s ≡ s.
  --
  -- 回边
  --
  -- M 边以同质 refl 钉住目标索引。对标签 r，从 (A,s) 回到 (A,s) 的边
  -- 存在当且仅当 r s ≡ s。

  return-edge
    : ∀ (r : Fin n → Fin n) (A s : Fin n)
    → r s ≡ s
    → MO.E Cn FinFC (A , s) (label r) (A , s)
  return-edge r A s eq =
    tt , Σ-≡,≡→≡ (refl , sym eq)

  no-return-edge
    : ∀ (r : Fin n → Fin n) (A s : Fin n)
    → r s ≢ s
    → ¬ MO.E Cn FinFC (A , s) (label r) (A , s)
  no-return-edge r A s ne (tt , q) =
    ne (sym (cong proj₂ q))

  ----------------------------------------------------------------------
  -- Concrete obstruction
  --
  -- 1 ≠ 0 in Fin n (n ≥ 2); the constant routing rChg sends every shape
  -- to fsuc fzero, so it moves fzero.
  --
  -- 具体障碍
  --
  -- Fin n（n ≥ 2）中 1 ≠ 0；常值路由 rChg 把每个形状送到 fsuc fzero，
  -- 故它移动 fzero。

  zero one : Fin n
  zero = fzero
  one  = fsuc fzero

  one≢zero : one ≢ zero
  one≢zero ()

  rChg : Fin n → Fin n
  rChg _ = one

  rChg-moves-fzero : rChg fzero ≢ fzero
  rChg-moves-fzero = one≢zero

  -- The routing-changed label has no return edge at (A , fzero) for any
  -- object A: the elements-category retract is replaced by the M edge.
  --
  -- 路由改变的标签在 (A , fzero) 处对任意对象 A 都无回边：元素范畴
  -- retract 被 M 边取代。
  no-retract-routing-change
    : ∀ (A : Fin n)
    → ¬ MO.E Cn FinFC (A , fzero) (label rChg) (A , fzero)
  no-retract-routing-change A =
    no-return-edge rChg A fzero rChg-moves-fzero

  -- The universal outer-rule propagation fails at n ≥ 2.
  --
  -- 全称 outer 规则传播在 n ≥ 2 失败。
  no-universal-return
    : ¬ (∀ (r : Fin n → Fin n) (A s : Fin n)
        → MO.E Cn FinFC (A , s) (label r) (A , s))
  no-universal-return h =
    no-retract-routing-change fzero (h rChg fzero fzero)

  ----------------------------------------------------------------------
  -- DirectionDichotomy, M form (necessity at n ≥ 2)
  --
  -- Fin n is not a singleton, so by the category-free dichotomy the
  -- fixed-point property fails; a return edge is exactly a fixed point.
  --
  -- 方向二分的 M 形态（n ≥ 2 的必要性）
  --
  -- Fin n 非单点，故由无范畴二分不动点性质失败；回边恰是一个不动点。

  Fin-not-singleton : ¬ (∀ (x y : Fin n) → x ≡ y)
  Fin-not-singleton u = one≢zero (u one zero)

  Fin-not-all-fixed : ¬ (∀ (r : Fin n → Fin n) (s : Fin n) → r s ≡ s)
  Fin-not-all-fixed h =
    Fin-not-singleton λ a b → sym (h (const b) a)

  fixed-point-iff-return-edge
    : ∀ (r : Fin n → Fin n) (A s : Fin n)
    → (r s ≡ s)
      ⇔ (MO.E Cn FinFC (A , s) (label r) (A , s))
  fixed-point-iff-return-edge r A s =
    mk⇔ (return-edge r A s)
         λ { (tt , q) → sym (cong proj₂ q) }
