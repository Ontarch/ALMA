------------------------------------------------------------------------
-- Tower separation witness on the carried M base
--
-- Over FinCat n (n ≥ 2), the identity-like cosmos (uf.F₀ = proj₁) and
-- the constant-first cosmos (uf.F₀ = const fzero) are not bisimilar.
-- The base category is Indiscrete (Fin n) with a singleton-shape /
-- singleton-position container; the M-Cosmos index
-- Σ (Fin n) (λ _ → ⊤) is isomorphic to Fin n. A propositional
-- bisimulation carries a head-label equality here-eq : dId ≡ dC0;
-- projecting uf.F₀ at (fsuc fzero , tt) yields fsuc fzero ≡ fzero,
-- absorbed by the empty pattern (constructive no-confusion, not
-- K/UIP). The parameter m encodes n = suc (suc m), so n ≥ 2 holds
-- definitionally; at n = 1 the object set is a singleton and no
-- separation exists.
--
-- 携带式 M 底座上的塔层分离见证
--
-- FinCat n（n ≥ 2）上两个被区分的 M-Cosmos 不互模拟。基范畴为
-- Indiscrete (Fin n)，配单点形状/单点位置容器；M-Cosmos 索引
-- Σ (Fin n) (λ _ → ⊤) 与 Fin n 同构。命题互模拟携带头标签等式
-- here-eq : dId ≡ dC0；在 (fsuc fzero , tt) 处投影 uf.F₀ 得
-- fsuc fzero ≡ fzero，由空模式吸收（构造性无混淆，而非 K/UIP）。
-- 参数 m 编码 n = suc (suc m)，使 n ≥ 2 定义性成立；n = 1 时对象集
-- 为单点，不存在分离。
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module ALMA.Cosmos.M.TowerSeparation where

open import Agda.Primitive using (lzero)
open import Agda.Builtin.Equality using (refl)
open import Agda.Builtin.Sigma using (_,_)
open import Data.Unit.Polymorphic.Base using (⊤; tt)
open import Data.Nat using (ℕ; suc)
open import Data.Fin.Base using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.Product.Base using (proj₁)
open import Data.Container.Core using (Container)
open import Relation.Binary.PropositionalEquality.Core using (cong)
open import Relation.Nullary.Negation using (¬_)

open import Categories.Category.Core using (Category)
open import Categories.Category.Indiscrete using (Indiscrete)
open import Categories.Functor.Core using (Functor)
open Functor using (F₀)

open import ALMA.Cosmos.ContCategory using (ContCat; ≈sr-refl)
open import ALMA.Cosmos.ContCatEquiv using (ShapeCat)
open import ALMA.Base.MCorrSetoid using (propEqOn; here-eq)
import ALMA.Cosmos.M.Object as MO

------------------------------------------------------------------------
-- The FinCat n tower stage
--
-- Parameterised by m with n = suc (suc m).
--
-- FinCat n 塔层
--
-- 以 m 为参数，n = suc (suc m)。

module TowerSeparation (m : ℕ) where

  n : ℕ
  n = suc (suc m)

  Cn : Category lzero lzero lzero
  Cn = Indiscrete (Fin n)

  -- Trivial-fibre container: singleton shapes and singleton positions.
  --
  -- 平凡纤维容器：单点形状、单点位置。
  TrivContainer : Container lzero lzero
  TrivContainer = record { Shape = ⊤ ; Position = λ _ → ⊤ }

  TrivFC : Functor Cn (ContCat lzero lzero)
  TrivFC = record
    { F₀           = λ _ → TrivContainer
    ; F₁           = λ _ → record { shape = λ _ → tt ; position = λ _ → tt }
    ; identity     = ≈sr-refl
    ; homomorphism = ≈sr-refl
    ; F-resp-≈     = λ _ → ≈sr-refl
    }

  ----------------------------------------------------------------------
  -- The two object maps uf as functors ShapeCat Cn TrivFC → Cn
  --
  -- ShapeCat is the category of elements of the singleton shape
  -- functor, so its homs are unique and F₁ and all functor laws hold by
  -- refl; the two differ only in F₀.
  --
  -- 两个对象映射 uf，作为 ShapeCat Cn TrivFC → Cn 的函子
  --
  -- ShapeCat 是单点形状函子的元素范畴，故其 hom 唯一，F₁ 与所有函子律
  -- 由 refl 成立；两者唯一差别在 F₀。

  ufId : Functor (ShapeCat Cn TrivFC) Cn
  ufId = record
    { F₀           = proj₁
    ; F₁           = proj₁
    ; identity     = refl
    ; homomorphism = refl
    ; F-resp-≈     = λ p → p
    }

  ufC0 : Functor (ShapeCat Cn TrivFC) Cn
  ufC0 = record
    { F₀           = λ _ → fzero
    ; F₁           = proj₁
    ; identity     = refl
    ; homomorphism = refl
    ; F-resp-≈     = λ p → p
    }

  -- The two head labels differ only in uf; positions and shapes are
  -- singletons, so pts is the unique map.
  --
  -- 两个头标签仅在 uf 上不同；位置与形状均为单点，故 pts 为唯一映射。
  dId : MO.CosmosData Cn TrivFC
  dId = record { uf = ufId ; pts = λ _ _ → tt }

  dC0 : MO.CosmosData Cn TrivFC
  dC0 = record { uf = ufC0 ; pts = λ _ _ → tt }

  ----------------------------------------------------------------------
  -- Constant coalgebras and their constant trees
  --
  -- Over a singleton state family.
  --
  -- 单点状态族上的常余代数，及其展开的常树

  γId : MO.Coalgebra Cn TrivFC lzero (λ _ → ⊤)
  MO.Coalgebra.label γId _ tt = dId
  MO.Coalgebra.child γId _ tt _ = tt

  γC0 : MO.Coalgebra Cn TrivFC lzero (λ _ → ⊤)
  MO.Coalgebra.label γC0 _ tt = dC0
  MO.Coalgebra.child γC0 _ tt _ = tt

  treeId : (i : MO.I Cn TrivFC) → MO.CosmosM Cn TrivFC i
  treeId i = MO.ana Cn TrivFC γId i tt

  treeC0 : (i : MO.I Cn TrivFC) → MO.CosmosM Cn TrivFC i
  treeC0 i = MO.ana Cn TrivFC γC0 i tt

  -- The distinguishing index: the second object paired with the unique
  -- shape; it exists only because n ≥ 2.
  --
  -- 区分性索引：第二个对象配上唯一形状；它仅因 n ≥ 2 而存在。
  i₁ : MO.I Cn TrivFC
  i₁ = fsuc fzero , tt

  ----------------------------------------------------------------------
  -- Non-bisimilarity
  --
  -- Projecting uf.F₀ at i₁ turns a head-label equality into
  -- fsuc fzero ≡ fzero, absorbed by the empty pattern.
  --
  -- 非互模拟
  --
  -- 在 i₁ 处投影 uf.F₀ 把头标签等式变为 fsuc fzero ≡ fzero，由空模式
  -- 吸收。

  idN≉const0N
    : ¬ MO.≈CosmosM Cn TrivFC (λ _ → propEqOn _)
          (treeId i₁) (treeC0 i₁)
  idN≉const0N b
    with cong (λ d → F₀ (MO.CosmosData.uf d) i₁) (here-eq b)
  ... | ()
