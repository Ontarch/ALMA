------------------------------------------------------------------------
-- Structured carried endomorphisms versus coalgebra homomorphisms
--
-- The non-fullness counterexample on the M base. The legacy inclusion
-- CoalgHom → StructuredFunc is not full. On M two things change: a
-- carried categorical morphism FMˢ must carry an index pullback
-- (coverage) and a whole-fibre FiberAdjˢ, so the legacy collapse
-- toOther is refused as a morphism altogether (its constant index map
-- is not surjective and the position fibres have different
-- cardinality); and the genuine non-fullness is witnessed by swapFMˢ
-- (ListSwap), a carried morphism that DOES carry a fibre bijection.
-- Applied to the constant dList tree it produces the constant dSwap
-- tree, whose head label routes position 0 of shape 2 to child shape 1
-- rather than 0, so the two trees are not bisimilar. The forward
-- inclusion is the terminality theorem !-unique in CoalgCat; this
-- module supplies the strictness witness. Everything is propositional
-- and constructive; the head mismatch is absorbed by the empty pattern.
--
-- 结构化携带自态射与余代数同态
--
-- 在 M 底座上重建的非满性反例。旧包含 CoalgHom → StructuredFunc 非满。
-- 在 M 上两处变化：携带式范畴态射 FMˢ 必须携带索引 pullback（覆盖）与
-- 整纤维 FiberAdjˢ，故旧折叠 toOther 根本不被承认为态射（其常值索引映射
-- 不满，位置纤维基数不同）；真正的非满性由 swapFMˢ（ListSwap）见证：它
-- 确带纤维双射，作用于常 dList 树得到常 dSwap 树，其头标签把形状 2 的
-- 位置 0 路由到子形状 1 而非 0，故两树不互模拟。正向包含即 CoalgCat 的
-- 终性定理 !-unique；本模块供给严格性见证。全部命题且构造性；头部失配
-- 由空模式吸收。
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module ALMA.Cosmos.M.MorphismCorrespondence where

open import Agda.Primitive using (lzero)
open import Data.Unit.Polymorphic.Base using (⊤; tt)
open import Data.Fin.Base using (zero)
open import Data.Product.Base using (Σ; _,_)
open import Relation.Binary.PropositionalEquality.Core using (cong)
open import Relation.Nullary.Negation using (¬_)

open import ALMA.Base.MCorrSetoid using (propEqOn; here-eq)
open import ALMA.Base.MCorrSetoidCat using (FMˢ; FMapˢ)
import ALMA.Cosmos.M.Object as MO
import ALMA.Cosmos.M.ListSwap as LS

------------------------------------------------------------------------
-- The list universe and the carried system
--
-- Reused from ListSwap.
--
-- 列表宇宙与携带系统
--
-- 复用 ListSwap。

private
  C₀ = LS.C₀
  ListFC = LS.ListFC

  sysP = MO.sys C₀ ListFC (λ _ → propEqOn _)

  dList = LS.dList

  -- StructuredEndo is a carried congruent system endomorphism (an FMˢ
  -- bundle), the M-base counterpart of the legacy StructuredFunc.
  --
  -- StructuredEndo 是携带式同余系统自态射（FMˢ 束），旧 StructuredFunc
  -- 的 M 底座对应物。
  StructuredEndo : Set lzero
  StructuredEndo = FMˢ sysP sysP

  swapSF : StructuredEndo
  swapSF = LS.swapFMˢ

  -- The coalgebra-endo commutation for an INDEX-PRESERVING structured
  -- endomorphism: its tree map fixes every tree up to ≈CosmosM. The
  -- predicate is stated concretely at swapFMˢ (u = id); a general FMˢ
  -- with non-identity u is a map between distinct indices and is not a
  -- terminal-coalgebra endomorphism in this sense.
  --
  -- 索引保持型结构化自态射的余代数自态射交换：树映射在 ≈CosmosM 下固定
  -- 每棵树。谓词对 swapFMˢ（u = id）具体陈述；u 非恒等的一般 FMˢ 是
  -- 不同索引间的映射，不属于此意义下的终余代数自态射。
  swap-commutes : Set lzero
  swap-commutes =
    ∀ (i : MO.I C₀ ListFC) (t : MO.CosmosM C₀ ListFC i)
    → MO.≈CosmosM C₀ ListFC (λ _ → propEqOn _)
        (FMapˢ.mapFˢ (FMˢ.mor swapSF) i t) t

  ----------------------------------------------------------------------
  -- The constant dList coalgebra and the two trees at shape 2
  --
  -- 常 dList 余代数与形状 2 处的两棵树

  γList : MO.Coalgebra C₀ ListFC lzero (λ _ → ⊤)
  MO.Coalgebra.label γList _ tt = dList
  MO.Coalgebra.child γList _ tt _ = tt

  listTree : (i : MO.I C₀ ListFC) → MO.CosmosM C₀ ListFC i
  listTree i = MO.ana C₀ ListFC γList i tt

  swappedTree : (i : MO.I C₀ ListFC) → MO.CosmosM C₀ ListFC i
  swappedTree i = FMapˢ.mapFˢ (FMˢ.mor LS.swapFMˢ) i (listTree i)

  ----------------------------------------------------------------------
  -- Pointwise failure at shape 2, position zero
  --
  -- pts dList 2 zero = 0 and pts dSwap 2 zero = toℕ (opposite zero) = 1.
  -- The n = 2 clause of swap01 is definitionally opposite, so this is a
  -- definitional 1 vs 0 mismatch; a bisimulation would carry a head
  -- label equality dSwap ≡ dList, and projecting at shape 2 position
  -- zero yields 1 ≡ 0.
  --
  -- 形状 2、位置 zero 处的点态失败
  --
  -- pts dList 2 zero = 0，pts dSwap 2 zero = toℕ (opposite zero) = 1。
  -- swap01 的 n = 2 子句定义性为 opposite，故这是定义性的 1 对 0 失配；
  -- 互模拟会携带头标签等式 dSwap ≡ dList，投影出形状 2、位置 zero 处的
  -- 路由得 1 ≡ 0。

  swap-not-commute :
    ¬ MO.≈CosmosM C₀ ListFC (λ _ → propEqOn _)
        (swappedTree (tt , 2)) (listTree (tt , 2))
  swap-not-commute b
    with cong (λ d → MO.CosmosData.pts d 2 zero) (here-eq b)
  ... | ()

  ----------------------------------------------------------------------
  -- swapFMˢ is a StructuredEndo but not a coalgebra endomorphism
  --
  -- Hence the forgetful map CoalgHom → StructuredFunc is not full.
  --
  -- swapFMˢ 是 StructuredEndo，但不是余代数自态射
  --
  -- 故忘却映射 CoalgHom → StructuredFunc 非满。

  swapSF-not-CoalgEndo : ¬ swap-commutes
  swapSF-not-CoalgEndo h =
    swap-not-commute (h (tt , 2) (listTree (tt , 2)))

  not-full : Σ StructuredEndo λ _ → ¬ swap-commutes
  not-full = swapSF , swapSF-not-CoalgEndo
