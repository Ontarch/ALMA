------------------------------------------------------------------------
-- Container instance of the M-Cosmos: type seam
--
-- Pins down where the old container Cosmos (terminal coalgebra with
-- deterministic shape-functor morphisms _⇒ℱ[S]_) lives as a special
-- case of the strictly stronger M-Cosmos: index relation R is the
-- propositional graph of S.₀, labels are compared propositionally, and
-- the edge FiberAdjˢ is the onPos adjunction (fro = onPos, η/ε
-- replacing the old pts-compat / onActP with no subst). The general
-- M-Cosmos strictly generalises this by allowing a non-propositional
-- label EqOn and an arbitrary (non-graph) index relation.
--
-- M-Cosmos 的容器实例：类型接缝
--
-- 钉住旧容器 Cosmos（带确定性形状函子态射 _⇒ℱ[S]_ 的终余代数）作为
-- 严格更强 M-Cosmos 的特例所处的位置：索引关系 R 是 S.₀ 的命题图，
-- 标签按命题比较，边 FiberAdjˢ 是 onPos 伴随（fro = onPos，η/ε 取代旧
-- pts-compat / onActP，不用 subst）。一般 M-Cosmos 严格推广它：允许
-- 非命题标签 EqOn 与任意（非图）索引关系。
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module ALMA.Cosmos.M.ContainerInstance where

open import Agda.Primitive using (Level; _⊔_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Sigma using (Σ; _,_)
open import Data.Product.Base using (proj₁)
open import Relation.Binary.PropositionalEquality.Core using (cong)

open import Categories.Category.Core using (Category)
open import Categories.Functor.Core using (Functor)
open import Categories.Functor using () renaming (id to idF)

open import ALMA.Base.MCorrSetoid using (EqOn; propEqOn; FiberAdjˢ; idAdjˢ; Stepˢ)
open import ALMA.Base.MCorrSetoidCat using (FMapˢ; FMˢ; idFMˢ)
open import ALMA.Cosmos.ContCategory using (ContCat)
open import ALMA.Cosmos.ContCatEquiv using (ShapeCat)
open import ALMA.Cosmos.M.Object as MO

module _ {o h e s p : Level}
         (C  : Category o h e)
         (FC : Functor C (ContCat s p)) where

  -- The propositional graph of a shape endofunctor on the index.
  --
  -- 形状自函子在索引上的命题图。
  Graph : Functor (ShapeCat C FC) (ShapeCat C FC)
        → MO.I C FC → MO.I C FC → Set (o ⊔ s)
  Graph S i j = Functor.F₀ S i ≡ j

  propLabel : (i : MO.I C FC)
            → EqOn {ℓ = o ⊔ h ⊔ e ⊔ s ⊔ p} (MO.CosmosData C FC)
  propLabel _ = propEqOn _

  -- Carried type of the old deterministic _⇒ℱ[S]_.
  --
  -- 旧确定性 _⇒ℱ[S]_ 的携带式类型。
  DetCosmosM⇒ : Functor (ShapeCat C FC) (ShapeCat C FC)
              → Set (o ⊔ h ⊔ e ⊔ s ⊔ p)
  DetCosmosM⇒ S = MO.CosmosM⇒ C FC propLabel (Graph S)

  -- Graph id is definitionally the index path relation, so the carried
  -- morphism is idCosmosM: this recovers the old id⇒ℱ.
  --
  -- Graph id 定义性地为索引路径关系，故携带态射为 idCosmosM：恢复
  -- 旧 id⇒ℱ。
  Det-id : DetCosmosM⇒ idF
  Det-id = MO.idCosmosM C FC propLabel

  ----------------------------------------------------------------------
  -- Carried construction data for a deterministic S-morphism
  --
  -- 确定性 S-态射的携带式构造数据

  private
    f₀ : (S : Functor (ShapeCat C FC) (ShapeCat C FC))
       → MO.I C FC → MO.I C FC
    f₀ S = Functor.F₀ S

    sysP = MO.sys C FC propLabel

  record DetData (S : Functor (ShapeCat C FC) (ShapeCat C FC))
         : Set (o ⊔ h ⊔ e ⊔ s ⊔ p) where
    field
      -- Index-aware label map: the old morphism builds this layerwise
      -- from the two unfoldings and the shape natural isomorphism, so
      -- it must see the source index x.
      --
      -- 索引感知的标签映射：旧态射由两个 unfolding 与形状自然同构逐层
      -- 构造它，故必须见到源索引 x。
      labelMap : (x : MO.I C FC) (d : MO.CosmosData C FC)
               → MO.CosmosData C FC
      -- Coverage of S.₀: the deterministic analogue of FMap.childF.
      --
      -- S.₀ 的覆盖：FMap.childF 的确定性对应物。
      pullback : (d : MO.CosmosData C FC) (v : MO.I C FC)
               → Σ (MO.I C FC) λ x' → f₀ S x' ≡ v
      -- fro is the old onPos; to/η/ε are the carried replacements for
      -- pts-compat / onActP.
      --
      -- fro 即旧 onPos；to/η/ε 是 pts-compat / onActP 的携带式替代。
      edgeAdj  : (x : MO.I C FC) (d : MO.CosmosData C FC)
                 (v : MO.I C FC)
                 (pb : Σ (MO.I C FC) λ x' → f₀ S x' ≡ v)
               → FiberAdjˢ (propEqOn (MO.E C FC (f₀ S x) (labelMap x d) v))
                            (propEqOn (MO.E C FC x d (proj₁ pb)))
  open DetData public

  -- One deterministic step: matching refl pins the target index to
  -- S.₀ x; child is the supplied pullback and edge-adj the supplied
  -- adjunction. No equality is eliminated.
  --
  -- 一个确定性步：匹配 refl 把目标索引钉为 S.₀ x；child 取所供
  -- pullback，edge-adj 取所供伴随。不消去任何等式。
  private
    detStep : (S : Functor (ShapeCat C FC) (ShapeCat C FC))
              (dd : DetData S)
            → ∀ {x y : MO.I C FC} (r : Graph S x y)
            → Stepˢ sysP sysP (Graph S) r
    detStep S dd {x = x₀} {y = .(f₀ S x₀)} refl = record
      { shapeᴿ = labelMap dd x₀
      ; child   = λ d v → pullback dd d v
      ; edge-adj = λ d v → edgeAdj dd x₀ d v (pullback dd d v)
      }

  mkDetCosmosM⇒ : (S : Functor (ShapeCat C FC) (ShapeCat C FC))
                → DetData S → DetCosmosM⇒ S
  mkDetCosmosM⇒ S dd = record { step = detStep S dd }

  ----------------------------------------------------------------------
  -- Identity lifting
  --
  -- Base case of the adjunction+coverage supply; validates the DetData
  -- interface end to end.
  --
  -- 恒等提升
  --
  -- 伴随+覆盖供给的基例；端到端验证 DetData 接口。

  detData-id : DetData idF
  DetData.labelMap detData-id _ d = d
  DetData.pullback detData-id _ v = v , refl
  DetData.edgeAdj  detData-id x d v₀ (v , refl) =
    idAdjˢ (propEqOn (MO.E C FC x d v))

  ----------------------------------------------------------------------
  -- Pointwise assembly of FMapˢ from DetData
  --
  -- u is S.₀ (its propositional graph is the unique witness refl used
  -- by asMorphˢ), shape is labelMap, the canonical child is the
  -- pullback and the edge adjunction is edgeAdj.
  --
  -- 由 DetData 逐点装配 FMapˢ
  --
  -- u 为 S.₀（其命题图即 asMorphˢ 所用的唯一见证 refl），shape 为
  -- labelMap，规范子节点为 pullback，边伴随为 edgeAdj。

  detFMapˢ : (S : Functor (ShapeCat C FC) (ShapeCat C FC))
           → DetData S → FMapˢ sysP sysP
  FMapˢ.u      (detFMapˢ S dd) = f₀ S
  FMapˢ.shape  (detFMapˢ S dd) x d = labelMap dd x d
  FMapˢ.childF (detFMapˢ S dd) x d v = pullback dd d v
  FMapˢ.adjFˢ  (detFMapˢ S dd) x d v =
    edgeAdj dd x d v (pullback dd d v)

  ----------------------------------------------------------------------
  -- Categorical endomorphism bundle
  --
  -- The congruence FMˢ.map-cong must be carried as data: it cannot be
  -- reconstructed from the pointwise DetData fields, since FMapˢ
  -- deliberately drops childF-coh and no pointwise link across a head
  -- equality is derivable without K or subst. The identity S supplies
  -- its bundle canonically as detFMˢ-id = idFMˢ; a non-identity S
  -- supplies its map-cong from its onPos round-trip data.
  --
  -- 范畴自态射束
  --
  -- 同余 FMˢ.map-cong 必须作为数据携带：它无法由 DetData 的逐点字段
  -- 重建，因 FMapˢ 刻意删除 childF-coh，跨头部等式的逐点联系在不用 K
  -- 或 subst 时无法导出。恒等 S 典范地以 detFMˢ-id = idFMˢ 供给其束；
  -- 非恒等 S 由其 onPos 往返数据供给 map-cong。

  mkDetFMˢ : (S : Functor (ShapeCat C FC) (ShapeCat C FC))
             (dd : DetData S)
           → ( ∀ {x : MO.I C FC} {t s : MO.CosmosM C FC x}
             → MO.≈CosmosM C FC propLabel t s
             → MO.≈CosmosM C FC propLabel
                 (FMapˢ.mapFˢ (detFMapˢ S dd) x t)
                 (FMapˢ.mapFˢ (detFMapˢ S dd) x s) )
           → FMˢ sysP sysP
  mkDetFMˢ S dd mc = record
    { mor        = detFMapˢ S dd
    ; shape-cong = λ {x = x} {a₁} {a₂} ea → cong (labelMap dd x) ea
    ; map-cong   = mc
    }

  detFMˢ-id : FMˢ sysP sysP
  detFMˢ-id = idFMˢ {X = sysP}
