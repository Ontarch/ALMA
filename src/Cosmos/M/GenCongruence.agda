------------------------------------------------------------------------
-- Deterministic congruence engine for the LABEL-CHANGING container
-- regime, strictly generalising DetCongruence
--
-- A carried label action σ : (x : I) → CosmosData → CosmosData replaces
-- the identity label map, so the image tree at F₀ S x carries the
-- (possibly different) label σ x d. This is the regime of the old
-- label-changing _⇒ℱ_ witnesses such as the list swap01. The canonical
-- child coverage stays label-independent, so the coinductive engine is
-- structurally the fixed-label one; the only change is that the target
-- edge fibres carry σ x dT / σ x dS instead of dT / dS. The fixed-label
-- engine is the special case σ x d = d (DetCongruence).
--
-- 改标签容器制度下的确定性同余引擎，严格泛化 DetCongruence
--
-- 携带的标签作用 σ : (x : I) → CosmosData → CosmosData 取代恒等标签
-- 映射，使 F₀ S x 处的像树携带（可能不同的）标签 σ x d。这正是旧的
-- 改标签 _⇒ℱ_ 见证（如列表 swap01）所处的制度。规范子覆盖仍与标签
-- 无关，故余归纳引擎与固定标签版结构相同；唯一变化是目标边纤维携带
-- σ x dT / σ x dS 而非 dT / dS。固定标签引擎是 σ x d = d 的特例
-- （DetCongruence）。
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module Cosmos.M.GenCongruence where

open import Agda.Primitive using (Level; _⊔_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Sigma using (Σ; _,_)
open import Data.Product.Base using (proj₁; proj₂)
open import Relation.Binary.PropositionalEquality.Core using (cong)

open import Categories.Category.Core using (Category)
open import Categories.Functor.Core using (Functor)

open import Base.MCorr using (M)
open import Base.MCorr.Setoid using
  (EqOn; SysEq; propEqOn; FiberAdjˢ; symAdjˢ; compAdjˢ; Morphˢ; here-eq
  ; below-eq; ≈Mˢ-refl; ≈Mˢ-sym; ≈Mˢ-trans)
open import Base.MCorr.SetoidCat using (FMapˢ; FMˢ)
open import Cosmos.ContCategory using (ContCat)
open import Cosmos.ContCatEquiv using (ShapeCat)
open import Cosmos.M.Object using (I; E; sys; CosmosM; CosmosData; ≈CosmosM)

module _ {o h e s p : Level}
         (C  : Category o h e)
         (FC : Functor C (ContCat s p)) where

  private
    iL = o ⊔ s
    aL = o ⊔ h ⊔ e ⊔ s ⊔ p
    bL = o ⊔ s ⊔ p

    propLabel : (i : I C FC) → EqOn {ℓ = aL} (CosmosData C FC)
    propLabel _ = propEqOn _

    sysP : SysEq iL aL bL aL bL
    sysP = sys C FC propLabel

    ≈A = SysEq.≈A sysP
    ≈E = SysEq.≈E sysP

    EM = E C FC

  ----------------------------------------------------------------------
  -- General deterministic data
  --
  -- A carried label action σ together with a label-independent coverage
  -- pullback and a per-label edge adjunction. This is the carried shape
  -- of a label-changing deterministic container endomorphism.
  --
  -- 一般确定性数据
  --
  -- 携带的标签作用 σ，连同与标签无关的覆盖拉回和逐标签边伴随。这是
  -- 改标签确定性容器自态射的携带形状。

  record GenDet (S : Functor (ShapeCat C FC) (ShapeCat C FC))
         : Set aL where
    field
      σ   : (x : I C FC) → CosmosData C FC → CosmosData C FC
      pb  : (v : I C FC)
          → Σ (I C FC) λ x' → Functor.F₀ S x' ≡ v
      adj : (x : I C FC) (d : CosmosData C FC) (v : I C FC)
          → FiberAdjˢ (propEqOn (EM (Functor.F₀ S x) (σ x d) v))
                      (propEqOn (EM x d (proj₁ (pb v))))
  open GenDet public

  ----------------------------------------------------------------------
  -- Underlying deterministic carried functor
  --
  -- Labels acted on by σ.
  --
  -- 底层确定性携带函子
  --
  -- 标签由 σ 作用。

  genFMapˢ : (S : Functor (ShapeCat C FC) (ShapeCat C FC))
              (g : GenDet S) → FMapˢ sysP sysP
  FMapˢ.u      (genFMapˢ S g) = Functor.F₀ S
  FMapˢ.shape  (genFMapˢ S g) x d = σ g x d
  FMapˢ.childF (genFMapˢ S g) x d v = pb g v
  FMapˢ.adjFˢ  (genFMapˢ S g) x d v = adj g x d v

  ----------------------------------------------------------------------
  -- Edge relocation under the propositional edge EqOn
  --
  -- 命题边 EqOn 下的边重定位

  private
    edge-reloc : ∀ {x y : I C FC}
                 (u : CosmosM C FC x)
                 {e e' : EM x (M.here u) y}
               → e ≡ e'
               → ≈CosmosM C FC propLabel
                   (M.below u y e) (M.below u y e')
    edge-reloc u {e = z} {e' = .z} refl =
      ≈Mˢ-refl ≈A ≈E (M.below u _ z)

  private
    mapR-of : (S : Functor (ShapeCat C FC) (ShapeCat C FC))
              (g : GenDet S)
            → ∀ {x v} → Functor.F₀ S x ≡ v
            → CosmosM C FC x → CosmosM C FC v
    mapR-of S g = Morphˢ.mapR (FMapˢ.asMorphˢ (genFMapˢ S g))

  ----------------------------------------------------------------------
  -- The coinductive congruence engine
  --
  -- Structurally the fixed-label one: both below fields are direct
  -- guarded go calls, the backward one first reversing the source-level
  -- bisimulation with ≈Mˢ-sym; the target fibre labels are
  -- σ x dT / σ x dS.
  --
  -- 余归纳同余引擎
  --
  -- 结构与固定标签版相同：两个 below 字段都是直接受保护的 go 调用，
  -- 反向先以 ≈Mˢ-sym 反转源层互模拟；目标纤维标签为 σ x dT / σ x dS。
  private
    go : (S : Functor (ShapeCat C FC) (ShapeCat C FC))
         (g : GenDet S)
       → ∀ {x v : I C FC} (r : Functor.F₀ S x ≡ v)
         {t s : CosmosM C FC x}
       → ≈CosmosM C FC propLabel t s
       → ≈CosmosM C FC propLabel (mapR-of S g r t) (mapR-of S g r s)
    go S g {x = x} {.(Functor.F₀ S x)} refl {t = t} {s = s} h
        .here-eq = cong (σ g x) (h .here-eq)
    go S g {x = x} {.(Functor.F₀ S x)} refl {t = t} {s = s} h
        .below-eq v =
        adjOut , ( (λ q → go S g eqw (hF q))
                 , (λ r → go S g eqw (≈Mˢ-sym ≈A ≈E (hT r))) )
      where
      dT  = M.here t
      dS  = M.here s
      dTσ = σ g x dT
      dSσ = σ g x dS
      x'  = proj₁ (pb g v)
      eqw = proj₂ (pb g v)

      Aₜ : FiberAdjˢ (propEqOn (EM (Functor.F₀ S x) dTσ v))
                     (propEqOn (EM x dT x'))
      Aₜ = adj g x dT v

      Aₛ : FiberAdjˢ (propEqOn (EM (Functor.F₀ S x) dSσ v))
                     (propEqOn (EM x dS x'))
      Aₛ = adj g x dS v

      adjH : FiberAdjˢ (propEqOn (EM x dS x'))
                       (propEqOn (EM x dT x'))
      adjH = proj₁ (h .below-eq x')

      hfwd : ∀ (e₁ : EM x dT x')
           → ≈CosmosM C FC propLabel
               (M.below t x' e₁)
               (M.below s x' (FiberAdjˢ.to adjH e₁))
      hfwd = proj₁ (proj₂ (h .below-eq x'))

      hbwd : ∀ (e₂ : EM x dS x')
           → ≈CosmosM C FC propLabel
               (M.below s x' e₂)
               (M.below t x' (FiberAdjˢ.fro adjH e₂))
      hbwd = proj₂ (proj₂ (h .below-eq x'))

      -- Stage 1: target-t ET → source-t Tsrc (sym Aₜ), then Tsrc →
      -- source-s Ssrc (adjH); overall FiberAdjˢ Ssrc ET.
      --
      -- 第一阶段：target-t ET → source-t Tsrc（sym Aₜ），再 Tsrc →
      -- source-s Ssrc（adjH）；整体为 FiberAdjˢ Ssrc ET。
      c1 : FiberAdjˢ (propEqOn (EM x dS x'))
                     (propEqOn (EM (Functor.F₀ S x) dTσ v))
      c1 = compAdjˢ (propEqOn (EM (Functor.F₀ S x) dTσ v))
                    (propEqOn (EM x dT x'))
                    (propEqOn (EM x dS x'))
                    (symAdjˢ Aₜ) adjH

      adjOut : FiberAdjˢ (propEqOn (EM (Functor.F₀ S x) dSσ v))
                        (propEqOn (EM (Functor.F₀ S x) dTσ v))
      adjOut = compAdjˢ (propEqOn (EM (Functor.F₀ S x) dTσ v))
                        (propEqOn (EM x dS x'))
                        (propEqOn (EM (Functor.F₀ S x) dSσ v))
                        c1 Aₛ

      -- Forward source-level child bisimulation; built only from h and
      -- edge-reloc, so no go call occurs here.
      --
      -- 正向的源层子互模拟；仅由 h 与 edge-reloc 构造，其中无 go。
      hF : ∀ (q : EM (Functor.F₀ S x) dTσ v)
         → ≈CosmosM C FC propLabel
             (M.below t x' (FiberAdjˢ.fro Aₜ q))
             (M.below s x' (FiberAdjˢ.fro Aₛ (FiberAdjˢ.to adjOut q)))
      hF q =
        let eT = FiberAdjˢ.fro Aₜ q
            eS = FiberAdjˢ.to adjH eT
        in ≈Mˢ-trans ≈A ≈E (hfwd eT)
               (≈Mˢ-sym ≈A ≈E (edge-reloc s (FiberAdjˢ.η Aₛ eS)))

      -- Backward source-level child bisimulation, oriented t-child ≈
      -- s-child so that a single go (then image symmetry ≈Mˢ-sym) gives
      -- the goal.
      --
      -- 反向的源层子互模拟，方向取 t-子 ≈ s-子，使单个 go（再取像对称
      -- ≈Mˢ-sym）即得目标。
      hT : ∀ (r : EM (Functor.F₀ S x) dSσ v)
         → ≈CosmosM C FC propLabel
             (M.below t x' (FiberAdjˢ.fro Aₜ (FiberAdjˢ.fro adjOut r)))
             (M.below s x' (FiberAdjˢ.fro Aₛ r))
      hT r =
        let eSsrc = FiberAdjˢ.fro Aₛ r
            z     = FiberAdjˢ.fro adjH eSsrc
        in ≈Mˢ-trans ≈A ≈E (edge-reloc t (FiberAdjˢ.η Aₜ z))
               (≈Mˢ-sym ≈A ≈E (hbwd eSsrc))

  ----------------------------------------------------------------------
  -- mapFˢ is mapR along refl, so the congruence is go refl.
  --
  -- mapFˢ 即沿 refl 的 mapR，故同余为 go refl。

  gen-map-cong : (S : Functor (ShapeCat C FC) (ShapeCat C FC))
                 (g : GenDet S)
               → ∀ {x : I C FC} {t s : CosmosM C FC x}
               → ≈CosmosM C FC propLabel t s
               → ≈CosmosM C FC propLabel
                   (FMapˢ.mapFˢ (genFMapˢ S g) x t)
                   (FMapˢ.mapFˢ (genFMapˢ S g) x s)
  gen-map-cong S g = go S g refl

  ----------------------------------------------------------------------
  -- Categorical endomorphism bundle
  --
  -- shape-cong is the propositional congruence of σ; map-cong is the
  -- coinductive engine.
  --
  -- 范畴自态射束
  --
  -- shape-cong 为 σ 的命题同余；map-cong 为余归纳引擎。

  genFMˢ : (S : Functor (ShapeCat C FC) (ShapeCat C FC))
           (g : GenDet S) → FMˢ sysP sysP
  genFMˢ S g = record
    { mor        = genFMapˢ S g
    ; shape-cong = λ {x} {d} {d'} eq → cong (σ g x) eq
    ; map-cong   = gen-map-cong S g
    }
