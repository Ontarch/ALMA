------------------------------------------------------------------------
-- Deterministic congruence engine for the fixed-label container regime
--
-- The setoid analogue of the propositional "gow" relabelling machine.
-- Under the two conditions that model the old deterministic container
-- endomorphism _⇒ℱ[S]_ on a FIXED Cosmos — labels are preserved (the
-- deterministic shape action is the identity) and the canonical child
-- pullback is label-independent — the cross-label child coherence that
-- the propositional gow carried as childF-coh is DEFINITIONAL. The
-- engine go is a single coinductive function indexed by the
-- (propositional, not necessarily refl) graph witness, defined by J
-- with the witness generalised to refl.
--
-- 固定标签容器制度下的确定性同余引擎
--
-- 命题版 "gow" 重排机器的 setoid 对应物。在真正刻画固定 Cosmos 上旧
-- 确定性容器自态射 _⇒ℱ[S]_ 的两条条件下——标签保持（确定性 shape 作用
-- 为恒等）、规范子拉回与标签无关——命题版 gow 须作为 childF-coh 携带
-- 的跨标签子相干是定义性的。引擎 go 是单个余归纳函数，以（命题的、未必
-- refl 的）图见证为索引，在刚性索引变量上用 J 把见证一般化为 refl 来
-- 定义。
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module ALMA.Cosmos.M.DetCongruence where

open import Agda.Primitive using (Level; _⊔_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Sigma using (Σ; _,_)
open import Data.Product.Base using (proj₁; proj₂)

open import Categories.Category.Core using (Category)
open import Categories.Functor.Core using (Functor)

open import ALMA.Base.MCorr using (M)
open import ALMA.Base.MCorrSetoid using
  (EqOn; SysEq; propEqOn; FiberAdjˢ; symAdjˢ; compAdjˢ; Morphˢ
  ; _≈Mˢ_; here-eq; below-eq; ≈Mˢ-refl; ≈Mˢ-sym; ≈Mˢ-trans)
open import ALMA.Base.MCorrSetoidCat using (FMapˢ; FMˢ)
open import ALMA.Cosmos.ContCategory using (ContCat)
open import ALMA.Cosmos.ContCatEquiv using (ShapeCat)
open import ALMA.Cosmos.M.Object as MO

module _ {o h e s p : Level}
         (C  : Category o h e)
         (FC : Functor C (ContCat s p)) where

  private
    iL = o ⊔ s
    aL = o ⊔ h ⊔ e ⊔ s ⊔ p
    bL = o ⊔ s ⊔ p

    propLabel : (i : MO.I C FC) → EqOn {ℓ = aL} (MO.CosmosData C FC)
    propLabel _ = propEqOn _

    sysP : SysEq iL aL bL aL bL
    sysP = MO.sys C FC propLabel

    ≈A = SysEq.≈A sysP
    ≈E = SysEq.≈E sysP

    EM = MO.E C FC

  ----------------------------------------------------------------------
  -- Uniform deterministic data
  --
  -- Label-preserving with a label-independent coverage pullback; the
  -- onPos bijection supplies the per-label edge adjunction.
  --
  -- 一致确定性数据
  --
  -- 标签保持且覆盖拉回与标签无关；onPos 双射供给逐标签边伴随。

  record UniDet (S : Functor (ShapeCat C FC) (ShapeCat C FC))
         : Set aL where
    field
      pb  : (v : MO.I C FC)
          → Σ (MO.I C FC) λ x' → Functor.F₀ S x' ≡ v
      adj : (x : MO.I C FC) (d : MO.CosmosData C FC) (v : MO.I C FC)
          → FiberAdjˢ (propEqOn (EM (Functor.F₀ S x) d v))
                      (propEqOn (EM x d (proj₁ (pb v))))
  open UniDet public

  ----------------------------------------------------------------------
  -- Underlying deterministic carried functor with labels fixed
  --
  -- 底层确定性携带函子，标签固定

  uniFMapˢ : (S : Functor (ShapeCat C FC) (ShapeCat C FC))
             (u : UniDet S) → FMapˢ sysP sysP
  FMapˢ.u      (uniFMapˢ S u) = Functor.F₀ S
  FMapˢ.shape  (uniFMapˢ S u) x d = d
  FMapˢ.childF (uniFMapˢ S u) x d v = pb u v
  FMapˢ.adjFˢ  (uniFMapˢ S u) x d v = adj u x d v

  ----------------------------------------------------------------------
  -- Edge relocation under the propositional edge EqOn
  --
  -- Matching the equality with a rigid edge variable is a legal J step
  -- (z is generalised, not a neutral projection).
  --
  -- 命题边 EqOn 下的边重定位
  --
  -- 用刚性边变量匹配该等式是合法 J 步骤（z 被一般化，不是中性投影）。

  private
    edge-reloc : ∀ {x y : MO.I C FC}
                 (u : MO.CosmosM C FC x)
                 {e e' : EM x (M.here u) y}
               → e ≡ e'
               → MO.≈CosmosM C FC propLabel
                   (M.below u y e) (M.below u y e')
    edge-reloc u {e = z} {e' = .z} refl =
      ≈Mˢ-refl ≈A ≈E (M.below u _ z)

  ----------------------------------------------------------------------
  -- The coinductive congruence engine go
  --
  -- Indexed by the graph witness r : F₀ S x ≡ v and defined by J with
  -- r refl. Child coverage pb v = (x' , eqw) keeps eqw neutral and
  -- recurses directly; both below fields are direct guarded go calls,
  -- and the backward one first reverses the source-level bisimulation
  -- with the non-recursive ≈Mˢ-sym.
  --
  -- 余归纳同余引擎 go
  --
  -- 以图见证 r : F₀ S x ≡ v 为索引，用 J 以 r refl 定义。子覆盖
  -- pb v = (x' , eqw) 保持 eqw 中性并直接递归；两个 below 字段都是
  -- 直接受保护的 go 调用，反向先以非递归的 ≈Mˢ-sym 反转源层互模拟。

  private
    mapR-of : (S : Functor (ShapeCat C FC) (ShapeCat C FC))
              (u : UniDet S)
            → ∀ {x v} → Functor.F₀ S x ≡ v
            → MO.CosmosM C FC x → MO.CosmosM C FC v
    mapR-of S u = Morphˢ.mapR (FMapˢ.asMorphˢ (uniFMapˢ S u))

    go : (S : Functor (ShapeCat C FC) (ShapeCat C FC))
         (u : UniDet S)
       → ∀ {x v : MO.I C FC} (r : Functor.F₀ S x ≡ v)
         {t s : MO.CosmosM C FC x}
       → MO.≈CosmosM C FC propLabel t s
       → MO.≈CosmosM C FC propLabel (mapR-of S u r t) (mapR-of S u r s)
    go S u {x = x} {.(Functor.F₀ S x)} refl {t = t} {s = s} h
        .here-eq = h .here-eq
    go S u {x = x} {.(Functor.F₀ S x)} refl {t = t} {s = s} h
        .below-eq v =
        adjOut , ( (λ q → go S u eqw (hF q))
                 , (λ r → go S u eqw (≈Mˢ-sym ≈A ≈E (hT r))) )
      where
      dT = M.here t
      dS = M.here s
      x'  = proj₁ (pb u v)
      eqw = proj₂ (pb u v)

      Aₜ : FiberAdjˢ (propEqOn (EM (Functor.F₀ S x) dT v))
                     (propEqOn (EM x dT x'))
      Aₜ = adj u x dT v

      Aₛ : FiberAdjˢ (propEqOn (EM (Functor.F₀ S x) dS v))
                     (propEqOn (EM x dS x'))
      Aₛ = adj u x dS v

      adjH : FiberAdjˢ (propEqOn (EM x dS x'))
                       (propEqOn (EM x dT x'))
      adjH = proj₁ (h .below-eq x')

      hfwd : ∀ (e₁ : EM x dT x')
           → MO.≈CosmosM C FC propLabel
               (M.below t x' e₁)
               (M.below s x' (FiberAdjˢ.to adjH e₁))
      hfwd = proj₁ (proj₂ (h .below-eq x'))

      hbwd : ∀ (e₂ : EM x dS x')
           → MO.≈CosmosM C FC propLabel
               (M.below s x' e₂)
               (M.below t x' (FiberAdjˢ.fro adjH e₂))
      hbwd = proj₂ (proj₂ (h .below-eq x'))

      -- Stage 1: target-t ET → source-t Tsrc (sym Aₜ), then Tsrc →
      -- source-s Ssrc (adjH); overall FiberAdjˢ Ssrc ET.
      --
      -- 第一阶段：target-t ET → source-t Tsrc（sym Aₜ），再 Tsrc →
      -- source-s Ssrc（adjH）；整体为 FiberAdjˢ Ssrc ET。
      c1 : FiberAdjˢ (propEqOn (EM x dS x'))
                     (propEqOn (EM (Functor.F₀ S x) dT v))
      c1 = compAdjˢ (propEqOn (EM (Functor.F₀ S x) dT v))
                    (propEqOn (EM x dT x'))
                    (propEqOn (EM x dS x'))
                    (symAdjˢ Aₜ) adjH

      adjOut : FiberAdjˢ (propEqOn (EM (Functor.F₀ S x) dS v))
                        (propEqOn (EM (Functor.F₀ S x) dT v))
      adjOut = compAdjˢ (propEqOn (EM (Functor.F₀ S x) dT v))
                        (propEqOn (EM x dS x'))
                        (propEqOn (EM (Functor.F₀ S x) dS v))
                        c1 Aₛ

      -- Forward source-level child bisimulation; built only from h and
      -- edge-reloc, so no go call occurs here. The Aₛ η round-trip
      -- identifies the s-edge reached via adjH with the one reached by
      -- fro Aₛ (to adjOut q).
      --
      -- 正向的源层子互模拟；仅由 h 与 edge-reloc 构造，其中无 go。
      -- Aₛ 的 η 往返把经 adjH 到达的 s 边与 fro Aₛ (to adjOut q) 到达
      -- 的 s 边等同。
      hF : ∀ (q : EM (Functor.F₀ S x) dT v)
         → MO.≈CosmosM C FC propLabel
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
      hT : ∀ (r : EM (Functor.F₀ S x) dS v)
         → MO.≈CosmosM C FC propLabel
             (M.below t x' (FiberAdjˢ.fro Aₜ (FiberAdjˢ.fro adjOut r)))
             (M.below s x' (FiberAdjˢ.fro Aₛ r))
      hT r =
        let eSsrc = FiberAdjˢ.fro Aₛ r
            z     = FiberAdjˢ.fro adjH eSsrc
        in ≈Mˢ-trans ≈A ≈E (edge-reloc t (FiberAdjˢ.η Aₜ z))
               (≈Mˢ-sym ≈A ≈E (hbwd eSsrc))

  ----------------------------------------------------------------------
  -- mapFˢ is mapR along refl, so the desired congruence is go refl.
  --
  -- mapFˢ 即沿 refl 的 mapR，故所求同余为 go refl。

  uni-map-cong : (S : Functor (ShapeCat C FC) (ShapeCat C FC))
                 (u : UniDet S)
               → ∀ {x : MO.I C FC} {t s : MO.CosmosM C FC x}
               → MO.≈CosmosM C FC propLabel t s
               → MO.≈CosmosM C FC propLabel
                   (FMapˢ.mapFˢ (uniFMapˢ S u) x t)
                   (FMapˢ.mapFˢ (uniFMapˢ S u) x s)
  uni-map-cong S u = go S u refl

  ----------------------------------------------------------------------
  -- The categorical endomorphism bundle FMˢ for a uniform deterministic
  -- S
  --
  -- shape-cong is the identity (labels fixed) and map-cong is the
  -- coinductive engine above.
  --
  -- 一致确定性 S 的范畴自态射束 FMˢ
  --
  -- shape-cong 为恒等（标签固定），map-cong 为上述余归纳引擎。

  uniFMˢ : (S : Functor (ShapeCat C FC) (ShapeCat C FC))
           (u : UniDet S) → FMˢ sysP sysP
  uniFMˢ S u = record
    { mor        = uniFMapˢ S u
    ; shape-cong = λ ea → ea
    ; map-cong   = uni-map-cong S u
    }
