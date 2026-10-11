------------------------------------------------------------------------
-- Deterministic carried morphisms over setoid systems
--
-- The setoid generalisation of FMap. A FMapˢ carries an index function
-- u, a shape map, a canonical source child with the graph witness
-- u x' ≡ v, and a whole-fibre carried adjunction FiberAdjˢ at that
-- child; it induces a tree map mapFˢ via Morphˢ along the graph
-- relation (λ x v → u x ≡ v). Compared with FMap, the edge adjunction
-- is a FiberAdjˢ and the propositional childF-coh field is dropped,
-- its coherence being absorbed by FiberAdjˢ's to-cong / fro-cong.
--
-- setoid 系统上的确定性携带态射
--
-- FMap 的 setoid 泛化。FMapˢ 携带索引函数 u、形状映射、连同图见证
-- u x' ≡ v 的规范源子节点，以及该子节点上的整纤维携带伴随
-- FiberAdjˢ；它沿图关系（λ x v → u x ≡ v）经 Morphˢ 诱导出树映射
-- mapFˢ。与 FMap 相比，边伴随为 FiberAdjˢ，命题版的 childF-coh 字段
-- 被去掉，其相干性由 FiberAdjˢ 的 to-cong / fro-cong 吸收。
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module ALMA.Base.MCorrSetoidCat where

open import Agda.Primitive using (Level; _⊔_; lsuc)
open import Agda.Builtin.Sigma using (Σ; _,_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Product.Base using (proj₁)
open import Function.Base using (_∘_)
open import Relation.Binary.PropositionalEquality.Core using (cong; sym; trans)
open import Relation.Binary.Structures using (IsEquivalence)

open import Categories.Category.Core using (Category)

open import ALMA.Base.MCorr using (M)
open import ALMA.Base.MCorrSetoid using
  (SysEq; EqOn; FiberAdjˢ; Morphˢ; idAdjˢ; compAdjˢ; shapeᴿ; child
  ; edge-adj; _≈Mˢ_; here-eq; below-eq; ≈Mˢ-refl; ≈Mˢ-sym; ≈Mˢ-trans)

open SysEq
open FiberAdjˢ
open Morphˢ

------------------------------------------------------------------------
-- Deterministic carried morphism
--
-- 确定性携带态射

record FMapˢ {i j a b c d ℓa ℓe ℓc ℓd : Level}
             (X : SysEq i a b ℓa ℓe)
             (Y : SysEq j c d ℓc ℓd)
       : Set (i ⊔ j ⊔ a ⊔ b ⊔ c ⊔ d ⊔ ℓe ⊔ ℓd) where
  field
    u      : I X → I Y
    shape  : (x : I X) → A X x → A Y (u x)

    -- Canonical source child of target child v, carrying u x' ≡ v.
    --
    -- 目标子节点 v 的规范源子节点，携带 u x' ≡ v。
    childF : (x : I X) (a : A X x) (v : I Y)
           → Σ (I X) λ x' → u x' ≡ v

    adjFˢ  : (x : I X) (a : A X x) (v : I Y)
           → FiberAdjˢ (≈E Y (u x) (shape x a) v)
                       (≈E X x a (proj₁ (childF x a v)))

  -- Pullback: canonical source child, the source edge via fro, and the
  -- graph witness.
  --
  -- 拉回：规范源子节点、经 fro 的源边、图见证。
  pullFˢ : (x : I X) (a : A X x) (v : I Y)
           (q : E Y (u x) (shape x a) v)
         → Σ (I X) λ x' → Σ (E X x a x') λ e → u x' ≡ v
  pullFˢ x a v q =
    let x' , r' = childF x a v
    in x' , fro (adjFˢ x a v) q , r'

  -- Deterministic map as a relation-general Morphˢ along the graph of u.
  --
  -- 确定性映射作为沿 u 之图的关系泛化 Morphˢ。
  asMorphˢ : Morphˢ X Y (λ (x : I X) (v : I Y) → u x ≡ v)
  asMorphˢ .Morphˢ.step {x = x} {y = .(u x)} refl = record
    { shapeᴿ   = shape x
    ; child    = childF x
    ; edge-adj = adjFˢ x
    }

  mapFˢ : (x : I X) → M (A X) (E X) x → M (A Y) (E Y) (u x)
  mapFˢ x t = Morphˢ.mapR asMorphˢ refl t

open FMapˢ public

------------------------------------------------------------------------
-- Identity and composition
--
-- 恒等与复合

idFˢ : ∀ {i a b ℓa ℓe : Level} {X : SysEq i a b ℓa ℓe}
      → FMapˢ X X
idFˢ {X = X} = record
  { u      = λ x → x
  ; shape  = λ _ a → a
  ; childF = λ x _ v → v , refl
  ; adjFˢ  = λ x a v → idAdjˢ (≈E X x a v)
  }

compFˢ : ∀ {i j k a b c d e f ℓa ℓe ℓc ℓd ℓg ℓh : Level}
           {X : SysEq i a b ℓa ℓe}
           {Y : SysEq j c d ℓc ℓd}
           {Z : SysEq k e f ℓg ℓh}
       → FMapˢ Y Z → FMapˢ X Y → FMapˢ X Z
compFˢ {X = X} {Y = Y} {Z = Z} g f = record
  { u      = ug ∘ uf
  ; shape  = λ x a → shapeg (uf x) (shapef x a)
  ; childF = childcomp
  ; adjFˢ  = adjcomp
  }
  where
  uf     = FMapˢ.u f
  ug     = FMapˢ.u g
  shapef = FMapˢ.shape f
  shapeg = FMapˢ.shape g

  childcomp : (x : I X) (a : A X x) (w : I Z)
            → Σ (I X) λ x'' → ug (uf x'') ≡ w
  childcomp x a w =
    let y' , eg  = FMapˢ.childF g (uf x) (shapef x a) w
        x'' , ef = FMapˢ.childF f x a y'
    in x'' , trans (cong ug ef) eg

  adjcomp : (x : I X) (a : A X x) (w : I Z)
          → FiberAdjˢ (≈E Z (ug (uf x))
                            (shapeg (uf x) (shapef x a)) w)
                      (≈E X x a (proj₁ (childcomp x a w)))
  adjcomp x a w =
    let y' , _   = FMapˢ.childF g (uf x) (shapef x a) w
        x'' , _  = FMapˢ.childF f x a y'
    in compAdjˢ (≈E X x a x'')
                (≈E Y (uf x) (shapef x a) y')
                (≈E Z (ug (uf x)) (shapeg (uf x) (shapef x a)) w)
                (FMapˢ.adjFˢ f x a y')
                (FMapˢ.adjFˢ g (uf x) (shapef x a) w)

------------------------------------------------------------------------
-- Subst-free relocation along a propositional index equality
--
-- At refl it is the identity, so every round-trip / congruence lemma
-- collapses to carried bisimulation reflexivity.
--
-- 沿命题索引等式的零 subst 重定位
--
-- 在 refl 处为恒等，故所有往返/同余引理都坍缩为携带式互模拟自反。

private
  relocate : ∀ {i a b : Level} {I : Set i} {A : I → Set a}
               {E : (x : I) (a : A x) (y : I) → Set b} {x y : I}
           → x ≡ y → M A E x → M A E y
  relocate refl t = t

  trans-refl-≡ : ∀ {ℓ} {A : Set ℓ} {x y : A} (p : x ≡ y)
               → trans p refl ≡ p
  trans-refl-≡ refl = refl

  ≈rel-respˢ : ∀ {i a b ℓa ℓe : Level} {I : Set i} {A : I → Set a}
                 {E : (x : I) (a : A x) (y : I) → Set b}
                 (≈A : (x : I) → EqOn {ℓ = ℓa} (A x))
                 (≈E : (x : I) (a : A x) (y : I) → EqOn {ℓ = ℓe} (E x a y))
                 {x y : I} (r : x ≡ y) {t s : M A E x}
             → _≈Mˢ_ ≈A ≈E t s
             → _≈Mˢ_ ≈A ≈E (relocate r t) (relocate r s)
  ≈rel-respˢ ≈A ≈E refl p = p

  ≈rel-roundˢ : ∀ {i a b ℓa ℓe : Level} {I : Set i} {A : I → Set a}
                  {E : (x : I) (a : A x) (y : I) → Set b}
                  (≈A : (x : I) → EqOn {ℓ = ℓa} (A x))
                  (≈E : (x : I) (a : A x) (y : I) → EqOn {ℓ = ℓe} (E x a y))
                  {x y : I} (r : x ≡ y) (t : M A E x)
              → _≈Mˢ_ ≈A ≈E (relocate (sym r) (relocate r t)) t
  ≈rel-roundˢ ≈A ≈E refl t = ≈Mˢ-refl ≈A ≈E t

  ≈rel-compˢ : ∀ {i a b ℓa ℓe : Level} {I : Set i} {A : I → Set a}
                 {E : (x : I) (a : A x) (y : I) → Set b}
                 (≈A : (x : I) → EqOn {ℓ = ℓa} (A x))
                 (≈E : (x : I) (a : A x) (y : I) → EqOn {ℓ = ℓe} (E x a y))
                 {x y z : I} (r : x ≡ y) (s : y ≡ z) (t : M A E x)
             → _≈Mˢ_ ≈A ≈E (relocate (trans r s) t)
                           (relocate s (relocate r t))
  ≈rel-compˢ ≈A ≈E refl refl t = ≈Mˢ-refl ≈A ≈E t

------------------------------------------------------------------------
-- Public re-export: relocating both trees along the same index
-- equality preserves the carried bisimulation.
--
-- 公开重导出：沿同一索引等式 relocate 两棵树保持携带互模拟。
relocate-resp-≈Mˢ : ∀ {i a b ℓa ℓe : Level} {I : Set i} {A : I → Set a}
                 {E : (x : I) (a : A x) (y : I) → Set b}
                 (≈A : (x : I) → EqOn {ℓ = ℓa} (A x))
                 (≈E : (x : I) (a : A x) (y : I) → EqOn {ℓ = ℓe} (E x a y))
                 {x y : I} (r : x ≡ y) {t s : M A E x}
             → _≈Mˢ_ ≈A ≈E t s
             → _≈Mˢ_ ≈A ≈E (relocate r t) (relocate r s)
relocate-resp-≈Mˢ = ≈rel-respˢ

-- Public alias for the index relocation of an M-tree.
--
-- M-树索引重定位的公开别名。
relocateˢ : ∀ {i a b : Level} {I : Set i} {A : I → Set a}
               {E : (x : I) (a : A x) (y : I) → Set b} {x y : I}
           → x ≡ y → M A E x → M A E y
relocateˢ = relocate

------------------------------------------------------------------------
-- Behavioural equivalence of deterministic carried morphisms
--
-- The index functions agree; after matching that refl the two image
-- trees share an index and are related by ≈Mˢ. In every category law
-- the index component is definitionally refl.
--
-- 确定性携带态射的行为等价
--
-- 索引函数一致；匹配该 refl 后两棵像树共享索引，由 ≈Mˢ 相关。所有
-- 范畴律中索引分量定义性地为 refl。

module _ {i j a b c d ℓa ℓe ℓc ℓd : Level}
         {X : SysEq i a b ℓa ℓe} {Y : SysEq j c d ℓc ℓd} where

  _≈Fˢ_ : FMapˢ X Y → FMapˢ X Y
        → Set (i ⊔ j ⊔ a ⊔ b ⊔ c ⊔ d ⊔ ℓc ⊔ ℓd)
  _≈Fˢ_ f g =
    ∀ (x : I X)
    → Σ (FMapˢ.u f x ≡ FMapˢ.u g x)
        (λ r → ∀ (t : M (A X) (E X) x)
             → _≈Mˢ_ (≈A Y) (≈E Y)
                      (relocate r (FMapˢ.mapFˢ f x t))
                      (FMapˢ.mapFˢ g x t))

  ≈Fˢ-refl : (f : FMapˢ X Y) → f ≈Fˢ f
  ≈Fˢ-refl f x =
      refl
    , λ t → ≈Mˢ-refl (≈A Y) (≈E Y) (FMapˢ.mapFˢ f x t)

  ≈Fˢ-sym : {f g : FMapˢ X Y} → f ≈Fˢ g → g ≈Fˢ f
  ≈Fˢ-sym {f = f} {g = g} p x with p x
  ... | r , h =
      sym r
    , λ t → ≈Mˢ-trans (≈A Y) (≈E Y)
              (≈rel-respˢ (≈A Y) (≈E Y) (sym r)
                 (≈Mˢ-sym (≈A Y) (≈E Y) (h t)))
              (≈rel-roundˢ (≈A Y) (≈E Y) r (FMapˢ.mapFˢ f x t))

  ≈Fˢ-trans : {f g h : FMapˢ X Y}
            → f ≈Fˢ g → g ≈Fˢ h → f ≈Fˢ h
  ≈Fˢ-trans {f = f} {g = g} {h = h} p q x with p x | q x
  ... | r1 , h1 | r2 , h2 =
      trans r1 r2
    , λ t → ≈Mˢ-trans (≈A Y) (≈E Y)
              (≈rel-compˢ (≈A Y) (≈E Y) r1 r2 (FMapˢ.mapFˢ f x t))
              (≈Mˢ-trans (≈A Y) (≈E Y)
                 (≈rel-respˢ (≈A Y) (≈E Y) r2 (h1 t))
                 (h2 t))

  ≈Fˢ-isEquivalence : IsEquivalence _≈Fˢ_
  ≈Fˢ-isEquivalence = record
    { refl  = λ {f} → ≈Fˢ-refl f
    ; sym   = λ {f g} → ≈Fˢ-sym {f = f} {g = g}
    ; trans = λ {f g h} → ≈Fˢ-trans {f = f} {g = g} {h = h}
    }

------------------------------------------------------------------------
-- Coinductive fusion
--
-- compFˢ uses the same canonical child decomposition as the nested
-- mapR, so each output child is one guarded recursive call and the
-- carried fibre adjunction is the identity.
--
-- 余归纳融合
--
-- compFˢ 采用与嵌套 mapR 相同的规范子节点分解，故每个输出子节点恰为
-- 一次受保护递归调用，携带的纤维伴随为恒等。

module Fusionˢ {i j k a b c d e f ℓa ℓe ℓc ℓd ℓg ℓh : Level}
              {X : SysEq i a b ℓa ℓe}
              {Y : SysEq j c d ℓc ℓd}
              {Z : SysEq k e f ℓg ℓh}
              (gm : FMapˢ Y Z) (fm : FMapˢ X Y) where

  uf     = FMapˢ.u fm
  ug     = FMapˢ.u gm
  shapef = FMapˢ.shape fm
  shapeg = FMapˢ.shape gm
  asF    = FMapˢ.asMorphˢ fm
  asG    = FMapˢ.asMorphˢ gm
  asC    = FMapˢ.asMorphˢ (compFˢ gm fm)

  mutual
    fusionˢ : ∀ {x : I X} {y : I Y} {z : I Z}
                (rf : uf x ≡ y) (rg : ug y ≡ z)
                (t : M (A X) (E X) x)
            → _≈Mˢ_ (≈A Z) (≈E Z)
                     (Morphˢ.mapR asC (trans (cong ug rf) rg) t)
                     (Morphˢ.mapR asG rg (Morphˢ.mapR asF rf t))
    fusionˢ {x = x} {y = .(uf x)} {z = .(ug (uf x))} refl refl t
      .here-eq = EqOn.refl (≈A Z (ug (uf x)))
    fusionˢ {x = x} {y = .(uf x)} {z = .(ug (uf x))} refl refl t
      .below-eq w =
        idAdjˢ (≈E Z (ug (uf x))
                     (shapeg (uf x) (shapef x (M.here t))) w)
      , ( (λ q → let y' , eY , eg =
                        FMapˢ.pullFˢ gm (uf x) (shapef x (M.here t)) w q
                     x'' , eX , ef =
                        FMapˢ.pullFˢ fm x (M.here t) y' eY
                 in fusionˢ ef eg (M.below t x'' eX))
        , (λ q → let y' , eY , eg =
                        FMapˢ.pullFˢ gm (uf x) (shapef x (M.here t)) w q
                     x'' , eX , ef =
                        FMapˢ.pullFˢ fm x (M.here t) y' eY
                 in fusion˘ˢ ef eg (M.below t x'' eX)) )

    fusion˘ˢ : ∀ {x : I X} {y : I Y} {z : I Z}
                 (rf : uf x ≡ y) (rg : ug y ≡ z)
                 (t : M (A X) (E X) x)
             → _≈Mˢ_ (≈A Z) (≈E Z)
                      (Morphˢ.mapR asG rg (Morphˢ.mapR asF rf t))
                      (Morphˢ.mapR asC (trans (cong ug rf) rg) t)
    fusion˘ˢ {x = x} {y = .(uf x)} {z = .(ug (uf x))} refl refl t
      .here-eq = EqOn.refl (≈A Z (ug (uf x)))
    fusion˘ˢ {x = x} {y = .(uf x)} {z = .(ug (uf x))} refl refl t
      .below-eq w =
        idAdjˢ (≈E Z (ug (uf x))
                     (shapeg (uf x) (shapef x (M.here t))) w)
      , ( (λ q → let y' , eY , eg =
                        FMapˢ.pullFˢ gm (uf x) (shapef x (M.here t)) w q
                     x'' , eX , ef =
                        FMapˢ.pullFˢ fm x (M.here t) y' eY
                 in fusion˘ˢ ef eg (M.below t x'' eX))
        , (λ q → let y' , eY , eg =
                        FMapˢ.pullFˢ gm (uf x) (shapef x (M.here t)) w q
                     x'' , eX , ef =
                        FMapˢ.pullFˢ fm x (M.here t) y' eY
                 in fusionˢ ef eg (M.below t x'' eX)) )

mapFˢ-comp : ∀ {i j k a b c d e f ℓa ℓe ℓc ℓd ℓg ℓh : Level}
               {X : SysEq i a b ℓa ℓe}
               {Y : SysEq j c d ℓc ℓd}
               {Z : SysEq k e f ℓg ℓh}
               (gm : FMapˢ Y Z) (fm : FMapˢ X Y)
               (x : I X) (t : M (A X) (E X) x)
           → _≈Mˢ_ (≈A Z) (≈E Z)
                    (FMapˢ.mapFˢ (compFˢ gm fm) x t)
                    (FMapˢ.mapFˢ gm (FMapˢ.u fm x) (FMapˢ.mapFˢ fm x t))
mapFˢ-comp gm fm x t = Fusionˢ.fusionˢ gm fm refl refl t

mapFˢ-comp˘ : ∀ {i j k a b c d e f ℓa ℓe ℓc ℓd ℓg ℓh : Level}
                {X : SysEq i a b ℓa ℓe}
                {Y : SysEq j c d ℓc ℓd}
                {Z : SysEq k e f ℓg ℓh}
                (gm : FMapˢ Y Z) (fm : FMapˢ X Y)
                (x : I X) (t : M (A X) (E X) x)
            → _≈Mˢ_ (≈A Z) (≈E Z)
                     (FMapˢ.mapFˢ gm (FMapˢ.u fm x) (FMapˢ.mapFˢ fm x t))
                     (FMapˢ.mapFˢ (compFˢ gm fm) x t)
mapFˢ-comp˘ gm fm x t = Fusionˢ.fusion˘ˢ gm fm refl refl t

------------------------------------------------------------------------
-- The identity tree map is the identity up to carried bisimulation
--
-- 恒等树映射在携带式互模拟意义下为恒等。

module _ {i a b ℓa ℓe : Level} {X : SysEq i a b ℓa ℓe} where

  mutual
    mapFˢ-id : (x : I X) (t : M (A X) (E X) x)
             → _≈Mˢ_ (≈A X) (≈E X)
                      (FMapˢ.mapFˢ (idFˢ {X = X}) x t) t
    mapFˢ-id x t .here-eq = EqOn.refl (≈A X x)
    mapFˢ-id x t .below-eq w =
        idAdjˢ (≈E X x (M.here t) w)
      , ( (λ q → mapFˢ-id w (M.below t w q))
        , (λ q → mapFˢ-id˘ w (M.below t w q)) )

    mapFˢ-id˘ : (x : I X) (t : M (A X) (E X) x)
              → _≈Mˢ_ (≈A X) (≈E X)
                       t (FMapˢ.mapFˢ (idFˢ {X = X}) x t)
    mapFˢ-id˘ x t .here-eq = EqOn.refl (≈A X x)
    mapFˢ-id˘ x t .below-eq w =
        idAdjˢ (≈E X x (M.here t) w)
      , ( (λ q → mapFˢ-id˘ w (M.below t w q))
        , (λ q → mapFˢ-id w (M.below t w q)) )

------------------------------------------------------------------------
-- Index-only reflow machine for FMapˢ
--
-- These change only the INDEX witness of mapR; labels are untouched, so
-- here-eq is EqOn.refl and below-eq uses idAdjˢ. No label equation and
-- no childF coherence is involved.
--
-- FMapˢ 的纯索引重排机器
--
-- 它们只改变 mapR 的索引见证；标签不变，故 here-eq 为 EqOn.refl，
-- below-eq 用 idAdjˢ。不涉及标签等式与 childF 相干。

module CongIdxˢ {i j a b c d ℓa ℓe ℓc ℓd : Level}
               {X : SysEq i a b ℓa ℓe}
               {Y : SysEq j c d ℓc ℓd}
               (f : FMapˢ X Y) where

  private
    asF  = FMapˢ.asMorphˢ f
    uf   = FMapˢ.u f
    mapf = FMapˢ.mapFˢ f

  mutual
    mapR-rel : ∀ {x : I X} {v : I Y} (r : uf x ≡ v)
                 (t : M (A X) (E X) x)
             → _≈Mˢ_ (≈A Y) (≈E Y)
                      (Morphˢ.mapR asF r t)
                      (relocate r (mapf x t))
    mapR-rel {x = x} refl t =
      ≈Mˢ-refl (≈A Y) (≈E Y) (mapf x t)

    mapR-rel˘ : ∀ {x : I X} {v : I Y} (r : uf x ≡ v)
                  (t : M (A X) (E X) x)
              → _≈Mˢ_ (≈A Y) (≈E Y)
                      (relocate r (mapf x t))
                      (Morphˢ.mapR asF r t)
    mapR-rel˘ {x = x} refl t =
      ≈Mˢ-refl (≈A Y) (≈E Y) (mapf x t)

    mapR-r-eq : ∀ {x : I X} {v : I Y} {r r' : uf x ≡ v}
                  (eq : r ≡ r') (t : M (A X) (E X) x)
              → _≈Mˢ_ (≈A Y) (≈E Y)
                      (Morphˢ.mapR asF r t)
                      (Morphˢ.mapR asF r' t)
    mapR-r-eq {x = x} {r = z} {r' = .z} refl t =
      ≈Mˢ-refl (≈A Y) (≈E Y) (Morphˢ.mapR asF z t)

    mapR-cross : ∀ {x₁ x₀ : I X} {v : I Y}
                   (d : x₁ ≡ x₀) (r₀ : uf x₀ ≡ v)
                   (s₁ : M (A X) (E X) x₁)
               → _≈Mˢ_ (≈A Y) (≈E Y)
                      (Morphˢ.mapR asF r₀ (relocate d s₁))
                      (Morphˢ.mapR asF (trans (cong uf d) r₀) s₁)
    mapR-cross {x₁ = z} {x₀ = .z} refl refl s₁ .here-eq =
      EqOn.refl (≈A Y (uf z))
    mapR-cross {x₁ = z} {x₀ = .z} refl refl s₁ .below-eq w =
        idAdjˢ (≈E Y (uf z) (FMapˢ.shape f z (M.here s₁)) w)
      , ( (λ q → let x' , e , r' = FMapˢ.pullFˢ f z (M.here s₁) w q
                 in mapR-cross refl r' (M.below s₁ x' e))
        , (λ q → let x' , e , r' = FMapˢ.pullFˢ f z (M.here s₁) w q
                 in mapR-cross˘ refl r' (M.below s₁ x' e)) )

    mapR-cross˘ : ∀ {x₁ x₀ : I X} {v : I Y}
                    (d : x₁ ≡ x₀) (r₀ : uf x₀ ≡ v)
                    (s₁ : M (A X) (E X) x₁)
                → _≈Mˢ_ (≈A Y) (≈E Y)
                      (Morphˢ.mapR asF (trans (cong uf d) r₀) s₁)
                      (Morphˢ.mapR asF r₀ (relocate d s₁))
    mapR-cross˘ {x₁ = z} {x₀ = .z} refl refl s₁ .here-eq =
      EqOn.refl (≈A Y (uf z))
    mapR-cross˘ {x₁ = z} {x₀ = .z} refl refl s₁ .below-eq w =
        idAdjˢ (≈E Y (uf z) (FMapˢ.shape f z (M.here s₁)) w)
      , ( (λ q → let x' , e , r' = FMapˢ.pullFˢ f z (M.here s₁) w q
                 in mapR-cross˘ refl r' (M.below s₁ x' e))
        , (λ q → let x' , e , r' = FMapˢ.pullFˢ f z (M.here s₁) w q
                 in mapR-cross refl r' (M.below s₁ x' e)) )

------------------------------------------------------------------------
-- Deterministic carried setoid functor
--
-- Beyond the operational FMapˢ, a setoid morphism preserves the carried
-- label equivalence and acts on bisimilar trees; both congruences are
-- carried as data.
--
-- 确定性携带 setoid 函子
--
-- 除操作性的 FMapˢ 外，setoid 态射还保持所携带的标签等价并作用于互
-- 模拟树；两个同余均作为数据携带。

record FMˢ {i j a b c d ℓa ℓe ℓc ℓd : Level}
           (X : SysEq i a b ℓa ℓe)
           (Y : SysEq j c d ℓc ℓd)
       : Set (i ⊔ j ⊔ a ⊔ b ⊔ c ⊔ d ⊔ ℓa ⊔ ℓe ⊔ ℓc ⊔ ℓd) where
  field
    mor        : FMapˢ X Y

    -- The shape action preserves the carried label equivalence.
    --
    -- shape 作用保持所携带的标签等价。
    shape-cong : ∀ {x : I X} {a₁ a₂ : A X x}
               → EqOn._≈_ (≈A X x) a₁ a₂
               → EqOn._≈_ (≈A Y (FMapˢ.u mor x))
                           (FMapˢ.shape mor x a₁)
                           (FMapˢ.shape mor x a₂)

    map-cong   : ∀ {x : I X} {t s : M (A X) (E X) x}
               → _≈Mˢ_ (≈A X) (≈E X) t s
               → _≈Mˢ_ (≈A Y) (≈E Y)
                        (FMapˢ.mapFˢ mor x t)
                        (FMapˢ.mapFˢ mor x s)
open FMˢ public

------------------------------------------------------------------------
-- Identity and composition of setoid functors
--
-- setoid 函子的恒等与复合

idFMˢ : ∀ {i a b ℓa ℓe : Level} {X : SysEq i a b ℓa ℓe} → FMˢ X X
idFMˢ {X = X} = record
  { mor        = idFˢ {X = X}
  ; shape-cong = λ ea → ea
  ; map-cong   = λ {x} {t} {s} h →
      ≈Mˢ-trans (≈A X) (≈E X)
        (mapFˢ-id x t)
        (≈Mˢ-trans (≈A X) (≈E X) h (mapFˢ-id˘ x s))
  }

compFMˢ : ∀ {i j k a b c d e f ℓa ℓe ℓc ℓd ℓg ℓh : Level}
            {X : SysEq i a b ℓa ℓe}
            {Y : SysEq j c d ℓc ℓd}
            {Z : SysEq k e f ℓg ℓh}
        → FMˢ Y Z → FMˢ X Y → FMˢ X Z
compFMˢ {X = X} {Y = Y} {Z = Z} gm fm = record
  { mor        = compFˢ gm0 fm0
  ; shape-cong = λ ea → FMˢ.shape-cong gm (FMˢ.shape-cong fm ea)
  ; map-cong   = λ {x} {t} {s} h →
      ≈Mˢ-trans (≈A Z) (≈E Z)
        (mapFˢ-comp gm0 fm0 x t)
        (≈Mˢ-trans (≈A Z) (≈E Z)
           (FMˢ.map-cong gm (FMˢ.map-cong fm h))
           (mapFˢ-comp˘ gm0 fm0 x s))
  }
  where
  gm0 = FMˢ.mor gm
  fm0 = FMˢ.mor fm

------------------------------------------------------------------------
-- Hom equivalence
--
-- Behavioural equality of the underlying carried morphisms.
--
-- hom 等价
--
-- 底层携带态射的行为相等。

module _ {i a b ℓa ℓe : Level}
         {X Y : SysEq i a b ℓa ℓe} where

  _≈FM_ : FMˢ X Y → FMˢ X Y → Set (i ⊔ a ⊔ b ⊔ ℓa ⊔ ℓe)
  f ≈FM g = FMˢ.mor f ≈Fˢ FMˢ.mor g

  ≈FM-refl : (f : FMˢ X Y) → f ≈FM f
  ≈FM-refl f = ≈Fˢ-refl (FMˢ.mor f)

  ≈FM-sym : {f g : FMˢ X Y} → f ≈FM g → g ≈FM f
  ≈FM-sym p = ≈Fˢ-sym p

  ≈FM-trans : {f g h : FMˢ X Y} → f ≈FM g → g ≈FM h → f ≈FM h
  ≈FM-trans p q = ≈Fˢ-trans p q

  ≈FM-isEquivalence : IsEquivalence _≈FM_
  ≈FM-isEquivalence = record
    { refl  = λ {f} → ≈FM-refl f
    ; sym   = λ {f g} → ≈FM-sym {f = f} {g = g}
    ; trans = λ {f g h} → ≈FM-trans {f = f} {g = g} {h = h}
    }

------------------------------------------------------------------------
-- Composition respects behavioural equality
--
-- 复合尊重行为相等。

module _ {i a b ℓa ℓe : Level}
         {X Y Z : SysEq i a b ℓa ℓe} where

  ∘-resp-≈FM : {F₁ F₂ : FMˢ X Y} {G₁ G₂ : FMˢ Y Z}
             → F₁ ≈FM F₂ → G₁ ≈FM G₂
             → compFMˢ G₁ F₁ ≈FM compFMˢ G₂ F₂
  ∘-resp-≈FM {F₁ = F₁} {F₂ = F₂} {G₁ = G₁} {G₂ = G₂} eqF eqG x
    with eqF x | eqG (FMapˢ.u (FMˢ.mor F₂) x)
  ... | rF , hF | rG , hG =
      trans (cong (FMapˢ.u (FMˢ.mor G₁)) rF) rG
    , λ t →
        let s1 = FMapˢ.mapFˢ (FMˢ.mor F₁) x t
            s2 = FMapˢ.mapFˢ (FMˢ.mor F₂) x t
            a1 = FMapˢ.mapFˢ (FMˢ.mor G₁) (FMapˢ.u (FMˢ.mor F₁) x) s1
            cg = cong (FMapˢ.u (FMˢ.mor G₁)) rF
            b1 = FMapˢ.mapFˢ (FMˢ.mor G₁) (FMapˢ.u (FMˢ.mor F₂) x)
                             (relocate rF s1)
            r  = trans cg rG
        in
        ≈Mˢ-trans (≈A Z) (≈E Z)
          (≈rel-respˢ (≈A Z) (≈E Z) r
             {t = FMapˢ.mapFˢ (compFˢ (FMˢ.mor G₁) (FMˢ.mor F₁)) x t}
             {s = a1}
             (mapFˢ-comp (FMˢ.mor G₁) (FMˢ.mor F₁) x t))
          (≈Mˢ-trans (≈A Z) (≈E Z)
            (≈rel-compˢ (≈A Z) (≈E Z) cg rG a1)
            (≈Mˢ-trans (≈A Z) (≈E Z)
              (≈rel-respˢ (≈A Z) (≈E Z) rG
                 {t = relocate cg a1} {s = b1}
                 (≈Mˢ-trans (≈A Z) (≈E Z)
                    (CongIdxˢ.mapR-rel˘ (FMˢ.mor G₁) cg s1)
                    (≈Mˢ-trans (≈A Z) (≈E Z)
                       (CongIdxˢ.mapR-r-eq (FMˢ.mor G₁)
                          (sym (trans-refl-≡ cg)) s1)
                       (CongIdxˢ.mapR-cross˘ (FMˢ.mor G₁) rF refl s1))))
              (≈Mˢ-trans (≈A Z) (≈E Z)
                (≈rel-respˢ (≈A Z) (≈E Z) rG
                   {t = b1}
                   {s = FMapˢ.mapFˢ (FMˢ.mor G₁) (FMapˢ.u (FMˢ.mor F₂) x) s2}
                   (FMˢ.map-cong G₁ (hF t)))
                (≈Mˢ-trans (≈A Z) (≈E Z)
                   (hG s2)
                   (≈Mˢ-sym (≈A Z) (≈E Z)
                      (mapFˢ-comp (FMˢ.mor G₂) (FMˢ.mor F₂) x t))))))

------------------------------------------------------------------------
-- Category laws
--
-- All at behavioural equality; the index components are definitionally
-- refl, so no index transport is used.
--
-- 范畴律
--
-- 全部建立在行为相等上；索引分量定义性地为 refl，故不使用索引传输。

module _ {i a b ℓa ℓe : Level}
         {W X Y Z : SysEq i a b ℓa ℓe}
         {f : FMˢ W X} {g : FMˢ X Y} {h : FMˢ Y Z} where

  private
    f0 = FMˢ.mor f
    g0 = FMˢ.mor g
    h0 = FMˢ.mor h

  assocFM : compFMˢ (compFMˢ h g) f ≈FM compFMˢ h (compFMˢ g f)
  assocFM x = refl , λ t →
    let lhs→c =
          ≈Mˢ-trans (≈A Z) (≈E Z)
            (mapFˢ-comp (compFˢ h0 g0) f0 x t)
            (mapFˢ-comp h0 g0 (FMapˢ.u f0 x)
                            (FMapˢ.mapFˢ f0 x t))
        rhs→c =
          ≈Mˢ-trans (≈A Z) (≈E Z)
            (mapFˢ-comp h0 (compFˢ g0 f0) x t)
            (FMˢ.map-cong h (mapFˢ-comp g0 f0 x t))
    in ≈Mˢ-trans (≈A Z) (≈E Z) lhs→c
                   (≈Mˢ-sym (≈A Z) (≈E Z) rhs→c)

  sym-assocFM : compFMˢ h (compFMˢ g f) ≈FM compFMˢ (compFMˢ h g) f
  sym-assocFM =
    ≈FM-sym {i = i} {a = a} {b = b} {ℓa = ℓa} {ℓe = ℓe}
            {X = W} {Y = Z}
            {f = compFMˢ (compFMˢ h g) f}
            {g = compFMˢ h (compFMˢ g f)}
            assocFM

module _ {i a b ℓa ℓe : Level}
         {X Y : SysEq i a b ℓa ℓe}
         {f : FMˢ X Y} where

  private
    f0 = FMˢ.mor f

  identityˡFM : compFMˢ idFMˢ f ≈FM f
  identityˡFM x = refl , λ t →
    ≈Mˢ-trans (≈A Y) (≈E Y)
      (mapFˢ-comp idFˢ f0 x t)
      (mapFˢ-id (FMapˢ.u f0 x) (FMapˢ.mapFˢ f0 x t))

  identityʳFM : compFMˢ f idFMˢ ≈FM f
  identityʳFM x = refl , λ t →
    ≈Mˢ-trans (≈A Y) (≈E Y)
      (mapFˢ-comp f0 idFˢ x t)
      (FMˢ.map-cong f (mapFˢ-id x t))

module _ {i a b ℓa ℓe : Level}
         {X : SysEq i a b ℓa ℓe} where

  identity²FM : compFMˢ idFMˢ idFMˢ ≈FM (idFMˢ {X = X})
  identity²FM x = refl , λ t →
    ≈Mˢ-trans (≈A X) (≈E X)
      (mapFˢ-comp idFˢ idFˢ x t)
      (mapFˢ-id x (FMapˢ.mapFˢ idFˢ x t))

------------------------------------------------------------------------
-- The category of setoid systems and deterministic carried setoid
-- functors
--
-- setoid 系统与确定性携带 setoid 函子的范畴

MCorrCatˢ : (i a b ℓa ℓe : Level)
          → Category (lsuc (i ⊔ a ⊔ b ⊔ ℓa ⊔ ℓe))
                     (i ⊔ a ⊔ b ⊔ ℓa ⊔ ℓe)
                     (i ⊔ a ⊔ b ⊔ ℓa ⊔ ℓe)
MCorrCatˢ i a b ℓa ℓe = record
  { Obj       = SysEq i a b ℓa ℓe
  ; _⇒_       = λ X Y → FMˢ X Y
  ; _≈_       = λ {X} {Y} f g → _≈FM_ {X = X} {Y = Y} f g
  ; id        = λ {X} → idFMˢ {X = X}
  ; _∘_       = λ {X} {Y} {Z} g f → compFMˢ g f
  ; equiv     = λ {X} {Y} → ≈FM-isEquivalence {X = X} {Y = Y}
  ; ∘-resp-≈  = λ {X} {Y} {Z} {f} {h} {g} {k} fh gk →
                  ∘-resp-≈FM {X = X} {Y = Y} {Z = Z}
                              {F₁ = g} {F₂ = k} {G₁ = f} {G₂ = h} gk fh
  ; assoc     = λ {W} {X} {Y} {Z} {f} {g} {h} →
                  assocFM {W = W} {X = X} {Y = Y} {Z = Z}
                          {f = f} {g = g} {h = h}
  ; sym-assoc = λ {W} {X} {Y} {Z} {f} {g} {h} →
                  sym-assocFM {W = W} {X = X} {Y = Y} {Z = Z}
                              {f = f} {g = g} {h = h}
  ; identityˡ = λ {X} {Y} {f} → identityˡFM {X = X} {Y = Y} {f = f}
  ; identityʳ = λ {X} {Y} {f} → identityʳFM {X = X} {Y = Y} {f = f}
  ; identity² = λ {X} → identity²FM {X = X}
  }
