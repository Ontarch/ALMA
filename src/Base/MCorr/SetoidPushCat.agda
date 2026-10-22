------------------------------------------------------------------------
-- Category of setoid systems under forward simulations
--
-- 前向模拟下 setoid 系统的范畴
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module Base.MCorr.SetoidPushCat where

open import Agda.Primitive using (Level; _⊔_; lsuc; lzero)
open import Agda.Builtin.Sigma using (Σ; _,_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Unit.Polymorphic.Base using (⊤; tt)
open import Function.Base using (_∘_)
open import Relation.Binary.PropositionalEquality.Core using (cong; sym; trans)
open import Relation.Binary.Structures using (IsEquivalence)

open import Categories.Category.Core using (Category)

open import Base.MCorr using (M; _⍮_; relocate)
open import Base.MCorr.Setoid using (SysEq; _≈Mˢ_; ≈Mˢ-refl; ≈Mˢ-sym; ≈Mˢ-trans)
open SysEq
open import Base.MCorr.SetoidPush using (PushSimˢ)
open import Base.MCorr.SetoidPushComp using (H∘G; push-comp)
open import Base.MCorr.SetoidPushMap using (push-map)
open import Base.MCorr.SetoidCat using
  (relocate-resp-≈Mˢ; relocate-roundˢ; relocate-compˢ)

------------------------------------------------------------------------
-- Fixed layer for an index function
--
-- The propositional graph of u, and the trivial label correspondence
-- (labels are tracked by the image tree and compared by ≈Mˢ, not by an
-- equation in the simulation witness).
--
-- 索引函数的固定层
--
-- u 的命题图，以及平凡标签对应（标签由像树承载并由 ≈Mˢ 比较，
-- 而非由模拟见证中的等式承载）。

Graph : ∀ {i : Level} {I J : Set i} (u : I → J) → I → J → Set i
Graph u x v = u x ≡ v

-- Trivial label correspondence over any index layer R.
--
-- 任意索引层 R 上的平凡标签对应。
TopH : ∀ {i a b ℓa ℓe : Level}
         {X : SysEq i a b ℓa ℓe} {Y : SysEq i a b ℓa ℓe}
         {R : I X → I Y → Set i}
       → (x : I X) (v : I Y) (r : R x v)
       → (a₁ : A X x) (a₂ : A Y v) → Set lzero
TopH _ _ _ _ _ = ⊤

------------------------------------------------------------------------
-- Identity forward simulation over the trivial label correspondence
--
-- 平凡标签对应下的恒等前向模拟

push-reflᵗ : ∀ {i a b ℓa ℓe : Level} {X : SysEq i a b ℓa ℓe}
            {x : I X} (t : M (A X) (E X) x)
          → PushSimˢ X X (Graph {I = I X} {J = I X} (λ z → z))
                (TopH {X = X} {Y = X}
                      {R = Graph {I = I X} {J = I X} (λ z → z)})
                refl t t
push-reflᵗ {X = X} t .PushSimˢ.here-eq = tt
push-reflᵗ {X = X} t .PushSimˢ.push y e =
  y , e , refl , push-reflᵗ (M.below t y e)

------------------------------------------------------------------------
-- Composition of forward simulations along graph layers
--
-- Rescope the Sigma middle (v , r , s) to the composite graph by the
-- pure map (trans (cong ug) r) s and collapse the middle-label Sigma
-- to tt.
--
-- 沿图层复合两个前向模拟
--
-- 用纯映射 (trans (cong ug) r) s 把含中间项的 Σ 见证 (v , r , s)
-- 重定域到复合图，并把中间标签 Σ 坍缩为 tt。

pushF-comp :
  ∀ {i a b ℓa ℓe : Level}
    {X Y Z : SysEq i a b ℓa ℓe}
    {uf : I X → I Y} {ug : I Y → I Z}
    {x : I X} {t : M (A X) (E X) x}
    {u' : M (A Y) (E Y) (uf x)}
    {w' : M (A Z) (E Z) (ug (uf x))}
  → PushSimˢ X Y (Graph uf)
      (TopH {X = X} {Y = Y} {R = Graph uf}) refl t u'
  → PushSimˢ Y Z (Graph ug)
      (TopH {X = Y} {Y = Z} {R = Graph ug}) refl u' w'
  → PushSimˢ X Z (Graph (ug ∘ uf))
      (TopH {X = X} {Y = Z} {R = Graph (ug ∘ uf)}) refl t w'
pushF-comp {X = X} {Y = Y} {Z = Z} {uf = uf} {ug = ug} pf qg =
  push-map {X = X} {Y = Z}
    (Graph uf ⍮ Graph ug)
    (Graph (ug ∘ uf))
    (H∘G {X = X} {Y = Y} {Z = Z} (Graph uf) (Graph ug)
            (TopH {X = X} {Y = Y} {R = Graph uf})
            (TopH {X = Y} {Y = Z} {R = Graph ug}))
    (TopH {X = X} {Y = Z} {R = Graph (ug ∘ uf)})
    (λ { (v , rf , rg) → trans (cong ug rf) rg })
    (λ _ (b , _ , _) → tt)
    (push-comp {X = X} {Y = Y} {Z = Z} (Graph uf) (Graph ug)
                (TopH {X = X} {Y = Y} {R = Graph uf})
                (TopH {X = Y} {Y = Z} {R = Graph ug}) pf qg)

------------------------------------------------------------------------
-- Forward embedding morphism
--
-- This is the push dual of MCorrSetoidCat. A pull functor FMapˢ gives,
-- for every target child, a canonical source child; a forward embedding
-- instead points from a finite stage into a richer target and carries no
-- totality over target children. A PushMˢ packs an index function u,
-- an image tree mapP x t, a forward-simulation certificate leg, and a
-- bisimulation congruence mapP-cong. Hom equality forgets the
-- certificates and compares index maps pointwise and image trees by
-- ≈Mˢ.
--
-- 前向嵌入态射
--
-- 这是 MCorrSetoidCat 的 push 对偶。pull 函子对每个目标子节点给出
-- 规范源子节点；前向嵌入则从有限阶段指向更丰富的目标，不对目标子节点
-- 求全。PushMˢ 打包索引函数 u、像树 mapP x t、前向模拟证书 leg 与
-- 互模拟同余 mapP-cong。hom 相等忽略证书，逐点比较索引函数、以 ≈Mˢ
-- 比较像树。

record PushMˢ {i a b ℓa ℓe : Level}
             (X Y : SysEq i a b ℓa ℓe)
       : Set (i ⊔ a ⊔ b ⊔ ℓa ⊔ ℓe) where
  field
    u        : I X → I Y
    mapP     : (x : I X) (t : M (A X) (E X) x) → M (A Y) (E Y) (u x)
    mapP-cong : ∀ {x : I X} {t s : M (A X) (E X) x}
              → _≈Mˢ_ (≈A X) (≈E X) t s
              → _≈Mˢ_ (≈A Y) (≈E Y) (mapP x t) (mapP x s)
    leg      : (x : I X) (t : M (A X) (E X) x)
             → PushSimˢ X Y (Graph u)
                 (TopH {X = X} {Y = Y} {R = Graph u})
                 refl t (mapP x t)

open PushMˢ public

------------------------------------------------------------------------
-- Identity and composition
--
-- 恒等与复合

idPMˢ : ∀ {i a b ℓa ℓe : Level} {X : SysEq i a b ℓa ℓe} → PushMˢ X X
idPMˢ {X = X} = record
  { u         = λ z → z
  ; mapP      = λ _ t → t
  ; mapP-cong = λ h → h
  ; leg       = λ _ t → push-reflᵗ {X = X} t
  }

compPMˢ : ∀ {i a b ℓa ℓe : Level} {X Y Z : SysEq i a b ℓa ℓe}
        → PushMˢ Y Z → PushMˢ X Y → PushMˢ X Z
compPMˢ {X = X} {Y = Y} {Z = Z} g f = record
  { u         = ug ∘ uf
  ; mapP      = λ x t → mapP g (uf x) (mapP f x t)
  ; mapP-cong = λ h → mapP-cong g (mapP-cong f h)
  ; leg       = λ x t →
                  pushF-comp {X = X} {Y = Y} {Z = Z}
                             {uf = uf} {ug = ug}
                             (leg f x t)
                             (leg g (uf x) (mapP f x t))
  }
  where
  uf = u f
  ug = u g

-- Relocation commutes with the image map past an index equality;
-- matching the equality argument as refl is not an appeal to K.
--
-- 重定位越过索引等式与像映射交换；将等式参数匹配为 refl 并非诉诸 K。
mapP-cross : ∀ {i a b ℓa ℓe : Level}
                {X Y : SysEq i a b ℓa ℓe} {f : PushMˢ X Y}
                {x y : I X} (r : x ≡ y) (t : M (A X) (E X) x)
            → _≈Mˢ_ (≈A Y) (≈E Y)
                    (relocate (cong (u f) r) (mapP f x t))
                    (mapP f y (relocate r t))
mapP-cross {Y = Y} {f = f} refl t =
  ≈Mˢ-refl (≈A Y) (≈E Y) (mapP f _ t)

------------------------------------------------------------------------
-- Behavioural equality
--
-- Index maps agree and image trees are bisimilar.
--
-- 行为相等
--
-- 索引函数一致，像树互模拟。

module _ {i a b ℓa ℓe : Level} {X Y : SysEq i a b ℓa ℓe} where

  _≈PM_ : PushMˢ X Y → PushMˢ X Y → Set (i ⊔ a ⊔ b ⊔ ℓa ⊔ ℓe)
  _≈PM_ f g =
    ∀ (x : I X)
    → Σ (u f x ≡ u g x) λ r
    → ∀ (t : M (A X) (E X) x)
      → _≈Mˢ_ (≈A Y) (≈E Y)
               (relocate r (mapP f x t)) (mapP g x t)

  ≈PM-refl : (f : PushMˢ X Y) → f ≈PM f
  ≈PM-refl f x = refl , λ t → ≈Mˢ-refl (≈A Y) (≈E Y) (mapP f x t)

  ≈PM-sym : {f g : PushMˢ X Y} → f ≈PM g → g ≈PM f
  ≈PM-sym {f = f} {g = g} p x with p x
  ... | r , h = sym r , λ t →
      ≈Mˢ-trans (≈A Y) (≈E Y)
        (relocate-resp-≈Mˢ (≈A Y) (≈E Y) (sym r)
           (≈Mˢ-sym (≈A Y) (≈E Y) (h t)))
        (relocate-roundˢ (≈A Y) (≈E Y) r (mapP f x t))

  ≈PM-trans : {f g h : PushMˢ X Y} → f ≈PM g → g ≈PM h → f ≈PM h
  ≈PM-trans {f = f} {g = g} {h = h} p q x with p x | q x
  ... | r₁ , h₁ | r₂ , h₂ = trans r₁ r₂ , λ t →
      ≈Mˢ-trans (≈A Y) (≈E Y)
        (relocate-compˢ (≈A Y) (≈E Y) r₁ r₂ (mapP f x t))
        (≈Mˢ-trans (≈A Y) (≈E Y)
           (relocate-resp-≈Mˢ (≈A Y) (≈E Y) r₂ (h₁ t))
           (h₂ t))

  ≈PM-isEquivalence : IsEquivalence _≈PM_
  ≈PM-isEquivalence = record
    { refl  = λ {f} → ≈PM-refl f
    ; sym   = λ {f g} → ≈PM-sym {f = f} {g = g}
    ; trans = λ {f g h} → ≈PM-trans {f = f} {g = g} {h = h}
    }

------------------------------------------------------------------------
-- Composition respects behavioural equality
--
-- 复合尊重行为相等

module _ {i a b ℓa ℓe : Level} {X Y Z : SysEq i a b ℓa ℓe} where

  ∘-resp-≈PM : {F₁ F₂ : PushMˢ X Y} {G₁ G₂ : PushMˢ Y Z}
             → F₁ ≈PM F₂ → G₁ ≈PM G₂
             → compPMˢ G₁ F₁ ≈PM compPMˢ G₂ F₂
  ∘-resp-≈PM {F₁ = F₁} {F₂ = F₂} {G₁ = G₁} {G₂ = G₂} eqF eqG x
    with eqF x | eqG (u F₂ x)
  ... | rF , hF | rG , hG =
      trans (cong (u G₁) rF) rG
    , λ t →
        let i₁ = mapP F₁ x t
            i₂ = mapP F₂ x t
            c  = cong (u G₁) rF
        in
        ≈Mˢ-trans (≈A Z) (≈E Z)
          (relocate-compˢ (≈A Z) (≈E Z) c rG
             (mapP G₁ (u F₁ x) i₁))
          (≈Mˢ-trans (≈A Z) (≈E Z)
            (relocate-resp-≈Mˢ (≈A Z) (≈E Z) rG
               (mapP-cross {f = G₁} rF i₁))
            (≈Mˢ-trans (≈A Z) (≈E Z)
              (relocate-resp-≈Mˢ (≈A Z) (≈E Z) rG
                 (mapP-cong G₁ (hF t)))
              (hG i₂)))

------------------------------------------------------------------------
-- Category laws
--
-- The image maps compose as functions, so after the index refl is
-- grouped every law is bisimulation reflexivity.
--
-- 范畴律
--
-- 像映射如函数般复合，故归并索引 refl 后每条律都是互模拟自反。

module _ {i a b ℓa ℓe : Level}
         {W X Y Z : SysEq i a b ℓa ℓe}
         {f : PushMˢ W X} {g : PushMˢ X Y} {h : PushMˢ Y Z} where

  assocPM : compPMˢ (compPMˢ h g) f ≈PM compPMˢ h (compPMˢ g f)
  assocPM w = refl , λ t → ≈Mˢ-refl (≈A Z) (≈E Z)
                          (mapP h (u g (u f w))
                            (mapP g (u f w) (mapP f w t)))

  sym-assocPM : compPMˢ h (compPMˢ g f) ≈PM compPMˢ (compPMˢ h g) f
  sym-assocPM w = refl , λ t → ≈Mˢ-refl (≈A Z) (≈E Z)
                          (mapP h (u g (u f w))
                            (mapP g (u f w) (mapP f w t)))

module _ {i a b ℓa ℓe : Level} {X Y : SysEq i a b ℓa ℓe}
         {f : PushMˢ X Y} where

  identityˡPM : compPMˢ idPMˢ f ≈PM f
  identityˡPM x = refl , λ t → ≈Mˢ-refl (≈A Y) (≈E Y) (mapP f x t)

  identityʳPM : compPMˢ f idPMˢ ≈PM f
  identityʳPM x = refl , λ t → ≈Mˢ-refl (≈A Y) (≈E Y) (mapP f x t)

module _ {i a b ℓa ℓe : Level} {X : SysEq i a b ℓa ℓe} where

  identity²PM : compPMˢ (idPMˢ {X = X}) idPMˢ ≈PM idPMˢ {X = X}
  identity²PM x = refl , λ t → ≈Mˢ-refl (≈A X) (≈E X) t

------------------------------------------------------------------------
-- The category
--
-- A fully relational index layer (u itself a relation) is a
-- bicategory/proarrow equipment, not a plain 1-category.
--
-- 范畴
--
-- 完全关系化的索引层（u 本身也是关系）是双范畴/前伴随装备，
-- 而非普通 1-范畴。

PushCatˢ : (i a b ℓa ℓe : Level)
         → Category (lsuc (i ⊔ a ⊔ b ⊔ ℓa ⊔ ℓe))
                    (i ⊔ a ⊔ b ⊔ ℓa ⊔ ℓe)
                    (i ⊔ a ⊔ b ⊔ ℓa ⊔ ℓe)
PushCatˢ i a b ℓa ℓe = record
  { Obj       = SysEq i a b ℓa ℓe
  ; _⇒_       = PushMˢ
  ; _≈_       = λ {X} {Y} → _≈PM_ {X = X} {Y = Y}
  ; id        = λ {X} → idPMˢ {X = X}
  ; _∘_       = λ {X} {Y} {Z} g f → compPMˢ g f
  ; assoc     = λ {W} {X} {Y} {Z} {f} {g} {h} →
                  assocPM {W = W} {X = X} {Y = Y} {Z = Z}
                           {f = f} {g = g} {h = h}
  ; sym-assoc = λ {W} {X} {Y} {Z} {f} {g} {h} →
                  sym-assocPM {W = W} {X = X} {Y = Y} {Z = Z}
                               {f = f} {g = g} {h = h}
  ; identityˡ = λ {X} {Y} {f} → identityˡPM {X = X} {Y = Y} {f = f}
  ; identityʳ = λ {X} {Y} {f} → identityʳPM {X = X} {Y = Y} {f = f}
  ; identity² = λ {X} → identity²PM {X = X}
  ; equiv     = λ {X} {Y} → ≈PM-isEquivalence {X = X} {Y = Y}
  ; ∘-resp-≈  = λ {X} {Y} {Z} {f = f} {h = h} {g = g} {i = k} fh gk →
                  ∘-resp-≈PM {X = X} {Y = Y} {Z = Z}
                              {F₁ = g} {F₂ = k} {G₁ = f} {G₂ = h} gk fh
  }
