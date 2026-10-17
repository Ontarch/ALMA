------------------------------------------------------------------------
-- ListSwapDef: a label-changing deterministic endomorphism on a small
-- universe whose position permutation is DEFINITIONALLY involutive on
-- every relevant shape
--
-- The carried fibre adjunction closes by pure construction.
-- The position set at shape n is Fin n ⊎ Fin n (two copies), and
-- flip swaps the two summands.
-- inj₁/inj₂ are constructors of the ordinary (non-indexed) sum type, so
-- splitting on them is legal under --cubical-compatible, and
-- flip ∘ flip reduces to the identity definitionally in every clause.
-- Contrast: the general ℕ/Fin swap01 (ListSwap) only has propositional
-- involution and needs the conditional DecUIP theorem for ε.
--
-- ListSwapDef：一个小宇宙上的改标签确定性自态射，其位置置换在所有相
-- 关形状上均定义性对合
--
-- 携带纤维伴随由纯构造闭合。
-- 形状 n 处的位置集为 Fin n ⊎ Fin n（两份副本），置换 flip 交换两个
-- 求和分支。inj₁/inj₂ 是普通（非索引）求和类型的构造子，故在
-- --cubical-compatible 下对其匹配合法，且 flip ∘ flip 在每个子句中
-- 定义性归约为恒等。对照：一般 ℕ/Fin 的 swap01（ListSwap）仅命题对合，
-- 其 ε 需要条件 DecUIP 定理。
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module ALMA.Cosmos.M.ListSwapDef where

open import Agda.Primitive using (lzero)
open import Data.Unit.Polymorphic.Base using (tt)
open import Data.Nat using (ℕ; _+_)
open import Data.Fin.Base using (Fin; zero; toℕ)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Product.Base using (proj₁; _,_)
open import Data.Container.Core using (Container)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl; cong)
open import Relation.Nullary.Negation using (¬_)

open import Categories.Category.Core using (Category)
open import Categories.Category.Instance.One using (One)
open import Categories.Functor using (Functor) renaming (id to idF)

open import ALMA.Cosmos.ContCategory using (ContCat; ≈sr-refl)
open import ALMA.Cosmos.ContCatEquiv using (ShapeCat)
open import ALMA.Base.MCorrSetoid using (FiberAdjˢ; propEqOn)
open import ALMA.Base.MCorrSetoidCat using (FMˢ; FMapˢ)
import ALMA.Cosmos.M.Object as MO
import ALMA.Cosmos.M.GenCongruence as GC

------------------------------------------------------------------------
-- Terminal base category and the two-copy list container
--
-- Position n = Fin n ⊎ Fin n.
--
-- 终基范畴与双份列表容器
--
-- Position n = Fin n ⊎ Fin n。

C₀ : Category lzero lzero lzero
C₀ = One

SumContainer : Container lzero lzero
SumContainer = record { Shape = ℕ ; Position = λ n → Fin n ⊎ Fin n }

idSum : ∀ {n : ℕ} → Fin n ⊎ Fin n → Fin n ⊎ Fin n
idSum z = z

SumFC : Functor C₀ (ContCat lzero lzero)
SumFC = record
  { F₀           = λ _ → SumContainer
  ; F₁           = λ _ → record { shape = λ n → n ; position = idSum }
  ; identity     = ≈sr-refl
  ; homomorphism = ≈sr-refl
  ; F-resp-≈     = λ _ → ≈sr-refl
  }

open GC using (GenDet; genFMˢ)

------------------------------------------------------------------------
-- Indices, labels and edge fibres
--
-- 索引、标签与边纤维

S-I : Set lzero
S-I = MO.I C₀ SumFC

SData : Set lzero
SData = MO.CosmosData C₀ SumFC

SE : (i : S-I) (d : SData) (j : S-I) → Set lzero
SE = MO.E C₀ SumFC

uf0 : Functor (ShapeCat C₀ SumFC) C₀
uf0 = record
  { F₀           = proj₁
  ; F₁           = proj₁
  ; identity     = Category.Equiv.refl C₀
  ; homomorphism = Category.Equiv.refl C₀
  ; F-resp-≈     = λ p → p
  }

------------------------------------------------------------------------
-- flip
--
-- Swaps the two summands; definitionally involutive on every constructor
-- form (only the non-indexed inj₁/inj₂ are matched).
--
-- flip
--
-- 交换两个求和分支；在每个构造形式上定义性对合（只匹配非索引的
-- inj₁/inj₂）。

flip : ∀ {n : ℕ} → Fin n ⊎ Fin n → Fin n ⊎ Fin n
flip (inj₁ x) = inj₂ x
flip (inj₂ x) = inj₁ x

------------------------------------------------------------------------
-- The standard two-copy label and the total label action
--
-- pts (σ d) n q = pts d n (flip q). The first copy routes to toℕ k, the
-- second to toℕ k + n, so the two copies genuinely lead to different
-- child shapes and flipping them changes the label.
--
-- 标准双份标签与满标签作用
--
-- pts (σ d) n q = pts d n (flip q)。第一份路由到 toℕ k，第二份到
-- toℕ k + n，故两份确实通向不同子形状，交换它们会改变标签。

route : (n : ℕ) → Fin n ⊎ Fin n → ℕ
route n (inj₁ k) = toℕ k
route n (inj₂ k) = toℕ k + n

dStd : SData
dStd = record { uf = uf0 ; pts = λ { {A} n z → route n z } }

σlabel : SData → SData
σlabel d = record
  { uf  = MO.CosmosData.uf d
  ; pts = λ { {A} n q → MO.CosmosData.pts d n (flip q) }
  }

------------------------------------------------------------------------
-- The carried flip edge self-bijection
--
-- After splitting on inj₁/inj₂, the target routing
-- pts (σ d) n (flip p) = pts d n (flip (flip p)) reduces definitionally
-- to pts d n p, so both directions reuse the carried equation and both
-- round-trips are definitionally the identity.
--
-- 携带的 flip 边自双射
--
-- 在按 inj₁/inj₂ 分情况后，目标路由
-- pts (σ d) n (flip p) = pts d n (flip (flip p)) 定义性归约为
-- pts d n p，故两个方向都直接复用携带的等式，两条往返都定义性为恒等。

private
  toAdj : ∀ {n m} (d : SData)
        → SE (tt , n) d (tt , m) → SE (tt , n) (σlabel d) (tt , m)
  toAdj d (inj₁ x , eq) = inj₂ x , eq
  toAdj d (inj₂ x , eq) = inj₁ x , eq

  froAdj : ∀ {n m} (d : SData)
         → SE (tt , n) (σlabel d) (tt , m) → SE (tt , n) d (tt , m)
  froAdj d (inj₁ x , eq) = inj₂ x , eq
  froAdj d (inj₂ x , eq) = inj₁ x , eq

  adjη : ∀ {n m} d (e : SE (tt , n) d (tt , m))
       → froAdj d (toAdj d e) ≡ e
  adjη d (inj₁ x , eq) = refl
  adjη d (inj₂ x , eq) = refl

  adjε : ∀ {n m} d (e : SE (tt , n) (σlabel d) (tt , m))
       → toAdj d (froAdj d e) ≡ e
  adjε d (inj₁ x , eq) = refl
  adjε d (inj₂ x , eq) = refl

  flipAdj : ∀ {n m} (d : SData)
          → FiberAdjˢ (propEqOn (SE (tt , n) (σlabel d) (tt , m)))
                      (propEqOn (SE (tt , n) d (tt , m)))
  flipAdj {n = n} {m = m} d = record
    { to       = toAdj d
    ; fro      = froAdj d
    ; to-cong  = λ eq → cong (toAdj d) eq
    ; fro-cong = λ eq → cong (froAdj d) eq
    ; η        = adjη d
    ; ε        = adjε d
    }

------------------------------------------------------------------------
-- General deterministic data for the identity index functor
--
-- 恒等索引函子的一般确定性数据

flipGen : GenDet C₀ SumFC (idF {C = ShapeCat C₀ SumFC})
GenDet.σ   flipGen _ d = σlabel d
GenDet.pb  flipGen v = v , refl
GenDet.adj flipGen (tt , n) d (tt , m) = flipAdj {n = n} {m = m} d

------------------------------------------------------------------------
-- Categorical label-changing deterministic endomorphism bundle
--
-- Its map-cong is supplied by the GenCongruence engine.
--
-- 范畴改标签确定性自态射束
--
-- 其 map-cong 由 GenCongruence 引擎供给。

flipFMˢ : FMˢ (MO.sys C₀ SumFC (λ _ → propEqOn _))
              (MO.sys C₀ SumFC (λ _ → propEqOn _))
flipFMˢ = genFMˢ C₀ SumFC (idF {C = ShapeCat C₀ SumFC}) flipGen

------------------------------------------------------------------------
-- Non-identity witness at shape 1
--
-- The first copy (position inj₁ fzero, routing to child shape 0) is sent
-- to the second copy (inj₂ fzero), which under σ d routes back to child
-- shape 0. The position changes, so the edge action is not the identity.
--
-- 形状 1 处的非恒等见证
--
-- 第一份（位置 inj₁ fzero，路由到子形状 0）被送到第二份
-- （inj₂ fzero），后者在 σ d 下路由回子形状 0。位置发生改变，故边作用
-- 非恒等。

private
  e0 : SE (tt , 1) dStd (tt , 0)
  e0 = inj₁ zero , refl

  e1 : SE (tt , 1) (σlabel dStd) (tt , 0)
  e1 = inj₂ zero , refl

  adjAt : FiberAdjˢ (propEqOn (SE (tt , 1) (σlabel dStd) (tt , 0)))
                    (propEqOn (SE (tt , 1) dStd (tt , 0)))
  adjAt = FMapˢ.adjFˢ (FMˢ.mor flipFMˢ) (tt , 1) dStd (tt , 0)

  fwd : SE (tt , 1) dStd (tt , 0) → SE (tt , 1) (σlabel dStd) (tt , 0)
  fwd = FiberAdjˢ.to adjAt

flip-sends-0→1 : fwd e0 ≡ e1
flip-sends-0→1 = refl

flip-nonidentity : ¬ (proj₁ (fwd e0) ≡ inj₁ zero)
flip-nonidentity ()
