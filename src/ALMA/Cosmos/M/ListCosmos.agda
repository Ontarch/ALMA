------------------------------------------------------------------------
-- Non-trivial fixed-label deterministic endomorphism on the M-Cosmos
--
-- The uniform binary universe and the swap01 (n = 2) edge permutation.
-- The fixed-label essence of the old ListCosmos swap01 is the
-- non-identity edge bijection at n = 2 (opposite, exchanging positions
-- 0 and 1); it is a legitimate fixed-label endomorphism exactly on a
-- UNIFORMLY BRANCHING universe, i.e. the single-shape container
-- (Shape = ⊤, Position = const (Fin 2)). The index I = Σ ⊤ ⊤ is a
-- singleton, every label has a unique ⊤-valued pts, and the edge fibre
-- is Fin 2, so opposite is a total involutive edge self-bijection for
-- every label. Everything is carried data.
--
-- M-Cosmos 上的非平凡固定标签确定性自态射
--
-- 一致二元宇宙与 swap01（n = 2）边置换。旧 ListCosmos swap01 在固定
-- 标签下的本质是 n = 2 处的非恒等边双射（opposite，交换位置 0 与 1）；
-- 它恰在一致分支宇宙上成为合法的固定标签自态射，即单一形状容器
-- （Shape = ⊤、Position = const (Fin 2)）。索引 I = Σ ⊤ ⊤ 为单例，
-- 每个标签的 pts 唯一，边纤维即 Fin 2，故 opposite 对每个标签都是满
-- 定义、对合的边自双射。一切皆为携带数据。
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module ALMA.Cosmos.M.ListCosmos where

open import Agda.Primitive using (lzero)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Sigma using (Σ; _,_)
open import Data.Unit.Polymorphic.Base using (⊤; tt)
open import Data.Fin.Base using (Fin; opposite) renaming (zero to fzero; suc to fsuc)
open import Data.Fin.Properties using (opposite-involutive)
open import Data.Container.Core using (Container)
open import Data.Product.Base using (proj₁)
open import Relation.Binary.PropositionalEquality.Core using (cong)
open import Relation.Nullary.Negation using (¬_)

open import Categories.Category.Core using (Category)
open import Categories.Category.Instance.One using (One)
open import Categories.Functor.Core using (Functor)
open import Categories.Functor using () renaming (id to idF)

open import ALMA.Cosmos.ContCategory using (ContCat; ≈sr-refl)
open import ALMA.Cosmos.ContCatEquiv using (ShapeCat)
open import ALMA.Base.MCorrSetoid using (FiberAdjˢ; propEqOn)
open import ALMA.Base.MCorrSetoidCat using (FMˢ; FMapˢ)
import ALMA.Cosmos.M.Object as MO
import ALMA.Cosmos.M.DetCongruence as DC

------------------------------------------------------------------------
-- Terminal base category and the uniform binary container
--
-- 终基范畴与一致二元容器

C₀ : Category lzero lzero lzero
C₀ = One

BinContainer : Container lzero lzero
BinContainer = record { Shape = ⊤ ; Position = λ _ → Fin 2 }

idFin2 : Fin 2 → Fin 2
idFin2 p = p

BinFC : Functor C₀ (ContCat lzero lzero)
BinFC = record
  { F₀           = λ _ → BinContainer
  ; F₁           = λ _ → record { shape = λ _ → tt ; position = idFin2 }
  ; identity     = ≈sr-refl
  ; homomorphism = ≈sr-refl
  ; F-resp-≈     = λ _ → ≈sr-refl
  }

open DC using (UniDet; uniFMapˢ; uniFMˢ)

------------------------------------------------------------------------
-- Index, label and edge fibre for the binary universe
--
-- 二元宇宙的索引、标签与边纤维

BinI : Set lzero
BinI = MO.I C₀ BinFC

BinData : Set lzero
BinData = MO.CosmosData C₀ BinFC

BinE : (i : BinI) (d : BinData) (j : BinI) → Set lzero
BinE = MO.E C₀ BinFC

i0 : BinI
i0 = tt , tt

-- At the unique index the edge fibre is Fin 2
--
-- The target equation is necessarily i0 ≡ i0. Edges are introduced as
-- (p , refl).
--
-- 在唯一索引处边纤维即 Fin 2
--
-- 目标等式必为 i0 ≡ i0。边以 (p , refl) 引入。
Edge : (d : BinData) → Set lzero
Edge d = BinE i0 d i0

------------------------------------------------------------------------
-- The unique label
--
-- uf is the unique ShapeCat → One functor, pts the unique ⊤-valued map.
--
-- 唯一标签
--
-- uf 是唯一的 ShapeCat → One 函子，pts 是唯一的 ⊤ 值映射。

uf0 : Functor (ShapeCat C₀ BinFC) C₀
uf0 = record
  { F₀           = proj₁
  ; F₁           = proj₁
  ; identity     = Category.Equiv.refl C₀
  ; homomorphism = Category.Equiv.refl C₀
  ; F-resp-≈     = λ p → p
  }

d0 : BinData
d0 = record { uf = uf0 ; pts = λ { _ _ → tt } }

------------------------------------------------------------------------
-- The edge permutation
--
-- It acts only on the position and keeps the constructive target
-- equation as an (un-matched) variable: at the unique index the target
-- is i0 regardless of the position, so the same equation types the
-- moved edge. Matching it with refl would require pair injectivity
-- (unsupported under --cubical-compatible).
--
-- 边置换
--
-- 只作用于位置，并把构造性目标等式作为（不匹配的）变量保留：在唯一
-- 索引处目标恒为 i0，与位置无关，故同一等式即可为移动后的边定型。
-- 用 refl 匹配该等式会依赖配对单射（--cubical-compatible 不支持）。

swapE : ∀ (d : BinData) → Edge d → Edge d
swapE d (p , eq) = opposite p , eq

------------------------------------------------------------------------
-- Uniform deterministic data for the identity index functor
--
-- pb v = (v , refl); adj is the opposite edge self-bijection, with both
-- round-trips from the involution; it ignores d, satisfying the
-- fixed-label uniformity premise.
--
-- 恒等索引函子的一致确定性数据
--
-- pb v = (v , refl)；adj 为 opposite 边自双射，两条往返由对合给出；
-- 忽略 d，满足固定标签一致性前提。

private
  swapAdj : (d : BinData)
          → FiberAdjˢ (propEqOn (Edge d)) (propEqOn (Edge d))
  swapAdj d = record
    { to        = swapE d
    ; fro       = swapE d
    ; to-cong   = λ eq → cong (swapE d) eq
    ; fro-cong  = λ eq → cong (swapE d) eq
    ; η         = λ { (p , eq) →
                    cong (λ q → (q , eq)) (opposite-involutive p) }
    ; ε         = λ { (p , eq) →
                    cong (λ q → (q , eq)) (opposite-involutive p) }
    }

swapUni : UniDet C₀ BinFC (idF {C = ShapeCat C₀ BinFC})
UniDet.pb  swapUni v = v , refl
UniDet.adj swapUni (tt , tt) d (tt , tt) = swapAdj d

------------------------------------------------------------------------
-- Categorical endomorphism bundle
--
-- map-cong is supplied by the fixed-label gow-setoid engine (uniFMˢ),
-- never derived by eliminating equality.
--
-- 范畴自态射束
--
-- map-cong 由固定标签 gow-setoid 引擎（uniFMˢ）供给，绝不靠消去等式
-- 得到。

swapFMˢ : FMˢ (MO.sys C₀ BinFC (λ _ → propEqOn _))
              (MO.sys C₀ BinFC (λ _ → propEqOn _))
swapFMˢ = uniFMˢ C₀ BinFC (idF {C = ShapeCat C₀ BinFC}) swapUni

------------------------------------------------------------------------
-- Non-identity witness
--
-- The carried edge action sends position 0 to position 1, so it cannot
-- fix position 0.
--
-- 非恒等见证
--
-- 所携带的边作用把位置 0 送到位置 1，故它不可能固定位置 0。

e0 : Edge d0
e0 = fzero , refl

e1 : Edge d0
e1 = fsuc fzero , refl

swap-sends-0→1 :
  FiberAdjˢ.to (FMapˢ.adjFˢ (FMˢ.mor swapFMˢ) i0 d0 i0) e0 ≡ e1
swap-sends-0→1 = refl

swap-nonidentity :
  ¬ FiberAdjˢ.to (FMapˢ.adjFˢ (FMˢ.mor swapFMˢ) i0 d0 i0) e0 ≡ e0
swap-nonidentity ()
