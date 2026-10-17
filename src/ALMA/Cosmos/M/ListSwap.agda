------------------------------------------------------------------------
-- Label-changing deterministic endomorphism on the M-Cosmos
--
-- The list universe (Shape = ℕ, Position = Fin n) and the swap01
-- permutation, via the label-changing engine Cosmos.M.GenCongruence.
-- The endomorphism keeps the node index (S = id), conjugates the
-- routing by swap01
--   pts (σ d) n q = pts d n (swap01 n q),
-- covers each target child index by itself, and carries the swap01 edge
-- self-bijection uniformly for every d. On general Fin n swap01 is only
-- propositionally involutive; the edge bijection keeps the routing
-- equation as a carried variable, and the only transport is a single
-- legal J (castTo) matching the involution redex with a neutral term on
-- the left and a rigid p on the right.
--
-- M-Cosmos 上的改标签确定性自态射
--
-- 列表宇宙（Shape = ℕ，Position = Fin n）与 swap01 置换，经由改标签
-- 引擎 Cosmos.M.GenCongruence。该自态射保持节点索引（S = id），用
-- swap01 共轭路由
--   pts (σ d) n q = pts d n (swap01 n q)，
-- 每个目标子索引由自身覆盖，并对每个 d 一致地携带 swap01 边自双射。
-- 在一般 Fin n 上 swap01 仅命题地对合；边双射把路由等式作为携带变量
-- 保留，唯一传输是单个合法 J（castTo），以左侧中性项、右侧刚性 p 匹
-- 配对合可约式。
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module ALMA.Cosmos.M.ListSwap where

open import Agda.Primitive using (lzero)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Sigma using (Σ; _,_)
open import Axiom.UniquenessOfIdentityProofs using (module Decidable⇒UIP)
open import Data.Unit.Polymorphic.Base using (⊤; tt)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Fin.Base using (Fin; toℕ; splitAt; join; opposite)
  renaming (zero to fzero; suc to fsuc)
open import Data.Fin.Properties using (opposite-involutive; join-splitAt; splitAt-join)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Product.Base using (proj₁)
open import Data.Product.Properties using (≡-dec)
open import Data.Nat using (_≟_)
open import Data.Unit.Polymorphic.Properties renaming (_≟_ to _⊤≟_)
open import Data.Container.Core using (Container)
open import Function.Base using (_∘_)
open import Relation.Binary.Definitions using (Irrelevant)
open import Relation.Binary.PropositionalEquality.Core using (cong; trans)
open import Relation.Binary.PropositionalEquality.Properties using (module ≡-Reasoning)
open ≡-Reasoning
open import Relation.Nullary.Negation using (¬_)

open import Categories.Category.Core using (Category)
open import Categories.Category.Instance.One using (One)
open import Categories.Functor using (id)
open import Categories.Functor.Core using (Functor)
open Functor using (F₀)

open import ALMA.Cosmos.ContCategory using (ContCat; ≈sr-refl)
open import ALMA.Cosmos.ContCatEquiv using (ShapeCat)
open import ALMA.Base.MCorrSetoid using (FiberAdjˢ; propEqOn)
open import ALMA.Base.MCorrSetoidCat using (FMˢ; FMapˢ)
import ALMA.Cosmos.M.Object as MO
import ALMA.Cosmos.M.GenCongruence as GC

------------------------------------------------------------------------
-- Terminal base category and the list container
--
-- 终基范畴与列表容器

C₀ : Category lzero lzero lzero
C₀ = One

ListContainer : Container lzero lzero
ListContainer = record { Shape = ℕ ; Position = Fin }

idFin : ∀ {n : ℕ} → Fin n → Fin n
idFin p = p

ListFC : Functor C₀ (ContCat lzero lzero)
ListFC = record
  { F₀           = λ _ → ListContainer
  ; F₁           = λ _ → record { shape = λ n → n ; position = idFin }
  ; identity     = ≈sr-refl
  ; homomorphism = ≈sr-refl
  ; F-resp-≈     = λ _ → ≈sr-refl
  }

open GC using (GenDet; genFMˢ)

------------------------------------------------------------------------
-- Indices, labels and edge fibres
--
-- 索引、标签与边纤维

L-I : Set lzero
L-I = MO.I C₀ ListFC

LData : Set lzero
LData = MO.CosmosData C₀ ListFC

LE : (i : L-I) (d : LData) (j : L-I) → Set lzero
LE = MO.E C₀ ListFC

uf0 : Functor (ShapeCat C₀ ListFC) C₀
uf0 = record
  { F₀           = proj₁
  ; F₁           = proj₁
  ; identity     = Category.Equiv.refl C₀
  ; homomorphism = Category.Equiv.refl C₀
  ; F-resp-≈     = λ p → p
  }

------------------------------------------------------------------------
-- swap01
--
-- Swap the first two positions of Fin n, leave the rest.
--
-- swap01
--
-- 交换 Fin n 的前两个位置，其余不变。

private
  swapFin2 : Fin 2 → Fin 2
  swapFin2 = opposite

  swapSum : ∀ {n} → Fin 2 ⊎ Fin n → Fin 2 ⊎ Fin n
  swapSum (inj₁ i) = inj₁ (swapFin2 i)
  swapSum (inj₂ k) = inj₂ k

  swapSum-invol : ∀ {n} (z : Fin 2 ⊎ Fin n) → swapSum (swapSum z) ≡ z
  swapSum-invol (inj₁ i) = cong inj₁ (opposite-involutive i)
  swapSum-invol (inj₂ k) = refl

-- Shape n is a plain natural number, so the case split is ordinary Nat
-- matching: at n = 2 the permutation is opposite (definitional); at
-- n ≥ 3 it is the splitAt/join surgery.
--
-- 形状 n 是普通自然数，故分情形是普通 Nat 匹配：n = 2 时置换为
-- opposite（定义性）；n ≥ 3 时为 splitAt/join 手术。
swap01 : (n : ℕ) → Fin n → Fin n
swap01 zero              ()
swap01 (suc zero)        i = i
swap01 (suc (suc zero))  i = opposite i
swap01 (suc (suc (suc n))) i = join 2 (suc n) (swapSum (splitAt 2 i))

-- Propositional involution of swap01; no Fin-constructor indexed match.
--
-- swap01 的命题对合；无 Fin 构造子索引匹配。
swap01-invol : ∀ {n : ℕ} (p : Fin n) → swap01 n (swap01 n p) ≡ p
swap01-invol {zero}              ()
swap01-invol {suc zero}          i = refl
swap01-invol {suc (suc zero)}    i = opposite-involutive i
swap01-invol {suc (suc (suc n))} i =
  begin
    join 2 (suc n)
      (swapSum (splitAt 2
        (join 2 (suc n) (swapSum (splitAt 2 i)))))
  ≡⟨ cong (join 2 (suc n) ∘ swapSum)
         (splitAt-join 2 (suc n) (swapSum (splitAt 2 i))) ⟩
    join 2 (suc n) (swapSum (swapSum (splitAt 2 i)))
  ≡⟨ cong (join 2 (suc n)) (swapSum-invol (splitAt 2 i)) ⟩
    join 2 (suc n) (splitAt 2 i)
  ≡⟨ join-splitAt 2 (suc n) i ⟩
    i
  ∎

------------------------------------------------------------------------
-- The standard list label and its swap-conjugate
--
-- 标准列表标签与其交换共轭

dList : LData
dList = record { uf = uf0 ; pts = λ { {A} n i → toℕ i } }

dSwap : LData
dSwap = record { uf = uf0 ; pts = λ { {A} n i → toℕ (swap01 n i) } }

-- Total label action: conjugate the routing by swap01; σ dList is
-- definitionally dSwap.
--
-- 满标签作用：用 swap01 共轭路由；σ dList 定义性地即 dSwap。
σlabel : LData → LData
σlabel d = record
  { uf  = MO.CosmosData.uf d
  ; pts = λ { {A} n q → MO.CosmosData.pts d n (swap01 n q) }
  }

------------------------------------------------------------------------
-- The uniform swap01 edge self-bijection at a fixed child shape m
--
-- fro keeps the routing equation as a carried variable (the swapped
-- position routes under d exactly where the σ d edge witnesses). to
-- changes the routing from pts d n p to pts d n (swap01 (swap01 p));
-- castTo is a single legal J on the neutral involution redex
-- (generalises to rigid p), computing to the identity. The round-trips
-- close by that same J.
--
-- 固定子形状 m 处一致的 swap01 边自双射
--
-- fro 把路由等式作为携带变量保留（交换后的位置在 d 下恰路由到 σ d 边
-- 所见证处）。to 把路由从 pts d n p 改为 pts d n (swap01 (swap01 p))；
-- castTo 是对中性对合可约式的单个合法 J（一般化为刚性 p），计算为恒
-- 等。往返由同一 J 闭合。

private
  ρof : (ℓ : LData) (n : ℕ) → Fin n → ℕ
  ρof ℓ n i = MO.CosmosData.pts ℓ n i

  -- p₁ and p₂ are independent variables, so matching ip with refl is
  -- the J rule (generalises a neutral index).
  --
  -- p₁、p₂ 为独立变量，故用 refl 匹配 ip 是 J 规则（一般化中性索引）。
  castTo : ∀ {n m : ℕ} (ℓ : LData) (ρ : Fin n → ℕ) {p₁ p₂ : Fin n}
         → p₁ ≡ p₂
         → (tt , m) ≡ (F₀ (MO.CosmosData.uf ℓ) (tt , n) , ρ p₂)
         → (tt , m) ≡ (F₀ (MO.CosmosData.uf ℓ) (tt , n) , ρ p₁)
  castTo ℓ ρ refl eq = eq

  edgeJ : ∀ {n m : ℕ} (ℓ : LData) (ρ : Fin n → ℕ) {p₁ p₂ : Fin n}
        → (ip : p₁ ≡ p₂)
        → (eq : (tt , m) ≡ (F₀ (MO.CosmosData.uf ℓ) (tt , n) , ρ p₂))
        → (p₁ , castTo ℓ ρ ip eq) ≡ (p₂ , eq)
  edgeJ ℓ ρ refl eq = refl

  -- Conditional proof irrelevance for ⊤ × ℕ, used only in this ℕ/Fin
  -- example: ℕ has decidable equality, so UIP holds here as a theorem
  -- (DecUIP). The M core and the GenCongruence engine remain pure J
  -- and do not use this.
  --
  -- 索引集 ⊤ × ℕ 的条件证明无关性，仅用于本 ℕ/Fin 示例：ℕ 具有可判定
  -- 等式，故 UIP 在此作为定理（DecUIP）成立。M 内核与 GenCongruence
  -- 引擎仍为纯 J，不使用此定理。
  index-eq? : Relation.Binary.Definitions.DecidableEquality (Σ ⊤ (λ _ → ℕ))
  index-eq? = ≡-dec (_⊤≟_ {lzero}) _≟_

  pair-eq-irr : Irrelevant {A = Σ ⊤ (λ _ → ℕ)} _≡_
  pair-eq-irr = Decidable⇒UIP.≡-irrelevant index-eq?

  toAdj : ∀ {n m} (d : LData)
        → LE (tt , n) d (tt , m) → LE (tt , n) (σlabel d) (tt , m)
  toAdj {n = n} d (p , eq) =
    swap01 n p , castTo d (ρof d n) (swap01-invol p) eq

  froAdj : ∀ {n m} (d : LData)
        → LE (tt , n) (σlabel d) (tt , m) → LE (tt , n) d (tt , m)
  froAdj {n = n} d (q , eq) = swap01 n q , eq

  adjη : ∀ {n m} d (e : LE (tt , n) d (tt , m))
       → froAdj d (toAdj d e) ≡ e
  adjη {n = n} d (p , eq) =
    edgeJ d (ρof d n) (swap01-invol p) eq

  -- ε closes by the same J, after identifying the two J transports along
  -- the two involution proofs with the conditional DecUIP irrelevance.
  --
  -- ε 先以条件 DecUIP 证明无关性识别沿两个对合证明的两个 J 传输，再由
  -- 同一 J 闭合。
  adjε : ∀ {n m} d (e : LE (tt , n) (σlabel d) (tt , m))
       → toAdj d (froAdj d e) ≡ e
  adjε {n = n} d (q , eq) =
    let castA = castTo d (ρof d n) (swap01-invol (swap01 n q)) eq
        castB = castTo (σlabel d) (ρof (σlabel d) n) (swap01-invol q) eq
    in trans (cong (λ e0 → swap01 n (swap01 n q) , e0)
                   (pair-eq-irr castA castB))
             (edgeJ (σlabel d) (ρof (σlabel d) n) (swap01-invol q) eq)

  swapAdj : ∀ {n m} (d : LData)
          → FiberAdjˢ (propEqOn (LE (tt , n) (σlabel d) (tt , m)))
                      (propEqOn (LE (tt , n) d (tt , m)))
  swapAdj {n = n} {m = m} d = record
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

swapGen : GenDet C₀ ListFC (id {C = ShapeCat C₀ ListFC})
GenDet.σ   swapGen _ d = σlabel d
GenDet.pb  swapGen v = v , refl
GenDet.adj swapGen (tt , n) d (tt , m) = swapAdj {n = n} {m = m} d

------------------------------------------------------------------------
-- Categorical label-changing deterministic endomorphism bundle
--
-- Its map-cong is supplied by the GenCongruence engine.
--
-- 范畴改标签确定性自态射束
--
-- 其 map-cong 由 GenCongruence 引擎供给。

swapFMˢ : FMˢ (MO.sys C₀ ListFC (λ _ → propEqOn _))
              (MO.sys C₀ ListFC (λ _ → propEqOn _))
swapFMˢ = genFMˢ C₀ ListFC (id {C = ShapeCat C₀ ListFC}) swapGen

------------------------------------------------------------------------
-- Non-identity witness at shape 2
--
-- The forward edge action sends position 0 (routing to child shape 0
-- under dList) to position 1 (the σ dList = dSwap routing), so it cannot
-- fix position 0.
--
-- 形状 2 处的非恒等见证
--
-- 正向边作用把位置 0（dList 下路由到子形状 0）送到位置 1（σ dList =
-- dSwap 路由），故它不可能固定位置 0。

private
  e0 : LE (tt , 2) dList (tt , 0)
  e0 = fzero , refl

  e1 : LE (tt , 2) (σlabel dList) (tt , 0)
  e1 = fsuc fzero , refl

private
  adjAt : FiberAdjˢ (propEqOn (LE (tt , 2) (σlabel dList) (tt , 0)))
                    (propEqOn (LE (tt , 2) dList (tt , 0)))
  adjAt = FMapˢ.adjFˢ (FMˢ.mor swapFMˢ) (tt , 2) dList (tt , 0)

  fwd : LE (tt , 2) dList (tt , 0) → LE (tt , 2) (σlabel dList) (tt , 0)
  fwd = FiberAdjˢ.to adjAt

swap-sends-0→1 : fwd e0 ≡ e1
swap-sends-0→1 = refl

-- The forward edge leaving child shape 0 carries position 1, never
-- position 0: the relabelling is not the identity on edges.
--
-- 离开子形状 0 的前向边携带位置 1，绝非位置 0：该重标在边上不是恒等。
swap-nonidentity : ¬ (proj₁ (fwd e0) ≡ fzero)
swap-nonidentity ()
