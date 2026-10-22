------------------------------------------------------------------------
-- Universal property of the compatible-tower colimit
-- 相容塔余极限泛性质
--
-- Provides the colimit cocone, the cross-category morphism equivalence
-- _≈⇒ℱX_, the iterated tower embeddings embedCosmos^d / lift-subtower,
-- and the left-unit law for comp⇒ℱX-id-left
-- 提供余极限余锥、跨范畴态射等价 _≈⇒ℱX_、迭代塔嵌入 embedCosmos^d /
-- lift-subtower，以及 comp⇒ℱX-id-left 的左单位律
--
-- Zero-subst carried style: the d-fold Fin embedding is the carried
-- embFin (re-exported as inject₁^d from FinCatInfinity, target size
-- n-at (shift d m) reduces definitionally); the finFromℕ-maybe /
-- restrictFin machine in embedCosmos congruence is replaced by the total
-- clamp representative cl and the FinEmbed lemmas embedF-inject₁ /
-- embedF-newtop split by the Cubical-safe ≤-or->; the single transport
-- subst in transport-to-S-proj is replaced by a plain rewrite of the
-- natural-number index equality. No subst, no cast, no Maybe, no Dec/Bool.
-- 零 subst 携带式：d 次 Fin 嵌入即携带式 embFin（由 FinCatInfinity 再导出
-- 为 inject₁^d，目标尺寸 n-at (shift d m) 定义性归约）；embedCosmos 同余
-- 中的 finFromℕ-maybe / restrictFin 机器替换为全函数 clamp 代表 cl 与
-- FinEmbed 引理 embedF-inject₁ / embedF-newtop，按 Cubical 安全的
-- ≤-or-> 拆分；transport-to-S-proj 中唯一的传输 subst 改为对自然数索引
-- 等式的普通 rewrite。无 subst、无 cast、无 Maybe、无 Dec/Bool。
------------------------------------------------------------------------
{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module SecondPass.FinCatInfinityColimitUniversal where

open import Agda.Primitive using (Level; _⊔_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Level using (lift)
open import Data.Unit.Polymorphic.Base using (tt)
open import Data.Nat using (ℕ; zero; suc; _+_; _∸_; _≤_; _<_; z≤n; s≤s)
open import Data.Nat.Properties
  using ( +-identityʳ; +-suc; ≤-refl; ≤-trans; ≤-antisym; ≤-pred )
open import Data.Fin.Base using (Fin; toℕ; inject₁)
open import Data.Fin.Properties
  using (toℕ-inject₁; toℕ-injective; toℕ<n)
open import Data.Product.Base using (_,_; proj₁; proj₂)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality.Core using (cong; sym; trans)
open import Relation.Binary.PropositionalEquality.Properties using (module ≡-Reasoning)
open ≡-Reasoning

open import Categories.Category.Core using (Category)
open import Categories.Functor.Core using (Functor)
open import Categories.Functor using (id; _∘F_)

open import Cosmos.ContCategory using (ContCat)
open import Cosmos.ContCategoryLemmas using (ShapeOf; PosOf)
open import Cosmos.ContCatEquiv using (ShapeCat)
open import SecondPass.Unfolding using (Unfolding; module Unfolding)
open import SecondPass.Cosmos using (Cosmos; out; _⇒ℱ_; ⇒ℱLayer[_])
open import SecondPass.MorphismObject using (MorphismObject; compMorphismObject)
open import SecondPass.MorphismMorphism using (MorphismMorphism; compMorphismMorphism)
open import SecondPass.Terminal using (_≈C_; ≈C-refl; ≈C-sym; ≈C-trans)
open import SecondPass.MorphismCorrespondence using (≈C→⇒ℱ)
open import SecondPass.FinCatNWitness using (module FinCatN)
open import SecondPass.FinCatInfinity
  using (FinCat∞; TrivialFC∞; n-at)
open import SecondPass.FinCatInfinityProjection
  using (module FinCatNColimitProjection)
open import SecondPass.FinCatInfinityTowerCompat using (module FinCatTowerCompat)
open import Cosmos.Carried.LimitSystem using (cl; cl-toℕ; ≤-or->)
open import Cosmos.Carried.FinEmbed
  using (embedF-inject₁; embedF-newtop)
open import SecondPass.FinCatInfinityColimit
  using (CompatibleTower; subtower; towerColimit; towerColimit-spec
        ; _⇒ℱX[_]_; ⇒ℱXLayer[_]; comp⇒ℱX; id⇒ℱX; module TowerShapeFunctors
        ; module ProjCosmosMorphism; module EmbedCosmosMorphism)
open FinCatNColimitProjection using (defaultFin)
open _≈C_
open ⇒ℱLayer[_]
open _⇒ℱX[_]_
open ⇒ℱXLayer[_]
open CompatibleTower
open MorphismObject
open MorphismMorphism

-- Conversion from the S = id specialisation to the general cross-category
-- morphism along the identity shape functor
-- 从 S = id 特化到沿恒等形状函子的一般跨范畴态射的转换
⇒ℱ→⇒ℱX[id] : ∀ {o h e s p} {C : Category o h e} {FC : Functor C (ContCat s p)}
  → {F G : Cosmos C FC} → F ⇒ℱ G → F ⇒ℱX[ id ] G
⇒ℱ→⇒ℱX[id] m .out = record
  { shapeTrans    = ⇒ℱLayer[_].shapeTrans (m .out)
  ; morphismObj   = ⇒ℱLayer[_].morphismObj (m .out)
  ; morphismMor   = ⇒ℱLayer[_].morphismMor (m .out)
  ; onunfold-next = λ s → ⇒ℱ→⇒ℱX[id] (⇒ℱLayer[_].onunfold-next (m .out) s)
  }

-- Colimit cocone: layer m of the tower maps to the colimit, as a
-- cross-category morphism along the projection shape functor S-proj m
-- 余极限余锥：塔的第 m 层映射到余极限，作为沿投影形状函子 S-proj m
-- 的跨范畴态射
colimitCocone : ∀ (tower : CompatibleTower) m
  → CompatibleTower.seq tower m
    ⇒ℱX[ TowerShapeFunctors.S-proj m ] towerColimit tower
colimitCocone tower m =
  comp⇒ℱX
    (⇒ℱ→⇒ℱX[id] (≈C→⇒ℱ (towerColimit-spec tower m)))
    (ProjCosmosMorphism.projCosmos-morphism m (CompatibleTower.seq tower m))

-- Decision: either m ≤ n or suc n ≤ m (structurally recursive,
-- Cubical-safe sum view)
-- 判定：要么 m ≤ n，要么 suc n ≤ m（结构化递归、Cubical 安全的和式视图）
split≤ : ∀ m n → (m ≤ n) ⊎ (suc n ≤ m)
split≤ zero    n       = inj₁ z≤n
split≤ (suc m) zero    = inj₂ (s≤s z≤n)
split≤ (suc m) (suc n) with split≤ m n
... | inj₁ m≤n   = inj₁ (s≤s m≤n)
... | inj₂ sn≤m  = inj₂ (s≤s sn≤m)

-- Iterated inject₁: Fin (n-at m) → Fin (n-at (m + d)). The only rewrites
-- are natural-number arithmetic (+-identityʳ / +-suc); there is no subst
-- over Fin indices and no cast.
-- inject₁ 的 d 次迭代：Fin (n-at m) → Fin (n-at (m + d))。仅有的 rewrite
-- 是自然数算术（+-identityʳ / +-suc），不存在沿 Fin 索引的 subst，也无 cast。
inject₁^d : ∀ d {m} → Fin (n-at m) → Fin (n-at (m + d))
inject₁^d zero    {m} x rewrite +-identityʳ m = x
inject₁^d (suc d) {m} x rewrite +-suc m d     = inject₁ (inject₁^d d x)

-- inject₁^d preserves toℕ
-- inject₁^d 保持 toℕ
toℕ-inject₁^d : ∀ d {m} (x : Fin (n-at m)) → toℕ (inject₁^d d x) ≡ toℕ x
toℕ-inject₁^d zero    {m} x rewrite +-identityʳ m = refl
toℕ-inject₁^d (suc d) {m} x rewrite +-suc m d =
  begin
    toℕ (inject₁ (inject₁^d d x))
      ≡⟨ toℕ-inject₁ (inject₁^d d x) ⟩
    toℕ (inject₁^d d x)
      ≡⟨ toℕ-inject₁^d d x ⟩
    toℕ x
  ∎

-- Iterated S-embed: FinCatN m → FinCatN (m + d) at the shape level
-- S-embed 的 d 次迭代：形状层面 FinCatN m → FinCatN (m + d)
S-embed^d : ∀ d m → Functor (ShapeCat (FinCatN.FinCatN m) (FinCatN.TrivialFCN m))
                            (ShapeCat (FinCatN.FinCatN (m + d)) (FinCatN.TrivialFCN (m + d)))
S-embed^d zero    m rewrite +-identityʳ m = id
S-embed^d (suc d) m rewrite +-suc m d =
  let open TowerShapeFunctors (m + d) using (S-embed)
  in S-embed ∘F S-embed^d d m

-- Iterated embedCosmos: FinCatN m → FinCatN (m + d) at the cosmos level
-- embedCosmos 的 d 次迭代：宇宙层面 FinCatN m → FinCatN (m + d)
embedCosmos^d : ∀ d m
  → Cosmos (FinCatN.FinCatN m) (FinCatN.TrivialFCN m)
  → Cosmos (FinCatN.FinCatN (m + d)) (FinCatN.TrivialFCN (m + d))
embedCosmos^d zero    m x rewrite +-identityʳ m = x
embedCosmos^d (suc d) m x rewrite +-suc m d =
  FinCatTowerCompat.embedCosmos (m + d) (embedCosmos^d d m x)

-- Congruence of the one-step embedding on endofunctions. Split the
-- reading of the stage-(suc m) element by ≤-or->: on the inject₁ image
-- use embedF-inject₁ and the pointwise equality; at the new top both
-- embeddings fix the element by embedF-newtop. Total clamp throughout.
--
-- 一步嵌入对端函数的同余。按 ≤-or-> 拆分层 (suc m) 元素的读数：在
-- inject₁ 像上用 embedF-inject₁ 与逐点相等；新末位处两个嵌入都由
-- embedF-newtop 固定该元素。全程使用全函数 clamp。
private
  embedF₀ = FinCatTowerCompat.embedF₀

  embedF₀-cong : ∀ m (f g : Fin (n-at m) → Fin (n-at m))
    → (∀ (A : Fin (n-at m)) → f A ≡ g A)
    → (A' : Fin (n-at (suc m)))
    → embedF₀ m f A' ≡ embedF₀ m g A'
  embedF₀-cong m f g feq A' with ≤-or-> (suc m) (toℕ A')
  -- In range: A' is the inject₁ image of its clamp predecessor p.
  -- 范围内：A' 是其 clamp 前驱 p 的 inject₁ 像。
  ... | inj₁ le =
      let p = cl m (toℕ A')
          A'≡inj : A' ≡ inject₁ p
          A'≡inj = toℕ-injective
                     (trans (sym (cl-toℕ m (toℕ A') le))
                            (sym (toℕ-inject₁ p)))
      in begin
        embedF₀ m f A'
          ≡⟨ cong (embedF₀ m f) A'≡inj ⟩
        embedF₀ m f (inject₁ p)
          ≡⟨ embedF-inject₁ {m = m} f p ⟩
        inject₁ (f p)
          ≡⟨ cong inject₁ (feq p) ⟩
        inject₁ (g p)
          ≡˘⟨ embedF-inject₁ {m = m} g p ⟩
        embedF₀ m g (inject₁ p)
          ≡˘⟨ cong (embedF₀ m g) A'≡inj ⟩
        embedF₀ m g A'
      ∎
  -- New top: toℕ A' is forced to n-at m, and embedF fixes it on both sides.
  -- 新末位：toℕ A' 被迫等于 n-at m，两侧嵌入都固定它。
  ... | inj₂ gt =
      let etop : toℕ A' ≡ n-at m
          etop = ≤-antisym (≤-pred (toℕ<n A')) gt
          t = cl (suc m) (n-at m)
          t-e : toℕ t ≡ n-at m
          t-e = cl-toℕ (suc m) (n-at m) ≤-refl
          A'≡t : A' ≡ t
          A'≡t = toℕ-injective (trans etop (sym t-e))
          ffix : embedF₀ m f A' ≡ A'
          ffix = trans
                   (trans (cong (embedF₀ m f) A'≡t)
                          (embedF-newtop {m = m} f t t-e))
                   (sym A'≡t)
          gfix : embedF₀ m g A' ≡ A'
          gfix = trans
                   (trans (cong (embedF₀ m g) A'≡t)
                          (embedF-newtop {m = m} g t t-e))
                   (sym A'≡t)
      in trans ffix (sym gfix)

-- embedCosmos preserves _≈C_. The F₀ field is embedF₀-cong; the successor
-- follows the total clamp predecessor cl m (toℕ A') (no restrictFin).
--
-- embedCosmos 保持 _≈C_。F₀ 字段为 embedF₀-cong；后继跟随全函数 clamp
-- 前驱 cl m (toℕ A')（无 restrictFin）。
embedCosmos-resp-≈C : ∀ m {x y}
  → x ≈C y
  → FinCatTowerCompat.embedCosmos m x ≈C FinCatTowerCompat.embedCosmos m y
embedCosmos-resp-≈C m {x} {y} eq .unfoldFunctor₀-eq {A = A'} _ =
  embedF₀-cong m fx fy
    (λ A₁ → eq .unfoldFunctor₀-eq {A = A₁} (lift tt))
    A'
  where
    fx fy : Fin (n-at m) → Fin (n-at m)
    fx A₁ = Functor.F₀ (Unfolding.unfoldFunctor (out x)) (A₁ , lift tt)
    fy A₁ = Functor.F₀ (Unfolding.unfoldFunctor (out y)) (A₁ , lift tt)
embedCosmos-resp-≈C m eq .pos-to-shape-eq _ _ = refl
embedCosmos-resp-≈C m {x} {y} eq .unfold-next-eq {A = A'} _ =
  embedCosmos-resp-≈C m
    (eq .unfold-next-eq {A = cl m (toℕ A')} (lift tt))

-- Iterated compatibility: seq of subtower at layer m+d is the
-- embedCosmos^d image of its value at layer m
-- 迭代相容性：subtower 在第 m+d 层的 seq 是其第 m 层值的 embedCosmos^d 像
subtower-compat-iter : ∀ tower k m d
  → CompatibleTower.seq (subtower tower k) (m + d)
    ≈C embedCosmos^d d m (CompatibleTower.seq (subtower tower k) m)
subtower-compat-iter tower k m zero    rewrite +-identityʳ m = ≈C-refl
subtower-compat-iter tower k m (suc d) rewrite +-suc m d =
  ≈C-trans
    (CompatibleTower.compat (subtower tower k) (m + d))
    (embedCosmos-resp-≈C (m + d) (subtower-compat-iter tower k m d))

-- embedCosmos^d as a cross-category morphism along S-embed^d
-- embedCosmos^d 作为沿 S-embed^d 的跨范畴态射
embedCosmos^d-morphism : ∀ d m (x : Cosmos (FinCatN.FinCatN m) (FinCatN.TrivialFCN m))
  → x ⇒ℱX[ S-embed^d d m ] embedCosmos^d d m x
embedCosmos^d-morphism zero    m x rewrite +-identityʳ m = id⇒ℱX
embedCosmos^d-morphism (suc d) m x rewrite +-suc m d =
  comp⇒ℱX
    (EmbedCosmosMorphism.embedCosmos-morphism (m + d) (embedCosmos^d d m x))
    (embedCosmos^d-morphism d m x)

-- Composition of a cross-category morphism along id on the left,
-- with a morphism along an arbitrary shape functor on the right
-- 左复合：沿 id 的跨范畴态射与沿任意形状函子的跨范畴态射的复合
comp⇒ℱX-id-left : ∀
  {o h e o′ ℓ′ e′ s p}
  {C : Category o h e} {D : Category o′ ℓ′ e′}
  {FC : Functor C (ContCat s p)} {FD : Functor D (ContCat s p)}
  {S : Functor (ShapeCat C FC) (ShapeCat D FD)}
  {F : Cosmos C FC} {G H : Cosmos D FD}
  → G ⇒ℱX[ id ] H → F ⇒ℱX[ S ] G → F ⇒ℱX[ S ] H
comp⇒ℱX-id-left {S = S} {F = F} {G = G} {H = H} g f .out = record
  { shapeTrans    = λ {A} {s} p →
      ⇒ℱXLayer[_].shapeTrans gLayer
        (MorphismObject.onPos (⇒ℱXLayer[_].morphismObj fLayer) p)
  ; morphismObj   = record
    { onPos      = MorphismObject.onPos moComp
    ; pts-compat = MorphismObject.pts-compat moComp
    }
  ; morphismMor   = record
    { onActP = MorphismMorphism.onActP mmComp
    }
  ; onunfold-next = λ {A} s′ →
      let A′  = proj₁ (Sf.₀ (A , s′))
          s″ = proj₂ (Sf.₀ (A , s′))
      in  comp⇒ℱX-id-left
            (⇒ℱXLayer[_].onunfold-next gLayer {A = A′} s″)
            (⇒ℱXLayer[_].onunfold-next fLayer s′)
  }
  where
    open MorphismObject
    open MorphismMorphism
    module Sf = Functor S
    UF = out F
    UG = out G
    UH = out H
    fLayer = _⇒ℱX[_]_.out f
    gLayer = _⇒ℱX[_]_.out g
    stF = ⇒ℱXLayer[_].shapeTrans fLayer
    stG = ⇒ℱXLayer[_].shapeTrans gLayer
    moF = ⇒ℱXLayer[_].morphismObj fLayer
    moG = ⇒ℱXLayer[_].morphismObj gLayer
    mmF = ⇒ℱXLayer[_].morphismMor fLayer
    mmG = ⇒ℱXLayer[_].morphismMor gLayer
    moComp = compMorphismObject UF UG UH S id stF stG moF moG
    mmComp = compMorphismMorphism UF UG UH S id stF stG mmF mmG

-- Lift a subtower's layer-m value to layer m+d along S-embed^d
-- 沿 S-embed^d 将 subtower 的第 m 层值提升到第 m+d 层
lift-subtower : ∀ tower k m d
  → CompatibleTower.seq (subtower tower k) m
    ⇒ℱX[ S-embed^d d m ] CompatibleTower.seq (subtower tower k) (m + d)
lift-subtower tower k m d =
  comp⇒ℱX-id-left
    (⇒ℱ→⇒ℱX[id] (≈C→⇒ℱ (≈C-sym (subtower-compat-iter tower k m d))))
    (embedCosmos^d-morphism d m (CompatibleTower.seq (subtower tower k) m))

-- First component of F₀ (S-embed^d d m) is inject₁^d d
-- F₀ (S-embed^d d m) 的第一分量是 inject₁^d d
S-embed^d-F₀-proj₁ : ∀ d m (A : Fin (n-at m))
    (s : ShapeOf (FinCatN.TrivialFCN m) A)
  → Functor.F₀ (S-embed^d d m) (A , s) .proj₁ ≡ inject₁^d d A
S-embed^d-F₀-proj₁ zero    m A s rewrite +-identityʳ m = refl
S-embed^d-F₀-proj₁ (suc d) m A s rewrite +-suc m d =
  cong inject₁ (S-embed^d-F₀-proj₁ d m A s)

-- Transport a cross-category morphism along S-proj (m+d) ∘ S-embed^d d m
-- to one along S-proj m. The two projected successor indices are equal as
-- natural numbers (toℕ (inject₁^d d A) ≡ toℕ A), so a plain rewrite aligns
-- the target cosmos without any subst.
--
-- 将沿 S-proj (m+d) ∘ S-embed^d d m 的跨范畴态射传输为沿 S-proj m 的
-- 跨范畴态射。两个投影后继索引作为自然数相等
-- （toℕ (inject₁^d d A) ≡ toℕ A），故一次普通 rewrite 即可对齐目标
-- 宇宙，无需任何 subst。
transport-to-S-proj : ∀ {m : ℕ} {d : ℕ}
    {F : Cosmos (FinCatN.FinCatN m) (FinCatN.TrivialFCN m)}
    {G : Cosmos FinCat∞ TrivialFC∞}
  → F ⇒ℱX[ TowerShapeFunctors.S-proj (m + d) ∘F S-embed^d d m ] G
  → F ⇒ℱX[ TowerShapeFunctors.S-proj m ] G
transport-to-S-proj {m} {d} {F} {G} h .out .shapeTrans {A} _ = lift tt
transport-to-S-proj {m} {d} {F} {G} h .out .morphismObj .onPos {A} _ = lift tt
transport-to-S-proj {m} {d} {F} {G} h .out .morphismObj .pts-compat {A} _ = refl
transport-to-S-proj {m} {d} {F} {G} h .out .morphismMor .onActP {A} {B} _ _ _ = refl
transport-to-S-proj {m} {d} {F} {G} h .out .onunfold-next {A} s
  rewrite sym
    (begin
      toℕ (Functor.F₀ (S-embed^d d m) (A , s) .proj₁)
        ≡⟨ cong toℕ (S-embed^d-F₀-proj₁ d m A s) ⟩
      toℕ (inject₁^d d A)
        ≡⟨ toℕ-inject₁^d d {m = m} A ⟩
      toℕ A
    ∎) =
  transport-to-S-proj {m = m} {d = d} (h .out .onunfold-next {A = A} s)

-- defaultFin preserves toℕ when k is in range. The total clamp cl
-- satisfies this directly by cl-toℕ (n-at m ∸ 1 = suc m).
--
-- 当 k 在范围内时 defaultFin 保持 toℕ。全函数 clamp cl 由 cl-toℕ
-- 直接满足（n-at m ∸ 1 = suc m）。
toℕ-defaultFin : ∀ m k → k ≤ n-at m ∸ 1 → toℕ (defaultFin m k) ≡ k
toℕ-defaultFin m k k≤ = cl-toℕ m k k≤

mutual
  -- Cross-category morphism equivalence: a coinductive bisimulation
  -- comparing shapeTrans, onPos, and onunfold-next
  -- 跨范畴态射等价：余归纳互模拟，比较 shapeTrans、onPos 与 onunfold-next
  record _≈⇒ℱX_ {o h e o′ h′ e′ s p}
    {C : Category o h e} {D : Category o′ h′ e′}
    {FC : Functor C (ContCat s p)} {FD : Functor D (ContCat s p)}
    {S : Functor (ShapeCat C FC) (ShapeCat D FD)}
    {x : Cosmos C FC} {y : Cosmos D FD}
    (f g : x ⇒ℱX[ S ] y)
    : Set (o ⊔ h ⊔ e ⊔ o′ ⊔ h′ ⊔ e′ ⊔ s ⊔ p) where
    coinductive
    field
      out : ≈⇒ℱXLayer f g

  -- One-layer content of the equivalence
  -- 等价的单层内容
  record ≈⇒ℱXLayer {o h e o′ h′ e′ s p}
    {C : Category o h e} {D : Category o′ h′ e′}
    {FC : Functor C (ContCat s p)} {FD : Functor D (ContCat s p)}
    {S : Functor (ShapeCat C FC) (ShapeCat D FD)}
    {x : Cosmos C FC} {y : Cosmos D FD}
    (f g : x ⇒ℱX[ S ] y)
    : Set (o ⊔ h ⊔ e ⊔ o′ ⊔ h′ ⊔ e′ ⊔ s ⊔ p) where
    inductive
    field
      shapeTrans-eq : ∀ {A} {s : ShapeOf FC A} (p : PosOf FC s)
                    → ⇒ℱXLayer[_].shapeTrans (f .out) p
                    ≡ ⇒ℱXLayer[_].shapeTrans (g .out) p
      onPos-eq : ∀ {A} {s : ShapeOf FC A} (p : PosOf FC s)
               → MorphismObject.onPos (⇒ℱXLayer[_].morphismObj (f .out)) p
               ≡ MorphismObject.onPos (⇒ℱXLayer[_].morphismObj (g .out)) p
      onunfold-next-eq : ∀ {A} (s : ShapeOf FC A)
                       → f .out .onunfold-next {A = A} s
                         ≈⇒ℱX g .out .onunfold-next {A = A} s

open _≈⇒ℱX_ public
open ≈⇒ℱXLayer public

-- Specialisation of _≈⇒ℱX_ to FinCat∞ with S = id
-- _≈⇒ℱX_ 在 FinCat∞ 上、S = id 的特化
_≈⇒ℱX[id]_ : ∀ {x y : Cosmos FinCat∞ TrivialFC∞}
            → (f g : x ⇒ℱX[ id ] y) → Set
_≈⇒ℱX[id]_ = _≈⇒ℱX_ {C = FinCat∞} {D = FinCat∞}
                     {FC = TrivialFC∞} {FD = TrivialFC∞} {S = id}

-- Reflexivity of _≈⇒ℱX_
-- _≈⇒ℱX_ 的自反性
≈⇒ℱX-refl : ∀ {o h e o′ h′ e′ s p}
  {C : Category o h e} {D : Category o′ h′ e′}
  {FC : Functor C (ContCat s p)} {FD : Functor D (ContCat s p)}
  {S : Functor (ShapeCat C FC) (ShapeCat D FD)}
  {x : Cosmos C FC} {y : Cosmos D FD}
  {f : x ⇒ℱX[ S ] y} → f ≈⇒ℱX f
≈⇒ℱX-refl .out .shapeTrans-eq _ = refl
≈⇒ℱX-refl .out .onPos-eq _ = refl
≈⇒ℱX-refl .out .onunfold-next-eq s = ≈⇒ℱX-refl

-- Symmetry of _≈⇒ℱX_
-- _≈⇒ℱX_ 的对称性
≈⇒ℱX-sym : ∀ {o h e o′ h′ e′ s p}
  {C : Category o h e} {D : Category o′ h′ e′}
  {FC : Functor C (ContCat s p)} {FD : Functor D (ContCat s p)}
  {S : Functor (ShapeCat C FC) (ShapeCat D FD)}
  {x : Cosmos C FC} {y : Cosmos D FD}
  {f g : x ⇒ℱX[ S ] y} → f ≈⇒ℱX g → g ≈⇒ℱX f
≈⇒ℱX-sym p .out .shapeTrans-eq q = sym (p .out .shapeTrans-eq q)
≈⇒ℱX-sym p .out .onPos-eq q = sym (p .out .onPos-eq q)
≈⇒ℱX-sym p .out .onunfold-next-eq s = ≈⇒ℱX-sym (p .out .onunfold-next-eq s)

-- Transitivity of _≈⇒ℱX_
-- _≈⇒ℱX_ 的传递性
≈⇒ℱX-trans : ∀ {o h e o′ h′ e′ s p}
  {C : Category o h e} {D : Category o′ h′ e′}
  {FC : Functor C (ContCat s p)} {FD : Functor D (ContCat s p)}
  {S : Functor (ShapeCat C FC) (ShapeCat D FD)}
  {x : Cosmos C FC} {y : Cosmos D FD}
  {f g h : x ⇒ℱX[ S ] y}
  → f ≈⇒ℱX g → g ≈⇒ℱX h → f ≈⇒ℱX h
≈⇒ℱX-trans p q .out .shapeTrans-eq r =
  trans (p .out .shapeTrans-eq r) (q .out .shapeTrans-eq r)
≈⇒ℱX-trans p q .out .onPos-eq r =
  trans (p .out .onPos-eq r) (q .out .onPos-eq r)
≈⇒ℱX-trans p q .out .onunfold-next-eq s =
  ≈⇒ℱX-trans (p .out .onunfold-next-eq s) (q .out .onunfold-next-eq s)

-- Propositional equality implies _≈⇒ℱX_
-- 命题相等蕴含 _≈⇒ℱX_
≡-to-≈⇒ℱX : ∀ {o h e o′ h′ e′ s p}
  {C : Category o h e} {D : Category o′ h′ e′}
  {FC : Functor C (ContCat s p)} {FD : Functor D (ContCat s p)}
  {S : Functor (ShapeCat C FC) (ShapeCat D FD)}
  {x : Cosmos C FC} {y : Cosmos D FD}
  {f g : x ⇒ℱX[ S ] y} → f ≡ g → f ≈⇒ℱX g
≡-to-≈⇒ℱX refl = ≈⇒ℱX-refl

-- Congruence of composition with respect to _≈⇒ℱX_
-- 复合关于 _≈⇒ℱX_ 的同余性
comp⇒ℱX-cong-≈⇒ℱX :
  ∀ {o₁ h₁ e₁ o₂ h₂ e₂ o₃ h₃ e₃ s p}
    {C : Category o₁ h₁ e₁} {D : Category o₂ h₂ e₂} {E : Category o₃ h₃ e₃}
    {FC : Functor C (ContCat s p)} {FD : Functor D (ContCat s p)}
    {FE : Functor E (ContCat s p)}
    {S₁ : Functor (ShapeCat C FC) (ShapeCat D FD)}
    {S₂ : Functor (ShapeCat D FD) (ShapeCat E FE)}
    {F : Cosmos C FC} {G : Cosmos D FD} {H : Cosmos E FE}
    {f f′ : F ⇒ℱX[ S₁ ] G} {g g′ : G ⇒ℱX[ S₂ ] H}
  → f ≈⇒ℱX f′ → g ≈⇒ℱX g′
  → comp⇒ℱX g f ≈⇒ℱX comp⇒ℱX g′ f′
comp⇒ℱX-cong-≈⇒ℱX
  {S₁ = S₁} {S₂ = S₂}
  {f = f} {f′ = f′} {g = g} {g′ = g′} eqf eqg = result
  where
    result : comp⇒ℱX g f ≈⇒ℱX comp⇒ℱX g′ f′
    result .out .shapeTrans-eq {A} {s} p =
      begin
        ⇒ℱXLayer[_].shapeTrans (g .out)
          (MorphismObject.onPos (⇒ℱXLayer[_].morphismObj (f .out)) p)
          ≡⟨ cong (λ q → ⇒ℱXLayer[_].shapeTrans (g .out) q)
                  (eqf .out .onPos-eq {A} {s} p) ⟩
        ⇒ℱXLayer[_].shapeTrans (g .out)
          (MorphismObject.onPos (⇒ℱXLayer[_].morphismObj (f′ .out)) p)
          ≡⟨ eqg .out .shapeTrans-eq
              (MorphismObject.onPos (⇒ℱXLayer[_].morphismObj (f′ .out)) p) ⟩
        ⇒ℱXLayer[_].shapeTrans (g′ .out)
          (MorphismObject.onPos (⇒ℱXLayer[_].morphismObj (f′ .out)) p)
      ∎
    result .out .onPos-eq {A} {s} p =
      begin
        MorphismObject.onPos (⇒ℱXLayer[_].morphismObj (g .out))
          (MorphismObject.onPos (⇒ℱXLayer[_].morphismObj (f .out)) p)
          ≡⟨ cong (λ q → MorphismObject.onPos
                          (⇒ℱXLayer[_].morphismObj (g .out)) q)
                  (eqf .out .onPos-eq {A} {s} p) ⟩
        MorphismObject.onPos (⇒ℱXLayer[_].morphismObj (g .out))
          (MorphismObject.onPos (⇒ℱXLayer[_].morphismObj (f′ .out)) p)
          ≡⟨ eqg .out .onPos-eq
              (MorphismObject.onPos (⇒ℱXLayer[_].morphismObj (f′ .out)) p) ⟩
        MorphismObject.onPos (⇒ℱXLayer[_].morphismObj (g′ .out))
          (MorphismObject.onPos (⇒ℱXLayer[_].morphismObj (f′ .out)) p)
      ∎
    result .out .onunfold-next-eq {A} s =
      comp⇒ℱX-cong-≈⇒ℱX
        {S₁ = S₁} {S₂ = S₂}
        (eqf .out .onunfold-next-eq {A = A} s)
        (eqg .out .onunfold-next-eq
           {A = proj₁ (Functor.F₀ S₁ (A , s))}
           (proj₂ (Functor.F₀ S₁ (A , s))))

-- Left-unit law: composition with id⇒ℱX on the left is _≈⇒ℱX_-equivalent
-- to the original morphism
-- 左单位律：与 id⇒ℱX 的左复合 _≈⇒ℱX_-等价于原态射
left-id-law : ∀ {o h e o′ h′ e′ s p}
    {C : Category o h e} {D : Category o′ h′ e′}
    {FC : Functor C (ContCat s p)} {FD : Functor D (ContCat s p)}
    {S : Functor (ShapeCat C FC) (ShapeCat D FD)}
    {X : Cosmos C FC} {Y : Cosmos D FD}
  (f : X ⇒ℱX[ S ] Y)
  → comp⇒ℱX-id-left (id⇒ℱX {F = Y}) f ≈⇒ℱX f
left-id-law f .out .shapeTrans-eq {A} {s} p =
  sym (MorphismObject.pts-compat (⇒ℱXLayer[_].morphismObj (f .out))
        {A = A} {s = s} p)
left-id-law f .out .onPos-eq {A} {s} p = refl
left-id-law f .out .onunfold-next-eq {A} s =
  left-id-law (⇒ℱXLayer[_].onunfold-next (f .out) {A = A} s)

-- Consequence: id⇒ℱX satisfies the triangle equation at Y = towerColimit,
-- g = colimitCocone
-- 推论：id⇒ℱX 在 Y = towerColimit、g = colimitCocone 处满足三角等式
id-satisfies-h-tri : ∀ (tower : CompatibleTower) (m : ℕ)
  → comp⇒ℱX-id-left (id⇒ℱX {F = towerColimit tower})
                    (colimitCocone tower m)
    ≈⇒ℱX colimitCocone tower m
id-satisfies-h-tri tower m = left-id-law (colimitCocone tower m)
