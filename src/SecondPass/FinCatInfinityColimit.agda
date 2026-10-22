------------------------------------------------------------------------
-- Cross-category cosmos morphisms and colimit of a compatible tower
-- 跨范畴宇宙态射与相容塔的余极限
--
-- Defines the cross-category cosmos morphism _⇒ℱX[_]_, its identity and
-- composition, and the shape functors S-proj / S-embed associated with
-- the tower. Using these, projCosmos and embedCosmos are promoted to
-- cross-category morphisms. A compatible tower {x_m} satisfies
-- x_{suc m} ≈C embedCosmos m x_m; its colimit towerColimit satisfies
-- projCosmos m x_m ≈C towerColimit for all m, and is unique.
--
-- 定义跨范畴宇宙态射 _⇒ℱX[_]_ 及其恒等与复合，以及塔相关的形状函子
-- S-proj 与 S-embed。借助这些，projCosmos 与 embedCosmos 被提升为
-- 跨范畴态射。相容塔 {x_m} 满足 x_{suc m} ≈C embedCosmos m x_m；
-- 其余极限 towerColimit 满足对所有 m，projCosmos m x_m ≈C towerColimit，且唯一。
--
-- Zero-subst carried style: the partial finFromℕ-maybe / restrictFin
-- machine and every explicit Fin-index subst are deleted. The total clamp
-- representative cl (exact on the inject₁ image, top dummy beyond range)
-- supplies both the projection default and the embedding predecessor;
-- cross-stage agreement is cl-embed-default, and the only rewrites are
-- natural-number stage arithmetic (m + suc d = suc (m + d) is definitional,
-- m + (k ∸ m) = k by m+[n∸m]≡n). No subst, no cast, no Dec/Bool match.
-- 零 subst 携带式：删除偏函数 finFromℕ-maybe / restrictFin 机器及所有
-- 显式 Fin 索引 subst。全函数 clamp 代表 cl（inject₁ 像上精确、越界取
-- 末位哑元）同时提供投影默认值与嵌入前驱；跨层一致由 cl-embed-default
-- 给出，唯一的 rewrite 是自然数层算术（m + suc d = suc (m + d) 为定义性，
-- m + (k ∸ m) = k 由 m+[n∸m]≡n）。无 subst、无 cast、无 Dec/Bool 匹配。
------------------------------------------------------------------------
{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module SecondPass.FinCatInfinityColimit where

open import Agda.Primitive using (Level; _⊔_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Level using (lift)
open import Data.Unit.Polymorphic.Base using (tt)
open import Data.Nat using (ℕ; zero; suc; _+_; _∸_; _≤_; _<_)
open import Data.Nat.Properties
  using ( +-identityʳ; +-suc; m+[n∸m]≡n
        ; ≤-refl; ≤-trans; m≤n⇒m≤1+n )
open import Data.Fin.Base using (Fin; toℕ; inject₁)
open import Data.Fin.Properties using (toℕ-inject₁)
open import Data.Product.Base using (_,_; proj₁; proj₂)
open import Data.Sum.Base using (inj₁; inj₂)
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
open import SecondPass.MorphismObject
  using (MorphismObject; idMorphismObject; compMorphismObject)
open import SecondPass.MorphismMorphism
  using (MorphismMorphism; idMorphismMorphism; compMorphismMorphism)
open import SecondPass.Cosmos using (Cosmos; out)
open import SecondPass.Terminal using (_≈C_; ≈C-refl; ≈C-sym; ≈C-trans)
open _≈C_
open import SecondPass.FinCatNWitness using (module FinCatN)
open import SecondPass.FinCatInfinity using (FinCat∞; TrivialFC∞; n-at)
open import SecondPass.FinCatInfinityProjection
  using (module FinCatNColimitProjection)
open FinCatNColimitProjection
  using (extendFin; defaultFin; projCosmos; projCosmos-F₀-spec; cl-self)
open import SecondPass.FinCatInfinityTowerCompat using (module FinCatTowerCompat)
open import Cosmos.Carried.LimitSystem using (cl; ≤-or->)

-- Cross-category cosmos morphism _⇒ℱX[_]_
-- 跨范畴宇宙态射 _⇒ℱX[_]_

-- Coinductive record: a cross-category morphism from F to G along
-- shape functor S, whose layer contains shapeTrans, morphismObj,
-- morphismMor, and the recursive cross-category morphism on next seeds
-- 余归纳记录：沿形状函子 S 从 F 到 G 的跨范畴态射，其层包含
-- shapeTrans、morphismObj、morphismMor 及下一层种子上的递归跨范畴态射
mutual
  record _⇒ℱX[_]_
    {o h e o′ ℓ′ e′ s p : Level}
    {C : Category o h e} {D : Category o′ ℓ′ e′}
    {FC : Functor C (ContCat s p)} {FD : Functor D (ContCat s p)}
    (F : Cosmos C FC)
    (S : Functor (ShapeCat C FC) (ShapeCat D FD))
    (G : Cosmos D FD)
    : Set (o ⊔ h ⊔ e ⊔ o′ ⊔ ℓ′ ⊔ e′ ⊔ s ⊔ p) where
    coinductive
    field
      out : ⇒ℱXLayer[ S ] F G

  -- One-layer content of a cross-category morphism
  -- 跨范畴态射的单层内容
  record ⇒ℱXLayer[_]
    {o h e o′ ℓ′ e′ s p : Level}
    {C : Category o h e} {D : Category o′ ℓ′ e′}
    {FC : Functor C (ContCat s p)} {FD : Functor D (ContCat s p)}
    (S : Functor (ShapeCat C FC) (ShapeCat D FD))
    (F : Cosmos C FC) (G : Cosmos D FD)
    : Set (o ⊔ h ⊔ e ⊔ o′ ⊔ ℓ′ ⊔ e′ ⊔ s ⊔ p) where
    inductive
    private
      UF = out F
      UG = out G
      module Sf = Functor S
    field
      shapeTrans : ∀ {A} {s : ShapeOf FC A}
        → PosOf FC s
        → ShapeOf FD (Functor.₀ (Unfolding.unfoldFunctor UG) (Sf.₀ (A , s)))
      morphismObj : MorphismObject UF UG S shapeTrans
      morphismMor : MorphismMorphism UF UG S shapeTrans morphismObj
      onunfold-next : ∀ {A} (s : ShapeOf FC A)
        → Unfolding.unfold-next UF s ⇒ℱX[ S ]
          Unfolding.unfold-next UG (proj₂ (Sf.₀ (A , s)))

open _⇒ℱX[_]_ public
open ⇒ℱXLayer[_] public

-- Identity cross-category morphism along the identity shape functor
-- 沿恒等形状函子的恒等跨范畴态射
id⇒ℱX : ∀ {o h e s p} {C : Category o h e} {FC : Functor C (ContCat s p)}
  → {F : Cosmos C FC} → F ⇒ℱX[ id ] F
id⇒ℱX {F = F} .out = record
  { shapeTrans    = λ p → Unfolding.pos-to-shape UF _ p
  ; morphismObj   = idMorphismObject UF
  ; morphismMor   = idMorphismMorphism UF
  ; onunfold-next = λ _ → id⇒ℱX
  }
  where UF = out F

-- Composition of cross-category morphisms: S₂ ∘F S₁ as the composite
-- shape functor, with composite MorphismObject / MorphismMorphism and
-- recursive composition on next seeds
-- 跨范畴态射的复合：形状函子为 S₂ ∘F S₁，MorphismObject / MorphismMorphism
-- 取复合，下一层种子上的递归复合
comp⇒ℱX : ∀
  {o₁ h₁ e₁ o₂ h₂ e₂ o₃ h₃ e₃ s p}
  {C : Category o₁ h₁ e₁} {D : Category o₂ h₂ e₂} {E : Category o₃ h₃ e₃}
  {FC : Functor C (ContCat s p)} {FD : Functor D (ContCat s p)} {FE : Functor E (ContCat s p)}
  {S₁ : Functor (ShapeCat C FC) (ShapeCat D FD)}
  {S₂ : Functor (ShapeCat D FD) (ShapeCat E FE)}
  {F : Cosmos C FC} {G : Cosmos D FD} {H : Cosmos E FE}
  → G ⇒ℱX[ S₂ ] H → F ⇒ℱX[ S₁ ] G → F ⇒ℱX[ S₂ ∘F S₁ ] H
comp⇒ℱX {S₁ = S₁} {S₂ = S₂} {F = F} {G = G} {H = H} g f .out = record
  { shapeTrans    = λ p → shapeTrans (g .out) (MorphismObject.onPos moF p)
  ; morphismObj   = compMorphismObject UF UG UH S₁ S₂ stF stG moF moG
  ; morphismMor   = compMorphismMorphism UF UG UH S₁ S₂ stF stG mmF mmG
  ; onunfold-next = λ {A} s′ →
      let A′ = proj₁ (S₁.₀ (A , s′))
          s″ = proj₂ (S₁.₀ (A , s′))
      in  comp⇒ℱX (onunfold-next (g .out) {A = A′} s″)
                   (onunfold-next (f .out) s′)
  }
  where
    open MorphismObject
    module S₁ = Functor S₁
    UF  = out F; UG = out G; UH = out H
    stF = shapeTrans (f .out); stG = shapeTrans (g .out)
    moF = morphismObj (f .out); moG = morphismObj (g .out)
    mmF = morphismMor (f .out); mmG = morphismMor (g .out)

-- Shape functors for the tower
-- 塔族的形状函子
module TowerShapeFunctors (m : ℕ) where
  module M = FinCatN m
  module S = FinCatN (suc m)
  open M

  -- S-proj: shape functor from ShapeCat (FinCatN m) to ShapeCat FinCat∞,
  -- mapping objects by toℕ and morphisms to tt
  -- S-proj：从 ShapeCat (FinCatN m) 到 ShapeCat FinCat∞ 的形状函子，
  -- 对象经 toℕ 映射，态射映为 tt
  S-proj : Functor (ShapeCat M.FinCatN TrivialFCN) (ShapeCat FinCat∞ TrivialFC∞)
  S-proj = record
    { F₀           = λ { (A , _) → (toℕ A , lift tt) }
    ; F₁           = λ { (f , _) → (tt , refl) }
    ; identity     = refl
    ; homomorphism = refl
    ; F-resp-≈     = λ _ → refl
    }

  -- S-embed: shape functor from ShapeCat (FinCatN m) to
  -- ShapeCat (FinCatN (suc m)), mapping objects by inject₁ and
  -- morphisms to tt
  -- S-embed：从 ShapeCat (FinCatN m) 到 ShapeCat (FinCatN (suc m)) 的
  -- 形状函子，对象经 inject₁ 映射，态射映为 tt
  S-embed : Functor (ShapeCat M.FinCatN TrivialFCN) (ShapeCat S.FinCatN S.TrivialFCN)
  S-embed = record
    { F₀           = λ { (A , _) → (inject₁ A , lift tt) }
    ; F₁           = λ { (f , _) → (tt , refl) }
    ; identity     = refl
    ; homomorphism = refl
    ; F-resp-≈     = λ _ → refl
    }

-- projCosmos as cross-category morphism
-- projCosmos 作为跨范畴态射
module ProjCosmosMorphism (m : ℕ) where
  open TowerShapeFunctors m
  open FinCatN m
  module S-proj = Functor S-proj
  open MorphismObject
  open MorphismMorphism

  -- projCosmos m as a cross-category morphism along S-proj: shapeTrans,
  -- onPos, and onActP are trivially lift tt; onunfold-next recurses
  -- after the total clamp defaultFin (toℕ A) reduces to A (cl-self).
  -- projCosmos m 沿 S-proj 的跨范畴态射：shapeTrans、onPos、onActP
  -- 均为平凡的 lift tt；onunfold-next 在全函数 clamp 默认值
  -- defaultFin (toℕ A) 归约为 A（cl-self）后递归
  projCosmos-morphism : ∀ (x : Cosmos M.FinCatN TrivialFCN)
    → x ⇒ℱX[ S-proj ] projCosmos m x
  projCosmos-morphism x .out .shapeTrans {A} _ = lift tt
  projCosmos-morphism x .out .morphismObj .onPos {A} _ = lift tt
  projCosmos-morphism x .out .morphismObj .pts-compat {A} _ = refl
  projCosmos-morphism x .out .morphismMor .onActP {A} {B} _ _ _ = refl
  projCosmos-morphism x .out .onunfold-next {A} (lift tt)
    rewrite FinCatNColimitProjection.defaultFin-toℕ-self m A =
      projCosmos-morphism (UX.unfold-next {A = A} (lift tt))
    where
      UX = out x
      module UX = Unfolding UX

-- embedCosmos as cross-category morphism
-- embedCosmos 作为跨范畴态射
module EmbedCosmosMorphism (m : ℕ) where
  open TowerShapeFunctors m
  open FinCatTowerCompat m using (embedCosmos)
  open FinCatN m
  module S-embed = Functor S-embed

  -- The total clamp predecessor of an inject₁ image at stage suc m is the
  -- original stage-m element: cl m (toℕ (inject₁ A)) = cl m (toℕ A) = A.
  -- This replaces the old partial restrictFin left-inverse.
  --
  -- 层 suc m 上 inject₁ 像的全函数 clamp 前驱即原层 m 元素：
  -- cl m (toℕ (inject₁ A)) = cl m (toℕ A) = A。
  -- 这替代旧的偏函数 restrictFin 左逆。
  pred-inject₁ : ∀ (A : Fin M.n) → cl m (toℕ (inject₁ A)) ≡ A
  pred-inject₁ A rewrite toℕ-inject₁ A =
    FinCatNColimitProjection.cl-self m A

  -- embedCosmos m as a cross-category morphism along S-embed: shapeTrans,
  -- onPos, and onActP are trivially lift tt; onunfold-next recurses after
  -- the clamp predecessor of inject₁ A reduces to A.
  -- embedCosmos m 沿 S-embed 的跨范畴态射：shapeTrans、onPos、onActP
  -- 均为平凡的 lift tt；onunfold-next 在 inject₁ A 的 clamp 前驱归约
  -- 为 A 后递归
  embedCosmos-morphism : ∀ (x : Cosmos M.FinCatN M.TrivialFCN)
    → x ⇒ℱX[ S-embed ] embedCosmos x
  embedCosmos-morphism x .out = record
    { shapeTrans    = λ {A} _ → lift tt
    ; morphismObj   = record
        { onPos      = λ {A} _ → lift tt
        ; pts-compat = λ {A} _ → refl
        }
    ; morphismMor   = record
        { onActP = λ {A} {B} _ _ _ → refl
        }
    ; onunfold-next = onunfold
    }
    where
      UX = out x
      module UX = Unfolding UX

      onunfold : ∀ {A} (s : ShapeOf M.TrivialFCN A)
        → UX.unfold-next s ⇒ℱX[ S-embed ]
          Unfolding.unfold-next (out (embedCosmos x))
            {A = inject₁ A} (lift tt)
      onunfold {A} (lift tt)
        rewrite pred-inject₁ A
        = embedCosmos-morphism (UX.unfold-next {A = A} (lift tt))

-- Compatible tower and its colimit
-- 相容塔及其余极限

-- A compatible tower: a sequence of cosmoi indexed by ℕ, together with
-- the compatibility witness x_{suc m} ≈C embedCosmos m x_m
-- 相容塔：以 ℕ 为索引的宇宙序列，以及相容性见证
-- x_{suc m} ≈C embedCosmos m x_m
record CompatibleTower : Set₁ where
  field
    seq    : ∀ m → Cosmos (FinCatN.FinCatN m) (FinCatN.TrivialFCN m)
    compat : ∀ m → seq (suc m) ≈C FinCatTowerCompat.embedCosmos m (seq m)

open CompatibleTower

-- F₀ function of the m-th layer of the tower
-- 塔第 m 层的 F₀ 函数
private
  f-at : ∀ (tower : CompatibleTower) m → Fin (n-at m) → Fin (n-at m)
  f-at tower m A =
    Functor.F₀ (Unfolding.unfoldFunctor (out (seq tower m))) (A , lift tt)

  -- extendFin is invariant under pointwise equal functions. The total
  -- extendFin reads f on cl m k in range and is k beyond range.
  --
  -- extendFin 在逐点相等的函数下不变。全函数 extendFin 在范围内于
  -- cl m k 上读 f，越界恒为 k。
  extendFin-cong : ∀ m (f g : Fin (n-at m) → Fin (n-at m)) k
    → (∀ x → f x ≡ g x) → extendFin m f k ≡ extendFin m g k
  extendFin-cong m f g k feq with ≤-or-> (suc m) k
  ... | inj₁ _  = cong toℕ (feq (cl m k))
  ... | inj₂ _  = refl

  -- One-step compatibility of F₀ across the tower embedding
  -- 跨塔嵌入的 F₀ 一步相容性
  extendFin-step : ∀ (tower : CompatibleTower) m k
    → extendFin (suc m) (f-at tower (suc m)) k ≡ extendFin m (f-at tower m) k
  extendFin-step tower m k =
    begin
      extendFin (suc m) (f-at tower (suc m)) k
        ≡⟨ extendFin-cong (suc m) (f-at tower (suc m))
            (FinCatTowerCompat.embedF₀ m (f-at tower m)) k
            (λ A → compat tower m .unfoldFunctor₀-eq {A = A} (lift tt)) ⟩
      extendFin (suc m) (FinCatTowerCompat.embedF₀ m (f-at tower m)) k
        ≡⟨ FinCatTowerCompat.extendFin-embedF₀ m (f-at tower m) k ⟩
      extendFin m (f-at tower m) k
    ∎

  -- Iterated compatibility: extendFin at layer m+d equals extendFin at m.
  -- m + suc d reduces to suc (m + d) definitionally, so no +-suc subst.
  --
  -- 迭代相容性：层 m+d 的 extendFin 等于层 m 的 extendFin。
  -- m + suc d 定义性归约为 suc (m + d)，故无需 +-suc subst。
  extendFin-iter : ∀ (tower : CompatibleTower) m d k
    → extendFin (m + d) (f-at tower (m + d)) k ≡ extendFin m (f-at tower m) k
  extendFin-iter tower m zero k
    rewrite +-identityʳ m = refl
  extendFin-iter tower m (suc d) k rewrite +-suc m d =
    begin
      extendFin (suc (m + d)) (f-at tower (suc (m + d))) k
        ≡⟨ extendFin-step tower (m + d) k ⟩
      extendFin (m + d) (f-at tower (m + d)) k
        ≡⟨ extendFin-iter tower m d k ⟩
      extendFin m (f-at tower m) k
    ∎

  -- Layer independence: extendFin m (f-at m) k = extendFin k (f-at k) k.
  -- Structurally recursive strict dichotomy ≤-or-> (Cubical-safe); the
  -- only rewrite is the natural-number subtraction lemma.
  --
  -- 层独立性：extendFin m (f-at m) k = extendFin k (f-at k) k。
  -- 用结构化递归严格二分 ≤-or->（Cubical 安全）；唯一 rewrite 是
  -- 自然数减法引理。
  -- m < k branch: read the m-th leg as the k-th one via d = k ∸ m.
  -- m < k 分支：经 d = k ∸ m 把第 m 条腿读作第 k 条。
  layer-up : ∀ (tower : CompatibleTower) m k
    → (m<k : m < k)
    → extendFin m (f-at tower m) k ≡ extendFin k (f-at tower k) k
  layer-up tower m k m<k =
    trans (sym (extendFin-iter tower m (k ∸ m) k))
          (cong (λ j → extendFin j (f-at tower j) k)
                (m+[n∸m]≡n m≤k))
    where
      m≤k = ≤-trans (m≤n⇒m≤1+n (≤-refl {x = m})) m<k

  -- k ≤ m branch: read the k-th leg directly via d = m ∸ k.
  -- k ≤ m 分支：经 d = m ∸ k 直接读第 k 条腿。
  layer-down : ∀ (tower : CompatibleTower) m k
    → (k≤m : k ≤ m)
    → extendFin m (f-at tower m) k ≡ extendFin k (f-at tower k) k
  layer-down tower m k k≤m =
    trans (cong (λ j → extendFin j (f-at tower j) k)
                (sym (m+[n∸m]≡n k≤m)))
          (extendFin-iter tower k (m ∸ k) k)

  extendFin-layer-independent : ∀ (tower : CompatibleTower) m k
    → extendFin m (f-at tower m) k ≡ extendFin k (f-at tower k) k
  extendFin-layer-independent tower m k with ≤-or-> m k
  ... | inj₂ m<k = layer-up tower m k m<k
  ... | inj₁ k≤m = layer-down tower m k k≤m

-- Sub-tower at position k: replace each layer by its unfold-next at the
-- total clamp defaultFin k, with compatibility inherited from the
-- original tower. The embedding predecessor of the stage-(suc m) default
-- is the stage-m default by cl-embed-default (a plain congruence, no
-- subst).
-- 位置 k 处的子塔：将每层替换为其在全函数 clamp 默认值 defaultFin k
-- 处的 unfold-next，相容性继承自原塔。层 (suc m) 默认值的嵌入前驱由
-- cl-embed-default 等于层 m 默认值（纯同余，无 subst）。
subtower : CompatibleTower → ℕ → CompatibleTower
subtower tower k = record
  { seq    = λ m →
      Unfolding.unfold-next (out (seq tower m))
        {A = FinCatNColimitProjection.defaultFin m k} (lift tt)
  ; compat = subtower-compat tower k
  }
  where
    -- Compatibility of the sub-tower. The original witness c compares the
    -- two unfold-nexts at the stage-(suc m) default A0; the embedding's
    -- unfold-next at A0 is definitionally embedCosmos of the predecessor
    -- cl m (toℕ A0), which equals the stage-m default A1 by
    -- cl-embed-default. Congruence of embedCosmos closes the gap.
    --
    -- 子塔的相容性。原见证 c 在层 (suc m) 默认值 A0 处比较两个
    -- unfold-next；嵌入在 A0 处的 unfold-next 定义性等于前驱
    -- cl m (toℕ A0) 上的 embedCosmos，而该前驱由 cl-embed-default
    -- 等于层 m 默认值 A1。embedCosmos 的同余闭合此差距。
    subtower-compat : ∀ tower k m
      → Unfolding.unfold-next (out (seq tower (suc m)))
          {A = FinCatNColimitProjection.defaultFin (suc m) k} (lift tt)
        ≈C FinCatTowerCompat.embedCosmos m
              (Unfolding.unfold-next (out (seq tower m))
                {A = FinCatNColimitProjection.defaultFin m k} (lift tt))
    subtower-compat tower k m = ≈C-trans step resp
      where
        open FinCatTowerCompat m using (embedCosmos; cl-embed-default)

        c : seq tower (suc m) ≈C embedCosmos (seq tower m)
        c = compat tower m

        A0 = FinCatNColimitProjection.defaultFin (suc m) k
        A1 = FinCatNColimitProjection.defaultFin m k

        step
          : Unfolding.unfold-next (out (seq tower (suc m)))
              {A = A0} (lift tt)
            ≈C Unfolding.unfold-next (out (embedCosmos (seq tower m)))
                  {A = A0} (lift tt)
        step = c .unfold-next-eq {A = A0} (lift tt)

        -- The embedding's successor at A0 is embedCosmos of the stage-m
        -- successor at cl m (toℕ A0) = defaultFin m k.
        --
        -- 嵌入在 A0 处的后继即 cl m (toℕ A0) = defaultFin m k 处层 m
        -- 后继的 embedCosmos。
        goal
          : Unfolding.unfold-next (out (embedCosmos (seq tower m)))
              {A = A0} (lift tt)
          ≡ embedCosmos
              (Unfolding.unfold-next (out (seq tower m))
                {A = A1} (lift tt))
        goal =
          cong (λ B → embedCosmos
                   (Unfolding.unfold-next (out (seq tower m))
                     {A = B} (lift tt)))
               (cl-embed-default k)

        -- Propositional equality of the two successors gives a
        -- bisimulation by reflexivity transported along goal.
        --
        -- 两个后继的命题相等经自反性沿 goal 传输给出互模拟。
        resp
          : Unfolding.unfold-next (out (embedCosmos (seq tower m)))
              {A = A0} (lift tt)
            ≈C embedCosmos
                (Unfolding.unfold-next (out (seq tower m))
                  {A = A1} (lift tt))
        resp rewrite goal = ≈C-refl

-- Colimit of a compatible tower: coinductive construction whose F₀ at
-- layer k reads projCosmos k (seq k) at k, and whose unfold-next is
-- the colimit of the sub-tower at k
-- 相容塔的余极限：余归纳构造，其 F₀ 在第 k 层读取 projCosmos k (seq k) 在 k 处，
-- 其 unfold-next 是位置 k 处子塔的余极限
towerColimit : CompatibleTower → Cosmos FinCat∞ TrivialFC∞
towerColimit tower .out = record
  { unfoldFunctor = record
    { F₀           = λ { (k , _) →
        Functor.₀ (Unfolding.unfoldFunctor (out (projCosmos k (seq tower k)))) (k , lift tt) }
    ; F₁           = λ _ → tt
    ; identity     = refl
    ; homomorphism = refl
    ; F-resp-≈     = λ _ → refl
    }
  ; unfold-next     = λ { {k} _ → towerColimit (subtower tower k) }
  ; pos-to-shape    = λ _ _ → lift tt
  ; pos-actS-compat = λ _ _ _ → refl
  }

-- Specification: projCosmos m (seq tower m) ≈C towerColimit tower
-- Proof by coinduction; the F₀ field uses layer independence
-- 规范：projCosmos m (seq tower m) ≈C towerColimit tower
-- 证明经余归纳；F₀ 字段使用层独立性
towerColimit-spec : ∀ (tower : CompatibleTower) m
  → projCosmos m (seq tower m) ≈C towerColimit tower
towerColimit-spec tower m = go
  where
    go : projCosmos m (seq tower m) ≈C towerColimit tower
    go .unfoldFunctor₀-eq {A = k} (lift tt) =
      begin
        Functor.₀ (Unfolding.unfoldFunctor
                    (out (projCosmos m (seq tower m)))) (k , lift tt)
          ≡⟨ projCosmos-F₀-spec m (seq tower m) k ⟩
        extendFin m (f-at tower m) k
          ≡⟨ extendFin-layer-independent tower m k ⟩
        extendFin k (f-at tower k) k
          ≡˘⟨ projCosmos-F₀-spec k (seq tower k) k ⟩
        Functor.₀ (Unfolding.unfoldFunctor
                    (out (projCosmos k (seq tower k)))) (k , lift tt)
      ∎
    go .pos-to-shape-eq _ _ = refl
    go .unfold-next-eq {A = k} (lift tt) =
      towerColimit-spec (subtower tower k) m

-- Uniqueness: any z satisfying projCosmos m (seq tower m) ≈C z for all m
-- is bisimilar to towerColimit tower; it suffices to use m = 0
-- 唯一性：任意满足对所有 m，projCosmos m (seq tower m) ≈C z 的 z
-- 与 towerColimit tower 互模拟；只需取 m = 0
towerColimit-unique : ∀ (tower : CompatibleTower) (z : Cosmos FinCat∞ TrivialFC∞)
  → (∀ m → projCosmos m (seq tower m) ≈C z)
  → z ≈C towerColimit tower
towerColimit-unique tower z spec =
  ≈C-trans (≈C-sym (spec zero)) (towerColimit-spec tower zero)
