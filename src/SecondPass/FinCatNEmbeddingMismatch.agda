------------------------------------------------------------------------
-- Diagnostic: outer-rule ≠ dep-embed at every layer of the FinCat n tower
-- Also exposes a general mismatch skeleton (embed-mismatch-general):
-- strictEmbed and dep-embed-general differ whenever the input cosmos's
-- F₀ is non-trivial on some shape, as witnessed by a probe function
-- No downstream users; records why FinCatNColimit.WithSurjectivity's
-- `embed-eq` is unsatisfiable for R = outer-rule. The parameter m
-- encodes n = suc (suc m), so n ≥ 2 holds definitionally
-- 诊断：outer-rule 在 FinCat n 塔的每一层上 ≠ dep-embed
-- 同时暴露一般化不匹配骨架 embed-mismatch-general：
-- 当输入宇宙的 F₀ 在某形状上非平凡（由探针函数见证）时，
-- strictEmbed 与 dep-embed-general 不相等
-- 无下游使用方；记录 FinCatNColimit.WithSurjectivity 的 `embed-eq`
-- 在 R = outer-rule 下不可满足。参数 m 编码 n = suc (suc m)，
-- 使 n ≥ 2 定义性成立
------------------------------------------------------------------------
{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module SecondPass.FinCatNEmbeddingMismatch where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Sigma using (_,_)
open import Level using (lift)
open import Relation.Binary.PropositionalEquality.Core using (cong; sym; _≢_)
open import Relation.Binary.PropositionalEquality.Properties using (module ≡-Reasoning)
open ≡-Reasoning
open import Relation.Nullary using (¬_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit.Polymorphic.Base using (tt)
open import Data.Product.Base using (proj₁; proj₂)
open import Data.Fin.Base using (Fin) renaming (zero to fzero; suc to fsuc)

open import Categories.Category.Core using (Category)
open import Categories.Functor.Core using (Functor)

open import Cosmos.ContCategoryLemmas using (ShapeOf; PosOf; actSOf)
open import Cosmos.ContCatEquiv using (ShapeCat)
open import SecondPass.Unfolding using (Unfolding)
open import SecondPass.Cosmos using (Cosmos; out)
open import SecondPass.CumulativeHierarchy using (EmbeddingData; mkEmbeddingData)
open import SecondPass.StrictLift using
  (strictStep-suc; StrictLayer; EmbeddingRule; outer-rule; strictEmbed; strictEmbed-unfoldFunctor)
open import SecondPass.CumulativeHierarchyLimit using (Tower)
open import SecondPass.FinCatNWitness
open import SecondPass.FinCatNTowerLemmas
open import SecondPass.FinCatNColimit
open import SecondPass.DependentEmbedding
  using (dep-embed-general; dep-unfoldFunctor-general)

-- strictEmbed's F₀ first component is the source object, by definition
-- strictEmbed 的 F₀ 第一分量按定义为源对象
strictEmbed-F₀-first
  : ∀ {o h e s p} (L : StrictLayer o h e s p)
    (A : Category.Obj (StrictLayer.C L))
    (s : ShapeOf (StrictLayer.FC L) A)
    (u : ShapeOf (StrictLayer.FC (strictStep-suc L)) (A , s))
  → proj₁ (strictEmbed-unfoldFunctor L .Functor.F₀ ((A , s) , u))
  ≡ A
strictEmbed-F₀-first L A s u = refl

-- dep-embed-general's F₀ first component is x.F₀ applied to (A, s),
-- by definition
-- dep-embed-general 的 F₀ 第一分量按定义为 x.F₀ 作用于 (A, s)
dep-embed-general-F₀-first
  : ∀ {o h e s p} (L : StrictLayer o h e s p)
    (pos-inhab : ∀ {A : Category.Obj (StrictLayer.C L)}
                   (s : ShapeOf (StrictLayer.FC L) A)
               → PosOf (StrictLayer.FC L) {A = A} s)
    (pos-singleton : ∀ {A : Category.Obj (StrictLayer.C L)}
                       (s : ShapeOf (StrictLayer.FC L) A)
                   → (p q : PosOf (StrictLayer.FC L) {A = A} s) → p ≡ q)
    (shape-singleton : (A : Category.Obj (StrictLayer.C (strictStep-suc L)))
                     → (s t : ShapeOf (StrictLayer.FC (strictStep-suc L)) A)
                     → s ≡ t)
    (x : Cosmos (StrictLayer.C L) (StrictLayer.FC L))
    (ed : EmbeddingData x)
    (A : Category.Obj (StrictLayer.C L))
    (s : ShapeOf (StrictLayer.FC L) A)
    (u : ShapeOf (StrictLayer.FC (strictStep-suc L)) (A , s))
  → proj₁ (dep-unfoldFunctor-general L pos-inhab pos-singleton x
            .Functor.F₀ ((A , s) , u))
  ≡ Unfolding.unfoldFunctor (out x) .Functor.F₀ (A , s)
dep-embed-general-F₀-first L pos-inhab pos-singleton shape-singleton
                           x ed A s u = refl

-- General mismatch theorem: if some probe π distinguishes x.F₀ (A, s)
-- from A, then strictEmbed and dep-embed-general cannot be propositionally
-- equal on (x, ed)
-- 一般不匹配定理：若某探针 π 区分 x.F₀ (A, s) 与 A，
-- 则 strictEmbed 与 dep-embed-general 在 (x, ed) 上不可能命题相等
embed-mismatch-general
  : ∀ {o h e s p} (L : StrictLayer o h e s p)
    (pos-inhab : ∀ {A : Category.Obj (StrictLayer.C L)}
                   (s : ShapeOf (StrictLayer.FC L) A)
               → PosOf (StrictLayer.FC L) {A = A} s)
    (pos-singleton : ∀ {A : Category.Obj (StrictLayer.C L)}
                       (s : ShapeOf (StrictLayer.FC L) A)
                   → (p q : PosOf (StrictLayer.FC L) {A = A} s) → p ≡ q)
    (shape-singleton : (A : Category.Obj (StrictLayer.C (strictStep-suc L)))
                     → (s t : ShapeOf (StrictLayer.FC (strictStep-suc L)) A)
                     → s ≡ t)
    (x : Cosmos (StrictLayer.C L) (StrictLayer.FC L))
    (ed : EmbeddingData x)
    (A : Category.Obj (StrictLayer.C L))
    (s : ShapeOf (StrictLayer.FC L) A)
    (u : ShapeOf (StrictLayer.FC (strictStep-suc L)) (A , s))
    {Y : Set}
    (π : Category.Obj (StrictLayer.C L) → Y)
  → π (Unfolding.unfoldFunctor (out x) .Functor.F₀ (A , s))
    ≢ π A
  → strictEmbed L x ed
    ≢ dep-embed-general L pos-inhab pos-singleton
                        shape-singleton x ed
embed-mismatch-general L pos-inhab pos-singleton shape-singleton
                       x ed A s u {Y} π ineq eq =
  ineq (sym (cong {A = Cosmos (StrictLayer.C (strictStep-suc L))
                                (StrictLayer.FC (strictStep-suc L))}
                  {B = Y}
                  (λ c → π (proj₁ (Unfolding.unfoldFunctor (out c)
                                     .Functor.F₀ ((A , s) , u))))
                  eq))

-- FinCatN m instance: outer-rule ≠ dep-embed at every layer. The probe
-- is proj-obj k ∘ F₀ restricted to a witness shape, and the mismatch is
-- iterated over k by composing dep-embed
-- FinCatN m 实例：outer-rule 在每一层上 ≠ dep-embed。探针为
-- proj-obj k ∘ F₀ 限制在某见证形状上，不匹配性经复合 dep-embed 迭代到 k
module FinCatNEmbeddingMismatch (m : ℕ) where

  open FinCatN m
  open FinCatNTowerLemmas m
  open FinCatNColimit m

  -- EmbeddingData for cosmos-const0N
  -- cosmos-const0N 的 EmbeddingData
  ed-const0 : EmbeddingData cosmos-const0N
  ed-const0 = mkEmbeddingData
    (λ _ _ → tt)
    (λ _ _ → refl)
    cosmos-const0N

  -- Witness shape at layer 1
  -- 第 1 层的见证形状
  z : Category.Obj
        (ShapeCat (StrictLayer.C (strictStep-suc nLayer))
                  (StrictLayer.FC (strictStep-suc nLayer)))
  z = ((fsuc {n = suc m} (fzero {n = m}) , lift tt) , lift (lift tt))

  -- Layer-0 mismatch: transport the mismatch along an assumed pointwise equality
  -- 第 0 层不匹配：把不匹配性沿假设的逐点相等性传输
  apply-eq
    : EmbeddingRule.Embed outer-rule nLayer ≡ FinCatNColimit.dep-embed m 0
    → EmbeddingRule.Embed outer-rule nLayer cosmos-const0N ed-const0
      ≡ FinCatNColimit.dep-embed m 0 cosmos-const0N ed-const0
  apply-eq eq = cong (λ f → f cosmos-const0N ed-const0) eq

  -- The two unfoldFunctor.F₀ images at z coincide
  -- 两个 unfoldFunctor.F₀ 在 z 处重合
  eq-obj
    : (eq : EmbeddingRule.Embed outer-rule nLayer ≡ FinCatNColimit.dep-embed m 0)
    → Unfolding.unfoldFunctor
        (out (EmbeddingRule.Embed outer-rule nLayer cosmos-const0N ed-const0))
        .Functor.F₀ z
      ≡ Unfolding.unfoldFunctor
          (out (FinCatNColimit.dep-embed m 0 cosmos-const0N ed-const0))
          .Functor.F₀ z
  eq-obj eq = cong (λ c → Unfolding.unfoldFunctor (out c) .Functor.F₀ z)
                   (apply-eq eq)

  -- Their first components coincide
  -- 二者第一分量重合
  eq-first
    : (eq : EmbeddingRule.Embed outer-rule nLayer ≡ FinCatNColimit.dep-embed m 0)
    → proj₁ (Unfolding.unfoldFunctor
               (out (EmbeddingRule.Embed outer-rule nLayer cosmos-const0N ed-const0))
               .Functor.F₀ z)
      ≡ proj₁ (Unfolding.unfoldFunctor
                 (out (FinCatNColimit.dep-embed m 0 cosmos-const0N ed-const0))
                 .Functor.F₀ z)
  eq-first eq = cong proj₁ (eq-obj eq)

  -- Left first component evaluates to fsuc fzero
  -- 左侧第一分量求值为 fsuc fzero
  lhs-first
    : proj₁ (Unfolding.unfoldFunctor
               (out (EmbeddingRule.Embed outer-rule nLayer cosmos-const0N ed-const0))
               .Functor.F₀ z)
      ≡ fsuc {n = suc m} (fzero {n = m})
  lhs-first = refl

  -- Right first component evaluates to fzero
  -- 右侧第一分量求值为 fzero
  rhs-first
    : proj₁ (Unfolding.unfoldFunctor
               (out (FinCatNColimit.dep-embed m 0 cosmos-const0N ed-const0))
               .Functor.F₀ z)
      ≡ fzero
  rhs-first = refl

  -- Layer-0 mismatch: outer-rule is not pointwise equal to dep-embed at layer 0
  -- Chain: fsuc fzero ≡ (left first) ≡ (eq) ≡ (right first) ≡ fzero
  -- 第 0 层不匹配：outer-rule 在层 0 上不与 dep-embed 逐点相等
  -- 链：fsuc fzero ≡（左侧第一分量）≡（假设等式）≡（右侧第一分量）≡ fzero
  embed-eq-false-zero
      : ¬ (EmbeddingRule.Embed outer-rule nLayer ≡ FinCatNColimit.dep-embed m 0)
  embed-eq-false-zero eq =
    fsuc-fzero≠fzero (begin
      fsuc {n = suc m} (fzero {n = m})
        ≡˘⟨ lhs-first ⟩
      proj₁ (Unfolding.unfoldFunctor
               (out (EmbeddingRule.Embed outer-rule nLayer cosmos-const0N ed-const0))
               .Functor.F₀ z)
        ≡⟨ eq-first eq ⟩
      proj₁ (Unfolding.unfoldFunctor
               (out (FinCatNColimit.dep-embed m 0 cosmos-const0N ed-const0))
               .Functor.F₀ z)
        ≡⟨ rhs-first ⟩
      fzero
      ∎)

  -- Iterated construction, lifting the mismatch to all k
  -- EmbeddingData for dep-embed k y ed
  -- 迭代构造：把不匹配性提升到所有 k
  -- dep-embed k y ed 的 EmbeddingData
  ed-for : ∀ k
    (y  : Cosmos (StrictLayer.C (Tower.layer nTower k))
                (StrictLayer.FC (Tower.layer nTower k)))
    (ed : EmbeddingData y)
    → EmbeddingData (FinCatNColimit.dep-embed m k y ed)
  ed-for k y ed .EmbeddingData.retract {A} s =
    ( EmbeddingData.retract ed (proj₂ A)
    , shape-singleton-at k (proj₁ A)
        (actSOf (StrictLayer.FC (Tower.layer nTower k))
          (EmbeddingData.retract ed (proj₂ A))
          (Unfolding.pos-to-shape (out y) (proj₂ A)
              (pos-inhabited-tower k (proj₁ A) (proj₂ A))))
        (proj₂ A) )
  ed-for k y ed .EmbeddingData.retract-natural {A} {B} {s} {t} f eq =
    EmbeddingData.retract-natural ed (proj₁ f) (proj₂ f)
  ed-for k y ed .EmbeddingData.next {A} s =
    ed-for k
      (Unfolding.unfold-next (out y) {A = proj₁ A} (proj₂ A))
      (EmbeddingData.next ed {A = proj₁ A} (proj₂ A))

  -- Iterated const0 cosmos and its embedding data
  -- 迭代的 const0 宇宙及其嵌入数据
  mutual
    const0-k : ∀ k
      → Cosmos (StrictLayer.C (Tower.layer nTower k))
              (StrictLayer.FC (Tower.layer nTower k))
    const0-k zero    = cosmos-const0N
    const0-k (suc k) = FinCatNColimit.dep-embed m k (const0-k k) (ed-base k)

    ed-base : ∀ k → EmbeddingData (const0-k k)
    ed-base zero    = ed-const0
    ed-base (suc k) = ed-for k (const0-k k) (ed-base k)

  -- proj-obj is a left inverse of embed-obj
  -- proj-obj 是 embed-obj 的左逆
  proj-obj∘embed-obj : ∀ k (a : Fin n) → proj-obj k (embed-obj k a) ≡ a
  proj-obj∘embed-obj zero    a = refl
  proj-obj∘embed-obj (suc k) a = proj-obj∘embed-obj k a

  -- Left first component projects to fzero
  -- 左侧第一分量投影为 fzero
  fzero-lemma : ∀ k
    → proj-obj k
        (Unfolding.unfoldFunctor (out (const0-k k)) .Functor.F₀
          (embed-obj k (fsuc fzero), embed-shape k (embed-obj k (fsuc fzero))))
      ≡ fzero
  fzero-lemma zero    = refl
  fzero-lemma (suc k) = fzero-lemma k

  -- Right first component projects to fsuc fzero
  -- 右侧第一分量投影为 fsuc fzero
  fsuc-lemma : ∀ k
    → proj-obj k (proj₁ (embed-obj (suc k) (fsuc fzero))) ≡ fsuc fzero
  fsuc-lemma zero    = refl
  fsuc-lemma (suc k) =
    proj-obj∘embed-obj (suc k) (fsuc fzero)

  -- Mismatch at every layer: outer-rule ≠ dep-embed pointwise
  -- Chain: fsuc fzero ≡ (left) ≡ (eq) ≡ (right) ≡ fzero
  -- 每一层上的不匹配：outer-rule 与 dep-embed 不逐点相等
  -- 链：fsuc fzero ≡（左侧）≡（假设等式）≡（右侧）≡ fzero
  embed-eq-false
    : ∀ k
    → ¬ (EmbeddingRule.Embed outer-rule (Tower.layer nTower k)
         ≡ FinCatNColimit.dep-embed m k)
  embed-eq-false k eq =
    fsuc-fzero≠fzero (begin
      fsuc {n = suc m} (fzero {n = m})
        ≡˘⟨ left≡fsuc ⟩
      left-F₀
        ≡⟨ eq-F₀ ⟩
      right-F₀
        ≡⟨ right≡fzero ⟩
      fzero
      ∎)
    where
      x    = const0-k k
      ed-x = ed-base k
      z-k  = ( embed-obj (suc k) (fsuc fzero)
             , embed-shape (suc k) (embed-obj (suc k) (fsuc fzero)) )
      left  = strictEmbed (Tower.layer nTower k) x ed-x
      right = FinCatNColimit.dep-embed m k x ed-x
      left-F₀  = proj-obj k
                  (Unfolding.unfoldFunctor (out left)  .Functor.F₀ z-k .proj₁)
      right-F₀ = proj-obj k
                  (Unfolding.unfoldFunctor (out right) .Functor.F₀ z-k .proj₁)
      left≡fsuc  : left-F₀ ≡ fsuc fzero
      left≡fsuc = fsuc-lemma k
      right≡fzero : right-F₀ ≡ fzero
      right≡fzero = fzero-lemma k
      eq1   = cong (λ f → f x ed-x) eq
      eq-F₀ : left-F₀ ≡ right-F₀
      eq-F₀ = cong (λ c → proj-obj k
                    (Unfolding.unfoldFunctor (out c) .Functor.F₀ z-k .proj₁)) eq1
