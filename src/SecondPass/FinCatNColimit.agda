------------------------------------------------------------------------
-- Dependent embedding and LimitLayer for the FinCat n tower
--
-- Provides dep-F₀, dep-F₁, dep-embed, the LimitLayer with
-- layer∞ = nLayer, the LimitCompatible proof, the layer lifting map
-- dep-liftAt with its resp/step lemmas, and the conditional framework
-- WithSurjectivity (parameterised by R, fams, embed-eq, surj)
-- The parameter m encodes n = suc (suc m), so n ≥ 2 holds definitionally.
--
-- FinCat n 塔的依赖嵌入与极限层
--
-- 提供 dep-F₀、dep-F₁、dep-embed、layer∞ = nLayer 的 LimitLayer、
-- LimitCompatible 证明、层提升映射 dep-liftAt 及其 resp/step 引理，
-- 以及条件性框架 WithSurjectivity（以 R、fams、embed-eq、surj 为参数）
-- 参数 m 编码 n = suc (suc m)，使 n ≥ 2 定义性成立。
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module SecondPass.FinCatNColimit where

open import Agda.Primitive using (lzero)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Sigma using (Σ; _,_)
open import Level using (lift)
open import Relation.Binary.PropositionalEquality.Core using (sym; cong; subst)
open import Relation.Binary.PropositionalEquality.Properties using (module ≡-Reasoning)
open ≡-Reasoning
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit.Polymorphic.Base using (tt)
open import Data.Product.Base using (proj₁; proj₂)

open import Categories.Category.Core using (Category)
open import Categories.Functor.Core using (Functor)
open import Categories.NaturalTransformation.Core using (ntHelper)

open import Cosmos.ContCategoryLemmas using (ShapeOf; PosOf; actPOf; actSOf)
open import Cosmos.ContCatEquiv using (ShapeCat)
open import SecondPass.Unfolding using (Unfolding)
open import SecondPass.Cosmos using (Cosmos; out)
open import SecondPass.Terminal using (_≈C_; ≈C-refl; ≈C-sym; ≈C-trans)
open import SecondPass.CumulativeHierarchy using (EmbeddingData)
open import SecondPass.StrictLift using (StrictLayer; EmbeddingRule; EmbedFamily)
open import SecondPass.CumulativeHierarchyLimit
  using (Tower; LimitLayer; LimitCompatible; EnrichedTower)
open import SecondPass.FinCatNWitness
open import SecondPass.FinCatNTowerLemmas
open import SecondPass.ConditionalNontrivialLimit
  using (Cocone; UniversalLimit; NontrivialLimit)

------------------------------------------------------------------------
-- Parameterised construction over FinCatN m
-- FinCatN m 上的参数化构造
------------------------------------------------------------------------

module FinCatNColimit (m : ℕ) where

  open FinCatN m
  open FinCatNTowerLemmas m

  -- Position inhabitants and singletons for tower layers
  -- Every shape at every layer of nTower has a position, and any two
  -- positions at the same shape are propositionally equal
  -- 塔层的位置居民与单点性
  -- nTower 的每一层、每个形状都有位置；同一形状上的任意两个位置命题相等
  pos-inhabited-tower
    : ∀ k (A : Category.Obj (StrictLayer.C (Tower.layer nTower k)))
    → (s : ShapeOf (StrictLayer.FC (Tower.layer nTower k)) A)
    → PosOf (StrictLayer.FC (Tower.layer nTower k)) {A = A} s
  pos-inhabited-tower zero    A         (lift tt) = lift tt
  pos-inhabited-tower (suc k) (A , _)   (lift u)  = lift (pos-inhabited-tower k A u)

  -- Any two positions at the same shape of the k-th layer are equal
  -- 第 k 层同一形状上的任意两个位置相等
  pos-singleton-tower
    : ∀ k (A : Category.Obj (StrictLayer.C (Tower.layer nTower k)))
    → (s : ShapeOf (StrictLayer.FC (Tower.layer nTower k)) A)
    → (p q : PosOf (StrictLayer.FC (Tower.layer nTower k)) {A = A} s) → p ≡ q
  pos-singleton-tower zero    A         (lift tt) (lift tt) (lift tt) = refl
  pos-singleton-tower (suc k) (A , _)   (lift u)  (lift p)  (lift q) =
    cong lift (pos-singleton-tower k A u p q)

  -- The pair (embed-obj (suc k) A, embed-shape (suc k) (embed-obj (suc k) A))
  -- as a single object of the (suc k)-th layer's ShapeCat
  -- 把 (embed-obj (suc k) A, embed-shape (suc k) (embed-obj (suc k) A)) 作为
  -- 第 (suc k) 层 ShapeCat 的单个对象
  private
    embed-pair
      : (k : ℕ) (A : Category.Obj FinCatN)
      → Σ (Category.Obj (StrictLayer.C (Tower.layer nTower (suc k))))
          (λ X → ShapeOf (StrictLayer.FC (Tower.layer nTower (suc k))) X)
    embed-pair k A =
      embed-obj (suc k) A , embed-shape (suc k) (embed-obj (suc k) A)

  -- Dependent unfoldFunctor and dependent embedding
  -- dep-F₀, dep-F₁, dep-unfoldFunctor, dep-embed: F₀ depends on the input
  -- cosmos x, using pos-inhabited-tower to supply a position for
  -- x's pos-to-shape
  -- 依赖展开函子与依赖嵌入
  -- dep-F₀、dep-F₁、dep-unfoldFunctor、dep-embed：F₀ 依赖输入宇宙 x，
  -- 用 pos-inhabited-tower 为 x 的 pos-to-shape 提供位置
  dep-F₀
    : ∀ k (x : Cosmos (StrictLayer.C (Tower.layer nTower k))
                       (StrictLayer.FC (Tower.layer nTower k)))
    → Category.Obj (ShapeCat
        (StrictLayer.C (Tower.layer nTower (suc k)))
        (StrictLayer.FC (Tower.layer nTower (suc k))))
    → Category.Obj (StrictLayer.C (Tower.layer nTower (suc k)))
  dep-F₀ k x z =
    ( Unfolding.unfoldFunctor (out x) .Functor.F₀ (proj₁ z)
    , Unfolding.pos-to-shape (out x)
        {A = proj₁ (proj₁ z)} (proj₂ (proj₁ z))
        (pos-inhabited-tower k (proj₁ (proj₁ z)) (proj₂ (proj₁ z))) )

  -- Dependent F₁: applies x.F₁ on the first component; the second
  -- component is the shape-level proof, completed via pos-actS-compat
  -- and pos-singleton-tower
  -- 依赖 F₁：第一分量施加 x.F₁；第二分量是形状层证明，经
  -- pos-actS-compat 与 pos-singleton-tower 补全
  dep-F₁
    : ∀ k (x : Cosmos (StrictLayer.C (Tower.layer nTower k))
                       (StrictLayer.FC (Tower.layer nTower k)))
    → {u v : Category.Obj (ShapeCat
        (StrictLayer.C (Tower.layer nTower (suc k)))
        (StrictLayer.FC (Tower.layer nTower (suc k))))}
    → Category._⇒_ (ShapeCat
        (StrictLayer.C (Tower.layer nTower (suc k)))
        (StrictLayer.FC (Tower.layer nTower (suc k)))) u v
    → Category._⇒_ (StrictLayer.C (Tower.layer nTower (suc k)))
        (dep-F₀ k x u) (dep-F₀ k x v)
  dep-F₁ k x {u} {v} f = (F₁-part , eq-part)
    where
      Cₖ  = StrictLayer.C (Tower.layer nTower k)
      FCₖ = StrictLayer.FC (Tower.layer nTower k)
      UXF = Unfolding.unfoldFunctor (out x)

      uA = proj₁ u
      vA = proj₁ v
      A  = proj₁ uA
      s  = proj₂ uA
      B  = proj₁ vA
      t  = proj₂ vA
      g  = proj₁ (proj₁ f)
      q  = proj₂ (proj₁ f)

      F₁-part : Category._⇒_ Cₖ (Functor.₀ UXF uA) (Functor.₀ UXF vA)
      F₁-part = UXF .Functor.F₁ (proj₁ f)

      posAtA : PosOf FCₖ s → ShapeOf FCₖ (Functor.₀ UXF uA)
      posAtA = Unfolding.pos-to-shape (out x) {A = A} s

      posAtB : PosOf FCₖ t → ShapeOf FCₖ (Functor.₀ UXF vA)
      posAtB = Unfolding.pos-to-shape (out x) {A = B} t

      p' = pos-inhabited-tower k B (actSOf FCₖ g s)

      a1 : posAtB (subst (PosOf FCₖ) q p')
         ≡ actSOf FCₖ F₁-part (posAtA (actPOf FCₖ g s p'))
      a1 = Unfolding.pos-actS-compat (out x)
             {A = A} {B = B} {s = s} {t = t} g q p'

      a2 : actPOf FCₖ g s p' ≡ pos-inhabited-tower k A s
      a2 = pos-singleton-tower k A s
             (actPOf FCₖ g s p') (pos-inhabited-tower k A s)
      a3 : subst (PosOf FCₖ) q p' ≡ pos-inhabited-tower k B t
      a3 = pos-singleton-tower k B t
             (subst (PosOf FCₖ) q p') (pos-inhabited-tower k B t)

      eq-part : actSOf FCₖ F₁-part (posAtA (pos-inhabited-tower k A s))
              ≡ posAtB (pos-inhabited-tower k B t)
      eq-part = begin
        actSOf FCₖ F₁-part (posAtA (pos-inhabited-tower k A s))
          ≡⟨ cong (actSOf FCₖ F₁-part) (sym (cong posAtA a2)) ⟩
        actSOf FCₖ F₁-part (posAtA (actPOf FCₖ g s p'))
          ≡⟨ sym a1 ⟩
        posAtB (subst (PosOf FCₖ) q p')
          ≡⟨ cong posAtB a3 ⟩
        posAtB (pos-inhabited-tower k B t)
        ∎

  -- The dependent unfold functor assembling dep-F₀ and dep-F₁
  -- 组装 dep-F₀ 与 dep-F₁ 的依赖展开函子
  dep-unfoldFunctor
    : ∀ k (x : Cosmos (StrictLayer.C (Tower.layer nTower k))
                       (StrictLayer.FC (Tower.layer nTower k)))
    → Functor (ShapeCat
        (StrictLayer.C (Tower.layer nTower (suc k)))
        (StrictLayer.FC (Tower.layer nTower (suc k))))
        (StrictLayer.C (Tower.layer nTower (suc k)))
  dep-unfoldFunctor k x = record
    { F₀           = dep-F₀ k x
    ; F₁           = dep-F₁ k x
    ; identity     = Unfolding.unfoldFunctor (out x) .Functor.identity
    ; homomorphism = Unfolding.unfoldFunctor (out x) .Functor.homomorphism
    ; F-resp-≈     = λ f≈g → Unfolding.unfoldFunctor (out x) .Functor.F-resp-≈ f≈g
    }

  -- The dependent strict embedding of the k-th layer into the (suc k)-th
  -- 将第 k 层依赖严格嵌入到第 suc k 层
  dep-embed
    : ∀ k (x : Cosmos (StrictLayer.C (Tower.layer nTower k))
                       (StrictLayer.FC (Tower.layer nTower k)))
    → EmbeddingData x
    → Cosmos (StrictLayer.C (Tower.layer nTower (suc k)))
             (StrictLayer.FC (Tower.layer nTower (suc k)))
  dep-embed k x ed .out = record
    { unfoldFunctor = dep-unfoldFunctor k x
    ; unfold-next = λ { {A} s →
        dep-embed k
          (Unfolding.unfold-next (out x) {A = proj₁ A} (proj₂ A))
          (EmbeddingData.next ed {A = proj₁ A} (proj₂ A)) }
    ; pos-to-shape = λ { {A} _ _ →
        lift (Unfolding.pos-to-shape (out x) {A = proj₁ A} (proj₂ A)
                (pos-inhabited-tower k (proj₁ A) (proj₂ A))) }
    ; pos-actS-compat = λ { {A} {B} {s} {t} f eq p →
        let
          FC' = StrictLayer.FC (Tower.layer nTower (suc k))
          UF  = dep-unfoldFunctor k x
          lhs = lift (Unfolding.pos-to-shape (out x) {A = proj₁ B} (proj₂ B)
                         (pos-inhabited-tower k (proj₁ B) (proj₂ B)))
          rhs = actSOf FC' (UF .Functor.F₁ (f , eq))
                  (lift (Unfolding.pos-to-shape (out x) {A = proj₁ A} (proj₂ A)
                             (pos-inhabited-tower k (proj₁ A) (proj₂ A))))
          C₀  = UF .Functor.F₀ (B , t)
        in shape-singleton-at (suc k) C₀ lhs rhs }
    }

  -- Colimit layer for the FinCat n tower: layer∞ = nLayer (FinCatN with
  -- TrivialFCN), projC k .F₀ = proj-obj k, projC k .F₁ = λ _ → tt.
  -- Type-correctness of F₁ = tt follows from FinCatN's hom-set being ⊤;
  -- faithfulness holds because every tower layer's hom-set is ⊤ up to
  -- propositional equality, so F₁ is a bijection on hom-sets.
  -- LimitCompatible is trivial: both sides of proj-step-coh are constant
  -- on hom-sets, so the natural isomorphism is the identity
  -- 塔的余极限层：layer∞ = nLayer（FinCatN 配 TrivialFCN），
  -- projC k .F₀ = proj-obj k，projC k .F₁ = λ _ → tt。
  -- F₁ = tt 的类型正确性源于 FinCatN 的 hom 集为 ⊤；忠实性成立是因为
  -- 每层塔的 hom 集在命题相等下为 ⊤，故 F₁ 在 hom 集上是双射。
  -- LimitCompatible 平凡：proj-step-coh 两边在 hom 集上均为常值，
  -- 自然同构即为恒等
  colimitLayer : LimitLayer nIdx nTower
  colimitLayer = record
    { o∞ = lzero ; h∞ = lzero ; e∞ = lzero ; s∞ = lzero ; p∞ = lzero
    ; layer∞ = nLayer
    ; projC = λ k → record
        { F₀           = proj-obj k
        ; F₁           = λ _ → tt
        ; identity     = refl
        ; homomorphism = refl
        ; F-resp-≈     = λ _ → refl
        }
    }

  -- Compatibility: projC (suc k) ≅ projC k ∘F π; both sides are
  -- constant on hom-sets, so the natural isomorphism is trivial
  -- 相容性：projC (suc k) ≅ projC k ∘F π；两边在 hom 集上均为常值，
  -- 自然同构平凡
  colimitLayer-compatible : LimitCompatible colimitLayer
  colimitLayer-compatible = record
    { proj-step-coh = λ k → record
        { F⇒G  = ntHelper record { η = λ _ → tt ; commute = λ _ → refl }
        ; F⇐G  = ntHelper record { η = λ _ → tt ; commute = λ _ → refl }
        ; iso  = λ _ → record { isoˡ = refl ; isoʳ = refl }
        }
    }

  -- Layer lifting map dep-liftAt and its lemmas
  -- dep-liftAt 0 = id; dep-liftAt (suc k) projects F₀ via proj-obj and
  -- recurses on unfold-next. dep-liftAt-resp preserves _≈C_;
  -- dep-liftAt-step witnesses dep-liftAt (suc k) ∘ dep-embed k ≈C dep-liftAt k
  -- 层提升映射 dep-liftAt 及其引理
  -- dep-liftAt 0 = id；dep-liftAt (suc k) 经 proj-obj 投影 F₀ 并在
  -- unfold-next 上递归。dep-liftAt-resp 保持 _≈C_；
  -- dep-liftAt-step 见证 dep-liftAt (suc k) ∘ dep-embed k ≈C dep-liftAt k
  dep-liftAt
    : ∀ k → Cosmos (StrictLayer.C (Tower.layer nTower k))
                    (StrictLayer.FC (Tower.layer nTower k))
          → Cosmos FinCatN TrivialFCN
  dep-liftAt zero    x = x
  dep-liftAt (suc k) x .out = record
    { unfoldFunctor = record
        { F₀ = λ { (A , _) →
            proj-obj (suc k)
              (Unfolding.unfoldFunctor (out x) .Functor.F₀ (embed-pair k A)) }
        ; F₁ = λ _ → tt
        ; identity = refl ; homomorphism = refl ; F-resp-≈ = λ _ → refl }
    ; unfold-next = λ { {A = A} _ →
        let p = embed-pair k A
        in dep-liftAt (suc k)
             (Unfolding.unfold-next (out x) {A = proj₁ p} (proj₂ p)) }
    ; pos-to-shape    = λ _ _ → lift tt
    ; pos-actS-compat = λ _ _ _ → refl
    }

  -- dep-liftAt preserves _≈C_
  -- dep-liftAt 保持 _≈C_
  dep-liftAt-resp
    : ∀ k {x y : Cosmos (StrictLayer.C (Tower.layer nTower k))
                         (StrictLayer.FC (Tower.layer nTower k))}
    → x ≈C y → dep-liftAt k x ≈C dep-liftAt k y
  dep-liftAt-resp zero    p = p
  dep-liftAt-resp (suc k) p ._≈C_.unfoldFunctor₀-eq {A} s =
    let q = embed-pair k A
    in cong (proj-obj (suc k))
         (p ._≈C_.unfoldFunctor₀-eq {A = proj₁ q} (proj₂ q))
  dep-liftAt-resp (suc k) p ._≈C_.pos-to-shape-eq s q = refl
  dep-liftAt-resp (suc k) p ._≈C_.unfold-next-eq {A} s =
    let q = embed-pair k A
    in dep-liftAt-resp (suc k)
         (p ._≈C_.unfold-next-eq {A = proj₁ q} (proj₂ q))

  -- dep-liftAt-step: lifting after embedding equals lifting directly
  -- dep-liftAt-step：嵌入后再提升等于直接从上一层提升
  dep-liftAt-step
    : ∀ k
      (x : Cosmos (StrictLayer.C (Tower.layer nTower k))
                   (StrictLayer.FC (Tower.layer nTower k)))
      (ed : EmbeddingData x)
    → dep-liftAt (suc k) (dep-embed k x ed) ≈C dep-liftAt k x
  dep-liftAt-step zero x ed ._≈C_.unfoldFunctor₀-eq {A} s = refl
  dep-liftAt-step zero x ed ._≈C_.pos-to-shape-eq  s p = refl
  dep-liftAt-step zero x ed ._≈C_.unfold-next-eq  {A = A} s =
    dep-liftAt-step zero
      (Unfolding.unfold-next (out x) {A = A} s)
      (EmbeddingData.next ed {A = A} s)
  dep-liftAt-step (suc k) x ed ._≈C_.unfoldFunctor₀-eq {A} s = refl
  dep-liftAt-step (suc k) x ed ._≈C_.pos-to-shape-eq  s p = refl
  dep-liftAt-step (suc k) x ed ._≈C_.unfold-next-eq {A = A} s =
    let p = embed-pair k A
    in dep-liftAt-step (suc k)
         (Unfolding.unfold-next (out x) {A = proj₁ p} (proj₂ p))
         (EmbeddingData.next ed {A = proj₁ p} (proj₂ p))

  -- embed-eq is a genuine constraint: it does NOT hold for R = outer-rule
  -- (see FinCatNEmbeddingMismatch). For a rule-independent framework that
  -- uses dep-embed-tower directly, see FinCatNColimitWithDep
  -- embed-eq 是实质约束，对 R = outer-rule 不成立（见 FinCatNEmbeddingMismatch）
  -- 直接使用 dep-embed-tower 的规则无关框架见 FinCatNColimitWithDep
  module WithSurjectivity
    (R : EmbeddingRule)
    (fams : ∀ k → EmbedFamily R (Tower.layer nTower k))
    (embed-eq : ∀ k → EmbeddingRule.Embed R (Tower.layer nTower k) ≡ dep-embed k)
    (surj : ∀ k
            (x : Cosmos (StrictLayer.C (Tower.layer nTower (suc k)))
                         (StrictLayer.FC (Tower.layer nTower (suc k))))
          → Σ (Cosmos (StrictLayer.C (Tower.layer nTower k))
                       (StrictLayer.FC (Tower.layer nTower k)))
              (λ y → x ≈C EmbeddingRule.Embed R (Tower.layer nTower k) y
                       (EmbedFamily.getData (fams k) y))) where
    private
      ET : EnrichedTower R nIdx
      ET = record { tower = nTower ; fams = fams }

    -- liftAt-step expressed via Embed R, using embed-eq to reduce to
    -- dep-liftAt-step
    -- 用 Embed R 表达的 liftAt-step，经 embed-eq 归约为 dep-liftAt-step
    liftAt-step-R
      : ∀ k
        (x : Cosmos (StrictLayer.C (Tower.layer nTower k))
                     (StrictLayer.FC (Tower.layer nTower k)))
      → dep-liftAt (suc k)
          (EmbeddingRule.Embed R (Tower.layer nTower k) x
            (EmbedFamily.getData (fams k) x))
        ≈C dep-liftAt k x
    liftAt-step-R k x rewrite embed-eq k =
      dep-liftAt-step k x (EmbedFamily.getData (fams k) x)

    -- mediate-coh for dep-liftAt: map cone 0 ∘ dep-liftAt k ≈C map cone k,
    -- by induction on k using surj to recover the layer-k input
    -- dep-liftAt 的 mediate-coh：map cone 0 ∘ dep-liftAt k ≈C map cone k，
    -- 对 k 归纳，用 surj 恢复第 k 层输入
    dep-mediate-coh
      : ∀ {oD hD eD sD pD}
        {D : StrictLayer oD hD eD sD pD}
        (cone : Cocone ET D) (k : ℕ)
        (x : Cosmos (StrictLayer.C (Tower.layer nTower k))
                     (StrictLayer.FC (Tower.layer nTower k)))
      → _≈C_ {C = StrictLayer.C D} {FC = StrictLayer.FC D}
          (Cocone.map cone 0 (dep-liftAt k x))
          (Cocone.map cone k x)
    dep-mediate-coh cone zero    x = ≈C-refl
    dep-mediate-coh cone (suc k) x =
      let (y , p) = surj k x
          q1 = Cocone.map-resp cone 0 (dep-liftAt-resp (suc k) p)
          q2 = Cocone.map-resp cone 0 (liftAt-step-R k y)
          q3 = dep-mediate-coh cone k y
          q4 = ≈C-trans (≈C-sym (Cocone.step-compat cone k y))
                        (Cocone.map-resp cone (suc k) (≈C-sym p))
      in ≈C-trans q1 (≈C-trans q2 (≈C-trans q3 q4))

    -- The universal limit assembled from dep-liftAt, mediate = map cone 0
    -- 由 dep-liftAt 组装的通用极限，mediate = map cone 0
    dependentUniversalLimit : UniversalLimit ET
    dependentUniversalLimit = record
      { limit          = colimitLayer
      ; liftAt         = dep-liftAt
      ; liftAt-resp    = λ k {x} {y} → dep-liftAt-resp k
      ; liftAt-step    = λ k x → liftAt-step-R k x
      ; mediate        = λ D cone z → Cocone.map cone 0 z
      ; mediate-resp   = λ {D} cone {x} {y} eq → Cocone.map-resp cone 0 eq
      ; mediate-coh    = λ {D} cone k x → dep-mediate-coh cone k x
      ; mediate-unique = λ {D} cone g g-resp g-coh z → g-coh 0 z
      }

    -- liftAt 0 is the identity, hence injective
    -- liftAt 0 是恒等，故为单射
    lift0-inj
      : ∀ {x y : Cosmos FinCatN TrivialFCN}
      → _≈C_ {C = StrictLayer.C
                (LimitLayer.layer∞ (UniversalLimit.limit dependentUniversalLimit))}
             {FC = StrictLayer.FC
                (LimitLayer.layer∞ (UniversalLimit.limit dependentUniversalLimit))}
             (UniversalLimit.liftAt dependentUniversalLimit 0 x)
             (UniversalLimit.liftAt dependentUniversalLimit 0 y)
      → x ≈C y
    lift0-inj p = p

    -- Non-triviality witness: cosmos-idN and cosmos-const0N remain
    -- distinguishable after lifting at layer 0
    -- 非平凡见证：cosmos-idN 与 cosmos-const0N 在层 0 提升后仍可区分
    dependentNontrivial : NontrivialLimit dependentUniversalLimit
    dependentNontrivial = record
      { n    = 0
      ; x    = cosmos-idN
      ; y    = cosmos-const0N
      ; x≉y  = cosmos-idN≉cosmos-const0N
      }
