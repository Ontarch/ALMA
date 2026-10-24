------------------------------------------------------------------------
-- Type class for dependent strict embeddings
--
-- Defines the type class DependentEmbeddingRule, whose EmbedDep field
-- captures the exact prerequisites of the dependent strict embedding
-- dep-embed: position inhabitants, position singletons, and shape
-- singletons of the next layer. The pointwise equality embed-eq becomes
-- definitional (refl) once dep-embed-general is registered as the
-- EmbedDep field of dep-rule
--
-- 依赖严格嵌入的类型类
--
-- 定义类型类 DependentEmbeddingRule，其 EmbedDep 字段精确刻画
-- 依赖严格嵌入 dep-embed 的前提条件：位置居民、位置单点性、
-- 以及下一层的形状单点性。一旦把 dep-embed-general 注册为
-- dep-rule 的 EmbedDep 字段，逐点等式 embed-eq 就成为定义性相等（refl）
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module SecondPass.DependentEmbedding where

open import Agda.Primitive using (lsuc; _⊔_; Setω)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Level using (lift)
open import Relation.Binary.PropositionalEquality.Core using (cong; sym; trans; subst)
open import Data.Product.Base using (_,_; proj₁; proj₂)

open import Categories.Category.Core using (Category)
open import Categories.Functor.Core using (Functor)

open import Cosmos.ContCategoryLemmas using (ShapeOf; PosOf; actSOf; actPOf)
open import Cosmos.ContCatEquiv using (ShapeCat)
open import SecondPass.Unfolding using (Unfolding)
open import SecondPass.Cosmos using (Cosmos; out)
open import SecondPass.CumulativeHierarchy using (EmbeddingData)
open import SecondPass.StrictLift using (StrictLayer; strictStep-suc)

-- Type class
-- 类型类
record DependentEmbeddingRule : Setω where
  field
    EmbedDep
      : ∀ {o h e s p} (L : StrictLayer o h e s p)
      → (pos-inhab : ∀ {A : Category.Obj (StrictLayer.C L)}
                       (s : ShapeOf (StrictLayer.FC L) A)
                   → PosOf (StrictLayer.FC L) {A = A} s)
      → (pos-singleton : ∀ {A : Category.Obj (StrictLayer.C L)}
                           (s : ShapeOf (StrictLayer.FC L) A)
                       → (p q : PosOf (StrictLayer.FC L) {A = A} s) → p ≡ q)
      → (shape-singleton : (A : Category.Obj (StrictLayer.C (strictStep-suc L)))
                         → (s t : ShapeOf (StrictLayer.FC (strictStep-suc L)) A)
                         → s ≡ t)
      → (x : Cosmos (StrictLayer.C L) (StrictLayer.FC L))
      → EmbeddingData x
      → Cosmos (StrictLayer.C (strictStep-suc L))
               (StrictLayer.FC (strictStep-suc L))

open DependentEmbeddingRule

-- Generalized dependent unfoldFunctor
-- 广义依赖展开函子
dep-F₀-general
  : ∀ {o h e s p} (L : StrictLayer o h e s p)
  → (pos-inhab : ∀ {A} (s : ShapeOf (StrictLayer.FC L) A)
               → PosOf (StrictLayer.FC L) {A = A} s)
  → (x : Cosmos (StrictLayer.C L) (StrictLayer.FC L))
  → Category.Obj (ShapeCat
      (StrictLayer.C (strictStep-suc L))
      (StrictLayer.FC (strictStep-suc L)))
  → Category.Obj (StrictLayer.C (strictStep-suc L))
dep-F₀-general L pos-inhab x z =
  ( Unfolding.unfoldFunctor (out x) .Functor.F₀ (proj₁ z)
  , Unfolding.pos-to-shape (out x)
      {A = proj₁ (proj₁ z)} (proj₂ (proj₁ z))
      (pos-inhab {A = proj₁ (proj₁ z)} (proj₂ (proj₁ z))) )

dep-F₁-general
  : ∀ {o h e s p} (L : StrictLayer o h e s p)
  → (pos-inhab : ∀ {A} (s : ShapeOf (StrictLayer.FC L) A)
               → PosOf (StrictLayer.FC L) {A = A} s)
  → (pos-singleton : ∀ {A} (s : ShapeOf (StrictLayer.FC L) A)
                   → (p q : PosOf (StrictLayer.FC L) {A = A} s) → p ≡ q)
  → (x : Cosmos (StrictLayer.C L) (StrictLayer.FC L))
  → {u v : Category.Obj (ShapeCat
      (StrictLayer.C (strictStep-suc L))
      (StrictLayer.FC (strictStep-suc L)))}
  → Category._⇒_ (ShapeCat
      (StrictLayer.C (strictStep-suc L))
      (StrictLayer.FC (strictStep-suc L))) u v
  → Category._⇒_ (StrictLayer.C (strictStep-suc L))
      (dep-F₀-general L pos-inhab x u) (dep-F₀-general L pos-inhab x v)
dep-F₁-general L pos-inhab pos-singleton x {u} {v} f =
  ( Unfolding.unfoldFunctor (out x) .Functor.F₁
      {A = proj₁ u} {B = proj₁ v} gShape
  , trans step1 (trans step2 step3) )
  where
    FC      = StrictLayer.FC L
    A       = proj₁ (proj₁ u)
    s       = proj₂ (proj₁ u)
    B       = proj₁ (proj₁ v)
    t       = proj₂ (proj₁ v)
    gShape  = proj₁ f
    g       = proj₁ gShape
    q       = proj₂ gShape
    p'      = pos-inhab {A = B} (actSOf FC g s)
    G       = Unfolding.unfoldFunctor (out x) .Functor.F₁
                {A = proj₁ u} {B = proj₁ v} gShape
    s'      = Unfolding.pos-to-shape (out x) {A = A} s (pos-inhab {A = A} s)
    t'      = Unfolding.pos-to-shape (out x) {A = B} t (pos-inhab {A = B} t)

    a1 : Unfolding.pos-to-shape (out x) {A = B} t (subst (PosOf FC) q p')
       ≡ actSOf FC G
           (Unfolding.pos-to-shape (out x) {A = A} s (actPOf FC g s p'))
    a1 = Unfolding.pos-actS-compat (out x)
           {A = A} {B = B} {s = s} {t = t} g q p'

    a2 : actPOf FC g s p' ≡ pos-inhab {A = A} s
    a2 = pos-singleton {A = A} s
           (actPOf FC g s p') (pos-inhab {A = A} s)

    a3 : subst (PosOf FC) q p' ≡ pos-inhab {A = B} t
    a3 = pos-singleton {A = B} t
           (subst (PosOf FC) q p') (pos-inhab {A = B} t)

    step1 : actSOf FC G s'
          ≡ actSOf FC G
              (Unfolding.pos-to-shape (out x) {A = A} s (actPOf FC g s p'))
    step1 = sym (cong
              (λ r → actSOf FC G
                       (Unfolding.pos-to-shape (out x) {A = A} s r))
              a2)

    step2 : actSOf FC G
              (Unfolding.pos-to-shape (out x) {A = A} s (actPOf FC g s p'))
          ≡ Unfolding.pos-to-shape (out x) {A = B} t (subst (PosOf FC) q p')
    step2 = sym a1

    step3 : Unfolding.pos-to-shape (out x) {A = B} t (subst (PosOf FC) q p')
          ≡ t'
    step3 = cong
              (λ r → Unfolding.pos-to-shape (out x) {A = B} t r)
              a3

dep-unfoldFunctor-general
  : ∀ {o h e s p} (L : StrictLayer o h e s p)
  → (pos-inhab : ∀ {A} (s : ShapeOf (StrictLayer.FC L) A)
               → PosOf (StrictLayer.FC L) {A = A} s)
  → (pos-singleton : ∀ {A} (s : ShapeOf (StrictLayer.FC L) A)
                   → (p q : PosOf (StrictLayer.FC L) {A = A} s) → p ≡ q)
  → (x : Cosmos (StrictLayer.C L) (StrictLayer.FC L))
  → Functor (ShapeCat
      (StrictLayer.C (strictStep-suc L))
      (StrictLayer.FC (strictStep-suc L)))
      (StrictLayer.C (strictStep-suc L))
dep-unfoldFunctor-general L pos-inhab pos-singleton x = record
  { F₀           = dep-F₀-general L pos-inhab x
  ; F₁           = dep-F₁-general L pos-inhab pos-singleton x
  ; identity     = Unfolding.unfoldFunctor (out x) .Functor.identity
  ; homomorphism = Unfolding.unfoldFunctor (out x) .Functor.homomorphism
  ; F-resp-≈     = λ f≈g →
      Unfolding.unfoldFunctor (out x) .Functor.F-resp-≈ f≈g
  }

-- The dependent embedding
-- 依赖嵌入
dep-embed-general
  : ∀ {o h e s p} (L : StrictLayer o h e s p)
  → (pos-inhab : ∀ {A} (s : ShapeOf (StrictLayer.FC L) A)
               → PosOf (StrictLayer.FC L) {A = A} s)
  → (pos-singleton : ∀ {A} (s : ShapeOf (StrictLayer.FC L) A)
                   → (p q : PosOf (StrictLayer.FC L) {A = A} s) → p ≡ q)
  → (shape-singleton : (A : Category.Obj (StrictLayer.C (strictStep-suc L)))
                     → (s t : ShapeOf (StrictLayer.FC (strictStep-suc L)) A)
                     → s ≡ t)
  → (x : Cosmos (StrictLayer.C L) (StrictLayer.FC L))
  → EmbeddingData x
  → Cosmos (StrictLayer.C (strictStep-suc L))
           (StrictLayer.FC (strictStep-suc L))
dep-embed-general {s = s} {p = p}
                  L pos-inhab pos-singleton shape-singleton x ed .out = record
  { unfoldFunctor = dep-unfoldFunctor-general L pos-inhab pos-singleton x
  ; unfold-next = λ { {A = A} _ →
      dep-embed-general L pos-inhab pos-singleton shape-singleton
        (Unfolding.unfold-next (out x) {A = proj₁ A} (proj₂ A))
        (EmbeddingData.next ed {A = proj₁ A} (proj₂ A)) }
  ; pos-to-shape = λ { {A = A} _ _ →
      lift {ℓ = lsuc (s ⊔ p)}
        (Unfolding.pos-to-shape (out x) {A = proj₁ A} (proj₂ A)
           (pos-inhab {A = proj₁ A} (proj₂ A))) }
  ; pos-actS-compat = λ { {A} {B} {s = sA} {t = tB} f eq pos →
      let
        FC' = StrictLayer.FC (strictStep-suc L)
        UF  = dep-unfoldFunctor-general L pos-inhab pos-singleton x
        C₀  = UF .Functor.F₀ (B , tB)

        lhs : ShapeOf FC' C₀
        lhs = lift {ℓ = lsuc (s ⊔ p)}
                (Unfolding.pos-to-shape (out x) {A = proj₁ B} (proj₂ B)
                   (pos-inhab {A = proj₁ B} (proj₂ B)))

        rhs : ShapeOf FC' C₀
        rhs = actSOf FC' (UF .Functor.F₁ (f , eq))
                (lift {ℓ = lsuc (s ⊔ p)}
                  (Unfolding.pos-to-shape (out x) {A = proj₁ A} (proj₂ A)
                     (pos-inhab {A = proj₁ A} (proj₂ A))))
      in shape-singleton C₀ lhs rhs }
  }

-- Instance registration and definitional embed-eq
-- 实例注册与定义性 embed-eq
dep-rule : DependentEmbeddingRule
dep-rule .EmbedDep = dep-embed-general

embed-eq-refl
  : ∀ {o h e s p} (L : StrictLayer o h e s p)
    (pos-inhab : ∀ {A} (s : ShapeOf (StrictLayer.FC L) A)
               → PosOf (StrictLayer.FC L) {A = A} s)
    (pos-singleton : ∀ {A} (s : ShapeOf (StrictLayer.FC L) A)
                   → (p q : PosOf (StrictLayer.FC L) {A = A} s) → p ≡ q)
    (shape-singleton : (A : Category.Obj (StrictLayer.C (strictStep-suc L)))
                     → (s t : ShapeOf (StrictLayer.FC (strictStep-suc L)) A)
                     → s ≡ t)
    (x : Cosmos (StrictLayer.C L) (StrictLayer.FC L))
    (ed : EmbeddingData x)
  → EmbedDep dep-rule L pos-inhab pos-singleton shape-singleton x ed
    ≡ dep-embed-general L pos-inhab pos-singleton shape-singleton x ed
embed-eq-refl L pos-inhab pos-singleton shape-singleton x ed = refl
