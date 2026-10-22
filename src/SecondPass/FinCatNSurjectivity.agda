------------------------------------------------------------------------
-- Surjectivity of the dependent embedding on the FinCat n tower
-- FinCat n 塔上依赖嵌入的满射性
--
-- Proves SurjectivityForTower for arbitrary uniform embedding families:
-- every cosmos at layer suc k arises, up to _≈C_, as dep-embed-tower k y
-- for some y at layer k. Uses only the tower's intrinsic structural facts
-- (shape-singleton-at, pos-inhabited-tower). The parameter m encodes
-- n = suc (suc m), so n ≥ 2 holds definitionally
-- 对任意一致嵌入族证明 SurjectivityForTower：第 suc k 层的任意宇宙都
-- 在 _≈C_ 意义下等于某第 k 层宇宙 y 的 dep-embed-tower k y 像。
-- 仅使用塔的固有结构事实（shape-singleton-at、pos-inhabited-tower）。
-- 参数 m 编码 n = suc (suc m)，使 n ≥ 2 定义性成立
------------------------------------------------------------------------
{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module SecondPass.FinCatNSurjectivity where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Sigma using (Σ; _,_)
open import Level using (Lift; lift; lower)
open import Relation.Binary.PropositionalEquality.Core using (cong; subst)
open import Relation.Binary.PropositionalEquality.Properties using (module ≡-Reasoning)
open ≡-Reasoning
open import Data.Nat using (ℕ; suc)
open import Data.Product.Base using (proj₁; proj₂)

open import Categories.Category.Core using (Category)
open import Categories.Functor.Core using (Functor)

open import Cosmos.ContCategoryLemmas using (ShapeOf; PosOf; actSOf)
open import Cosmos.ContCatEquiv using (ShapeCat)
open import SecondPass.Unfolding using (Unfolding; unfold-next)
open import SecondPass.Cosmos using (Cosmos; out)
open import SecondPass.Terminal using (_≈C_)
open import SecondPass.CumulativeHierarchy using (EmbeddingData; UniformEmbeddingFamily)
open import SecondPass.StrictLift using (StrictLayer)
open import SecondPass.CumulativeHierarchyLimit using (Tower)
open import SecondPass.FinCatNWitness
open import SecondPass.FinCatNTowerLemmas
open import SecondPass.FinCatNColimit
open import SecondPass.FinCatNColimitWithDep

------------------------------------------------------------------------
-- Parameterised construction over FinCatN m
-- FinCatN m 上的参数化构造
------------------------------------------------------------------------

module FinCatNSurjectivity (m : ℕ) where

  open FinCatN m
  open FinCatNTowerLemmas m
  open FinCatNColimit m
  open FinCatNColimitWithDep m
    using (SurjectivityForTower; UniformEmbeddingFamilyForTower; dep-embed-tower)

  -- Inverse cosmos: read x.F₀ and x.F₁ componentwise at the diagonal lift
  -- of ((A, s), s); the choice of lift s is immaterial by shape singleton
  -- 逆宇宙：在对角提升 ((A, s), s) 处逐分量读取 x.F₀ 与 x.F₁；
  -- 由形状单点性，lift s 的选择无关紧要
  y-F₀ : ∀ k
    (x : Cosmos (StrictLayer.C (Tower.layer nTower (suc k)))
                (StrictLayer.FC (Tower.layer nTower (suc k))))
    (A : Category.Obj (StrictLayer.C (Tower.layer nTower k)))
    (s : ShapeOf (StrictLayer.FC (Tower.layer nTower k)) A)
    → Category.Obj (StrictLayer.C (Tower.layer nTower k))
  y-F₀ k x A s =
    proj₁ (Unfolding.unfoldFunctor (out x) .Functor.F₀ ((A , s) , lift s))

  y-F₁ : ∀ k
    (x : Cosmos (StrictLayer.C (Tower.layer nTower (suc k)))
                (StrictLayer.FC (Tower.layer nTower (suc k))))
    {A B : Category.Obj (StrictLayer.C (Tower.layer nTower k))}
    {s : ShapeOf (StrictLayer.FC (Tower.layer nTower k)) A}
    {t : ShapeOf (StrictLayer.FC (Tower.layer nTower k)) B}
    (f : Category._⇒_ (StrictLayer.C (Tower.layer nTower k)) A B)
    (q : actSOf (StrictLayer.FC (Tower.layer nTower k)) f s ≡ t)
    → Category._⇒_ (StrictLayer.C (Tower.layer nTower k))
        (y-F₀ k x A s) (y-F₀ k x B t)
  y-F₁ k x {A} {B} {s} {t} f q =
    proj₁ (Unfolding.unfoldFunctor (out x) .Functor.F₁
             {A = ((A , s) , lift s)}
             {B = ((B , t) , lift t)}
             ((f , q) , cong lift q))

  -- Functor laws inherited from x via F-resp-≈ on diagonally-lifted morphisms;
  -- the diagonal identity and composite are pointwise equal to the actual
  -- ones, so F-resp-≈ applies directly
  -- 函子律经 F-resp-≈ 作用于对角提升的态射，从 x 继承；
  -- 对角恒等与复合与实际恒等/复合逐分量相等，故 F-resp-≈ 直接适用
  y-unfoldFunctor : ∀ k
    (x : Cosmos (StrictLayer.C (Tower.layer nTower (suc k)))
                (StrictLayer.FC (Tower.layer nTower (suc k))))
    → Functor (ShapeCat
        (StrictLayer.C (Tower.layer nTower k))
        (StrictLayer.FC (Tower.layer nTower k)))
        (StrictLayer.C (Tower.layer nTower k))
  y-unfoldFunctor k x = record
    { F₀           = λ { (A , s) → y-F₀ k x A s }
    ; F₁           = λ { {A , s} {B , t} (f , q) →
                         y-F₁ k x {A = A} {B = B} {s = s} {t = t} f q }
    ; identity     = λ { {A , s} →
        let
          module SCₖ = Category (ShapeCat
            (StrictLayer.C (Tower.layer nTower k))
            (StrictLayer.FC (Tower.layer nTower k)))
          module SC₊ = Category (ShapeCat
            (StrictLayer.C (Tower.layer nTower (suc k)))
            (StrictLayer.FC (Tower.layer nTower (suc k))))
          module Cₖ  = Category (StrictLayer.C (Tower.layer nTower k))
          UF      = Unfolding.unfoldFunctor (out x)
          id-k    = SCₖ.id {A = (A , s)}
          diag-id = (id-k , cong lift (proj₂ id-k))

          coh-id : SC₊._≈_ diag-id (SC₊.id {A = ((A , s) , lift s)})
          coh-id = Cₖ.Equiv.refl
        in
        Cₖ.Equiv.trans
          (Functor.F-resp-≈ UF {f = diag-id} coh-id)
          (Functor.identity UF {A = ((A , s) , lift s)}) }
    ; homomorphism = λ { {X = (A , s)} {Y = (B , t)} {Z = (C , u)}
                         {f = (f₁ , q₁)} {g = (g₁ , q₂)} →
        let
          module Cₖ  = Category (StrictLayer.C (Tower.layer nTower k))
          module SCₖ = Category (ShapeCat
            (StrictLayer.C (Tower.layer nTower k))
            (StrictLayer.FC (Tower.layer nTower k)))
          module SC₊ = Category (ShapeCat
            (StrictLayer.C (Tower.layer nTower (suc k)))
            (StrictLayer.FC (Tower.layer nTower (suc k))))
          UF = Unfolding.unfoldFunctor (out x)
          f-sc : SCₖ._⇒_ (A , s) (B , t)
          f-sc = (f₁ , q₁)
          g-sc : SCₖ._⇒_ (B , t) (C , u)
          g-sc = (g₁ , q₂)
          g∘f : SCₖ._⇒_ (A , s) (C , u)
          g∘f = g-sc SCₖ.∘ f-sc
          f'       = (f-sc , cong lift q₁)
          g'       = (g-sc , cong lift q₂)
          diag-g∘f = (g∘f , cong lift (proj₂ g∘f))
          g'∘f'    = g' SC₊.∘ f'
          coh-hom : SC₊._≈_ diag-g∘f g'∘f'
          coh-hom = Cₖ.Equiv.refl
        in
        Cₖ.Equiv.trans
          (Functor.F-resp-≈ UF {f = diag-g∘f} {g = g'∘f'} coh-hom)
          (Functor.homomorphism UF {f = f'} {g = g'}) }
    ; F-resp-≈     = λ { {A , s} {B , t}
                        {f = (f₁ , q₁)} {g = (f₂ , q₂)} eq-f →
        Unfolding.unfoldFunctor (out x) .Functor.F-resp-≈
          {A = ((A , s) , lift s)}
          {B = ((B , t) , lift t)}
          {f = ((f₁ , q₁) , cong lift q₁)}
          {g = ((f₂ , q₂) , cong lift q₂)}
          eq-f }
    }

  -- pos-to-shape-y: the second component of x.F₀ equals the shape of x.F₁'s
  -- image, up to shape singleton at the target
  -- pos-to-shape-y：x.F₀ 的第二分量等于 x.F₁ 像的形状，
  -- 在目标对象上的形状单点性意义下
  pos-actS-y : ∀ k
    (x : Cosmos (StrictLayer.C (Tower.layer nTower (suc k)))
                (StrictLayer.FC (Tower.layer nTower (suc k))))
    {A B : Category.Obj (StrictLayer.C (Tower.layer nTower k))}
    {s : ShapeOf (StrictLayer.FC (Tower.layer nTower k)) A}
    {t : ShapeOf (StrictLayer.FC (Tower.layer nTower k)) B}
    (f : Category._⇒_ (StrictLayer.C (Tower.layer nTower k)) A B)
    (q : actSOf (StrictLayer.FC (Tower.layer nTower k)) f s ≡ t)
    (p : PosOf (StrictLayer.FC (Tower.layer nTower k)) {A = A} s)
    → proj₂ (Unfolding.unfoldFunctor (out x) .Functor.F₀ ((B , t) , lift t))
      ≡ actSOf (StrictLayer.FC (Tower.layer nTower k))
          (proj₁ (Unfolding.unfoldFunctor (out x) .Functor.F₁
                   {A = ((A , s) , lift s)}
                   {B = ((B , t) , lift t)}
                   ((f , q) , cong lift q)))
          (proj₂ (Unfolding.unfoldFunctor (out x) .Functor.F₀ ((A , s) , lift s)))
  pos-actS-y k x {A} {B} {s} {t} f q p =
    shape-singleton-at k
      (proj₁ (Unfolding.unfoldFunctor (out x) .Functor.F₀ ((B , t) , lift t)))
      (proj₂ (Unfolding.unfoldFunctor (out x) .Functor.F₀ ((B , t) , lift t)))
      (actSOf (StrictLayer.FC (Tower.layer nTower k))
        (proj₁ (Unfolding.unfoldFunctor (out x) .Functor.F₁
                 {A = ((A , s) , lift s)}
                 {B = ((B , t) , lift t)}
                 ((f , q) , cong lift q)))
        (proj₂ (Unfolding.unfoldFunctor (out x) .Functor.F₀ ((A , s) , lift s))))

  -- surj-y: unfoldFunctor is y-unfoldFunctor; unfold-next recurses on the
  -- diagonal lift; pos-to-shape reads x.F₀'s second component;
  -- pos-actS-compat is pos-actS-y at the canonical position inhabitant
  -- surj-y：unfoldFunctor 为 y-unfoldFunctor；unfold-next 在对角提升上
  -- 递归；pos-to-shape 读取 x.F₀ 的第二分量；
  -- pos-actS-compat 由 pos-actS-y 在典范位置居民处给出
  surj-y : ∀ k
    (x : Cosmos (StrictLayer.C (Tower.layer nTower (suc k)))
                (StrictLayer.FC (Tower.layer nTower (suc k))))
    → Cosmos (StrictLayer.C (Tower.layer nTower k))
              (StrictLayer.FC (Tower.layer nTower k))
  surj-y k x .out = record
    { unfoldFunctor   = y-unfoldFunctor k x
    ; unfold-next     = λ {A} s →
        surj-y k (x .out .unfold-next {A = (A , s)} (lift s))
    ; pos-to-shape    = λ {A} s _ →
        proj₂ (Unfolding.unfoldFunctor (out x) .Functor.F₀ ((A , s) , lift s))
    ; pos-actS-compat = λ {A} {B} {s} {t} f q _ →
        pos-actS-y k x f q (pos-inhabited-tower k A s)
    }

  -- x.F₀ is independent of the shape component at layer suc k, by shape
  -- singleton at layer k
  -- x.F₀ 在 suc k 层的形状分量上无关，由 k 层的形状单点性给出
  x-F₀-shape-irrelevant : ∀ k
    (x : Cosmos (StrictLayer.C (Tower.layer nTower (suc k)))
                (StrictLayer.FC (Tower.layer nTower (suc k))))
    (A : Category.Obj (StrictLayer.C (Tower.layer nTower k)))
    (s : ShapeOf (StrictLayer.FC (Tower.layer nTower k)) A)
    (u v : ShapeOf (StrictLayer.FC (Tower.layer nTower (suc k))) (A , s))
    → Unfolding.unfoldFunctor (out x) .Functor.F₀ ((A , s) , u)
    ≡ Unfolding.unfoldFunctor (out x) .Functor.F₀ ((A , s) , v)
  x-F₀-shape-irrelevant k x A s u v =
    cong F (begin
      u
        ≡˘⟨ lift-lower-eq u ⟩
      lift (lower u)
        ≡⟨ cong lift (shape-singleton-at k A (lower u) (lower v)) ⟩
      lift (lower v)
        ≡⟨ lift-lower-eq v ⟩
      v
      ∎)
    where
      F = λ w → Unfolding.unfoldFunctor (out x) .Functor.F₀ ((A , s) , w)
      lift-lower-eq
        : (w : ShapeOf (StrictLayer.FC (Tower.layer nTower (suc k))) (A , s))
        → lift (lower w) ≡ w
      lift-lower-eq (lift _) = refl

  -- dep-F₀ and pos-to-shape of the composite reduce definitionally to
  -- x.F₀ at the diagonal lift; the choice of s'' is absorbed by y-F₀'s
  -- shape-irrelevance
  -- 复合的 dep-F₀ 与 pos-to-shape 定义性归约为对角提升处的 x.F₀；
  -- s'' 的选择由 y-F₀ 的形状无关性吸收
  dep-F₀-reduce : ∀ k
    (x : Cosmos (StrictLayer.C (Tower.layer nTower (suc k)))
                (StrictLayer.FC (Tower.layer nTower (suc k))))
    (ed : EmbeddingData (surj-y k x))
    (A : Category.Obj (StrictLayer.C (Tower.layer nTower k)))
    (s : ShapeOf (StrictLayer.FC (Tower.layer nTower k)) A)
    (s'' : ShapeOf (StrictLayer.FC (Tower.layer nTower k)) A)
    → Unfolding.unfoldFunctor
        (out (dep-embed-tower k (surj-y k x) ed))
        .Functor.F₀ ((A , s) , lift s'')
    ≡ Unfolding.unfoldFunctor (out x) .Functor.F₀ ((A , s) , lift s)
  dep-F₀-reduce k x ed A s s'' = refl

  -- Transport of lift along a sigma equality
  -- 沿 sigma 等式的 lift 传输
  subst-Σ-Lift-≡ : ∀ {a b ℓ} {A : Set a} {B : A → Set b}
    {p q : Σ A B} (e : p ≡ q)
    → subst (λ z → Lift ℓ (B (proj₁ z))) e (lift (proj₂ p))
    ≡ lift (proj₂ q)
  subst-Σ-Lift-≡ refl = refl

  -- Coinductive bisimulation: unfoldFunctor₀-eq by dep-F₀-reduce +
  -- x-F₀-shape-irrelevant; pos-to-shape-eq by shape-singleton-at at the
  -- target; unfold-next-eq by rewriting with shape-singleton-at then
  -- recursing
  -- 余归纳互模拟：unfoldFunctor₀-eq 由 dep-F₀-reduce + x-F₀-shape-irrelevant；
  -- pos-to-shape-eq 由目标处的 shape-singleton-at；unfold-next-eq 先用
  -- shape-singleton-at 改写再递归
  surj-bisim : ∀ k
    (x : Cosmos (StrictLayer.C (Tower.layer nTower (suc k)))
                (StrictLayer.FC (Tower.layer nTower (suc k))))
    (ed : EmbeddingData (surj-y k x))
    → x ≈C dep-embed-tower k (surj-y k x) ed
  surj-bisim k x ed ._≈C_.unfoldFunctor₀-eq {A = (A , s)} (lift s'') = begin
    Unfolding.unfoldFunctor (out x) .Functor.F₀ ((A , s) , lift s'')
      ≡˘⟨ x-F₀-shape-irrelevant k x A s (lift s) (lift s'') ⟩
    Unfolding.unfoldFunctor (out x) .Functor.F₀ ((A , s) , lift s)
      ≡˘⟨ dep-F₀-reduce k x ed A s s'' ⟩
    Unfolding.unfoldFunctor (out (dep-embed-tower k (surj-y k x) ed))
      .Functor.F₀ ((A , s) , lift s'')
    ∎
  surj-bisim k x ed ._≈C_.pos-to-shape-eq {A = (A , s)} (lift s'') p =
    shape-singleton-at (suc k)
      (Unfolding.unfoldFunctor (out (dep-embed-tower k (surj-y k x) ed))
         .Functor.F₀ ((A , s) , lift s'')) _ _
  surj-bisim k x ed ._≈C_.unfold-next-eq {A = (A , s)} (lift s'')
    rewrite shape-singleton-at (suc k) (A , s) (lift s'') (lift s) =
    surj-bisim k
      (x .out .unfold-next {A = (A , s)} (lift s))
      (EmbeddingData.next ed {A = A} s)

  -- Surjectivity is unconditional: the proof only invokes
  -- shape-singleton-at and pos-inhabited-tower, both intrinsic to the tower
  -- 满射性无条件成立：证明只用到 shape-singleton-at 与 pos-inhabited-tower，
  -- 二者都是塔的固有结构
  surj : (unif : UniformEmbeddingFamilyForTower)
       → SurjectivityForTower unif
  surj unif k x =
    surj-y k x ,
    surj-bisim k x (UniformEmbeddingFamily.getData (unif k) (surj-y k x))
