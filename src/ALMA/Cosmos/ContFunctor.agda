------------------------------------------------------------------------
-- Containers as polynomial functors on Setoids
--
-- Builds the functor ⟦ C ⟧ and the embedding ContCat → SetoidFunctorCat,
-- proves preservation of identity, composition and _≈sr_, and proves
-- faithfulness and fullness. Faithfulness is obtained by choosing a
-- Yoneda-style test object and applying projection (lower) plus
-- congruence; fullness constructs a preimage from the test object and
-- verifies equality with the given natural transformation via
-- naturality. Establishes the strong equivalence, and the induced
-- adjoint equivalence, between the category of containers and the full
-- subcategory of polynomial functors.
--
-- 容器作为 Setoids 上的多项式函子
--
-- 构造函子 ⟦ C ⟧ 及嵌入 ContCat → SetoidFunctorCat，证明恒等态射、复合
-- 及 _≈sr_ 的保持性，并证明忠实性与满性。忠实性通过选取 Yoneda 式测试
-- 对象并利用投影（lower）与同余得证；满性通过测试对象构造原像，并利用
-- 自然性验证其与给定自然变换相等。建立容器范畴与多项式函子全子范畴之间
-- 的强等价及由此诱导的伴随等价。
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module ALMA.Cosmos.ContFunctor where

open import Agda.Primitive using (Level; lsuc; _⊔_)
open import Agda.Builtin.Equality using (refl)
open import Agda.Builtin.Sigma using (Σ; _,_)
open import Level using (Lift; lift; lower)
open import Data.Product.Base using (proj₁; proj₂)
open import Data.Container.Core using (Container; Shape; Position; map; _⇒_)
open import Data.Container.Morphism using (id) renaming (_∘_ to _∘Cont_)
open import Data.Container.Relation.Binary.Equality.Setoid using (setoid)
open import Data.Container.Relation.Binary.Pointwise as PW using (_,_; Pointwise)
open import Function.Base using (_∘_)
open import Function.Bundles using (Func; _⇔_; mk⇔)
open import Relation.Binary.PropositionalEquality.Core using (cong)
open import Relation.Binary.PropositionalEquality.Properties renaming
  (setoid to discreteSetoid)
open import Relation.Binary.Bundles using (Setoid)

open import Categories.Adjoint.Equivalence using (⊣Equivalence)
open import Categories.Category.Core using (Category)
open import Categories.Category.Equivalence using (StrongEquivalence)
open import Categories.Category.Equivalence.Properties using (C≅D)
open import Categories.Category.Instance.Setoids using (Setoids)
open import Categories.Category.Construction.Functors using (Functors)
open import Categories.Functor.Core using (Functor)
open import Categories.Functor.Properties using (Faithful; Full; FullyFaithful)
open import Categories.NaturalTransformation.Core using
  (NaturalTransformation; ntHelper; _∘ᵥ_) renaming (id to idNT)
open import Categories.NaturalTransformation.NaturalIsomorphism using
  (_≃_; module ≃; module NaturalIsomorphism)
open import Categories.Morphism using (_≅_; Iso)

open import ALMA.Cosmos.ContCategory using (_≈sr_; ContCat)
open import ALMA.Base.Equivalence using (toStrongEquiv)

------------------------------------------------------------------------
-- Polynomial functor of a fixed container
--
-- For a fixed container C, builds the polynomial functor
-- ⟦ C ⟧ : Setoids → Setoids.
--
-- 固定容器的多项式函子
--
-- 对固定容器 C，构造多项式函子 ⟦ C ⟧ : Setoids → Setoids。

module _ {s p ℓ : Level} where

  -- Source and target levels
  --
  -- The source level only needs to host the position types (p) plus an
  -- arbitrary extra level ℓ for greater generality; the target level
  -- additionally hosts the shape level s.
  --
  -- 源与目标层级
  --
  -- 源层级只需容纳位置类型（p）并额外加上任意层级 ℓ 以使结论更具一般性；
  -- 目标层级还容纳形状层级 s。
  srcLevel = p ⊔ ℓ
  tgtLevel = s ⊔ p ⊔ ℓ

  -- The functor category [Setoids, Setoids] on the chosen levels
  --
  -- Source and target Setoids live at different levels; this is the
  -- standard behavior of Functors, not a special construction.
  --
  -- 所选层级上的函子范畴 [Setoids, Setoids]
  --
  -- 源与目标 Setoids 处于不同层级；这是 Functors 的标准行为，并非特殊
  -- 构造。
  SetoidFunctorCat = Functors (Setoids srcLevel srcLevel) (Setoids tgtLevel tgtLevel)

  -- Category structure of SetoidFunctorCat, used for natural
  -- transformation equivalence.
  --
  -- SetoidFunctorCat 的范畴结构，用于自然变换等价。
  module FuncCat = Category SetoidFunctorCat

  -- Full subcategory construction inherited from the standard library,
  -- instantiated at SetoidFunctorCat.
  --
  -- 从标准库继承的全子范畴构造，实例化到 SetoidFunctorCat。
  open import Categories.Category.SubCategory SetoidFunctorCat using (FullSubCategory)

  module Src = Category (Setoids srcLevel srcLevel) renaming
    ( id to idS ; _∘_ to _∘S_ ; _⇒_ to _⇒S_ ; _≈_ to _≈S_ )
  module Tgt = Category (Setoids tgtLevel tgtLevel) renaming
    ( id to idT ; _∘_ to _∘T_ ; _⇒_ to _⇒T_ ; _≈_ to _≈T_ )

  private
    -- Pointwise congruence on a container extension
    --
    -- The shape is definitionally equal, positions are related
    -- pointwise.
    --
    -- 容器扩张上的逐点同余
    --
    -- 形状定义上相等，位置逐点相关。
    ptw-cong :
      {a : Level} {X : Setoid a a} {C : Container s p}
      (s : Shape C)
      {h k : Position C s → Setoid.Carrier X}
      (eq : ∀ p → Setoid._≈_ X (h p) (k p))
      → Setoid._≈_ (setoid X C) (s , h) (s , k)
    ptw-cong s eq = refl PW., eq

    -- Pointwise reflexive equality on a container extension.
    --
    -- 容器扩张上的逐点自反相等。
    ptw-refl :
      {a : Level} {X : Setoid a a} {C : Container s p}
      (s : Shape C)
      (h : Position C s → Setoid.Carrier X)
      → Setoid._≈_ (setoid X C) (s , h) (s , h)
    ptw-refl {X = X} s h = ptw-cong {X = X} s (λ p → Setoid.refl X {x = h p})

  ----------------------------------------------------------------------
  -- The polynomial functor of a container
  --
  -- Parameterised record: packages the container C; level parameters
  -- are provided by the enclosing module.
  --
  -- 容器的多项式函子
  --
  -- 以容器 C 为参数的 record；层级参数由外层模块提供。

  record ContFunctor (C : Container s p) : Set where
    private
      -- Object mapping: interpret C as a setoid-valued functor.
      --
      -- 对象映射：将 C 解释为取值于 Setoids 的函子。
      ⟦_⟧ₛ : Setoid srcLevel srcLevel → Setoid tgtLevel tgtLevel
      ⟦_⟧ₛ A = setoid A C

      -- Morphism mapping: lift a setoid function to the container
      -- extension.
      --
      -- 态射映射：将 setoid 态射提升为容器扩张上的 setoid 态射。
      mapₛ : {A B : Setoid srcLevel srcLevel} → A Src.⇒S B → ⟦ A ⟧ₛ Tgt.⇒T ⟦ B ⟧ₛ
      mapₛ {A} {B} f = record
        { to   = map {C = C} {X = Setoid.Carrier A} {Y = Setoid.Carrier B} (Func.to f)
        ; cong = λ { (sh , ps) → sh , λ p → Func.cong f (ps p) }
        }

      -- Preservation of identity: mapₛ (id) ≈ id.
      --
      -- 恒等态射的保持：mapₛ (id) ≈ id。
      map-id≗ : {A : Setoid srcLevel srcLevel}
              → mapₛ (Src.idS {A}) Tgt.≈T Tgt.idT {A = ⟦_⟧ₛ A}
      map-id≗ {A} {x = (s , h)} = ptw-refl {X = A} s h

      -- Preservation of composition: mapₛ (g ∘ f) ≈ mapₛ g ∘ mapₛ f.
      --
      -- 复合的保持：mapₛ (g ∘ f) ≈ mapₛ g ∘ mapₛ f。
      map-∘≗ : {A B D : Setoid srcLevel srcLevel} {f : A Src.⇒S B} {g : B Src.⇒S D}
             → mapₛ (g Src.∘S f) Tgt.≈T (mapₛ g Tgt.∘T mapₛ f)
      map-∘≗ {A} {B} {D} {f = f} {g = g} {x = (s , h)} =
        ptw-refl {X = D} s (λ p → Func.to g (Func.to f (h p)))

      -- Preservation of equivalence: f ≈ g → mapₛ f ≈ mapₛ g.
      --
      -- 等价的保持：f ≈ g → mapₛ f ≈ mapₛ g。
      map-resp-≗ : {A B : Setoid srcLevel srcLevel} {f g : A Src.⇒S B}
                 → f Src.≈S g → mapₛ f Tgt.≈T mapₛ g
      map-resp-≗ {A} {B} {f} {g} f≈g {x = (s , h)} =
        ptw-cong {X = B} s (λ p → f≈g {x = h p})

    -- Assemble the polynomial functor ⟦ C ⟧ : Setoids → Setoids.
    --
    -- 组装多项式函子 ⟦ C ⟧ : Setoids → Setoids。
    functor : Functor (Setoids srcLevel srcLevel) (Setoids tgtLevel tgtLevel)
    functor = record
      { F₀           = ⟦_⟧ₛ
      ; F₁           = mapₛ
      ; identity     = λ {A} → map-id≗ {A = A}
      ; homomorphism = λ {A} {B} {D} {f} {g}
                     → map-∘≗ {A = A} {B = B} {D = D} {f = f} {g = g}
      ; F-resp-≈     = λ {A} {B} {f} {g} f≈g
                     → map-resp-≗ {A = A} {B = B} {f = f} {g = g} f≈g
      }

  -- The polynomial functor ⟦ C ⟧ associated to a container C.
  --
  -- 容器 C 所对应的多项式函子 ⟦ C ⟧。
  ⟦_⟧ : Container s p → Functor (Setoids srcLevel srcLevel) (Setoids tgtLevel tgtLevel)
  ⟦ C ⟧ = ContFunctor.functor {C = C} (record {})

  -- Lift a container morphism m : C ⇒ D to a natural transformation
  -- ⟦ C ⟧ ⟹ ⟦ D ⟧.
  --
  -- 将容器态射 m : C ⇒ D 提升为自然变换 ⟦ C ⟧ ⟹ ⟦ D ⟧。
  mapNT : {C D : Container s p} → (C ⇒ D) → NaturalTransformation ⟦ C ⟧ ⟦ D ⟧
  mapNT {C} {D} m = ntHelper record
    { η = λ X → record
      { to = _⇒_.⟪_⟫ m
      ; cong = λ { {x = (s , k)} (refl , eq) →
          let open _⇒_ m in
          ptw-cong {X = X} (shape s) (λ p → eq (position p)) }
      }
    -- Naturality: η_Y ∘ ⟦ C ⟧ f ≈ ⟦ D ⟧ f ∘ η_X.
    --
    -- 自然性：η_Y ∘ ⟦ C ⟧ f ≈ ⟦ D ⟧ f ∘ η_X。
    ; commute = λ {X Y} f {x} →
        let (s , k) = x
        in ptw-refl {X = Y} {C = D} (_⇒_.shape m s)
             (λ p → Func.to f (k (_⇒_.position m p)))
    }

  -- Identity preservation: mapNT (id C) ≈ id.
  --
  -- 恒等态射的保持：mapNT (id C) ≈ id。
  mapNT-id : {C : Container s p} → mapNT (id C) FuncCat.≈ idNT
  mapNT-id {C} {X} {x = (s , k)} = ptw-refl {X = X} s k

  -- Composition preservation: mapNT (m ∘ n) ≈ mapNT m ∘ᵥ mapNT n.
  --
  -- 复合的保持：mapNT (m ∘ n) ≈ mapNT m ∘ᵥ mapNT n。
  mapNT-∘ : {C D E : Container s p} {m : D ⇒ E} {n : C ⇒ D}
          → mapNT (m ∘Cont n) FuncCat.≈ (mapNT m ∘ᵥ mapNT n)
  mapNT-∘ {C} {D} {E} {m} {n} {X} {x = (s , k)} =
    ptw-refl {X = X}
      (_⇒_.shape m (_⇒_.shape n s))
      (λ p → k (_⇒_.position n (_⇒_.position m p)))

  -- Equivalence preservation: m ≈sr n → mapNT m ≈ mapNT n.
  --
  -- 等价的保持：m ≈sr n → mapNT m ≈ mapNT n。
  mapNT-resp-≈ : {C D : Container s p} {m n : C ⇒ D}
               → m ≈sr n → mapNT m FuncCat.≈ mapNT n
  mapNT-resp-≈ {C} {D} {m} {n} eq {X} {x = (s , k)} =
    _≈sr_.shape-eq eq s , λ q → Setoid.reflexive X (cong k (_≈sr_.position-eq eq s q))

  -- The embedding functor ContCat → [Setoids, Setoids].
  --
  -- 嵌入函子 ContCat → [Setoids, Setoids]。
  ContEmbedding : Functor (ContCat s p) SetoidFunctorCat
  ContEmbedding = record
    { F₀         = ⟦_⟧
    ; F₁         = mapNT
    ; identity   = λ {A} {X} {x} → mapNT-id {C = A} {X} {x}
    ; homomorphism = λ {X Y Z f g} {S} {x} → mapNT-∘ {m = g} {n = f} {S} {x}
    ; F-resp-≈  = λ {A B f g} eq {X} {x} → mapNT-resp-≈ eq {X} {x}
    }

  ----------------------------------------------------------------------
  -- Faithfulness
  --
  -- mapNT m ≈ mapNT n → m ≈sr n, via a Yoneda-style discrete test
  -- object and projection lower.
  --
  -- 忠实性
  --
  -- mapNT m ≈ mapNT n → m ≈sr n，经由 Yoneda 式离散测试对象与投影
  -- lower。

  ContEmbedding-faithful : Faithful ContEmbedding
  ContEmbedding-faithful {C} {D} {m} {n} nt-eq = record
    { shape-eq = λ s → Pointwise.shape (get-eq s)
    ; position-eq   = λ s q → cong lower (Pointwise.position (get-eq s) q)
    }
    where
      get-eq : (s : Shape C) → _
      get-eq s = nt-eq {discreteSetoid (Lift srcLevel (Position C s))} { (s , lift) }

  -- Equivalence between container-morphism equivalence and
  -- natural-transformation equivalence.
  --
  -- 容器态射等价与其诱导的自然变换等价之间的双向等价关系。
  mapNT-iff-≈sr : {C D : Container s p} {m n : C ⇒ D}
               → (mapNT m FuncCat.≈ mapNT n) ⇔ (m ≈sr n)
  mapNT-iff-≈sr = mk⇔ ContEmbedding-faithful mapNT-resp-≈

  ----------------------------------------------------------------------
  -- Fullness
  --
  -- Every natural transformation η : ⟦ C ⟧ ⟹ ⟦ D ⟧ arises, up to
  -- FuncCat._≈_, from a container morphism m : C ⇒ D.
  --
  -- 满性
  --
  -- 每个自然变换 η : ⟦ C ⟧ ⟹ ⟦ D ⟧ 都模去 FuncCat._≈_ 后来自某个容器
  -- 态射 m : C ⇒ D。

  ContEmbedding-full : Full ContEmbedding
  ContEmbedding-full {C} {D} η = m , mapNT≈η
    where
      module NT = NaturalTransformation η

      testObj : Shape C → Setoid srcLevel srcLevel
      testObj s = discreteSetoid (Lift srcLevel (Position C s))

      η-at : (s : Shape C) →
             Σ (Shape D) (λ t → Position D t → Lift srcLevel (Position C s))
      η-at s = Func.to (NT.η (testObj s)) (s , lift)

      m : C ⇒ D
      m = record
        { shape    = λ s → proj₁ (η-at s)
        ; position = λ {s} p → lower (proj₂ (η-at s) p)
        }

      -- Promote an arbitrary position function to a Setoid morphism
      -- whose domain is the discrete setoid on positions.
      --
      -- Because the domain equality is propositional identity, every
      -- function is automatically a Setoid morphism.
      --
      -- 把任意位置函数提升为以位置集上的离散 setoid 为定义域的 Setoid
      -- 态射。
      --
      -- 定义域等价为命题相等，故任意函数自动是同态。
      promote : (s : Shape C) {X : Setoid srcLevel srcLevel}
              → (Position C s → Setoid.Carrier X)
              → testObj s Src.⇒S X
      promote s {X} k = record
        { to   = λ { (lift p) → k p }
        ; cong = λ { refl → Setoid.refl X }
        }

      η≈mapNT : η FuncCat.≈ mapNT m
      η≈mapNT {X} {x = (s , k)} =
        NT.commute (promote s k) {x = (s , lift)}

      -- Reverse the pointwise equivalence to match the direction
      -- required by Full's full field (F₁ g ≈ f).
      --
      -- 逐点反转等价，以匹配 Full 的 full 字段所要求的方向
      -- （F₁ g ≈ f）。
      mapNT≈η : mapNT m FuncCat.≈ η
      mapNT≈η {X} {x} = Setoid.sym (Functor.F₀ ⟦ D ⟧ X) (η≈mapNT {X} {x})

  -- Fully faithful: Full × Faithful.
  --
  -- 全忠实：Full × Faithful。
  ContEmbedding-fully-faithful : FullyFaithful ContEmbedding
  ContEmbedding-fully-faithful = ContEmbedding-full , ContEmbedding-faithful

  ----------------------------------------------------------------------
  -- Polynomial functors as a full subcategory
  --
  -- Predicate: F is a polynomial functor, i.e. there exist a container
  -- C and a natural isomorphism F ≃ ⟦ C ⟧.
  --
  -- 多项式函子作为全子范畴
  --
  -- 谓词：F 是多项式函子，即存在容器 C 与自然同构 F ≃ ⟦ C ⟧。

  PolyPred : Category.Obj SetoidFunctorCat → Set (lsuc (s ⊔ p ⊔ ℓ))
  PolyPred F = Σ (Container s p) (λ C → F ≃ ⟦ C ⟧)

  -- Objects of the full subcategory.
  --
  -- 全子范畴的对象。
  PolyObj : Set (lsuc (s ⊔ p ⊔ ℓ))
  PolyObj = Σ (Category.Obj SetoidFunctorCat) PolyPred

  pattern poly F C iso = F , C , iso

  polyF : PolyObj → Functor (Setoids srcLevel srcLevel) (Setoids tgtLevel tgtLevel)
  polyF (poly F _ _) = F

  polyC : (A : PolyObj) → Container s p
  polyC (poly _ C _) = C

  polyIso : (A : PolyObj) → polyF A ≃ ⟦ polyC A ⟧
  polyIso (poly _ _ iso) = iso

  -- Full subcategory: all categorical structure inherited from
  -- SetoidFunctorCat via the standard-library FullSubCategory.
  --
  -- 全子范畴：所有范畴结构经标准库 FullSubCategory 继承自
  -- SetoidFunctorCat。
  PolyFunctors :
    Category (lsuc (s ⊔ p ⊔ ℓ)) (s ⊔ lsuc p ⊔ lsuc ℓ) (s ⊔ lsuc p ⊔ lsuc ℓ)
  PolyFunctors = FullSubCategory {I = PolyObj} proj₁

  ----------------------------------------------------------------------
  -- Restriction Φ to the essential image
  --
  -- Φ : ContCat s p → PolyFunctors, the restriction of ContEmbedding to
  -- its essential image; C ↦ (⟦ C ⟧ , C , ≃.refl).
  --
  -- 限制到本质像的 Φ
  --
  -- Φ : ContCat s p → PolyFunctors，ContEmbedding 到其本质像上的限制；
  -- C ↦ (⟦ C ⟧ , C , ≃.refl)。
  Φ : Functor (ContCat s p) PolyFunctors
  Φ = record
    { F₀ = λ C → poly (⟦ C ⟧) C (≃.refl)
    ; F₁ = λ {C} {D} m → mapNT {C = C} {D = D} m
    ; identity = λ {C} {X} {x} →
        Functor.identity ContEmbedding {A = C} {X} {x}
    ; homomorphism = λ {A} {B} {C} {f} {g} {X} {x} →
        Functor.homomorphism ContEmbedding
          {X = A} {Y = B} {Z = C} {f = f} {g = g} {X} {x}
    ; F-resp-≈ = λ {A} {B} {f} {g} eq {X} {x} →
        Functor.F-resp-≈ ContEmbedding
          {A = A} {B = B} {f = f} {g = g} eq {X} {x}
    }

  -- Φ is full, inherited from ContEmbedding.
  --
  -- Φ 是满函子，继承自 ContEmbedding。
  Φ-full : Full Φ
  Φ-full {C} {D} η = ContEmbedding-full {C} {D} η

  -- Φ is faithful, inherited from ContEmbedding.
  --
  -- Φ 是忠实函子，继承自 ContEmbedding。
  Φ-faithful : Faithful Φ
  Φ-faithful {C} {D} {m} {n} = ContEmbedding-faithful {C} {D} {m} {n}

  -- Φ is fully faithful: Full × Faithful.
  --
  -- Φ 全忠实：Full × Faithful。
  Φ-fully-faithful : FullyFaithful Φ
  Φ-fully-faithful = Φ-full , Φ-faithful

  -- Φ is split essentially surjective: (F , C , iso) ↦ C
  --
  -- from/to are swapped relative to ⇐/⇒ of iso, hence isoˡ/isoʳ are
  -- swapped.
  --
  -- Φ 分裂本质满射：(F , C , iso) ↦ C
  --
  -- from/to 相对 iso 的 ⇐/⇒ 对调，故 isoˡ/isoʳ 互换。
  Φ-split-ess-surj :
    (Y : Category.Obj PolyFunctors) →
    Σ (Category.Obj (ContCat s p))
      (λ X → _≅_ PolyFunctors (Functor.F₀ Φ X) Y)
  Φ-split-ess-surj (poly F C iso) = C , record
    { from = NaturalIsomorphism.F⇐G iso
    ; to   = NaturalIsomorphism.F⇒G iso
    ; iso  = record
      { isoˡ = λ {X} → Iso.isoʳ (NaturalIsomorphism.iso iso X)
      ; isoʳ = λ {X} → Iso.isoˡ (NaturalIsomorphism.iso iso X)
      }
    }

  -- Containers (syntax) ≃ polynomial functors (semantics)
  --
  -- From Φ being fully faithful and split essentially surjective,
  -- obtain a strong equivalence via the generic bridge.
  --
  -- 容器（语法）≃ 多项式函子（语义）
  --
  -- 由 Φ 全忠实 + 分裂本质满射，经通用桥接得到强等价。
  ContCat≈PolyFunctors : StrongEquivalence (ContCat s p) PolyFunctors
  ContCat≈PolyFunctors = toStrongEquiv Φ Φ-fully-faithful Φ-split-ess-surj

  -- StrongEquivalence yields an adjoint equivalence via C≅D.
  --
  -- StrongEquivalence 经 C≅D 得到伴随等价。
  ContCat⊣EquivPolyFunctors : ⊣Equivalence (ContCat s p) PolyFunctors
  ContCat⊣EquivPolyFunctors = C≅D ContCat≈PolyFunctors
