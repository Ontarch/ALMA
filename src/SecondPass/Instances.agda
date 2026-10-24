------------------------------------------------------------------------
-- LayeredEqGen instances
--
-- The three equivalence relations as LayeredEqGen instances. Each of
-- _≈C_, _≈ℱ_, _≈⇒ℱX_ is embedded into LayeredEqGen. All three share the
-- same constant observation family Σ Obj (ShapeOf FC), so obs-map is the
-- identity function. For _≈ℱ_ and _≈⇒ℱX_ the state is a triple of two
-- Cosmos and a witness; the layer carries the source-target equalities
-- that align the witness's shapeTrans and onPos before comparison. Only
-- the embedding into LayeredEqGen is definable: the reverse would require
-- eliminating those equalities, which needs path irrelevance and is not
-- available under --safe.
--
-- LayeredEqGen 实例
--
-- 三个等价关系作为 LayeredEqGen 实例。_≈C_、_≈ℱ_、_≈⇒ℱX_ 各自嵌入
-- LayeredEqGen。三者共享同一个常数观察族 Σ Obj (ShapeOf FC)，故
-- obs-map 为恒等函数。_≈ℱ_ 与 _≈⇒ℱX_ 的状态是两个 Cosmos 与见证的
-- 三元组；layer 携带源-目标等式，用于在比较前对齐见证的 shapeTrans
-- 与 onPos。只有嵌入 LayeredEqGen 可定义：反向需要消去这些等式，需要
-- 路径无关性，在 --safe 下不可用。
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module SecondPass.Instances where

open import Agda.Primitive using (Level; _⊔_; lsuc; lzero)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Sigma using (Σ)
open import Relation.Binary.PropositionalEquality.Core
  using (cong; sym; trans; subst)
open import Relation.Binary.PropositionalEquality.Properties
  using (subst-subst; subst-sym-subst; module ≡-Reasoning)
open import Relation.Binary.Structures using (IsEquivalence)
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)
open import Data.Unit.Polymorphic.Base using (⊤; tt)

open import Categories.Category.Core using (Category)
open import Categories.Functor.Core using (Functor)

open import Base.IndexedMType using (Mᵢ)
open import Cosmos.ContCategory using (ContCat)
open import Cosmos.ContCategoryLemmas using (ShapeOf; PosOf)
open import Cosmos.ContCatEquiv using (ShapeCat)
open import SecondPass.Unfolding using (Unfolding; pos-to-shape)
open import SecondPass.Cosmos using (Cosmos; out; _⇒ℱ_; ⇒ℱLayer[_])
open import SecondPass.MorphismObject using (MorphismObject)
open import SecondPass.Terminal using (_≈C_)
open import SecondPass.CosmosCategory using (_≈ℱ_)
open import Equivalence.Core using (LayeredEqGen)
open import Equivalence.Properties
  using (module LayeredEqGen-Properties)
open import SecondPass.FinCatInfinityColimit
  using (_⇒ℱX[_]_; ⇒ℱXLayer[_])
open _⇒ℱX[_]_
open import SecondPass.FinCatInfinityColimitUniversal
  using (_≈⇒ℱX_; ≈⇒ℱXLayer)

------------------------------------------------------------------------
-- Instance-C: _≈C_ as a LayeredEqGen instance
-- The observation set is the constant family of shape-position pairs.
-- It does not depend on the Cosmos, so obs-map is the identity function
-- and the next-eq branch of LayeredEqGen reduces to its non-dependent form
--
-- 实例 C：把 _≈C_ 实例化为 LayeredEqGen
-- 观察集是形状-位置对的常数族。它不依赖 Cosmos，故 obs-map 为恒等
-- 函数，LayeredEqGen 的 next-eq 分支退化为非依赖形式
------------------------------------------------------------------------
module Instance-C {o h e s p : Level}
                  {C : Category o h e}
                  {FC : Functor C (ContCat s p)} where

  open ≡-Reasoning

  private
    module C  = Category C
    module FC = Functor FC

  X-C : Set (o ⊔ h ⊔ e ⊔ s ⊔ p)
  X-C = Cosmos C FC

  -- Constant observation family: shape-position pairs
  --
  -- 常数观察族：形状-位置对
  Obs-C : X-C → Set (o ⊔ s)
  Obs-C _ = Σ (Category.Obj C) (ShapeOf FC)

  -- Recursive descent: unfold the next-layer seed
  --
  -- 递归下降：展开下一层种子
  step-C : (F : X-C) → Obs-C F → X-C
  step-C F (A , s) = Unfolding.unfold-next (out F) {A = A} s

  -- Current-layer observation: object map equality + pos-to-shape
  -- compatibility
  --
  -- 当前层观察：展开函子对象映射 + pos-to-shape 相容性
  layer-C : X-C → X-C → Set (o ⊔ s ⊔ p)
  layer-C F G =
    Σ (∀ {A} (s : ShapeOf FC A)
         → Functor.₀ (Unfolding.unfoldFunctor (out F)) (A , s)
           ≡ Functor.₀ (Unfolding.unfoldFunctor (out G)) (A , s))
      (λ uf-eq →
         ∀ {A} (s : ShapeOf FC A) (q : PosOf FC s)
         → subst (λ x → ShapeOf FC x) (uf-eq s)
                 (pos-to-shape (out F) s q)
           ≡ pos-to-shape (out G) s q)

  -- obs-map is the identity because Obs-C is constant
  --
  -- obs-map 为恒等，因为 Obs-C 是常数
  obs-map-C : (F G : X-C) → layer-C F G → Obs-C F → Obs-C G
  obs-map-C _ _ _ o = o

  LayeredEqGen-C : X-C → X-C → Set (o ⊔ s ⊔ p)
  LayeredEqGen-C = LayeredEqGen Obs-C step-C layer-C obs-map-C

  -- From LayeredEqGen-C to _≈C_
  --
  -- 从 LayeredEqGen-C 到 _≈C_
  to-≈C : ∀ {F G} → LayeredEqGen-C F G → F ≈C G
  to-≈C {F} {G} p ._≈C_.unfoldFunctor₀-eq =
    proj₁ (p .Mᵢ.fst)
  to-≈C {F} {G} p ._≈C_.pos-to-shape-eq =
    proj₂ (p .Mᵢ.fst)
  to-≈C {F} {G} p ._≈C_.unfold-next-eq {A} s =
    to-≈C (p .Mᵢ.snd (A , s))

  -- From _≈C_ to LayeredEqGen-C
  -- 从 _≈C_ 到 LayeredEqGen-C
  from-≈C : ∀ {F G} → F ≈C G → LayeredEqGen-C F G
  from-≈C {F} {G} p .Mᵢ.fst =
    ( p ._≈C_.unfoldFunctor₀-eq
    , p ._≈C_.pos-to-shape-eq )
  from-≈C {F} {G} p .Mᵢ.snd (A , s) =
    from-≈C (p ._≈C_.unfold-next-eq {A = A} s)

  -- Equivalence relation for LayeredEqGen-C, supplied by the generic
  -- properties module. The three coherence conditions are all refl
  -- because obs-map is the identity
  --
  -- LayeredEqGen-C 的等价关系，由通用性质模块提供。三条相干性条件
  -- 全为 refl，因为 obs-map 为恒等
  LayeredEqGen-C-isEquiv : IsEquivalence LayeredEqGen-C
  LayeredEqGen-C-isEquiv =
    LayeredEqGen-Properties.le-isEquivalence
      layer-C-isEquiv
      (λ _ _ → refl)
      (λ _ _ → refl)
      (λ _ _ _ → refl)
    where
      layer-C-isEquiv : IsEquivalence layer-C
      layer-C-isEquiv = record
        { refl  = (λ s → refl) , (λ s q → refl)
        ; sym   = λ { {F} {G} (eq₁ , eq₂) →
                    (λ s → sym (eq₁ s))
                  , (λ s q →
                      begin
                        subst (ShapeOf FC) (sym (eq₁ s))
                          (pos-to-shape (out G) s q)
                          ≡⟨ cong (subst (ShapeOf FC) (sym (eq₁ s)))
                                  (sym (eq₂ s q)) ⟩
                        subst (ShapeOf FC) (sym (eq₁ s))
                          (subst (ShapeOf FC) (eq₁ s)
                                 (pos-to-shape (out F) s q))
                          ≡⟨ subst-sym-subst {P = ShapeOf FC} (eq₁ s)
                                             {p = pos-to-shape (out F) s q} ⟩
                        pos-to-shape (out F) s q
                      ∎) }
        ; trans = λ { {F} {G} {H} (eq₁ , eq₂) (eq₁' , eq₂') →
                    (λ s → trans (eq₁ s) (eq₁' s))
                  , (λ s q →
                      begin
                        subst (ShapeOf FC) (trans (eq₁ s) (eq₁' s))
                          (pos-to-shape (out F) s q)
                          ≡⟨ sym (subst-subst {P = ShapeOf FC}
                                              (eq₁ s) {y≡z = eq₁' s}
                                              {p = pos-to-shape (out F) s q}) ⟩
                        subst (ShapeOf FC) (eq₁' s)
                          (subst (ShapeOf FC) (eq₁ s)
                                 (pos-to-shape (out F) s q))
                          ≡⟨ cong (subst (ShapeOf FC) (eq₁' s))
                                  (eq₂ s q) ⟩
                        subst (ShapeOf FC) (eq₁' s)
                          (pos-to-shape (out G) s q)
                          ≡⟨ eq₂' s q ⟩
                        pos-to-shape (out H) s q
                      ∎) }
        }

------------------------------------------------------------------------
-- Instance-F: _≈ℱ_ as a LayeredEqGen instance
-- State is a triple (F, G, m). The layer must carry F ≡ F' and
-- G ≡ G' because shapeTrans and onPos depend on source and target
-- Cosmos; without these equalities two witnesses cannot be compared.
-- The embedding from _≈ℱ_ sets both to refl since the two triples
-- share F and G
--
-- 实例 F：把 _≈ℱ_ 实例化为 LayeredEqGen
-- 状态为三元组 (F, G, m)。layer 必须携带 F ≡ F' 与 G ≡ G'，因为
-- shapeTrans 与 onPos 依赖源和目标 Cosmos；没有这些等式两个见证
-- 无法比较。从 _≈ℱ_ 的嵌入把两者取为 refl，因为两个三元组共享
-- F 与 G
module Instance-F {o h e s p : Level}
                  {C : Category o h e}
                  {FC : Functor C (ContCat s p)} where

  open ≡-Reasoning

  private
    module C  = Category C
    module FC = Functor FC

  X-F : Set (o ⊔ h ⊔ e ⊔ s ⊔ p)
  X-F = Σ (Cosmos C FC) (λ F → Σ (Cosmos C FC) (λ G → F ⇒ℱ G))

  Obs-F : X-F → Set (o ⊔ s)
  Obs-F _ = Σ (Category.Obj C) (ShapeOf FC)

  step-F : (z : X-F) → Obs-F z → X-F
  step-F (F , G , m) (A , s) =
    ( Unfolding.unfold-next (out F) {A = A} s
    , Unfolding.unfold-next (out G) {A = A} s
    , m .out .⇒ℱLayer[_].onunfold-next {A = A} s )

  layer-F : X-F → X-F → Set (o ⊔ h ⊔ e ⊔ s ⊔ p)
  layer-F (F , G , m) (F' , G' , n) =
    Σ (F ≡ F') (λ eF → Σ (G ≡ G') (λ eG →
      let m'  = subst (λ X → X ⇒ℱ G) eF m
          m'' = subst (λ X → F' ⇒ℱ X) eG m'
      in
      ( ∀ {A} {s : ShapeOf FC A} (q : PosOf FC s)
        → ⇒ℱLayer[_].shapeTrans (m'' .out) q
          ≡ ⇒ℱLayer[_].shapeTrans (n .out) q )
      ×
      ( ∀ {A} {s : ShapeOf FC A} (q : PosOf FC s)
        → MorphismObject.onPos (⇒ℱLayer[_].morphismObj (m'' .out)) q
          ≡ MorphismObject.onPos (⇒ℱLayer[_].morphismObj (n .out)) q )
    ))

  obs-map-F : (z w : X-F) → layer-F z w → Obs-F z → Obs-F w
  obs-map-F _ _ _ o = o

  LayeredEqGen-F : X-F → X-F → Set (o ⊔ h ⊔ e ⊔ s ⊔ p)
  LayeredEqGen-F = LayeredEqGen Obs-F step-F layer-F obs-map-F

  -- Embedding from _≈ℱ_: both equalities are refl, and the subst in
  -- layer-F reduces to the identity, so the two comparison fields are
  -- inherited directly from p
  --
  -- 从 _≈ℱ_ 的嵌入：两个等式都是 refl，layer-F 中的 subst 退化为
  -- 恒等，两个比较字段直接继承自 p
  from-≈ℱ : ∀ {F G} {m n : F ⇒ℱ G}
          → m ≈ℱ n → LayeredEqGen-F (F , G , m) (F , G , n)
  from-≈ℱ {F} {G} {m} {n} p .Mᵢ.fst =
    ( refl , refl
    , ( p ._≈ℱ_.shapeTrans-≈
      , p ._≈ℱ_.onPos-≈ ) )
  from-≈ℱ {F} {G} {m} {n} p .Mᵢ.snd (A , s) =
    from-≈ℱ (p ._≈ℱ_.unfold-next-≈ {A = A} s)

------------------------------------------------------------------------
-- Instance-X: _≈⇒ℱX_ as a LayeredEqGen instance
-- Same structure as Instance-F: state is a triple (x, y, f) of two
-- Cosmos and a cross-category morphism between them. The layer must
-- carry x ≡ x' and y ≡ y' because shapeTrans depends on the target
-- Cosmos y. The embedding from _≈⇒ℱX_ sets both equalities to refl
--
-- 实例 X：把 _≈⇒ℱX_ 实例化为 LayeredEqGen
-- 与 Instance-F 结构相同：状态是两个 Cosmos 及其间跨范畴态射的
-- 三元组 (x, y, f)。layer 必须携带 x ≡ x' 与 y ≡ y'，因为
-- shapeTrans 依赖目标 Cosmos y。从 _≈⇒ℱX_ 的嵌入把两个等式都取为 refl
------------------------------------------------------------------------
module Instance-X {o h e o′ ℓ′ e′ s p : Level}
                  {C : Category o h e} {D : Category o′ ℓ′ e′}
                  {FC : Functor C (ContCat s p)} {FD : Functor D (ContCat s p)}
                  (S : Functor (ShapeCat C FC) (ShapeCat D FD)) where

  private
    module C  = Category C
    module Sf = Functor S

  X-X : Set (o ⊔ h ⊔ e ⊔ o′ ⊔ ℓ′ ⊔ e′ ⊔ s ⊔ p)
  X-X = Σ (Cosmos C FC) (λ x → Σ (Cosmos D FD) (λ y → x ⇒ℱX[ S ] y))

  Obs-X : X-X → Set (o ⊔ s)
  Obs-X _ = Σ (Category.Obj C) (ShapeOf FC)

  step-X : (z : X-X) → Obs-X z → X-X
  step-X (x , y , f) (A , s) =
    ( Unfolding.unfold-next (out x) {A = A} s
    , Unfolding.unfold-next (out y)
        {A = proj₁ (Sf.₀ (A , s))} (proj₂ (Sf.₀ (A , s)))
    , f .out .⇒ℱXLayer[_].onunfold-next {A = A} s )

  layer-X : X-X → X-X
          → Set (o ⊔ h ⊔ e ⊔ o′ ⊔ ℓ′ ⊔ e′ ⊔ s ⊔ p)
  layer-X (x , y , f) (x' , y' , g) =
    Σ (x ≡ x') (λ ex → Σ (y ≡ y') (λ ey →
      let f'  = subst (λ X → X ⇒ℱX[ S ] y) ex f
          f'' = subst (λ Y → x' ⇒ℱX[ S ] Y) ey f'
      in
      ( ∀ {A} {s : ShapeOf FC A} (q : PosOf FC s)
        → ⇒ℱXLayer[_].shapeTrans (f'' .out) q
          ≡ ⇒ℱXLayer[_].shapeTrans (g .out) q )
      ×
      ( ∀ {A} {s : ShapeOf FC A} (q : PosOf FC s)
        → MorphismObject.onPos (⇒ℱXLayer[_].morphismObj (f'' .out)) q
          ≡ MorphismObject.onPos (⇒ℱXLayer[_].morphismObj (g .out)) q )
    ))

  obs-map-X : (z w : X-X) → layer-X z w → Obs-X z → Obs-X w
  obs-map-X _ _ _ o = o

  LayeredEqGen-X : X-X → X-X
                 → Set (o ⊔ h ⊔ e ⊔ o′ ⊔ ℓ′ ⊔ e′ ⊔ s ⊔ p)
  LayeredEqGen-X = LayeredEqGen Obs-X step-X layer-X obs-map-X

  -- Embedding from _≈⇒ℱX_: both equalities are refl, and the subst in
  -- layer-X reduces to the identity, so shapeTrans and onPos comparisons
  -- are inherited directly from p
  --
  -- 从 _≈⇒ℱX_ 的嵌入：两个等式都是 refl，layer-X 中的 subst 退化为
  -- 恒等，shapeTrans 与 onPos 的比较直接继承自 p
  from-≈⇒ℱX : ∀ {x y} {f g : x ⇒ℱX[ S ] y}
            → f ≈⇒ℱX g → LayeredEqGen-X (x , y , f) (x , y , g)
  from-≈⇒ℱX {x} {y} {f} {g} p .Mᵢ.fst =
    ( refl , refl
    , ( p ._≈⇒ℱX_.out .≈⇒ℱXLayer.shapeTrans-eq
      , p ._≈⇒ℱX_.out .≈⇒ℱXLayer.onPos-eq ) )
  from-≈⇒ℱX {x} {y} {f} {g} p .Mᵢ.snd (A , s) =
    from-≈⇒ℱX (p ._≈⇒ℱX_.out .≈⇒ℱXLayer.onunfold-next-eq {A = A} s)

  -- Equivalence relation for LayeredEqGen-X. obs-map-X is the identity,
  -- so the three coherence conditions are refl
  --
  -- LayeredEqGen-X 的等价关系。obs-map-X 为恒等，故三条相干性条件全为 refl
  LayeredEqGen-X-isEquiv
    : (layer-X-isEquiv : IsEquivalence layer-X)
    → IsEquivalence LayeredEqGen-X
  LayeredEqGen-X-isEquiv layer-X-isEquiv =
    LayeredEqGen-Properties.le-isEquivalence
      layer-X-isEquiv
      (λ _ _ → refl)
      (λ _ _ → refl)
      (λ _ _ _ → refl)
