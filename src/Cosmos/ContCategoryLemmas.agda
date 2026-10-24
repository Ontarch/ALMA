------------------------------------------------------------------------
-- Container morphism lemmas
--
-- Container morphism equivalence lemmas, container functor basics and
-- projections. Shape-level laws for _≈sr_ (sym, trans, assoc,
-- whiskering), basic container functor projections (ShapeOf, PosOf,
-- actSOf, actPOf), and transport of container shapes along object
-- equalities (transport, transport-refl, transport-sym, transport-trans,
-- transport-cong), encapsulating the recurring subst patterns: transport
-- along an object equality, cancellation along sym, split a composite
-- transport, and push a transport through a shape-level map.
--
-- 容器态射引理
--
-- 容器态射等价引理与容器函子基础与投影。_≈sr_ 的形状层面代数律
-- （对称、传递、结合、左右复合）、容器函子的基本投影
-- （ShapeOf、PosOf、actSOf、actPOf）、及沿底范畴对象等式运输容器形状
-- （transport、transport-refl、transport-sym、transport-trans、
-- transport-cong），封装反复出现的 subst 模式：沿对象等式运输形状、
-- 消去沿 sym 的运输、拆分复合运输、把运输推过形状层映射。
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module Cosmos.ContCategoryLemmas where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Container.Core using (Container; shape; position; _⇒_)
open import Relation.Binary.PropositionalEquality.Core using (cong; sym; trans)

open import Categories.Category.Core using (Category)
open import Categories.Functor.Core using (Functor)

open import Cosmos.ContCategory using
  (_≈sr_; ≈sr-sym; ≈sr-trans; ∘M-assoc; ∘M-resp-≈ˡ; ∘M-resp-≈ʳ; ContCat)

------------------------------------------------------------------------
-- Shape-level extraction and laws
--
-- Extract the shape-level equality from an _≈sr_ proof, and record how
-- it behaves under sym, trans, assoc, and the two whiskerings.
--
-- 形状层面的提取与代数律
--
-- 从 _≈sr_ 证明中提取形状层面的等式，并记录其在 sym、trans、assoc 与
-- 两个 whiskering 下的行为。

shape-eq-from-≈sr : ∀ {s p} {C D : Container s p} {f g : C ⇒ D}
                  → f ≈sr g → ∀ x → shape f x ≡ shape g x
shape-eq-from-≈sr eq x = let open _≈sr_ eq in shape-eq x

-- Shape component of ≈sr-sym equals pointwise sym of the shape component.
--
-- ≈sr-sym 的形状分量等于形状分量的逐点对称。
shape-eq-sym : ∀ {s p} {C D : Container s p} {f g : C ⇒ D}
              → (eq : f ≈sr g) (x : Container.Shape C)
              → shape-eq-from-≈sr (≈sr-sym eq) x ≡ sym (shape-eq-from-≈sr eq x)
shape-eq-sym _ _ = refl

-- Shape component of ≈sr-trans equals pointwise trans of the shape
-- components.
--
-- ≈sr-trans 的形状分量等于形状分量的逐点传递。
shape-eq-trans : ∀ {s p} {C D : Container s p} {f g h : C ⇒ D}
                → (eq1 : f ≈sr g) (eq2 : g ≈sr h) (x : Container.Shape C)
                → shape-eq-from-≈sr (≈sr-trans eq1 eq2) x
                  ≡ trans (shape-eq-from-≈sr eq1 x) (shape-eq-from-≈sr eq2 x)
shape-eq-trans _ _ _ = refl

-- Shape component of ∘M-assoc is definitionally refl.
--
-- ∘M-assoc 的形状分量在定义上即为 refl。
shape-eq-assoc : ∀ {s p} {A B C D : Container s p}
              → {f : A ⇒ B} {g : B ⇒ C} {h : C ⇒ D}
              → (x : Container.Shape A)
              → shape-eq-from-≈sr (∘M-assoc {A = A} {B} {C} {D} {f} {g} {h}) x ≡ refl
shape-eq-assoc _ = refl

-- Shape component respects left whiskering: precomposition with f.
--
-- 形状分量关于左复合（与 f 的前复合）的相容性。
shape-eq-resp-ˡ : ∀ {s p} {A B C : Container s p}
                  → {g₁ g₂ : B ⇒ C} {f : A ⇒ B}
                  → (eq : g₁ ≈sr g₂) (x : Container.Shape A)
                  → shape-eq-from-≈sr (∘M-resp-≈ˡ {f = f} eq) x
                    ≡ shape-eq-from-≈sr eq (_⇒_.shape f x)
shape-eq-resp-ˡ {f = f} eq x = refl

-- Shape component respects right whiskering: postcomposition with g.
--
-- 形状分量关于右复合（与 g 的后复合）的相容性。
shape-eq-resp-ʳ : ∀ {s p} {A B C : Container s p}
                → {g : B ⇒ C} {f₁ f₂ : A ⇒ B}
                → (eq : f₁ ≈sr f₂) (x : Container.Shape A)
                → shape-eq-from-≈sr (∘M-resp-≈ʳ {g = g} eq) x
                  ≡ cong (shape g) (shape-eq-from-≈sr eq x)
shape-eq-resp-ʳ _ _ = refl

------------------------------------------------------------------------
-- Basic container functor projections
--
-- ShapeOf and PosOf read the shape and position fibres of a
-- container-valued functor; actSOf and actPOf are its shape- and
-- position-level actions (the latter contravariant in shape).
--
-- 容器函子的基本投影
--
-- ShapeOf 与 PosOf 读取以容器为值的函子的形状纤维与位置纤维；
-- actSOf 与 actPOf 是其形状层与位置层作用（后者关于形状反变）。

ShapeOf : ∀ {o ℓ e s p} {C : Category o ℓ e}
        → Functor C (ContCat s p) → Category.Obj C → Set s
ShapeOf F A = Container.Shape (Functor.₀ F A)

PosOf : ∀ {o ℓ e s p} {C : Category o ℓ e}
      → (F : Functor C (ContCat s p)) {A : Category.Obj C}
      → ShapeOf F A → Set p
PosOf F {A} s = Container.Position (Functor.₀ F A) s

actSOf : ∀ {o ℓ e s p} {C : Category o ℓ e}
        → (F : Functor C (ContCat s p)) {A B : Category.Obj C}
        → Category._⇒_ C A B → ShapeOf F A → ShapeOf F B
actSOf F f = shape (Functor.₁ F f)

actPOf : ∀ {o ℓ e s p} {C : Category o ℓ e}
        → (F : Functor C (ContCat s p)) {A B : Category.Obj C}
        → (f : Category._⇒_ C A B) (s : ShapeOf F A)
        → PosOf F (actSOf F f s) → PosOf F s
actPOf F f s = position (Functor.₁ F f) {s = s}

------------------------------------------------------------------------
-- Transport of container shapes along object equalities
--
-- Transport a shape along an object equality, and record its
-- cancellation and composition laws and its commutation with a
-- shape-level map.
--
-- 沿底范畴对象等式运输容器形状
--
-- 沿对象等式运输形状，并记录其消去律、复合律，以及其与形状层映射的
-- 交换律。

transport : ∀ {o h e s p} {D : Category o h e}
            (FD : Functor D (ContCat s p))
            {a b : Category.Obj D}
          → a ≡ b → ShapeOf FD a → ShapeOf FD b
transport FD refl x = x

-- Transport along refl is the identity.
--
-- 沿 refl 的运输是恒等。
transport-refl : ∀ {o h e s p} {D : Category o h e}
                 (FD : Functor D (ContCat s p))
                 {a : Category.Obj D} (x : ShapeOf FD a)
               → transport FD refl x ≡ x
transport-refl FD x = refl

-- Transport along sym cancels a transport along e.
--
-- 沿 sym e 的运输消去沿 e 的运输。
transport-sym : ∀ {o h e s p} {D : Category o h e}
                (FD : Functor D (ContCat s p))
                {a b : Category.Obj D}
                (e : a ≡ b) (x : ShapeOf FD a)
              → transport FD (sym e) (transport FD e x) ≡ x
transport-sym FD refl x = refl

-- Transport along a composite splits into two transports.
--
-- 沿复合等式的运输拆成两次运输。
transport-trans : ∀ {o h e s p} {D : Category o h e}
                  (FD : Functor D (ContCat s p))
                  {a b c : Category.Obj D}
                  (e₁ : a ≡ b) (e₂ : b ≡ c) (x : ShapeOf FD a)
                → transport FD (trans e₁ e₂) x
                  ≡ transport FD e₂ (transport FD e₁ x)
transport-trans FD refl _ _ = refl

-- Transport commutes with a shape-level map.
--
-- 运输与形状层映射交换。
transport-cong : ∀ {o h e o′ h′ e′ s p}
                 {D : Category o h e} {E : Category o′ h′ e′}
                 (FD : Functor D (ContCat s p))
                 (FE : Functor E (ContCat s p))
                 {H : Functor D E}
                 {a b : Category.Obj D}
                 {f : ∀ {x} → ShapeOf FD x → ShapeOf FE (Functor.F₀ H x)}
                 (e : a ≡ b) (x : ShapeOf FD a)
               → transport FE (cong (Functor.F₀ H) e) (f x)
                 ≡ f (transport FD e x)
transport-cong FD FE refl _ = refl
