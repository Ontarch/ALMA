------------------------------------------------------------------------
-- The category rooted in the indexed coinductive type Mᵢ, together with
-- the ordinary container category as its trivial specialisation at I = ⊤.
--
-- 扎根于索引余归纳类型 Mᵢ 的范畴，以及 I = ⊤ 处的普通容器范畴特化。
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module ALMA.Base.MCategory where

open import Agda.Primitive using (Level; _⊔_; lsuc)
open import Agda.Builtin.Sigma using (Σ; _,_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Product.Base using (proj₁; proj₂)
open import Data.Unit.Polymorphic.Base using (⊤; tt)
open import Function.Base using (id; _∘_)
open import Relation.Binary.PropositionalEquality.Core using (cong; sym; trans; subst)
open import Relation.Binary.Structures using (IsEquivalence)
open import Relation.Binary.PropositionalEquality.Properties using
  (subst-subst; subst-subst-sym; module ≡-Reasoning)
open ≡-Reasoning

open import Categories.Category.Core using (Category)

open import ALMA.Base.IndexedMType using (Mᵢ; fst; snd)

------------------------------------------------------------------------
-- Generic two-level dependent transport
--
-- 泛化两层依赖传输

module DependentTransport
  {ℓᵢ ℓₐ ℓₚ : Level}
  {Idx : Set ℓᵢ} {Sh : Idx → Set ℓₐ}
  (Ps : (i : Idx) → Sh i → Set ℓₚ) where

  transport₂ : ∀ {i₁ i₂ : Idx} {a₁ : Sh i₁} {a₂ : Sh i₂}
    → (eᵢ : i₁ ≡ i₂) (eₛ : subst Sh eᵢ a₁ ≡ a₂)
    → Ps i₁ a₁ → Ps i₂ a₂
  transport₂ refl refl q = q

  subst-sym' : ∀ {i₁ i₂ : Idx} {a₁ : Sh i₁} {a₂ : Sh i₂}
    → (eᵢ : i₁ ≡ i₂) (eₛ : subst Sh eᵢ a₁ ≡ a₂)
    → subst Sh (sym eᵢ) a₂ ≡ a₁
  subst-sym' refl refl = refl

  transport₂-round : ∀ {i₁ i₂ : Idx} {a₁ : Sh i₁} {a₂ : Sh i₂}
    → (eᵢ : i₁ ≡ i₂) (eₛ : subst Sh eᵢ a₁ ≡ a₂) (q' : Ps i₂ a₂)
    → transport₂ eᵢ eₛ
        (transport₂ (sym eᵢ) (subst-sym' eᵢ eₛ) q') ≡ q'
  transport₂-round refl refl q' = refl

  subst-trans' : ∀ {i₁ i₂ i₃ : Idx}
                   {a₁ : Sh i₁} {a₂ : Sh i₂} {a₃ : Sh i₃}
    → (e₁ : i₁ ≡ i₂) (e₂ : i₂ ≡ i₃)
      (s₁ : subst Sh e₁ a₁ ≡ a₂) (s₂ : subst Sh e₂ a₂ ≡ a₃)
    → subst Sh (trans e₁ e₂) a₁ ≡ a₃
  subst-trans' refl refl refl refl = refl

  transport₂-trans : ∀ {i₁ i₂ i₃ : Idx}
                       {a₁ : Sh i₁} {a₂ : Sh i₂} {a₃ : Sh i₃}
    → (e₁ : i₁ ≡ i₂) (e₂ : i₂ ≡ i₃)
      (s₁ : subst Sh e₁ a₁ ≡ a₂) (s₂ : subst Sh e₂ a₂ ≡ a₃)
      (q : Ps i₁ a₁)
    → transport₂ e₂ s₂ (transport₂ e₁ s₁ q)
      ≡ transport₂ (trans e₁ e₂) (subst-trans' e₁ e₂ s₁ s₂) q
  transport₂-trans refl refl refl refl q = refl

------------------------------------------------------------------------
-- Indexed objects
--
-- 索引对象

record Mᵢ-Obj (i a b : Level) : Set (lsuc (i ⊔ a ⊔ b)) where
  field
    I    : Set i
    A    : I → Set a
    B    : (i : I) (a : A i) → Set b
    next : (i : I) (a : A i) (p : B i a) → I
    root : I
open Mᵢ-Obj public

------------------------------------------------------------------------
-- Indexed morphisms; pos is contravariant on positions
--
-- 索引态射；pos 在位置上反变

record Mᵢ-⇒ {i₁ a₁ b₁ i₂ a₂ b₂}
               (X : Mᵢ-Obj i₁ a₁ b₁)
               (Y : Mᵢ-Obj i₂ a₂ b₂)
  : Set (i₁ ⊔ a₁ ⊔ b₁ ⊔ i₂ ⊔ a₂ ⊔ b₂) where
  field
    idx   : I X → I Y
    shape : (x : I X) → A X x → A Y (idx x)
    pos   : (x : I X) (ax : A X x)
          → B Y (idx x) (shape x ax) → B X x ax
open Mᵢ-⇒ public

------------------------------------------------------------------------
-- Identity and composition
--
-- 恒等与复合

idᵢ : ∀ {i a b} {X : Mᵢ-Obj i a b} → Mᵢ-⇒ X X
idᵢ {X = X} = record
  { idx = id ; shape = λ _ → id ; pos = λ _ _ → id }

infixr 9 _∘ᵢ_
_∘ᵢ_ : ∀ {i₁ a₁ b₁ i₂ a₂ b₂ i₃ a₃ b₃}
      {X : Mᵢ-Obj i₁ a₁ b₁} {Y : Mᵢ-Obj i₂ a₂ b₂} {Z : Mᵢ-Obj i₃ a₃ b₃}
      → Mᵢ-⇒ Y Z → Mᵢ-⇒ X Y → Mᵢ-⇒ X Z
_∘ᵢ_ g f = record
  { idx   = idx g ∘ idx f
  ; shape = λ x → shape g (idx f x) ∘ shape f x
  ; pos   = λ x ax → pos f x ax ∘ pos g (idx f x) (shape f x ax)
  }

------------------------------------------------------------------------
-- The flat morphism fibre over a source point and a fixed target index
--
-- 态射在一个源点、一个固定目标索引上的扁平纤维

record Fiber {i₁ a₁ b₁ i₂ a₂ b₂}
             {X : Mᵢ-Obj i₁ a₁ b₁} {Y : Mᵢ-Obj i₂ a₂ b₂}
             (x : I X) (i : I Y)
  : Set (a₁ ⊔ a₂ ⊔ b₁ ⊔ b₂) where
  field
    shp : A X x → A Y i
    pso : (ax : A X x) → B Y i (shp ax) → B X x ax

fiber-of : ∀ {i₁ a₁ b₁ i₂ a₂ b₂}
             {X : Mᵢ-Obj i₁ a₁ b₁} {Y : Mᵢ-Obj i₂ a₂ b₂}
             (f : Mᵢ-⇒ X Y) (x : I X)
           → Fiber {X = X} {Y = Y} x (idx f x)
fiber-of f x = record { shp = shape f x ; pso = pos f x }

-- Canonical J-transport of a flat fibre along a target-index equality.
--
-- 扁平纤维沿目标索引等式的规范 J 传输。

fiber-tr : ∀ {i₁ a₁ b₁ i₂ a₂ b₂}
             {X : Mᵢ-Obj i₁ a₁ b₁} {Y : Mᵢ-Obj i₂ a₂ b₂}
             {x : I X} {i j : I Y}
         → i ≡ j
         → Fiber {X = X} {Y = Y} x i
         → Fiber {X = X} {Y = Y} x j
fiber-tr refl φ = φ

------------------------------------------------------------------------
-- FE: flat shape+position equality on fibres
--
-- FE：纤维上的扁平形状+位置相等

module FE {i₁ a₁ b₁ i₂ a₂ b₂}
          {X : Mᵢ-Obj i₁ a₁ b₁} {Y : Mᵢ-Obj i₂ a₂ b₂}
          (x : I X) (i : I Y) where

  private
    Fib : Set (a₁ ⊔ a₂ ⊔ b₁ ⊔ b₂)
    Fib = Fiber {X = X} {Y = Y} x i

    shpᵢ : Fib → A X x → A Y i
    shpᵢ φ = Fiber.shp φ

    psoᵢ : (φ : Fib) (ax : A X x)
         → B Y i (Fiber.shp φ ax) → B X x ax
    psoᵢ φ = Fiber.pso φ

  record _≈sr_ (α β : Fib)
    : Set (a₁ ⊔ a₂ ⊔ b₁ ⊔ b₂) where
    field
      shape-eq : ∀ (ax : A X x)
               → shpᵢ α ax ≡ shpᵢ β ax
      position-eq : ∀ (ax : A X x)
                      (q : B Y i (shpᵢ α ax))
                  → psoᵢ α ax q
                  ≡ psoᵢ β ax
                      (subst (B Y i) (shape-eq ax) q)
  open _≈sr_ public

  ≈sr-refl : ∀ {α : Fib} → α ≈sr α
  ≈sr-refl = record
    { shape-eq    = λ _ → refl
    ; position-eq = λ _ _ → refl
    }

  -- Symmetry absorbs the transport round-trip via subst-subst-sym.
  --
  -- 对称用 subst-subst-sym 吸收传输往返。
  ≈sr-sym : ∀ {α β : Fib} → α ≈sr β → β ≈sr α
  ≈sr-sym {α = α} {β = β} p = record
    { shape-eq    = λ ax → sym (shape-eq p ax)
    ; position-eq = λ ax q →
        let e = shape-eq p ax in
        begin
          psoᵢ β ax q
            ≡⟨ cong (psoᵢ β ax)
                   (sym (subst-subst-sym {P = B Y i} e {p = q})) ⟩
          psoᵢ β ax
            (subst (B Y i) e (subst (B Y i) (sym e) q))
            ≡⟨ sym (position-eq p ax (subst (B Y i) (sym e) q)) ⟩
          psoᵢ α ax (subst (B Y i) (sym e) q)
        ∎
    }

  -- Transitivity merges transports via subst-subst.
  --
  -- 传递用 subst-subst 合并传输。
  ≈sr-trans : ∀ {α β γ : Fib} → α ≈sr β → β ≈sr γ → α ≈sr γ
  ≈sr-trans {α = α} {β = β} {γ = γ} p q = record
    { shape-eq    = λ ax → trans (shape-eq p ax) (shape-eq q ax)
    ; position-eq = λ ax r →
        let e₁ = shape-eq p ax
            e₂ = shape-eq q ax
            r₁ = subst (B Y i) e₁ r
        in begin
          psoᵢ α ax r
            ≡⟨ position-eq p ax r ⟩
          psoᵢ β ax r₁
            ≡⟨ position-eq q ax r₁ ⟩
          psoᵢ γ ax (subst (B Y i) e₂ r₁)
            ≡⟨ cong (psoᵢ γ ax)
                   (subst-subst {P = B Y i} e₁ {y≡z = e₂} {p = r}) ⟩
          psoᵢ γ ax (subst (B Y i) (trans e₁ e₂) r)
        ∎
    }

------------------------------------------------------------------------
-- Morphism equality: outer index equality stacked with inner FE
--
-- 态射相等：外层索引相等与内层 FE 相堆叠

module _ {i₁ a₁ b₁ i₂ a₂ b₂}
        {X : Mᵢ-Obj i₁ a₁ b₁} {Y : Mᵢ-Obj i₂ a₂ b₂} where

  private
    module FE' (x : I X) (i : I Y) =
      FE {i₁ = i₁} {a₁ = a₁} {b₁ = b₁}
         {i₂ = i₂} {a₂ = a₂} {b₂ = b₂} {X = X} {Y = Y} x i

  Mᵢ-≈ : (f g : Mᵢ-⇒ X Y) → Set (i₁ ⊔ a₁ ⊔ b₁ ⊔ i₂ ⊔ a₂ ⊔ b₂)
  Mᵢ-≈ f g = ∀ (x : I X) →
    Σ (idx f x ≡ idx g x)
      λ eᵢ → FE'._≈sr_ x (idx f x)
               (fiber-of f x)
               (fiber-tr (sym eᵢ) (fiber-of g x))

  ≈fib-sym : ∀ (x : I X) {i j : I Y} (e' : j ≡ i)
               {α : Fiber {X = X} {Y = Y} x i}
               {β : Fiber {X = X} {Y = Y} x j}
           → FE'._≈sr_ x i α (fiber-tr e' β)
           → FE'._≈sr_ x j β (fiber-tr (sym e') α)
  ≈fib-sym x refl h = FE'.≈sr-sym x _ h

  ≈fib-trans : ∀ (x : I X) {i j k : I Y}
                 (e₁ : i ≡ j) (e₂ : j ≡ k)
                 {α : Fiber {X = X} {Y = Y} x i}
                 {β : Fiber {X = X} {Y = Y} x j}
                 {γ : Fiber {X = X} {Y = Y} x k}
             → FE'._≈sr_ x i α (fiber-tr (sym e₁) β)
             → FE'._≈sr_ x j β (fiber-tr (sym e₂) γ)
             → FE'._≈sr_ x i α (fiber-tr (sym (trans e₁ e₂)) γ)
  ≈fib-trans x refl refl h₁ h₂ = FE'.≈sr-trans x _ h₁ h₂

  Mᵢ-≈-refl : (f : Mᵢ-⇒ X Y) → Mᵢ-≈ f f
  Mᵢ-≈-refl f x = refl , FE'.≈sr-refl x (idx f x)

  Mᵢ-≈-sym : {f g : Mᵢ-⇒ X Y} → Mᵢ-≈ f g → Mᵢ-≈ g f
  Mᵢ-≈-sym p x
    with p x
  ... | eᵢ , h = sym eᵢ , ≈fib-sym x (sym eᵢ) h

  Mᵢ-≈-trans : {f g h : Mᵢ-⇒ X Y} → Mᵢ-≈ f g → Mᵢ-≈ g h → Mᵢ-≈ f h
  Mᵢ-≈-trans p q x
    with p x | q x
  ... | e₁ , h₁ | e₂ , h₂ =
      trans e₁ e₂ , ≈fib-trans x e₁ e₂ h₁ h₂

  Mᵢ-≈-isEquivalence : IsEquivalence Mᵢ-≈
  Mᵢ-≈-isEquivalence = record
    { refl  = λ {f} → Mᵢ-≈-refl f
    ; sym   = λ {f g} → Mᵢ-≈-sym {f = f} {g = g}
    ; trans = λ {f g h} → Mᵢ-≈-trans {f = f} {g = g} {h = h}
    }

------------------------------------------------------------------------
-- Congruence of composition
--
-- 复合的同余

module _ {i₁ a₁ b₁ i₂ a₂ b₂ i₃ a₃ b₃ : Level}
        {X : Mᵢ-Obj i₁ a₁ b₁} {Y : Mᵢ-Obj i₂ a₂ b₂} {Z : Mᵢ-Obj i₃ a₃ b₃}
  where

  private
    module FE-XY (x : I X) (i : I Y) =
      FE {i₁ = i₁} {a₁ = a₁} {b₁ = b₁}
         {i₂ = i₂} {a₂ = a₂} {b₂ = b₂} {X = X} {Y = Y} x i
    module FE-YZ (y : I Y) (i : I Z) =
      FE {i₁ = i₂} {a₁ = a₂} {b₁ = b₂}
         {i₂ = i₃} {a₂ = a₃} {b₂ = b₃} {X = Y} {Y = Z} y i
    module FE-XZ (x : I X) (i : I Z) =
      FE {i₁ = i₁} {a₁ = a₁} {b₁ = b₁}
         {i₂ = i₃} {a₂ = a₃} {b₂ = b₃} {X = X} {Y = Z} x i

    -- Naturality of a morphism's contravariant position with respect to
    -- a shape equality at a fixed target index; refl on independent
    -- shape variables.
    --
    -- 态射反变位置在固定目标索引处对形状等式的自然性；对独立形状
    -- 变量为 refl。
    pos-nat-shape : (G : Mᵢ-⇒ Y Z) (y : I Y)
      → ∀ {b₁ b₂ : A Y y} (s : b₁ ≡ b₂)
          (qZ : B Z (idx G y) (shape G y b₁))
      → subst (B Y y) s (pos G y b₁ qZ)
        ≡ pos G y b₂
            (subst (B Z (idx G y)) (cong (shape G y) s) qZ)
    pos-nat-shape G y refl qZ = refl

  private
    comp-fibʳ : (F : Mᵢ-⇒ X Y) (x : I X) {i : I Z}
              → Fiber {X = Y} {Y = Z} (idx F x) i
              → Fiber {X = X} {Y = Z} x i
    comp-fibʳ F x γ = record
      { shp = λ ax → Fiber.shp γ (shape F x ax)
      ; pso = λ ax qZ → pos F x ax (Fiber.pso γ (shape F x ax) qZ)
      }

    comp-fibˡ : (G : Mᵢ-⇒ Y Z) (x : I X) {y : I Y}
              → Fiber {X = X} {Y = Y} x y
              → Fiber {X = X} {Y = Z} x (idx G y)
    comp-fibˡ G x {y = y} δ = record
      { shp = λ ax → shape G y (Fiber.shp δ ax)
      ; pso = λ ax qZ → Fiber.pso δ ax (pos G y (Fiber.shp δ ax) qZ)
      }

  respʳ-fib : {F : Mᵢ-⇒ X Y}
              (x : I X)
              {i j : I Z} (e : i ≡ j)
              (α : Fiber {X = Y} {Y = Z} (idx F x) i)
              (β : Fiber {X = Y} {Y = Z} (idx F x) j)
            → FE-YZ._≈sr_ (idx F x) i α (fiber-tr (sym e) β)
            → FE-XZ._≈sr_ x i
                (comp-fibʳ F x α)
                (fiber-tr (sym e) (comp-fibʳ F x β))
  respʳ-fib {F = F} x refl α β
            record { shape-eq = se ; position-eq = pe } =
    record
      { shape-eq    = λ ax → se (shape F x ax)
      ; position-eq = λ ax qZ →
          cong (pos F x ax) (pe (shape F x ax) qZ)
      }

  respˡ-fib : {G : Mᵢ-⇒ Y Z}
              (x : I X)
              {y₁ y₂ : I Y} (e : y₁ ≡ y₂)
              (α : Fiber {X = X} {Y = Y} x y₁)
              (β : Fiber {X = X} {Y = Y} x y₂)
            → FE-XY._≈sr_ x y₁ α (fiber-tr (sym e) β)
            → FE-XZ._≈sr_ x (idx G y₁)
                (comp-fibˡ G x α)
                (fiber-tr (sym (cong (idx G) e)) (comp-fibˡ G x β))
  respˡ-fib {G = G} x {y} refl α β
            record { shape-eq = se ; position-eq = pe } =
    record
      { shape-eq    = λ ax → cong (shape G y) (se ax)
      ; position-eq = λ ax qZ →
          trans (pe ax (pos G y (Fiber.shp α ax) qZ))
                (cong (Fiber.pso β ax)
                      (pos-nat-shape G y (se ax) qZ))
      }

  ∘ᵢ-resp-≈ʳ : {G₁ G₂ : Mᵢ-⇒ Y Z} {F : Mᵢ-⇒ X Y}
             → Mᵢ-≈ G₁ G₂ → Mᵢ-≈ (G₁ ∘ᵢ F) (G₂ ∘ᵢ F)
  ∘ᵢ-resp-≈ʳ {G₁ = G₁} {G₂ = G₂} {F = F} eqG x
    with eqG (idx F x)
  ... | e , hG =
      e , respʳ-fib {F = F} x e
            (fiber-of G₁ (idx F x)) (fiber-of G₂ (idx F x)) hG

  ∘ᵢ-resp-≈ˡ : {F₁ F₂ : Mᵢ-⇒ X Y} {G : Mᵢ-⇒ Y Z}
             → Mᵢ-≈ F₁ F₂ → Mᵢ-≈ (G ∘ᵢ F₁) (G ∘ᵢ F₂)
  ∘ᵢ-resp-≈ˡ {F₁ = F₁} {F₂ = F₂} {G = G} eqF x
    with eqF x
  ... | e , hF =
      cong (idx G) e ,
        respˡ-fib {G = G} x e (fiber-of F₁ x) (fiber-of F₂ x) hF

  ∘ᵢ-resp-≈ : {F₁ F₂ : Mᵢ-⇒ X Y} {G₁ G₂ : Mᵢ-⇒ Y Z}
            → Mᵢ-≈ G₁ G₂ → Mᵢ-≈ F₁ F₂
            → Mᵢ-≈ (G₁ ∘ᵢ F₁) (G₂ ∘ᵢ F₂)
  ∘ᵢ-resp-≈ {F₁ = F₁} {F₂ = F₂} {G₁ = G₁} {G₂ = G₂} eqG eqF =
    Mᵢ-≈-trans
      {i₁ = i₁} {a₁ = a₁} {b₁ = b₁}
      {i₂ = i₃} {a₂ = a₃} {b₂ = b₃}
      {X = X} {Y = Z}
      {f = G₁ ∘ᵢ F₁}
      {g = G₁ ∘ᵢ F₂}
      {h = G₂ ∘ᵢ F₂}
      (∘ᵢ-resp-≈ˡ {F₁ = F₁} {F₂ = F₂} {G = G₁} eqF)
      (∘ᵢ-resp-≈ʳ {G₁ = G₁} {G₂ = G₂} {F = F₂} eqG)

------------------------------------------------------------------------
-- Category laws
--
-- 范畴定律

module _ {i a b} {W X Y Z : Mᵢ-Obj i a b}
         {f : Mᵢ-⇒ W X} {g : Mᵢ-⇒ X Y} {h : Mᵢ-⇒ Y Z} where

  private
    module FE-WZ (x : I W) (k : I Z) =
      FE {i₁ = i} {a₁ = a} {b₁ = b}
         {i₂ = i} {a₂ = a} {b₂ = b} {X = W} {Y = Z} x k

  ∘ᵢ-assoc : Mᵢ-≈ ((h ∘ᵢ g) ∘ᵢ f) (h ∘ᵢ (g ∘ᵢ f))
  ∘ᵢ-assoc x = refl , FE-WZ.≈sr-refl x _

  ∘ᵢ-sym-assoc : Mᵢ-≈ (h ∘ᵢ (g ∘ᵢ f)) ((h ∘ᵢ g) ∘ᵢ f)
  ∘ᵢ-sym-assoc x = refl , FE-WZ.≈sr-refl x _

module _ {i a b} {X Y : Mᵢ-Obj i a b} {f : Mᵢ-⇒ X Y} where

  private
    module FE-XY (x : I X) (k : I Y) =
      FE {i₁ = i} {a₁ = a} {b₁ = b}
         {i₂ = i} {a₂ = a} {b₂ = b} {X = X} {Y = Y} x k

  ∘ᵢ-identityˡ : Mᵢ-≈ (idᵢ ∘ᵢ f) f
  ∘ᵢ-identityˡ x = refl , FE-XY.≈sr-refl x _

  ∘ᵢ-identityʳ : Mᵢ-≈ (f ∘ᵢ idᵢ) f
  ∘ᵢ-identityʳ x = refl , FE-XY.≈sr-refl x _

module _ {i a b} {X : Mᵢ-Obj i a b} where

  private
    -- Rigid monomorphic identity, anchoring the implicit object and
    -- level arguments of Mᵢ-≈.
    --
    -- 刚性单态恒等，为 Mᵢ-≈ 的隐式对象与层级参数提供锚点。
    idX : Mᵢ-⇒ X X
    idX = idᵢ

    module FE-XX (x : I X) (k : I X) =
      FE {i₁ = i} {a₁ = a} {b₁ = b}
         {i₂ = i} {a₂ = a} {b₂ = b} {X = X} {Y = X} x k

  ∘ᵢ-identity² : Mᵢ-≈ (idX ∘ᵢ idX) idX
  ∘ᵢ-identity² x = refl , FE-XX.≈sr-refl x _

------------------------------------------------------------------------
-- Same-universe monomorphic aliases
--
-- 同宇宙单态别名

private
  Hom : (i a b : Level)
      → Mᵢ-Obj i a b → Mᵢ-Obj i a b → Set (i ⊔ a ⊔ b)
  Hom i a b X Y =
    Mᵢ-⇒ {i₁ = i} {a₁ = a} {b₁ = b}
         {i₂ = i} {a₂ = a} {b₂ = b} X Y

  Eq : (i a b : Level) {X Y : Mᵢ-Obj i a b}
     → Hom i a b X Y → Hom i a b X Y → Set (i ⊔ a ⊔ b)
  Eq i a b {X = X} {Y = Y} f g =
    Mᵢ-≈ {i₁ = i} {a₁ = a} {b₁ = b}
         {i₂ = i} {a₂ = a} {b₂ = b} {X = X} {Y = Y} f g

  id₀ : (i a b : Level) {X : Mᵢ-Obj i a b} → Hom i a b X X
  id₀ i a b {X = X} = idᵢ {i = i} {a = a} {b = b} {X = X}

  comp₀ : (i a b : Level) {X Y Z : Mᵢ-Obj i a b}
        → Hom i a b Y Z → Hom i a b X Y → Hom i a b X Z
  comp₀ i a b {X = X} {Y = Y} {Z = Z} g f =
    _∘ᵢ_ {i₁ = i} {a₁ = a} {b₁ = b}
         {i₂ = i} {a₂ = a} {b₂ = b}
         {i₃ = i} {a₃ = a} {b₃ = b}
         {X = X} {Y = Y} {Z = Z} g f

------------------------------------------------------------------------
-- The category MᵢCat
--
-- 范畴 MᵢCat

MᵢCat : (i a b : Level) → Category (lsuc (i ⊔ a ⊔ b)) (i ⊔ a ⊔ b) (i ⊔ a ⊔ b)
MᵢCat i a b = record
  { Obj       = Mᵢ-Obj i a b
  ; _⇒_       = Hom i a b
  ; _≈_       = Eq i a b
  ; id        = id₀ i a b
  ; _∘_       = comp₀ i a b
  ; equiv     = λ {X} {Y} → Mᵢ-≈-isEquivalence {X = X} {Y = Y}
  ; ∘-resp-≈  = λ {X} {Y} {Z} {f} {h} {g} {k} → ∘ᵢ-resp-≈ {X = X} {Y = Y} {Z = Z}
                  {F₁ = g} {F₂ = k} {G₁ = f} {G₂ = h}
  ; assoc     = λ {W} {X} {Y} {Z} {f} {g} {h} → ∘ᵢ-assoc {W = W} {X = X} {Y = Y} {Z = Z}
                  {f = f} {g = g} {h = h}
  ; sym-assoc = λ {W} {X} {Y} {Z} {f} {g} {h} → ∘ᵢ-sym-assoc {W = W} {X = X} {Y = Y} {Z = Z}
                  {f = f} {g = g} {h = h}
  ; identityˡ = λ {X} {Y} {f} → ∘ᵢ-identityˡ {X = X} {Y = Y} {f = f}
  ; identityʳ = λ {X} {Y} {f} → ∘ᵢ-identityʳ {X = X} {Y = Y} {f = f}
  ; identity² = λ {X} → ∘ᵢ-identity² {X = X}
  }

------------------------------------------------------------------------
-- The ordinary container category as the trivial specialisation I = ⊤
--
-- 普通容器范畴，即 I = ⊤ 的平凡特化

module Container-Specialization (i a b : Level) where

  trivial-Mᵢ : (S : Set a) → (S → Set b) → Mᵢ-Obj i a b
  trivial-Mᵢ S P = record
    { I    = ⊤ {i}
    ; A    = λ _ → S
    ; B    = λ _ s → P s
    ; next = λ _ _ _ → tt {i}
    ; root = tt {i}
    }

  ContObj : Set (lsuc (a ⊔ b))
  ContObj = Σ (Set a) (λ S → S → Set b)

  Cont⇒ : (X Y : ContObj) → Set (i ⊔ a ⊔ b)
  Cont⇒ X Y =
    let SX = proj₁ X ; PX = proj₂ X
        SY = proj₁ Y ; PY = proj₂ Y
    in Mᵢ-⇒ (trivial-Mᵢ SX PX) (trivial-Mᵢ SY PY)

  Cont-≈ : {X Y : ContObj} → Cont⇒ X Y → Cont⇒ X Y → Set (i ⊔ a ⊔ b)
  Cont-≈ {X = X} {Y = Y} f g = Mᵢ-≈ f g

  ContCat : Category (lsuc (i ⊔ a ⊔ b)) (i ⊔ a ⊔ b) (i ⊔ a ⊔ b)
  ContCat = MᵢCat i a b

------------------------------------------------------------------------
-- The container final coalgebra at I = ⊤
--
-- I = ⊤ 处的容器终余代数

module _ {i a b : Level} (S : Set a) (P : S → Set b) where
  open Container-Specialization i a b

  ContainerCoalg : Set (a ⊔ b)
  ContainerCoalg =
    Mᵢ {I = ⊤ {i}} (λ _ → S) (λ _ s → P s)
                    (λ _ _ _ → tt {i}) (tt {i})

  out : ContainerCoalg → Σ S (λ s → P s → ContainerCoalg)
  out c = fst c , λ q → snd c q

  ana : ∀ {c} {X : Set c}
      → (X → Σ S (λ s → P s → X)) → X → ContainerCoalg
  ana γ x .fst = proj₁ (γ x)
  ana γ x .snd q = ana γ (proj₂ (γ x) q)
