------------------------------------------------------------------------
-- Bridging FullyFaithful + EssSurj to StrongEquivalence
--
-- Given a fully faithful, split essentially surjective functor
-- F : C → D, this module builds the inverse functor G : D → C
-- explicitly, the natural isomorphisms F ∘ G ≃ id and G ∘ F ≃ id, and
-- assembles them into a StrongEquivalence record.
--
-- 从 FullyFaithful + EssSurj 桥接到 StrongEquivalence
--
-- 给定完全忠实、分裂本质满射的函子 F : C → D，本模块显式构造逆函子
-- G : D → C、自然同构 F ∘ G ≃ id 与 G ∘ F ≃ id，并组装为
-- StrongEquivalence 记录。
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module Equivalence.StrongEquiv where

open import Agda.Primitive using (Level)
open import Data.Product.Base using (proj₁; proj₂)

open import Categories.Category.Core using (Category)
open import Categories.Category.Equivalence using (StrongEquivalence)
open import Categories.Functor.Core using (Functor)
open import Categories.Functor using (id; _∘F_)
open import Categories.Functor.Properties using
  (FullyFaithful; Full; Faithful; EssentiallySurjective; EssSurj×Full×Faithful⇒Invertible)
open import Categories.NaturalTransformation.Core using (ntHelper)
open import Categories.NaturalTransformation.NaturalIsomorphism using (NaturalIsomorphism)
open import Categories.Morphism using (_≅_; Iso)

module _ {oc ℓc ec od ℓd ed : Level}
         {C : Category oc ℓc ec}
         {D : Category od ℓd ed}
         (F : Functor C D)
         (ff : FullyFaithful F)
         (ses : EssentiallySurjective F) where

  module C = Category C
  module D = Category D
  module Fm = Functor F

  open D.HomReasoning

  full : Full F
  full = proj₁ ff

  faithful : Faithful F
  faithful = proj₂ ff

  G : Functor D C
  G = EssSurj×Full×Faithful⇒Invertible F ses full faithful

  module Gm = Functor G

  -- D is written explicitly because _≅_ takes three parameters:
  -- category, source, target.
  --
  -- D 显式写出，因为 _≅_ 需要三个参数：范畴、源、靶。
  isoAt : (Y : Category.Obj D) → _≅_ D (Fm.F₀ (Gm.F₀ Y)) Y
  isoAt Y = proj₂ (ses Y)

  fwd : (Y : Category.Obj D) → Fm.F₀ (Gm.F₀ Y) D.⇒ Y
  fwd Y = _≅_.from (isoAt Y)

  bwd : (Y : Category.Obj D) → Y D.⇒ Fm.F₀ (Gm.F₀ Y)
  bwd Y = _≅_.to (isoAt Y)

  isoAt-fwd-bwd : (Y : Category.Obj D) → fwd Y D.∘ bwd Y D.≈ D.id
  isoAt-fwd-bwd Y = Iso.isoʳ (_≅_.iso (isoAt Y))

  isoAt-bwd-fwd : (Y : Category.Obj D) → bwd Y D.∘ fwd Y D.≈ D.id
  isoAt-bwd-fwd Y = Iso.isoˡ (_≅_.iso (isoAt Y))

  -- Essential characterisation of G₁: it factors through the chosen
  -- isomorphism F (G Y) ≅ Y. This is the key lemma driving all
  -- subsequent naturality and inverse proofs.
  --
  -- G₁ 的本质刻画：它经由所选同构 F (G Y) ≅ Y 分解。这是驱动后续
  -- 所有自然性与逆证明的关键引理。
  F₁G₁-char : ∀ {Y Z} (f : Y D.⇒ Z)
            → Fm.F₁ (Gm.F₁ f) D.≈ bwd Z D.∘ (f D.∘ fwd Y)
  F₁G₁-char {Y} {Z} f = proj₂ (full (bwd Z D.∘ (f D.∘ fwd Y)))

  FG-comm : ∀ {Y Z} (f : Y D.⇒ Z)
          → fwd Z D.∘ Fm.F₁ (Gm.F₁ f) D.≈ f D.∘ fwd Y
  FG-comm {Y} {Z} f = begin
    fwd Z D.∘ Fm.F₁ (Gm.F₁ f)
      ≈⟨ D.∘-resp-≈ʳ (F₁G₁-char f) ⟩
    fwd Z D.∘ (bwd Z D.∘ (f D.∘ fwd Y))
      ≈˘⟨ D.assoc ⟩
    (fwd Z D.∘ bwd Z) D.∘ (f D.∘ fwd Y)
      ≈⟨ D.∘-resp-≈ˡ (isoAt-fwd-bwd Z) ⟩
    D.id D.∘ (f D.∘ fwd Y)
      ≈⟨ D.identityˡ ⟩
    f D.∘ fwd Y
      ∎

  FG-comm⁻¹ : ∀ {Y Z} (f : Y D.⇒ Z)
            → bwd Z D.∘ f D.≈ Fm.F₁ (Gm.F₁ f) D.∘ bwd Y
  FG-comm⁻¹ {Y} {Z} f = begin
    bwd Z D.∘ f
      ≈˘⟨ D.∘-resp-≈ʳ D.identityʳ ⟩
    bwd Z D.∘ (f D.∘ D.id)
      ≈˘⟨ D.∘-resp-≈ʳ (D.∘-resp-≈ʳ (isoAt-fwd-bwd Y)) ⟩
    bwd Z D.∘ (f D.∘ (fwd Y D.∘ bwd Y))
      ≈⟨ D.∘-resp-≈ʳ (D.sym-assoc {f = bwd Y} {g = fwd Y} {h = f}) ⟩
    bwd Z D.∘ ((f D.∘ fwd Y) D.∘ bwd Y)
      ≈˘⟨ D.assoc ⟩
    (bwd Z D.∘ (f D.∘ fwd Y)) D.∘ bwd Y
      ≈˘⟨ D.∘-resp-≈ˡ (F₁G₁-char f) ⟩
    Fm.F₁ (Gm.F₁ f) D.∘ bwd Y
      ∎

  F∘G≃id : NaturalIsomorphism (F ∘F G) id
  F∘G≃id = record
    { F⇒G = ntHelper record
      { η       = λ Y → fwd Y
      ; commute = λ {Y} {Z} f → FG-comm f
      }
    ; F⇐G = ntHelper record
      { η       = λ Y → bwd Y
      ; commute = λ {Y} {Z} f → FG-comm⁻¹ f
      }
    ; iso = λ Y → _≅_.iso (isoAt Y)
    }

  GF-fwd : ∀ X → Gm.F₀ (Fm.F₀ X) C.⇒ X
  GF-fwd X = proj₁ (full (fwd (Fm.F₀ X)))

  GF-fwd-comm : ∀ X → Fm.F₁ (GF-fwd X) D.≈ fwd (Fm.F₀ X)
  GF-fwd-comm X = proj₂ (full (fwd (Fm.F₀ X)))

  GF-bwd : ∀ X → X C.⇒ Gm.F₀ (Fm.F₀ X)
  GF-bwd X = proj₁ (full (bwd (Fm.F₀ X)))

  GF-bwd-comm : ∀ X → Fm.F₁ (GF-bwd X) D.≈ bwd (Fm.F₀ X)
  GF-bwd-comm X = proj₂ (full (bwd (Fm.F₀ X)))

  -- Absorb the round-trip fwd Z ∘ bwd Z on the left.
  --
  -- 在左侧吸收往返 fwd Z ∘ bwd Z。
  fwd-bwd-absorb : ∀ {W Z} (g : W D.⇒ Z)
                 → fwd Z D.∘ (bwd Z D.∘ g) D.≈ g
  fwd-bwd-absorb {Z = Z} g = begin
    fwd Z D.∘ (bwd Z D.∘ g)
      ≈˘⟨ D.assoc ⟩
    (fwd Z D.∘ bwd Z) D.∘ g
      ≈⟨ D.∘-resp-≈ˡ (isoAt-fwd-bwd Z) ⟩
    D.id D.∘ g
      ≈⟨ D.identityˡ ⟩
    g
      ∎

  -- Absorb the round-trip fwd W ∘ bwd W on the right.
  --
  -- 在右侧吸收往返 fwd W ∘ bwd W。
  bwd-fwd-absorb : ∀ {W Z} (g : W D.⇒ Z)
                 → (g D.∘ fwd W) D.∘ bwd W D.≈ g
  bwd-fwd-absorb {W = W} g = begin
    (g D.∘ fwd W) D.∘ bwd W
      ≈⟨ D.assoc ⟩
    g D.∘ (fwd W D.∘ bwd W)
      ≈⟨ D.∘-resp-≈ʳ (isoAt-fwd-bwd W) ⟩
    g D.∘ D.id
      ≈⟨ D.identityʳ ⟩
    g
      ∎

  GF-isoˡ : ∀ X → GF-fwd X C.∘ GF-bwd X C.≈ C.id
  GF-isoˡ X = faithful (begin
    Fm.F₁ (GF-fwd X C.∘ GF-bwd X)
      ≈⟨ Fm.homomorphism ⟩
    Fm.F₁ (GF-fwd X) D.∘ Fm.F₁ (GF-bwd X)
      ≈⟨ D.∘-resp-≈ (GF-fwd-comm X) (GF-bwd-comm X) ⟩
    fwd (Fm.F₀ X) D.∘ bwd (Fm.F₀ X)
      ≈⟨ isoAt-fwd-bwd (Fm.F₀ X) ⟩
    D.id
      ≈˘⟨ Fm.identity ⟩
    Fm.F₁ C.id
      ∎)

  GF-isoʳ : ∀ X → GF-bwd X C.∘ GF-fwd X C.≈ C.id
  GF-isoʳ X = faithful (begin
    Fm.F₁ (GF-bwd X C.∘ GF-fwd X)
      ≈⟨ Fm.homomorphism ⟩
    Fm.F₁ (GF-bwd X) D.∘ Fm.F₁ (GF-fwd X)
      ≈⟨ D.∘-resp-≈ (GF-bwd-comm X) (GF-fwd-comm X) ⟩
    bwd (Fm.F₀ X) D.∘ fwd (Fm.F₀ X)
      ≈⟨ isoAt-bwd-fwd (Fm.F₀ X) ⟩
    D.id
      ≈˘⟨ Fm.identity ⟩
    Fm.F₁ C.id
      ∎)

  -- Naturality of G∘F ≅ id, proved via faithfulness.
  --
  -- G∘F ≅ id 的自然性，经忠实性证明。
  GF-comm : ∀ {X Y} (f : X C.⇒ Y)
          → GF-fwd Y C.∘ Gm.F₁ (Fm.F₁ f) C.≈ f C.∘ GF-fwd X
  GF-comm {X} {Y} f = faithful (begin
    Fm.F₁ (GF-fwd Y C.∘ Gm.F₁ (Fm.F₁ f))
      ≈⟨ Fm.homomorphism ⟩
    Fm.F₁ (GF-fwd Y) D.∘ Fm.F₁ (Gm.F₁ (Fm.F₁ f))
      ≈⟨ D.∘-resp-≈ (GF-fwd-comm Y) (F₁G₁-char (Fm.F₁ f)) ⟩
    fwd (Fm.F₀ Y) D.∘ (bwd (Fm.F₀ Y) D.∘ (Fm.F₁ f D.∘ fwd (Fm.F₀ X)))
      ≈⟨ fwd-bwd-absorb (Fm.F₁ f D.∘ fwd (Fm.F₀ X)) ⟩
    Fm.F₁ f D.∘ fwd (Fm.F₀ X)
      ≈˘⟨ D.∘-resp-≈ʳ (GF-fwd-comm X) ⟩
    Fm.F₁ f D.∘ Fm.F₁ (GF-fwd X)
      ≈˘⟨ Fm.homomorphism ⟩
    Fm.F₁ (f C.∘ GF-fwd X)
      ∎)

  GF-comm⁻¹ : ∀ {X Y} (f : X C.⇒ Y)
            → Gm.F₁ (Fm.F₁ f) C.∘ GF-bwd X C.≈ GF-bwd Y C.∘ f
  GF-comm⁻¹ {X} {Y} f = faithful (begin
    Fm.F₁ (Gm.F₁ (Fm.F₁ f) C.∘ GF-bwd X)
      ≈⟨ Fm.homomorphism ⟩
    Fm.F₁ (Gm.F₁ (Fm.F₁ f)) D.∘ Fm.F₁ (GF-bwd X)
      ≈⟨ D.∘-resp-≈ (F₁G₁-char (Fm.F₁ f)) (GF-bwd-comm X) ⟩
    (bwd (Fm.F₀ Y) D.∘ (Fm.F₁ f D.∘ fwd (Fm.F₀ X))) D.∘ bwd (Fm.F₀ X)
      ≈⟨ D.assoc ⟩
    bwd (Fm.F₀ Y) D.∘ ((Fm.F₁ f D.∘ fwd (Fm.F₀ X)) D.∘ bwd (Fm.F₀ X))
      ≈⟨ D.∘-resp-≈ʳ (bwd-fwd-absorb (Fm.F₁ f)) ⟩
    bwd (Fm.F₀ Y) D.∘ Fm.F₁ f
      ≈˘⟨ D.∘-resp-≈ˡ (GF-bwd-comm Y) ⟩
    Fm.F₁ (GF-bwd Y) D.∘ Fm.F₁ f
      ≈˘⟨ Fm.homomorphism ⟩
    Fm.F₁ (GF-bwd Y C.∘ f)
      ∎)

  G∘F≃id : NaturalIsomorphism (G ∘F F) id
  G∘F≃id = record
    { F⇒G = ntHelper record
      { η       = λ X → GF-fwd X
      ; commute = λ {X} {Y} f → GF-comm f
      }
    ; F⇐G = ntHelper record
      { η       = λ X → GF-bwd X
      ; commute = λ {X} {Y} f → C.Equiv.sym (GF-comm⁻¹ f)
      }
    ; iso = λ X → record { isoˡ = GF-isoʳ X ; isoʳ = GF-isoˡ X }
    }

  toStrongEquiv : StrongEquivalence C D
  toStrongEquiv = record
    { F            = F
    ; G            = G
    ; weak-inverse = record
      { F∘G≈id = F∘G≃id
      ; G∘F≈id = G∘F≃id
      }
    }
