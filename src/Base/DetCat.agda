------------------------------------------------------------------------
-- Category of deterministic transition systems
--
-- 确定性转移系统的范畴
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module Base.DetCat where

open import Agda.Primitive using (Level; lsuc)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality.Core using (cong; trans; sym)

open import Categories.Category.Core using (Category)

------------------------------------------------------------------------
-- Objects
--
-- Deterministic transition systems
--
-- 对象
--
-- 确定性转移系统

record DetSys (i : Level) : Set (lsuc i) where
  field
    I    : Set i
    step : I → I

open DetSys

------------------------------------------------------------------------
-- Forward semiconjugacy morphisms
--
-- Objects are pairs (I, step); a morphism X ⇒ Y is an index map q with
-- q (step X x) ≡ step Y (q x). Unlike the pull correspondences FMapˢ
-- these maps need not hit every target index, so the colimit legs of a
-- forward chain are morphisms here. Hom equality is pointwise
-- propositional equality, so no function extensionality is required
-- and the category laws hold pointwise.
--
-- 前向半共轭态射
--
-- 对象为 (I, step) 对；态射 X ⇒ Y 是满足 q (step X x) ≡ step Y (q x)
-- 的索引映射。与 pull 对应 FMapˢ 不同，这些映射不必满射到每个目标
-- 索引，故前向链的余极限腿在此是态射。hom 相等取逐点命题相等，
-- 无需函数外延，范畴律逐点成立。

record DM {i : Level} (X Y : DetSys i) : Set i where
  field
    q   : I X → I Y
    coh : (x : I X) → q (step X x) ≡ step Y (q x)

open DM

-- Pointwise hom equality
--
-- 逐点 hom 相等
_≈DM_ : ∀ {i : Level} {X Y : DetSys i} → DM X Y → DM X Y → Set i
_≈DM_ f g = ∀ x → q f x ≡ q g x

-- Identity
--
-- 恒等
idDM : ∀ {i : Level} (X : DetSys i) → DM X X
idDM X = record { q = λ x → x ; coh = λ _ → refl }

-- Composition: g after f; the coherence chains the two semiconjugacies.
--
-- 复合：g 在 f 之后；相干性串联两个半共轭等式。
compDM : ∀ {i : Level} {X Y Z : DetSys i}
       → DM Y Z → DM X Y → DM X Z
compDM {X = X} {Y = Y} {Z = Z} g f = record
  { q   = λ x → q g (q f x)
  ; coh = λ x → trans (cong (q g) (coh f x)) (coh g (q f x))
  }

assocDM : ∀ {i : Level} {W X Y Z : DetSys i}
          (h : DM Y Z) (g : DM X Y) (f : DM W X)
        → compDM (compDM h g) f ≈DM compDM h (compDM g f)
assocDM _ _ _ _ = refl

identityˡDM : ∀ {i : Level} {X Y : DetSys i} (f : DM X Y)
            → compDM (idDM Y) f ≈DM f
identityˡDM _ _ = refl

identityʳDM : ∀ {i : Level} {X Y : DetSys i} (f : DM X Y)
            → compDM f (idDM X) ≈DM f
identityʳDM _ _ = refl

------------------------------------------------------------------------
-- The category
--
-- 范畴

DetCat : (i : Level) → Category (lsuc i) i i
DetCat i = record
  { Obj       = DetSys i
  ; _⇒_       = DM {i}
  ; _≈_       = _≈DM_ {i}
  ; id        = idDM {i} _
  ; _∘_       = compDM {i}
  ; assoc     = λ {_ _ _ _ f g h} → assocDM h g f
  ; sym-assoc = λ {_ _ _ _ f g h} x → sym (assocDM h g f x)
  ; identityˡ = λ {_ _ f} → identityˡDM f
  ; identityʳ = λ {_ _ f} → identityʳDM f
  ; identity² = λ _ → refl
  ; equiv     = record
    { refl  = λ {x} _ → refl
    ; sym   = λ {x y} e z → sym (e z)
    ; trans = λ {x y z} e₁ e₂ w → trans (e₁ w) (e₂ w)
    }
  ; ∘-resp-≈  = λ {f = f} {h = h} {g = g} {i = k} efo ein z →
                  trans (cong (q f) (ein z)) (efo (q k z))
  }
