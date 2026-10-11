------------------------------------------------------------------------
-- The wide subcategory of MCorrCatˢ on identity-index carried functors
--
-- Objects are ℕ-indexed deterministic systems with a fixed successor
-- dynamics d : ℕ → ℕ; only the label fibre varies. A morphism is given
-- just by a fibre map shape and its congruence; the index map, child
-- map and edge adjunction are fixed (identity index, singleton child
-- refl, identity fibre adjunction), so the underlying FMˢ has a
-- definitionally identity index. Morphism equality is the pointwise
-- label-tree bisimulation with no index path and no transport. This is
-- the range in which the nchain push colimit mediating functor is total
-- and unique: every cocone leg follows the identity trajectory, so the
-- non-surjective index obstruction of ColimitPolarity cannot arise.
--
-- MCorrCatˢ 在“索引恒等”携带函子上的宽子范畴
--
-- 对象是以固定后继动力 d : ℕ → ℕ 的 ℕ 索引确定性系统，只有标签纤维可变。
-- 态射仅由纤维映射 shape 及其同余给出；索引映射、子节点映射与边伴随均
-- 固定（索引恒等、单子节点 refl、恒等纤维伴随），故底层 FMˢ 的索引定义性
-- 为恒等。态射相等是逐点标签树互模拟，不含索引路径、不含传输。这正是
-- nchain push 余极限 mediate 函子全且唯一的范围：每条余锥腿沿恒等轨迹，
-- 不会出现 ColimitPolarity 的索引非满射障碍。
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module ALMA.Cosmos.Carried.SameIndexCatS where

open import Agda.Primitive using (Level; lzero; lsuc)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Sigma using (Σ; _,_)
open import Data.Unit.Polymorphic.Base using (⊤; tt)
open import Data.Nat.Base using (ℕ)
open import Relation.Binary.Structures using (IsEquivalence)

open import Categories.Category.Core using (Category)

open import ALMA.Base.MCorr using (M)
open import ALMA.Base.MCorrSetoid using
  (SysEq; EqOn; propEqOn; idAdjˢ; _≈Mˢ_; ≈Mˢ-refl; ≈Mˢ-sym; ≈Mˢ-trans)
open import ALMA.Base.MCorrSetoidCat using (FMapˢ; FMˢ)

open SysEq

------------------------------------------------------------------------
-- An object
--
-- A label family over ℕ together with its fibre setoid.
--
-- 对象
--
-- ℕ 上的标签族及其纤维 setoid。

record LabelSys (ℓ : Level) : Set (lsuc ℓ) where
  field
    A₀   : ℕ → Set ℓ
    ≈A₀  : (v : ℕ) → EqOn {ℓ = ℓ} (A₀ v)
open LabelSys public

-- The deterministic system for a label family under dynamics d.
--
-- 动力 d 下标签族对应的确定性系统。
dsys : (d : ℕ → ℕ) {ℓ : Level} (X : LabelSys ℓ)
     → SysEq lzero ℓ lzero ℓ lzero
dsys d X = record
  { I  = ℕ
  ; A  = A₀ X
  ; E  = λ v _ w → Σ (⊤ {lzero}) λ _ → w ≡ d v
  ; ≈A = ≈A₀ X
  ; ≈E = λ v _ w → propEqOn (Σ (⊤ {lzero}) λ _ → w ≡ d v)
  }

------------------------------------------------------------------------
-- Identity-index carried functors and the wide subcategory
--
-- 索引恒等携带函子与宽子范畴

module _ (d : ℕ → ℕ) {ℓ : Level} where

  private
    s = dsys d

  -- The generic identity-index FMˢ for a fibre map and its congruence.
  --
  -- 纤维映射及其同余对应的通用索引恒等 FMˢ。
  idxFM : (X Y : LabelSys ℓ)
          (sh : (v : ℕ) → A₀ X v → A₀ Y v)
          (shc : ∀ {v : ℕ} {a a' : A₀ X v}
               → EqOn._≈_ (≈A₀ X v) a a'
               → EqOn._≈_ (≈A₀ Y v) (sh v a) (sh v a'))
        → FMˢ (s X) (s Y)
  idxFM X Y sh shc = record
    { mor        = fmor
    ; shape-cong = λ e → shc e
    ; map-cong   = go
    }
    where
    fmor : FMapˢ (s X) (s Y)
    fmor = record
      { u      = λ v → v
      ; shape  = sh
      ; childF = λ v _ w → w , refl
      ; adjFˢ  = λ v a w → idAdjˢ (≈E (s Y) v (sh v a) w)
      }
    mutual
      go : ∀ {v : ℕ} {t t' : M (A (s X)) (E (s X)) v}
         → _≈Mˢ_ (≈A (s X)) (≈E (s X)) t t'
         → _≈Mˢ_ (≈A (s Y)) (≈E (s Y))
                  (FMapˢ.mapFˢ fmor v t) (FMapˢ.mapFˢ fmor v t')
      go p ._≈Mˢ_.here-eq = shc (_≈Mˢ_.here-eq p)
      go p ._≈Mˢ_.below-eq w =
        let adj , fs = _≈Mˢ_.below-eq p w
            fwd , bwd = fs
        in adj , ((λ e₁ → go (fwd e₁)) , (λ e₂ → go (bwd e₂)))

  -- A morphism is a fibre map and its congruence; the FMˢ is derived.
  --
  -- 态射即纤维映射及其同余；FMˢ 由此导出。
  record Idx⇒ (X Y : LabelSys ℓ) : Set ℓ where
    field
      shape      : (v : ℕ) → A₀ X v → A₀ Y v
      shape-cong : ∀ {v : ℕ} {a a' : A₀ X v}
                 → EqOn._≈_ (≈A₀ X v) a a'
                 → EqOn._≈_ (≈A₀ Y v) (shape v a) (shape v a')
    mor : FMˢ (s X) (s Y)
    mor = idxFM X Y shape shape-cong
  open Idx⇒ public

  ----------------------------------------------------------------------
  -- Identity and composition at the fibre-map level
  --
  -- 纤维映射层面的恒等与复合

  idxi : (X : LabelSys ℓ) → Idx⇒ X X
  idxi X = record
    { shape      = λ _ a → a
    ; shape-cong = λ e → e
    }

  compi : {X Y Z : LabelSys ℓ} → Idx⇒ Y Z → Idx⇒ X Y → Idx⇒ X Z
  compi g f = record
    { shape      = λ v a → shape g v (shape f v a)
    ; shape-cong = λ e → shape-cong g (shape-cong f e)
    }

  ----------------------------------------------------------------------
  -- Morphism equality
  --
  -- Pointwise label-tree bisimulation, no path.
  --
  -- 态射相等
  --
  -- 逐点标签树互模拟，无路径。

  _≈i_ : {X Y : LabelSys ℓ} → Idx⇒ X Y → Idx⇒ X Y → Set ℓ
  _≈i_ {X = X} {Y = Y} f g =
    ∀ (v : ℕ) (t : M (A (s X)) (E (s X)) v)
    → _≈Mˢ_ (≈A (s Y)) (≈E (s Y))
             (FMapˢ.mapFˢ (FMˢ.mor (mor f)) v t)
             (FMapˢ.mapFˢ (FMˢ.mor (mor g)) v t)

  ≈i-refl : {X Y : LabelSys ℓ} (f : Idx⇒ X Y) → f ≈i f
  ≈i-refl {Y = Y} f v t =
    ≈Mˢ-refl (≈A (s Y)) (≈E (s Y))
      (FMapˢ.mapFˢ (FMˢ.mor (mor f)) v t)

  ≈i-sym : {X Y : LabelSys ℓ} {f g : Idx⇒ X Y} → f ≈i g → g ≈i f
  ≈i-sym {Y = Y} p v t =
    ≈Mˢ-sym (≈A (s Y)) (≈E (s Y)) (p v t)

  ≈i-trans : {X Y : LabelSys ℓ} {f g h : Idx⇒ X Y}
           → f ≈i g → g ≈i h → f ≈i h
  ≈i-trans {Y = Y} p q v t =
    ≈Mˢ-trans (≈A (s Y)) (≈E (s Y)) (p v t) (q v t)

  ≈i-isEquivalence : {X Y : LabelSys ℓ} → IsEquivalence (_≈i_ {X} {Y})
  ≈i-isEquivalence = record
    { refl  = λ {f} → ≈i-refl f
    ; sym   = λ {f g} → ≈i-sym {f = f} {g = g}
    ; trans = λ {f g h} → ≈i-trans {f = f} {g = g} {h = h}
    }

  ----------------------------------------------------------------------
  -- Composition respects pointwise bisimilarity
  --
  -- The head labels are forced by the two congruences; the child trees
  -- recurse guardedly.
  --
  -- 复合尊重逐点互模拟
  --
  -- 头标签由两个同余强制，子树守卫递归。
  ∘-resp-≈i : {X Y Z : LabelSys ℓ}
              {F₁ F₂ : Idx⇒ X Y} {G₁ G₂ : Idx⇒ Y Z}
            → F₁ ≈i F₂ → G₁ ≈i G₂
            → compi G₁ F₁ ≈i compi G₂ F₂
  ∘-resp-≈i {X = X} {Y = Y} {Z = Z}
            {F₁ = F₁} {F₂ = F₂} {G₁ = G₁} {G₂ = G₂} eqF eqG = go
    where
    mutual
      go : (v : ℕ) (t : M (A (s X)) (E (s X)) v)
         → _≈Mˢ_ (≈A (s Z)) (≈E (s Z))
                  (FMapˢ.mapFˢ (FMˢ.mor (mor (compi G₁ F₁))) v t)
                  (FMapˢ.mapFˢ (FMˢ.mor (mor (compi G₂ F₂))) v t)
      go v t ._≈Mˢ_.here-eq =
        EqOn.trans (≈A (s Z) v)
          (shape-cong G₁ (_≈Mˢ_.here-eq (eqF v t)))
          (_≈Mˢ_.here-eq
            (eqG v (FMapˢ.mapFˢ (FMˢ.mor (mor F₂)) v t)))
      go v t ._≈Mˢ_.below-eq w =
          idAdjˢ (propEqOn (Σ (⊤ {lzero}) λ _ → w ≡ d v))
        , ( (λ e₁ → go w (M.below t w e₁))
          , (λ e₂ → go˘ w (M.below t w e₂)) )

      go˘ : (v : ℕ) (t : M (A (s X)) (E (s X)) v)
          → _≈Mˢ_ (≈A (s Z)) (≈E (s Z))
                   (FMapˢ.mapFˢ (FMˢ.mor (mor (compi G₂ F₂))) v t)
                   (FMapˢ.mapFˢ (FMˢ.mor (mor (compi G₁ F₁))) v t)
      go˘ v t ._≈Mˢ_.here-eq =
        EqOn.trans (≈A (s Z) v)
          (EqOn.sym (≈A (s Z) v)
            (_≈Mˢ_.here-eq
              (eqG v (FMapˢ.mapFˢ (FMˢ.mor (mor F₂)) v t))))
          (EqOn.sym (≈A (s Z) v)
            (shape-cong G₁ (_≈Mˢ_.here-eq (eqF v t))))
      go˘ v t ._≈Mˢ_.below-eq w =
          idAdjˢ (propEqOn (Σ (⊤ {lzero}) λ _ → w ≡ d v))
        , ( (λ e₁ → go˘ w (M.below t w e₁))
          , (λ e₂ → go w (M.below t w e₂)) )

  ----------------------------------------------------------------------
  -- Pointwise lifting
  --
  -- Head equations in the target's own setoid (any setoid, not only a
  -- propositional fibre) give morphism bisimilarity; child trees recurse
  -- guardedly along the identity index.
  --
  -- 逐点提升
  --
  -- 目标自身 setoid（任意 setoid，不限于命题纤维）中的头部等式给出态射
  -- 互模拟；子树沿恒等索引守卫递归。
  pointwise-i : {X Y : LabelSys ℓ} (f g : Idx⇒ X Y)
    → (∀ (v : ℕ) (a : A₀ X v)
        → EqOn._≈_ (≈A₀ Y v) (shape f v a) (shape g v a))
    → f ≈i g
  pointwise-i {X = X} {Y = Y} f g eq v t = go v t
    where
    edgeAdj : (v w : ℕ) → _
    edgeAdj v w = idAdjˢ (propEqOn (Σ (⊤ {lzero}) λ _ → w ≡ d v))
    mutual
      go : (v : ℕ) (u : M (A (s X)) (E (s X)) v)
         → _≈Mˢ_ (≈A (s Y)) (≈E (s Y))
                  (FMapˢ.mapFˢ (FMˢ.mor (mor f)) v u)
                  (FMapˢ.mapFˢ (FMˢ.mor (mor g)) v u)
      go v u ._≈Mˢ_.here-eq = eq v (M.here u)
      go v u ._≈Mˢ_.below-eq w =
        edgeAdj v w
          , ( (λ e → go w (M.below u w e))
            , (λ e → go˘ w (M.below u w e)) )

      go˘ : (v : ℕ) (u : M (A (s X)) (E (s X)) v)
          → _≈Mˢ_ (≈A (s Y)) (≈E (s Y))
                   (FMapˢ.mapFˢ (FMˢ.mor (mor g)) v u)
                   (FMapˢ.mapFˢ (FMˢ.mor (mor f)) v u)
      go˘ v u ._≈Mˢ_.here-eq =
        EqOn.sym (≈A (s Y) v) (eq v (M.here u))
      go˘ v u ._≈Mˢ_.below-eq w =
        edgeAdj v w
          , ( (λ e → go˘ w (M.below u w e))
            , (λ e → go w (M.below u w e)) )

  ----------------------------------------------------------------------
  -- Category laws
  --
  -- Associativity and identity hold definitionally at the fibre-map
  -- level, hence by reflexivity.
  --
  -- 范畴律
  --
  -- 结合律与恒等律在纤维映射层面定义性成立，故由自反性给出。
  assoc-i : {A B C D : LabelSys ℓ}
            {f : Idx⇒ A B} {g : Idx⇒ B C} {h : Idx⇒ C D}
          → compi (compi h g) f ≈i compi h (compi g f)
  assoc-i {f = f} {g = g} {h = h} = ≈i-refl (compi (compi h g) f)

  sym-assoc-i : {A B C D : LabelSys ℓ}
                {f : Idx⇒ A B} {g : Idx⇒ B C} {h : Idx⇒ C D}
              → compi h (compi g f) ≈i compi (compi h g) f
  sym-assoc-i {f = f} {g = g} {h = h} = ≈i-refl (compi h (compi g f))

  identityˡ-i : {X Y : LabelSys ℓ} {g : Idx⇒ X Y}
              → compi (idxi Y) g ≈i g
  identityˡ-i {g = g} = ≈i-refl g

  identityʳ-i : {X Y : LabelSys ℓ} {g : Idx⇒ X Y}
              → compi g (idxi X) ≈i g
  identityʳ-i {g = g} = ≈i-refl g

  identity²-i : {X : LabelSys ℓ} → compi (idxi X) (idxi X) ≈i idxi X
  identity²-i {X = X} = ≈i-refl (idxi X)

  ----------------------------------------------------------------------
  -- The wide subcategory
  --
  -- 宽子范畴

  SameIndexCat : Category (lsuc ℓ) ℓ ℓ
  SameIndexCat = record
    { Obj       = LabelSys ℓ
    ; _⇒_       = Idx⇒
    ; _≈_       = λ {X} {Y} → _≈i_ {X} {Y}
    ; id        = λ {X} → idxi X
    ; _∘_       = λ {X} {Y} {Z} g f → compi {X} {Y} {Z} g f
    ; equiv     = λ {X} {Y} → ≈i-isEquivalence {X} {Y}
    ; ∘-resp-≈  = λ {X} {Y} {Z} {f} {h} {g} {k} fh gk →
                     ∘-resp-≈i {X} {Y} {Z}
                                {F₁ = g} {F₂ = k}
                                {G₁ = f} {G₂ = h} gk fh
    ; assoc     = λ {W} {X} {Y} {Z} {f} {g} {h} →
                     assoc-i {A = W} {B = X} {C = Y} {D = Z}
                             {f = f} {g = g} {h = h}
    ; sym-assoc = λ {W} {X} {Y} {Z} {f} {g} {h} →
                     sym-assoc-i {A = W} {B = X} {C = Y} {D = Z}
                                 {f = f} {g = g} {h = h}
    ; identityˡ = λ {X} {Y} {f} → identityˡ-i {X} {Y} {g = f}
    ; identityʳ = λ {X} {Y} {f} → identityʳ-i {X} {Y} {g = f}
    ; identity² = λ {X} → identity²-i {X = X}
    }
