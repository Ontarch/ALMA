------------------------------------------------------------------------
-- Setoid-parameterised carried correspondences
--
-- MCorr hard-wires propositional equality in three places (FiberAdj
-- η/ε, the bisimulation here-eq, and the FMap graph witness /
-- relocation); this module replaces the edge/label equality by a
-- carried equivalence on the manifest carrier.
--
-- setoid 参数化的携带式对应
--
-- MCorr 在三处硬编码命题相等（FiberAdj 的 η/ε、互模拟的 here-eq、
-- FMap 图见证/重定位）；本模块把边/标签等价替换为建立在外显载体上的、
-- 被携带的等价关系。
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module ALMA.Base.MCorrSetoid where

open import Agda.Primitive using (Level; _⊔_; lsuc; lzero)
open import Agda.Builtin.Sigma using (Σ; _,_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)
open import Data.Unit.Polymorphic.Base using (⊤; tt)
open import Data.Nat using (ℕ)
open import Data.Bool using (Bool; true; false)
open import Data.Product.Base using (_×_; proj₁; proj₂)
open import Function.Base using (id; _∘_)
open import Relation.Binary.Core using (Rel)
open import Relation.Binary.Structures using (IsEquivalence)
open import Relation.Binary.PropositionalEquality.Core as Prop using (cong)
open import Relation.Binary.PropositionalEquality.Properties renaming
  (isEquivalence to ≡-isEquivalence)
open import Relation.Nullary.Negation using (¬_)

open import ALMA.Base.MCorr using (M; FiberAdj; _⍮_)

------------------------------------------------------------------------
-- Equivalence on a manifest carrier
--
-- This is stdlib's Setoid with Carrier promoted to a module parameter,
-- so EqOn (A x) is by construction an equivalence on exactly A x.
--
-- 外显载体上的等价
--
-- 即 stdlib Setoid 把 Carrier 提为模块参数，故 EqOn (A x) 按构造
-- 正是 A x 上的等价。

record EqOn {a ℓ : Level} (Carrier : Set a) : Set (lsuc (a ⊔ ℓ)) where
  infix 4 _≈_
  field
    _≈_           : Rel Carrier ℓ
    isEquivalence : IsEquivalence _≈_
  open IsEquivalence isEquivalence public using (refl; sym; trans; reflexive)

------------------------------------------------------------------------
-- Fibre adjunction between two carriers with carried equivalences
--
-- η/ε live at the carried _≈_; to-cong/fro-cong carry the naturality
-- coherence as data.
--
-- 两个载体间、在携带等价上的纤维伴随
--
-- η/ε 建立在携带的 _≈_ 上；to-cong/fro-cong 把自然性相干作为数据
-- 携带。

record FiberAdjˢ {c d ℓc ℓd : Level}
                {P : Set c} {R : Set d}
                (EP : EqOn {ℓ = ℓc} P) (ER : EqOn {ℓ = ℓd} R)
       : Set (c ⊔ d ⊔ ℓc ⊔ ℓd) where
  private
    module EP = EqOn EP
    module ER = EqOn ER
  field
    to       : R → P
    fro      : P → R
    to-cong  : ∀ {r r'} → r ER.≈ r' → to r EP.≈ to r'
    fro-cong : ∀ {p p'} → p EP.≈ p' → fro p ER.≈ fro p'
    η        : (r : R) → fro (to r) ER.≈ r
    ε        : (p : P) → to (fro p) EP.≈ p
open FiberAdjˢ public

idAdjˢ : ∀ {c ℓ} {P : Set c} (E : EqOn {ℓ = ℓ} P) → FiberAdjˢ E E
idAdjˢ E = record
  { to       = id
  ; fro      = id
  ; to-cong  = λ e → e
  ; fro-cong = λ e → e
  ; η        = λ _ → EqOn.refl E
  ; ε        = λ _ → EqOn.refl E
  }

symAdjˢ : ∀ {c d ℓc ℓd} {P : Set c} {R : Set d}
          {EP : EqOn {ℓ = ℓc} P} {ER : EqOn {ℓ = ℓd} R}
        → FiberAdjˢ EP ER → FiberAdjˢ ER EP
symAdjˢ a = record
  { to       = fro a
  ; fro      = to a
  ; to-cong  = fro-cong a
  ; fro-cong = to-cong a
  ; η        = ε a
  ; ε        = η a
  }

compAdjˢ : ∀ {r g h ℓr ℓg ℓh : Level}
           {R : Set r} {G : Set g} {H : Set h}
           (ER : EqOn {ℓ = ℓr} R)
           (EG : EqOn {ℓ = ℓg} G)
           (EH : EqOn {ℓ = ℓh} H)
         → FiberAdjˢ EG ER → FiberAdjˢ EH EG → FiberAdjˢ EH ER
compAdjˢ ER EG EH a₁ a₂ = record
  { to       = to a₂ ∘ to a₁
  ; fro      = fro a₁ ∘ fro a₂
  ; to-cong  = to-cong a₂ ∘ to-cong a₁
  ; fro-cong = fro-cong a₁ ∘ fro-cong a₂
  ; η = λ r → EqOn.trans ER
               (fro-cong a₁ (η a₂ (to a₁ r)))
               (η a₁ r)
  ; ε = λ p → EqOn.trans EH
               (to-cong a₂ (ε a₁ (fro a₂ p)))
               (ε a₂ p)
  }

------------------------------------------------------------------------
-- Coinductive bisimulation over carried label/edge equivalences
--
-- 在携带的标签/边等价上的余归纳互模拟

record _≈Mˢ_ {i a b ℓa ℓe : Level}
             {I : Set i} {A : I → Set a}
             {E : (x : I) (a : A x) (y : I) → Set b}
             (≈A : (x : I) → EqOn {ℓ = ℓa} (A x))
             (≈E : (x : I) (a : A x) (y : I) → EqOn {ℓ = ℓe} (E x a y))
             {x : I} (t s : M A E x)
       : Set (i ⊔ a ⊔ b ⊔ ℓa ⊔ ℓe) where
  coinductive
  field
    here-eq : EqOn._≈_ (≈A x) (M.here t) (M.here s)
    below-eq : ∀ (y : I)
      → Σ (FiberAdjˢ (≈E x (M.here s) y) (≈E x (M.here t) y)) λ adj
      →   (∀ (e₁ : E x (M.here t) y)
           → _≈Mˢ_ ≈A ≈E (M.below t y e₁)
                           (M.below s y (to adj e₁)))
        × (∀ (e₂ : E x (M.here s) y)
           → _≈Mˢ_ ≈A ≈E (M.below s y e₂)
                           (M.below t y (fro adj e₂)))
open _≈Mˢ_ public

≈Mˢ-refl : ∀ {i a b ℓa ℓe : Level}
             {I : Set i} {A : I → Set a}
             {E : (x : I) (a : A x) (y : I) → Set b}
             (≈A : (x : I) → EqOn {ℓ = ℓa} (A x))
             (≈E : (x : I) (a : A x) (y : I) → EqOn {ℓ = ℓe} (E x a y))
             {x : I} (t : M A E x) → _≈Mˢ_ ≈A ≈E t t
≈Mˢ-refl ≈A ≈E t .here-eq = EqOn.refl (≈A _)
≈Mˢ-refl ≈A ≈E {x = x} t .below-eq y =
    idAdjˢ (≈E x (M.here t) y)
  , ( (λ e₁ → ≈Mˢ-refl ≈A ≈E (M.below t y e₁))
    , (λ e₂ → ≈Mˢ-refl ≈A ≈E (M.below t y e₂)) )

-- The below-eq field already stores both directions, so symmetry only
-- swaps the adjunction and exchanges the two components; no
-- coinductive call, no transport.
--
-- below-eq 已同时存放两个方向，故对称性只需交换伴随并对调两个分量；
-- 无需余归纳调用，也无需传输。
≈Mˢ-sym : ∀ {i a b ℓa ℓe : Level}
            {I : Set i} {A : I → Set a}
            {E : (x : I) (a : A x) (y : I) → Set b}
            (≈A : (x : I) → EqOn {ℓ = ℓa} (A x))
            (≈E : (x : I) (a : A x) (y : I) → EqOn {ℓ = ℓe} (E x a y))
            {x : I} {t s : M A E x}
          → _≈Mˢ_ ≈A ≈E t s → _≈Mˢ_ ≈A ≈E s t
≈Mˢ-sym ≈A ≈E {x = x} p .here-eq = EqOn.sym (≈A x) (p .here-eq)
≈Mˢ-sym ≈A ≈E {x = x} p .below-eq y
    with p .below-eq y
... | adj , fwd , bwd =
      symAdjˢ adj , ( bwd , fwd )

-- Compose the two adjunctions with compAdjˢ; every recursive call lies
-- under the coinductive below-eq constructor.
--
-- 用 compAdjˢ 复合两根伴随；每个递归调用都位于余归纳 below-eq 构造子
-- 之下。
≈Mˢ-trans : ∀ {i a b ℓa ℓe : Level}
              {I : Set i} {A : I → Set a}
              {E : (x : I) (a : A x) (y : I) → Set b}
              (≈A : (x : I) → EqOn {ℓ = ℓa} (A x))
              (≈E : (x : I) (a : A x) (y : I) → EqOn {ℓ = ℓe} (E x a y))
              {x : I} {t m s : M A E x}
            → _≈Mˢ_ ≈A ≈E t m → _≈Mˢ_ ≈A ≈E m s
            → _≈Mˢ_ ≈A ≈E t s
≈Mˢ-trans ≈A ≈E {x = x} p q .here-eq =
    EqOn.trans (≈A x) (p .here-eq) (q .here-eq)
≈Mˢ-trans ≈A ≈E {x = x} {t = t} {m = m} {s = s} p q .below-eq y
    with p .below-eq y | q .below-eq y
... | adjp , fwdp , bwdp | adjq , fwdq , bwdq =
      compAdjˢ (≈E x (M.here t) y) (≈E x (M.here m) y) (≈E x (M.here s) y)
               adjp adjq
    , ( (λ e₁ → ≈Mˢ-trans ≈A ≈E (fwdp e₁) (fwdq (to adjp e₁)))
      , (λ e₂ → ≈Mˢ-trans ≈A ≈E (bwdq e₂) (bwdp (fro adjq e₂))) )

------------------------------------------------------------------------
-- Propositional FiberAdj as an instance of the setoid one
--
-- The _≡_ kernel is exactly the EqOn special case at propositional
-- equality.
--
-- 命题版 FiberAdj 作为 setoid 版的实例
--
-- _≡_ 内核恰为 EqOn 在命题相等处的特例。

propEqOn : ∀ {a} (A : Set a) → EqOn {ℓ = a} A
propEqOn A = record
  { _≈_ = _≡_
  ; isEquivalence = ≡-isEquivalence
  }

fromAdjˢ : ∀ {ℓp ℓr : Level} {P : Set ℓp} {R : Set ℓr}
         → FiberAdj P R → FiberAdjˢ (propEqOn P) (propEqOn R)
fromAdjˢ a = record
  { to       = FiberAdj.to a
  ; fro      = FiberAdj.fro a
  ; to-cong  = cong (FiberAdj.to a)
  ; fro-cong = cong (FiberAdj.fro a)
  ; η        = FiberAdj.η a
  ; ε        = FiberAdj.ε a
  }

toAdjˢ : ∀ {ℓp ℓr : Level} {P : Set ℓp} {R : Set ℓr}
       → FiberAdjˢ (propEqOn P) (propEqOn R) → FiberAdj P R
toAdjˢ a = record
  { to  = to a
  ; fro = fro a
  ; η   = η a
  ; ε   = ε a
  }

------------------------------------------------------------------------
-- Systems carrying label/edge equivalences
--
-- A Sys together with an EqOn on every label fibre and every edge
-- fibre. The M type itself is unchanged; only the comparison regime is
-- carried.
--
-- 携带标签/边等价的系统
--
-- Sys 外加每个标签纤维与边纤维上的 EqOn。M 型本身不变；被携带的只是
-- 比较制度。

record SysEq (i a b ℓa ℓe : Level) : Set (lsuc (i ⊔ a ⊔ ℓa ⊔ b ⊔ ℓe)) where
  field
    I   : Set i
    A   : I → Set a
    E   : (x : I) (a : A x) (y : I) → Set b
    ≈A  : (x : I) → EqOn {ℓ = ℓa} (A x)
    ≈E  : (x : I) (a : A x) (y : I) → EqOn {ℓ = ℓe} (E x a y)
open SysEq public

------------------------------------------------------------------------
-- One-step carried correspondence over an arbitrary index layer R
--
-- R need not be propositional equality; mapR only uses fro/pull and
-- contains no equality.
--
-- 任意索引层 R 上的一步携带对应
--
-- R 不必是命题相等；mapR 仅用 fro/pull，不含任何相等。

record Stepˢ {i j a b c d ℓr ℓa ℓe ℓc ℓd : Level}
             (X : SysEq i a b ℓa ℓe)
             (Y : SysEq j c d ℓc ℓd)
             (R : I X → I Y → Set ℓr)
             {x : I X} {y : I Y} (r : R x y)
       : Set (i ⊔ j ⊔ a ⊔ b ⊔ c ⊔ d ⊔ ℓr ⊔ ℓa ⊔ ℓe ⊔ ℓc ⊔ ℓd) where
  field
    shapeᴿ   : A X x → A Y y
    child    : (a : A X x) (v : I Y) → Σ (I X) λ x' → R x' v
    edge-adj : (a : A X x) (v : I Y)
             → FiberAdjˢ (≈E Y y (shapeᴿ a) v)
                          (≈E X x a (proj₁ (child a v)))

  pullˢ : (a : A X x) (v : I Y) (q : E Y y (shapeᴿ a) v)
        → Σ (I X) λ x' → Σ (E X x a x') λ e → R x' v
  pullˢ a v q =
    let x' , r' = child a v
    in x' , fro (edge-adj a v) q , r'
open Stepˢ public

record Morphˢ {i j a b c d ℓr ℓa ℓe ℓc ℓd : Level}
              (X : SysEq i a b ℓa ℓe)
              (Y : SysEq j c d ℓc ℓd)
              (R : I X → I Y → Set ℓr)
       : Set (i ⊔ j ⊔ a ⊔ b ⊔ c ⊔ d ⊔ ℓr ⊔ ℓa ⊔ ℓe ⊔ ℓc ⊔ ℓd) where
  field
    step : ∀ {x : I X} {y : I Y} (r : R x y)
         → Stepˢ X Y R r

  mapR : ∀ {x : I X} {y : I Y} → R x y
       → M (A X) (E X) x → M (A Y) (E Y) y
  mapR r t .M.here   = shapeᴿ (step r) (M.here t)
  mapR r t .M.below v q =
    let x' , e , r' = pullˢ (step r) (M.here t) v q
    in mapR r' (M.below t x' e)
open Morphˢ public

------------------------------------------------------------------------
-- Composition
--
-- Edge adjunctions compose via compAdjˢ.
--
-- 复合
--
-- 边伴随经 compAdjˢ 复合。

compMˢ :
  ∀ {i j k a b c d e f ℓ₁ ℓ₂ ℓa ℓe ℓc ℓd ℓg ℓh : Level}
    {X : SysEq i a b ℓa ℓe}
    {Y : SysEq j c d ℓc ℓd}
    {Z : SysEq k e f ℓg ℓh}
    {R : I X → I Y → Set ℓ₁} {S : I Y → I Z → Set ℓ₂}
  → Morphˢ X Y R → Morphˢ Y Z S → Morphˢ X Z (R ⍮ S)
compMˢ {X = X} {Y = Y} {Z = Z} φ ψ .step {x = x} {y = z} (ym , r , s) =
  let φr = step φ r
      ψs = step ψ s
  in record
  { shapeᴿ = λ a → shapeᴿ ψs (shapeᴿ φr a)
  ; child = λ a w →
      let ym' , s' = child ψs (shapeᴿ φr a) w
          x' , r'  = child φr a ym'
      in x' , (ym' , r' , s')
  ; edge-adj = λ a w →
      let ym' , s' = child ψs (shapeᴿ φr a) w
          x' , r'  = child φr a ym'
      in compAdjˢ (≈E X x a x')
                  (≈E Y ym (shapeᴿ φr a) ym')
                  (≈E Z z (shapeᴿ ψs (shapeᴿ φr a)) w)
                  (edge-adj φr a ym')
                  (edge-adj ψs (shapeᴿ φr a) w)
  }

------------------------------------------------------------------------
-- Identity
--
-- The free path groupoid on the index; edge round-trips are at the
-- carried EqOn.
--
-- 恒等
--
-- 索引上的自由路径广群；边往返律建立在携带的 EqOn 上。

idMˢ : ∀ {i a b ℓa ℓe : Level} (X : SysEq i a b ℓa ℓe)
     → Morphˢ X X (λ (x y : I X) → x ≡ y)
idMˢ X .step {x = x₀} {y = .x₀} refl = record
  { shapeᴿ   = λ a → a
  ; child    = λ a v → v , refl
  ; edge-adj = λ a v → idAdjˢ (≈E X x₀ a v)
  }

------------------------------------------------------------------------
-- Pilot: a genuinely non-propositional equivalence
--
-- Carrier L = ℕ × Bool with (n , b) ≈L (m , c) iff n ≡ m, ignoring the
-- tag; so (0 , true) ≈L (0 , false) but they are not propositionally
-- equal.
--
-- 试点：真正非命题的等价
--
-- 载体 L = ℕ × Bool，(n , b) ≈L (m , c) 当且仅当 n ≡ m，忽略标签；
-- 故 (0 , true) ≈L (0 , false)，但二者命题不相等。

L : Set lzero
L = ℕ × Bool

infix 4 _≈L_
_≈L_ : Rel L lzero
(n , _) ≈L (m , _) = n ≡ m

LEq : EqOn L
LEq = record
  { _≈_ = _≈L_
  ; isEquivalence = record
    { refl  = refl
    ; sym   = Prop.sym
    ; trans = Prop.trans
    }
  }

bool-neq : true ≡ false → ⊥
bool-neq ()

tag-neq : ¬ ((0 , true) ≡ (0 , false))
tag-neq e = bool-neq (cong proj₂ e)

------------------------------------------------------------------------
-- Container position adjunction on the non-propositional equivalence
--
-- Source positions R = L (tagged), target positions P = ℕ (untagged);
-- fro is the old contravariant onPos, while to and η/ε are the data
-- formerly rebuilt by subst (pts-compat / onActP), now carried at an
-- equivalence strictly coarser than _≡_.
--
-- 非命题等价上的容器位置伴随
--
-- 源位置 R = L（带标签），目标位置 P = ℕ（无标签）；fro 即旧反变
-- onPos，而 to 与 η/ε 正是过去靠 subst（pts-compat / onActP）补造的
-- 数据，此处被携带，且建立在严格粗于 _≡_ 的等价上。

onPosAdj : FiberAdjˢ (propEqOn ℕ) LEq
onPosAdj = record
  { to       = proj₁
  ; fro      = λ n → (n , true)
  ; to-cong  = λ e → e
  ; fro-cong = λ e → e
  ; η        = λ { (n , _) → refl }
  ; ε        = λ _ → refl
  }

------------------------------------------------------------------------
-- Expressiveness witness
--
-- Two M-trees bisimilar under LEq but with propositionally distinct
-- head labels. _≈Mˢ_ relates them; the old _≈M_ cannot, since its
-- here-eq would ask for (0 , true) ≡ (0 , false).
--
-- 表达力见证
--
-- 两棵 M 树在 LEq 下互模拟，但头部标签命题不相等。_≈Mˢ_ 联系二者；
-- 旧 _≈M_ 不能，因其 here-eq 会要求 (0 , true) ≡ (0 , false)。

private
  Iᵗ : Set lzero
  Iᵗ = ⊤ {lzero}

  ttᵗ : Iᵗ
  ttᵗ = tt {lzero}

  Aᵗ : Iᵗ → Set lzero
  Aᵗ _ = L

  Eᵗ : (i : Iᵗ) (a : Aᵗ i) (j : Iᵗ) → Set lzero
  Eᵗ _ _ _ = L

  ≈Aᵗ : (x : Iᵗ) → EqOn (Aᵗ x)
  ≈Aᵗ _ = LEq

  ≈Eᵗ : (x : Iᵗ) (a : Aᵗ x) (j : Iᵗ) → EqOn (Eᵗ x a j)
  ≈Eᵗ _ _ _ = LEq

  K : M Aᵗ Eᵗ ttᵗ
  K .M.here = (0 , true)
  K .M.below _ _ = K

  t : M Aᵗ Eᵗ ttᵗ
  t .M.here = (0 , true)
  t .M.below _ _ = K

  s : M Aᵗ Eᵗ ttᵗ
  s .M.here = (0 , false)
  s .M.below _ _ = K

  t≈Mˢs : _≈Mˢ_ ≈Aᵗ ≈Eᵗ t s
  t≈Mˢs .here-eq = refl
  t≈Mˢs .below-eq _ =
      idAdjˢ LEq
    , ( (λ _ → ≈Mˢ-refl ≈Aᵗ ≈Eᵗ K)
      , (λ _ → ≈Mˢ-refl ≈Aᵗ ≈Eᵗ K) )

  t≄Ms-head : ¬ (M.here t ≡ M.here s)
  t≄Ms-head = tag-neq
