------------------------------------------------------------------------
-- Bundles for interval reals
--
-- 区间实数的打包结构
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module Real.Interval.Bundles where

open import Algebra.Apartness using
  (IsHeytingCommutativeRing; IsHeytingField; HeytingCommutativeRing; HeytingField)
open import Algebra.Bundles using
  (CommutativeMonoid; AbelianGroup; Ring; CommutativeRing)
open import Algebra.Bundles.Raw using (RawSemiring; RawRing)
open import Algebra.Structures using
  (IsMagma; IsSemigroup; IsMonoid; IsCommutativeMonoid; IsGroup; IsAbelianGroup
  ; IsRing; IsCommutativeRing)
open import Level using (0ℓ)
open import Data.Nat using (ℕ)
open import Data.Product using (Σ; _×_; _,_)
open import Data.Rational using (ℚ; _+_; _*_; _<_; -_)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary.Bundles using (Poset; StrictPartialOrder)
open import Relation.Binary.Structures using (IsPartialOrder; IsStrictPartialOrder)
open import Relation.Binary.Definitions using (Tight)

open import Real using (embed)
open import Real.Interval using (RealI; embedℚ)
open import Real.Interval.Equiv using (_≈ℝ_; ≈ℝ-isEquivalence; ≈ℝ-trans; ≈ℝ-sym)
open import Real.Interval.Apartness using (_#ℝ_; #ℝ-isApartnessRelation; #ℝ-irrefl)
open import Real.Interval.ApartnessInvertible using (invertible⇒#)
open import Real.Interval.Arith using (0ℝ; 1ℝ; _+ℝ_; negℝ; _-ℝ_)
open import Real.Interval.ArithLaws using
  (+ℝ-assoc; +ℝ-comm; +ℝ-identityˡ; +ℝ-identityʳ; +ℝ-inverseˡ; +ℝ-inverseʳ)
open import Real.Interval.Mul using (_*ℝ_)
open import Real.Interval.Mul.Laws using
  (*ℝ-assoc; *ℝ-comm; *ℝ-identityˡ; *ℝ-identityʳ; *ℝ-distribˡ-+; *ℝ-distribʳ-+)
open import Real.Interval.Mul.Cong using (*ℝ-cong)
open import Real.Interval.Mul.Order using (+ℝ-cong; ≈-neg; ≈-<-respʳ; <-*mono)
open import Real.Interval.Order using (_<ℝ_; <-irrefl; <-trans)
open import Real.Interval.OrderLaws using (≈-<-resp; <-+mono)
open import Real.Interval.OrderLe using (≤ℝ-trans; ≤ℝ-antisym)
open import Real.Interval.OrderComplete.Base using (Subset; Located; emb<; _≤ℝ_)
open import Real.Interval.OrderComplete using (order-complete)
open import Real.Interval.Infimum using (LocatedBelow)
  renaming (inf-complete to infimum-complete)
open import Real.Interval.Inverse using (*ℝ-inverse)
open import Real.Interval.Recip using (recipℝ')
open import Real.Interval.Embed using (0ℝ<ℝ1ℝ; embedℚ-+; embedℚ-*; embedℚ-neg)
open import Real.Interval.DensityArch renaming
  (dense to dense-proof; archimedean to archimedean-proof)
open import Real.Interval.LimitLaws using (tight)

------------------------------------------------------------------------
-- Additive group
--
-- 加法群

+ℝ-isMagma : IsMagma _≈ℝ_ _+ℝ_
+ℝ-isMagma = record
  { isEquivalence = ≈ℝ-isEquivalence
  ; ∙-cong        = +ℝ-cong
  }

+ℝ-isSemigroup : IsSemigroup _≈ℝ_ _+ℝ_
+ℝ-isSemigroup = record
  { isMagma = +ℝ-isMagma
  ; assoc   = +ℝ-assoc
  }

+ℝ-isMonoid : IsMonoid _≈ℝ_ _+ℝ_ 0ℝ
+ℝ-isMonoid = record
  { isSemigroup = +ℝ-isSemigroup
  ; identity    = +ℝ-identityˡ , +ℝ-identityʳ
  }

+ℝ-isGroup : IsGroup _≈ℝ_ _+ℝ_ 0ℝ negℝ
+ℝ-isGroup = record
  { isMonoid = +ℝ-isMonoid
  ; inverse  = +ℝ-inverseˡ , +ℝ-inverseʳ
  ; ⁻¹-cong  = ≈-neg
  }

+ℝ-isAbelianGroup : IsAbelianGroup _≈ℝ_ _+ℝ_ 0ℝ negℝ
+ℝ-isAbelianGroup = record
  { isGroup = +ℝ-isGroup
  ; comm    = +ℝ-comm
  }

------------------------------------------------------------------------
-- Multiplicative monoid
--
-- 乘法幺半群

*ℝ-isMagma : IsMagma _≈ℝ_ _*ℝ_
*ℝ-isMagma = record
  { isEquivalence = ≈ℝ-isEquivalence
  ; ∙-cong        = *ℝ-cong
  }

*ℝ-isSemigroup : IsSemigroup _≈ℝ_ _*ℝ_
*ℝ-isSemigroup = record
  { isMagma = *ℝ-isMagma
  ; assoc   = *ℝ-assoc
  }

*ℝ-isMonoid : IsMonoid _≈ℝ_ _*ℝ_ 1ℝ
*ℝ-isMonoid = record
  { isSemigroup = *ℝ-isSemigroup
  ; identity    = *ℝ-identityˡ , *ℝ-identityʳ
  }

*ℝ-isCommutativeMonoid : IsCommutativeMonoid _≈ℝ_ _*ℝ_ 1ℝ
*ℝ-isCommutativeMonoid = record
  { isMonoid = *ℝ-isMonoid
  ; comm     = *ℝ-comm
  }

------------------------------------------------------------------------
-- Ring and commutative ring
--
-- 环与交换环

+ℝ*ℝ-isRing : IsRing _≈ℝ_ _+ℝ_ _*ℝ_ negℝ 0ℝ 1ℝ
+ℝ*ℝ-isRing = record
  { +-isAbelianGroup = +ℝ-isAbelianGroup
  ; *-cong           = *ℝ-cong
  ; *-assoc          = *ℝ-assoc
  ; *-identity       = *ℝ-identityˡ , *ℝ-identityʳ
  ; distrib          = *ℝ-distribˡ-+ , *ℝ-distribʳ-+
  }

+ℝ*ℝ-isCommutativeRing :
  IsCommutativeRing _≈ℝ_ _+ℝ_ _*ℝ_ negℝ 0ℝ 1ℝ
+ℝ*ℝ-isCommutativeRing = record
  { isRing = +ℝ*ℝ-isRing
  ; *-comm = *ℝ-comm
  }

------------------------------------------------------------------------
-- Invertibility and tightness
--
-- The standard library's notion of invertibility unfolds to a pair of
-- mutual inverses, and tightness unfolds to the two implications
-- relating non-apartness and equivalence.
--
-- 可逆性与紧密性
--
-- 标准库的可逆性展开为一对互逆元素，紧密性展开为联系非分离与等价
-- 的两个蕴含式。

#⇒invertible-stdlib : ∀ {x y : RealI} → x #ℝ y →
  Σ RealI λ z →
    (z *ℝ (x -ℝ y)) ≈ℝ 1ℝ × ((x -ℝ y) *ℝ z) ≈ℝ 1ℝ
#⇒invertible-stdlib {x} {y} (inj₁ x<y) =
  let
    d = x -ℝ y
    d<0 : d <ℝ 0ℝ
    d<0 = ≈-<-respʳ (+ℝ-inverseʳ y)
            (<-+mono x y (negℝ y) x<y)
    inv = recipℝ' d (inj₂ d<0)
    d*inv : d *ℝ inv ≈ℝ 1ℝ
    d*inv = *ℝ-inverse d (inj₂ d<0)
    inv*d : inv *ℝ d ≈ℝ 1ℝ
    inv*d = ≈ℝ-trans (*ℝ-comm inv d) d*inv
  in inv , inv*d , d*inv
#⇒invertible-stdlib {x} {y} (inj₂ y<x) =
  let
    d = x -ℝ y
    0<d : 0ℝ <ℝ d
    0<d = ≈-<-resp (+ℝ-inverseʳ y)
            (<-+mono y x (negℝ y) y<x)
    inv = recipℝ' d (inj₁ 0<d)
    d*inv : d *ℝ inv ≈ℝ 1ℝ
    d*inv = *ℝ-inverse d (inj₁ 0<d)
    inv*d : inv *ℝ d ≈ℝ 1ℝ
    inv*d = ≈ℝ-trans (*ℝ-comm inv d) d*inv
  in inv , inv*d , d*inv

invertible⇒#-stdlib : ∀ {x y : RealI} →
  Σ RealI (λ z →
    (z *ℝ (x -ℝ y)) ≈ℝ 1ℝ × ((x -ℝ y) *ℝ z) ≈ℝ 1ℝ) →
  x #ℝ y
invertible⇒#-stdlib {x} {y} (z , zd , dz) =
  invertible⇒# x y (z , dz , zd)

tight-full : Tight _≈ℝ_ _#ℝ_
tight-full x y = tight {x} {y} , #ℝ-irrefl {x} {y}

------------------------------------------------------------------------
-- The standard library IsHeytingCommutativeRing instance
--
-- 标准库的海廷交换环实例

intervalHeytingCommutativeRing :
  IsHeytingCommutativeRing _≈ℝ_ _#ℝ_ _+ℝ_ _*ℝ_ negℝ 0ℝ 1ℝ
intervalHeytingCommutativeRing = record
  { isCommutativeRing   = +ℝ*ℝ-isCommutativeRing
  ; isApartnessRelation = #ℝ-isApartnessRelation
  ; #⇒invertible        = #⇒invertible-stdlib
  ; invertible⇒#        = invertible⇒#-stdlib
  }

------------------------------------------------------------------------
-- The standard library IsHeytingField instance
--
-- 标准库的海廷域实例

intervalHeytingField :
  IsHeytingField _≈ℝ_ _#ℝ_ _+ℝ_ _*ℝ_ negℝ 0ℝ 1ℝ
intervalHeytingField = record
  { isHeytingCommutativeRing = intervalHeytingCommutativeRing
  ; tight = tight-full
  }

------------------------------------------------------------------------
-- Order bundles
--
-- The strict order is packaged as a standard library strict partial
-- order and the non-strict order as a poset. Constructively the reals
-- cannot carry a total order: totality of the non-strict order would
-- imply LLPO.
--
-- 序打包
--
-- 严格序打包为标准库的严格偏序，非严格序打包为偏序集。构造性实数
-- 不能携带全序：非严格序的全序性将蕴含 LLPO。

intervalStrictPartialOrder : StrictPartialOrder 0ℓ 0ℓ 0ℓ
intervalStrictPartialOrder = record
  { Carrier              = RealI
  ; _≈_                  = _≈ℝ_
  ; _<_                  = _<ℝ_
  ; isStrictPartialOrder = record
      { isEquivalence = ≈ℝ-isEquivalence
      ; irrefl        = λ {x} {y} x≈y x<y →
          <-irrefl y (≈-<-resp x≈y x<y)
      ; trans         = <-trans
      ; <-resp-≈      = ≈-<-respʳ , ≈-<-resp
      }
  }

-- Equality reflects into the non-strict order.
--
-- 等价可转化为非严格序。
≤ℝ-reflexive : ∀ {x y} → x ≈ℝ y → x ≤ℝ y
≤ℝ-reflexive {x} {y} x≈y y<x =
  <-irrefl x (≈-<-resp (≈ℝ-sym x≈y) y<x)

≤ℝ-isPartialOrder : IsPartialOrder _≈ℝ_ _≤ℝ_
≤ℝ-isPartialOrder = record
  { isPreorder = record
    { isEquivalence = ≈ℝ-isEquivalence
    ; reflexive     = ≤ℝ-reflexive
    ; trans         = ≤ℝ-trans
    }
  ; antisym = ≤ℝ-antisym
  }

intervalPoset : Poset 0ℓ 0ℓ 0ℓ
intervalPoset = record
  { Carrier        = RealI
  ; _≈_            = _≈ℝ_
  ; _≤_            = _≤ℝ_
  ; isPartialOrder = ≤ℝ-isPartialOrder
  }

------------------------------------------------------------------------
-- Ordered field
--
-- 有序域

record IsIntervalOrderedField : Set₁ where
  field
    isIntervalHeytingField :
      IsHeytingField _≈ℝ_ _#ℝ_ _+ℝ_ _*ℝ_ negℝ 0ℝ 1ℝ
    <-isStrictPartialOrder : IsStrictPartialOrder _≈ℝ_ _<ℝ_
    +-mono-<     : ∀ x y z → x <ℝ y → (x +ℝ z) <ℝ (y +ℝ z)
    *-mono-<-pos : ∀ x y z → x <ℝ y → 0ℝ <ℝ z →
                   (x *ℝ z) <ℝ (y *ℝ z)
    0<1          : 0ℝ <ℝ 1ℝ

intervalOrderedField : IsIntervalOrderedField
intervalOrderedField = record
  { isIntervalHeytingField = intervalHeytingField
  ; <-isStrictPartialOrder =
      StrictPartialOrder.isStrictPartialOrder intervalStrictPartialOrder
  ; +-mono-<               = <-+mono
  ; *-mono-<-pos           = <-*mono
  ; 0<1                    = 0ℝ<ℝ1ℝ
  }

------------------------------------------------------------------------
-- Complete ordered field
--
-- 完备有序域

record IsIntervalCompleteOrderedField : Set₁ where
  field
    isIntervalOrderedField : IsIntervalOrderedField
    sup-complete :
      (P : Subset) (loc : Located P)
      (x₀ : RealI) (px₀ : P x₀)
      (u₀ : RealI) (isUpper : (x : RealI) → P x → x ≤ℝ u₀) →
      Σ RealI λ s →
        (∀ x → P x → x ≤ℝ s)
        × (∀ u → ((x : RealI) → P x → x ≤ℝ u) → s ≤ℝ u)
    inf-complete :
      (P : Subset) (locb : LocatedBelow P)
      (x₀ : RealI) (px₀ : P x₀)
      (l₀ : RealI) (isLower : (x : RealI) → P x → l₀ ≤ℝ x) →
      Σ RealI λ i →
        (∀ x → P x → i ≤ℝ x)
        × (∀ l → ((x : RealI) → P x → l ≤ℝ x) → l ≤ℝ i)

intervalCompleteOrderedField : IsIntervalCompleteOrderedField
intervalCompleteOrderedField = record
  { isIntervalOrderedField = intervalOrderedField
  ; sup-complete = λ P loc x₀ px₀ u₀ isUpper →
      order-complete {P = P} loc {x₀} px₀ {u₀} isUpper
  ; inf-complete = λ P locb x₀ px₀ l₀ isLower →
      infimum-complete {P = P} locb {x₀} px₀ {l₀} isLower
  }

------------------------------------------------------------------------
-- Archimedean field with ℚ embedding
--
-- 带 ℚ 嵌入的阿基米德域

record IsIntervalArchimedeanField : Set₁ where
  field
    isIntervalCompleteOrderedField : IsIntervalCompleteOrderedField
    embed-+     : ∀ (p q : ℚ) →
                  embedℚ (p + q) ≈ℝ (embedℚ p +ℝ embedℚ q)
    embed-*     : ∀ (p q : ℚ) →
                  embedℚ (p * q) ≈ℝ (embedℚ p *ℝ embedℚ q)
    embed-neg   : ∀ (p : ℚ) → embedℚ (- p) ≈ℝ negℝ (embedℚ p)
    embed-<     : ∀ {p q : ℚ} → p < q → embedℚ p <ℝ embedℚ q
    dense       : ∀ (x y : RealI) → x <ℝ y →
                  Σ ℚ (λ q → (x <ℝ embedℚ q) × (embedℚ q <ℝ y))
    archimedean : ∀ x → Σ ℕ (λ n → x <ℝ embedℚ (embed n))

intervalArchimedeanField : IsIntervalArchimedeanField
intervalArchimedeanField = record
  { isIntervalCompleteOrderedField = intervalCompleteOrderedField
  ; embed-+     = embedℚ-+
  ; embed-*     = embedℚ-*
  ; embed-neg   = embedℚ-neg
  ; embed-<     = emb<
  ; dense       = λ x y p → dense-proof {x} {y} p
  ; archimedean = archimedean-proof
  }

------------------------------------------------------------------------
-- Standard library bundles
--
-- 标准库打包结构

intervalCommutativeRing : CommutativeRing 0ℓ 0ℓ
intervalCommutativeRing = record
  { Carrier           = RealI
  ; _≈_               = _≈ℝ_
  ; _+_               = _+ℝ_
  ; _*_               = _*ℝ_
  ; -_                = negℝ
  ; 0#                = 0ℝ
  ; 1#                = 1ℝ
  ; isCommutativeRing = +ℝ*ℝ-isCommutativeRing
  }

intervalRing : Ring 0ℓ 0ℓ
intervalRing = CommutativeRing.ring intervalCommutativeRing

intervalAbelianGroup : AbelianGroup 0ℓ 0ℓ
intervalAbelianGroup =
  CommutativeRing.+-abelianGroup intervalCommutativeRing

intervalCommutativeMonoid : CommutativeMonoid 0ℓ 0ℓ
intervalCommutativeMonoid =
  CommutativeRing.*-commutativeMonoid intervalCommutativeRing

intervalRawRing : RawRing 0ℓ 0ℓ
intervalRawRing = record
  { Carrier = RealI
  ; _≈_     = _≈ℝ_
  ; _+_     = _+ℝ_
  ; _*_     = _*ℝ_
  ; -_      = negℝ
  ; 0#      = 0ℝ
  ; 1#      = 1ℝ
  }

intervalRawSemiring : RawSemiring 0ℓ 0ℓ
intervalRawSemiring = record
  { Carrier = RealI
  ; _≈_     = _≈ℝ_
  ; _+_     = _+ℝ_
  ; _*_     = _*ℝ_
  ; 0#      = 0ℝ
  ; 1#      = 1ℝ
  }

------------------------------------------------------------------------
-- Standard library Heyting field bundles
--
-- 标准库的海廷域打包结构

intervalHeytingCommutativeRingBundle : HeytingCommutativeRing 0ℓ 0ℓ 0ℓ
intervalHeytingCommutativeRingBundle = record
  { isHeytingCommutativeRing = intervalHeytingCommutativeRing
  }

intervalHeytingFieldBundle : HeytingField 0ℓ 0ℓ 0ℓ
intervalHeytingFieldBundle = record
  { isHeytingField = intervalHeytingField
  }
