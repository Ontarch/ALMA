------------------------------------------------------------------------
-- Local charts as a LayeredEqGen instance
--
-- The construction is single-directional: ManifoldStructure carries
-- support inclusion under restriction in one direction only, matching
-- standard manifolds; consequently ManifoldEq is a preorder, not an
-- equivalence relation.
--
-- 局部坐标卡作为 LayeredEqGen 实例
--
-- 该构造是单向的：ManifoldStructure 仅单向携带限制下的支撑包含，
-- 匹配标准流形；因此 ManifoldEq 是预序，不是等价关系。
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module Equivalence.ManifoldEq where

open import Agda.Primitive using (lsuc)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Sigma using (Σ; _,_)
open import Data.Nat.Base using (z<s)
open import Data.Product.Base using (proj₁; proj₂; _×_)
open import Data.Sum.Base using (inj₁; inj₂)
open import Data.Rational.Base using (ℚ; _+_; _-_; -_; _⊔_; _⊓_; _<_; 0ℚ; 1ℚ; *<*)
open import Data.Integer.Base using (-<+; +<+)
open import Data.Rational.Properties using
  (+-identityʳ; +-monoʳ-<; ≤-total; <-trans; <-irrefl; ≤-<-trans; <-≤-trans
  ; p≤p⊔q; p≤q⊔p; p⊓q≤p; p⊓q≤q; p≤q⇒p⊓q≡p; p≥q⇒p⊓q≡q; p≤q⇒p⊔q≡q; p≥q⇒p⊔q≡p)
open import Relation.Binary.PropositionalEquality.Core using (trans; sym; subst)
open import Relation.Binary.Structures using (IsPreorder)
open import Relation.Nullary using (¬_)

open import Base.IndexedMType using (Mᵢ)
open import Equivalence.Core using (LayeredEqGen)
open import Equivalence.Properties using (module LayeredEqGen-Properties)

------------------------------------------------------------------------
-- Manifold structure with local charts
--
-- 带局部坐标卡的流形结构

record ManifoldStructure {a} (X : Set a) : Set (lsuc a) where
  field
    E        : Set a
    Chart    : X → Set a
    Support  : (x : X) → Chart x → X → Set a
    readout  : (x : X) (c : Chart x) (y : X) → Support x c y → E
    restrict : (x : X) (c : Chart x) (y : X) (h : Support x c y) → Chart y

    -- Single-directional support inclusion under restriction.
    --
    -- 限制下的单向支撑包含。
    support-mono
      : (x y : X) (c : Chart x) (h : Support x c y)
      → ∀ w → Support y (restrict x c y h) w → Support x c w

    readout-restrict
      : (x y : X) (c : Chart x) (h : Support x c y)
      → (w : X) (hw' : Support y (restrict x c y h) w)
      → readout x c w (support-mono x y c h w hw')
        ≡ readout y (restrict x c y h) w hw'

    -- Naturality of restriction with respect to layer.
    --
    -- 限制关于 layer 的自然性。
    layer-preserve
      : (x y : X) (c : Chart x) (d : Chart y)
      → (f : ∀ w → Support x c w → Support y d w)
      → (coh : ∀ w (hw : Support x c w)
               → readout x c w hw ≡ readout y d w (f w hw))
      → (pt : X) (hpt : Support x c pt)
      → Σ (∀ w → Support pt (restrict x c pt hpt) w
                → Support pt (restrict y d pt (f pt hpt)) w)
          (λ f' → ∀ w (hw : Support pt (restrict x c pt hpt) w)
                  → readout pt (restrict x c pt hpt) w hw
                    ≡ readout pt (restrict y d pt (f pt hpt)) w (f' w hw))

------------------------------------------------------------------------
-- ManifoldEq as a LayeredEqGen instance
--
-- State is a point together with a chart, observation is a point in
-- its support, step restricts the chart, and layer is
-- single-directional coverage with readout agreement.
--
-- ManifoldEq 作为 LayeredEqGen 的实例
--
-- 状态是点加坐标卡，观察是支撑中的点，步进限制坐标卡，
-- layer 是单向覆盖加读出一致。

module ManifoldEq {a} {X : Set a} (𝕄 : ManifoldStructure X) where
  open ManifoldStructure 𝕄

  State : Set a
  State = Σ X Chart

  Obs : State → Set a
  Obs (x , c) = Σ X (Support x c)

  step : (s : State) → Obs s → State
  step (x , c) (y , h) = (y , restrict x c y h)

  -- f maps the source support into the target support, preserving
  -- readout.
  --
  -- f 将源支撑映入目标支撑，保持读数。
  layer : State → State → Set a
  layer (x , c) (y , d) =
    Σ (∀ w → Support x c w → Support y d w)
      (λ f → ∀ w (hw : Support x c w)
             → readout x c w hw ≡ readout y d w (f w hw))

  -- Keeps the point, transports the support proof along the coverage.
  --
  -- 保持点不变，沿覆盖搬送支撑证明。
  obs-map : (s t : State) → layer s t → Obs s → Obs t
  obs-map (x , c) (y , d) l (w , hw) = (w , proj₁ l w hw)

  layer-refl : ∀ s → layer s s
  layer-refl (x , c) = (λ w hw → hw) , (λ w hw → refl)

  layer-trans : ∀ {s t u} → layer s t → layer t u → layer s u
  layer-trans {x , c} {y , d} {z , e} (f₁ , coh₁) (f₂ , coh₂) =
    (λ w hw → f₂ w (f₁ w hw))
    , (λ w hw → trans (coh₁ w hw) (coh₂ w (f₁ w hw)))

  layer-isPreorder : IsPreorder _≡_ layer
  layer-isPreorder = record
    { isEquivalence = record
      { refl  = λ {x} → refl
      ; sym   = λ {x} {y} → sym
      ; trans = λ {x} {y} {z} → trans
      }
    ; reflexive = λ { {x} refl → layer-refl x }
    ; trans     = λ {x} {y} {z} → layer-trans {x} {y} {z}
    }

  obs-refl-map : ∀ s (obs : Obs s)
               → obs-map s s (layer-refl s) obs ≡ obs
  obs-refl-map (x , c) (w , hw) = refl

  -- The composite coverage is definitionally f₂ ∘ f₁, so the equality
  -- is refl.
  --
  -- 复合覆盖定义上为 f₂ ∘ f₁，故相等为 refl。
  obs-trans-map : ∀ {s t u} (l : layer s t) (m : layer t u) (obs : Obs s)
                → obs-map t u m (obs-map s t l obs)
                  ≡ obs-map s u (layer-trans l m) obs
  obs-trans-map {x , c} {y , d} {z , e} l m (w , hw) = refl

  ManifoldEq : State → State → Set _
  ManifoldEq = LayeredEqGen Obs step layer obs-map

  ManifoldEq-isPreorder : IsPreorder _≡_ ManifoldEq
  ManifoldEq-isPreorder =
    LayeredEqGen-Properties.le-isPreorder
      layer-refl
      (λ {s} {t} {u} → layer-trans {s} {t} {u})
      obs-refl-map
      (λ l m obs → obs-trans-map l m obs)

  -- Layer is stable under step, by layer-preserve.
  --
  -- layer 在 step 下稳定，由 layer-preserve 给出。
  layer-stable
    : ∀ {s t} (l : layer s t) (pt : X)
      (hpt : Support (proj₁ s) (proj₂ s) pt)
    → layer (step s (pt , hpt)) (step t (obs-map s t l (pt , hpt)))
  layer-stable {s = x , c} {t = y , d} (f , coh) pt hpt =
    layer-preserve x y c d f coh pt hpt

------------------------------------------------------------------------
-- Concrete ℚ instance
--
-- Charts are open intervals (a, b), support is membership, readout is
-- the identity, and restriction intersects the chart with the unit
-- neighbourhood (y - 1, y + 1) of the restriction point.
-- support-mono is interval inclusion.
--
-- ℚ 上的具体实例
--
-- 坐标卡是开区间 (a, b)，支撑是成员关系，读数是恒等，限制取坐标卡
-- 与限制点单位邻域 (y - 1, y + 1) 的交。support-mono 是区间包含。

private
  -1<0 : (- 1ℚ) < 0ℚ
  -1<0 = *<* -<+

  0<1 : 0ℚ < 1ℚ
  0<1 = *<* (+<+ z<s)

  y-1<y : ∀ y → y - 1ℚ < y
  y-1<y y = subst (λ z → y - 1ℚ < z) (+-identityʳ y) (+-monoʳ-< y -1<0)

  y<y+1 : ∀ y → y < y + 1ℚ
  y<y+1 y = subst (λ z → z < y + 1ℚ) (+-identityʳ y) (+-monoʳ-< y 0<1)

  ⊔-< : ∀ {a b c} → a < c → b < c → a ⊔ b < c
  ⊔-< {a} {b} {c} a<c b<c with ≤-total a b
  ... | inj₁ a≤b = subst (λ z → z < c) (sym (p≤q⇒p⊔q≡q a≤b)) b<c
  ... | inj₂ b≤a = subst (λ z → z < c) (sym (p≥q⇒p⊔q≡p b≤a)) a<c

  <-⊓ : ∀ {a b c} → a < b → a < c → a < b ⊓ c
  <-⊓ {a} {b} {c} a<b a<c with ≤-total b c
  ... | inj₁ b≤c = subst (λ z → a < z) (sym (p≤q⇒p⊓q≡p b≤c)) a<b
  ... | inj₂ c≤b = subst (λ z → a < z) (sym (p≥q⇒p⊓q≡q c≤b)) a<c

  max-<min : ∀ {a b c d} → a < b → a < d → c < b → c < d
           → a ⊔ c < b ⊓ d
  max-<min a<b a<d c<b c<d = <-⊓ (⊔-< a<b c<b) (⊔-< a<d c<d)

ℚManifold : ManifoldStructure ℚ
ℚManifold = record
  { E       = ℚ
  ; Chart   = λ _ → Σ ℚ (λ a → Σ ℚ (λ b → a < b))
  ; Support = λ _ (a , b , _) y → (a < y) × (y < b)
  ; readout = λ _ _ y _ → y
  ; restrict = λ _ (a , b , _) y (ay , yb) →
      let a' = a ⊔ (y - 1ℚ)
          b' = b ⊓ (y + 1ℚ)
      in a' , b' ,
         max-<min (<-trans ay yb) (<-trans ay (y<y+1 y))
                  (<-trans (y-1<y y) yb) (<-trans (y-1<y y) (y<y+1 y))
  ; support-mono = λ _ y (a , b , _) _ w (h₁ , h₂) →
      ≤-<-trans (p≤p⊔q a (y - 1ℚ)) h₁
      , <-≤-trans h₂ (p⊓q≤p b (y + 1ℚ))
  ; readout-restrict = λ _ _ _ _ _ _ → refl
  ; layer-preserve = λ _ _ (a , b , _) (c' , d' , _) f coh pt (pt-a , pt-b) →
      let a'  = a ⊔ (pt - 1ℚ)
          b'  = b ⊓ (pt + 1ℚ)
          c'' = c' ⊔ (pt - 1ℚ)
          d'' = d' ⊓ (pt + 1ℚ)
          f' : ∀ w → (a' < w) × (w < b') → (c'' < w) × (w < d'')
          f' w (h₁ , h₂) =
            let a<w    = ≤-<-trans (p≤p⊔q a (pt - 1ℚ)) h₁
                w<b    = <-≤-trans h₂ (p⊓q≤p b (pt + 1ℚ))
                c'<w , w<d' = f w (a<w , w<b)
                pt-1<w = ≤-<-trans (p≤q⊔p a (pt - 1ℚ)) h₁
                w<pt+1 = <-≤-trans h₂ (p⊓q≤q b (pt + 1ℚ))
            in ⊔-< c'<w pt-1<w , <-⊓ w<d' w<pt+1
      in f' , (λ w hw → refl)
  }

------------------------------------------------------------------------
-- Obstruction
--
-- ManifoldEq is not symmetric on ℚManifold. The chart (0, 1) is
-- contained in (-1, 1) but not vice versa; the witness is w = 0.
--
-- 障碍
--
-- ManifoldEq 在 ℚManifold 上不对称。坐标卡 (0, 1) 包含于 (-1, 1)，
-- 反之不成立；见证点 w = 0。

module ℚManifoldEqObstruction where
  open ManifoldEq ℚManifold
  open ManifoldStructure ℚManifold

  ManifoldEq-refl : ∀ s → ManifoldEq s s
  ManifoldEq-refl (x , c) .Mᵢ.fst =
    (λ w hw → hw) , (λ w hw → refl)
  ManifoldEq-refl (x , c) .Mᵢ.snd (w , hw) =
    ManifoldEq-refl (w , restrict x c w hw)

  private
    -1<1 : - 1ℚ < 1ℚ
    -1<1 = <-trans -1<0 0<1

    s : State
    s = 1ℚ , (0ℚ , 1ℚ , 0<1)

    t : State
    t = 0ℚ , (- 1ℚ , 1ℚ , -1<1)

  -- Coinductive closure of layer-preserve.
  --
  -- layer-preserve 的余归纳闭包。
  layer→ManifoldEq : ∀ {s t} → layer s t → ManifoldEq s t
  layer→ManifoldEq {s = x , c} {t = y , d} l .Mᵢ.fst = l
  layer→ManifoldEq {s = x , c} {t = y , d} l .Mᵢ.snd (w , hw) =
    layer→ManifoldEq
      (layer-preserve x y c d (proj₁ l) (proj₂ l) w hw)

  Mst : ManifoldEq s t
  Mst = layer→ManifoldEq
    ( (λ w (h₁ , h₂) → <-trans -1<0 h₁ , h₂)
    , (λ w hw → refl) )

  -- Applying symmetry to Mst would send w = 0 with proof
  -- (-1 < 0, 0 < 1) to a proof of 0 < 0.
  --
  -- 把对称性应用于 Mst 会把 w = 0 连同证明 (-1 < 0, 0 < 1) 送到
  -- 0 < 0 的证明。
  not-symmetric : ¬ (∀ {s t} → ManifoldEq s t → ManifoldEq t s)
  not-symmetric sym =
    let l = proj₁ ((sym Mst) .Mᵢ.fst)
        h = l 0ℚ (-1<0 , 0<1)
    in <-irrefl refl (proj₁ h)
