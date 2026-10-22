------------------------------------------------------------------------
-- Preservation of the two skeletons under compatible maps
--
-- LayeredEqGen-Map is proved once for the generic skeleton;
-- IndexedLayeredEq-Map is proved directly, since its index type
-- Σ I (X' × X') differs from the X × X used by LayeredEqGen;
-- LayeredEq-Map is a direct instantiation of LayeredEqGen-Map at a
-- constant observation family.
--
-- 两个骨架在相容映射下的保持性
--
-- LayeredEqGen-Map 在最一般的骨架上证明一次；IndexedLayeredEq-Map
-- 直接证明，因其索引类型 Σ I (X' × X') 与 LayeredEqGen 所用的
-- X × X 不同；LayeredEq-Map 是 LayeredEqGen-Map 在常数观察族处的
-- 直接实例化。
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module Equivalence.Map where

open import Agda.Primitive using (Level; _⊔_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Sigma using (Σ; _,_)
open import Data.Product.Base using (_×_; proj₁; proj₂)
open import Data.Product.Properties using (Σ-≡,≡→≡)
open import Relation.Binary.PropositionalEquality.Core using
  (sym; trans; cong; cong₂; subst)
open import Relation.Binary.PropositionalEquality.Properties using (subst-subst-sym)

open import Base.IndexedMType using (Mᵢ)
open import Equivalence.Core using (LayeredEqGen; IndexedLayeredEq; LayeredEq)

------------------------------------------------------------------------
-- Preservation of LayeredEqGen under a compatible map
--
-- LayeredEqGen 在相容映射下的保持性

module LayeredEqGen-Map
    {a b cX cY e} {X : Set a} {Y : Set e}
    {ObsX : X → Set b} {ObsY : Y → Set b}
    {stepX : (x : X) → ObsX x → X}
    {stepY : (y : Y) → ObsY y → Y}
    {layerX : X → X → Set cX}
    {layerY : Y → Y → Set cY}
    (obs-mapX : (x y : X) → layerX x y → ObsX x → ObsX y)
    (obs-mapY : (x y : Y) → layerY x y → ObsY x → ObsY y)
    (f : X → Y)
    (obs-cast : (x : X) → ObsX x → ObsY (f x))
    (obs-cast-inv : (x : X) → ObsY (f x) → ObsX x)
    (obs-cast-inv-right : (x : X) (q : ObsY (f x)) →
        obs-cast x (obs-cast-inv x q) ≡ q)
    (comm : (x : X) (s : ObsX x) →
              f (stepX x s) ≡ stepY (f x) (obs-cast x s))
    (layer-comm : ∀ {x y} → layerX x y → layerY (f x) (f y))
    (obs-coherence : ∀ {x y} (l : layerX x y) (s : ObsX x) →
        obs-cast y (obs-mapX x y l s)
        ≡ obs-mapY (f x) (f y) (layer-comm l) (obs-cast x s))
    where

  le-map : ∀ {x y} → LayeredEqGen ObsX stepX layerX obs-mapX x y
                  → LayeredEqGen ObsY stepY layerY obs-mapY (f x) (f y)
  le-map p .Mᵢ.fst = layer-comm (p .Mᵢ.fst)
  le-map {x} {y} p .Mᵢ.snd q = body
    where
      s  = obs-cast-inv x q
      l  = p .Mᵢ.fst
      l' = layer-comm l

      rec : LayeredEqGen ObsY stepY layerY obs-mapY
              (f (stepX x s))
              (f (stepX y (obs-mapX x y l s)))
      rec = le-map (p .Mᵢ.snd s)

      leftEq : f (stepX x s) ≡ stepY (f x) q
      leftEq = trans (comm x s)
                     (cong (stepY (f x)) (obs-cast-inv-right x q))

      rightEq : f (stepX y (obs-mapX x y l s))
              ≡ stepY (f y) (obs-mapY (f x) (f y) l' q)
      rightEq = trans (comm y (obs-mapX x y l s))
                      (cong (stepY (f y))
                            (trans (obs-coherence l s)
                                   (cong (obs-mapY (f x) (f y) l')
                                         (obs-cast-inv-right x q))))

      body : LayeredEqGen ObsY stepY layerY obs-mapY
               (stepY (f x) q)
               (stepY (f y) (obs-mapY (f x) (f y) l' q))
      body rewrite sym leftEq | sym rightEq = rec

------------------------------------------------------------------------
-- Degeneration: state carries an index
--
-- I/J, X'/Y', layerI/layerJ each live at independent levels.
-- ObsI/ObsJ must share one level, because obs-comm-I :
-- ObsI i ≡ ObsJ (fI i) is a propositional equality and therefore
-- forces both sides into the same universe.
--
-- 退化：状态携带索引
--
-- I/J、X'/Y'、layerI/layerJ 各自位于独立级别；ObsI/ObsJ 必须共享
-- 一个级别，因为 obs-comm-I : ObsI i ≡ ObsJ (fI i) 是命题等式，
-- 从而要求两侧位于同一宇宙。

module IndexedLayeredEq-Map
    {aI aJ bX bY c dI dJ : Level}
    {I : Set aI} {J : Set aJ}
    {X' : I → Set bX} {Y' : J → Set bY}
    {nextX : I → I} {nextY : J → J}
    {ObsI : I → Set c} {ObsJ : J → Set c}
    {stepI : (i : I) → X' i → ObsI i → X' (nextX i)}
    {stepJ : (j : J) → Y' j → ObsJ j → Y' (nextY j)}
    {layerI : (i : I) → X' i → X' i → Set dI}
    {layerJ : (j : J) → Y' j → Y' j → Set dJ}
    (fI : I → J)
    (f' : (i : I) → X' i → Y' (fI i))
    (next-compat : (i : I) → fI (nextX i) ≡ nextY (fI i))
    (obs-comm-I : (i : I) → ObsI i ≡ ObsJ (fI i))
    (step-compat : (i : I) (x : X' i) (s : ObsI i) →
        subst (λ j → Y' j) (next-compat i) (f' (nextX i) (stepI i x s))
        ≡ stepJ (fI i) (f' i x) (subst (λ T → T) (obs-comm-I i) s))
    (layer-comm-I : (i : I) {x y : X' i} →
        layerI i x y → layerJ (fI i) (f' i x) (f' i y))
    where

  private
    P : Set c → Set c
    P T = T

    J' : Set (aJ ⊔ bY)
    J' = Σ J (λ j → Y' j × Y' j)

    A : J' → Set dJ
    A (_ , x , y) = layerJ _ x y

    B : (j' : J') → A j' → Set c
    B (j , _ , _) _ = ObsJ j

    next' : (j' : J') (p : A j') (s : B j' p) → J'
    next' (j , x , y) p s = nextY j , stepJ j x s , stepJ j y s

    -- Substitution along an index equality does not decompose
    -- definitionally into the two components, so an explicit lemma is
    -- needed.
    --
    -- 沿索引等式的替换不会定义性地分解到两个分量上，因此需要显式
    -- 引理。
    subst-× : ∀ {j j' : J} (e : j ≡ j') (p : Y' j × Y' j)
            → subst (λ l → Y' l × Y' l) e p
              ≡ (subst Y' e (proj₁ p) , subst Y' e (proj₂ p))
    subst-× refl p = refl

  le-map : ∀ {i x y}
         → IndexedLayeredEq X' nextX ObsI stepI layerI i x y
         → IndexedLayeredEq Y' nextY ObsJ stepJ layerJ
             (fI i) (f' i x) (f' i y)
  le-map {i} {x} {y} p .Mᵢ.fst = layer-comm-I i (p .Mᵢ.fst)
  le-map {i} {x} {y} p .Mᵢ.snd s = body
    where
      s' : ObsI i
      s' = subst P (sym (obs-comm-I i)) s

      s-eq : subst P (obs-comm-I i) s' ≡ s
      s-eq = subst-subst-sym (obs-comm-I i) {p = s}

      rec : Mᵢ A B next'
              (fI (nextX i) ,
               f' (nextX i) (stepI i x s') ,
               f' (nextX i) (stepI i y s'))
      rec = le-map (p .Mᵢ.snd s')

      stepx : subst Y' (next-compat i) (f' (nextX i) (stepI i x s'))
            ≡ stepJ (fI i) (f' i x) s
      stepx = trans (step-compat i x s')
                    (cong (stepJ (fI i) (f' i x)) s-eq)

      stepy : subst Y' (next-compat i) (f' (nextX i) (stepI i y s'))
            ≡ stepJ (fI i) (f' i y) s
      stepy = trans (step-compat i y s')
                    (cong (stepJ (fI i) (f' i y)) s-eq)

      eq-pair : subst (λ j → Y' j × Y' j) (next-compat i)
                  (f' (nextX i) (stepI i x s') ,
                   f' (nextX i) (stepI i y s'))
              ≡ (stepJ (fI i) (f' i x) s ,
                 stepJ (fI i) (f' i y) s)
      eq-pair = trans (subst-× (next-compat i) _)
                      (cong₂ _,_ stepx stepy)

      i'-eq : (fI (nextX i) ,
               f' (nextX i) (stepI i x s') ,
               f' (nextX i) (stepI i y s'))
            ≡ (nextY (fI i) ,
               stepJ (fI i) (f' i x) s ,
               stepJ (fI i) (f' i y) s)
      i'-eq = Σ-≡,≡→≡ (next-compat i , eq-pair)

      body : Mᵢ A B next'
               (nextY (fI i) ,
                stepJ (fI i) (f' i x) s ,
                stepJ (fI i) (f' i y) s)
      body rewrite sym i'-eq = rec

------------------------------------------------------------------------
-- Degeneration: constant observation
--
-- LayeredEq Obs step layer is LayeredEqGen (λ _ → Obs) step layer
-- (λ _ _ _ o → o); instantiating LayeredEqGen-Map at this observation
-- family gives the map lemma for LayeredEq.
--
-- 退化：常数观察
--
-- LayeredEq Obs step layer 即 LayeredEqGen (λ _ → Obs) step layer
-- (λ _ _ _ o → o)；在该观察族处实例化 LayeredEqGen-Map 即得
-- LayeredEq 的映射引理。

module LayeredEq-Map
    {a b c d} {X : Set a} {Y : Set d}
    {ObsX : Set b} {ObsY : Set b}
    {stepX : X → ObsX → X} {stepY : Y → ObsY → Y}
    {layerX : X → X → Set c} {layerY : Y → Y → Set c}
    (f : X → Y)
    (obs-cast : ObsX → ObsY)
    (obs-cast-inv : ObsY → ObsX)
    (obs-cast-inv-right : (q : ObsY) → obs-cast (obs-cast-inv q) ≡ q)
    (comm : (x : X) (s : ObsX) →
              f (stepX x s) ≡ stepY (f x) (obs-cast s))
    (layer-comm : ∀ {x y} → layerX x y → layerY (f x) (f y))
    where

  private
    -- With constant observation, obs-coherence reduces to refl.
    --
    -- 常数观察下，obs-coherence 退化为 refl。
    obs-coherence : ∀ {x y} (l : layerX x y) (s : ObsX) →
        obs-cast s ≡ obs-cast s
    obs-coherence l s = refl

  module M = LayeredEqGen-Map
    {X = X} {Y = Y}
    {ObsX = λ _ → ObsX} {ObsY = λ _ → ObsY}
    {stepX = stepX} {stepY = stepY}
    {layerX = layerX} {layerY = layerY}
    (λ _ _ _ o → o) (λ _ _ _ o → o) f
    (λ _ → obs-cast) (λ _ → obs-cast-inv)
    (λ _ → obs-cast-inv-right)
    comm layer-comm obs-coherence

  le-map : ∀ {x y} → LayeredEq ObsX stepX layerX x y
                  → LayeredEq ObsY stepY layerY (f x) (f y)
  le-map = M.le-map
