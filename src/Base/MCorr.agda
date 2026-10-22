------------------------------------------------------------------------
-- E-M-types: indexed M-types over an edge family
--
-- Carried functional correspondences over this indexed M-type form
-- the category MCorrCat.
--
-- E-M 型：边族上的索引 M 型
--
-- 此索引 M 型上的携带式功能对应构成范畴 MCorrCat。
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module Base.MCorr where

open import Agda.Primitive using (Level; _⊔_; lsuc)
open import Agda.Builtin.Sigma using (Σ; _,_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Product.Base using (_×_; proj₁; proj₂)
open import Function.Base using (id; _∘_)
open import Relation.Binary.PropositionalEquality.Core using (cong; sym; trans)
open import Relation.Binary.PropositionalEquality.Properties using (trans-reflʳ)
open import Relation.Binary.Structures using (IsEquivalence)

open import Categories.Category.Core using (Category)

------------------------------------------------------------------------
-- E-M-types: indexed M-types over an edge family
--
-- Indexed by the vertex set I; parameterised by the edge family E.
--
-- E-M 型：边族上的索引 M 型
--
-- 以顶点集 I 为索引、以边族 E 为参数。

record M {i a b : Level} {I : Set i}
         (A : I → Set a)
         (E : (x : I) (a : A x) (y : I) → Set b)
         (x : I) : Set (i ⊔ a ⊔ b) where
  coinductive
  field
    here  : A x
    below : (y : I) (e : E x here y) → M A E y
open M public

------------------------------------------------------------------------
-- Fibre adjunction between homogeneous edge sets
--
-- 同质边集间的纤维伴随

record FiberAdj {ℓp ℓr : Level} (P : Set ℓp) (R : Set ℓr)
       : Set (ℓp ⊔ ℓr) where
  field
    to : R → P
    fro : P → R
    η   : (r : R) → fro (to r) ≡ r
    ε   : (p : P) → to (fro p) ≡ p

  symAdj : FiberAdj R P
  symAdj = record { to = fro ; fro = to ; η = ε ; ε = η }
open FiberAdj public

------------------------------------------------------------------------
-- Identity and composition of fibre adjunctions
--
-- 纤维伴随的恒等与复合

idAdj : ∀ {ℓ : Level} (P : Set ℓ) → FiberAdj P P
idAdj P = record { to = id ; fro = id ; η = λ _ → refl ; ε = λ _ → refl }

compAdj : ∀ {ℓr ℓg ℓh : Level}
          (R : Set ℓr) (G : Set ℓg) (H : Set ℓh)
        → FiberAdj G R → FiberAdj H G → FiberAdj H R
compAdj R G H a₁ a₂ = record
  { to  = FiberAdj.to a₂ ∘ FiberAdj.to a₁
  ; fro = FiberAdj.fro a₁ ∘ FiberAdj.fro a₂
  ; η = λ r → trans (cong (FiberAdj.fro a₁)
                         (FiberAdj.η a₂ (FiberAdj.to a₁ r)))
                   (FiberAdj.η a₁ r)
  ; ε = λ p → trans (cong (FiberAdj.to a₂)
                         (FiberAdj.ε a₁ (FiberAdj.fro a₂ p)))
                   (FiberAdj.ε a₂ p)
  }

------------------------------------------------------------------------
-- Coinductive bisimulation at the same index
--
-- 同一索引处的余归纳互模拟

record _≈M_ {i a b : Level} {I : Set i} {A : I → Set a}
            {E : (x : I) (a : A x) (y : I) → Set b} {x : I}
            (t s : M A E x) : Set (i ⊔ a ⊔ b) where
  coinductive
  field
    here-eq : here t ≡ here s
    below-eq : ∀ (y : I)
      → Σ (FiberAdj (E x (here s) y) (E x (here t) y)) λ adj
      →   (∀ (e₁ : E x (here t) y)
           → (below t y e₁) ≈M (below s y (FiberAdj.to adj e₁)))
        × (∀ (e₂ : E x (here s) y)
           → (below s y e₂) ≈M (below t y (FiberAdj.fro adj e₂)))
open _≈M_

≈M-refl : ∀ {i a b : Level} {I : Set i} {A : I → Set a}
            {E : (x : I) (a : A x) (y : I) → Set b} {x : I}
            (t : M A E x) → t ≈M t
≈M-refl t .here-eq = refl
≈M-refl {E = E} {x = x} t .below-eq y =
    idAdj (E x (here t) y)
  , ( (λ e₁ → ≈M-refl (below t y e₁))
    , (λ e₂ → ≈M-refl (below t y e₂)) )

------------------------------------------------------------------------
-- Children along homogeneously equal edges in the same fibre
--
-- 同一纤维内同质相等边上的子树

edge-≈ : ∀ {i a b : Level} {I : Set i} {A : I → Set a}
           {E : (x : I) (a : A x) (y : I) → Set b} {x y : I}
           (u : M A E x) {e e' : E x (here u) y}
       → e ≡ e' → below u y e ≈M below u y e'
edge-≈ u {e = z} {e' = .z} refl = ≈M-refl (below u _ z)

≈M-trans : ∀ {i a b : Level} {I : Set i} {A : I → Set a}
             {E : (x : I) (a : A x) (y : I) → Set b} {x : I}
             {t g h : M A E x}
         → t ≈M g → g ≈M h → t ≈M h
≈M-trans {E = E} {x = x} {t = t} {g = g} {h = h} p q .here-eq =
  trans (here-eq p) (here-eq q)
≈M-trans {E = E} {x = x} {t = t} {g = g} {h = h} p q .below-eq y
  with p .below-eq y | q .below-eq y
... | adj₁ , (fwd₁ , bwd₁) | adj₂ , (fwd₂ , bwd₂) =
    compAdj (E x (here t) y) (E x (here g) y) (E x (here h) y) adj₁ adj₂
  , ( (λ e₁ → ≈M-trans (fwd₁ e₁) (fwd₂ (FiberAdj.to adj₁ e₁)))
    , (λ e₃ → ≈M-trans (bwd₂ e₃) (bwd₁ (FiberAdj.fro adj₂ e₃))) )

≈M-sym : ∀ {i a b : Level} {I : Set i} {A : I → Set a}
           {E : (x : I) (a : A x) (y : I) → Set b} {x : I}
           {t s : M A E x}
       → t ≈M s → s ≈M t
≈M-sym {E = E} {x = x} {t = t} {s = s} p .here-eq = sym (here-eq p)
≈M-sym {E = E} {x = x} {t = t} {s = s} p .below-eq y
  with p .below-eq y
... | adj , (fwd , bwd) = symAdj adj , (bwd , fwd)

------------------------------------------------------------------------
-- One-step functional correspondence over an index layer R
--
-- 索引层 R 上的一步功能对应

record Step {i j a b c d ℓr : Level}
            {I : Set i} {J : Set j}
            (R : I → J → Set ℓr)
            (A : I → Set a)
            (E : (x : I) (a : A x) (y : I) → Set b)
            (C : J → Set c)
            (D : (y : J) (q : C y) (v : J) → Set d)
            {x : I} {y : J} (r : R x y)
       : Set (i ⊔ j ⊔ a ⊔ b ⊔ c ⊔ d ⊔ ℓr) where
  field
    shapeᴿ : A x → C y

    -- Canonical source child of target child v, edge-independent.
    --
    -- 目标子节点 v 的规范源子节点，与边无关。
    child : (a : A x) (v : J) → Σ I λ x' → R x' v

    -- Whole-fibre adjunction at the canonical child; fro is the edge
    -- pullback.
    --
    -- 规范子节点上的整纤维伴随；fro 即边拉回。
    edge-adj : (a : A x) (v : J)
             → FiberAdj (D y (shapeᴿ a) v)
                        (E x a (proj₁ (child a v)))

  pull : (a : A x) (v : J) (q : D y (shapeᴿ a) v)
       → Σ I λ x' → Σ (E x a x') λ e → R x' v
  pull a v q =
    let x' , r' = child a v
    in x' , FiberAdj.fro (edge-adj a v) q , r'
open Step public

------------------------------------------------------------------------
-- Morphism and subst-free tree action
--
-- 态射与零 subst 树作用

record Morph {i j a b c d ℓr : Level}
             {I : Set i} {J : Set j}
             (R : I → J → Set ℓr)
             (A : I → Set a)
             (E : (x : I) (a : A x) (y : I) → Set b)
             (C : J → Set c)
             (D : (y : J) (q : C y) (v : J) → Set d)
       : Set (i ⊔ j ⊔ a ⊔ b ⊔ c ⊔ d ⊔ ℓr) where
  field
    step : ∀ {x : I} {y : J} (r : R x y)
         → Step R A E C D r

  mapR : ∀ {x : I} {y : J} → R x y → M A E x → M C D y
  mapR r t .here   = shapeᴿ (step r) (here t)

  -- `let` (not `with`) keeps the continuation definitionally unfolding.
  --
  -- 用 `let`（非 `with`）保持连续化定义性展开。
  mapR r t .below v q =
    let x' , e , r' = pull (step r) (here t) v q
    in mapR r' (below t x' e)
open Morph public

------------------------------------------------------------------------
-- Relational composition of index layers
--
-- 索引层的关系复合

infixr 9 _⍮_
_⍮_ : ∀ {i j k ℓ₁ ℓ₂ : Level}
        {I : Set i} {J : Set j} {K : Set k}
      (R : I → J → Set ℓ₁) (S : J → K → Set ℓ₂)
    → I → K → Set (j ⊔ ℓ₁ ⊔ ℓ₂)
(R ⍮ S) x z = Σ _ λ y → Σ (R x y) λ _ → S y z

------------------------------------------------------------------------
-- Composition of carried correspondences
--
-- 携带式对应的复合

compM :
  ∀ {i j k a b c d e f ℓ₁ ℓ₂ : Level}
    {I : Set i} {J : Set j} {K : Set k}
    {A : I → Set a} {E : (x : I) (a : A x) (y : I) → Set b}
    {C : J → Set c} {D : (y : J) (q : C y) (v : J) → Set d}
    {G : K → Set e} {F : (z : K) (q : G z) (w : K) → Set f}
    {R : I → J → Set ℓ₁} {S : J → K → Set ℓ₂}
  → Morph R A E C D → Morph S C D G F
  → Morph (R ⍮ S) A E G F
compM {E = E} {D = D} {F = F} φ ψ .step {x = x} {y = z} (ym , r , s) =
  let φr = Morph.step φ r
      ψs = Morph.step ψ s
  in record
  { shapeᴿ = λ a → Step.shapeᴿ ψs (Step.shapeᴿ φr a)
  ; child = λ a w →
      let ym' , s' = Step.child ψs (Step.shapeᴿ φr a) w
          x' , r'  = Step.child φr a ym'
      in x' , (ym' , r' , s')
  ; edge-adj = λ a w →
      let ym' , s' = Step.child ψs (Step.shapeᴿ φr a) w
          x' , r'  = Step.child φr a ym'
      in compAdj (E x a x')
                 (D ym (Step.shapeᴿ φr a) ym')
                 (F z (Step.shapeᴿ ψs (Step.shapeᴿ φr a)) w)
                 (Step.edge-adj φr a ym')
                 (Step.edge-adj ψs (Step.shapeᴿ φr a) w)
  }

------------------------------------------------------------------------
-- Free path-groupoid instance
--
-- 自由路径广群实例

idM : ∀ {i a b : Level} {I : Set i}
        (A : I → Set a) (E : (x : I) (a : A x) (y : I) → Set b)
      → Morph (λ (x y : I) → x ≡ y) A E A E
idM A E .step {x = x} {y = .x} refl = record
  { shapeᴿ  = λ a → a
  ; child    = λ a v → v , refl
  ; edge-adj = λ a v → idAdj (E x a v)
  }

idM-edge-adj : ∀ {i a b : Level} {I : Set i} {A : I → Set a}
                 {E : (x : I) (a : A x) (y : I) → Set b}
                 {x x₁ x₀ : I} (a : A x) (d : x₁ ≡ x₀)
             → FiberAdj (E x a x₀) (E x a x₁)
idM-edge-adj {E = E} {x₁ = z} {x₀ = .z} a refl = idAdj (E _ a z)

------------------------------------------------------------------------
-- Bundled edge-family system
--
-- 束装的边族系统

record Sys (i a b : Level) : Set (lsuc (i ⊔ a ⊔ b)) where
  field
    I : Set i
    A : I → Set a
    E : (x : I) (a : A x) (y : I) → Set b
open Sys public

------------------------------------------------------------------------
-- Deterministic carried morphism
--
-- 确定性携带态射

record FMap {i j a b c d : Level}
            (X : Sys i a b) (Y : Sys j c d)
       : Set (i ⊔ j ⊔ a ⊔ b ⊔ c ⊔ d) where
  field
    u     : I X → I Y
    shape : (x : I X) → A X x → A Y (u x)

    -- Canonical source child of target child v, edge-independent,
    -- carrying the graph witness u x' ≡ v.
    --
    -- 目标子节点 v 的规范源子节点，与边无关，携带图见证 u x' ≡ v。
    childF : (x : I X) (a : A X x) (v : I Y)
           → Σ (I X) λ x' → u x' ≡ v

    -- Whole-fibre adjunction at the canonical child.
    --
    -- 规范子节点上的整纤维伴随。
    adjF  : (x : I X) (a : A X x) (v : I Y)
          → FiberAdj (E Y (u x) (shape x a) v)
                     (E X x a (proj₁ (childF x a v)))

    -- Index-layer coherence: carries both the child-index equation d
    -- and the witness compatibility r₁ ≡ trans (cong u d) r₀.
    --
    -- 索引层相干性：同时携带子索引等式 d 与见证相容性
    -- r₁ ≡ trans (cong u d) r₀。
    childF-coh : (x : I X) {a a' : A X x} (e : a ≡ a') (v : I Y)
               → Σ (proj₁ (childF x a' v) ≡ proj₁ (childF x a v)) λ d
               → proj₂ (childF x a' v)
                 ≡ trans (cong u d) (proj₂ (childF x a v))

  pullF : (x : I X) (a : A X x) (v : I Y)
          (q : E Y (u x) (shape x a) v)
        → Σ (I X) λ x' → Σ (E X x a x') λ e → u x' ≡ v
  pullF x a v q =
    let x' , r' = childF x a v
    in x' , FiberAdj.fro (adjF x a v) q , r'

  asMorph : Morph (λ (x : I X) (v : I Y) → u x ≡ v)
                  (A X) (E X) (A Y) (E Y)
  asMorph .step {x = x} {y = .(u x)} refl = record
    { shapeᴿ  = shape x
    ; child    = childF x
    ; edge-adj = adjF x
    }

  mapF : (x : I X) → M (A X) (E X) x → M (A Y) (E Y) (u x)
  mapF x t = mapR asMorph refl t
open FMap public

------------------------------------------------------------------------
-- Identity and composition
--
-- 恒等与复合

idF : ∀ {i a b : Level} (X : Sys i a b) → FMap X X
idF X = record
  { u          = id
  ; shape      = λ _ a → a
  ; childF     = λ x a v → v , refl
  ; adjF       = λ x a v → idAdj (E X x a v)
  ; childF-coh = λ x e v → refl , refl
  }

compF : ∀ {i j k a b c d e f : Level}
          {X : Sys i a b} {Y : Sys j c d} {Z : Sys k e f}
      → FMap Y Z → FMap X Y → FMap X Z
compF {X = X} {Y = Y} {Z = Z} g f = record
  { u          = ug ∘ uf
  ; shape      = λ x a → shapeg (uf x) (shapef x a)
  ; childF     = childcomp
  ; adjF       = adjcomp
  ; childF-coh = cohcomp
  }
  where
    uf     = FMap.u f
    ug     = FMap.u g
    shapef = FMap.shape f
    shapeg = FMap.shape g

    childcomp : (x : I X) (a : A X x) (w : I Z)
             → Σ (I X) λ x'' → ug (uf x'') ≡ w
    childcomp x a w =
      let y' , eg = FMap.childF g (uf x) (shapef x a) w
          x'' , ef = FMap.childF f x a y'
      in x'' , trans (cong ug ef) eg

    -- Same canonical decomposition as childcomp, so its fro is
    -- definitionally the two-stage pullback used by nested mapR.
    --
    -- 与 childcomp 采用相同规范分解，故其 fro 定义性等于嵌套 mapR
    -- 的两段边拉回。
    adjcomp : (x : I X) (a : A X x) (w : I Z)
            → FiberAdj (E Z (ug (uf x))
                           (shapeg (uf x) (shapef x a)) w)
                       (E X x a (proj₁ (childcomp x a w)))
    adjcomp x a w =
      let y' , _  = FMap.childF g (uf x) (shapef x a) w
          x'' , _ = FMap.childF f x a y'
      in compAdj (E X x a x'')
                 (E Y (uf x) (shapef x a) y')
                 (E Z (ug (uf x)) (shapeg (uf x) (shapef x a)) w)
                 (FMap.adjF f x a y')
                 (FMap.adjF g (uf x) (shapef x a) w)

    cohcomp : (x : I X) {a a' : A X x} (e : a ≡ a') (w : I Z)
            → Σ (proj₁ (childcomp x a' w) ≡ proj₁ (childcomp x a w)) λ d
            → proj₂ (childcomp x a' w)
              ≡ trans (cong (ug ∘ uf) d) (proj₂ (childcomp x a w))
    cohcomp x {a = z} {a' = .z} refl w = refl , refl

------------------------------------------------------------------------
-- Subst-free relocation
--
-- 零 subst 重定位

relocate : ∀ {i a b : Level} {I : Set i} {A : I → Set a}
             {E : (x : I) (a : A x) (y : I) → Set b} {x y : I}
         → x ≡ y → M A E x → M A E y
relocate {A = A} {E = E} refl t = t

------------------------------------------------------------------------
-- Behavioural equivalence
--
-- 行为等价

_≈F_ : ∀ {i j a b c d : Level}
         {X : Sys i a b} {Y : Sys j c d}
       → FMap X Y → FMap X Y → Set (i ⊔ j ⊔ a ⊔ b ⊔ c ⊔ d)
_≈F_ {X = X} {Y = Y} f g =
  ∀ (x : I X)
  → Σ (FMap.u f x ≡ FMap.u g x)
      (λ r → ∀ (t : M (A X) (E X) x)
            → relocate r (FMap.mapF f x t) ≈M FMap.mapF g x t)

------------------------------------------------------------------------
-- Relocation along refl is the identity up to bisimulation
--
-- 沿 refl 重定位在互模拟意义下是恒等

mutual
  ≈rel-refl : ∀ {i a b : Level} {I : Set i} {A : I → Set a}
                {E : (x : I) (a : A x) (y : I) → Set b} {x : I}
                (t : M A E x) → relocate refl t ≈M t
  ≈rel-refl {E = E} {x = x} t .here-eq = refl
  ≈rel-refl {E = E} {x = x} t .below-eq y =
      idAdj (E x (here t) y)
    , ( (λ e₁ → ≈rel-refl (below t y e₁))
      , (λ e₂ → ≈rel-refl˘ (below t y e₂)) )

  ≈rel-refl˘ : ∀ {i a b : Level} {I : Set i} {A : I → Set a}
                 {E : (x : I) (a : A x) (y : I) → Set b} {x : I}
                 (t : M A E x) → t ≈M relocate refl t
  ≈rel-refl˘ {E = E} {x = x} t .here-eq = refl
  ≈rel-refl˘ {E = E} {x = x} t .below-eq y =
      idAdj (E x (here t) y)
    , ( (λ e₁ → ≈rel-refl˘ (below t y e₁))
      , (λ e₂ → ≈rel-refl (below t y e₂)) )

≈F-refl : ∀ {i j a b c d : Level}
            {X : Sys i a b} {Y : Sys j c d}
            (f : FMap X Y) → f ≈F f
≈F-refl f x = refl , λ t → ≈rel-refl (FMap.mapF f x t)

------------------------------------------------------------------------
-- Groupoid action of relocation
--
-- 重定位的广群作用

≈rel-resp : ∀ {i a b : Level} {I : Set i} {A : I → Set a}
              {E : (x : I) (a : A x) (y : I) → Set b} {x y : I}
              (r : x ≡ y) (t s : M A E x)
          → t ≈M s → relocate r t ≈M relocate r s
≈rel-resp refl t s p =
  ≈M-trans (≈rel-refl t) (≈M-trans p (≈rel-refl˘ s))

≈rel-round : ∀ {i a b : Level} {I : Set i} {A : I → Set a}
               {E : (x : I) (a : A x) (y : I) → Set b} {x y : I}
               (r : x ≡ y) (t : M A E x)
           → relocate (sym r) (relocate r t) ≈M t
≈rel-round {x = x} {y = .x} refl t =
  ≈M-trans (≈rel-refl (relocate refl t)) (≈rel-refl t)

≈rel-comp : ∀ {i a b : Level} {I : Set i} {A : I → Set a}
              {E : (x : I) (a : A x) (y : I) → Set b} {x y z : I}
              (r : x ≡ y) (s : y ≡ z) (t : M A E x)
          → relocate (trans r s) t ≈M relocate s (relocate r t)
≈rel-comp {x = x} {y = .x} {z = .x} refl refl t =
  ≈rel-refl˘ (relocate refl t)

rel-child-nat : ∀ {i a b : Level} {I : Set i} {A : I → Set a}
                  {E : (x : I) (a : A x) (y : I) → Set b}
                  {x x₁ x₀ : I}
                  (u : M A E x) (d : x₁ ≡ x₀)
                  (e0 : E x (here u) x₀)
              → relocate {E = E} d
                  (below u x₁ (FiberAdj.fro
                     (idM-edge-adj {E = E} {x = x} (here u) d) e0))
                ≈M below u x₀ e0
rel-child-nat {E = E} {x = x} {x₁ = z} {x₀ = .z} u refl e0 =
  ≈rel-refl (below u z e0)

≈F-sym : ∀ {i j a b c d : Level}
           {X : Sys i a b} {Y : Sys j c d}
           {f g : FMap X Y}
       → f ≈F g → g ≈F f
≈F-sym {f = f} {g = g} p x
  with p x
... | r , h =
    sym r
  , λ t → let a = FMap.mapF f x t
              b = FMap.mapF g x t
          in ≈M-trans (≈rel-resp (sym r) b (relocate r a) (≈M-sym (h t)))
                      (≈rel-round r a)

≈F-trans : ∀ {i j a b c d : Level}
             {X : Sys i a b} {Y : Sys j c d}
             {f g h : FMap X Y}
         → f ≈F g → g ≈F h → f ≈F h
≈F-trans {f = f} {g = g} {h = h} p q x
  with p x | q x
... | r₁ , h₁ | r₂ , h₂ =
    trans r₁ r₂
  , λ t → let a = FMap.mapF f x t
              b = FMap.mapF g x t
          in ≈M-trans (≈rel-comp r₁ r₂ a)
                      (≈M-trans (≈rel-resp r₂ (relocate r₁ a) b (h₁ t))
                                (h₂ t))

≈F-isEquivalence : ∀ {i j a b c d : Level}
                     {X : Sys i a b} {Y : Sys j c d}
                 → IsEquivalence (_≈F_ {X = X} {Y = Y})
≈F-isEquivalence = record
  { refl  = λ {f} → ≈F-refl f
  ; sym   = ≈F-sym
  ; trans = ≈F-trans
  }

------------------------------------------------------------------------
-- Coinductive fusion
--
-- 余归纳融合

module Fusion {i j k a b c d e fℓ : Level}
             {X : Sys i a b} {Y : Sys j c d} {Z : Sys k e fℓ}
             (gm : FMap Y Z) (fm : FMap X Y) where

  uf  = FMap.u fm
  ug  = FMap.u gm
  asF = FMap.asMorph fm
  asG = FMap.asMorph gm
  asC = FMap.asMorph (compF gm fm)

  mutual
    fusion : ∀ {x : I X} {y : I Y} {z : I Z}
               (rf : uf x ≡ y) (rg : ug y ≡ z)
               (t : M (A X) (E X) x)
           → mapR asC (trans (cong ug rf) rg) t
             ≈M mapR asG rg (mapR asF rf t)
    fusion {x = x} {y = .(uf x)} {z = .(ug (uf x))} refl refl t .here-eq =
      refl
    fusion {x = x} {y = .(uf x)} {z = .(ug (uf x))} refl refl t .below-eq w =
        idAdj (E Z (ug (uf x))
                   (FMap.shape gm (uf x) (FMap.shape fm x (here t))) w)
      , ( (λ q → let y' , eY , eg =
                        FMap.pullF gm (uf x) (FMap.shape fm x (here t)) w q
                     x'' , eX , ef =
                        FMap.pullF fm x (here t) y' eY
                 in fusion ef eg (below t x'' eX))
        , (λ q → let y' , eY , eg =
                        FMap.pullF gm (uf x) (FMap.shape fm x (here t)) w q
                     x'' , eX , ef =
                        FMap.pullF fm x (here t) y' eY
                 in fusion˘ ef eg (below t x'' eX)) )

    fusion˘ : ∀ {x : I X} {y : I Y} {z : I Z}
                (rf : uf x ≡ y) (rg : ug y ≡ z)
                (t : M (A X) (E X) x)
            → mapR asG rg (mapR asF rf t)
              ≈M mapR asC (trans (cong ug rf) rg) t
    fusion˘ {x = x} {y = .(uf x)} {z = .(ug (uf x))} refl refl t .here-eq =
      refl
    fusion˘ {x = x} {y = .(uf x)} {z = .(ug (uf x))} refl refl t .below-eq w =
        idAdj (E Z (ug (uf x))
                   (FMap.shape gm (uf x) (FMap.shape fm x (here t))) w)
      , ( (λ q → let y' , eY , eg =
                        FMap.pullF gm (uf x) (FMap.shape fm x (here t)) w q
                     x'' , eX , ef =
                        FMap.pullF fm x (here t) y' eY
                 in fusion˘ ef eg (below t x'' eX))
        , (λ q → let y' , eY , eg =
                        FMap.pullF gm (uf x) (FMap.shape fm x (here t)) w q
                     x'' , eX , ef =
                        FMap.pullF fm x (here t) y' eY
                 in fusion ef eg (below t x'' eX)) )

------------------------------------------------------------------------
-- Consequences of fusion
--
-- 融合的推论

mapF-comp : ∀ {i j k a b c d e fℓ : Level}
              {X : Sys i a b} {Y : Sys j c d} {Z : Sys k e fℓ}
              (gm : FMap Y Z) (fm : FMap X Y)
              (x : I X) (t : M (A X) (E X) x)
          → FMap.mapF (compF gm fm) x t
            ≈M FMap.mapF gm (FMap.u fm x) (FMap.mapF fm x t)
mapF-comp gm fm x t = Fusion.fusion gm fm refl refl t

mutual
  mapF-id : ∀ {i a b : Level} {X : Sys i a b}
              (x : I X) (t : M (A X) (E X) x)
          → FMap.mapF (idF X) x t ≈M relocate refl t
  mapF-id {X = X} x t .here-eq = refl
  mapF-id {X = X} x t .below-eq w =
      idAdj (E X x (here t) w)
    , ( (λ q → mapF-id w (below t w q))
      , (λ q → mapF-id˘ w (below t w q)) )

  mapF-id˘ : ∀ {i a b : Level} {X : Sys i a b}
               (x : I X) (t : M (A X) (E X) x)
           → relocate refl t ≈M FMap.mapF (idF X) x t
  mapF-id˘ {X = X} x t .here-eq = refl
  mapF-id˘ {X = X} x t .below-eq w =
      idAdj (E X x (here t) w)
    , ( (λ q → mapF-id˘ w (below t w q))
      , (λ q → mapF-id w (below t w q)) )

------------------------------------------------------------------------
-- Congruence of the deterministic tree action
--
-- 确定性树作用的同余

module Cong {i j a b c d : Level}
           {X : Sys i a b} {Y : Sys j c d}
           (f : FMap X Y) where
  private
    asF  = FMap.asMorph f
    uf   = FMap.u f
    mapf = FMap.mapF f

  mutual
    mapR-rel : ∀ {x : I X} {v : I Y} (r : uf x ≡ v)
                 (t : M (A X) (E X) x)
             → mapR asF r t ≈M relocate r (mapf x t)
    mapR-rel {x = x} {v = .(uf x)} refl t = ≈rel-refl˘ (mapf x t)

    mapR-rel˘ : ∀ {x : I X} {v : I Y} (r : uf x ≡ v)
                  (t : M (A X) (E X) x)
              → relocate r (mapf x t) ≈M mapR asF r t
    mapR-rel˘ {x = x} {v = .(uf x)} refl t = ≈rel-refl (mapf x t)

    mapR-r-eq : ∀ {x : I X} {v : I Y} {r r' : uf x ≡ v}
                  (eq : r ≡ r') (t : M (A X) (E X) x)
              → mapR asF r t ≈M mapR asF r' t
    mapR-r-eq {x = x} {r = z} {r' = .z} refl t =
      ≈M-refl (mapR asF z t)

    -- The two directions are a mutual pair; each child calls the
    -- matching direction bare (never wrapped by ≈M-sym).
    --
    -- 两方向构成互逆对；每个子节点裸调用匹配方向（不被 ≈M-sym 包裹）。
    mapR-cross : ∀ {x₁ x₀ : I X} {v : I Y}
                   (d : x₁ ≡ x₀) (r₀ : uf x₀ ≡ v)
                   (s₁ : M (A X) (E X) x₁)
               → mapR asF r₀ (relocate d s₁)
                 ≈M mapR asF (trans (cong uf d) r₀) s₁
    mapR-cross {x₁ = z} {x₀ = .z} {v = .(uf z)} refl refl s₁ .here-eq =
      refl
    mapR-cross {x₁ = z} {x₀ = .z} {v = .(uf z)} refl refl s₁ .below-eq w =
      idAdj (E Y (uf z) (FMap.shape f z (here s₁)) w)
      , ( (λ q → let x' , e , r' = FMap.pullF f z (here s₁) w q
                 in mapR-cross refl r' (below s₁ x' e))
        , (λ q → let x' , e , r' = FMap.pullF f z (here s₁) w q
                 in mapR-cross˘ refl r' (below s₁ x' e)) )

    mapR-cross˘ : ∀ {x₁ x₀ : I X} {v : I Y}
                    (d : x₁ ≡ x₀) (r₀ : uf x₀ ≡ v)
                    (s₁ : M (A X) (E X) x₁)
                → mapR asF (trans (cong uf d) r₀) s₁
                  ≈M mapR asF r₀ (relocate d s₁)
    mapR-cross˘ {x₁ = z} {x₀ = .z} {v = .(uf z)} refl refl s₁ .here-eq =
      refl
    mapR-cross˘ {x₁ = z} {x₀ = .z} {v = .(uf z)} refl refl s₁ .below-eq w =
      idAdj (E Y (uf z) (FMap.shape f z (here s₁)) w)
      , ( (λ q → let x' , e , r' = FMap.pullF f z (here s₁) w q
                 in mapR-cross˘ refl r' (below s₁ x' e))
        , (λ q → let x' , e , r' = FMap.pullF f z (here s₁) w q
                 in mapR-cross refl r' (below s₁ x' e)) )

    -- Fused congruence engine. All index equations are J-eliminated
    -- up front; the ascribed copy h' forces the refl conversion once
    -- at tree level. Each output child is one bare gow / gow˘ call.
    --
    -- 融合同余引擎。所有索引等式前端 J 消去；带类型标注的副本 h' 在
    -- 树层级强制一次 refl 转换。每个输出子节点恰为一次裸 gow / gow˘
    -- 调用。
    gow : ∀ {xS xT : I X} {v : I Y}
            (d : xS ≡ xT) (rT : uf xT ≡ v) {rS : uf xS ≡ v}
            (ww : rS ≡ trans (cong uf d) rT)
            {T : M (A X) (E X) xT} {S : M (A X) (E X) xS}
            (h : T ≈M relocate d S)
        → mapR asF rT T ≈M mapR asF rS S
    gow˘ : ∀ {xS xT : I X} {v : I Y}
             (d : xS ≡ xT) (rT : uf xT ≡ v) {rS : uf xS ≡ v}
             (ww : rS ≡ trans (cong uf d) rT)
             {T : M (A X) (E X) xT} {S : M (A X) (E X) xS}
             (h : T ≈M relocate d S)
         → mapR asF rS S ≈M mapR asF rT T

    gow {xS = z} {xT = .z} {v = .(uf z)} refl refl {rS = refl} refl h
      .here-eq = cong (FMap.shape f z) (h .here-eq)
    gow {xS = z} {xT = .z} {v = .(uf z)} refl refl {rS = refl} refl
        {T = T} {S = S} h
      .below-eq w = adjout , (fwd , bwd)
      where
      h' : T ≈M S
      h' = h
      e   = h' .here-eq
      At  = FMap.adjF f z (here T) w
      As  = FMap.adjF f z (here S) w
      Pt = E Y (uf z) (FMap.shape f z (here T)) w
      Ps = E Y (uf z) (FMap.shape f z (here S)) w
      dd~ = FMap.childF-coh f z e w
      dd  = proj₁ dd~
      ww' = proj₂ dd~
      Dadj = idM-edge-adj {E = E X} {x = z} (here S) dd
      xT' = proj₁ (FMap.childF f z (here T) w)
      xS' = proj₁ (FMap.childF f z (here S) w)
      Rt  = E X z (here T) xT'
      Rs₀ = E X z (here S) xT'
      Rs₁ = E X z (here S) xS'
      bp  = h' .below-eq xT'
      padj = proj₁ bp
      pfwd = proj₁ (proj₂ bp)
      pbwd = proj₂ (proj₂ bp)
      c02 = compAdj Rs₀ Rs₁ Ps (FiberAdj.symAdj Dadj) As
      c03 = compAdj Rt Rs₀ Ps padj c02
      adjout : FiberAdj Ps Pt
      adjout = compAdj Pt Rt Ps (FiberAdj.symAdj At) c03

      fwd : ∀ (qT : Pt)
          → below (mapR asF refl T) w qT
            ≈M below (mapR asF refl S) w (FiberAdj.to adjout qT)
      fwd qT =
        let xT₁ , eT , rT' = FMap.pullF f z (here T) w qT
            qS = FiberAdj.to adjout qT
            xS₁ , _ , rS' = FMap.pullF f z (here S) w qS
            e0  = FiberAdj.to padj eT
            e1  = FiberAdj.fro Dadj e0
            ηs  = FiberAdj.η As e1
            Tsub    = below T xT₁ eT
            B0      = below S xT₁ e0
            SsubCan = below S xS₁ e1
            Sraw    = below S xS₁ (FiberAdj.fro As (FiberAdj.to As e1))
            hrec : Tsub ≈M relocate dd Sraw
            hrec =
              ≈M-trans (pfwd eT)
              (≈M-trans (≈rel-refl B0)
              (≈M-trans (≈M-sym (rel-child-nat S dd e0))
                        (≈M-sym (≈rel-resp dd Sraw SsubCan
                                          (edge-≈ S ηs)))))
        in gow dd rT' ww' hrec

      bwd : ∀ (qS : Ps)
          → below (mapR asF refl S) w qS
            ≈M below (mapR asF refl T) w (FiberAdj.fro adjout qS)
      bwd qS =
        let xS₁ , es , rS' = FMap.pullF f z (here S) w qS
            qT = FiberAdj.fro adjout qS
            xT₁ , _ , rT' = FMap.pullF f z (here T) w qT
            e0' = FiberAdj.to Dadj es
            et' = FiberAdj.fro padj e0'
            ηd  = FiberAdj.η Dadj es
            ηt  = FiberAdj.η At et'
            Sraw    = below S xS₁ es
            SCan'   = below S xS₁ (FiberAdj.fro Dadj e0')
            Traw    = below T xT₁ (FiberAdj.fro At (FiberAdj.to At et'))
            hrb : Traw ≈M relocate dd Sraw
            hrb =
              ≈M-trans (edge-≈ T ηt)
              (≈M-trans (≈M-sym (pbwd e0'))
              (≈M-trans (≈M-sym (rel-child-nat S dd e0'))
                        (≈rel-resp dd SCan' Sraw
                                   (edge-≈ S ηd))))
        in gow˘ dd rT' ww' hrb

    gow˘ {xS = z} {xT = .z} {v = .(uf z)} refl refl {rS = refl} refl h
      .here-eq = cong (FMap.shape f z) (sym (h .here-eq))
    gow˘ {xS = z} {xT = .z} {v = .(uf z)} refl refl {rS = refl} refl
          {T = T} {S = S} h
      .below-eq w = FiberAdj.symAdj adjout , (fwd˘ , bwd˘)
      where
      h' : T ≈M S
      h' = h
      e   = h' .here-eq
      At  = FMap.adjF f z (here T) w
      As  = FMap.adjF f z (here S) w
      Pt = E Y (uf z) (FMap.shape f z (here T)) w
      Ps = E Y (uf z) (FMap.shape f z (here S)) w
      dd~ = FMap.childF-coh f z e w
      dd  = proj₁ dd~
      ww' = proj₂ dd~
      Dadj = idM-edge-adj {E = E X} {x = z} (here S) dd
      xT' = proj₁ (FMap.childF f z (here T) w)
      xS' = proj₁ (FMap.childF f z (here S) w)
      Rt  = E X z (here T) xT'
      Rs₀ = E X z (here S) xT'
      Rs₁ = E X z (here S) xS'
      bp  = h' .below-eq xT'
      padj = proj₁ bp
      pfwd = proj₁ (proj₂ bp)
      pbwd = proj₂ (proj₂ bp)
      c02 = compAdj Rs₀ Rs₁ Ps (FiberAdj.symAdj Dadj) As
      c03 = compAdj Rt Rs₀ Ps padj c02
      adjout : FiberAdj Ps Pt
      adjout = compAdj Pt Rt Ps (FiberAdj.symAdj At) c03

      fwd˘ : ∀ (qS : Ps)
           → below (mapR asF refl S) w qS
             ≈M below (mapR asF refl T) w (FiberAdj.fro adjout qS)
      fwd˘ qS =
        let xS₁ , es , rS' = FMap.pullF f z (here S) w qS
            qT = FiberAdj.fro adjout qS
            xT₁ , _ , rT' = FMap.pullF f z (here T) w qT
            e0' = FiberAdj.to Dadj es
            et' = FiberAdj.fro padj e0'
            ηd  = FiberAdj.η Dadj es
            ηt  = FiberAdj.η At et'
            Sraw    = below S xS₁ es
            SCan'   = below S xS₁ (FiberAdj.fro Dadj e0')
            Traw    = below T xT₁ (FiberAdj.fro At (FiberAdj.to At et'))
            hrb : Traw ≈M relocate dd Sraw
            hrb =
              ≈M-trans (edge-≈ T ηt)
              (≈M-trans (≈M-sym (pbwd e0'))
              (≈M-trans (≈M-sym (rel-child-nat S dd e0'))
                        (≈rel-resp dd SCan' Sraw
                                   (edge-≈ S ηd))))
        in gow˘ dd rT' ww' hrb

      bwd˘ : ∀ (qT : Pt)
           → below (mapR asF refl T) w qT
             ≈M below (mapR asF refl S) w (FiberAdj.to adjout qT)
      bwd˘ qT =
        let xT₁ , eT , rT' = FMap.pullF f z (here T) w qT
            qS = FiberAdj.to adjout qT
            xS₁ , _ , rS' = FMap.pullF f z (here S) w qS
            e0  = FiberAdj.to padj eT
            e1  = FiberAdj.fro Dadj e0
            ηs  = FiberAdj.η As e1
            Tsub    = below T xT₁ eT
            B0      = below S xT₁ e0
            SsubCan = below S xS₁ e1
            Sraw    = below S xS₁ (FiberAdj.fro As (FiberAdj.to As e1))
            hrec : Tsub ≈M relocate dd Sraw
            hrec =
              ≈M-trans (pfwd eT)
              (≈M-trans (≈rel-refl B0)
              (≈M-trans (≈M-sym (rel-child-nat S dd e0))
                        (≈M-sym (≈rel-resp dd Sraw SsubCan
                                          (edge-≈ S ηs)))))
        in gow dd rT' ww' hrec

    mapF-cong : ∀ {x : I X} {t s : M (A X) (E X) x}
              → t ≈M s → mapf x t ≈M mapf x s
    mapF-cong {x = x} {t = t} {s = s} p =
      gow refl refl refl
          (≈M-trans p (≈rel-refl˘ s))

------------------------------------------------------------------------
-- Composition respects behavioural equivalence
--
-- 复合同余于行为等价

∘-resp-≈ : ∀ {i j k a b c d e fℓ : Level}
             {X : Sys i a b} {Y : Sys j c d} {Z : Sys k e fℓ}
             {G₁ G₂ : FMap Y Z} {F₁ F₂ : FMap X Y}
         → G₁ ≈F G₂ → F₁ ≈F F₂
         → compF G₁ F₁ ≈F compF G₂ F₂
∘-resp-≈ {X = X} {Y = Y} {Z = Z} {G₁ = G₁} {G₂ = G₂}
          {F₁ = F₁} {F₂ = F₂} eqG eqF x
  with eqF x | eqG (FMap.u F₂ x)
... | rF , hF | rG , hG =
    trans (cong (FMap.u G₁) rF) rG
  , λ t →
      let s1 = FMap.mapF F₁ x t
          s2 = FMap.mapF F₂ x t
          a1 = FMap.mapF G₁ (FMap.u F₁ x) s1
          r  = trans (cong (FMap.u G₁) rF) rG
      in
      ≈M-trans
        (≈rel-resp r (FMap.mapF (compF G₁ F₁) x t) a1
                    (mapF-comp G₁ F₁ x t))
        (≈M-trans
          (≈rel-comp (cong (FMap.u G₁) rF) rG a1)
          (≈M-trans
            (≈rel-resp rG
              (relocate (cong (FMap.u G₁) rF) a1)
              (FMap.mapF G₁ (FMap.u F₂ x) (relocate rF s1))
              (≈M-trans (Cong.mapR-rel˘ G₁ (cong (FMap.u G₁) rF) s1)
              (≈M-trans (Cong.mapR-r-eq G₁
                          (sym (trans-reflʳ (cong (FMap.u G₁) rF))) s1)
                        (Cong.mapR-cross˘ G₁ rF refl s1))))
            (≈M-trans
              (≈rel-resp rG
                (FMap.mapF G₁ (FMap.u F₂ x) (relocate rF s1))
                (FMap.mapF G₁ (FMap.u F₂ x) s2)
                (Cong.mapF-cong G₁ (hF t)))
              (≈M-trans
                (hG s2)
                (≈M-sym (mapF-comp G₂ F₂ x t))))))

------------------------------------------------------------------------
-- Category laws
--
-- 范畴律

assoc-f : ∀ {i a b : Level} {W X Y Z : Sys i a b}
            (f : FMap W X) (g : FMap X Y) (h : FMap Y Z)
        → compF (compF h g) f ≈F compF h (compF g f)
assoc-f {i = i} {a = a} {b = b} {W} {X} {Y} {Z} f g h x =
    refl
  , λ t →
      let t1 = FMap.mapF f x t
      in ≈M-trans (mapF-comp (compF h g) f x t)
         (≈M-trans (mapF-comp h g (FMap.u f x) t1)
         (≈M-sym
           (≈M-trans (mapF-comp h (compF g f) x t)
                     (Cong.mapF-cong h (mapF-comp g f x t)))))

sym-assoc-f : ∀ {i a b : Level} {W X Y Z : Sys i a b}
                (f : FMap W X) (g : FMap X Y) (h : FMap Y Z)
            → compF h (compF g f) ≈F compF (compF h g) f
sym-assoc-f f g h = ≈F-sym (assoc-f f g h)

identityˡ-f : ∀ {i a b : Level} {X Y : Sys i a b} (f : FMap X Y)
            → compF (idF Y) f ≈F f
identityˡ-f {X = X} {Y = Y} f x =
    refl
  , λ t → ≈M-trans (mapF-comp (idF Y) f x t)
                   (mapF-id (FMap.u f x) (FMap.mapF f x t))

identityʳ-f : ∀ {i a b : Level} {X Y : Sys i a b} (f : FMap X Y)
            → compF f (idF X) ≈F f
identityʳ-f {X = X} {Y = Y} f x =
    refl
  , λ t → ≈M-trans (mapF-comp f (idF X) x t)
                   (Cong.mapF-cong f (mapF-id x t))

identity²-f : ∀ {i a b : Level} {X : Sys i a b}
            → compF (idF X) (idF X) ≈F idF X
identity²-f {X = X} = identityˡ-f (idF X)

------------------------------------------------------------------------
-- The category MCorrCat
--
-- 范畴 MCorrCat

MCorrCat : (i a b : Level)
         → Category (lsuc (i ⊔ a ⊔ b)) (i ⊔ a ⊔ b) (i ⊔ a ⊔ b)
MCorrCat i a b = record
  { Obj       = Sys i a b
  ; _⇒_       = λ X Y → FMap {i = i} {j = i} {a = a} {b = b}
                             {c = a} {d = b} X Y
  ; _≈_       = λ {X} {Y} f g → _≈F_ {i = i} {j = i} {a = a} {b = b}
                                 {c = a} {d = b}
                                 {X = X} {Y = Y} f g
  ; id        = λ {X} → idF X
  ; _∘_       = λ {X} {Y} {Z} g f → compF g f
  ; equiv     = λ {X} {Y} → ≈F-isEquivalence {i = i} {j = i} {a = a}
                                            {b = b} {c = a} {d = b}
                                            {X = X} {Y = Y}
  ; ∘-resp-≈  = λ {X} {Y} {Z} {f} {h} {g} {k} eqG eqF →
                  ∘-resp-≈ {c = a} {d = b} {e = a} {fℓ = b}
                           {X = X} {Y = Y} {Z = Z}
                           {G₁ = f} {G₂ = h} {F₁ = g} {F₂ = k}
                           eqG eqF
  ; assoc     = λ {W} {X} {Y} {Z} {f} {g} {h} →
                  assoc-f {i = i} {a = a} {b = b}
                          {W = W} {X = X} {Y = Y} {Z = Z} f g h
  ; sym-assoc = λ {W} {X} {Y} {Z} {f} {g} {h} →
                  sym-assoc-f {i = i} {a = a} {b = b}
                              {W = W} {X = X} {Y = Y} {Z = Z} f g h
  ; identityˡ = λ {X} {Y} {f} →
                  identityˡ-f {i = i} {a = a} {b = b} {X = X} {Y = Y} f
  ; identityʳ = λ {X} {Y} {f} →
                  identityʳ-f {i = i} {a = a} {b = b} {X = X} {Y = Y} f
  ; identity² = λ {X} →
                  identity²-f {i = i} {a = a} {b = b} {X = X}
  }
