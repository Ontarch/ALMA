------------------------------------------------------------------------
-- Transformation invariance of ScaleInvariant under a group action
--
-- GroupInvariant is ScaleInvariant at Obs = G, step = act; the group
-- axioms yield two-sided invariance and the corresponding inverse and
-- round-trip lemmas.
--
-- 群作用下 ScaleInvariant 的变换不变性
--
-- GroupInvariant 是 Obs = G、step = act 处的 ScaleInvariant；群公理
-- 给出双向不变性及相应的逆与往返引理。
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module Equivalence.GroupInvariant where

open import Agda.Builtin.Equality using (_≡_)
open import Data.Unit.Polymorphic.Base using (tt)
open import Data.Product.Base using (_×_; _,_)
open import Relation.Binary.PropositionalEquality.Core using (subst₂; cong; trans)
open import Relation.Binary.PropositionalEquality.Properties using (module ≡-Reasoning)
open ≡-Reasoning

open import Base.IndexedMType using (fst; snd)
open import Equivalence.ScaleInvariant using (ScaleInvariant)

------------------------------------------------------------------------
-- A minimal group record carrying the five axioms used below
--
-- 最小群记录，携带下面使用的五条公理

record GroupStructure {g} (G : Set g) : Set g where
  infixl 6 _·_
  field
    _·_   : G → G → G
    e     : G
    _⁻¹   : G → G
    assoc : ∀ a b c → (a · b) · c ≡ a · (b · c)
    idˡ   : ∀ a → e · a ≡ a
    idʳ   : ∀ a → a · e ≡ a
    invˡ  : ∀ a → (a ⁻¹) · a ≡ e
    invʳ  : ∀ a → a · (a ⁻¹) ≡ e

module GroupAction
    {a g} {X : Set a} {G : Set g}
    (𝔾 : GroupStructure G)
    (act : X → G → X)
    (act-id   : ∀ x → act x (GroupStructure.e 𝔾) ≡ x)
    (act-comp : ∀ x (g h : G) →
                  act (act x g) h ≡ act x (GroupStructure._·_ 𝔾 g h))
  where

  open GroupStructure 𝔾

  -- Universe is Set g: ScaleInvariant's universe does not depend on
  -- the universe of the state type X.
  --
  -- universe 是 Set g：ScaleInvariant 的 universe 不依赖状态类型 X
  -- 的 universe。
  GroupInvariant : X → X → Set g
  GroupInvariant = ScaleInvariant act

  ----------------------------------------------------------------------
  -- Group lemmas: two dual pairs (invʳ / idˡ and invˡ / idʳ)
  --
  -- 群论引理：两对对偶（invʳ / idˡ 与 invˡ / idʳ）

  g·g⁻¹·h≡h : ∀ (g h : G) → g · ((g ⁻¹) · h) ≡ h
  g·g⁻¹·h≡h g h = begin
    g · ((g ⁻¹) · h)
      ≡˘⟨ assoc g (g ⁻¹) h ⟩
    (g · (g ⁻¹)) · h
      ≡⟨ cong (_· h) (invʳ g) ⟩
    e · h
      ≡⟨ idˡ h ⟩
    h
    ∎

  g⁻¹·g·h≡h : ∀ (g h : G) → (g ⁻¹) · (g · h) ≡ h
  g⁻¹·g·h≡h g h = begin
    (g ⁻¹) · (g · h)
      ≡˘⟨ assoc (g ⁻¹) g h ⟩
    ((g ⁻¹) · g) · h
      ≡⟨ cong (_· h) (invˡ g) ⟩
    e · h
      ≡⟨ idˡ h ⟩
    h
    ∎

  g·h·h⁻¹≡g : ∀ (g h : G) → (g · h) · (h ⁻¹) ≡ g
  g·h·h⁻¹≡g g h = begin
    (g · h) · (h ⁻¹)
      ≡⟨ assoc g h (h ⁻¹) ⟩
    g · (h · (h ⁻¹))
      ≡⟨ cong (g ·_) (invʳ h) ⟩
    g · e
      ≡⟨ idʳ g ⟩
    g
    ∎

  g·h⁻¹·h≡g : ∀ (g h : G) → (g · (h ⁻¹)) · h ≡ g
  g·h⁻¹·h≡g g h = begin
    (g · (h ⁻¹)) · h
      ≡⟨ assoc g (h ⁻¹) h ⟩
    g · ((h ⁻¹) · h)
      ≡⟨ cong (g ·_) (invˡ h) ⟩
    g · e
      ≡⟨ idʳ g ⟩
    g
    ∎

  ----------------------------------------------------------------------
  -- Inverse-action lemmas: dual pair consuming invʳ / invˡ
  --
  -- 逆作用引理：消费 invʳ / invˡ 的对偶对

  act-inverseʳ : ∀ x (g : G) → act (act x g) (g ⁻¹) ≡ x
  act-inverseʳ x g = begin
    act (act x g) (g ⁻¹)
      ≡⟨ act-comp x g (g ⁻¹) ⟩
    act x (g · (g ⁻¹))
      ≡⟨ cong (act x) (invʳ g) ⟩
    act x e
      ≡⟨ act-id x ⟩
    x
    ∎

  act-inverseˡ : ∀ x (g : G) → act (act x (g ⁻¹)) g ≡ x
  act-inverseˡ x g = begin
    act (act x (g ⁻¹)) g
      ≡⟨ act-comp x (g ⁻¹) g ⟩
    act x ((g ⁻¹) · g)
      ≡⟨ cong (act x) (invˡ g) ⟩
    act x e
      ≡⟨ act-id x ⟩
    x
    ∎

  ----------------------------------------------------------------------
  -- Invariance, forward and dual
  --
  -- 不变性，正向与对偶

  GI-invariant : ∀ {x y} (g : G)
               → GroupInvariant x y → GroupInvariant (act x g) (act y g)
  GI-invariant {x} {y} g p .fst = tt
  GI-invariant {x} {y} g p .snd h
    rewrite act-comp x g h | act-comp y g h =
    p .snd (g · h)

  GI-invariantˡ : ∀ {x y} (g : G)
                → GroupInvariant x y
                → GroupInvariant (act x (g ⁻¹)) (act y (g ⁻¹))
  GI-invariantˡ g = GI-invariant (g ⁻¹)

  ----------------------------------------------------------------------
  -- Inverses, forward and dual; each transports the recursive call
  -- along the corresponding group lemma via subst₂.
  --
  -- 逆，正向与对偶；各自沿对应的群论引理经 subst₂ 传输递归调用。

  GI-inverse : ∀ {x y} (g : G)
             → GroupInvariant (act x g) (act y g) → GroupInvariant x y
  GI-inverse {x} {y} g p .fst = tt
  GI-inverse {x} {y} g p .snd h =
    subst₂ GroupInvariant left-eq right-eq (p .snd k)
    where
      k : G
      k = (g ⁻¹) · h

      left-eq : act (act x g) k ≡ act x h
      left-eq = trans (act-comp x g k) (cong (act x) (g·g⁻¹·h≡h g h))

      right-eq : act (act y g) k ≡ act y h
      right-eq = trans (act-comp y g k) (cong (act y) (g·g⁻¹·h≡h g h))

  GI-inverseˡ : ∀ {x y} (g : G)
              → GroupInvariant (act x (g ⁻¹)) (act y (g ⁻¹))
              → GroupInvariant x y
  GI-inverseˡ g = GI-inverse (g ⁻¹)

  ----------------------------------------------------------------------
  -- Round trips: compose the two invariance directions, then rewrite
  -- the endpoints back via the corresponding inverse-action lemma.
  --
  -- 往返：复合两个不变性方向，再经对应的逆作用引理把端点重写回原处。

  GI-roundtrip : ∀ {x y} (g : G)
               → GroupInvariant x y → GroupInvariant x y
  GI-roundtrip {x} {y} g p =
    subst₂ GroupInvariant
      (act-inverseʳ x g)
      (act-inverseʳ y g)
      (GI-invariantˡ g (GI-invariant g p))

  GI-roundtripˡ : ∀ {x y} (g : G)
                → GroupInvariant x y → GroupInvariant x y
  GI-roundtripˡ {x} {y} g p =
    subst₂ GroupInvariant
      (act-inverseˡ x g)
      (act-inverseˡ y g)
      (GI-invariant g (GI-invariantˡ g p))

  ----------------------------------------------------------------------
  -- Bundled two-sided invariance
  --
  -- 打包的双向不变性

  GI-iff : ∀ {x y} (g : G)
         → ( GroupInvariant x y
             → GroupInvariant (act x g) (act y g) )
         × ( GroupInvariant (act x g) (act y g)
             → GroupInvariant x y )
         × ( GroupInvariant x y
             → GroupInvariant (act x (g ⁻¹)) (act y (g ⁻¹)) )
         × ( GroupInvariant (act x (g ⁻¹)) (act y (g ⁻¹))
             → GroupInvariant x y )
         × ( GroupInvariant x y → GroupInvariant x y )
         × ( GroupInvariant x y → GroupInvariant x y )
  GI-iff g = GI-invariant g , GI-inverse g
           , GI-invariantˡ g , GI-inverseˡ g
           , GI-roundtrip g , GI-roundtripˡ g

open GroupAction public
