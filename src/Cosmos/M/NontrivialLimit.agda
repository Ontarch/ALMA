------------------------------------------------------------------------
-- Non-triviality on the carried M base
--
-- Terminality gives only uniqueness of the mediating morphism
-- (!-unique); it does not make a fibre total. Totality is the explicit
-- predicate AllBisim j, with Subterminal = every fibre total. A carried
-- correspondence (CosmosM⇒ over an index relation R, mapping across
-- fibres via mapR along r : R i j) that reflects bisimulation cannot
-- send a separated source fibre into a total one. The FinCat n tower
-- supplies both the separated source (idN≉const0N) and the fact that
-- the terminal carrier is not subterminal.
--
-- 携带式 M 底座上的非平凡性
--
-- 终性只给中介映射唯一性（!-unique），不使纤维全体；全体性是显式谓词
-- AllBisim j，Subterminal 即每个纤维全体。反射互模拟的携带对应（索引
-- 关系 R 上的 CosmosM⇒，经 mapR 沿 r : R i j 跨纤维映射）不能把分离
-- 源纤维送入全体纤维。FinCat n 塔同时给出分离源（idN≉const0N）与终
-- 载体非亚终。
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module Cosmos.M.NontrivialLimit where

open import Agda.Primitive using (Level; _⊔_)
open import Agda.Builtin.Sigma using (Σ; _,_)
open import Data.Empty using (⊥)
open import Data.Nat using (ℕ)
open import Relation.Nullary using (¬_)

open import Categories.Category.Core using (Category)
open import Categories.Functor.Core using (Functor)

open import Cosmos.ContCategory using (ContCat)
open import Base.MCorr.Setoid using (EqOn; Morphˢ; propEqOn)
open Morphˢ using (mapR)
open import Cosmos.M.Object using
  (I; A; ana; CosmosM; unfold-coalgebra; Coalgebra; ana-unfold˘; CosmosM⇒; ≈CosmosM)
open import Cosmos.M.Terminal using (≈CosmosM-sym; ≈CosmosM-trans)
open import Cosmos.M.TowerSeparation using (module TowerSeparation)

module _ {o h e s p : Level}
         {C  : Category o h e}
         {FC : Functor C (ContCat s p)}
         {ℓd : Level}
         (≈CD : (i : I C FC) → EqOn {ℓ = ℓd} (A C FC i))
       where

  private
    L = o ⊔ h ⊔ e ⊔ s ⊔ p

  ----------------------------------------------------------------------
  -- Per-fibre totality and subterminal objects
  --
  -- Explicit, never derived from terminality.
  --
  -- 纤维全体性与亚终对象
  --
  -- 显式假设，不由终性导出。

  AllBisim : (j : I C FC) → Set (L ⊔ ℓd)
  AllBisim j =
    ∀ (t u : CosmosM C FC j) → ≈CosmosM C FC ≈CD t u

  Subterminal : Set (L ⊔ ℓd)
  Subterminal = ∀ (j : I C FC) → AllBisim j

  no-distinguishing-pair : ∀ {j : I C FC}
    → AllBisim j
    → ¬ Σ (CosmosM C FC j) λ t →
        Σ (CosmosM C FC j) λ u →
          ¬ ≈CosmosM C FC ≈CD t u
  no-distinguishing-pair all (t , u , t≉u) = t≉u (all t u)

  ----------------------------------------------------------------------
  -- Reflecting carried maps
  --
  -- A carried map reflects bisimulation along r : R i j when bisimilar
  -- images at j force bisimilar sources at i.
  --
  -- 反射携带映射
  --
  -- 携带映射沿 r : R i j 反射互模拟：j 处像互模拟则 i 处源互模拟。

  module _ {ℓr : Level}
           (R : I C FC → I C FC → Set ℓr)
           (φ : CosmosM⇒ C FC ≈CD R)
         where

    ReflectsBisimAt : ∀ {i j : I C FC} → R i j → Set (L ⊔ ℓd)
    ReflectsBisimAt {i = i} r =
      ∀ (t u : CosmosM C FC i)
      → ≈CosmosM C FC ≈CD (mapR φ r t) (mapR φ r u)
      → ≈CosmosM C FC ≈CD t u

    -- Contrapositive: separation at the source survives the map.
    --
    -- 逆否：源处的分离在映射后保持。
    separation-survives : ∀ {i j : I C FC}
      → (r : R i j) → ReflectsBisimAt r
      → (t u : CosmosM C FC i)
      → ¬ ≈CosmosM C FC ≈CD t u
      → ¬ ≈CosmosM C FC ≈CD (mapR φ r t) (mapR φ r u)
    separation-survives r reflect t u t≉u eq =
      t≉u (reflect t u eq)

    no-reflecting-into-total : ∀ {i j : I C FC}
      → (r : R i j) → AllBisim j → ReflectsBisimAt r
      → (t u : CosmosM C FC i)
      → ¬ ≈CosmosM C FC ≈CD t u → ⊥
    no-reflecting-into-total r all reflect t u t≉u =
      t≉u (reflect t u (all (mapR φ r t) (mapR φ r u)))

    no-reflecting-into-subterminal : ∀ {i j : I C FC}
      → (r : R i j) → Subterminal → ReflectsBisimAt r
      → (t u : CosmosM C FC i)
      → ¬ ≈CosmosM C FC ≈CD t u → ⊥
    no-reflecting-into-subterminal r sub reflect t u t≉u =
      no-reflecting-into-total r (sub _) reflect t u t≉u

  ----------------------------------------------------------------------
  -- Terminality is mediator uniqueness, not fibre totality
  --
  -- 终性是中介映射唯一性，非纤维全体性

  record TerminalMediator {u : Level}
         (Xst : I C FC → Set u)
         (γ   : Coalgebra C FC u Xst)
       : Set (L ⊔ ℓd ⊔ u) where
    field
      med      : ∀ (j : I C FC) (x : Xst j) → CosmosM C FC j
      med-comm : ∀ (j : I C FC) (x : Xst j)
        → ≈CosmosM C FC ≈CD
            (ana C FC (unfold-coalgebra C FC) j (med j x))
            (ana C FC γ j x)
  open TerminalMediator public

  terminal-unique : ∀ {u : Level}
      {Xst : I C FC → Set u}
      {γ   : Coalgebra C FC u Xst}
      (m   : TerminalMediator Xst γ)
      (j   : I C FC) (x : Xst j)
    → ≈CosmosM C FC ≈CD (med m j x) (ana C FC γ j x)
  terminal-unique {γ = γ} m j x =
    ≈CosmosM-trans ≈CD
      (ana-unfold˘ C FC ≈CD (med m j x))
      (med-comm m j x)

  -- Mediators of one coalgebra coincide pointwise.
  --
  -- 同一余代数的中介逐点重合。
  terminal-mediators-coincide : ∀ {u : Level}
      {Xst : I C FC → Set u}
      {γ   : Coalgebra C FC u Xst}
      (m n : TerminalMediator Xst γ)
      (j   : I C FC) (x : Xst j)
    → ≈CosmosM C FC ≈CD (med m j x) (med n j x)
  terminal-mediators-coincide {γ = γ} m n j x =
    ≈CosmosM-trans ≈CD
      (terminal-unique m j x)
      (≈CosmosM-sym ≈CD (terminal-unique n j x))

------------------------------------------------------------------------
-- FinCat n tower instantiation
--
-- FinCat n 塔实例化

module TowerInstance (m : ℕ) where

  open TowerSeparation m
    using (Cn; TrivFC; i₁; treeId; treeC0; idN≉const0N)

  private
    ≈CDn : (i : I Cn TrivFC) → EqOn (A Cn TrivFC i)
    ≈CDn _ = propEqOn _

  -- The terminal carrier fibre at i₁ is not total.
  --
  -- i₁ 处的终载体纤维并非全体。
  terminal-fibre-not-total
    : ¬ AllBisim {C = Cn} {FC = TrivFC} ≈CDn i₁
  terminal-fibre-not-total all =
    idN≉const0N (all (treeId i₁) (treeC0 i₁))

  -- No reflecting carried map leads from i₁ into a total fibre.
  --
  -- 不存在从 i₁ 指向全体纤维的反射携带映射。
  tower-no-reflection-into-total
    : ∀ {ℓr : Level}
        (R : I Cn TrivFC → I Cn TrivFC → Set ℓr)
        (φ : CosmosM⇒ Cn TrivFC ≈CDn R)
        (j : I Cn TrivFC) (r : R i₁ j)
    → AllBisim {C = Cn} {FC = TrivFC} ≈CDn j
    → ¬ ReflectsBisimAt {C = Cn} {FC = TrivFC} ≈CDn R φ r
  tower-no-reflection-into-total R φ j r all reflect =
    no-reflecting-into-total {C = Cn} {FC = TrivFC} ≈CDn R φ r
      all reflect (treeId i₁) (treeC0 i₁) idN≉const0N
