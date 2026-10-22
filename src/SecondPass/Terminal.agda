------------------------------------------------------------------------
-- Terminal coalgebra of the Unfolding endofunctor, up to bisimulation
-- (Setoid carrier + ≡ commute)
-- Defines general F-coalgebras with Setoid carriers and Func structure maps,
-- the anamorphism (unfold) into Cosmos, a bisimulation relation _≈C_ on Cosmos,
-- and establishes the universal property: Cosmos is the terminal coalgebra of
-- the unfolding endofunctor constructed from the container functor,
-- up to bisimulation
--
-- 展开自函子在互模拟意义下的终余代数（Setoid 载体 + ≡ 交换条件）
-- 定义具有 Setoid 载体与 Func 结构映射的一般 F-余代数、到 Cosmos 的 anamorphism（展开）、
-- Cosmos 上的互模拟关系 _≈C_，并证明泛性质：Cosmos 是由容器函子构造的展开自函子
-- 在互模拟意义下的终余代数
------------------------------------------------------------------------
{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module SecondPass.Terminal where

open import Agda.Primitive using (Level; lsuc; _⊔_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Product.Base using (∃; _,_; _×_; Σ; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality.Core using (cong; sym; trans; subst)
open import Relation.Binary.PropositionalEquality.Properties using (module ≡-Reasoning)
open ≡-Reasoning
open import Relation.Binary.Bundles using (Setoid)
open import Function.Bundles using (Func)

open import Categories.Category.Core using (Category)
open import Categories.Functor.Core using (Functor)

open import Equivalence.SubstTransport using (module SubstTransport-Left)
open import Cosmos.ContCategory using (ContCat)
open import Cosmos.ContCategoryLemmas using (ShapeOf; PosOf)
open import SecondPass.Unfolding using (Unfolding; mapUnfolding; module UnfoldingSetoid)
open import SecondPass.Cosmos using (Cosmos; out)

-- Parameterised module: fixes a base category C and a container-valued
-- functor FC : C → ContCat; all constructions below are relative to these
--
-- 参数化模块：固定基范畴 C 与容器值函子 FC : C → ContCat；
-- 以下所有构造均相对于这些参数
module _ {o h e s p : Level}
         {C : Category o h e}
         {FC : Functor C (ContCat s p)} where
  private
    -- Overall level of objects in this module
    --
    -- 本模块中对象的总层级
    L = o ⊔ h ⊔ e ⊔ s ⊔ p

    -- Instantiate the unfolding setoid module
    --
    -- 实例化展开集合模块
    module US = UnfoldingSetoid
      {o = o} {h = h} {e = e} {s = s} {p = p} {C = C} {F = FC}

  -- Coalgebra: Setoid carrier, Func structure map, ≡ commute
  --
  -- 余代数：Setoid 载体，Func 结构映射，≡ 交换条件
  record Coalgebra (r : Level) : Set (lsuc (L ⊔ r)) where
    field
      -- Carrier setoid of the coalgebra
      --
      -- 余代数的载体 Setoid
      Carrier : Setoid L r

      -- Structure map α : Carrier → Unfolding Carrier, preserving setoid equivalence
      --
      -- 结构映射 α : Carrier → Unfolding Carrier，保持 setoid 等价
      α       : Func Carrier (US.unfoldingSetoid Carrier)

  -- A homomorphism between coalgebras: a map commuting with the structure maps
  --
  -- 余代数之间的同态：与结构映射交换的映射
  record CoalgHom {r₁ r₂ : Level} (X : Coalgebra r₁) (Y : Coalgebra r₂)
      : Set (L ⊔ r₁ ⊔ r₂) where
    private module X = Coalgebra X; module Y = Coalgebra Y
    field
      -- Underlying setoid morphism between carriers
      --
      -- 载体之间的底层 setoid 态射
      f       : Func X.Carrier Y.Carrier

      -- Commutation with the structure maps
      --
      -- 与结构映射的交换性
      commute : ∀ x → mapUnfolding (Func.to f) (Func.to X.α x)
                     ≡ Func.to Y.α (Func.to f x)

  -- Bisimulation _≈C_ on Cosmos and cosmosSetoid
  --
  -- Cosmos 上的互模拟 _≈C_ 及 cosmosSetoid
  record _≈C_ (F G : Cosmos C FC) : Set (o ⊔ s ⊔ p) where
    coinductive
    module UF = Unfolding (out F)
    module UG = Unfolding (out G)
    field
      -- Unfolding functors are pointwise equal on objects
      --
      -- 展开函子在对象上逐点命题相等
      unfoldFunctor₀-eq : ∀ {A} (s : ShapeOf FC A)
                        → Functor.₀ UF.unfoldFunctor (A , s) ≡ Functor.₀ UG.unfoldFunctor (A , s)

      -- Position-to-shape maps agree after transport along the above equality
      --
      -- 位置到形状映射沿上述等式传输后一致
      pos-to-shape-eq  : ∀ {A} (s : ShapeOf FC A) (p : PosOf FC s)
                       → subst (λ x → ShapeOf FC x) (unfoldFunctor₀-eq s)
                                (UF.pos-to-shape s p)
                       ≡ UG.pos-to-shape s p

      -- Next seeds are coinductively equivalent (recursive _≈C_)
      --
      -- 下一层种子余归纳地等价（递归调用 _≈C_）
      unfold-next-eq   : ∀ {A} (s : ShapeOf FC A)
                       → UF.unfold-next s ≈C UG.unfold-next s

  open _≈C_

  -- Instance of SubstTransport-Left for _≈C_, used only for the shape and
  -- position components
  --
  -- 针对 _≈C_ 的 SubstTransport-Left 实例，仅用于 shape 与 position 分量
  private
    module ST = SubstTransport-Left
      {S = Σ (Category.Obj C) (ShapeOf FC)}
      {T = Category.Obj C}
      (ShapeOf FC)
      (λ { (A , s) → PosOf FC s })
      {F = Cosmos C FC}
      (λ F → Functor.₀ (Unfolding.unfoldFunctor (out F)))
      (λ F {s} → Unfolding.pos-to-shape (out F) {proj₁ s} (proj₂ s))

    to≈sl : ∀ {F G} → F ≈C G → ST._≈sl_ F G
    to≈sl eq = record
      { shape-eq    = λ { (A , s) → eq .unfoldFunctor₀-eq {A = A} s }
      ; position-eq = λ { (A , s) p → eq .pos-to-shape-eq {A = A} s p }
      }

  -- Reflexivity of the bisimulation relation
  --
  -- 互模拟关系的自反性
  ≈C-refl : ∀ {F} → F ≈C F
  ≈C-refl .unfoldFunctor₀-eq = λ _ → refl
  ≈C-refl .pos-to-shape-eq _ _ = refl
  ≈C-refl .unfold-next-eq _ = ≈C-refl

  -- Symmetry of the bisimulation relation
  --
  -- 互模拟关系的对称性
  ≈C-sym : ∀ {F G} → F ≈C G → G ≈C F
  ≈C-sym {F} {G} eq .unfoldFunctor₀-eq = λ s → sym (eq .unfoldFunctor₀-eq s)
  ≈C-sym {F} {G} eq .pos-to-shape-eq {A} s p =
    ST._≈sl_.position-eq (ST.≈sl-sym (to≈sl eq)) (A , s) p
  ≈C-sym eq .unfold-next-eq s = ≈C-sym (eq .unfold-next-eq s)

  -- Transitivity of the bisimulation relation
  --
  -- 互模拟关系的传递性
  ≈C-trans : ∀ {F G H} → F ≈C G → G ≈C H → F ≈C H
  ≈C-trans {F} {G} {H} e1 e2 .unfoldFunctor₀-eq =
    λ s → trans (e1 .unfoldFunctor₀-eq s) (e2 .unfoldFunctor₀-eq s)
  ≈C-trans {F} {G} {H} e1 e2 .pos-to-shape-eq {A} s p =
    ST._≈sl_.position-eq (ST.≈sl-trans (to≈sl e1) (to≈sl e2)) (A , s) p
  ≈C-trans e1 e2 .unfold-next-eq s =
    ≈C-trans (e1 .unfold-next-eq s) (e2 .unfold-next-eq s)

  -- The setoid of Cosmos objects under bisimulation equivalence
  --
  -- 互模拟等价下的 Cosmos 对象构成的 Setoid
  cosmosSetoid : Setoid L (o ⊔ s ⊔ p)
  cosmosSetoid = record
    { Carrier       = Cosmos C FC
    ; _≈_           = _≈C_
    ; isEquivalence = record
      { refl  = ≈C-refl ; sym = ≈C-sym ; trans = ≈C-trans }
    }

  -- Canonical coalgebra structure on Cosmos
  -- α.cong maps ≈C to ≈F via ≈C→≈U
  --
  -- Cosmos 上的典范余代数结构
  -- α.cong 通过 ≈C→≈U 将 ≈C 映射为 ≈F
  cosmosCoalg : Coalgebra (o ⊔ s ⊔ p)
  cosmosCoalg = record
    { Carrier = cosmosSetoid
    ; α       = record
        { to   = out
        ; cong = λ {F} {G} eq → ≈C→≈U eq
        }
    }
    where
      ≈C→≈U : ∀ {F G} → F ≈C G
             → US._≈U_ {X = cosmosSetoid} (out F) (out G)
      ≈C→≈U eq = record
        { sl-eq = record
            { shape-eq    = λ { (A , s) → eq .unfoldFunctor₀-eq {A = A} s }
            ; position-eq = λ { (A , s) p → eq .pos-to-shape-eq {A = A} s p }
            }
        ; unfold-next-eq = eq .unfold-next-eq
        }

  -- Existence: anamorphism
  --
  -- 存在性：anamorphism
  ana-to : {r : Level} (X : Coalgebra r)
         → Setoid.Carrier (Coalgebra.Carrier X) → Cosmos C FC
  ana-to X x .out = record
    { unfoldFunctor   = u₀.unfoldFunctor
    ; unfold-next     = λ s → ana-to X (u₀.unfold-next s)
    ; pos-to-shape    = u₀.pos-to-shape
    ; pos-actS-compat = u₀.pos-actS-compat
    }
    where
      u₀ = Func.to (Coalgebra.α X) x
      module u₀ = Unfolding u₀

  -- Congruence of ana-to with respect to carrier equivalence
  --
  -- ana-to 关于载体等价的兼容性
  ana-cong : {r : Level} (X : Coalgebra r)
          → ∀ {x y} → Setoid._≈_ (Coalgebra.Carrier X) x y
          → ana-to X x ≈C ana-to X y
  ana-cong X {x} {y} x≈y .unfoldFunctor₀-eq {A} s =
    SubstTransport-Left._≈sl_.shape-eq
      (US._≈U_.sl-eq (Func.cong (Coalgebra.α X) x≈y)) (A , s)
  ana-cong X {x} {y} x≈y .pos-to-shape-eq {A} s p =
    SubstTransport-Left._≈sl_.position-eq
      (US._≈U_.sl-eq (Func.cong (Coalgebra.α X) x≈y)) (A , s) p
  ana-cong X {x} {y} x≈y .unfold-next-eq {A} s =
    ana-cong X (US._≈U_.unfold-next-eq
      (Func.cong (Coalgebra.α X) x≈y) s)

  -- The anamorphism as a Setoid morphism
  --
  -- anamorphism 作为 Setoid 态射
  ana : {r : Level} (X : Coalgebra r)
      → Func (Coalgebra.Carrier X) cosmosSetoid
  ana X = record { to = ana-to X ; cong = ana-cong X }

  -- The anamorphism is a coalgebra homomorphism from X to Cosmos
  --
  -- anamorphism 是从 X 到 Cosmos 的余代数同态
  ana-hom : {r : Level} (X : Coalgebra r)
          → CoalgHom {r₁ = r} {r₂ = o ⊔ s ⊔ p} X cosmosCoalg
  ana-hom X = record { f = ana X ; commute = λ _ → refl }

  -- Uniqueness
  --
  -- 唯一性
  unique-ana : {r : Level} (X : Coalgebra r) (fhom : CoalgHom X cosmosCoalg)
            → ∀ x → Func.to (CoalgHom.f fhom) x ≈C ana-to X x
  unique-ana X fhom = λ x → helper x refl refl
    where
      module X  = Coalgebra X
      module fh = CoalgHom fhom
      open _≈C_
      open Unfolding using (unfoldFunctor; unfold-next; pos-to-shape)

      -- Core helper: given x and equalities a ≡ fhom f x and b ≡ ana X x,
      -- prove a ≈C b by coinduction
      --
      -- 核心辅助：给定 x 及等式 a ≡ fhom f x 与 b ≡ ana X x，
      -- 通过余归纳证明 a ≈C b
      helper : ∀ {a b : Cosmos C FC} (x : Setoid.Carrier X.Carrier)
             → (a≡fx : a ≡ Func.to fh.f x)
             → (b≡anax : b ≡ ana-to X x)
             → a ≈C b
      helper {a} {b} x a≡fx b≡anax = go
        where
          u₀ = Func.to X.α x

          eq-UF : out a ≡ mapUnfolding (Func.to fh.f) u₀
          eq-UF = begin
            out a
              ≡⟨ cong out a≡fx ⟩
            out (Func.to fh.f x)
              ≡⟨ sym (fh.commute x) ⟩
            mapUnfolding (Func.to fh.f) u₀
            ∎

          eq-UG : out b ≡ mapUnfolding (ana-to X) u₀
          eq-UG = begin
            out b
              ≡⟨ cong out b≡anax ⟩
            out (ana-to X x)
              ≡⟨ refl ⟩
            mapUnfolding (ana-to X) u₀
            ∎

          unfoldFunctor₀-eq-lem : ∀ {A} (s : ShapeOf FC A)
                                → Functor.₀ (unfoldFunctor (out a)) (A , s)
                                  ≡ Functor.₀ (unfoldFunctor (out b)) (A , s)
          unfoldFunctor₀-eq-lem {A} s =
            trans
              (cong (λ u → Functor.₀ (unfoldFunctor u) (A , s)) eq-UF)
              (sym (cong (λ u → Functor.₀ (unfoldFunctor u) (A , s)) eq-UG))

          pos-to-shape-eq-lem : ∀ {A} (s : ShapeOf FC A) (p : PosOf FC s)
                              → subst (λ x → ShapeOf FC x) (unfoldFunctor₀-eq-lem s)
                                       (pos-to-shape (out a) s p)
                                ≡ pos-to-shape (out b) s p
          pos-to-shape-eq-lem {A} s p
            rewrite eq-UF | eq-UG = refl

          go : a ≈C b
          go .unfoldFunctor₀-eq = unfoldFunctor₀-eq-lem
          go .pos-to-shape-eq   = pos-to-shape-eq-lem
          go .unfold-next-eq {A} s =
            let seed = unfold-next u₀ s
                a'≡ = cong (λ u → unfold-next u s) eq-UF
                b'≡ = cong (λ u → unfold-next u s) eq-UG
            in helper seed a'≡ b'≡

  -- Terminality up to _≈C_ (Func morphism, ≡ commute condition)
  --
  -- 在 _≈C_ 意义下的终余代数性（Func 态射，≡ 交换条件）
  terminality : {r : Level} (X : Coalgebra r)
              → ∃ λ (f : Func (Coalgebra.Carrier X) cosmosSetoid) →
                  (∀ x → mapUnfolding (Func.to f) (Func.to (Coalgebra.α X) x)
                         ≡ out (Func.to f x))
                × (∀ (g : Func (Coalgebra.Carrier X) cosmosSetoid)
                    → (∀ x → mapUnfolding (Func.to g) (Func.to (Coalgebra.α X) x)
                           ≡ out (Func.to g x))
                    → ∀ x → Func.to f x ≈C Func.to g x)
  terminality X =
    ( ana X
    , (λ _ → refl)
    , λ g gcomm x → ≈C-sym
        (unique-ana X (record { f = g ; commute = gcomm }) x)
    )

  -- Freedom of F₁: two unfoldings that are equivalent under _≈U_ (which
  -- ignores Functor.₁) give bisimilar Cosmos elements
  -- Convert any Unfolding into a Cosmos (copattern matching on out)
  --
  -- F₁ 自由度：两个在 _≈U_ 下等价的展开（忽略 Functor.₁）给出互模拟的 Cosmos 元素
  -- 将任意 Unfolding 通过 out 的 copattern 匹配转换为 Cosmos
  cosmos-from-unfolding : Unfolding FC (Cosmos C FC) → Cosmos C FC
  cosmos-from-unfolding u .out = u

  -- The main freedom lemma: _≈U_ implies _≈C_
  --
  -- 主要自由度引理：_≈U_ 蕴含 _≈C_
  ≈U→≈C : (u₁ u₂ : Unfolding FC (Cosmos C FC))
        → US._≈U_ {X = cosmosSetoid} u₁ u₂
        → cosmos-from-unfolding u₁ ≈C cosmos-from-unfolding u₂
  ≈U→≈C u₁ u₂ eqU = record
    { unfoldFunctor₀-eq = λ {A} s →
        SubstTransport-Left._≈sl_.shape-eq
          (US._≈U_.sl-eq eqU) (A , s)
    ; pos-to-shape-eq = λ {A} s p →
        SubstTransport-Left._≈sl_.position-eq
          (US._≈U_.sl-eq eqU) (A , s) p
    ; unfold-next-eq = US._≈U_.unfold-next-eq eqU
    }

  -- Corollary: if the unfoldings agree on object maps, pos-to-shape, and
  -- have propositionally equal next seeds, then the resulting Cosmos elements
  -- are bisimilar
  --
  -- 推论：若两个展开在对象映射、pos-to-shape 上一致，且下一层种子命题相等，
  -- 则构造出的 Cosmos 元素互模拟
  ≈C-from-unfolding-eq :
      (u₁ u₂ : Unfolding FC (Cosmos C FC))
    → (eq₀ : ∀ {A} (s : ShapeOf FC A)
           → Functor.₀ (Unfolding.unfoldFunctor u₁) (A , s)
           ≡ Functor.₀ (Unfolding.unfoldFunctor u₂) (A , s))
    → (eqP : ∀ {A} (s : ShapeOf FC A) (p : PosOf FC s)
           → subst (λ x → ShapeOf FC x) (eq₀ s)
                    (Unfolding.pos-to-shape u₁ s p)
             ≡ Unfolding.pos-to-shape u₂ s p)
    → (eqN : ∀ {A} (s : ShapeOf FC A)
           → Unfolding.unfold-next u₁ s ≡ Unfolding.unfold-next u₂ s)
    → cosmos-from-unfolding u₁ ≈C cosmos-from-unfolding u₂
  ≈C-from-unfolding-eq u₁ u₂ eq₀ eqP eqN =
    ≈U→≈C u₁ u₂ (record
      { sl-eq = record
          { shape-eq    = λ { (A , s) → eq₀ s }
          ; position-eq = λ { (A , s) p → eqP s p }
          }
      ; unfold-next-eq = λ s → subst (λ z → Unfolding.unfold-next u₁ s ≈C z)
                                      (eqN s) ≈C-refl
      })
