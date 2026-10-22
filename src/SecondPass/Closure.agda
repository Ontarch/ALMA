------------------------------------------------------------------------
-- Closure Properties of Cosmos
-- Cosmos 的闭包性质
--
-- out / in-F form an adjoint equivalence between Cosmos and Unfolding Cosmos
-- map closure: any Setoid endofunction lifts to a universe transformation
-- UnitCosmos uniqueness among UnitLike cosmoi
-- out / in-F 构成 Cosmos 与 Unfolding Cosmos 之间的伴随等价
-- 映射闭包：任意 Setoid 自映射可提升为宇宙变换
-- UnitCosmos 在 UnitLike 宇宙中的唯一性
------------------------------------------------------------------------
{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module SecondPass.Closure where

open import Agda.Primitive using (Level; _⊔_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Sigma using (_,_)
open import Relation.Binary.PropositionalEquality.Core using (cong; trans)
open import Relation.Binary.Bundles using (Setoid)
import Relation.Binary.Reasoning.Setoid as SetoidReasoning
open import Data.Unit.Polymorphic.Base using (⊤)
open import Function.Bundles using (Func)
open import Function.Base using (_∘_)
open import Function.Construct.Composition using (function)

open import Categories.Category.Core using (Category)
open import Categories.Functor.Core using (Functor)

open import Cosmos.ContCategory using (ContCat)
open import Cosmos.ContCategoryLemmas using (ShapeOf)
open import SecondPass.Unfolding using (Unfolding; mapUnfolding; mapUnfolding-id; mapUnfolding-∘; module UnfoldingSetoid)
open import SecondPass.Cosmos
  using (Cosmos; out; UnitCosmos; UnitCat; UnitContainerFunctor)
open import SecondPass.Terminal
  using (Coalgebra; cosmosCoalg; _≈C_; ≈C-refl; ≈C-trans; cosmosSetoid)
open import SecondPass.Lambek using (in-F; in-F-resp-≈F; in∘out≈id; out∘in≈Fid)

module _ {o h e s p : Level}
         {C : Category o h e}
         {FC : Functor C (ContCat s p)} where
  private
    L = o ⊔ h ⊔ e ⊔ s ⊔ p
    Lʳ = o ⊔ s ⊔ p
    T = Cosmos C FC
    FT = Unfolding FC T
    CS : Setoid L Lʳ
    CS = cosmosSetoid {C = C} {FC = FC}
    module US = UnfoldingSetoid
      {o = o} {h = h} {e = e} {s = s} {p = p} {C = C} {F = FC}
    module Coal = Coalgebra

    -- Instantiate the bisimulation relation for the current C/FC
    -- 实例化当前 C/FC 下的互模拟关系
    _≈C′_ : T → T → Set Lʳ
    _≈C′_ = _≈C_ {o = o} {h = h} {e = e} {s = s} {p = p} {C = C} {FC = FC}

  -- out as a Setoid morphism from Cosmos (carrying bisimulation) to the
  -- Unfolding Setoid; the forward direction of the Lambek isomorphism
  -- out 作为 Setoid 态射，从 Cosmos（携带互模拟等价）到 Unfolding Setoid；
  -- 即 Lambek 同构的正向
  outFunc : Func CS (US.unfoldingSetoid CS)
  outFunc = Coal.α cosmosCoalg

  -- in-F as a Setoid morphism, the backward direction of the Lambek
  -- isomorphism; congruence is supplied by in-F-resp-≈F
  -- in-F 作为 Setoid 态射，即 Lambek 同构的逆向；
  -- 其同态性由 in-F-resp-≈F 提供
  inFFunc : Func (US.unfoldingSetoid CS) CS
  inFFunc = record { to = in-F ; cong = in-F-resp-≈F }

  -- Unit (left inverse) and counit (right inverse) of Lambek isomorphism
  -- Lambek 同构的单位（左逆）与余单位（右逆）
  unit : ∀ x → in-F (out x) ≈C′ x
  unit = in∘out≈id

  counit : ∀ y → US._≈U_ {X = CS} (out (in-F y)) y
  counit = out∘in≈Fid

  private
    -- Identity Setoid endomorphism on Cosmos (with bisimulation), used as
    -- the unit for the map-closure construction
    -- Cosmos（携带互模拟等价）上的恒等 Setoid 自态射，用作映射闭包构造的单位
    idCS : Func CS CS
    idCS = record { to = λ x → x ; cong = λ x≈y → x≈y }

  -- Map closure: lifts a Setoid endomap on Cosmos to a universe transformation
  -- 映射闭包：将宇宙上的 Setoid 自映射提升为宇宙自身的映射
  mapℱ : Func CS CS → Func CS CS
  mapℱ F = record
    { to   = λ x → in-F (mapUnfolding (Func.to F) (out x))
    ; cong = λ {x} {y} x≈y →
        in-F-resp-≈F
          (Func.cong (US.mapUnfolding-resp F) (Func.cong outFunc x≈y))
    }

  -- Map closure preserves identity (up to bisimulation)
  -- 映射闭包保持恒等（互模拟意义下）
  mapℱ-id : ∀ x → Func.to (mapℱ idCS) x ≈C′ x
  mapℱ-id x =
    let open SetoidReasoning CS
    in begin
      Func.to (mapℱ idCS) x
        ≡⟨ refl ⟩
      in-F (mapUnfolding (λ z → z) (out x))
        ≡⟨ cong in-F (mapUnfolding-id (out x)) ⟩
      in-F (out x)
        ≈⟨ in∘out≈id x ⟩
      x
    ∎

  -- Map closure preserves composition (up to bisimulation)
  -- 映射闭包保持复合（互模拟意义下）
  mapℱ-comp : ∀ (F G : Func CS CS) x
            → Func.to (mapℱ (function F G)) x
              ≈C′ Func.to (mapℱ G) (Func.to (mapℱ F) x)
  mapℱ-comp F G x =
    let open SetoidReasoning CS
    in begin
      Func.to (mapℱ (function F G)) x
        ≡⟨ refl ⟩
      in-F (mapUnfolding (Func.to G ∘ Func.to F) (out x))
        ≡⟨ cong in-F (mapUnfolding-∘ (Func.to G) (Func.to F) (out x)) ⟩
      in-F (mapUnfolding (Func.to G) (mapUnfolding (Func.to F) (out x)))
        ≈⟨ in-F-resp-≈F
            (Func.cong (US.mapUnfolding-resp G)
              (US.≈U-sym CS (out∘in≈Fid (mapUnfolding (Func.to F) (out x))))) ⟩
      in-F (mapUnfolding (Func.to G) (out (in-F (mapUnfolding (Func.to F) (out x)))))
        ≡⟨ refl ⟩
      Func.to (mapℱ G) (Func.to (mapℱ F) x)
    ∎

  -- Compatibility of mapℱ with out (counit relation)
  -- mapℱ 与 out 的相容性（余单位关系）
  out-mapℱ : ∀ (F : Func CS CS) x
           → US._≈U_ {X = CS} (out (Func.to (mapℱ F) x)) (mapUnfolding (Func.to F) (out x))
  out-mapℱ F x = counit (mapUnfolding (Func.to F) (out x))

  -- Triangle identities for the adjoint equivalence out ⊣ in-F
  -- 伴随等价 out ⊣ in-F 的三角恒等式
  triangle-left : ∀ (x : T) → US._≈U_ {X = CS} (out (in-F (out x))) (out x)
  triangle-left x = counit (out x)

  triangle-right : ∀ (y : FT) → in-F (out (in-F y)) ≈C′ in-F y
  triangle-right y = unit (in-F y)

-- Uniqueness of UnitCosmos
-- UnitCosmos 的唯一性
module _ {ℓ : Level} where
  private
    C₀  = UnitCat {ℓ}
    FC₀ = UnitContainerFunctor {ℓ}
    T₀  = Cosmos C₀ FC₀

    _≈C₀_ : T₀ → T₀ → Set ℓ
    _≈C₀_ = _≈C_ {C = C₀} {FC = FC₀}

    ≈C₀-trans : ∀ {x y z} → x ≈C₀ y → y ≈C₀ z → x ≈C₀ z
    ≈C₀-trans = ≈C-trans {C = C₀} {FC = FC₀}

  -- UnitLike predicate: characterizes cosmoi with the same unfolding structure as UnitCosmos
  -- UnitLike 谓词：刻画与 UnitCosmos 具有相同展开结构的宇宙
  record UnitLike (x : T₀) : Set ℓ where
    field
      -- The object parts of the unfolding functors agree pointwise
      -- 展开函子在对象上逐点命题相等
      unfoldFunctor₀-eq : ∀ {A} (s : ShapeOf {C = C₀} FC₀ A)
                        → Functor.₀ (Unfolding.unfoldFunctor (out x)) (A , s)
                        ≡ Functor.₀ (Unfolding.unfoldFunctor (out UnitCosmos)) (A , s)
      next-self : ∀ {A} (s : ShapeOf {C = C₀} FC₀ A)
                → Unfolding.unfold-next (out x) s ≈C₀ x

  -- Any cosmo satisfying UnitLike is bisimilar to UnitCosmos
  -- 满足 UnitLike 的宇宙与 UnitCosmos 互模拟等价
  unitcosmos-unique : ∀ (x : T₀) → UnitLike x → x ≈C₀ UnitCosmos
  unitcosmos-unique x ul = helper ≈C₀-refl
    where
      open _≈C_
      module UL = UnitLike ul
      ≈C₀-refl : ∀ {z} → z ≈C₀ z
      ≈C₀-refl = ≈C-refl {C = C₀} {FC = FC₀}

      -- ⊤ is contractible: any two elements are propositionally equal
      -- ⊤ 可收缩：任意两个元素命题相等
      ⊤-≡ : ∀ {a b : ⊤ {ℓ}} → a ≡ b
      ⊤-≡ {a = tt} {b = tt} = refl

      -- Coinductive helper: from a ≈C₀ x derive a ≈C₀ UnitCosmos
      -- 辅助共归纳证明：由 a ≈C₀ x 推出 a ≈C₀ UnitCosmos
      helper : ∀ {a : T₀} → a ≈C₀ x → a ≈C₀ UnitCosmos
      helper {a} p .unfoldFunctor₀-eq s =
        trans (p .unfoldFunctor₀-eq s) (UL.unfoldFunctor₀-eq s)
      helper {a} p .pos-to-shape-eq {A} s q = ⊤-≡
      helper {a} p .unfold-next-eq {A} s =
        helper (≈C₀-trans (p .unfold-next-eq s) (UL.next-self s))
