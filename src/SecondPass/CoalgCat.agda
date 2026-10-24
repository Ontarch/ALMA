------------------------------------------------------------------------
-- Category of F-coalgebras and terminal object packaging
--
-- Constructs CoalgCat: objects are CosmosF-coalgebras, morphisms are
-- coalgebra homomorphisms, equivalence is pointwise propositional equality
-- Packages cosmosCoalg as terminal up to bisimulation _≈C_, without funext
-- or proof irrelevance (strengthening to _≡_ would require both)
--
-- F-余代数范畴与终对象封装
--
-- 构造 CoalgCat：对象为 CosmosF-余代数，态射为余代数同态，等价为逐点命题相等
-- 将 cosmosCoalg 封装为互模拟 _≈C_ 意义下的终对象（无需函数外延性与证明无关性；
-- 强化到 _≡_ 需要二者）
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module SecondPass.CoalgCat where

open import Agda.Primitive using (Level; lsuc; _⊔_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality.Core using (cong; sym; trans)
open import Relation.Binary.PropositionalEquality.Properties using (module ≡-Reasoning)
open ≡-Reasoning
open import Function.Base using (id)
open import Function.Bundles using (Func)

open import Categories.Category.Core using (Category)
open import Categories.Functor.Core using (Functor)
open import Categories.Functor.Coalgebra using (F-Coalgebra)
import Categories.Category.Construction.F-Coalgebras as FCoalg

open import Cosmos.ContCategory using (ContCat)
open import SecondPass.Unfolding using (mapUnfolding; mapUnfolding-id; mapUnfolding-∘; module UnfoldingEndoFunctor)
open import SecondPass.Terminal
  using (Coalgebra; CoalgHom; cosmosCoalg; ana-hom; unique-ana; _≈C_)

module _ {o h e s p : Level}
         {C : Category o h e}
         {FC : Functor C (ContCat s p)} where
  private
    L = o ⊔ h ⊔ e ⊔ s ⊔ p
    Lʳ = o ⊔ s ⊔ p
    module Coal = Coalgebra
    module Hom  = CoalgHom

    Coalgebra′ : (r : Level) → Set (lsuc (L ⊔ r))
    Coalgebra′ r = Coalgebra {o} {h} {e} {s} {p} {C} {FC} r

    CoalgHom′ : {r₁ r₂ : Level} → Coalgebra′ r₁ → Coalgebra′ r₂
              → Set (L ⊔ r₁ ⊔ r₂)
    CoalgHom′ {r₁} {r₂} = CoalgHom {o} {h} {e} {s} {p} {C} {FC} {r₁} {r₂}

  -- Identity and composition of coalgebra homomorphisms
  -- 余代数同态的恒等与复合
  idCoalg : ∀ {r} {X : Coalgebra′ r} → CoalgHom′ X X
  idCoalg {X = X} = record
    { f       = record { to = id; cong = λ eq → eq }
    ; commute = λ x → mapUnfolding-id (Func.to (Coal.α X) x)
    }

  -- Composition: mapUnfolding-∘ reduces mapUnfolding (g∘f) to mapUnfolding g ∘ mapUnfolding f,
  -- then f.commute and g.commute chain to Z.α
  -- 复合：mapUnfolding-∘ 将 mapUnfolding (g∘f) 归约为 mapUnfolding g ∘ mapUnfolding f，
  -- 再经 f.commute 与 g.commute 链式得到 Z.α
  _∘Coalg_ : ∀ {r₁ r₂ r₃}
               {X : Coalgebra′ r₁} {Y : Coalgebra′ r₂} {Z : Coalgebra′ r₃}
           → CoalgHom′ Y Z → CoalgHom′ X Y → CoalgHom′ X Z
  _∘Coalg_ {X = X} {Y = Y} {Z = Z} g f = record
    { f       = record
      { to   = λ x → Func.to (Hom.f g) (Func.to (Hom.f f) x)
      ; cong = λ x≈y → Func.cong (Hom.f g) (Func.cong (Hom.f f) x≈y)
      }
    ; commute = λ x → begin
        mapUnfolding (λ x → Func.to (Hom.f g) (Func.to (Hom.f f) x)) (Func.to (Coal.α X) x)
          ≡⟨ mapUnfolding-∘ (Func.to (Hom.f g)) (Func.to (Hom.f f)) (Func.to (Coal.α X) x) ⟩
        mapUnfolding (Func.to (Hom.f g)) (mapUnfolding (Func.to (Hom.f f)) (Func.to (Coal.α X) x))
          ≡⟨ cong (mapUnfolding (Func.to (Hom.f g))) (Hom.commute f x) ⟩
        mapUnfolding (Func.to (Hom.f g)) (Func.to (Coal.α Y) (Func.to (Hom.f f) x))
          ≡⟨ Hom.commute g (Func.to (Hom.f f) x) ⟩
        Func.to (Coal.α Z) (Func.to (Hom.f g) (Func.to (Hom.f f) x))
      ∎
    }

  -- Pointwise _≡_ on underlying functions; stronger than _≈C_
  -- 底层函数的逐点 _≡_；强于 _≈C_
  _≈Coalg_ : ∀ {r} {X Y : Coalgebra′ r}
           → CoalgHom′ X Y → CoalgHom′ X Y → Set L
  _≈Coalg_ f g = ∀ x → Func.to (Hom.f f) x ≡ Func.to (Hom.f g) x

  -- Category instance
  -- Laws are inlined: top-level helpers cause metavariable drift via CoalgHom′
  -- ∘-resp-≈: outer f≈, then inner g≈; proofs end in (x)
  -- 范畴实例
  -- 范畴律内联编写：顶层辅助函数会导致 CoalgHom′ 别名上的元变量漂移
  -- ∘-resp-≈：先外层 f≈，再内层 g≈；证明以 (x) 结尾
  CoalgCat : Category (lsuc L) L L
  CoalgCat = record
    { Obj       = Coalgebra′ L
    ; _⇒_       = λ X Y → CoalgHom′ {r₁ = L} {r₂ = L} X Y
    ; _≈_       = λ f g → _≈Coalg_ {r = L} f g
    ; id        = idCoalg {r = L}
    ; _∘_       = _∘Coalg_
    ; assoc     = λ {A B C D} {f g h} x → refl
    ; sym-assoc = λ {A B C D} {f g h} x → refl
    ; identityˡ = λ {A B} {f} x → refl
    ; identityʳ = λ {A B} {f} x → refl
    ; identity² = λ {A} x → refl
    ; equiv     = λ {A B} → record
      { refl  = λ {f} _ → refl
      ; sym   = λ {f g} eq x → sym (eq x)
      ; trans = λ {f g h} eq1 eq2 x → trans (eq1 x) (eq2 x)
      }
    ; ∘-resp-≈  = λ {A B C} {f h : CoalgHom′ {r₁ = L} {r₂ = L} B C}
                       {g i : CoalgHom′ {r₁ = L} {r₂ = L} A B}
                  f≈ g≈ x →
        trans (f≈ (Func.to (Hom.f g) x)) (cong (Func.to (Hom.f h)) (g≈ x))
    }

  -- Terminal object up to bisimulation
  -- Uniqueness only up to _≈C_; upgrading to _≡_ needs funext + proof irrelevance
  -- 互模拟意义下的终对象
  -- 唯一性仅到互模拟 _≈C_；强化到 _≡_ 需要函数外延性与证明无关性
  record IsTerminalUpToBisim : Set (lsuc L) where
    field
      !        : (X : Coalgebra′ Lʳ) → CoalgHom′ {r₁ = Lʳ} {r₂ = Lʳ} X cosmosCoalg
      !-unique : ∀ {X : Coalgebra′ Lʳ}
                   (f : CoalgHom′ {r₁ = Lʳ} {r₂ = Lʳ} X cosmosCoalg)
               → ∀ x → Func.to (Hom.f f) x ≈C Func.to (Hom.f (! X)) x

  -- cosmosCoalg is terminal up to _≈C_: ! = ana-hom, uniqueness = unique-ana
  -- cosmosCoalg 在 _≈C_ 意义下为终对象：! = ana-hom，唯一性 = unique-ana
  cosmosIsTerminal : IsTerminalUpToBisim
  cosmosIsTerminal = record
    { !        = ana-hom
    ; !-unique = λ {X} f x → unique-ana X f x
    }

  -- Standard-library packaging
  -- 标准库封装
  open UnfoldingEndoFunctor {C = C} {FC = FC}

  -- Standard-library F-coalgebra category for the unfolding endofunctor
  -- 展开自函子的标准库 F-余代数范畴
  StdCoalgCat : Category _ _ _
  StdCoalgCat = FCoalg.F-Coalgebras UnfoldingEndoFunctor

  -- Bridge: ALMA Coalgebra → standard F-Coalgebra
  -- 桥接：ALMA Coalgebra → 标准 F-Coalgebra
  toStdCoalg : Coalgebra′ Lʳ → F-Coalgebra UnfoldingEndoFunctor
  toStdCoalg X = record
    { A = Coal.Carrier X
    ; α = record
      { to   = Func.to (Coal.α X)
      ; cong = λ {x} {y} x≈y →
          Func.cong (Coal.α X) x≈y
      }
    }

  -- Bridge: standard F-Coalgebra → ALMA Coalgebra
  -- 桥接：标准 F-Coalgebra → ALMA Coalgebra
  fromStdCoalg : F-Coalgebra UnfoldingEndoFunctor → Coalgebra′ Lʳ
  fromStdCoalg X = record
    { Carrier = F-Coalgebra.A X
    ; α = record
      { to   = Func.to (F-Coalgebra.α X)
      ; cong = λ {x} {y} x≈y →
          Func.cong (F-Coalgebra.α X) x≈y
      }
    }
