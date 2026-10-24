------------------------------------------------------------------------
-- Correspondence between _⇒ℱ_ (structured simulation) and CoalgHom
--
-- Establishes: standard bisimulation _≈C_ is a subrelation of _⇒ℱ_;
-- every CoalgHom induces pointwise _⇒ℱ_ witnesses (forget functor);
-- StandardConditions characterises the image of forget; non-fullness
-- is conditional on nontrivial Cosmos instances
--
-- _⇒ℱ_（结构化模拟）与余代数同态的对应
--
-- 证明：标准互模拟 _≈C_ 是 _⇒ℱ_ 的子关系；每个 CoalgHom 诱导逐点 _⇒ℱ_
-- 见证（忘却函子）；StandardConditions 刻画忘却函子的像；非满性依赖于
-- 非平凡 Cosmos 实例的存在
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module SecondPass.MorphismCorrespondence where

open import Agda.Primitive using (Level; lsuc; _⊔_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality.Core using (cong; sym; trans; subst)
open import Relation.Nullary using (¬_)
open import Data.Product.Base using (_,_; ∃)
open import Function.Bundles using (Func)

open import Categories.Category.Core using (Category)
open import Categories.Functor.Core using (Functor)

open import Cosmos.ContCategory using (ContCat)
open import Cosmos.ContCategoryLemmas using (ShapeOf; PosOf)
open import SecondPass.Unfolding using (Unfolding; mapUnfolding)
open import SecondPass.MorphismObject using (MorphismObject)
open import SecondPass.Cosmos using (Cosmos; out; _⇒ℱ[_]_; _⇒ℱ_; ⇒ℱLayer[_])
open import SecondPass.Terminal using (Coalgebra; CoalgHom; cosmosCoalg; _≈C_)
open import SecondPass.CoalgCat using (_≈Coalg_)

module _ {o h e s p : Level}
         {C : Category o h e}
         {FC : Functor C (ContCat s p)} where
  open _≈C_
  private
    L = o ⊔ h ⊔ e ⊔ s ⊔ p
    T = Cosmos C FC
    CC = cosmosCoalg {C = C} {FC = FC}

  -- _≈C_ implies _⇒ℱ[_]_
  -- _≈C_ 蕴含 _⇒ℱ[_]_
  ≈C→⇒ℱ : ∀ {x y : T} → x ≈C y → x ⇒ℱ y
  ≈C→⇒ℱ {x} {y} eq ._⇒ℱ[_]_.out = record
    { shapeTrans  = λ {A} {s} p → UY.pos-to-shape s p
    ; morphismObj = record
      { onPos      = λ p → p
      ; pts-compat = λ p → refl
      }
    ; morphismMor = record
      { onActP = λ f s p → refl
      }
    ; onunfold-next = λ {A} s → ≈C→⇒ℱ (eq .unfold-next-eq s)
    }
    where
      UY = out y
      module UY = Unfolding UY

  -- Transport _⇒ℱ[_]_ along equality
  -- 沿等式传输 _⇒ℱ[_]_
  ⇒ℱ-respˡ : ∀ {x x' y : T} → x ≡ x' → x ⇒ℱ y → x' ⇒ℱ y
  ⇒ℱ-respˡ refl m = m

  ⇒ℱ-respʳ : ∀ {x y y' : T} → y ≡ y' → x ⇒ℱ y → x ⇒ℱ y'
  ⇒ℱ-respʳ refl m = m

  -- Forget functor: CoalgHom → pointwise _⇒ℱ[_]_
  -- 忘却函子：CoalgHom → 逐点 _⇒ℱ[_]_
  -- forget-helper：从 CoalgHom h 和 x 构造 x ⇒ℱ b（b ≡ f x）。
  -- b≡fx 用于将 commute 等式传输到 b，并在递归步骤中关联下一层种子。
  forget-helper : (h : CoalgHom CC CC)
                → ∀ {b : T} (x : T) (b≡fx : b ≡ Func.to (CoalgHom.f h) x)
                → x ⇒ℱ b
  forget-helper h {b} x b≡fx ._⇒ℱ[_]_.out = record
    { shapeTrans  = λ {A} {s} p → UB.pos-to-shape s p
    ; morphismObj = record
      { onPos      = λ p → p
      ; pts-compat = λ p → refl
      }
    ; morphismMor = record
      { onActP = λ f s p → refl
      }
    ; onunfold-next = λ {A} s →
        let seed        = UX.unfold-next s
            commute-next = cong (λ u → Unfolding.unfold-next u s)
                               (fh.commute x)
            b-next       = cong (λ u → Unfolding.unfold-next u s)
                               (cong out b≡fx)
            b'≡fseed    = trans b-next (sym commute-next)
        in forget-helper h seed b'≡fseed
    }
    where
      f  = Func.to (CoalgHom.f h)
      module fh = CoalgHom h
      UX  = out x
      UFX = out (f x)
      UB  = out b
      module UX  = Unfolding UX
      module UB  = Unfolding UB

  forget : (h : CoalgHom CC CC) → ∀ x → x ⇒ℱ Func.to (CoalgHom.f h) x
  forget h x = forget-helper h x refl

  -- Structured function carrying _⇒ℱ[_]_ witnesses
  -- 携带 _⇒ℱ[_]_ 见证的结构化函数
  record StructuredFunc : Set (lsuc L) where
    field
      f       : T → T
      witness : ∀ x → x ⇒ℱ f x

  forget→structured : (h : CoalgHom CC CC) → StructuredFunc
  forget→structured h = record
    { f       = Func.to (CoalgHom.f h)
    ; witness = forget h
    }

  -- Faithfulness: injective on underlying functions
  -- 忠实性：底层函数单射
  forget-faithful : ∀ {h h' : CoalgHom CC CC}
    → Func.to (CoalgHom.f h) ≡ Func.to (CoalgHom.f h')
    → h ≈Coalg h'
  forget-faithful {h} {h'} f≡ x = cong (λ g → g x) f≡

  -- StandardConditions: characterisation of forget's image
  -- 标准条件：忘却函子的像的刻画
  record StandardConditions {x y : T} (m : x ⇒ℱ y) : Set L where
    coinductive
    private
      UX = out x
      UY = out y
      module UX = Unfolding UX
      module UY = Unfolding UY
      module ml = ⇒ℱLayer[_] (m .out)
      module mo = MorphismObject ml.morphismObj
    field
      uf-eq : UX.unfoldFunctor ≡ UY.unfoldFunctor
      pts-preserved : ∀ {A} {s : ShapeOf FC A} (p : PosOf FC s)
        → subst (λ G → ShapeOf FC (Functor.₀ G (A , s)))
                uf-eq (UX.pos-to-shape s p)
        ≡ UY.pos-to-shape s (mo.onPos p)
      recursive : ∀ {A} (s : ShapeOf FC A)
        → StandardConditions (ml.onunfold-next s)

  -- forget's image satisfies StandardConditions
  -- 忘却像满足标准条件
  private
    pts-lemma2 : ∀ {f : T → T} {UX UFX UB : Unfolding FC T}
               → (eq1 : mapUnfolding f UX ≡ UFX)
               → (eq2 : UB ≡ UFX)
               → ∀ {A : Category.Obj C} {sh : ShapeOf FC A} (p : PosOf FC sh)
               → subst (λ G → ShapeOf FC (Functor.₀ G (A , sh)))
                        (trans (cong Unfolding.unfoldFunctor eq1)
                               (cong Unfolding.unfoldFunctor (sym eq2)))
                        (Unfolding.pos-to-shape UX sh p)
               ≡ Unfolding.pos-to-shape UB sh p
    pts-lemma2 refl refl _ = refl

  forget→standard : ∀ (h : CoalgHom CC CC) (x : T)
    → StandardConditions (forget h x)
  forget→standard h x = helper x refl
    where
      f  = Func.to (CoalgHom.f h)
      module fh = CoalgHom h

      helper : ∀ {b : T} (x : T) (b≡fx : b ≡ f x)
             → StandardConditions (forget-helper h x b≡fx)

      helper {b} x b≡fx .StandardConditions.uf-eq =
        let UX = out x
            UFX = out (f x)
            UB = out b
            eq-commute = fh.commute x
            eq-b = cong out b≡fx
        in trans (cong Unfolding.unfoldFunctor eq-commute)
                 (cong Unfolding.unfoldFunctor (sym eq-b))

      helper {b} x b≡fx .StandardConditions.pts-preserved {A} {sh} p =
        let UX = out x
            UFX = out (f x)
            UB = out b
            eq-commute = fh.commute x
            eq-b = cong out b≡fx
        in pts-lemma2 {f = f} {UX = UX} {UFX = UFX} {UB = UB}
                       eq-commute eq-b {A = A} {sh = sh} p

      helper {b} x b≡fx .StandardConditions.recursive {A} sh =
        let UX = out x
            UFX = out (f x)
            UB = out b
            eq-commute = fh.commute x
            eq-b = cong out b≡fx
            b-next       = cong (λ u → Unfolding.unfold-next u sh) eq-b
            commute-next = cong (λ u → Unfolding.unfold-next u sh) eq-commute
            b'≡fseed    = trans b-next (sym commute-next)
        in helper (Unfolding.unfold-next UX sh) b'≡fseed

  -- Non-fullness (conditional)
  -- 非满性（条件性）
  record NontrivialCosmos : Set (lsuc L) where
    field
      sf          : StructuredFunc
      x           : T
      not-commute : ¬ (mapUnfolding (StructuredFunc.f sf) (out x)
                     ≡ out (StructuredFunc.f sf x))

  not-full : NontrivialCosmos
    → ∃ λ (sf : StructuredFunc)
    → ¬ (∀ z → mapUnfolding (StructuredFunc.f sf) (out z)
             ≡ out (StructuredFunc.f sf z))
  not-full nc =
    ( NontrivialCosmos.sf nc
    , λ h → NontrivialCosmos.not-commute nc (h (NontrivialCosmos.x nc))
    )
