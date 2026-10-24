------------------------------------------------------------------------
-- Non-trivial Cosmos instance
--
-- The list container (Shape = ℕ, Position = Fin n) as a non-trivial
-- Cosmos instance. Constructs ListCosmos / OtherCosmos, a non-standard
-- _⇒ℱ_ witness (swap-⇒ℱ with onPos = position permutation), and a
-- concrete counterexample (otherSF) showing StructuredFunc is strictly
-- larger than CoalgHom.
--
-- 非平凡 Cosmos 实例
--
-- 列表容器（形状 = ℕ，位置 = Fin n）作为非平凡 Cosmos 实例。构造
-- ListCosmos / OtherCosmos、非标准 _⇒ℱ_ 见证（onPos 为位置置换），
-- 以及具体反例 otherSF，证明 StructuredFunc 严格包含 CoalgHom。
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module SecondPass.ListCosmos where

open import Agda.Primitive using (lzero)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Fin.Base using (Fin; toℕ; splitAt; join; opposite)
  renaming (zero to fzero; suc to fsuc)
open import Data.Unit.Polymorphic.Base using (tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product.Base using (∃)
open import Relation.Binary.PropositionalEquality.Core using (_≢_; sym; cong; subst)
open import Relation.Nullary.Negation using (¬_)
open import Data.Container.Core using (Container)

open import Categories.Category.Core using (Category)
open import Categories.Functor.Core using (Functor)
open import Categories.Functor using (id)

open import Cosmos.ContCategory using (ContCat; ≈sr-refl)
open import Cosmos.ContCategoryLemmas using (ShapeOf; PosOf; actSOf; actPOf)
open import Cosmos.ContCatEquiv using (ShapeCat)
open import SecondPass.Unfolding using (Unfolding; mapUnfolding)
open import SecondPass.MorphismObject using (MorphismObject)
open import SecondPass.MorphismMorphism using (actP-from-S)
open import SecondPass.Cosmos using (Cosmos; out; _⇒ℱ[_]_; _⇒ℱ_; ⇒ℱLayer[_]; UnitCat)
open import SecondPass.MorphismCorrespondence using (StructuredFunc; NontrivialCosmos; not-full)

module _ where
  -- The terminal category at level 0, used as the base category
  --
  -- 第 0 层的终范畴，用作基范畴
  C₀ : Category lzero lzero lzero
  C₀ = UnitCat {lzero}

  -- The list container: shapes are natural numbers, positions are Fin n
  --
  -- 列表容器：形状为自然数，位置为 Fin n
  ListContainer : Container lzero lzero
  ListContainer = record { Shape = ℕ ; Position = Fin }

  -- The constant functor from the terminal category to ContCat
  --
  -- 从终范畴到 ContCat 的常值函子
  ListFC : Functor C₀ (ContCat lzero lzero)
  ListFC = record
    { F₀           = λ _ → ListContainer
    ; F₁           = λ _ → Category.id (ContCat lzero lzero)
    ; identity     = ≈sr-refl
    ; homomorphism = ≈sr-refl
    ; F-resp-≈     = λ _ → ≈sr-refl
    }

  -- The universe over the list container
  --
  -- 基于列表容器的宇宙
  T = Cosmos C₀ ListFC

  -- The trivial unfold functor from the shape category to the terminal category
  -- All objects and morphisms are mapped to the unique element of the terminal category
  --
  -- 从形状范畴到终范畴的平凡展开函子
  -- 所有对象与态射均映射到终范畴的唯一元素
  private
    TrivialUnfoldFunctor : Functor (ShapeCat C₀ ListFC) C₀
    TrivialUnfoldFunctor = record
      { F₀           = λ _ → tt
      ; F₁           = λ _ → tt
      ; identity     = tt
      ; homomorphism = tt
      ; F-resp-≈     = λ _ → tt
      }

  -- ListCosmos: the unfold functor is the terminal map, positions map to toℕ
  -- The unfolding structure is self‑referential: unfold-next always returns ListCosmos
  --
  -- ListCosmos：展开函子为终映射，位置映射为 toℕ
  -- 该展开结构自指：unfold-next 始终返回 ListCosmos 自身
  ListCosmos : T
  ListCosmos .out = record
    { unfoldFunctor   = TrivialUnfoldFunctor
    ; unfold-next     = λ _ → ListCosmos
    ; pos-to-shape    = λ {A} n i → toℕ i
    ; pos-actS-compat = λ { f refl p → refl }
    }

  -- OtherCosmos: same unfoldFunctor / unfold-next, but pos-to-shape = 0
  -- At shape 2, position (suc fzero): ListCosmos → 1, OtherCosmos → 0
  -- This pointwise difference is the seed of the non-commutativity proof
  --
  -- OtherCosmos：相同的 unfoldFunctor / unfold-next，但 pos-to-shape = 0
  -- 在形状 2、位置 (suc fzero) 处：ListCosmos → 1，OtherCosmos → 0
  -- 该逐点差异是非交换性证明的起点
  OtherCosmos : T
  OtherCosmos .out = record
    { unfoldFunctor   = TrivialUnfoldFunctor
    ; unfold-next     = λ _ → OtherCosmos
    ; pos-to-shape    = λ {A} n i → 0
    ; pos-actS-compat = λ _ _ _ → refl
    }

  -- swapFin2: the non‑identity permutation on Fin 2
  --
  -- swapFin2：Fin 2 上的非恒等置换
  swapFin2 : Fin 2 → Fin 2
  swapFin2 = opposite

  -- swap01: permutation on Fin n, swapping the first two elements when n ≥ 2
  -- For n = 0 or 1 it is the identity; for n ≥ 2 it swaps 0 and 1, leaving rest unchanged
  --
  -- swap01：Fin n 上的置换；当 n ≥ 2 时交换前两个元素
  -- n = 0 或 1 时为恒等映射；n ≥ 2 时交换 0 和 1，其余元素不变
  swap01 : (n : ℕ) → Fin n → Fin n
  swap01 zero ()
  swap01 (suc zero) i = i
  swap01 (suc (suc n)) i =
    join 2 n (swapSum (splitAt 2 i))
    where
    -- Swaps only the first two positions, leaves the rest unchanged
    --
    -- 仅交换前两个位置，其余保持不变
    swapSum : Fin 2 ⊎ Fin n → Fin 2 ⊎ Fin n
    swapSum (inj₁ i) = inj₁ (swapFin2 i)
    swapSum (inj₂ k) = inj₂ k

  -- The first element is mapped to the second, so it is not fixed
  --
  -- 第一个元素被映射到第二个元素，因此不是不动点
  swap01-fzero≠fzero : ∀ {n} → swap01 (suc (suc n)) fzero ≢ fzero
  swap01-fzero≠fzero ()

  -- swap-⇒ℱ: a non‑standard _⇒ℱ_ witness with onPos = swap01.
  -- The shape translation and position mapping are both given by swap01;
  -- the compatibility proofs are trivial due to the triviality of the category.
  --
  -- swap-⇒ℱ：onPos = swap01 的非标准 _⇒ℱ_ 见证
  -- 形状翻译与位置映射均由 swap01 给出；
  -- 因范畴退化，相容性证明平凡
  swap-⇒ℱ : ListCosmos ⇒ℱ ListCosmos
  swap-⇒ℱ ._⇒ℱ[_]_.out = record
    { shapeTrans  = λ {A} {n} i → toℕ (swap01 n i)
    ; morphismObj = record
      { onPos      = λ {A} {n} i → swap01 n i
      ; pts-compat = λ _ → refl
      }
    ; morphismMor = record { onActP = onActP-swapped }
    ; onunfold-next = λ _ → swap-⇒ℱ
    }
    where
    onActP-swapped : ∀ {A B} (f : Category._⇒_ C₀ A B) {s : ShapeOf ListFC A} {t : ShapeOf ListFC B}
                  → (p : actSOf ListFC f s ≡ t) (q : PosOf ListFC t)
                  → swap01 s (actPOf ListFC f s (subst (PosOf ListFC) (sym p) q))
                    ≡ actP-from-S ListFC ListFC id f p (swap01 t q)
    onActP-swapped f {s} {t} refl q = refl

  -- swap-⇒ℱ is non‑standard at n ≥ 2 because onPos ≠ id
  --
  -- swap-⇒ℱ 在 n ≥ 2 处非标准，因为 onPos ≠ id
  swap-⇒ℱ-nonstandard : ∀ {n}
    → let open MorphismObject
          open ⇒ℱLayer[_] (swap-⇒ℱ .out)
       in onPos morphismObj {s = suc (suc n)} fzero ≢ fzero
  swap-⇒ℱ-nonstandard = swap01-fzero≠fzero

  -- toOther: canonical _⇒ℱ_ from any cosmos to OtherCosmos
  -- onPos = id, shapeTrans = 0 (matches OtherCosmos.pos-to-shape)
  -- Coinductive: recursive call at head of onunfold-next lambda
  --
  -- toOther：从任意宇宙到 OtherCosmos 的典范 _⇒ℱ_
  -- onPos = id，shapeTrans = 0（与 OtherCosmos.pos-to-shape 匹配）
  -- 余归纳：递归调用在 onunfold-next lambda 体头部
  toOther : ∀ x → x ⇒ℱ OtherCosmos
  toOther x ._⇒ℱ[_]_.out = record
    { shapeTrans  = λ {A} {n} i → 0
    ; morphismObj = record
      { onPos      = λ {A} {n} i → i
      ; pts-compat = λ _ → refl
      }
    ; morphismMor = record
      { onActP = λ _ _ _ → refl
      }
    ; onunfold-next = λ {A} s →
        toOther (Unfolding.unfold-next (out x) s)
    }

  -- otherSF: StructuredFunc with f = const OtherCosmos, witness from toOther
  --
  -- otherSF：f = const OtherCosmos 的 StructuredFunc，witness 由 toOther 给出
  otherSF : StructuredFunc {C = C₀} {FC = ListFC}
  otherSF = record { f = λ _ → OtherCosmos ; witness = toOther }
  pos2 : Fin 2
  pos2 = fsuc {n = 1} (fzero {n = 0})

  -- Pointwise failure at ListCosmos: pos-to-shape differs
  --
  -- 在 ListCosmos 处点态失败：pos-to-shape 不同
  otherSF-not-commute-ListCosmos :
      ¬ (mapUnfolding (λ _ → OtherCosmos) (out ListCosmos) ≡ out OtherCosmos)
  otherSF-not-commute-ListCosmos eq
    with cong (λ c → Unfolding.pos-to-shape c (suc (suc zero)) pos2) eq
  ... | ()

  -- Concrete non-trivial instance for non-fullness
  --
  -- 非满性的具体非平凡实例
  listNontrivial : NontrivialCosmos {C = C₀} {FC = ListFC}
  listNontrivial = record
    { sf          = otherSF
    ; x           = ListCosmos
    ; not-commute = otherSF-not-commute-ListCosmos
    }

  -- Unconditional non-fullness for this instance
  --
  -- 该实例下的无条件非满性
  listNotFull : ∃ λ (sf : StructuredFunc {C = C₀} {FC = ListFC})
             → ¬ (∀ z → mapUnfolding (StructuredFunc.f sf) (out z)
                      ≡ out (StructuredFunc.f sf z))
  listNotFull = not-full listNontrivial
