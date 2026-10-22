------------------------------------------------------------------------
-- Permuted embedding on the carried M base: refuting criterion C
--
-- Legacy result: for every f : Fin n → Fin n with a left inverse, a
-- tower-specific permuted embedding applies f at each layer together
-- with a liftAt applying f⁻¹, and when f has a non-fixed point the
-- embedding does not preserve the input F₀ while liftAt 0 is the
-- identity — refuting "feasibility of an embedding implies preservation
-- of the input F₀". On M the strict layer tower is absorbed by the
-- indexed coinductive type, so the residual content is purely finitary:
-- over a singleton-position container with shape fibre the plain
-- non-indexed enum Two, the transposition sw is a feasible carried
-- routing, is invertible (its own two-sided inverse, swapAdj is a
-- self-adjunction — the M form of an injective, identity-at-the-base
-- lift), yet changes shapes (sw w0 = w1 ≠ w0). The mismatch is absorbed
-- by constructive no-confusion.
--
-- 携带式 M 底座上的置换嵌入：反驳判据 C
--
-- 旧结果：对每个带左逆的 f : Fin n → Fin n，构造在每层施加 f 的塔特定
-- 置换嵌入，并用施加 f⁻¹ 的 liftAt 抵消；当 f 有非不动点时，嵌入在第 0
-- 层不保持输入 F₀，而 liftAt 0 为恒等——反驳“嵌入的可行性蕴含对输入 F₀
-- 的保持”。M 上严格层塔被索引余归纳类型吸收，剩余内容纯粹有限：在位置
-- 单点、形状纤维为普通非索引枚举 Two 的容器上，对换 sw 是完全可行的携带
-- 式路由，可逆（自身双侧逆，swapAdj 是自伴随——即“基底处恒等、单射的
-- lift”的 M 形态），却不保持输入形状（sw w0 = w1 ≠ w0）。失配由构造性
-- 无混淆吸收。
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module Cosmos.M.PermutedEmbedding where

open import Agda.Primitive using (lzero)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Unit.Polymorphic.Base using (⊤; tt)
open import Data.Product.Base using (proj₁)
open import Data.Container.Core using (Container)
open import Function.Base using (id)
open import Relation.Binary.PropositionalEquality.Core using (cong; _≢_)
open import Relation.Nullary.Negation using (¬_)

open import Categories.Category.Core using (Category)
open import Categories.Category.Indiscrete using (Indiscrete)
open import Categories.Functor.Core using (Functor)

open import Cosmos.ContCategory using (ContCat; ≈sr-refl)
open import Cosmos.ContCatEquiv using (ShapeCat)
import Cosmos.M.Object as MO
open import Base.MCorr.Setoid using (FiberAdjˢ; propEqOn)

------------------------------------------------------------------------
-- The two-element shape fibre
--
-- A plain non-indexed enumeration, so that matching its constructors
-- needs no injectivity (Cubical-safe).
--
-- 两元素形状纤维
--
-- 普通非索引枚举，故匹配其构造子无需内射（Cubical 安全）。

data Two : Set lzero where
  w0 w1 : Two

w1≢w0 : ¬ (w1 ≡ w0)
w1≢w0 ()

------------------------------------------------------------------------
-- Base category, container, and rigid container functor
--
-- Base category Indiscrete Two, a container with Shape = Two and
-- singleton positions, and the identity-on-shape rigid container
-- functor.
--
-- 基范畴、容器与刚性容器函子
--
-- 基范畴 Indiscrete Two，容器 Shape = Two、位置单点，容器函子在形状上
-- 恒等作用（刚性）。

C2 : Category lzero lzero lzero
C2 = Indiscrete Two

TwoContainer : Container lzero lzero
TwoContainer = record { Shape = Two ; Position = λ _ → ⊤ }

TwoFC : Functor C2 (ContCat lzero lzero)
TwoFC = record
  { F₀           = λ _ → TwoContainer
  ; F₁           = λ _ → record { shape = id ; position = λ _ → tt }
  ; identity     = ≈sr-refl
  ; homomorphism = ≈sr-refl
  ; F-resp-≈     = λ _ → ≈sr-refl
  }

ufId : Functor (ShapeCat C2 TwoFC) C2
ufId = record
  { F₀           = proj₁
  ; F₁           = proj₁
  ; identity     = refl
  ; homomorphism = refl
  ; F-resp-≈     = λ p → p
  }

-- Object-preserving label with shape routing r; positions singleton.
--
-- 形状路由为 r 的对象保持标签；位置单点。
label : (r : Two → Two) → MO.CosmosData C2 TwoFC
label r = record { uf = ufId ; pts = λ s _ → r s }

------------------------------------------------------------------------
-- The transposition sw
--
-- Swaps w0 and w1; definitionally an involution (its own two-sided
-- inverse), and moves w0 to w1.
--
-- 对换 sw
--
-- 交换 w0 与 w1；定义性对合（即自身的双侧逆），并把 w0 移到 w1。

sw : Two → Two
sw w0 = w1
sw w1 = w0

sw-invol : ∀ (s : Two) → sw (sw s) ≡ s
sw-invol w0 = refl
sw-invol w1 = refl

sw-moves-w0 : sw w0 ≢ w0
sw-moves-w0 = w1≢w0

------------------------------------------------------------------------
-- The carried fibre self-adjunction of sw
--
-- to = fro = sw with the involution as both round-trip laws — the M
-- form of the feasible embedding together with its canceling,
-- identity-at-the-base (hence injective) lift; a self-adjunction is a
-- carried bijection.
--
-- sw 的携带式纤维自伴随
--
-- to = fro = sw，对合同时作为两条往返律——“可行嵌入 + 其抵消的、基底处
-- 恒等（故单射）的 lift”的 M 形态；自伴随即携带式双射。

swapAdj : FiberAdjˢ (propEqOn Two) (propEqOn Two)
swapAdj = record
  { to       = sw
  ; fro      = sw
  ; to-cong  = λ e → cong sw e
  ; fro-cong = λ e → cong sw e
  ; η        = sw-invol
  ; ε        = sw-invol
  }

-- The permuted label: a valid object-preserving CosmosData whose shape
-- routing is sw; feasible, carries swapAdj, yet changes shapes.
--
-- 置换标签：合法的对象保持 CosmosData，其形状路由为 sw；可行、携带
-- swapAdj，却改变形状。
permuted-label : MO.CosmosData C2 TwoFC
permuted-label = label sw

------------------------------------------------------------------------
-- Criterion C, M form
--
-- Every routing f equipped with a left inverse must fix every shape, and
-- its refutation by sw.
--
-- 判据 C 的 M 形态
--
-- 每个配有左逆的路由必须固定每个形状，及其由 sw 给出的反驳。

CriterionC : Set lzero
CriterionC =
  ∀ (f f⁻¹ : Two → Two)
  → (∀ (s : Two) → f⁻¹ (f s) ≡ s)
  → ∀ (s : Two) → f s ≡ s

criterion-C-refuted : ¬ CriterionC
criterion-C-refuted cc =
  w1≢w0 (cc sw sw sw-invol w0)
