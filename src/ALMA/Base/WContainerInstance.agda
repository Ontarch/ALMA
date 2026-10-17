------------------------------------------------------------------------
-- Deterministic container μ as the native W-type
--
-- The inductive seam dual to ContainerInstance: for a plain container
-- (S , P) the edge family is deterministic at the trivial index ⊤. At
-- that system the generic edge-family Wˣ is the container W-type, with
-- node playing the role of Data.W's sup over the extension ⟦ S ▷ P ⟧.
-- A strict propositional bijection is not derivable under the fixed
-- flags, so the identification is carried instead: the native W
-- inherits the finite bisimulation as its EqOn (eqWⁿ), and the two maps
-- are mutually inverse and respectful up to that carried setoid. This
-- is exact, not an approximation.
--
-- 确定性容器 μ 即原生 W 型
--
-- ContainerInstance 的归纳接缝：对普通容器 (S , P)，边族在平凡索引 ⊤
-- 处是确定性的。在该系统上，泛型边族 Wˣ 就是容器 W 型，node 扮演
-- Data.W 的 sup（作用于扩展 ⟦ S ▷ P ⟧）。固定开关下导不出严格命题
-- 双射，故改为携带式等同：原生 W 以有限互模拟为其 EqOn（eqWⁿ），两个
-- 映射在该携带 setoid 上互为逆且保持等价。这是精确的，而非近似。
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module ALMA.Base.WContainerInstance where

open import Agda.Primitive using (Level; lzero; _⊔_)
open import Agda.Builtin.Equality using (refl)
open import Agda.Builtin.Sigma using (_,_)

open import Data.Unit using (⊤; tt)
open import Data.Container.Core using (Container; _▷_)
import Data.W as DW

open import ALMA.Base.MCorrSetoid using (SysEq; EqOn; idAdjˢ; propEqOn)
open import ALMA.Base.MCorrInitialAlgebra using
  (Wˣ; sup; _≈Wˢ_; ≈W-refl; ≈W-sym; ≈W-trans)

module _ {s p : Level} (S : Set s) (P : S → Set p) where

  private
    C : Container s p
    C = S ▷ P

  ----------------------------------------------------------------------
  -- Deterministic trivial-index edge family
  --
  -- One index, labels are shapes, edges are positions.
  --
  -- 确定性平凡索引边族
  --
  -- 唯一索引，标签为形状，边为位置。

  sys : SysEq lzero s p s p
  sys = record
    { I  = ⊤
    ; A  = λ { tt → S }
    ; E  = λ { tt a tt → P a }
    ; ≈A = λ { tt → propEqOn S }
    ; ≈E = λ { tt a tt → propEqOn (P a) }
    }

  -- The generic least fixpoint at the unique index.
  --
  -- 唯一索引处的泛型最小不动点。
  Wᶜ : Set (s ⊔ p)
  Wᶜ = Wˣ sys tt

  -- Native-looking node: a shape and one child per position.
  --
  -- 原生风格节点：一个形状与每个位置上的一个子节点。
  node : (a : S) → (P a → Wᶜ) → Wᶜ
  node a f = sup {x = tt} a λ { tt q → f q }

  head : Wᶜ → S
  head (sup {x = tt} a _) = a

  children : (w : Wᶜ) → P (head w) → Wᶜ
  children (sup {x = tt} _ k) q = k tt q

  ----------------------------------------------------------------------
  -- Definitional seam with Data.W
  --
  -- 与 Data.W 的定义性接缝

  toW : Wᶜ → DW.W C
  toW (sup {x = tt} a k) = DW.sup (a , λ q → toW (k tt q))

  fromW : DW.W C → Wᶜ
  fromW (DW.sup (a , f)) = node a λ q → fromW (f q)

  -- Finite bisimulation on the carried W, specialised to the container.
  --
  -- 携带式 W 上的有限互模拟，特化到容器。
  _≈Wᶜ_ : Wᶜ → Wᶜ → Set (s ⊔ p)
  _≈Wᶜ_ = _≈Wˢ_ sys

  -- The native W inherits the finite bisimulation along fromW.
  --
  -- 原生 W 沿 fromW 继承有限互模拟。
  _≈Wⁿ_ : DW.W C → DW.W C → Set (s ⊔ p)
  w ≈Wⁿ w' = fromW w ≈Wᶜ fromW w'

  eqWⁿ : EqOn {ℓ = s ⊔ p} (DW.W C)
  eqWⁿ = record
    { _≈_ = _≈Wⁿ_
    ; isEquivalence = record
      { refl  = λ {w} → ≈W-refl sys (fromW w)
      ; sym   = λ q → ≈W-sym sys q
      ; trans = λ q r → ≈W-trans sys q r
      }
    }

  ----------------------------------------------------------------------
  -- Round trips and respect
  --
  -- fromW-toW is structural recursion on the carried W: at a node the
  -- labels coincide and every position carries the induction hypothesis
  -- through the identity edge adjunction. No function extensionality,
  -- since the per-position proofs are data of the bisimulation. The
  -- other direction is inherited on the native W, and both maps respect
  -- the carried setoids.
  --
  -- 往返与保持
  --
  -- fromW-toW 对携带式 W 结构递归：节点处标签重合，每个位置经恒等边
  -- 携带归纳假设。无需函数外延性，因逐位置见证是互模拟的数据。另一
  -- 方向在原生 W 上继承；两个映射均保持携带 setoid。

  fromW-toW : (w : Wᶜ) → fromW (toW w) ≈Wᶜ w
  fromW-toW (sup {x = tt} a k) =
      refl
    , λ { tt → idAdjˢ (propEqOn (P a))
            , ( (λ q → fromW-toW (k tt q))
              , (λ q → ≈W-sym sys (fromW-toW (k tt q))) ) }

  toW-fromW : (w : DW.W C) → toW (fromW w) ≈Wⁿ w
  toW-fromW w = fromW-toW (fromW w)

  toW-resp : ∀ {w w' : Wᶜ} → w ≈Wᶜ w'
           → toW w ≈Wⁿ toW w'
  toW-resp {w = w} {w' = w'} q =
    ≈W-trans sys (fromW-toW w)
      (≈W-trans sys q (≈W-sym sys (fromW-toW w')))

  fromW-resp : ∀ {w w' : DW.W C} → w ≈Wⁿ w'
             → fromW w ≈Wᶜ fromW w'
  fromW-resp q = q
