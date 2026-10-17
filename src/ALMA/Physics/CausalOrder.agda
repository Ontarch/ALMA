------------------------------------------------------------------------
-- Emergent causal spacetime from an edge family
--
-- The M layer carries no time, space, metric or causal-order field:
-- all of these are read off the directed edge family E. This module
-- makes that reading explicit in pure order-theoretic, constructive
-- terms: causal reachability, acyclicity (the time arrow), spacelike
-- separation and slices, and finite-tree occurrence. Nothing here
-- eliminates an equality; paths carry their labels and edges as data.
--
-- 从边族涌现的因果时空
--
-- 时间、空间、度规、因果序都不是 M 的字段，全部从有向边族 E 读出。
-- 本模块以纯序论、构造性方式把这一“读出”显式化：因果可达、无环
-- （时间箭头）、类空分离与切片、有限树出现。此处不消去任何等式；
-- 路径把标签与边作为数据携带。
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module ALMA.Physics.CausalOrder where

open import Agda.Primitive using (Level; _⊔_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Sigma using (Σ; _,_)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Product.Base using (_×_)
open import Relation.Nullary.Negation using (¬_)

open import ALMA.Base.MCorrSetoid using (SysEq)
open import ALMA.Base.MCorrInitialAlgebra using (Wˣ; sup)

module _ {i a b ℓa ℓe : Level} (X : SysEq i a b ℓa ℓe) where

  open SysEq X

  private
    ℓord = i ⊔ a ⊔ b

  ----------------------------------------------------------------------
  -- Causal reachability
  --
  -- here is the zero-length path; there prepends one labelled edge. The
  -- label a is carried because E depends on it.
  --
  -- 因果可达
  --
  -- here 为零长路径；there 前置一条带标签的边。标签 a 被携带，因 E
  -- 依赖于它。
  data _⇝_ : I → I → Set ℓord where
    here  : ∀ {x : I} → x ⇝ x
    there : ∀ {x y z : I} (a : A x) (e : E x a y) → y ⇝ z → x ⇝ z

  -- Positive (non-empty) reachability: strict causal precedence.
  --
  -- 正（非空）可达：严格因果在先。
  data _⇝⁺_ : I → I → Set ℓord where
    step : ∀ {x y : I} (a : A x) (e : E x a y) → x ⇝⁺ y
    more : ∀ {x y z : I} (a : A x) (e : E x a y) → y ⇝⁺ z → x ⇝⁺ z

  -- A single edge is a one-step path.
  --
  -- 单边即一步路径。
  edge : ∀ {x y : I} (a : A x) (e : E x a y) → x ⇝ y
  edge a e = there a e here

  pos⁺ : ∀ {x y : I} → x ⇝⁺ y → x ⇝ y
  pos⁺ (step a e)   = there a e here
  pos⁺ (more a e p) = there a e (pos⁺ p)

  -- Path concatenation in both orders.
  --
  -- 两种序的路径拼接。
  ⇝-trans : ∀ {x y z : I} → x ⇝ y → y ⇝ z → x ⇝ z
  ⇝-trans here        q = q
  ⇝-trans (there a e p) q = there a e (⇝-trans p q)

  ⇝⁺-trans : ∀ {x y z : I} → x ⇝⁺ y → y ⇝⁺ z → x ⇝⁺ z
  ⇝⁺-trans (step a e)   q = more a e q
  ⇝⁺-trans (more a e p) q = more a e (⇝⁺-trans p q)

  ----------------------------------------------------------------------
  -- Time arrow
  --
  -- Acyclicity is the carried hypothesis that no positive path returns
  -- to its source; it makes strict precedence asymmetric, i.e. the
  -- directed order is irreversible. M does not guarantee it (an edge
  -- may point back), so irreversibility is a hypothesis, not a free
  -- theorem.
  --
  -- 时间箭头
  --
  -- 无环是携带假设：没有正路径回到其源；它使严格在先不对称，即有向序
  -- 不可逆。M 不保证无环（边可指回），故不可逆是假设而非免费定理。
  Acyclic : Set ℓord
  Acyclic = ∀ {x : I} → ¬ (x ⇝⁺ x)

  arrow-asym : Acyclic → ∀ {x y : I}
             → x ⇝⁺ y → ¬ (y ⇝⁺ x)
  arrow-asym ac p q = ac (⇝⁺-trans p q)

  ----------------------------------------------------------------------
  -- Spatial reading
  --
  -- Two indices are spacelike separated when neither positively precedes
  -- the other; an antichain (a cognitive / spatial slice) is a family
  -- that is pairwise spacelike. The uniform depth-n truncation Tr n in
  -- MCorrTerminalSequence is the corresponding graded section and is
  -- not rebuilt here.
  --
  -- 空间读法
  --
  -- 两个索引互不正在先则类空分离；反链（认知/空间切片）即逐对类空的
  -- 族。MCorrTerminalSequence 中均匀深度 n 截断 Tr n 是相应的分级
  -- 截面，此处不重建。
  _∥_ : I → I → Set ℓord
  x ∥ y = ¬ (x ⇝⁺ y) × ¬ (y ⇝⁺ x)

  Antichain : ∀ {ℓ : Level} (P : I → Set ℓ) → Set (ℓord ⊔ ℓ)
  Antichain P = ∀ {x y : I} → P x → P y → x ∥ y

  -- Under acyclicity every index is spacelike related to itself, so a
  -- one-point slice is admissible.
  --
  -- 无环下每个索引与自身类空相关，故单点切片可取。
  self-spacelike : Acyclic → ∀ (x : I) → x ∥ x
  self-spacelike ac x = ac , ac

  ----------------------------------------------------------------------
  -- Finite-tree occurrence
  --
  -- Reach w y says y occurs in the finite tree w: either it is the
  -- root, or it is reached through one child edge and then occurs in
  -- that child. Defined by recursion on the finite tree (no
  -- indexed-by-tree datatype, so no constructor injectivity is needed).
  -- Wˣ is the well-founded / finite-causal-past unfolding; the
  -- coinductive M admits infinite descent, so inductive occurrence is
  -- only available for Wˣ.
  --
  -- 有限树出现
  --
  -- Reach w y 表示 y 出现在有限树 w 中：或为根，或经一条子边到达并出现
  -- 在该子树中。按有限树递归定义（不用以树为索引的数据类型，故无需构造
  -- 子注入性）。Wˣ 是良基/有限因果过去的展开；余归纳 M 允许无穷下降，
  -- 故归纳的出现关系仅对 Wˣ 可用。
  Reach : ∀ {x : I} → Wˣ X x → I → Set ℓord
  Reach (sup {x = x} a k) y =
        (x ≡ y)
      ⊎ (Σ I λ z → Σ (E x a z) λ e → Reach (k z e) y)

  Reach→⇝ : ∀ {x y : I} {w : Wˣ X x} → Reach w y → x ⇝ y
  Reach→⇝ {x = x} {w = sup a k} (inj₁ refl)      = here
  Reach→⇝ {x = x} {w = sup a k} (inj₂ (z , (e , m))) =
    there a e (Reach→⇝ m)

  -- The root occurs in its own tree.
  --
  -- 根出现在自身树中。
  root-Reach : ∀ {x : I} (w : Wˣ X x) → Reach w x
  root-Reach (sup a k) = inj₁ refl

  -- The target of every child edge occurs in the node's tree.
  --
  -- 每条子边的目标都出现在该节点的树中。
  child-Reach : ∀ {x y : I} {a : A x}
                {k : (z : I) (e : E x a z) → Wˣ X z}
              → (e : E x a y) → Reach (sup {x = x} a k) y
  child-Reach {x = x} {y = y} {a = a} {k = k} e =
    inj₂ (y , (e , root-Reach (k y e)))
