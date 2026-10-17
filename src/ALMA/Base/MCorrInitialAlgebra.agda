------------------------------------------------------------------------
-- Generic carried initial algebra for an arbitrary setoid edge family
--
-- The least fixpoint of the indexed edge-family functor
--   F X i = Σ (A i) λ a → (j : I) (e : E i a j) → X j
-- is the indexed W-type Wˣ of finite (well-founded) trees: every node
-- carries a label and an edge-indexed family of children, and
-- well-foundedness makes every tree finite. Structural recursion gives
-- the catamorphism; the finite bisimulation _≈Wˢ_ gives the equality at
-- which folds are unique once the target is a setoid algebra. Nothing
-- matches an equality: the edge witness e is carried as data.
--
-- Wˣ is the inductive dual of the coinductive Mˣ in MCorrSetoidCoalg,
-- and embed : Wˣ → Mˣ is the finite-tree inclusion μF → νF. Because
-- every F-layer exposes its children as data, μF is the colimit of the
-- finite approximants Fⁿ0 reached at ω; the W-type carries that
-- colimit directly (each tree has finite depth), so no separate chain
-- of quotients is introduced here.
--
-- 任意 setoid 边族的泛型携带式初始代数
--
-- 索引边族函子
--   F X i = Σ (A i) λ a → (j : I) (e : E i a j) → X j
-- 的最小不动点是有限（良基）树的索引 W 型 Wˣ：每个节点携带一个标签与
-- 一个边索引的子节点族，良基性使每棵树有限。结构递归给出 catamorphism；
-- 有限互模拟 _≈Wˢ_ 给出“目标为 setoid 代数时折叠唯一”所处的相等。此处
-- 不匹配任何等式：边见证 e 作为数据携带。
--
-- Wˣ 是 MCorrSetoidCoalg 中余归纳 Mˣ 的归纳对偶，embed : Wˣ → Mˣ 即
-- 有限树嵌入（μF → νF）。由于每个 F 层都把子节点作为数据暴露，μF 即
-- 有限近似 Fⁿ0 在 ω 处达到的余极限；W 型直接承载该余极限（每棵树深度
-- 有限），故此处不再另建一条商链。
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module ALMA.Base.MCorrInitialAlgebra where

open import Agda.Primitive using (Level; lsuc; _⊔_)
open import Agda.Builtin.Sigma using (Σ; _,_)
open import Data.Product.Base using (_×_)

open import ALMA.Base.MCorr using (M)
open import ALMA.Base.MCorrSetoid using
  (SysEq; EqOn; FiberAdjˢ; idAdjˢ; symAdjˢ; compAdjˢ; _≈Mˢ_; ≈Mˢ-sym)
open FiberAdjˢ
open _≈Mˢ_ public

module _ {i a b ℓa ℓe : Level} (X : SysEq i a b ℓa ℓe) where

  open SysEq X

  private
    ℓw  = i ⊔ a ⊔ b
    ℓeq = i ⊔ a ⊔ b ⊔ ℓa ⊔ ℓe

  ----------------------------------------------------------------------
  -- Finite edge-indexed trees
  --
  -- The least fixpoint μF. The sole constructor sup is a node: a label
  -- plus, for every target index and edge out of that label, a finite
  -- child tree.
  --
  -- 有限边索引树
  --
  -- 最小不动点 μF。唯一构造子 sup 是一个节点：一个标签，以及对每个目标
  -- 索引和该标签下每条边的一棵有限子树。
  data Wˣ : I → Set ℓw where
    sup : ∀ {x : I} (a : A x)
          (k : (y : I) (e : E x a y) → Wˣ y) → Wˣ x

  -- The one-step algebra: at index x, a label and already-evaluated
  -- child values combine into a value.
  --
  -- 一步代数：在索引 x，一个标签与已求值的子值组合为一个值。
  record Algebra (u : Level) (Xst : I → Set u)
         : Set (i ⊔ u ⊔ a ⊔ b) where
    field
      alg : (x : I) (a : A x)
            (k : (y : I) (e : E x a y) → Xst y) → Xst x
  open Algebra public

  -- Catamorphism: structural recursion on the finite tree. The only
  -- recursive call is on the structurally smaller child k y e.
  --
  -- Catamorphism：对有限树结构递归。唯一递归调用作用于结构上更小的
  -- 子节点 k y e。
  cata : ∀ {u : Level} {Xst : I → Set u}
         (φ : Algebra u Xst) → ∀ {x : I} → Wˣ x → Xst x
  cata φ (sup {x = x} a k) =
    alg φ x a λ y e → cata φ (k y e)

  -- Finite-tree inclusion μF → νF. Productive: the head is immediate
  -- and every recursive call is guarded under M.below.
  --
  -- 有限树嵌入 μF → νF。受保护产出：头部立得，每个递归调用受守护于
  -- M.below 之下。
  embed : ∀ {x : I} → Wˣ x → M A E x
  embed (sup a k) .M.here      = a
  embed (sup a k) .M.below y e = embed (k y e)

  ----------------------------------------------------------------------
  -- Finite bisimulation
  --
  -- Inductive dual of the carried M-bisimulation: equal labels and, per
  -- target index, an edge adjunction relating the finite children in
  -- both directions. Defined by recursion on the finite trees rather
  -- than as an indexed datatype.
  --
  -- 有限互模拟
  --
  -- 携带式 M-互模拟的归纳对偶：标签相等，且每个目标索引有一根边伴随
  -- 双向关联有限子树。按有限树递归定义，而非索引归纳数据类型。
  _≈Wˢ_ : ∀ {x : I} → Wˣ x → Wˣ x → Set ℓeq
  _≈Wˢ_ {x = x} (sup a k) (sup a' k') =
      EqOn._≈_ (≈A x) a a'
    × ((y : I)
       → Σ (FiberAdjˢ (≈E x a' y) (≈E x a y)) λ adj
       → (∀ (e  : E x a  y) → _≈Wˢ_ (k y e)  (k' y (to adj e)))
       × (∀ (e' : E x a' y) → _≈Wˢ_ (k' y e') (k y (fro adj e'))))

  ≈W-refl : ∀ {x : I} (w : Wˣ x) → w ≈Wˢ w
  ≈W-refl (sup a k) =
      EqOn.refl (≈A _)
    , λ y → idAdjˢ (≈E _ a y)
      , ( (λ e  → ≈W-refl (k y e))
        , (λ e' → ≈W-refl (k y e')) )

  ≈W-sym : ∀ {x : I} {w w' : Wˣ x} → w ≈Wˢ w' → w' ≈Wˢ w
  ≈W-sym {x = x} {sup a k} {sup a' k'} (ha , body) =
      EqOn.sym (≈A x) ha
    , λ y →
        let adj , fwd , bwd = body y
        in symAdjˢ adj , (bwd , fwd)

  ≈W-trans : ∀ {x : I} {u v w : Wˣ x}
           → u ≈Wˢ v → v ≈Wˢ w → u ≈Wˢ w
  ≈W-trans {x = x} {sup a k} {sup a' k'} {sup a'' k''}
           (ha₁ , b₁) (ha₂ , b₂) =
      EqOn.trans (≈A x) ha₁ ha₂
    , λ y →
        let adj₁ , f1 , b1c = b₁ y
            adj₂ , f2 , b2c = b₂ y
            adj = compAdjˢ (≈E x a y) (≈E x a' y) (≈E x a'' y)
                            adj₁ adj₂
        in adj
         , ( (λ e   → ≈W-trans (f1 e) (f2 (to adj₁ e)))
           , (λ e'' → ≈W-trans (b2c e'') (b1c (fro adj₂ e''))) )

  -- Embedding reflects the finite bisimulation into the coinductive
  -- one: finitely bisimilar trees embed to bisimilar M-trees. Productive,
  -- with every recursive call guarded under below-eq.
  --
  -- 嵌入把有限互模拟映为余归纳互模拟：有限互模拟的树嵌入后为互模拟的
  -- M-树。受保护产出，每个递归调用受守护于 below-eq 之下。
  embed-≈W : ∀ {x : I} {w w' : Wˣ x} → w ≈Wˢ w'
           → _≈Mˢ_ ≈A ≈E (embed w) (embed w')
  embed-≈W {x = x} {sup a k} {sup a' k'} (ha , body) .here-eq = ha
  embed-≈W {x = x} {sup a k} {sup a' k'} (ha , body) .below-eq y =
      let adj , fwd , bwd = body y
      in adj , ((λ e → embed-≈W (fwd e)) , (λ e' → embed-≈W (bwd e')))

  -- Reflection: two finite trees whose embeddings are bisimilar are
  -- finitely bisimilar. Only the finite depth of the first tree is
  -- inspected; at each node the coinductive witness supplies the label
  -- equation and one edge adjunction, and recursion is structural in
  -- both trees (the backward component flips via ≈W-sym / ≈Mˢ-sym so
  -- the arguments never swap positions).
  --
  -- 反射：嵌入后互模拟的两棵有限树本身有限互模拟。只需检视第一棵树的
  -- 有限深度；每个节点处余归纳见证给出标签等式与一根边伴随，递归对两棵
  -- 树都结构递减（反向分量经 ≈W-sym / ≈Mˢ-sym 翻转，参数位置不交换）。
  embed-inj : ∀ {x : I} (w w' : Wˣ x)
            → _≈Mˢ_ ≈A ≈E (embed w) (embed w') → w ≈Wˢ w'
  embed-inj (sup a k) (sup a' k') p =
      here-eq p
    , λ y →
        let adj , fwd , bwd = below-eq p y
        in adj
         , ( (λ e  → embed-inj (k y e) (k' y (to adj e)) (fwd e))
           , (λ e' → ≈W-sym
                       (embed-inj (k y (fro adj e')) (k' y e')
                        (≈Mˢ-sym ≈A ≈E (bwd e')))) )

  ----------------------------------------------------------------------
  -- Setoid algebra and initiality up to the carrier setoid
  --
  -- A setoid algebra equips its carrier with an EqOn and its one-step
  -- evaluator with congruence: related labels and pointwise-related
  -- children (children related along a carried edge adjunction) give
  -- related results. The fold is then well-defined on the finite
  -- bisimulation, which is initiality at the setoid level (the _≡_
  -- version would compare child functions pointwise and need funExt,
  -- not assumed).
  --
  -- setoid 代数与到载体 setoid 的初始性
  --
  -- setoid 代数为载体配备 EqOn，为一步求值器配备同余：相关的标签与逐点
  -- 相关的子节点（子节点沿携带的边伴随相关）给出相关结果。于是折叠在有限
  -- 互模拟上良定，这即 setoid 层的初始性（_≡_ 版需逐点比较子函数、因而
  -- 需要 funExt，此处不假设）。
  record SetoidAlgebra (u ℓx : Level) (Xst : I → Set u)
         : Set (i ⊔ a ⊔ b ⊔ ℓa ⊔ ℓe ⊔ lsuc u ⊔ lsuc ℓx) where
    field
      eqX : (x : I) → EqOn {ℓ = ℓx} (Xst x)
      sAlg : (x : I) (a : A x)
             (k : (y : I) (e : E x a y) → Xst y) → Xst x
      sAlg-cong :
          (x : I) {a a' : A x} (ha : EqOn._≈_ (≈A x) a a')
          (k  : (y : I) (e  : E x a  y) → Xst y)
          (k' : (y : I) (e' : E x a' y) → Xst y)
        → ((y : I)
           → Σ (FiberAdjˢ (≈E x a' y) (≈E x a y)) λ adj
             → ∀ (e : E x a y)
             → EqOn._≈_ (eqX y) (k y e) (k' y (to adj e)))
        → EqOn._≈_ (eqX x) (sAlg x a k) (sAlg x a' k')
  open SetoidAlgebra public

  cataS : ∀ {u ℓx : Level} {Xst : I → Set u}
          (φ : SetoidAlgebra u ℓx Xst)
        → ∀ {x : I} → Wˣ x → Xst x
  cataS φ (sup {x = x} a k) =
    sAlg φ x a λ y e → cataS φ (k y e)

  -- The fold sends finitely bisimilar trees to carrier-related values.
  -- Structural recursion on the (inductive) finite-bisimulation witness.
  --
  -- 折叠把有限互模拟的树映为载体中相关的值。对（归纳的）有限互模拟见证
  -- 结构递归。
  cata-≈W : ∀ {u ℓx : Level} {Xst : I → Set u}
            (φ : SetoidAlgebra u ℓx Xst)
          → ∀ {x : I} {w w' : Wˣ x} → w ≈Wˢ w'
          → EqOn._≈_ (eqX φ x) (cataS φ w) (cataS φ w')
  cata-≈W φ {x = x} {sup a k} {sup a' k'} (ha , body) =
    sAlg-cong φ x ha
      (λ y e  → cataS φ (k y e))
      (λ y e' → cataS φ (k' y e'))
      λ y →
        let adj , fwd , _ = body y
        in adj , λ e → cata-≈W φ (fwd e)
