------------------------------------------------------------------------
-- Degeneration lattice
--
-- The degeneration lattice of LayeredEqGen. LayeredEqGen has two
-- fields: fst (the layer) and snd (the recursion); keeping or dropping
-- them spans a two-axis parameter space. The records are related by
-- projections, not inclusions: no canonical map back exists in general.
--
-- 退化格
--
-- LayeredEqGen 的退化格。LayeredEqGen 有两个字段：fst（当前层）与
-- snd（递归）；保留或去掉它们张成一个两轴参数空间。记录之间由投影
-- 联系，而非包含：一般不存在反向的典范映射。
--
--                    keep next
--                        ↑
--       ScaleInvariant   |   LayeredEqGen
--                        |
--   drop layer ←---------+---------→ keep layer
--                        |
--                        |   DiscreteEq
--                        ↓
--                    drop next
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module Equivalence.Lattice where

open import Data.Product.Base using (_×_; _,_)
open import Data.Unit.Polymorphic.Base using (tt)

open import Base.IndexedMType using (fst; snd)
open import Equivalence.Core using (LayeredEqGen)
open import Equivalence.DiscreteEq using (DiscreteEq)
open import Equivalence.ScaleInvariant using (ScaleInvariant)

------------------------------------------------------------------------
-- Projections
--
-- toScale replaces layer by the trivial layer ⊤ and keeps the
-- recursion; toDiscrete drops the recursion and keeps the layer.
--
-- toScale 把 layer 替换为平凡层 ⊤、保留递归；toDiscrete 去掉递归、
-- 保留 layer。

module Projections
    {a b c} {X : Set a} {Obs : Set b}
    (step : X → Obs → X)
    (layer : X → X → Set c)
  where

  -- Constant observation family, so obs-map is constantly the identity.
  --
  -- 观察族为常数，故 obs-map 恒为恒等。
  obs-map : (x y : X) → layer x y → Obs → Obs
  obs-map _ _ _ o = o

  toScale : ∀ {x y} → LayeredEqGen (λ _ → Obs) (λ x s → step x s)
                                   layer obs-map x y
          → ScaleInvariant step x y
  toScale p .fst = tt
  toScale p .snd s = toScale (p .snd s)

  toDiscrete : ∀ {x y} → LayeredEqGen (λ _ → Obs) (λ x s → step x s)
                                      layer obs-map x y
             → DiscreteEq layer x y
  toDiscrete p = p .fst

------------------------------------------------------------------------
-- Pair
--
-- Since fst and snd are the only two fields of LayeredEqGen, the pair
-- of projections retains the full field content. The converse is not
-- definable in general: DiscreteEq carries only the current layer, with
-- no evidence that layer is preserved by step.
--
-- fst 与 snd 是 LayeredEqGen 仅有的两个字段，故投影对保留全部字段
-- 内容。反向一般不成立：DiscreteEq 只携带当前层证据，不提供
-- “layer 在 step 下保持”的证据。

module Pair
    {a b c} {X : Set a} {Obs : Set b}
    (step : X → Obs → X)
    (layer : X → X → Set c)
  where

  open Projections step layer

  toPair : ∀ {x y} → LayeredEqGen (λ _ → Obs) (λ x s → step x s)
                                  layer obs-map x y
         → ScaleInvariant step x y × DiscreteEq layer x y
  toPair p = toScale p , toDiscrete p
