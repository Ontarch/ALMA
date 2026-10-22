------------------------------------------------------------------------
-- Composition of forward edge-following simulations
--
-- 前向边跟随模拟的复合
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module Base.MCorr.SetoidPushComp where

open import Agda.Primitive using (Level; _⊔_)
open import Agda.Builtin.Sigma using (Σ; _,_)
open import Data.Product.Base using (_×_)

open import Base.MCorr using (M; _⍮_)
open import Base.MCorr.Setoid using (SysEq)
open SysEq
open import Base.MCorr.SetoidPush using (PushSimˢ)

------------------------------------------------------------------------
-- Composite layer and label relations through the middle system Y
--
-- 经中间系统 Y 的复合层关系与标签对应

module _ {i j k a b c d e f ℓa ℓe ℓc ℓd ℓf ℓe3 ℓr ℓs ℓh ℓg : Level}
         {X : SysEq i a b ℓa ℓe}
         {Y : SysEq j c d ℓc ℓd}
         {Z : SysEq k e f ℓf ℓe3}
         (R : I X → I Y → Set ℓr)
         (S : I Y → I Z → Set ℓs)
         (H : (x : I X) (v : I Y) (r : R x v)
            → A X x → A Y v → Set ℓh)
         (G : (v : I Y) (z : I Z) (s : S v z)
            → A Y v → A Z z → Set ℓg)
         where

  -- Composite label correspondence: a middle label mediates the two
  -- cross-system label relations.
  --
  -- 复合标签对应：一个中间标签居间连接两个跨系统标签关系。
  H∘G : (x : I X) (z : I Z) (w : (R ⍮ S) x z)
      → A X x → A Z z → Set (c ⊔ ℓh ⊔ ℓg)
  H∘G x z (v , r , s) a c =
    Σ (A Y v) λ b → H x v r a b × G v z s b c

  -- Relational composition of forward simulations.
  --
  -- 前向模拟的关系复合。
  push-comp : ∀ {x : I X} {v : I Y} {z : I Z}
                {r : R x v} {s : S v z}
                {t : M (A X) (E X) x}
                {u : M (A Y) (E Y) v}
                {w : M (A Z) (E Z) z}
            → PushSimˢ X Y R H r t u
            → PushSimˢ Y Z S G s u w
            → PushSimˢ X Z (R ⍮ S) H∘G (v , r , s) t w
  push-comp {u = u} p q .PushSimˢ.here-eq =
    M.here u , PushSimˢ.here-eq p , PushSimˢ.here-eq q
  push-comp p q .PushSimˢ.push y e =
    let v' , eY , r' , p' = PushSimˢ.push p y e
        z' , eZ , s' , q' = PushSimˢ.push q v' eY
    in z' , eZ , (v' , r' , s') , push-comp p' q'
