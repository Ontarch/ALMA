------------------------------------------------------------------------
-- Witness rescoping for forward edge-following simulations
--
-- 前向边跟随模拟的见证重定域
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module Base.MCorr.SetoidPushMap where

open import Agda.Primitive using (Level)
open import Agda.Builtin.Sigma using (_,_)

open import Base.MCorr using (M)
open import Base.MCorr.Setoid using (SysEq)
open SysEq
open import Base.MCorr.SetoidPush using (PushSimˢ)

module _ {i j a b c d ℓa ℓe ℓc ℓd ℓr ℓr' ℓh ℓh' : Level}
         {X : SysEq i a b ℓa ℓe}
         {Y : SysEq j c d ℓc ℓd}
         (R  : I X → I Y → Set ℓr)
         (R' : I X → I Y → Set ℓr')
         (H  : (x : I X) (v : I Y) (r : R x v)
             → A X x → A Y v → Set ℓh)
         (H' : (x : I X) (v : I Y) (r' : R' x v)
             → A X x → A Y v → Set ℓh')
         (fR : ∀ {x v} → R x v → R' x v)
         (fH : ∀ {x v} (r : R x v) {a : A X x} {b : A Y v}
             → H x v r a b → H' x v (fR r) a b)
         where

  -- A PushSimˢ over R and H is pushed to one over R' and H' by pure
  -- functions: fR relabels the layer witness and fH relabels each label
  -- witness. This is the function-passing combinator that aligns a
  -- composite cocone leg (whose layer witness is a Sigma) with a direct
  -- leg (whose witness is a projection).
  --
  -- 层关系 R、标签对应 H 上的 PushSimˢ 经纯函数推到 R'、H'：fR 重标
  -- 层见证，fH 重标每个标签见证。这是把复合余锥腿（层见证为 Σ）与直接
  -- 腿（见证为投影）对齐的函数传递组合子。
  push-map : ∀ {x : I X} {v : I Y} {r : R x v}
               {t : M (A X) (E X) x}
               {u : M (A Y) (E Y) v}
           → PushSimˢ X Y R H r t u
           → PushSimˢ X Y R' H' (fR r) t u
  push-map p .PushSimˢ.here-eq = fH _ (PushSimˢ.here-eq p)
  push-map p .PushSimˢ.push y e
    with PushSimˢ.push p y e
  ... | w , e' , r₁ , q =
    w , e' , fR r₁ , push-map q
