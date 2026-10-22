------------------------------------------------------------------------
-- Forward edge-following simulations over setoid systems
--
-- setoid 系统上的前向边跟随模拟
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module Base.MCorr.SetoidPush where

open import Agda.Primitive using (Level; _⊔_)
open import Agda.Builtin.Sigma using (Σ; _,_)
open import Agda.Builtin.Equality using (_≡_; refl)

open import Base.MCorr using (M)
open import Base.MCorr.Setoid using (SysEq; EqOn)
open SysEq

------------------------------------------------------------------------
-- Forward simulation over index layer R with cross-system label
-- correspondence H
--
-- Stepˢ / Morphˢ in MCorrSetoid are pull notions: a step gives a
-- canonical source child for every target child. A direct-colimit leg
-- points the other way, from a finite stage into the limit, and is not
-- child-surjective (see ColimitPolarity). PushSimˢ is the forward dual
-- carried as a relation between two existing trees: for each source
-- edge it carries a target edge, a fresh index-layer witness and the
-- child simulation, with no totality over target indices and no edge
-- round-trip. The label correspondence H is a parameter, so the
-- relation stays honest when labels of the two systems differ in type.
-- push is one-way: source edges only.
--
-- 索引层 R 上、具跨系统标签对应 H 的前向模拟
--
-- Stepˢ / Morphˢ 是 pull 概念：一步对每个目标子节点给出规范源子节点。
-- 直接余极限腿方向相反，从有限层指向极限，且不满足子节点满。
-- PushSimˢ 是作为两棵已存在树之间关系的前向对偶：对每条源边携带一条
-- 目标边、一条新索引层见证与子模拟，既不对目标索引求满，也无边上的
-- 往返。标签对应 H 作为参数，使两系统标签类型不同时关系依然诚实。
-- push 单向，只沿源边。

record PushSimˢ {i j a b c d ℓa ℓe ℓc ℓd ℓr ℓh : Level}
               (X : SysEq i a b ℓa ℓe)
               (Y : SysEq j c d ℓc ℓd)
               (R : I X → I Y → Set ℓr)
               (H : (x : I X) (v : I Y) (r : R x v)
                  → A X x → A Y v → Set ℓh)
               {x : I X} {v : I Y} (r : R x v)
               (t : M (A X) (E X) x)
               (u : M (A Y) (E Y) v)
       : Set (i ⊔ j ⊔ a ⊔ b ⊔ c ⊔ d ⊔ ℓr ⊔ ℓh)
       where
  coinductive
  field
    here-eq : H x v r (M.here t) (M.here u)
    push : (y : I X) (e : E X x (M.here t) y)
         → Σ (I Y) λ w
         → Σ (E Y v (M.here u) w) λ e'
         → Σ (R y w) λ r'
         → PushSimˢ X Y R H r' (M.below t y e) (M.below u w e')
open PushSimˢ public

------------------------------------------------------------------------
-- Identity forward simulation
--
-- The layer is propositional index equality and H is the carried label
-- equivalence of the system.
--
-- 恒等前向模拟
--
-- 索引层取命题相等，H 取系统携带的标签等价。

EqH : {i a b ℓa ℓe : Level} (X : SysEq i a b ℓa ℓe)
    → (x v : I X) → x ≡ v → A X x → A X v → Set ℓa
EqH X x .x refl a b = EqOn._≈_ (≈A X x) a b

push-refl : {i a b ℓa ℓe : Level} (X : SysEq i a b ℓa ℓe)
          → {x : I X} (t : M (A X) (E X) x)
          → PushSimˢ X X (λ (y z : I X) → y ≡ z) (EqH X) refl t t
push-refl X {x = x} t .here-eq = EqOn.refl (≈A X x)
push-refl X {x = x} t .push y e =
  y , e , refl , push-refl X (M.below t y e)
