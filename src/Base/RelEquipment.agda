------------------------------------------------------------------------
-- Proof-relevant relations as a proarrow equipment
--
-- 证明相关关系作为 proarrow equipment
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module Base.RelEquipment where

open import Agda.Primitive using (Level; lzero; _⊔_)
open import Agda.Builtin.Sigma using (Σ; _,_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Product.Base using (proj₁; proj₂; _×_)
open import Data.Unit.Polymorphic.Base using (⊤; tt)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality.Core using (cong)
open import Relation.Nullary.Negation using (¬_)

------------------------------------------------------------------------
-- Identity relation and Sigma composition through a middle
--
-- 恒等关系与经中项的 Σ 复合

IdR : ∀ {i : Level} {I : Set i} → I → I → Set i
IdR x y = x ≡ y

infixr 9 _∘ᵣ_
_∘ᵣ_ : ∀ {i j k ℓr ℓs : Level}
         {I : Set i} {J : Set j} {K : Set k}
       (R : I → J → Set ℓr) (S : J → K → Set ℓs)
     → I → K → Set (j ⊔ ℓr ⊔ ℓs)
_∘ᵣ_ {J = J} R S x z = Σ J λ y → R x y × S y z

------------------------------------------------------------------------
-- The equipment 2-cells
--
-- A type-valued relation R : I → J → Set r carries its witnesses, so
-- unit and associativity hold only up to canonical Sigma reassociation
-- bijections (the equipment 2-cells), which keep every witness and
-- need no UIP. A plain 1-category instead has one fixed hom per pair
-- of objects, so its composite must be independent of the middle;
-- this is conditional on fibre propositionality, which is not
-- logically necessary under --safe --cubical-compatible (the two
-- obstructions are the diamond and parallel witnesses below).
--
-- equipment 的 2-胞腔
--
-- 类型值关系 R : I → J → Set r 携带见证，故单位与结合只在典范
-- Σ-重结合双射（equipment 的 2-胞腔）意义下成立，这些双射保留全部
-- 见证，无需 UIP。普通 1-范畴对每对对象只有一个固定 hom，其复合必须
-- 与中项无关；这以纤维命题化为条件，而在
-- --safe --cubical-compatible 下该条件并非逻辑必然（两条障碍即下面
-- 的菱形与平行见证）。

module _ {i j ℓr : Level} {I : Set i} {J : Set j}
         (R : I → J → Set ℓr) where

  unit-l-fwd : ∀ {x z} → (IdR ∘ᵣ R) x z → R x z
  unit-l-fwd (x , refl , r) = r
  unit-l-bwd : ∀ {x z} → R x z → (IdR ∘ᵣ R) x z
  unit-l-bwd r = _ , refl , r

  unit-r-fwd : ∀ {x z} → (R ∘ᵣ IdR) x z → R x z
  unit-r-fwd (z , r , refl) = r
  unit-r-bwd : ∀ {z : J} {x} → R x z → (R ∘ᵣ IdR) x z
  unit-r-bwd {z = z} r = z , r , refl

  unit-l-fwd∘bwd : ∀ {x z} (r : R x z) → unit-l-fwd (unit-l-bwd r) ≡ r
  unit-l-fwd∘bwd r = refl
  unit-r-fwd∘bwd : ∀ {x z} (r : R x z) → unit-r-fwd (unit-r-bwd r) ≡ r
  unit-r-fwd∘bwd r = refl

module _ {i ℓr ℓs ℓt : Level}
         {I J K L : Set i}
         (R : I → J → Set ℓr)
         (S : J → K → Set ℓs)
         (T : K → L → Set ℓt) where

  assoc-fwd : ∀ {x w} → ((R ∘ᵣ S) ∘ᵣ T) x w → (R ∘ᵣ (S ∘ᵣ T)) x w
  assoc-fwd (z , (y , r , s) , t) = y , r , (z , s , t)
  assoc-bwd : ∀ {x w} → (R ∘ᵣ (S ∘ᵣ T)) x w → ((R ∘ᵣ S) ∘ᵣ T) x w
  assoc-bwd (y , r , (z , s , t)) = z , (y , r , s) , t

  assoc-fwd∘bwd : ∀ {x w} (q : (R ∘ᵣ (S ∘ᵣ T)) x w)
                → assoc-fwd (assoc-bwd q) ≡ q
  assoc-fwd∘bwd (y , r , (z , s , t)) = refl
  assoc-bwd∘fwd : ∀ {x w} (p : ((R ∘ᵣ S) ∘ᵣ T) x w)
                → assoc-bwd (assoc-fwd p) ≡ p
  assoc-bwd∘fwd (z , (y , r , s) , t) = refl

------------------------------------------------------------------------
-- Fibre propositionality
--
-- A subset hom needs every edge fibre to be a proposition.
--
-- 纤维命题化
--
-- 子集 hom 需要每条边纤维是命题。

IsProp : ∀ {ℓ : Level} → Set ℓ → Set ℓ
IsProp X = ∀ (x y : X) → x ≡ y

------------------------------------------------------------------------
-- Diamond obstruction
--
-- Two distinct middle indices fill the same edge 0 ─→ 3. A
-- propositional composite would identify the two Sigma witnesses,
-- forcing 1 ≡ 2, which is absurd.
--
-- 菱形障碍
--
-- 两个不同中项填补同一条边 0 ─→ 3。命题化复合会等同两个 Σ 见证，
-- 迫使 1 ≡ 2，矛盾。

private
  -- Four-node shape 0 ─→ 1 ─→ 3 and 0 ─→ 2 ─→ 3.
  --
  -- 四节点形状 0 ─→ 1 ─→ 3 与 0 ─→ 2 ─→ 3。
  data D4 : Set where
    n0 n1 n2 n3 : D4

  R◇ : D4 → D4 → Set lzero
  R◇ n0 n0 = ⊥
  R◇ n0 n1 = ⊤
  R◇ n0 n2 = ⊤
  R◇ n0 n3 = ⊥
  R◇ n1 _  = ⊥
  R◇ n2 _  = ⊥
  R◇ n3 _  = ⊥

  S◇ : D4 → D4 → Set lzero
  S◇ n0 _  = ⊥
  S◇ n1 n0 = ⊥
  S◇ n1 n1 = ⊥
  S◇ n1 n2 = ⊥
  S◇ n1 n3 = ⊤
  S◇ n2 n0 = ⊥
  S◇ n2 n1 = ⊥
  S◇ n2 n2 = ⊥
  S◇ n2 n3 = ⊤
  S◇ n3 _  = ⊥

  w◇₁ : (R◇ ∘ᵣ S◇) n0 n3
  w◇₁ = n1 , tt , tt
  w◇₂ : (R◇ ∘ᵣ S◇) n0 n3
  w◇₂ = n2 , tt , tt

  ¬1≡2 : ¬ (n1 ≡ n2)
  ¬1≡2 ()

-- If the composite edge fibre were a proposition, the two distinct
-- middles would coincide, a contradiction.
--
-- 若复合边纤维为命题，两个不同中项将重合，矛盾。
strict-1cat-diamond→⊥ : IsProp ((R◇ ∘ᵣ S◇) n0 n3) → ⊥
strict-1cat-diamond→⊥ prop =
  ¬1≡2 (cong proj₁ (prop w◇₁ w◇₂))

------------------------------------------------------------------------
-- Parallel-witness obstruction
--
-- With a single object (hence a unique middle) and an arbitrary edge
-- fibre P, a propositional composite P × P forces any two inhabitants
-- of P to coincide, i.e. UIP for P.
--
-- 平行见证障碍
--
-- 单一对象（故中项唯一）而边纤维为任意 P 时，命题化复合 P × P 迫使
-- P 的任意两个居民重合，即 P 的 UIP。

module _ {ℓ : Level} (P : Set ℓ) where

  private
    RP : ⊤ {ℓ} → ⊤ {ℓ} → Set ℓ
    RP tt tt = P

    wP : P → P → (RP ∘ᵣ RP) tt tt
    wP p q = tt , p , q

  strict-1cat→fibre-prop
    : IsProp ((RP ∘ᵣ RP) tt tt) → IsProp P
  strict-1cat→fibre-prop prop a b =
    cong proj₂ (cong proj₂ (prop (wP a a) (wP a b)))
