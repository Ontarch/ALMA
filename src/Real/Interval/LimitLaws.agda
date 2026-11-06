------------------------------------------------------------------------
-- Limit laws for convergent interval sequences
--
-- 收敛区间序列的极限运算律
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module Real.Interval.LimitLaws where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat using (ℕ; suc; _≥_; _⊔_; s≤s) renaming (_≤_ to _≤ℕ_)
open import Data.Nat.Properties using (m≤m⊔n; m≤n⊔m)
open import Data.Product using (_,_)
open import Data.Rational using (0ℚ; _+_; _-_; _*_; _<_; _≤_; ∣_∣)
  renaming (-_ to neg)
open import Data.Rational.Base using (positive)
open import Data.Rational.Properties using
  (≤-refl; ≤-trans; ≤-<-trans; <-trans; <-irrefl; +-mono-<; +-inverseʳ
  ; 0≤p⇒∣p∣≡p; <⇒≤; pos*pos⇒pos; +-monoʳ-<; +-assoc; +-comm; positive⁻¹
  ; module ≤-Reasoning)
open ≤-Reasoning renaming (begin_ to begin≤_; _∎ to _≤∎)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; sym; trans; cong; cong₂; subst; subst₂)
open import Relation.Nullary using (¬_)

open import Real using (ε; 0<ε; half; embed; embed-mono-≤; embed-suc-pos)
open import Real.Interval using (RealI)
open import Real.IntervalEquiv using (centre; l; u; centre-l; centre-u)
open import Real.Interval.Arith using (negℝ)
open import Real.Interval.Complete using (_⟶_)
open import Real.Interval.Node using (centre-neg)
open import Real.Interval.OrderLaws using (eps-below)
open import Real.Interval.Equiv using (_≈ℝ_)
open import Real.Interval.Rational using (r≤|r|; pos-diff)
open import Real.Interval.Kit using (recip-antitone; two-half; abs-swap; 0<half)
open import Real.Interval.Order using
  (_<ℝ_) renaming (l-mono' to l-monoℓ; u-mono' to u-monoℓ)
open import Real.Interval.Apartness using (_#ℝ_)
open import Real.Interval.OrderLe using (≤ℝ-antisym; sub-mono)
open import Real.Interval.Mul using (cancelʳ; cancel-z)
open import Real.Interval.Mul.Order using (abs-neg)

------------------------------------------------------------------------
-- Monotonicity of ε: larger indices give no larger tolerances.
--
-- ε 的单调性：索引越大，容差越小。
ε-mono : ∀ {a b} → a ≤ℕ b → ε b ≤ ε a
ε-mono {a} {b} a≤b =
  recip-antitone (positive⁻¹ (embed (suc a)) {{embed-suc-pos}})
    (embed-mono-≤ (s≤s a≤b))

------------------------------------------------------------------------
-- Constant sequences converge to their value.
--
-- 常序列收敛到其自身。
⟶-const : (c : RealI) → (λ (_ : ℕ) → c) ⟶ c
⟶-const c k = 0 , λ _ _ →
  ≤-<-trans
    (begin≤
       ∣ centre c k - centre c k ∣
         ≡⟨ cong ∣_∣ (+-inverseʳ (centre c k)) ⟩
       ∣ 0ℚ ∣
         ≡⟨ 0≤p⇒∣p∣≡p {0ℚ} ≤-refl ⟩
       0ℚ
     ≤∎)
    (0<ε k)

------------------------------------------------------------------------
-- Negation commutes with taking limits.
--
-- 取负与求极限交换。
⟶-neg : ∀ {f L} → f ⟶ L → (λ n → negℝ (f n)) ⟶ negℝ L
⟶-neg {f} {L} conv k =
  let N , h = conv k
  in N , λ n n≥N →
    let
      d = centre (f n) k - centre L k
      e = h n n≥N
    in ≤-<-trans
         (begin≤
            ∣ centre (negℝ (f n)) k - centre (negℝ L) k ∣
              ≡⟨ cong₂ (λ a b → ∣ a - b ∣)
                       (centre-neg (f n) k) (centre-neg L k) ⟩
            ∣ neg (centre (f n) k) - neg (centre L k) ∣
              ≡⟨ abs-neg {centre (f n) k} {centre L k} ⟩
            ∣ d ∣
          ≤∎)
         e

------------------------------------------------------------------------
-- Limits are unique: two limits of the same sequence are equivalent.
--
-- 极限唯一：同一序列的两个极限彼此等价。

-- Tightness: apartness-free points are equivalent.
--
-- 紧致性：不可分离的点彼此等价。
tight : ∀ {x y} → ¬ (x #ℝ y) → x ≈ℝ y
tight {x} {y} ¬x#y = ≤ℝ-antisym ¬y<x ¬x<y
  where
    ¬y<x : ¬ (y <ℝ x)
    ¬y<x y<x = ¬x#y (inj₂ y<x)

    ¬x<y : ¬ (x <ℝ y)
    ¬x<y x<y = ¬x#y (inj₁ x<y)

-- A strict inequality is preserved when the same term is added on the right.
--
-- 右侧加上同一项后，严格不等式保持。
add-right-< : ∀ {x y z} → x < y → x + z < y + z
add-right-< {x} {y} {z} x<y =
  subst₂ (λ a b → a < b) (+-comm z x) (+-comm z y)
    (+-monoʳ-< z x<y)

-- Upper one-sided bound from an absolute-value bound.
--
-- 由绝对值界得到上侧界。
abs<⇒upper : ∀ {a c e} → ∣ c - a ∣ < e → c < a + e
abs<⇒upper {a} {c} {e} h =
  let d< : c - a < e
      d< = ≤-<-trans (r≤|r| (c - a)) h
      add : (c - a) + a < e + a
      add = add-right-< d<
      lhs : (c - a) + a ≡ c
      lhs = cancelʳ c a
      rhs : e + a ≡ a + e
      rhs = +-comm e a
  in subst (λ z → c < z) rhs (subst (λ z → z < e + a) lhs add)

-- Lower one-sided bound from an absolute-value bound.
--
-- 由绝对值界得到下侧界。
abs<⇒lower : ∀ {a c e} → ∣ c - a ∣ < e → a - e < c
abs<⇒lower {a} {c} {e} h =
  let h' : ∣ a - c ∣ < e
      h' = subst (λ z → z < e) (sym (abs-swap a c)) h
      d< : a - c < e
      d< = ≤-<-trans (r≤|r| (a - c)) h'
      add : (a - c) + c < e + c
      add = add-right-< d<
      lhs : (a - c) + c ≡ a
      lhs = cancelʳ a c
      a< : a < e + c
      a< = subst (λ z → z < e + c) lhs add
      step : a - e < (e + c) - e
      step = add-right-< a<
      rhs≡ : (e + c) - e ≡ c
      rhs≡ = cancel-z e c
  in subst (λ z → a - e < z) rhs≡ step

-- From b - e < c < a + e conclude b - a < e + e.
--
-- 由两侧的容差夹逼推出间隙小于两份容差。
gap-chain :
  ∀ {a b c e} → b - e < c → c < a + e → b - a < e + e
gap-chain {a} {b} {c} {e} lo hi =
  let
    mid : b - e < a + e
    mid = ≤-<-trans (<⇒≤ lo) hi

    add-e : (b - e) + e < (a + e) + e
    add-e = add-right-< mid

    lhs≡ : (b - e) + e ≡ b
    lhs≡ = cancelʳ b e

    b< : b < (a + e) + e
    b< = subst (λ z → z < (a + e) + e) lhs≡ add-e

    rhs≡ : (a + e) + e - a ≡ e + e
    rhs≡ =
      trans
        (cong (_- a) (+-assoc a e e))
        (cancel-z a (e + e))
  in subst (λ z → b - a < z) rhs≡ (add-right-< b<)

-- A rational gap between two limits is contradicted by convergence.
-- The two convergences are passed explicitly so the symmetric case
-- needs no recursion.
--
-- 两个极限之间的有理间隙与收敛性矛盾。两条收敛性显式传入，
-- 因而对称分支无需递归。
gap-contradiction :
  ∀ {A B f j} → f ⟶ A → f ⟶ B → u A j < l B j → ⊥
gap-contradiction {A} {B} {f} {j} convA convB gap =
  let
    g = l B j - u A j
    0<g : 0ℚ < g
    0<g = pos-diff (u A j) (l B j) gap

    q , εq< = eps-below (g * half)
                (positive⁻¹ (g * half)
                  {{pos*pos⇒pos g {{positive 0<g}} half {{positive 0<half}}}})
    p = q ⊔ j
    q≤p : q ≤ℕ p
    q≤p = m≤m⊔n q j
    j≤p : j ≤ℕ p
    j≤p = m≤n⊔m q j
    εp< : ε p < g * half
    εp< = ≤-<-trans (ε-mono q≤p) εq<

    N1 , w1 = convA p
    N2 , w2 = convB p
    N = N1 ⊔ N2
    n≥N1 : N ≥ N1
    n≥N1 = m≤m⊔n N1 N2
    n≥N2 : N ≥ N2
    n≥N2 = m≤n⊔m N1 N2

    c = centre (f N) p
    eA = w1 N n≥N1
    eB = w2 N n≥N2

    upper : c < centre A p + ε p
    upper = abs<⇒upper eA
    lower : centre B p - ε p < c
    lower = abs<⇒lower eB

    cA≤uAj : centre A p ≤ u A j
    cA≤uAj = ≤-trans (centre-u A p) (u-monoℓ A j≤p)

    cB≥lBj : l B j ≤ centre B p
    cB≥lBj = ≤-trans (l-monoℓ B j≤p) (centre-l B p)

    g≤sep : g ≤ centre B p - centre A p
    g≤sep = sub-mono cB≥lBj cA≤uAj

    sep<2ε : centre B p - centre A p < ε p + ε p
    sep<2ε =
      gap-chain {a = centre A p} {b = centre B p} {c = c} {e = ε p}
        lower upper

    2ε<g : ε p + ε p < g
    2ε<g =
      subst (λ z → ε p + ε p < z) (two-half g)
        (+-mono-< εp< εp<)
    g<2ε : g < ε p + ε p
    g<2ε = ≤-<-trans g≤sep sep<2ε
  in ⊥-elim (<-irrefl refl (<-trans g<2ε 2ε<g))

-- Two limits of the same sequence are equivalent.
--
-- 同一序列的两个极限彼此等价。
⟶-unique : ∀ {f L M} → f ⟶ L → f ⟶ M → L ≈ℝ M
⟶-unique {f} {L} {M} convL convM = tight ¬L#M
  where
    ¬L#M : ¬ (L #ℝ M)
    ¬L#M (inj₁ (j , gap)) =
      gap-contradiction {A = L} {B = M} {f = f} {j = j} convL convM gap
    ¬L#M (inj₂ (j , gap)) =
      gap-contradiction {A = M} {B = L} {f = f} {j = j} convM convL gap
