------------------------------------------------------------------------
-- Constructive Cauchy reals
--
-- Cauchy sequences of rationals with an explicit modulus of
-- convergence, quotiented by a setoid equivalence. The equivalence is
-- defined as a symmetric pair of inequalities, so symmetry is
-- structural (swap components).
--
-- 构造性柯西实数
--
-- 带显式收敛模数的有理柯西序列，按 setoid 等价商除。等价关系定义为
-- 对称双不等式，故对称性是结构性的（交换分量）。
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module ALMA.Base.Real where

open import Agda.Primitive using (lzero)
open import Data.Integer using (+_) renaming (_*_ to _ℤ*_)
open import Data.Integer.Properties using (+◃n≡+n)
open import Data.Nat using (ℕ; _≥_; _⊔_; suc) renaming (_*_ to _ℕ*_)
open import Data.Nat.Properties using (m≤m⊔n; m≤n⊔m; ≤-trans; *-suc)
open import Data.Nat.Coprimality using (1-coprimeTo) renaming (sym to coprime-sym)
open import Data.Product using (Σ; _,_; _×_)
open import Data.Rational using
  (ℚ; 0ℚ; 1ℚ; _+_; _-_; -_; _*_; ∣_∣; _<_; NonZero; Positive)
open import Data.Rational.Base using (1/_; mkℚ)
open import Data.Rational.Properties using
  (0≤p⇒∣p∣≡p; +-inverseʳ; ≤-refl; ≤-reflexive; +-assoc; positive⁻¹; pos⇒nonZero 
  ; normalize-coprime; /-cong; +-inverseˡ; +-identityʳ; ≤-<-trans; +-mono-<; *-inverseʳ
  ; *-assoc; *-comm; *-identityˡ; *-identityʳ; *-distribʳ-+; mkℚ+-pos)
open import Relation.Binary.Core using (Rel)
open import Relation.Binary.Structures using (IsEquivalence)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; cong; trans; subst; sym; module ≡-Reasoning)
open ≡-Reasoning

------------------------------------------------------------------------
-- Precision level
--
-- ε k = 1 / (k + 1). The k-th Cauchy level demands approximation
-- within 1/(k+1).
--
-- Embedding ℕ → ℚ as the normalised fraction n/1, built directly
-- with the raw constructor so the reciprocal 1/(suc n) reduces
-- definitionally (no gcd decision term).
--
-- 精度层
--
-- ε k = 1 / (k + 1)。第 k 层柯西条件要求逼近到 1/(k+1) 以内。
--
-- 将 ℕ 嵌入 ℚ 为规范化分数 n/1，直接用底层构造器构造，
-- 使倒数 1/(suc n) 可定义性归约（无 gcd 判定项）。

embed : ℕ → ℚ
embed n = mkℚ (+ n) 0 (coprime-sym (1-coprimeTo n))

-- ε k = 1 / (k + 1). The k-th Cauchy level demands approximation
-- within 1/(k+1).
--
-- ε k = 1 / (k + 1)。第 k 层柯西条件要求逼近到 1/(k+1) 以内。
ε : ℕ → ℚ
ε k = 1/ embed (suc k)

-- embed (suc n) is positive, hence nonzero.
--
-- embed (suc n) 为正，故非零。
embed-suc-pos : ∀ {n} → Positive (embed (suc n))
embed-suc-pos {n} =
  mkℚ+-pos (suc n) 1 {c = coprime-sym (1-coprimeTo (suc n))}

instance
  embed-suc-nonZero : ∀ {n} → NonZero (embed (suc n))
  embed-suc-nonZero {n} = pos⇒nonZero (embed (suc n)) {{embed-suc-pos {n}}}

-- The rational 2, built directly via the raw constructor so that
-- 2ℚ * embed n reduces via the fraction congruence (no sign wrapper).
--
-- 有理数 2，直接用底层构造器构造，使 2ℚ * embed n 经分数同余归约。
2ℚ : ℚ
2ℚ = embed 2

-- 2ℚ ≡ 1 + 1 (used to unfold the distributive law).
--
-- 2ℚ ≡ 1 + 1（用于展开分配律）。
2ℚ≡1+1 : 2ℚ ≡ 1ℚ + 1ℚ
2ℚ≡1+1 = sym (normalize-coprime (coprime-sym (1-coprimeTo 2)))

-- Numerator arithmetic: (+2) · (+n) = +(2n).
--
-- 分子算术：(+2) · (+n) = +(2n)。
num-2 : ∀ n → (+ 2) ℤ* (+ n) ≡ + (2 ℕ* n)
num-2 n = +◃n≡+n (2 ℕ* n)

2*embed : ∀ n → 2ℚ * embed n ≡ embed (2 ℕ* n)
2*embed n =
  trans (/-cong (num-2 n) refl)
        (normalize-coprime (coprime-sym (1-coprimeTo (2 ℕ* n))))

-- suc (suc (2*k)) = 2 * suc k.
--
-- 半精度分母等于全精度分母的两倍。
den-2 : ∀ k → suc (suc (2 ℕ* k)) ≡ 2 ℕ* suc k
den-2 k = sym (*-suc 2 k)

------------------------------------------------------------------------
-- Cauchy sequence record
--
-- A Cauchy sequence carries its own convergence modulus μ: for every
-- precision k, all terms from position μ k onward agree within ε k.
--
-- 柯西序列记录
--
-- 柯西序列携带自己的收敛模数 μ：对每个精度 k，从位置 μ k 起的所有项
-- 在 ε k 以内一致。

record CauchySeq : Set₁ where
  field
    f : ℕ → ℚ
    μ : ℕ → ℕ
    cauchy : ∀ k n m → n ≥ μ k → m ≥ μ k → ∣ f n - f m ∣ < ε k

open CauchySeq

------------------------------------------------------------------------
-- Symmetric close relation
--
-- q1 ≈[k] q2 iff both directions are within ε k:
--   (q1 - q2) < ε k  AND  (q2 - q1) < ε k
-- This is symmetric by construction — no absolute value, no subst.
--
-- 对称接近关系
--
-- q1 ≈[k] q2 当且仅当两个方向都在 ε k 以内：
--   (q1 - q2) < ε k 且  (q2 - q1) < ε k
-- 这按构造就是对称的——无绝对值、无 subst。

_s≈_ : ℚ → ℚ → ℕ → Set
_s≈_ q1 q2 k = (q1 + (- q2)) < ε k × (q2 + (- q1)) < ε k

------------------------------------------------------------------------
-- Setoid equivalence
--
-- x ≈ y iff for every k, eventually x n and y n are symmetrically
-- close within ε k.
--
-- setoid 等价
--
-- x ≈ y  iff  对每个 k，最终 x n 与 y n 在 ε k 内对称接近。

_≈_ : Rel CauchySeq lzero
_≈_ x y = ∀ k → Σ ℕ (λ N → ∀ n → n ≥ N → _s≈_ (f x n) (f y n) k)

------------------------------------------------------------------------
-- ε is positive
--
-- ε k = (+1)/(suc k) is positive by construction.
--
-- ε 为正
--
-- ε k = (+1)/(suc k) 按构造为正。

0<ε : ∀ k → 0ℚ < ε k
0<ε k =
  positive⁻¹ (ε k)
    {{mkℚ+-pos 1 (suc k) {c = 1-coprimeTo (suc k)}}}

------------------------------------------------------------------------
-- Telescoping lemma
--
-- (a + (-b)) + (b + (-c)) ≡ a + (-c)
--
-- 望远镜消去引理
--
-- 中间项 b 与 -b 相消。

telescope : ∀ a b c → (a + (- b)) + (b + (- c)) ≡ a + (- c)
telescope a b c = begin
  (a + (- b)) + (b + (- c))
    ≡⟨ sym (+-assoc (a + (- b)) b (- c)) ⟩
  ((a + (- b)) + b) + (- c)
    ≡⟨ cong (λ v → v + (- c)) (+-assoc a (- b) b) ⟩
  (a + ((- b) + b)) + (- c)
    ≡⟨ cong (λ v → v + (- c)) (cong (λ v → a + v) (+-inverseˡ b)) ⟩
  (a + 0ℚ) + (- c)
    ≡⟨ cong (λ v → v + (- c)) (+-identityʳ a) ⟩
  a + (- c)
  ∎

------------------------------------------------------------------------
-- Halving lemma
--
-- 1/(2m) + 1/(2m) = 1/m. Two approximations at half tolerance add
-- to the full tolerance. Pure field algebra over ℚ.
--
-- 折半引理
--
-- 1/(2m) + 1/(2m) = 1/m。半精度容差两次相加即全精度容差。
-- 纯 ℚ 域代数。

halve : ∀ m {{_ : NonZero m}} {{_ : NonZero (2ℚ * m)}} →
       (1/ (2ℚ * m)) + (1/ (2ℚ * m)) ≡ 1/ m
halve m =
  let t : ℚ
      t = 1/ (2ℚ * m)
      tt≡2t : t + t ≡ 2ℚ * t
      tt≡2t = begin
        t + t
          ≡⟨ cong (λ v → v + t) (sym (*-identityˡ t)) ⟩
        1ℚ * t + t
          ≡⟨ cong (λ v → (1ℚ * t) + v) (sym (*-identityˡ t)) ⟩
        1ℚ * t + 1ℚ * t
          ≡⟨ sym (*-distribʳ-+ t 1ℚ 1ℚ) ⟩
        (1ℚ + 1ℚ) * t
          ≡⟨ cong (λ v → v * t) (sym 2ℚ≡1+1) ⟩
        2ℚ * t
        ∎
      2tm : (2ℚ * t) * m ≡ 1ℚ
      2tm = begin
        (2ℚ * t) * m
          ≡⟨ *-assoc 2ℚ t m ⟩
        2ℚ * (t * m)
          ≡⟨ cong (2ℚ *_) (*-comm t m) ⟩
        2ℚ * (m * t)
          ≡⟨ sym (*-assoc 2ℚ m t) ⟩
        (2ℚ * m) * t
          ≡⟨ *-inverseʳ (2ℚ * m) ⟩
        1ℚ
        ∎
      2t≡1/m : 2ℚ * t ≡ 1/ m
      2t≡1/m = begin
        2ℚ * t
          ≡⟨ sym (*-identityʳ (2ℚ * t)) ⟩
        (2ℚ * t) * 1ℚ
          ≡⟨ cong (λ v → (2ℚ * t) * v) (sym (*-inverseʳ m)) ⟩
        (2ℚ * t) * (m * (1/ m))
          ≡⟨ sym (*-assoc (2ℚ * t) m (1/ m)) ⟩
        ((2ℚ * t) * m) * (1/ m)
          ≡⟨ cong (λ v → v * (1/ m)) 2tm ⟩
        1ℚ * (1/ m)
          ≡⟨ *-identityˡ (1/ m) ⟩
        1/ m
        ∎
  in begin
    t + t
      ≡⟨ tt≡2t ⟩
    2ℚ * t
      ≡⟨ 2t≡1/m ⟩
    1/ m
    ∎

-- Reciprocal respects propositional equality.
--
-- 倒数保持命题相等。
reciprocal-cong : ∀ a b → .{{na : NonZero a}} → .{{nb : NonZero b}} →
                  a ≡ b → 1/_ a ≡ 1/_ b
reciprocal-cong a .a {{na}} {{na₁}} refl = refl

------------------------------------------------------------------------
-- ε halving
--
-- ε(suc(2k)) + ε(suc(2k)) = ε k.
--
-- ε(suc(2k)) = 1/embed(suc(suc(2k))) = 1/(2·embed(suc k)),
-- so two copies add to 1/embed(suc k) = ε k.
--
-- ε 折半
--
-- ε(suc(2k)) + ε(suc(2k)) = ε k。
--
-- ε(suc(2k)) = 1/embed(suc(suc(2k))) = 1/(2·embed(suc k))，
-- 两份相加得 1/embed(suc k) = ε k。

1/embed : ∀ n → 1/ embed (suc n) ≡ ε n
1/embed n = refl

ε-half : ∀ k → ε (suc (2 ℕ* k)) + ε (suc (2 ℕ* k)) ≡ ε k
ε-half k =
  let m = embed (suc k)
      b = embed (suc (suc (2 ℕ* k)))
      e2m : 2ℚ * m ≡ b
      e2m = begin
        2ℚ * m
          ≡⟨ 2*embed (suc k) ⟩
        embed (2 ℕ* suc k)
          ≡⟨ cong embed (sym (den-2 k)) ⟩
        b
        ∎
      instance
        n2m : NonZero (2ℚ * m)
        n2m = subst NonZero (sym e2m) (pos⇒nonZero b)
      t : ℚ
      t = 1/ (2ℚ * m)
      l1 : t ≡ ε (suc (2 ℕ* k))
      l1 = begin
        t
          ≡⟨ reciprocal-cong (2ℚ * m) b e2m ⟩
        1/ b
          ≡⟨ sym (1/embed (suc (2 ℕ* k))) ⟩
        ε (suc (2 ℕ* k))
        ∎
      l2 : 1/ m ≡ ε k
      l2 = 1/embed k
      h : t + t ≡ 1/ m
      h = halve m
  in begin
    ε (suc (2 ℕ* k)) + ε (suc (2 ℕ* k))
      ≡⟨ cong (λ r → r + r) (sym l1) ⟩
    t + t
      ≡⟨ subst (λ r → t + t ≡ r) l2 h ⟩
    1/ m
      ≡⟨ l2 ⟩
    ε k
    ∎

------------------------------------------------------------------------
-- Reflexivity
--
-- Take N = μ x k. For n ≥ μ x k, the Cauchy condition gives
-- |f x n - f x n| < ε k, which implies both directions are close.
--
-- 自反性
--
-- 取 N = μ x k。n ≥ μ x k 时，柯西条件给出 |f x n - f x n| < ε k，
-- 蕴含两个方向都接近。

≈-refl : ∀ {x} → x ≈ x
≈-refl {x} k = μ x k , λ n n≥N →
  let eq : f x n + (- f x n) ≡ 0ℚ
      eq = +-inverseʳ (f x n)
      d1 : (f x n + (- f x n)) < ε k
      d1 = ≤-<-trans (≤-reflexive eq) (0<ε k)
      d2 : (f x n + (- f x n)) < ε k
      d2 = d1
  in (d1 , d2)

------------------------------------------------------------------------
-- Symmetry
--
-- Swap the two components of the symmetric close relation.
-- No subst, no absolute-value lemma.
--
-- 对称性
--
-- 交换对称接近关系的两个分量。无 subst、无绝对值引理。

≈-sym : ∀ {x y} → x ≈ y → y ≈ x
≈-sym {x} {y} x≈y k =
  let N , witness = x≈y k
  in N , λ n n≥N →
    let (d1 , d2) = witness n n≥N
    in (d2 , d1)

------------------------------------------------------------------------
-- One-direction triangle step
--
-- 单向三角步

trans-one-dir : ∀ (a b c : ℚ) {k : ℕ}
  → (a + (- b)) < ε (suc (2 ℕ* k))
  → (b + (- c)) < ε (suc (2 ℕ* k))
  → (a + (- c)) < ε k
trans-one-dir a b c {k} d1 d2 =
  let half  = 2 ℕ* k
      c'    = ε (suc half)
      cc    : c' + c' ≡ ε k
      cc    = ε-half k
      bound : (a + (- b)) + (b + (- c)) < c' + c'
      bound = +-mono-< d1 d2
      bound' : (a + (- b)) + (b + (- c)) < ε k
      bound' = subst (λ r → (a + (- b)) + (b + (- c)) < r) cc bound
      sum   : (a + (- b)) + (b + (- c)) ≡ a + (- c)
      sum   = telescope a b c
  in subst (λ r → r < ε k) sum bound'

------------------------------------------------------------------------
-- Transitivity
--
-- 传递性

≈-trans : ∀ {x y z} → x ≈ y → y ≈ z → x ≈ z
≈-trans {x} {y} {z} x≈y y≈z k =
  let half = 2 ℕ* k
      N1 , w1 = x≈y (suc half)
      N2 , w2 = y≈z (suc half)
      N = N1 ⊔ N2
  in N , λ n n≥N →
    let n≥N1 = ≤-trans (m≤m⊔n N1 N2) n≥N
        n≥N2 = ≤-trans (m≤n⊔m N1 N2) n≥N
        (d11 , d12) = w1 n n≥N1
        (d21 , d22) = w2 n n≥N2
    in trans-one-dir (f x n) (f y n) (f z n) d11 d21
     , trans-one-dir (f z n) (f y n) (f x n) d22 d12

------------------------------------------------------------------------
-- Setoid instance
--
-- setoid 实例

≈-isEquivalence : IsEquivalence {A = CauchySeq} _≈_
≈-isEquivalence = record
  { refl  = λ {x} → ≈-refl {x}
  ; sym   = λ {x y} → ≈-sym {x} {y}
  ; trans = λ {x y z} → ≈-trans {x} {y} {z}
  }

------------------------------------------------------------------------
-- ℚ embedding
--
-- Embed a rational q as the constant Cauchy sequence f n = q, with
-- modulus μ k = 0 (all terms are identical).
--
-- ℚ 嵌入
--
-- 将有理数 q 嵌入为常柯西序列 f n = q，模数 μ k = 0（所有项相同）。

const : ℚ → CauchySeq
const q = record
  { f      = λ n → q
  ; μ      = λ k → 0
  ; cauchy = λ k _ _ _ _ →
      let eq0 : ∣ q - q ∣ ≡ 0ℚ
          eq0 = begin
            ∣ q - q ∣
              ≡⟨ cong ∣_∣ (+-inverseʳ q) ⟩
            ∣ 0ℚ ∣
              ≡⟨ 0≤p⇒∣p∣≡p {0ℚ} (≤-refl {0ℚ}) ⟩
            0ℚ
            ∎
      in subst (λ z → z < ε k) (sym eq0) (0<ε k)
  }
