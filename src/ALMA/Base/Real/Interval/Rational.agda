------------------------------------------------------------------------
-- Rational lemmas for real-interval arithmetic
--
-- Negation, subtraction, min/max, absolute-value bounds, and fraction
-- comparison with a general denominator, used by the interval modules.
-- The min/max lattice is derived from the rational order and is used to
-- bound interval endpoints via mag.
--
-- 实区间算术所需的有理引理
--
-- 取负、减法、min/max 与绝对值界，以及一般分母的分数比较，供区间各
-- 模块使用。min/max 格结构由有理序导出，并通过 mag 界定区间端点。
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module ALMA.Base.Real.Interval.Rational where

open import Data.Empty using (⊥-elim)
open import Data.Integer using (+_; +<+) renaming (_*_ to _*ℤ_; _<_ to _<ℤ_)
import Data.Integer.Properties as ℤP
open import Data.Nat using
  (ℕ; zero; suc; z≤n; s≤s; _^_; _∸_) renaming (_+_ to _+ℕ_; _*_ to _*ℕ_; _<_ to _<ℕ_)
import Data.Nat.Properties as ℕP
open import Data.Rational using
  (ℚ; 0ℚ; _+_; _-_; _<_; _≤_; ∣_∣; fromℚᵘ; toℚᵘ) renaming (-_ to neg)
open import Data.Rational.Properties using
  (+-assoc; +-comm; +-inverseʳ; neg-distrib-+; +-mono-<-≤; ≤-refl; ≤-reflexive
  ; <⇒≤; <-cmp; ≤-trans; ≤-antisym; neg-antimono-≤; 0≤∣p∣
  ; ∣-p∣≡∣p∣; ∣p∣≡p∨∣p∣≡-p; 0≤p⇒∣p∣≡p; toℚᵘ-cancel-<; toℚᵘ-fromℚᵘ)
open import Data.Rational.Unnormalised.Base
  using (ℚᵘ; mkℚᵘ; _≃_; *≡*; *<*) renaming (_<_ to _<ᵘ_)
open import Data.Rational.Unnormalised.Properties using (<-respˡ-≃; <-respʳ-≃)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; cong; sym; subst; module ≡-Reasoning)
open ≡-Reasoning
open import Relation.Nullary.Negation using (¬_)
open import Relation.Binary.Definitions using (tri<; tri≈; tri>)

open import ALMA.Base.Real.Interval using (neg-invol)

------------------------------------------------------------------------
-- Order reflection
--
-- From ¬ (a < b) conclude b ≤ a, by trichotomy.
--
-- 序反射
--
-- 由 ¬ (a < b) 经三歧性得 b ≤ a。

¬<⇒≥ : ∀ {a b : ℚ} → ¬ (a < b) → b ≤ a
¬<⇒≥ {a} {b} ¬a<b with <-cmp a b
... | tri< a<b _ _ = ⊥-elim (¬a<b a<b)
... | tri≈ _ a≡b _ = ≤-reflexive (sym a≡b)
... | tri> _ _ b<a = <⇒≤ b<a

------------------------------------------------------------------------
-- Positive difference
--
-- a < b implies 0 < b − a.
--
-- 正差
--
-- a < b 蕴含 0 < b − a。

pos-diff : ∀ a b → a < b → 0ℚ < b - a
pos-diff a b a<b =
  subst (λ z → z < b - a)
        (+-inverseʳ a)
        (+-mono-<-≤ a<b (≤-refl {neg a}))

------------------------------------------------------------------------
-- Algebra of subtraction
--
-- rearrange regroups a four-term sum; sub-add distributes subtraction
-- over addition; negsub and neg-sub flip differences; cong-plus and
-- cong-minus are explicit two-argument congruences.
--
-- 减法代数
--
-- rearrange 重排四项和；sub-add 把减法分配到加法；negsub 与 neg-sub
-- 翻转差；cong-plus 与 cong-minus 是显式的双参数同余。

rearrange : ∀ a b c d
  → (a + b) + (neg c + neg d) ≡ (a + neg c) + (b + neg d)
rearrange a b c d = begin
  (a + b) + (neg c + neg d)
    ≡⟨ sym (+-assoc (a + b) (neg c) (neg d)) ⟩
  ((a + b) + neg c) + neg d
    ≡⟨ cong (λ z → z + neg d) (+-assoc a b (neg c)) ⟩
  (a + (b + neg c)) + neg d
    ≡⟨ cong (λ z → (a + z) + neg d) (+-comm b (neg c)) ⟩
  (a + (neg c + b)) + neg d
    ≡⟨ cong (λ z → z + neg d) (sym (+-assoc a (neg c) b)) ⟩
  ((a + neg c) + b) + neg d
    ≡⟨ +-assoc (a + neg c) b (neg d) ⟩
  (a + neg c) + (b + neg d)
  ∎

sub-add : (a b c d : ℚ) → (a + b) - (c + d) ≡ (a - c) + (b - d)
sub-add a b c d = begin
  (a + b) - (c + d)
    ≡⟨ cong (λ z → (a + b) + z) (neg-distrib-+ c d) ⟩
  (a + b) + (neg c + neg d)
    ≡⟨ rearrange a b c d ⟩
  (a - c) + (b - d)
  ∎

negsub : ∀ x y → neg (x - y) ≡ y - x
negsub x y = begin
  neg (x - y)
    ≡⟨ refl ⟩
  neg (x + neg y)
    ≡⟨ neg-distrib-+ x (neg y) ⟩
  neg x + neg (neg y)
    ≡⟨ cong (λ z → neg x + z) (neg-invol y) ⟩
  neg x + y
    ≡⟨ +-comm (neg x) y ⟩
  y + neg x
    ≡⟨ refl ⟩
  y - x
  ∎

neg-sub : ∀ a b → neg a - neg b ≡ b - a
neg-sub a b = begin
  neg a - neg b
    ≡⟨ refl ⟩
  neg a + neg (neg b)
    ≡⟨ cong (λ z → neg a + z) (neg-invol b) ⟩
  neg a + b
    ≡⟨ +-comm (neg a) b ⟩
  b + neg a
    ≡⟨ refl ⟩
  b - a
  ∎

cong-plus : ∀ {a a' b b' : ℚ} → a ≡ a' → b ≡ b' → a + b ≡ a' + b'
cong-plus {a} {a'} {b} {b'} e1 e2 = begin
  a + b
    ≡⟨ cong (λ z → z + b) e1 ⟩
  a' + b
    ≡⟨ cong (λ z → a' + z) e2 ⟩
  a' + b'
  ∎

cong-minus : ∀ {a a' b b' : ℚ} → a ≡ a' → b ≡ b' → a - b ≡ a' - b'
cong-minus {a} {a'} {b} {b'} e1 e2 = begin
  a - b
    ≡⟨ cong (λ z → z - b) e1 ⟩
  a' - b
    ≡⟨ cong (λ z → a' - z) e2 ⟩
  a' - b'
  ∎

------------------------------------------------------------------------
-- Minimum and maximum
--
-- 最小值与最大值

min : ℚ → ℚ → ℚ
min a b with <-cmp a b
... | tri< _ _ _ = a
... | tri≈ _ _ _ = a
... | tri> _ _ _ = b

max : ℚ → ℚ → ℚ
max a b with <-cmp a b
... | tri< _ _ _ = b
... | tri≈ _ _ _ = a
... | tri> _ _ _ = a

min≤ˡ : ∀ a b → min a b ≤ a
min≤ˡ a b with <-cmp a b
... | tri< _ _ _ = ≤-refl
... | tri≈ _ _ _ = ≤-refl
... | tri> _ _ b<a = <⇒≤ b<a

min≤ʳ : ∀ a b → min a b ≤ b
min≤ʳ a b with <-cmp a b
... | tri< a<b _ _ = <⇒≤ a<b
... | tri≈ _ a≡b _ = ≤-reflexive a≡b
... | tri> _ _ _ = ≤-refl

≤maxˡ : ∀ a b → a ≤ max a b
≤maxˡ a b with <-cmp a b
... | tri< a<b _ _ = <⇒≤ a<b
... | tri≈ _ _ _ = ≤-refl
... | tri> _ _ _ = ≤-refl

≤maxʳ : ∀ a b → b ≤ max a b
≤maxʳ a b with <-cmp a b
... | tri< _ _ _ = ≤-refl
... | tri≈ _ a≡b _ = ≤-reflexive (sym a≡b)
... | tri> _ _ b<a = <⇒≤ b<a

min<max : ∀ a b → ¬ (a ≡ b) → min a b < max a b
min<max a b a≠b with <-cmp a b
... | tri< a<b _ _ = a<b
... | tri≈ _ a≡b _ = ⊥-elim (a≠b a≡b)
... | tri> _ _ b<a = b<a

------------------------------------------------------------------------
-- min/max interaction with the order
--
-- 极值与序的交互

max-eq : ∀ a b → max a b ≡ a ⊎ max a b ≡ b
max-eq a b with <-cmp a b
... | tri< _ _ _ = inj₂ refl
... | tri≈ _ _ _ = inj₁ refl
... | tri> _ _ _ = inj₁ refl

min-eq : ∀ a b → min a b ≡ a ⊎ min a b ≡ b
min-eq a b with <-cmp a b
... | tri< _ _ _ = inj₁ refl
... | tri≈ _ _ _ = inj₁ refl
... | tri> _ _ _ = inj₂ refl

max-le : ∀ {a b : ℚ} → a ≤ b → max a b ≡ b
max-le {a} {b} a≤b with <-cmp a b
... | tri< _ _ _ = refl
... | tri≈ _ a≡b _ = a≡b
... | tri> ¬a<b _ _ = ≤-antisym a≤b (¬<⇒≥ ¬a<b)

max-ge : ∀ {a b : ℚ} → b ≤ a → max a b ≡ a
max-ge {a} {b} b≤a with <-cmp a b
... | tri< a<b _ _ = sym (≤-antisym (<⇒≤ a<b) b≤a)
... | tri≈ _ _ _ = refl
... | tri> _ _ _ = refl

min-le : ∀ {a b : ℚ} → a ≤ b → min a b ≡ a
min-le {a} {b} a≤b with <-cmp a b
... | tri< _ _ _ = refl
... | tri≈ _ _ _ = refl
... | tri> ¬a<b _ _ = ≤-antisym (¬<⇒≥ ¬a<b) a≤b

min-ge : ∀ {a b : ℚ} → b ≤ a → min a b ≡ b
min-ge {a} {b} b≤a with <-cmp a b
... | tri< a<b _ _ = ≤-antisym (<⇒≤ a<b) b≤a
... | tri≈ _ a≡b _ = a≡b
... | tri> _ _ _ = refl

max≤ : ∀ {a b c : ℚ} → a ≤ c → b ≤ c → max a b ≤ c
max≤ {a} {b} {c} a≤c b≤c with <-cmp a b
... | tri< _ _ _ = b≤c
... | tri≈ _ _ _ = a≤c
... | tri> _ _ _ = a≤c

≤min : ∀ {a b c : ℚ} → a ≤ b → a ≤ c → a ≤ min b c
≤min {a} {b} {c} a≤b a≤c with <-cmp b c
... | tri< _ _ _ = a≤b
... | tri≈ _ _ _ = a≤b
... | tri> _ _ _ = a≤c

max-mono : ∀ {a b c d : ℚ} → a ≤ c → b ≤ d → max a b ≤ max c d
max-mono {a} {b} {c} {d} a≤c b≤d =
  max≤ (≤-trans a≤c (≤maxˡ c d)) (≤-trans b≤d (≤maxʳ c d))

min-mono : ∀ {a b c d : ℚ} → a ≤ c → b ≤ d → min a b ≤ min c d
min-mono {a} {b} {c} {d} a≤c b≤d =
  ≤min (≤-trans (min≤ˡ a b) a≤c) (≤-trans (min≤ʳ a b) b≤d)

------------------------------------------------------------------------
-- Absolute value and magnitude bounds
--
-- r≤|r| and -r≤|r| are the two elementary absolute-value bounds; mag
-- combines them into max |l| |u| and mag-≤ shows |x| ≤ mag l u for any
-- x in [l, u].
--
-- 绝对值与量级界
--
-- r≤|r| 与 -r≤|r| 是两条基本绝对值界；mag 合并为 max |l| |u|，
-- mag-≤ 表明 [l, u] 中任意 x 满足 |x| ≤ mag l u。

r≤|r| : ∀ r → r ≤ ∣ r ∣
r≤|r| r with ∣p∣≡p∨∣p∣≡-p r
... | inj₁ |r|≡r = ≤-reflexive (sym |r|≡r)
... | inj₂ |r|≡-r = subst (λ z → r ≤ z) (sym |r|≡-r) r≤-r
  where
    0≤-r : 0ℚ ≤ neg r
    0≤-r = subst (λ z → 0ℚ ≤ z) |r|≡-r (0≤∣p∣ r)

    r≤0 : r ≤ 0ℚ
    r≤0 = subst (λ z → z ≤ 0ℚ) (neg-invol r) (neg-antimono-≤ 0≤-r)

    r≤-r : r ≤ neg r
    r≤-r = ≤-trans r≤0 0≤-r

-r≤|r| : ∀ r → neg r ≤ ∣ r ∣
-r≤|r| r = subst (λ z → neg r ≤ z) (∣-p∣≡∣p∣ r) (r≤|r| (neg r))

mag : ℚ → ℚ → ℚ
mag l u = max ∣ l ∣ ∣ u ∣

mag-≤ : ∀ {l u x : ℚ} → l ≤ x → x ≤ u → ∣ x ∣ ≤ mag l u
mag-≤ {l} {u} {x} l≤x x≤u with ∣p∣≡p∨∣p∣≡-p x
... | inj₁ |x|≡x =
      ≤-trans (≤-reflexive |x|≡x)
      (≤-trans x≤u
      (≤-trans (r≤|r| u) (≤maxʳ ∣ l ∣ ∣ u ∣)))
... | inj₂ |x|≡-x =
      ≤-trans (≤-reflexive |x|≡-x)
      (≤-trans (neg-antimono-≤ l≤x)
      (≤-trans (≤-reflexive (sym |l|≡-l)) (≤maxˡ ∣ l ∣ ∣ u ∣)))
  where
    0≤-x : 0ℚ ≤ neg x
    0≤-x = subst (λ z → 0ℚ ≤ z) |x|≡-x (0≤∣p∣ x)

    x≤0 : x ≤ 0ℚ
    x≤0 = subst (λ z → z ≤ 0ℚ) (neg-invol x) (neg-antimono-≤ 0≤-x)

    l≤0 : l ≤ 0ℚ
    l≤0 = ≤-trans l≤x x≤0

    0≤-l : 0ℚ ≤ neg l
    0≤-l = neg-antimono-≤ l≤0

    |l|≡-l : ∣ l ∣ ≡ neg l
    |l|≡-l = subst (λ z → z ≡ neg l) (∣-p∣≡∣p∣ l) (0≤p⇒∣p∣≡p {neg l} 0≤-l)

------------------------------------------------------------------------
-- Fraction comparison with a general denominator
--
-- If N * (k+1) < (suc d) * 2^t then N / (suc d * 2^t) < 1/(k+1).
-- This generalises fracL-strict from IntervalEquiv, which is the
-- special case d = 0.
--
-- 一般分母的分数比较
--
-- 若 N * (k+1) < (suc d) * 2^t，则 N / (suc d * 2^t) < 1/(k+1)。
-- 它推广了 IntervalEquiv 的 fracL-strict，后者是 d = 0 的特例。

0<2^t : (t : ℕ) → 0 <ℕ 2 ^ t
0<2^t zero    = s≤s z≤n
0<2^t (suc t) = ℕP.≤-trans (s≤s z≤n) (ℕP.*-monoʳ-≤ 2 (0<2^t t))

-- suc (n ∸ 1) ≡ n for n > 0.
--
-- 当 n > 0 时，suc (n ∸ 1) ≡ n。
suc∸1 : {n : ℕ} → 0 <ℕ n → suc (n ∸ 1) ≡ n
suc∸1 {n} 0<n = begin
  suc (n ∸ 1)
    ≡⟨ refl ⟩
  1 +ℕ (n ∸ 1)
    ≡⟨ ℕP.+-comm 1 (n ∸ 1) ⟩
  (n ∸ 1) +ℕ 1
    ≡⟨ ℕP.m∸n+n≡m 0<n ⟩
  n
  ∎

-- 0 < (suc d) * 2^t.
0<sucd*2^t : (d t : ℕ) → 0 <ℕ suc d *ℕ 2 ^ t
0<sucd*2^t d t = ℕP.≤-trans (0<2^t t) (ℕP.m≤n*m (2 ^ t) (suc d))

-- Raw combined fraction N / (suc d * 2^t).
-- mkℚᵘ's second argument is denominator - 1, so to get denominator
-- (suc d) * 2^t we pass (suc d) * 2^t ∸ 1.
--
-- 原始组合分数 N / (suc d * 2^t)。
-- mkℚᵘ 的第二参数是分母减一，故要得分母 (suc d) * 2^t，
-- 传入 (suc d) * 2^t ∸ 1。
rawComb : (N d t : ℕ) → ℚᵘ
rawComb N d t = mkℚᵘ (+ N) (suc d *ℕ 2 ^ t ∸ 1)

-- Raw right-hand side 1/(suc k).
-- mkℚᵘ (+ 1) k has denominator suc k, hence value 1/(suc k).
--
-- 原始右端 1/(suc k)。
-- mkℚᵘ (+ 1) k 的分母为 suc k，故值为 1/(suc k)。
rawR : (k : ℕ) → ℚᵘ
rawR k = mkℚᵘ (+ 1) k

combFrac : (N d t : ℕ) → ℚ
combFrac N d t = fromℚᵘ (rawComb N d t)

flip-≃ : {a b : ℚᵘ} → _≃_ a b → _≃_ b a
flip-≃ (*≡* e) = *≡* (sym e)

-- Cross-multiplication, general version.
--
-- 交叉乘法，一般版本。
rawCross : (N d k t : ℕ) →
  N *ℕ suc k <ℕ suc d *ℕ 2 ^ t →
  (+ N) *ℤ (+ suc k) <ℤ (+ 1) *ℤ (+ suc (suc d *ℕ 2 ^ t ∸ 1))
rawCross N d k t h =
  let dd    = suc d *ℕ 2 ^ t ∸ 1
      dd-eq : suc dd ≡ suc d *ℕ 2 ^ t
      dd-eq = suc∸1 (0<sucd*2^t d t)
  in
  ℤP.<-≤-trans
    (ℤP.≤-<-trans
       (ℤP.≤-reflexive (ℤP.+◃n≡+n (N *ℕ suc k)))
       (ℤP.<-≤-trans
          (+<+ h)
          (ℤP.≤-reflexive (cong +_ (sym dd-eq)))))
    (ℤP.≤-reflexive (sym (ℤP.*-identityˡ (+ suc dd))))

-- If N * (k+1) < (suc d) * 2^t then N / (suc d * 2^t) < 1/(k+1).
--
-- 若 N * (k+1) < (suc d) * 2^t，则 N / (suc d * 2^t) < 1/(k+1)。
comb-strict : (N d k t : ℕ) →
  N *ℕ suc k <ℕ suc d *ℕ 2 ^ t →
  combFrac N d t < fromℚᵘ (rawR k)
comb-strict N d k t h =
  toℚᵘ-cancel-<
    (let eqL : _≃_ (toℚᵘ (combFrac N d t)) (rawComb N d t)
         eqL = toℚᵘ-fromℚᵘ (rawComb N d t)
         eqR : _≃_ (toℚᵘ (fromℚᵘ (rawR k))) (rawR k)
         eqR = toℚᵘ-fromℚᵘ (rawR k)
         cross : _<ᵘ_ (rawComb N d t) (rawR k)
         cross = *<* (rawCross N d k t h)
         p1 : _<ᵘ_ (toℚᵘ (combFrac N d t)) (rawR k)
         p1 = <-respˡ-≃ (flip-≃ eqL) cross
         p2 : _<ᵘ_ (toℚᵘ (combFrac N d t))
                     (toℚᵘ (fromℚᵘ (rawR k)))
         p2 = <-respʳ-≃ (flip-≃ eqR) p1
     in p2)

------------------------------------------------------------------------
-- min/max rearrangement and negation interaction
--
-- 极值重排与取负交互

min-swap : ∀ a b → min a b ≡ min b a
min-swap a b = ≤-antisym
  (≤min (min≤ʳ a b) (min≤ˡ a b))
  (≤min (min≤ʳ b a) (min≤ˡ b a))

max-swap : ∀ a b → max a b ≡ max b a
max-swap a b = ≤-antisym
  (max≤ (≤maxʳ b a) (≤maxˡ b a))
  (max≤ (≤maxʳ a b) (≤maxˡ a b))

min-min-swap : ∀ a b c d →
  min (min a b) (min c d) ≡ min (min c d) (min a b)
min-min-swap a b c d = min-swap (min a b) (min c d)

max-max-swap : ∀ a b c d →
  max (max a b) (max c d) ≡ max (max c d) (max a b)
max-max-swap a b c d = max-swap (max a b) (max c d)

min-neg : ∀ a b → min (neg a) (neg b) ≡ neg (max a b)
min-neg a b = ≤-antisym upper lower
  where
    lower : neg (max a b) ≤ min (neg a) (neg b)
    lower = ≤min (neg-antimono-≤ (≤maxˡ a b))
                 (neg-antimono-≤ (≤maxʳ a b))

    upper : min (neg a) (neg b) ≤ neg (max a b)
    upper with max-eq a b
    ... | inj₁ max≡a =
          subst (λ z → min (neg a) (neg b) ≤ neg z) (sym max≡a)
                (min≤ˡ (neg a) (neg b))
    ... | inj₂ max≡b =
          subst (λ z → min (neg a) (neg b) ≤ neg z) (sym max≡b)
                (min≤ʳ (neg a) (neg b))

max-neg : ∀ a b → max (neg a) (neg b) ≡ neg (min a b)
max-neg a b = ≤-antisym upper lower
  where
    upper : max (neg a) (neg b) ≤ neg (min a b)
    upper = max≤ (neg-antimono-≤ (min≤ˡ a b))
                 (neg-antimono-≤ (min≤ʳ a b))

    lower : neg (min a b) ≤ max (neg a) (neg b)
    lower with min-eq a b
    ... | inj₁ min≡a =
          subst (λ z → neg z ≤ max (neg a) (neg b)) (sym min≡a)
                (≤maxˡ (neg a) (neg b))
    ... | inj₂ min≡b =
          subst (λ z → neg z ≤ max (neg a) (neg b)) (sym min≡b)
                (≤maxʳ (neg a) (neg b))
