------------------------------------------------------------------------
-- Continuity of interval reals
--
-- 区间实数的连续性
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module Real.Interval.Continuity where

open import Data.Nat using (ℕ; suc) renaming (_*_ to _ℕ*_)
open import Data.Product using (Σ; _,_; _×_; proj₁; proj₂)
open import Data.Rational using (ℚ; 0ℚ; _+_; _-_; _<_) renaming (-_ to neg)
open import Data.Rational.Properties using
  (+-assoc; +-comm; +-identityˡ; +-identityʳ; +-inverseˡ; +-inverseʳ ; +-monoˡ-<
  ; neg-distrib-+)
open import Relation.Binary.PropositionalEquality using
  (_≡_; sym; trans; cong; cong₂; subst; subst₂; module ≡-Reasoning)
open ≡-Reasoning

open import Base.RationalRing using (neg-involutive; +interchange)
open import Real using (ε; 0<ε; ε-half)
open import Real.Archimedean using (ε-archimedean)
open import Real.IntervalEquiv using (l; u; width; centre)
open import Real.Interval using (RealI; embedℚ; δ)
open import Real.Interval.Arith using (0ℝ; _+ℝ_; _-ℝ_; negℝ)
open import Real.Interval.ArithLaws using
  (+ℝ-comm; +ℝ-identityˡ; negℝ-negℝ; negℝ-0ℝ)
open import Real.Interval.DensityArch using (width-0ℝ)
open import Real.Interval.Embed using (embedℚ-+; embedℚ-cong; centre-embedℚ)
open import Real.Interval.Equiv using (_≈ℝ_; ≈ℝ-sym; ≈ℝ-refl; ≈ℝ-trans)
open import Real.Interval.Kit using (≈ℝ-of-eq)
open import Real.Interval.Mul.Order using (≈-neg; ≈-<-respʳ; +ℝ-cong; u-dyadic-0)
open import Real.Interval.NegLaws using (negℝ-+-distrib)
open import Real.Interval.Node using (l-dyadic; u-dyadic; centre-add; centre-neg)
open import Real.Interval.Order using (_<ℝ_; <-trans)
open import Real.Interval.OrderLaws using (<-+mono; <-neg; ≈-<-resp; width-below)

------------------------------------------------------------------------
-- Neighbourhood and the modulus definition
--
-- 邻域与模数定义

-- The two-sided open neighbourhood of radius d.
--
-- 半径为 d 的双侧开邻域。
Close : ℚ → RealI → RealI → Set
Close d x y = (x -ℝ embedℚ d <ℝ y) × (y <ℝ x +ℝ embedℚ d)

-- Pointwise continuity with an explicit modulus.
--
-- 带显式模数的点连续。
ContinuousAt : (RealI → RealI) → RealI → Set
ContinuousAt f x =
  ∀ k → Σ ℚ (λ d → (0ℚ < d) ×
    ∀ y → Close d x y → Close (ε k) (f x) (f y))

-- Global continuity.
--
-- 全局连续。
Continuous : (RealI → RealI) → Set
Continuous f = ∀ x → ContinuousAt f x

-- Joint continuity of a binary operation.
--
-- 二元运算的联合连续。
ContinuousAt₂ : (RealI → RealI → RealI) → RealI → RealI → Set
ContinuousAt₂ f x y =
  ∀ k → Σ ℚ (λ d → (0ℚ < d) ×
    ∀ x' y' → Close d x x' → Close d y y' →
      Close (ε k) (f x y) (f x' y'))

-- Global joint continuity.
--
-- 全局联合连续。
Continuous₂ : (RealI → RealI → RealI) → Set
Continuous₂ f = ∀ x y → ContinuousAt₂ f x y

------------------------------------------------------------------------
-- Centre of a difference
--
-- 差的中心

-- The centre of a difference is the difference of centres.
--
-- 差的中心等于中心之差。
centre-sub : (x y : RealI) (n : ℕ) →
  centre (x -ℝ y) n ≡ centre x n - centre y n
centre-sub x y n = begin
  centre (x -ℝ y) n
    ≡⟨ centre-add x (negℝ y) n ⟩
  centre x n + centre (negℝ y) n
    ≡⟨ cong (centre x n +_) (centre-neg y n) ⟩
  centre x n + neg (centre y n)
    ∎

-- The centre of a difference against an embedded rational.
--
-- 与嵌入有理数作差后的中心。
centre-sub-emb : (x : RealI) (q : ℚ) (n : ℕ) →
  centre (x -ℝ embedℚ q) n ≡ centre x n - q
centre-sub-emb x q n =
  trans (centre-sub x (embedℚ q) n)
        (cong (centre x n +_) (cong neg (centre-embedℚ q n)))

-- The centre of a sum with an embedded rational.
--
-- 与嵌入有理数求和后的中心。
centre-add-emb : (x : RealI) (q : ℚ) (n : ℕ) →
  centre (x +ℝ embedℚ q) n ≡ centre x n + q
centre-add-emb x q n =
  trans (centre-add x (embedℚ q) n) (cong (centre x n +_) (centre-embedℚ q n))

------------------------------------------------------------------------
-- Shifting a neighbourhood by a constant, and splitting a sum
--
-- 邻域的平移，以及和的分拆

-- Subtracting a rational then adding a constant is reordered.
--
-- 先减有理数再加常数可重排。
sub-shift : (x c : RealI) (q : ℚ) →
  (x +ℝ c) -ℝ embedℚ q ≈ℝ (x -ℝ embedℚ q) +ℝ c
sub-shift x c q = ≈ℝ-of-eq _ _ λ n →
  begin
    centre ((x +ℝ c) -ℝ embedℚ q) n
      ≡⟨ centre-sub (x +ℝ c) (embedℚ q) n ⟩
    centre (x +ℝ c) n - centre (embedℚ q) n
      ≡⟨ cong₂ _-_
           (centre-add x c n)
           (centre-embedℚ q n) ⟩
    (centre x n + centre c n) - q
      ≡⟨ +-assoc (centre x n) (centre c n) (neg q) ⟩
    centre x n + (centre c n + neg q)
      ≡⟨ cong (centre x n +_) (+-comm (centre c n) (neg q)) ⟩
    centre x n + (neg q + centre c n)
      ≡⟨ sym (+-assoc (centre x n) (neg q) (centre c n)) ⟩
    (centre x n + neg q) + centre c n
      ≡⟨ cong (λ z → z + centre c n) (sym (centre-sub-emb x q n)) ⟩
    centre (x -ℝ embedℚ q) n + centre c n
      ≡⟨ sym (centre-add (x -ℝ embedℚ q) c n) ⟩
    centre ((x -ℝ embedℚ q) +ℝ c) n
      ∎

-- Adding a rational then a constant is reordered.
--
-- 先加有理数再加常数可重排。
add-shift : (x c : RealI) (q : ℚ) →
  (x +ℝ c) +ℝ embedℚ q ≈ℝ (x +ℝ embedℚ q) +ℝ c
add-shift x c q = ≈ℝ-of-eq _ _ λ n →
  begin
    centre ((x +ℝ c) +ℝ embedℚ q) n
      ≡⟨ centre-add (x +ℝ c) (embedℚ q) n ⟩
    centre (x +ℝ c) n + centre (embedℚ q) n
      ≡⟨ cong₂ _+_ (centre-add x c n) (centre-embedℚ q n) ⟩
    (centre x n + centre c n) + q
      ≡⟨ +-assoc (centre x n) (centre c n) q ⟩
    centre x n + (centre c n + q)
      ≡⟨ cong (centre x n +_) (+-comm (centre c n) q) ⟩
    centre x n + (q + centre c n)
      ≡⟨ sym (+-assoc (centre x n) q (centre c n)) ⟩
    (centre x n + q) + centre c n
      ≡⟨ cong (λ z → z + centre c n) (sym (centre-add-emb x q n)) ⟩
    centre (x +ℝ embedℚ q) n + centre c n
      ≡⟨ sym (centre-add (x +ℝ embedℚ q) c n) ⟩
    centre ((x +ℝ embedℚ q) +ℝ c) n
      ∎

-- Subtracting a sum of embeddings distributes over the sum.
--
-- 减去两个嵌入之和等于分别相减再相加。
sub-add : (x y : RealI) (q r : ℚ) →
  (x +ℝ y) -ℝ (embedℚ q +ℝ embedℚ r) ≈ℝ
  (x -ℝ embedℚ q) +ℝ (y -ℝ embedℚ r)
sub-add x y q r = ≈ℝ-of-eq _ _ λ n →
  begin
    centre ((x +ℝ y) -ℝ (embedℚ q +ℝ embedℚ r)) n
      ≡⟨ centre-sub (x +ℝ y) (embedℚ q +ℝ embedℚ r) n ⟩
    centre (x +ℝ y) n - centre (embedℚ q +ℝ embedℚ r) n
      ≡⟨ cong₂ _-_
           (centre-add x y n)
           (trans (centre-add (embedℚ q) (embedℚ r) n)
                  (cong₂ _+_ (centre-embedℚ q n) (centre-embedℚ r n))) ⟩
    (centre x n + centre y n) - (q + r)
      ≡⟨ cong ((centre x n + centre y n) +_) (neg-distrib-+ q r) ⟩
    (centre x n + centre y n) + (neg q + neg r)
      ≡⟨ +-assoc (centre x n) (centre y n) (neg q + neg r) ⟩
    centre x n + (centre y n + (neg q + neg r))
      ≡⟨ cong (centre x n +_) (sym (+-assoc (centre y n) (neg q) (neg r))) ⟩
    centre x n + ((centre y n + neg q) + neg r)
      ≡⟨ cong (λ z → centre x n + (z + neg r))
                (+-comm (centre y n) (neg q)) ⟩
    centre x n + ((neg q + centre y n) + neg r)
      ≡⟨ cong (centre x n +_) (+-assoc (neg q) (centre y n) (neg r)) ⟩
    centre x n + (neg q + (centre y n + neg r))
      ≡⟨ sym (+-assoc (centre x n) (neg q) (centre y n + neg r)) ⟩
    (centre x n + neg q) + (centre y n + neg r)
      ≡⟨ cong₂ _+_
           (sym (centre-sub-emb x q n))
           (sym (centre-sub-emb y r n)) ⟩
    centre (x -ℝ embedℚ q) n + centre (y -ℝ embedℚ r) n
      ≡⟨ sym (centre-add (x -ℝ embedℚ q) (y -ℝ embedℚ r) n) ⟩
    centre ((x -ℝ embedℚ q) +ℝ (y -ℝ embedℚ r)) n
      ∎

-- Adding a sum of embeddings distributes over the sum.
--
-- 加上两个嵌入之和等于分别相加再相加。
add-split : (x y : RealI) (q r : ℚ) →
  (x +ℝ y) +ℝ (embedℚ q +ℝ embedℚ r) ≈ℝ
  (x +ℝ embedℚ q) +ℝ (y +ℝ embedℚ r)
add-split x y q r = ≈ℝ-of-eq _ _ λ n →
  begin
    centre ((x +ℝ y) +ℝ (embedℚ q +ℝ embedℚ r)) n
      ≡⟨ centre-add (x +ℝ y) (embedℚ q +ℝ embedℚ r) n ⟩
    centre (x +ℝ y) n + centre (embedℚ q +ℝ embedℚ r) n
      ≡⟨ cong₂ _+_
           (centre-add x y n)
           (trans (centre-add (embedℚ q) (embedℚ r) n)
                  (cong₂ _+_ (centre-embedℚ q n) (centre-embedℚ r n))) ⟩
    (centre x n + centre y n) + (q + r)
      ≡⟨ +-assoc (centre x n) (centre y n) (q + r) ⟩
    centre x n + (centre y n + (q + r))
      ≡⟨ cong (centre x n +_) (sym (+-assoc (centre y n) q r)) ⟩
    centre x n + ((centre y n + q) + r)
      ≡⟨ cong (λ z → centre x n + (z + r)) (+-comm (centre y n) q) ⟩
    centre x n + ((q + centre y n) + r)
      ≡⟨ cong (centre x n +_) (+-assoc q (centre y n) r) ⟩
    centre x n + (q + (centre y n + r))
      ≡⟨ sym (+-assoc (centre x n) q (centre y n + r)) ⟩
    (centre x n + q) + (centre y n + r)
      ≡⟨ cong₂ _+_
           (sym (centre-add-emb x q n))
           (sym (centre-add-emb y r n)) ⟩
    centre (x +ℝ embedℚ q) n + centre (y +ℝ embedℚ r) n
      ≡⟨ sym (centre-add (x +ℝ embedℚ q) (y +ℝ embedℚ r) n) ⟩
    centre ((x +ℝ embedℚ q) +ℝ (y +ℝ embedℚ r)) n
      ∎

------------------------------------------------------------------------
-- The embedding of a positive rational is a positive real
--
-- 正有理数的嵌入是正实数

-- The width of 0ℝ is twice the dyadic tolerance.
--
-- 0ℝ 的层宽是二进容差的两倍。
width-0ℝ' : ∀ m → width 0ℝ m ≡ δ m + δ m
width-0ℝ' m = width-0ℝ m

-- A positive rational embeds to a positive real.
--
-- 正有理数的嵌入是正实数。
0<embedℚ : (q : ℚ) → 0ℚ < q → 0ℝ <ℝ embedℚ q
0<embedℚ q q>0 =
  let n , w = width-below 0ℝ q q>0

      w' : δ n + δ n < q
      w' = subst (λ z → z < q) (width-0ℝ' n) w

      shift : (δ n + δ n) + neg (δ n) < q + neg (δ n)
      shift = +-monoˡ-< (neg (δ n)) w'

      collapse : (δ n + δ n) + neg (δ n) ≡ δ n
      collapse = begin
        (δ n + δ n) + neg (δ n)
          ≡⟨ +-assoc (δ n) (δ n) (neg (δ n)) ⟩
        δ n + (δ n + neg (δ n))
          ≡⟨ cong (δ n +_) (+-inverseʳ (δ n)) ⟩
        δ n + 0ℚ
          ≡⟨ +-identityʳ (δ n) ⟩
        δ n
          ∎

      h₁ : δ n < q + neg (δ n)
      h₁ = subst (λ z → z < (q + neg (δ n))) collapse shift

      h₂ : δ n < neg (δ n) + q
      h₂ = subst (λ z → δ n < z) (+-comm q (neg (δ n))) h₁

      goal : u 0ℝ n < l (embedℚ q) n
      goal = subst₂ (λ a b → a < b)
               (sym (u-dyadic-0 n)) (sym (l-dyadic q n)) h₂
  in n , goal

-- Negating a positive embedding gives a negative real.
--
-- 正嵌入取负得到负实数。
neg-embed-<0 : (q : ℚ) → 0ℚ < q → negℝ (embedℚ q) <ℝ 0ℝ
neg-embed-<0 q q>0 =
  ≈-<-respʳ negℝ-0ℝ (<-neg 0ℝ (embedℚ q) (0<embedℚ q q>0))

------------------------------------------------------------------------
-- A point is inside its own every neighbourhood
--
-- 任一点落在自己的每个邻域内

-- Every point lies in its own open neighbourhood.
--
-- 任一点落在以自身为中心的开邻域内。
Close-self : (q : ℚ) (0<q : 0ℚ < q) (x : RealI) → Close q x x
Close-self q q>0 x = lower , upper
  where
    lower : x -ℝ embedℚ q <ℝ x
    lower =
      ≈-<-respʳ (+ℝ-identityˡ x)
        (≈-<-resp (≈ℝ-sym (+ℝ-comm x (negℝ (embedℚ q))))
          (<-+mono (negℝ (embedℚ q)) 0ℝ x (neg-embed-<0 q q>0)))

    upper : x <ℝ x +ℝ embedℚ q
    upper =
      ≈-<-respʳ (+ℝ-comm (embedℚ q) x)
        (≈-<-resp (+ℝ-identityˡ x)
          (<-+mono 0ℝ (embedℚ q) x (0<embedℚ q q>0)))

------------------------------------------------------------------------
-- The constants, the identity, negation, translation, and addition
--
-- 常函数、恒等、取负、平移与加法

-- Constant functions are continuous.
--
-- 常函数连续。
continuous-const : (c : RealI) → Continuous (λ _ → c)
continuous-const c x k =
  ε k , 0<ε k , λ y _ → Close-self (ε k) (0<ε k) c

-- The identity is continuous.
--
-- 恒等函数连续。
continuous-id : Continuous (λ x → x)
continuous-id x k = ε k , 0<ε k , λ y h → h

-- Negation maps a neighbourhood to a neighbourhood.
--
-- 取负把一个邻域映为邻域。
neg-close : (k : ℕ) (x y : RealI) → Close (ε k) x y →
  Close (ε k) (negℝ x) (negℝ y)
neg-close k x y (h₁ , h₂) = lower , upper
  where
    lower : negℝ x -ℝ embedℚ (ε k) <ℝ negℝ y
    lower =
      ≈-<-resp (negℝ-+-distrib x (embedℚ (ε k)))
        (<-neg y (x +ℝ embedℚ (ε k)) h₂)

    upper : negℝ y <ℝ negℝ x +ℝ embedℚ (ε k)
    upper =
      ≈-<-respʳ
        (≈ℝ-trans (negℝ-+-distrib x (negℝ (embedℚ (ε k))))
          (+ℝ-cong ≈ℝ-refl (negℝ-negℝ (embedℚ (ε k)))))
        (<-neg (x -ℝ embedℚ (ε k)) y h₁)

-- Negation is continuous.
--
-- 取负连续。
continuous-neg : Continuous (λ x → negℝ x)
continuous-neg x k = ε k , 0<ε k , λ y h → neg-close k x y h

-- Translation is continuous.
--
-- 平移连续。
continuous-translate : (c : RealI) → Continuous (λ x → x +ℝ c)
continuous-translate c x k =
  ε k , 0<ε k , λ y (h₁ , h₂) →
    ≈-<-resp (≈ℝ-sym (sub-shift x c (ε k)))
      (<-+mono (x -ℝ embedℚ (ε k)) y c h₁)
    ,
    ≈-<-respʳ (≈ℝ-sym (add-shift x c (ε k)))
      (<-+mono y (x +ℝ embedℚ (ε k)) c h₂)

------------------------------------------------------------------------
-- Joint continuity of addition
--
-- 加法的联合连续

-- Addition is jointly continuous.
--
-- 加法联合连续。
continuous-+-at : ∀ x y → ContinuousAt₂ (λ a b → a +ℝ b) x y
continuous-+-at x y k =
  d , 0<ε (suc (2 ℕ* k)) , body
  where
    d : ℚ
    d = ε (suc (2 ℕ* k))

    e : RealI
    e = embedℚ d

    E : RealI
    E = embedℚ (ε k)

    emb-eq : E ≈ℝ e +ℝ e
    emb-eq =
      ≈ℝ-trans (≈ℝ-sym (embedℚ-cong (ε-half k))) (embedℚ-+ d d)

    body : ∀ x' y' → Close d x x' → Close d y y' →
      Close (ε k) (x +ℝ y) (x' +ℝ y')
    body x' y' (hx₁ , hx₂) (hy₁ , hy₂) = lower , upper
      where
        s₁ : (x -ℝ e) +ℝ (y -ℝ e) <ℝ x' +ℝ (y -ℝ e)
        s₁ = <-+mono (x -ℝ e) x' (y -ℝ e) hx₁

        s₂ : x' +ℝ (y -ℝ e) <ℝ x' +ℝ y'
        s₂ =
          ≈-<-respʳ (+ℝ-comm y' x')
            (≈-<-resp (+ℝ-comm (y -ℝ e) x')
              (<-+mono (y -ℝ e) y' x' hy₁))

        s₃ : (x -ℝ e) +ℝ (y -ℝ e) <ℝ x' +ℝ y'
        s₃ = <-trans s₁ s₂

        r₁ : (x +ℝ y) -ℝ (e +ℝ e) ≈ℝ (x -ℝ e) +ℝ (y -ℝ e)
        r₁ = sub-add x y d d

        r₂ : (x +ℝ y) -ℝ E ≈ℝ (x +ℝ y) -ℝ (e +ℝ e)
        r₂ = +ℝ-cong ≈ℝ-refl (≈-neg emb-eq)

        lower : (x +ℝ y) -ℝ E <ℝ x' +ℝ y'
        lower = ≈-<-resp (≈ℝ-sym (≈ℝ-trans r₂ r₁)) s₃

        t₁ : x' +ℝ y' <ℝ (x +ℝ e) +ℝ y'
        t₁ = <-+mono x' (x +ℝ e) y' hx₂

        t₂ : (x +ℝ e) +ℝ y' <ℝ (x +ℝ e) +ℝ (y +ℝ e)
        t₂ =
          ≈-<-respʳ (+ℝ-comm (y +ℝ e) (x +ℝ e))
            (≈-<-resp (+ℝ-comm y' (x +ℝ e))
              (<-+mono y' (y +ℝ e) (x +ℝ e) hy₂))

        t₃ : x' +ℝ y' <ℝ (x +ℝ e) +ℝ (y +ℝ e)
        t₃ = <-trans t₁ t₂

        u₁ : (x +ℝ y) +ℝ (e +ℝ e) ≈ℝ (x +ℝ e) +ℝ (y +ℝ e)
        u₁ = add-split x y d d

        u₂ : (x +ℝ y) +ℝ E ≈ℝ (x +ℝ y) +ℝ (e +ℝ e)
        u₂ = +ℝ-cong ≈ℝ-refl emb-eq

        upper : x' +ℝ y' <ℝ (x +ℝ y) +ℝ E
        upper =
          ≈-<-respʳ (≈ℝ-trans (≈ℝ-sym u₁) (≈ℝ-sym u₂)) t₃

-- Global joint continuity of addition.
--
-- 加法的全局联合连续。
continuous-+ : Continuous₂ (λ a b → a +ℝ b)
continuous-+ = continuous-+-at

------------------------------------------------------------------------
-- Rational bookkeeping
--
-- 有理数记账

-- Rearrangement of an additive inverse.
--
-- 加法逆元的重排。
sub-add-cancel : (a b : ℚ) → (a + neg b) + b ≡ a
sub-add-cancel a b = begin
  (a + neg b) + b
    ≡⟨ +-assoc a (neg b) b ⟩
  a + (neg b + b)
    ≡⟨ cong (a +_) (+-inverseˡ b) ⟩
  a + 0ℚ
    ≡⟨ +-identityʳ a ⟩
  a
    ∎

-- Cancellation of the double leading term.
--
-- 消去双重首项。
shift-cancel : (a b : ℚ) → ((a + a) + b) + neg a ≡ a + b
shift-cancel a b = begin
  ((a + a) + b) + neg a
    ≡⟨ +-assoc (a + a) b (neg a) ⟩
  (a + a) + (b + neg a)
    ≡⟨ cong ((a + a) +_) (+-comm b (neg a)) ⟩
  (a + a) + (neg a + b)
    ≡⟨ +-assoc a a (neg a + b) ⟩
  a + (a + (neg a + b))
    ≡⟨ cong (a +_) (sym (+-assoc a (neg a) b)) ⟩
  a + ((a + neg a) + b)
    ≡⟨ cong (a +_) (cong (_+ b) (+-inverseʳ a)) ⟩
  a + (0ℚ + b)
    ≡⟨ cong (a +_) (+-identityˡ b) ⟩
  a + b
    ∎

------------------------------------------------------------------------
-- The width of an embedded rational is twice the layer width
--
-- 嵌入有理点的层宽是层宽的两倍

-- The layer width of an embedded rational.
--
-- 嵌入有理点的层宽。
width-emb : (p : ℚ) (n : ℕ) → width (embedℚ p) n ≡ δ n + δ n
width-emb p n = begin
  width (embedℚ p) n
    ≡⟨ cong₂ _-_ (u-dyadic p n) (l-dyadic p n) ⟩
  (δ n + p) - (neg (δ n) + p)
    ≡⟨ cong ((δ n + p) +_) (neg-distrib-+ (neg (δ n)) p) ⟩
  (δ n + p) + (neg (neg (δ n)) + neg p)
    ≡⟨ cong (λ z → (δ n + p) + (z + neg p)) (neg-involutive (δ n)) ⟩
  (δ n + p) + (δ n + neg p)
    ≡⟨ +interchange (δ n) p (δ n) (neg p) ⟩
  (δ n + δ n) + (p + neg p)
    ≡⟨ cong ((δ n + δ n) +_) (+-inverseʳ p) ⟩
  (δ n + δ n) + 0ℚ
    ≡⟨ +-identityʳ (δ n + δ n) ⟩
  δ n + δ n
    ∎

------------------------------------------------------------------------
-- The embedding is strictly monotone
--
-- 嵌入是严格单调的

-- The rational embedding preserves strict order.
--
-- 有理嵌入保持严格序。
embedℚ-mono : (p q : ℚ) → p < q → embedℚ p <ℝ embedℚ q
embedℚ-mono p q p<q =
  let qp>0 : 0ℚ < q - p
      qp>0 = subst (λ z → z < q + neg p) (+-inverseʳ p) (+-monoˡ-< (neg p) p<q)

      n , w = width-below (embedℚ p) (q - p) qp>0

      w' : δ n + δ n < q - p
      w' = subst (λ z → z < q - p) (width-emb p n) w

      addp : (δ n + δ n) + p < (q + neg p) + p
      addp = +-monoˡ-< p w'

      h₀ : (δ n + δ n) + p < q
      h₀ = subst (λ z → (δ n + δ n) + p < z) (sub-add-cancel q p) addp

      h₁ : ((δ n + δ n) + p) + neg (δ n) < q + neg (δ n)
      h₁ = +-monoˡ-< (neg (δ n)) h₀

      h₂ : δ n + p < q + neg (δ n)
      h₂ = subst (λ z → z < q + neg (δ n)) (shift-cancel (δ n) p) h₁

      h₃ : δ n + p < neg (δ n) + q
      h₃ = subst (λ z → δ n + p < z) (+-comm q (neg (δ n))) h₂

      goal : u (embedℚ p) n < l (embedℚ q) n
      goal = subst₂ (λ a b → a < b)
               (sym (u-dyadic p n)) (sym (l-dyadic q n)) h₃
  in n , goal

------------------------------------------------------------------------
-- Widening a neighbourhood radius
--
-- 放大邻域半径

-- A smaller neighbourhood is contained in a larger one.
--
-- 较小的邻域包含于较大的邻域中。
close-mono : (d d' : ℚ) (x y : RealI) → d < d' → Close d x y → Close d' x y
close-mono d d' x y d<d' (h₁ , h₂) =
  let em : embedℚ d <ℝ embedℚ d'
      em = embedℚ-mono d d' d<d'

      nl : negℝ (embedℚ d') <ℝ negℝ (embedℚ d)
      nl = <-neg (embedℚ d) (embedℚ d') em

      addx : negℝ (embedℚ d') +ℝ x <ℝ negℝ (embedℚ d) +ℝ x
      addx = <-+mono (negℝ (embedℚ d')) (negℝ (embedℚ d)) x nl

      h₁' : negℝ (embedℚ d) +ℝ x <ℝ y
      h₁' = ≈-<-resp (+ℝ-comm x (negℝ (embedℚ d))) h₁

      lo : negℝ (embedℚ d') +ℝ x <ℝ y
      lo = <-trans addx h₁'

      lower : x -ℝ embedℚ d' <ℝ y
      lower = ≈-<-resp (≈ℝ-sym (+ℝ-comm x (negℝ (embedℚ d')))) lo

      adds : embedℚ d +ℝ x <ℝ embedℚ d' +ℝ x
      adds = <-+mono (embedℚ d) (embedℚ d') x em

      adds' : x +ℝ embedℚ d <ℝ embedℚ d' +ℝ x
      adds' = ≈-<-resp (+ℝ-comm (embedℚ d) x) adds

      up : x +ℝ embedℚ d <ℝ x +ℝ embedℚ d'
      up = ≈-<-respʳ (+ℝ-comm (embedℚ d') x) adds'

      upper : y <ℝ x +ℝ embedℚ d'
      upper = <-trans h₂ up
  in lower , upper

------------------------------------------------------------------------
-- Composition
--
-- 复合

-- Composition of continuous maps is continuous.
--
-- 连续映射的复合连续。
continuous-comp : (g f : RealI → RealI) →
  Continuous g → Continuous f → Continuous (λ x → g (f x))
continuous-comp g f cg cf x k =
  let d , pd = cg (f x) k
      j , ej<d = ε-archimedean d (proj₁ pd)
      e , pe = cf x j
  in e , proj₁ pe ,
     λ y cl →
       proj₂ pd (f y) (close-mono (ε j) d (f x) (f y) ej<d (proj₂ pe y cl))

------------------------------------------------------------------------
-- Derived closures
--
-- 导出的闭合性

-- Negating a continuous map keeps continuity.
--
-- 连续映射取负仍连续。
continuous-neg-comp : (f : RealI → RealI) →
  Continuous f → Continuous (λ x → negℝ (f x))
continuous-neg-comp f cf =
  continuous-comp (λ x → negℝ x) f continuous-neg cf

-- Shifting the values of a continuous map keeps continuity.
--
-- 连续映射的值整体平移仍连续。
continuous-translate-comp : (c : RealI) (f : RealI → RealI) →
  Continuous f → Continuous (λ x → f x +ℝ c)
continuous-translate-comp c f cf =
  continuous-comp (λ x → x +ℝ c) f (continuous-translate c) cf
