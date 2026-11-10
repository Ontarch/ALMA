------------------------------------------------------------------------
-- Invertibility entails apartness
--
-- 可逆性蕴含分离性
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module Real.Interval.ApartnessInvertible where

open import Data.Empty using (⊥-elim)
open import Data.Nat using (ℕ; zero; suc; _∸_; _^_; z≤n; s≤s)
  renaming (_*_ to _ℕ*_; _+_ to _ℕ+_; _<_ to _ℕ<_; _≤_ to _ℕ≤_; _≥_ to _ℕ≥_)
open import Data.Nat.Properties using (m≤m⊔n; m≤n⊔m; *-suc; ^-monoʳ-≤)
  renaming (<⇒≤ to ℕ<⇒≤)
open import Data.Product using (Σ; _×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_]′)
open import Data.Rational using
  (ℚ; 0ℚ; 1ℚ; _+_; _-_; _*_; _<_; _≤_; _⊓_; ∣_∣; _÷_; 1/_) renaming (-_ to neg)
open import Data.Rational.Base using (positive; nonNegative; Positive; NonZero)
open import Data.Rational.Properties using
  (+-identityˡ; +-identityʳ; +-inverseˡ; +-inverseʳ; +-comm; +-assoc; ≤-trans
  ; *-identityˡ; *-identityʳ; *-assoc; *-comm; *-distribʳ-+; *-zeroˡ; <⇒≤
  ; *-inverseˡ; *-inverseʳ; +-mono-<; +-monoˡ-<; +-mono-≤; neg-distrib-+
  ; ∣-p∣≡∣p∣; *-monoʳ-<-pos; *-monoˡ-<-pos; +-monoʳ-<; neg-distribˡ-*
  ; ≤-refl; *-distribˡ-+; +-mono-≤-<; 1/-involutive; neg-antimono-<
  ; neg-antimono-≤; *-monoʳ-≤-nonNeg; <-trans; <-irrefl; ≤-reflexive
  ; ≤-<-trans; <-≤-trans; p⊓q≤p; p⊓q≤q; <-cmp; 1/pos⇒pos; pos⇒nonNeg
  ; pos⇒nonZero; positive⁻¹; pos*pos⇒pos)
open import Function.Base using (case_of_)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; cong; cong₂; sym; trans; subst; subst₂; module ≡-Reasoning)
open ≡-Reasoning
open import Relation.Nullary using (¬_)
open import Relation.Binary.Definitions using (tri<; tri≈; tri>)

open import Base.RationalRing using (+interchange)
open import Real using
  (ε; 0<ε; half; 2ℚ; 2ℚ≡1+1; 0<embed; embed; embed-mono-<; embed-mono-≤)
open import Real.Interval using (RealI; dyadic; δ; δ-pos; δ-half; δs≤δ; embedℚ)
open import Real.IntervalEquiv using
  (node; l; u; width; centre; width-n; pow2; posPow2; denom-eq; recipPow2
  ; 0<width; n<2^n; 1≤2^n)
open import Real.Interval.Arith using (0ℝ; 1ℝ; _+ℝ_; negℝ; _-ℝ_)
open import Real.Interval.Mul using (_*ℝ_)
open import Real.Interval.Mul.Order using (δ-mono; u-dyadic-0)
open import Real.Interval.Order using (_<ℝ_; l-mono'; u-mono')
open import Real.Interval.AbsTriangle using (l0ℝ)
open import Real.Interval.Apartness using (_#ℝ_)
open import Real.Interval.Equiv using (_≈ℝ_)
open import Real.Interval.Node using
  (l-dyadic; u-dyadic; l-hom; u-hom; node-*ℝ; l-neg; u-neg; 0≤width-n)
open import Real.Interval.Rational using (r≤|r|; pos-diff; negsub; suc∸1)
open import Real.Interval.Kit using
  (0<half; 2ℚ*half≡1; half+half≡1; add-self; strict-recip; recipPow2-mono)
open import Real.Interval.Embed using (centre-embedℚ)
open import Real.Interval.DensityArch using (archimedean)
open import Real.Interval.Reasoning using (begin≤_; _≈⟨_⟩_; _≤⟨_⟩_; _≤∎)

------------------------------------------------------------------------
-- Layer commutation of multiplication
--
-- 乘法的层交换
--
-- RealI.next (x *ℝ y) steps two layers in each factor, so the node
-- functor commutes with _*ℝ_ at doubled depth.
--
-- 后继在每个因子上走两层，因此节点函子在双倍深度处与乘法交换。

node-2 : (r : RealI) (n : ℕ) →
  node r (2 ℕ* suc n) ≡ RealI.next (RealI.next (node r (2 ℕ* n)))
node-2 r n =
  begin
    node r (2 ℕ* suc n)
  ≡⟨ cong (node r) (*-suc 2 n) ⟩
    node r (2 ℕ+ 2 ℕ* n)
  ≡⟨ refl ⟩
    RealI.next (RealI.next (node r (2 ℕ* n)))
  ∎

-- Lower endpoint of a product as the meet of the four corner products.
--
-- 乘积下端点即四个角点乘积的下确界。
l-mul4 : (x y : RealI) (n : ℕ) →
  l (x *ℝ y) n
    ≡ ((l x (2 ℕ* n) * l y (2 ℕ* n)) ⊓ (l x (2 ℕ* n) * u y (2 ℕ* n)))
      ⊓ ((u x (2 ℕ* n) * l y (2 ℕ* n)) ⊓ (u x (2 ℕ* n) * u y (2 ℕ* n)))
l-mul4 x y n =
  begin
    l (x *ℝ y) n
  ≡⟨ refl ⟩
    RealI.l (node (x *ℝ y) n)
  ≡⟨ cong RealI.l (node-*ℝ x y n) ⟩
    RealI.l (node x (2 ℕ* n) *ℝ node y (2 ℕ* n))
  ≡⟨ refl ⟩
    ((l x (2 ℕ* n) * l y (2 ℕ* n)) ⊓ (l x (2 ℕ* n) * u y (2 ℕ* n)))
      ⊓ ((u x (2 ℕ* n) * l y (2 ℕ* n)) ⊓ (u x (2 ℕ* n) * u y (2 ℕ* n)))
  ∎

------------------------------------------------------------------------
-- Rational sign lemmas
--
-- 有理数符号引理

-- A positive meet has positive components.
--
-- 正的下确界两个分量均为正。
⊓-pos : {p q : ℚ} → 0ℚ < p ⊓ q → (0ℚ < p) × (0ℚ < q)
⊓-pos {p} {q} h = <-≤-trans h (p⊓q≤p p q) , <-≤-trans h (p⊓q≤q p q)

-- A product of a positive and a positive-product factor is positive.
--
-- 正因子与正乘积：另一因子为正。
pos-prod-pos : {a b : ℚ} → 0ℚ < a → 0ℚ < a * b → 0ℚ < b
pos-prod-pos {a} {b} a>0 ab>0 =
  let ia : ℚ
      ia = 1/_ a {{pos⇒nonZero a {{positive a>0}}}}
      ia-pos : Positive ia
      ia-pos = 1/pos⇒pos a {{positive a>0}}
      s1 : 0ℚ * ia < (a * b) * ia
      s1 = *-monoˡ-<-pos ia {{ia-pos}} ab>0
      s2 : 0ℚ * ia ≡ 0ℚ
      s2 = *-zeroˡ ia
      s3 : (a * b) * ia ≡ b
      s3 =
        begin
          (a * b) * ia
        ≡⟨ *-assoc a b ia ⟩
          a * (b * ia)
        ≡⟨ cong (a *_) (*-comm b ia) ⟩
          a * (ia * b)
        ≡⟨ sym (*-assoc a ia b) ⟩
          (a * ia) * b
        ≡⟨ cong (_* b) (*-inverseʳ a {{pos⇒nonZero a {{positive a>0}}}}) ⟩
          1ℚ * b
        ≡⟨ *-identityˡ b ⟩
          b
        ∎
  in subst (λ z → 0ℚ < z) s3 (subst (λ z → z < (a * b) * ia) s2 s1)

-- A product of a negative and a positive-product factor: the other
-- factor is negative.
--
-- 负因子与正乘积：另一因子为负。
neg-prod-pos : {a b : ℚ} → a < 0ℚ → 0ℚ < a * b → b < 0ℚ
neg-prod-pos {a} {b} a<0 ab>0 = helper
  where
  bad : ¬ (0ℚ ≤ b)
  bad b≥0 =
    <-irrefl refl
      (<-≤-trans ab>0
        (≤-trans
          (*-monoʳ-≤-nonNeg b {{nonNegative b≥0}} (<⇒≤ a<0))
          (≤-reflexive (*-zeroˡ b))))
  helper : b < 0ℚ
  helper = case <-cmp b 0ℚ of λ
    { (tri< lt _ _) → lt
    ; (tri≈ _ eq _) → ⊥-elim (bad (≤-reflexive (sym eq)))
    ; (tri> _ _ gt) → ⊥-elim (bad (<⇒≤ gt))
    }

-- Four positive corner products force the endpoints of the first
-- factor to share a strict sign.
--
-- 四个角点乘积为正迫使第一个因子的端点严格同号。
same-sign : {a b c d : ℚ} →
  0ℚ < a * c → 0ℚ < a * d → 0ℚ < b * c → 0ℚ < b * d →
  (0ℚ < a) ⊎ (b < 0ℚ)
same-sign {a} {b} {c} {d} ac>0 ad>0 bc>0 bd>0 with <-cmp a 0ℚ
... | tri< a<0 _ _ =
      inj₂ (neg-prod-pos {c} {b} c<0
              (subst (0ℚ <_) (*-comm b c) bc>0))
      where
      c<0 : c < 0ℚ
      c<0 = neg-prod-pos {a} {c} a<0 ac>0
... | tri≈ _ a≈0 _ =
      ⊥-elim (<-irrefl refl
        (subst (0ℚ <_) (trans (cong (_* c) a≈0) (*-zeroˡ c)) ac>0))
... | tri> _ _ a>0 = inj₁ a>0

------------------------------------------------------------------------
-- Bounds and the centre
--
-- 端点与中心

-- Division by embed 2 aligns with half.
--
-- 除以 embed 2 与 half 对齐。
div-half : (p : ℚ) → p ÷ embed 2 ≡ p * half
div-half p = refl

-- centre - width/2 = l at every depth.
--
-- 各深度处中心减去半宽等于下端点。
centre-half : (r : RealI) (n : ℕ) →
  centre r n - width r n ÷ embed 2 ≡ l r n
centre-half r n =
  let a = l r n
      b = u r n
      h = half
      s1 : (a + b) * h - (b - a) * h ≡ ((a + b) - (b - a)) * h
      s1 = sym (begin
        ((a + b) - (b - a)) * h
          ≡⟨ *-distribʳ-+ h (a + b) (neg (b - a)) ⟩
        (a + b) * h + (neg (b - a)) * h
          ≡⟨ cong ((a + b) * h +_) (sym (neg-distribˡ-* (b - a) h)) ⟩
        (a + b) * h - (b - a) * h
          ∎)
      s2 : (a + b) - (b - a) ≡ a + a
      s2 = begin
        (a + b) - (b - a)
          ≡⟨ refl ⟩
        (a + b) + neg (b - a)
          ≡⟨ cong ((a + b) +_) (negsub b a) ⟩
        (a + b) + (a - b)
          ≡⟨ refl ⟩
        (a + b) + (a + neg b)
          ≡⟨ +interchange a b a (neg b) ⟩
        (a + a) + (b + neg b)
          ≡⟨ cong ((a + a) +_) (+-inverseʳ b) ⟩
        (a + a) + 0ℚ
          ≡⟨ +-identityʳ (a + a) ⟩
        a + a
        ∎
      s3 : ((a + b) - (b - a)) * h ≡ a
      s3 =
        begin
          ((a + b) - (b - a)) * h
        ≡⟨ cong (_* h) s2 ⟩
          (a + a) * h
        ≡⟨ cong (_* h) (add-self a) ⟩
          (2ℚ * a) * h
        ≡⟨ *-assoc 2ℚ a h ⟩
          2ℚ * (a * h)
        ≡⟨ cong (2ℚ *_) (*-comm a h) ⟩
          2ℚ * (h * a)
        ≡⟨ sym (*-assoc 2ℚ h a) ⟩
          (2ℚ * h) * a
        ≡⟨ cong (_* a) 2ℚ*half≡1 ⟩
          1ℚ * a
        ≡⟨ *-identityˡ a ⟩
          a
        ∎
  in begin
    centre r n - width r n ÷ embed 2
  ≡⟨ refl ⟩
    (a + b) ÷ embed 2 - (b - a) ÷ embed 2
  ≡⟨ cong₂ _-_ (div-half (a + b)) (div-half (b - a)) ⟩
    (a + b) * h - (b - a) * h
  ≡⟨ s1 ⟩
    ((a + b) - (b - a)) * h
  ≡⟨ s3 ⟩
    a
  ∎

-- l ≥ centre - width: the interval stays within width of its centre.
--
-- 下端点不低于中心减宽度：区间保持在中心附近。
l≥centre-width : (r : RealI) (n : ℕ) →
  centre r n - width r n ≤ l r n
l≥centre-width r n =
  let c = centre r n
      w = width r n
      wh = w ÷ embed 2
      w≥0 : 0ℚ ≤ w
      w≥0 = 0≤width-n r n
      wh≥0 : 0ℚ ≤ wh
      wh≥0 =
        *-monoʳ-≤-nonNeg half
          {{pos⇒nonNeg half {{positive 0<half}}}}
          w≥0
      wh≤w : wh ≤ w
      wh≤w =
        begin≤
          wh
            ≈⟨ sym (+-identityʳ wh) ⟩
          wh + 0ℚ
            ≤⟨ +-mono-≤ (≤-refl {wh}) wh≥0 ⟩
          wh + wh
            ≈⟨ begin
                 wh + wh
               ≡⟨ sym (cong₂ _+_ (div-half w) (div-half w)) ⟩
                 w * half + w * half
               ≡⟨ sym (*-distribˡ-+ w half half) ⟩
                 w * (half + half)
               ≡⟨ cong (w *_) half+half≡1 ⟩
                 w * 1ℚ
               ≡⟨ *-identityʳ w ⟩
                 w
               ∎ ⟩
          w
        ≤∎
      step2 : c + neg w ≤ c + neg wh
      step2 = +-mono-≤ (≤-refl {c}) (neg-antimono-≤ wh≤w)
  in ≤-trans
       (≤-trans (≤-reflexive refl) step2)
       (≤-reflexive (centre-half r n))

------------------------------------------------------------------------
-- The dyadic tolerance shrinks to zero
--
-- δ (suc n) * 2 = δ n (δ-half), hence δ n * pow2 n = δ 0 and
-- δ n ≤ δ 0 ÷ pow2 n.  Unboundedness of pow2 (via the Archimedean
-- property of the reals) then yields δ n arbitrarily small.
--
-- dyadic 容差趋于零
--
-- 二进容差随层数减半，故与二的幂相乘后保持不变；而二的幂无界，
-- 因此二进容差可以任意小。

δs*2≡δ : (n : ℕ) → δ (suc n) * 2ℚ ≡ δ n
δs*2≡δ n =
  begin
    δ (suc n) * 2ℚ
  ≡⟨ cong (δ (suc n) *_) (sym 2ℚ≡1+1) ⟩
    δ (suc n) * (1ℚ + 1ℚ)
  ≡⟨ *-distribˡ-+ (δ (suc n)) 1ℚ 1ℚ ⟩
    δ (suc n) * 1ℚ + δ (suc n) * 1ℚ
  ≡⟨ cong₂ _+_ (*-identityʳ (δ (suc n))) (*-identityʳ (δ (suc n))) ⟩
    δ (suc n) + δ (suc n)
  ≡⟨ δ-half n ⟩
    δ n
  ∎

-- pow2 1 = 2.
--
-- pow2 1 = 2。
pow2-1≡2ℚ : pow2 1 ≡ 2ℚ
pow2-1≡2ℚ = refl

δ-pow2 : (n : ℕ) → δ n * pow2 n ≡ δ 0
δ-pow2 zero = *-identityʳ (δ 0)
δ-pow2 (suc n) =
  begin
    δ (suc n) * pow2 (suc n)
  ≡⟨ cong (δ (suc n) *_) (sym (denom-eq n)) ⟩
    δ (suc n) * (pow2 n * pow2 1)
  ≡⟨ sym (*-assoc (δ (suc n)) (pow2 n) (pow2 1)) ⟩
    (δ (suc n) * pow2 n) * pow2 1
  ≡⟨ cong₂ _*_ (*-comm (δ (suc n)) (pow2 n)) refl ⟩
    (pow2 n * δ (suc n)) * pow2 1
  ≡⟨ trans (*-assoc (pow2 n) (δ (suc n)) (pow2 1))
           (cong (pow2 n *_) (begin
             δ (suc n) * pow2 1
           ≡⟨ cong (δ (suc n) *_) pow2-1≡2ℚ ⟩
             δ (suc n) * 2ℚ
           ≡⟨ δs*2≡δ n ⟩
             δ n
           ∎)) ⟩
    pow2 n * δ n
  ≡⟨ *-comm (pow2 n) (δ n) ⟩
    δ n * pow2 n
  ≡⟨ δ-pow2 n ⟩
    δ 0
  ∎

pow2-nz : (n : ℕ) → NonZero (pow2 n)
pow2-nz n = pos⇒nonZero (pow2 n) {{posPow2 n}}

δ≤δ0/pow2 : (n : ℕ) →
  δ n ≤ δ 0 * (1/_ (pow2 n) {{pow2-nz n}})
δ≤δ0/pow2 n = ≤-reflexive (begin
  δ n
    ≡⟨ sym (*-identityʳ (δ n)) ⟩
  δ n * 1ℚ
    ≡⟨ cong (δ n *_) (sym (*-inverseʳ (pow2 n) {{pow2-nz n}})) ⟩
  δ n * (pow2 n * (1/_ (pow2 n) {{pow2-nz n}}))
    ≡⟨ sym (*-assoc (δ n) (pow2 n) (1/_ (pow2 n) {{pow2-nz n}})) ⟩
  (δ n * pow2 n) * (1/_ (pow2 n) {{pow2-nz n}})
    ≡⟨ cong (_* (1/_ (pow2 n) {{pow2-nz n}})) (δ-pow2 n) ⟩
  δ 0 * (1/_ (pow2 n) {{pow2-nz n}})
    ∎)

-- δ is non-increasing along the layers.
--
-- δ 沿层递减（即 δ m ≤ δ n 当 n ≤ m）。
δ-mono-aux : (n k : ℕ) → δ (k ℕ+ n) ≤ δ n
δ-mono-aux n zero    = ≤-refl
δ-mono-aux n (suc k) = ≤-trans (δs≤δ (k ℕ+ n)) (δ-mono-aux n k)

pow2-mono : {n m : ℕ} → n ℕ≤ m → pow2 n ≤ pow2 m
pow2-mono {n} {m} n≤m = embed-mono-≤ (^-monoʳ-≤ 2 n≤m)

-- pow2 is unbounded above the positive rationals (Archimedean).
--
-- pow2 在正有理数之上无界（阿基米德性）。
pow2-arch : (q : ℚ) → 0ℚ < q → Σ ℕ (λ n → q < pow2 n)
pow2-arch q q>0 =
  let (n , x<e) = archimedean (dyadic q 0)
      (k , wk) = x<e
      uq : u (dyadic q 0) k ≡ δ k + q
      uq = u-dyadic q k
      le : l (embedℚ (embed n)) k ≡ neg (δ k) + embed n
      le = l-dyadic (embed n) k
      wk' : δ k + q < neg (δ k) + embed n
      wk' = subst₂ _<_ uq le wk
      t3 : δ k + (neg (δ k) + embed n) ≡ embed n
      t3 = trans (sym (+-assoc (δ k) (neg (δ k)) (embed n)))
           (trans (cong (_+ embed n) (+-inverseʳ (δ k)))
                  (+-identityˡ (embed n)))
      s1 : (δ k + δ k) + q < embed n
      s1 = subst₂ _<_ (sym (+-assoc (δ k) (δ k) q)) t3
             (+-monoʳ-< (δ k) wk')
      p1 : q ≤ q + 0ℚ
      p1 = ≤-reflexive (sym (+-identityʳ q))
      p2 : q + 0ℚ ≤ q + (δ k + δ k)
      p2 = +-mono-≤ (≤-refl {q})
             (+-mono-≤ (<⇒≤ (δ-pos k)) (<⇒≤ (δ-pos k)))
      p3 : q + (δ k + δ k) ≤ (δ k + δ k) + q
      p3 = ≤-reflexive (+-comm q (δ k + δ k))
      q≤s1 : q ≤ (δ k + δ k) + q
      q≤s1 = ≤-trans p1 (≤-trans p2 p3)
      s2 : q < embed n
      s2 = ≤-<-trans q≤s1 s1
      s3 : embed n ≤ pow2 n
      s3 = embed-mono-≤ {n} {2 ^ n} (ℕ<⇒≤ (n<2^n n))
  in n , <-≤-trans s2 s3

-- δ n can be made arbitrarily small.
--
-- δ n 可以任意小。
δ-small : (q : ℚ) → 0ℚ < q → Σ ℕ (λ n → δ n < q)
δ-small q q>0 =
  let rq = 1/_ q {{pos⇒nonZero q {{positive q>0}}}}
      tgt = δ 0 * rq
      tgt-pos : Positive tgt
      tgt-pos = pos*pos⇒pos (δ 0) {{positive (δ-pos 0)}}
                            rq {{1/pos⇒pos q {{positive q>0}}}}
      tgt>0 : 0ℚ < tgt
      tgt>0 = positive⁻¹ tgt {{tgt-pos}}
      (n , pt) = pow2-arch tgt tgt>0

      δ-eq : (δ 0 * rq) * q ≡ δ 0
      δ-eq = begin
               (δ 0 * rq) * q
             ≡⟨ *-assoc (δ 0) rq q ⟩
               δ 0 * (rq * q)
             ≡⟨ cong (δ 0 *_) (*-inverseˡ q {{pos⇒nonZero q {{positive q>0}}}}) ⟩
               δ 0 * 1ℚ
             ≡⟨ *-identityʳ (δ 0) ⟩
               δ 0
             ∎

      s1 : δ 0 < pow2 n * q
      s1 = subst (λ z → z < pow2 n * q) δ-eq
             (subst (λ z → z < pow2 n * q)
                    (sym (*-comm (δ 0 * rq) q))
                    (subst (λ z → q * (δ 0 * rq) < z)
                           (*-comm q (pow2 n))
                           (*-monoʳ-<-pos q {{positive q>0}} pt)))

      inv-eq : (1/_ (pow2 n) {{pow2-nz n}}) * (pow2 n * q) ≡ q
      inv-eq = begin
                 (1/_ (pow2 n) {{pow2-nz n}}) * (pow2 n * q)
               ≡⟨ *-comm (1/_ (pow2 n) {{pow2-nz n}}) (pow2 n * q) ⟩
                 (pow2 n * q) * (1/_ (pow2 n) {{pow2-nz n}})
               ≡⟨ *-assoc (pow2 n) q (1/_ (pow2 n) {{pow2-nz n}}) ⟩
                 pow2 n * (q * (1/_ (pow2 n) {{pow2-nz n}}))
               ≡⟨ cong (pow2 n *_) (*-comm q (1/_ (pow2 n) {{pow2-nz n}})) ⟩
                 pow2 n * ((1/_ (pow2 n) {{pow2-nz n}}) * q)
               ≡⟨ sym (*-assoc (pow2 n) (1/_ (pow2 n) {{pow2-nz n}}) q) ⟩
                 (pow2 n * (1/_ (pow2 n) {{pow2-nz n}})) * q
               ≡⟨ cong (_* q) (*-inverseʳ (pow2 n) {{pow2-nz n}}) ⟩
                 1ℚ * q
               ≡⟨ *-identityˡ q ⟩
                 q
               ∎

      s2 : δ 0 * (1/_ (pow2 n) {{pow2-nz n}}) < q
      s2 = subst (λ z → z < q) (*-comm (1/_ (pow2 n) {{pow2-nz n}}) (δ 0))
             (subst (λ z → (1/_ (pow2 n) {{pow2-nz n}}) * (δ 0) < z) inv-eq
                    (*-monoʳ-<-pos (1/_ (pow2 n) {{pow2-nz n}})
                      {{1/pos⇒pos (pow2 n) {{posPow2 n}}}}
                      s1))
  in n , ≤-<-trans (δ≤δ0/pow2 n) s2

-- recipPow2 n can be made arbitrarily small.
--
-- recipPow2 n 可以任意小。
recipPow2-small : (q : ℚ) → 0ℚ < q → Σ ℕ (λ n → recipPow2 n < q)
recipPow2-small q q>0 =
  let rq = 1/_ q {{pos⇒nonZero q {{positive q>0}}}}
      rq>0 = positive⁻¹ rq {{1/pos⇒pos q {{positive q>0}}}}
      (n , pq) = pow2-arch rq rq>0
      D = embed (suc (2 ^ n ∸ 1))
      D≡pow2n : D ≡ pow2 n
      D≡pow2n = cong embed (suc∸1 {2 ^ n} (1≤2^n n))
      rq<D : rq < D
      rq<D = subst (λ z → rq < z) (sym D≡pow2n) pq
      s1 : recipPow2 n < 1/_ rq {{pos⇒nonZero rq {{positive rq>0}}}}
      s1 = subst₂ _<_ refl refl (strict-recip rq D rq>0 rq<D)
      -- 用 1/-involutive 把 1/(1/q) 改写成 q
      s2 : 1/_ rq {{pos⇒nonZero rq {{positive rq>0}}}} ≡ q
      s2 = 1/-involutive q {{pos⇒nonZero q {{positive q>0}}}}
  in n , subst (recipPow2 n <_) s2 s1

------------------------------------------------------------------------
-- Widths shrink to zero
--
-- 宽度趋于零
--
-- width r n ≤ width r 0 * recipPow2 n (width-n) and recipPow2 is
-- arbitrarily small, so after any depth N the width of r at depth n
-- is below any prescribed positive q.
--
-- 宽度由初始宽度乘以二进倒数控制，而二进倒数可以任意小，因此在
-- 任意深度之后，宽度低于任意给定正数。

width-small : (r : RealI) (N : ℕ) (q : ℚ) → 0ℚ < q →
  Σ ℕ (λ n → (n ℕ≥ N) × width r n < q)
width-small r N q q>0 =
  let w0 = width r 0
      w0>0 = 0<width r
      iw = 1/_ w0 {{pos⇒nonZero w0 {{positive w0>0}}}}
      tgt = q * iw
      tgt>0 : 0ℚ < tgt
      tgt>0 = positive⁻¹ tgt
                {{pos*pos⇒pos q {{positive q>0}} iw
                    {{1/pos⇒pos w0 {{positive w0>0}}}}}}
      (m , rm) = recipPow2-small tgt tgt>0
      n = Data.Nat._⊔_ N m
      n≥N : n ℕ≥ N
      n≥N = m≤m⊔n N m
      rm' : recipPow2 n < tgt
      rm' = ≤-<-trans (recipPow2-mono (m≤n⊔m N m)) rm
      s-m : w0 * recipPow2 n < w0 * tgt
      s-m = *-monoʳ-<-pos w0 {{positive w0>0}} rm'
      w0*tgt≡q : w0 * tgt ≡ q
      w0*tgt≡q =
        begin
          w0 * (q * iw)
        ≡⟨ sym (*-assoc w0 q iw) ⟩
          (w0 * q) * iw
        ≡⟨ cong (_* iw) (*-comm w0 q) ⟩
          (q * w0) * iw
        ≡⟨ *-assoc q w0 iw ⟩
          q * (w0 * iw)
        ≡⟨ cong (q *_) (*-inverseʳ w0 {{pos⇒nonZero w0 {{positive w0>0}}}}) ⟩
          q * 1ℚ
        ≡⟨ *-identityʳ q ⟩
          q
        ∎
      w0rm : w0 * recipPow2 n < q
      w0rm = <-≤-trans s-m (≤-reflexive w0*tgt≡q)
  in n , n≥N , ≤-<-trans (width-n r n) w0rm

------------------------------------------------------------------------
-- The product of a unit is eventually strictly positive
--
-- 单位乘积最终严格为正

-- ε 4 < 1/2.
--
-- 第 4 层精度小于二分之一。
2<5 : 2 ℕ< 5
2<5 = s≤s (s≤s (s≤s z≤n))

ε4<half : ε 4 < half
ε4<half =
  strict-recip (embed 2) (embed 5)
    (0<embed 1)
    (embed-mono-< {2} {5} 2<5)

-- 1 - 2·ε 4 > 0.
--
-- 一减去两倍第 4 层精度仍为正。
1-2e>0 : 0ℚ < 1ℚ - 2ℚ * ε 4
1-2e>0 = pos-diff (2ℚ * ε 4) 1ℚ
  (subst₂ _<_ (add-self (ε 4)) (half+half≡1)
    (+-mono-< ε4<half ε4<half))

------------------------------------------------------------------------
-- Separation of x -ℝ y from 0ℝ
--
-- 差与零区间的分离

-- u (x -ℝ y) n = u x n - l y n.
--
-- 差的上端点等于被减数上端点减去减数下端点。
u-sub : (x y : RealI) (n : ℕ) →
  u (x -ℝ y) n ≡ u x n - l y n
u-sub x y n =
  begin
    u (x -ℝ y) n
  ≡⟨ refl ⟩
    u (x +ℝ negℝ y) n
  ≡⟨ u-hom x (negℝ y) n ⟩
    u x n + u (negℝ y) n
  ≡⟨ cong (u x n +_) (u-neg y n) ⟩
    u x n + neg (l y n)
  ∎

-- l (x -ℝ y) n = l x n - u y n.
--
-- 差的下端点等于被减数下端点减去减数上端点。
l-sub : (x y : RealI) (n : ℕ) →
  l (x -ℝ y) n ≡ l x n - u y n
l-sub x y n =
  begin
    l (x -ℝ y) n
  ≡⟨ refl ⟩
    l (x +ℝ negℝ y) n
  ≡⟨ l-hom x (negℝ y) n ⟩
    l x n + l (negℝ y) n
  ≡⟨ cong (l x n +_) (l-neg y n) ⟩
    l x n + neg (u y n)
  ∎

-- (x -ℝ y) <ℝ 0ℝ implies x <ℝ y.
--
-- 差严格小于零蕴含前者严格小于后者。
d<0⇒x<y : (x y : RealI) → (x -ℝ y) <ℝ 0ℝ → x <ℝ y
d<0⇒x<y x y (n , wn) =
  let w2 : u x n - l y n < neg (δ n)
      w2 = subst₂ _<_ (u-sub x y n) (l0ℝ n) wn
      w3 : (u x n - l y n) + (l y n + δ n) < neg (δ n) + (l y n + δ n)
      w3 = +-monoˡ-< (l y n + δ n) w2
      lhs≡ : (u x n - l y n) + (l y n + δ n) ≡ u x n + δ n
      lhs≡ =
        begin
          (u x n - l y n) + (l y n + δ n)
        ≡⟨ refl ⟩
          (u x n + neg (l y n)) + (l y n + δ n)
        ≡⟨ +-assoc (u x n) (neg (l y n)) (l y n + δ n) ⟩
          u x n + (neg (l y n) + (l y n + δ n))
        ≡⟨ cong (u x n +_) (+-comm (neg (l y n)) (l y n + δ n)) ⟩
          u x n + ((l y n + δ n) + neg (l y n))
        ≡⟨ cong (u x n +_) (+-assoc (l y n) (δ n) (neg (l y n))) ⟩
          u x n + (l y n + (δ n + neg (l y n)))
        ≡⟨ cong (u x n +_) (cong (l y n +_) (+-comm (δ n) (neg (l y n)))) ⟩
          u x n + (l y n + (neg (l y n) + δ n))
        ≡⟨ cong (u x n +_) (sym (+-assoc (l y n) (neg (l y n)) (δ n))) ⟩
          u x n + ((l y n + neg (l y n)) + δ n)
        ≡⟨ cong (u x n +_) (cong (_+ δ n) (+-inverseʳ (l y n))) ⟩
          u x n + (0ℚ + δ n)
        ≡⟨ cong (u x n +_) (+-identityˡ (δ n)) ⟩
          u x n + δ n
        ∎
      rhs≡ : neg (δ n) + (l y n + δ n) ≡ l y n
      rhs≡ =
        begin
          neg (δ n) + (l y n + δ n)
        ≡⟨ +-comm (neg (δ n)) (l y n + δ n) ⟩
          (l y n + δ n) + neg (δ n)
        ≡⟨ +-assoc (l y n) (δ n) (neg (δ n)) ⟩
          l y n + (δ n + neg (δ n))
        ≡⟨ cong (l y n +_) (+-inverseʳ (δ n)) ⟩
          l y n + 0ℚ
        ≡⟨ +-identityʳ (l y n) ⟩
          l y n
        ∎
      w4 : u x n + δ n < l y n
      w4 = subst₂ _<_ lhs≡ rhs≡ w3
      w5 : u x n < u x n + δ n
      w5 = subst (λ z → z < u x n + δ n) (+-identityʳ (u x n))
             (+-mono-≤-< (≤-refl {u x n}) (δ-pos n))
  in n , <-trans w5 w4

-- 0ℝ <ℝ (x -ℝ y) implies y <ℝ x.
--
-- 零严格小于差蕴含后者严格小于前者。
0<d⇒y<x : (x y : RealI) → 0ℝ <ℝ (x -ℝ y) → y <ℝ x
0<d⇒y<x x y (n , wn) =
  let w2 : δ n < l x n - u y n
      w2 = subst₂ _<_ (u-dyadic-0 n) (l-sub x y n) wn
      w3 : u y n + δ n < u y n + (l x n - u y n)
      w3 = +-monoʳ-< (u y n) w2
      rhs≡ : u y n + (l x n - u y n) ≡ l x n
      rhs≡ =
        begin
          u y n + (l x n - u y n)
        ≡⟨ refl ⟩
          u y n + (l x n + neg (u y n))
        ≡⟨ sym (+-assoc (u y n) (l x n) (neg (u y n))) ⟩
          (u y n + l x n) + neg (u y n)
        ≡⟨ cong (_+ neg (u y n)) (+-comm (u y n) (l x n)) ⟩
          (l x n + u y n) + neg (u y n)
        ≡⟨ +-assoc (l x n) (u y n) (neg (u y n)) ⟩
          l x n + (u y n + neg (u y n))
        ≡⟨ cong (l x n +_) (+-inverseʳ (u y n)) ⟩
          l x n + 0ℚ
        ≡⟨ +-identityʳ (l x n) ⟩
          l x n
        ∎
      w4 : u y n + δ n < l x n
      w4 = subst₂ _<_ refl rhs≡ w3
      w5 : u y n < u y n + δ n
      w5 = subst (λ z → z < u y n + δ n) (+-identityʳ (u y n))
                 (+-monoʳ-< (u y n) (δ-pos n))
  in n , <-trans w5 w4

-- (x -ℝ y) #ℝ 0ℝ implies x #ℝ y.
--
-- 差与零分离蕴含两个原区间分离。
#0⇒# : (x y : RealI) → (x -ℝ y) #ℝ 0ℝ → x #ℝ y
#0⇒# x y (inj₁ d<0) = inj₁ (d<0⇒x<y x y d<0)
#0⇒# x y (inj₂ 0<d) = inj₂ (0<d⇒y<x x y 0<d)

-- If 1 - c < ε 4, then 1 - ε 4 < c.
--
-- 一减去某量小于第 4 层精度时，一减该精度小于该量。
1-e<c : (c : ℚ) → 1ℚ - c < ε 4 → 1ℚ - ε 4 < c
1-e<c c s-a = subst₂ _<_ t6 t7 t5
  where
  t1 : neg (ε 4) + (1ℚ - c) < neg (ε 4) + ε 4
  t1 = +-monoʳ-< (neg (ε 4)) s-a

  t2 : neg (ε 4) + ε 4 ≡ 0ℚ
  t2 = +-inverseˡ (ε 4)

  t3 : neg (ε 4) + (1ℚ - c) < 0ℚ
  t3 = subst (λ z → neg (ε 4) + (1ℚ - c) < z) t2 t1

  t4' : (1ℚ - ε 4) + neg c ≡ neg (ε 4) + (1ℚ - c)
  t4' = begin
    (1ℚ - ε 4) + neg c
    ≡⟨ refl ⟩
    (1ℚ + neg (ε 4)) + neg c
    ≡⟨ +-assoc 1ℚ (neg (ε 4)) (neg c) ⟩
    1ℚ + (neg (ε 4) + neg c)
    ≡⟨ cong (1ℚ +_) (+-comm (neg (ε 4)) (neg c)) ⟩
    1ℚ + (neg c + neg (ε 4))
    ≡⟨ sym (+-assoc 1ℚ (neg c) (neg (ε 4))) ⟩
    (1ℚ + neg c) + neg (ε 4)
    ≡⟨ +-comm (1ℚ + neg c) (neg (ε 4)) ⟩
    neg (ε 4) + (1ℚ + neg c)
    ≡⟨ refl ⟩
    neg (ε 4) + (1ℚ - c)
    ∎

  t4 : (1ℚ - ε 4) + neg c < 0ℚ
  t4 = subst (λ z → z < 0ℚ) (sym t4') t3

  t5 : ((1ℚ - ε 4) + neg c) + c < 0ℚ + c
  t5 = +-monoˡ-< c t4

  t6 : ((1ℚ - ε 4) + neg c) + c ≡ 1ℚ - ε 4
  t6 = begin
    ((1ℚ - ε 4) + neg c) + c
    ≡⟨ +-assoc (1ℚ - ε 4) (neg c) c ⟩
    (1ℚ - ε 4) + (neg c + c)
    ≡⟨ cong ((1ℚ - ε 4) +_) (+-inverseˡ c) ⟩
    (1ℚ - ε 4) + 0ℚ
    ≡⟨ +-identityʳ (1ℚ - ε 4) ⟩
    1ℚ - ε 4
    ∎

  t7 : 0ℚ + c ≡ c
  t7 = +-identityˡ c

-- If 1 - ε 4 < c, then 1 - 2 * ε 4 < c - ε 4.
--
-- 一减第 4 层精度小于某量时，一减两倍该精度小于该量减该精度。
1-2e<c-e : (c : ℚ) → 1ℚ - ε 4 < c → 1ℚ - 2ℚ * ε 4 < c - ε 4
1-2e<c-e c s-b =
  subst₂ _<_ e1 e2 (+-monoʳ-< (neg (ε 4)) s-b)
  where
  e1 : neg (ε 4) + (1ℚ - ε 4) ≡ 1ℚ - 2ℚ * ε 4
  e1 = begin
    neg (ε 4) + (1ℚ - ε 4)
    ≡⟨ +-comm (neg (ε 4)) (1ℚ - ε 4) ⟩
    (1ℚ - ε 4) + neg (ε 4)
    ≡⟨ refl ⟩
    (1ℚ + neg (ε 4)) + neg (ε 4)
    ≡⟨ +-assoc 1ℚ (neg (ε 4)) (neg (ε 4)) ⟩
    1ℚ + (neg (ε 4) + neg (ε 4))
    ≡⟨ cong (1ℚ +_) (sym (neg-distrib-+ (ε 4) (ε 4))) ⟩
    1ℚ + neg (ε 4 + ε 4)
    ≡⟨ cong (1ℚ +_) (cong neg (add-self (ε 4))) ⟩
    1ℚ + neg (2ℚ * ε 4)
    ∎

  e2 : neg (ε 4) + c ≡ c - ε 4
  e2 = +-comm (neg (ε 4)) c

-- A product equivalent to 1ℝ is separated from 0ℝ.
--
-- 与 1ℝ 等价的乘积与 0ℝ 分离。
inv⇒d#0 : (d : RealI) → Σ RealI (λ z → (d *ℝ z) ≈ℝ 1ℝ) → d #ℝ 0ℝ
inv⇒d#0 d (z , dz≈1) =
  let Np = dz≈1 4
      (N , Np') = Np
      (n₀ , n₀≥N , w₀) = width-small (d *ℝ z) N (ε 4) (0<ε 4)
      c1e : ∣ centre (d *ℝ z) n₀ - centre 1ℝ n₀ ∣ < ε 4
      c1e = Np' n₀ n₀≥N
      c1 : centre 1ℝ n₀ ≡ 1ℚ
      c1 = centre-embedℚ 1ℚ n₀
      c1e' : ∣ centre (d *ℝ z) n₀ - 1ℚ ∣ < ε 4
      c1e' = subst (λ y → ∣ centre (d *ℝ z) n₀ - y ∣ < ε 4) c1 c1e
      c = centre (d *ℝ z) n₀
      neg≡ : neg (c - 1ℚ) ≡ 1ℚ - c
      neg≡ = negsub c 1ℚ
      |1-c|≡ : ∣ 1ℚ - c ∣ ≡ ∣ c - 1ℚ ∣
      |1-c|≡ = trans (cong ∣_∣ (sym neg≡)) (∣-p∣≡∣p∣ (c - 1ℚ))
      s-a : 1ℚ - c < ε 4
      s-a = ≤-<-trans
              (subst (λ z → 1ℚ - c ≤ z) |1-c|≡ (r≤|r| (1ℚ - c)))
              c1e'
      s-b : 1ℚ - ε 4 < c
      s-b = 1-e<c c s-a
      s-c : 1ℚ - 2ℚ * ε 4 < c - ε 4
      s-c = 1-2e<c-e c s-b
      s-d : c - ε 4 < c - width (d *ℝ z) n₀
      s-d = +-monoʳ-< c (neg-antimono-< w₀)
      s-e : 1ℚ - 2ℚ * ε 4 < c - width (d *ℝ z) n₀
      s-e = <-trans s-c s-d
      s-f : 1ℚ - 2ℚ * ε 4 < l (d *ℝ z) n₀
      s-f = <-≤-trans s-e (l≥centre-width (d *ℝ z) n₀)
      lgt : 0ℚ < l (d *ℝ z) n₀
      lgt = <-trans 1-2e>0 s-f
      deep : 0ℚ < ((l d (2 ℕ* n₀) * l z (2 ℕ* n₀)) ⊓ (l d (2 ℕ* n₀) * u z (2 ℕ* n₀)))
                 ⊓ ((u d (2 ℕ* n₀) * l z (2 ℕ* n₀)) ⊓ (u d (2 ℕ* n₀) * u z (2 ℕ* n₀)))
      deep = subst (0ℚ <_) (l-mul4 d z n₀) lgt
      (l1 , l2) = ⊓-pos deep
      (ac , ad) = ⊓-pos l1
      (bc , bd) = ⊓-pos l2
      signs : (0ℚ < l d (2 ℕ* n₀)) ⊎ (u d (2 ℕ* n₀) < 0ℚ)
      signs = same-sign {l d (2 ℕ* n₀)} {u d (2 ℕ* n₀)} {l z (2 ℕ* n₀)} {u z (2 ℕ* n₀)}
                ac ad bc bd
      pos-case : 0ℚ < l d (2 ℕ* n₀) → d #ℝ 0ℝ
      pos-case ld>0 =
        let (m , δm<ld) = δ-small (l d (2 ℕ* n₀)) ld>0
            n = Data.Nat._⊔_ (2 ℕ* n₀) m
            n≥2n : 2 ℕ* n₀ ℕ≤ n
            n≥2n = m≤m⊔n (2 ℕ* n₀) m
            m≤n : m ℕ≤ n
            m≤n = m≤n⊔m (2 ℕ* n₀) m
            δn≤δm : δ n ≤ δ m
            δn≤δm = δ-mono {m} {n} m≤n
            δn<ld : δ n < l d (2 ℕ* n₀)
            δn<ld = ≤-<-trans δn≤δm δm<ld
            ldn : l d (2 ℕ* n₀) ≤ l d n
            ldn = l-mono' d {2 ℕ* n₀} {n} n≥2n
            δn<ldn : δ n < l d n
            δn<ldn = <-≤-trans δn<ld ldn
        in inj₂ (n , subst₂ _<_ (sym (u-dyadic-0 n)) refl δn<ldn)

      neg-case : u d (2 ℕ* n₀) < 0ℚ → d #ℝ 0ℝ
      neg-case ud<0 =
        let nd = neg (u d (2 ℕ* n₀))
            0<nd : 0ℚ < nd
            0<nd = neg-antimono-< ud<0
            (m , δm<nd) = δ-small nd 0<nd
            n = Data.Nat._⊔_ (2 ℕ* n₀) m
            n≥2n : 2 ℕ* n₀ ℕ≤ n
            n≥2n = m≤m⊔n (2 ℕ* n₀) m
            m≤n : m ℕ≤ n
            m≤n = m≤n⊔m (2 ℕ* n₀) m
            δn≤δm : δ n ≤ δ m
            δn≤δm = δ-mono {m} {n} m≤n
            δn<nd : δ n < neg (u d (2 ℕ* n₀))
            δn<nd = ≤-<-trans δn≤δm δm<nd
            udn≤ : u d n ≤ u d (2 ℕ* n₀)
            udn≤ = u-mono' d {2 ℕ* n₀} {n} n≥2n
            u2n<-δn : u d (2 ℕ* n₀) < neg (δ n)
            u2n<-δn = subst₂ _<_
              (begin
                 δ n + (u d (2 ℕ* n₀) + neg (δ n))
               ≡⟨ sym (+-assoc (δ n) (u d (2 ℕ* n₀)) (neg (δ n))) ⟩
                 (δ n + u d (2 ℕ* n₀)) + neg (δ n)
               ≡⟨ cong (_+ neg (δ n)) (+-comm (δ n) (u d (2 ℕ* n₀))) ⟩
                 (u d (2 ℕ* n₀) + δ n) + neg (δ n)
               ≡⟨ +-assoc (u d (2 ℕ* n₀)) (δ n) (neg (δ n)) ⟩
                 u d (2 ℕ* n₀) + (δ n + neg (δ n))
               ≡⟨ cong (u d (2 ℕ* n₀) +_) (+-inverseʳ (δ n)) ⟩
                 u d (2 ℕ* n₀) + 0ℚ
               ≡⟨ +-identityʳ (u d (2 ℕ* n₀)) ⟩
                 u d (2 ℕ* n₀)
               ∎)
              (begin
                 neg (u d (2 ℕ* n₀)) + (u d (2 ℕ* n₀) + neg (δ n))
               ≡⟨ sym (+-assoc (neg (u d (2 ℕ* n₀))) (u d (2 ℕ* n₀)) (neg (δ n))) ⟩
                 (neg (u d (2 ℕ* n₀)) + u d (2 ℕ* n₀)) + neg (δ n)
               ≡⟨ cong (_+ neg (δ n)) (+-inverseˡ (u d (2 ℕ* n₀))) ⟩
                 0ℚ + neg (δ n)
               ≡⟨ +-identityˡ (neg (δ n)) ⟩
                 neg (δ n)
               ∎)
              (+-monoˡ-< (u d (2 ℕ* n₀) + neg (δ n)) δn<nd)
            udn<-δn : u d n < neg (δ n)
            udn<-δn = ≤-<-trans udn≤ u2n<-δn
        in inj₁ (n , subst₂ _<_ refl (sym (l0ℝ n)) udn<-δn)
  in [ pos-case , neg-case ]′ signs

-- Invertibility entails apartness.
--
-- 可逆性蕴含分离性。
invertible⇒# : (x y : RealI) →
  Σ RealI (λ z → ((x -ℝ y) *ℝ z) ≈ℝ 1ℝ × (z *ℝ (x -ℝ y)) ≈ℝ 1ℝ) →
  x #ℝ y
invertible⇒# x y (z , lhs , rhs) =
  #0⇒# x y (inv⇒d#0 (x -ℝ y) (z , lhs))
