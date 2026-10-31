------------------------------------------------------------------------
-- Cauchy-side round-trip equivalence
--
-- 柯西侧往返等价
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module Real.Interval.RetractCauchy where

open import Data.Nat using (ℕ; suc; _⊔_; _^_; s≤s)
  renaming (_≤_ to _≤N_; _≥_ to _≥N_; _*_ to _*ℕ_; _<_ to _<N_)
open import Data.Nat.Properties using (m≤m⊔n; m≤n⊔m; m≤m+n; m≤n+m; n<1+n; ^-monoʳ-≤)
  renaming (≤-trans to ≤N-trans
           ; ≤-<-trans to ≤N-<-trans; <-≤-trans to <N-≤-trans)
open import Data.Rational using
  (ℚ; 0ℚ; 1ℚ; _+_; _-_; -_; _*_; _<_; _≤_; ∣_∣; 1/_; positive; Positive; NonZero; NonNegative; nonNegative)
open import Data.Rational.Properties using
  (≤-refl; ≤-reflexive; ≤-trans; <⇒≤; ≤-<-trans; <-≤-trans; <-trans
  ; +-mono-<; +-monoʳ-<; +-mono-≤; +-inverseʳ; +-identityˡ; ∣p+q∣≤∣p∣+∣q∣
  ; ∣-p∣≡∣p∣; positive⁻¹; *-inverseʳ; *-inverseˡ
  ; *-identityʳ; *-assoc; *-comm; *-monoˡ-≤-nonNeg
  ; *-monoʳ-<-pos
  ; +-assoc; +-comm)
  renaming (1/pos⇒pos to pos-recip)
open import Data.Product using (_,_)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; cong; sym; trans; subst; module ≡-Reasoning)
open ≡-Reasoning

open import Base.RationalRing using (telescope)
open import Real using
  (CauchySeq; ε; 0<ε; embed; _s≈_; _≈_; embed-mono-≤; ε-half; embed-mono-<)
open Real.CauchySeq using (f; μ; cauchy)
open import Real.Interval.Equiv using (_≈ℝ_)
open import Real.IntervalEquiv using (realI→cauchy; centre; n<2^n)
open import Real.CauchyToInterval using
  (cauchy→realI; M; K; centre-cauchy→realI; μ≤M; K≥k)
open import Real.Regular using (regularize; μr; μr≥k; μr-mono≤)
open import Real.Interval.Rational using (r≤|r|; negsub)

-- Generic reassociation: a + b + c ≡ b + (a + c), with abstract
-- operands so no rational normal form is forced.
--
-- 泛型重排
--
-- 操作数抽象，不强制有理数归约。
reassoc3 : ∀ (a b c : ℚ) → (a + b) + c ≡ b + (a + c)
reassoc3 a b c = begin
  (a + b) + c
    ≡⟨ cong (λ v → v + c) (+-comm a b) ⟩
  (b + a) + c
    ≡⟨ +-assoc b a c ⟩
  b + (a + c) ∎

------------------------------------------------------------------------
-- regularize x ≈ x
--
-- The two sequences share the same f, so at every index the terms are
-- identical; the symmetric close relation reduces to the reflexive
-- case. N = 0 works for every k.
--
-- 正规化序列与原序列相等
--
-- 两序列共享同一 f，故每个下标处的项完全相同，对称接近关系归约为
-- 自反情形。对每个 k 取 N = 0。

regularize≈ : (x : CauchySeq) → regularize x ≈ x
regularize≈ x k = 0 , λ n _ →
  let q = f x n
      eq : q + (- q) ≡ 0ℚ
      eq = +-inverseʳ q
      d : (q + (- q)) < ε k
      d = ≤-<-trans (≤-reflexive eq) (0<ε k)
  in (d , d)

------------------------------------------------------------------------
-- realI→cauchy respects ≈ℝ
--
-- The ≈ℝ witness bounds the absolute difference by ε k, which bounds
-- both directed differences, exactly the two components of _s≈_.
--
-- realI→cauchy 保持 ≈ℝ
--
-- ≈ℝ 见证以 ε k 界绝对差，从而界两个方向的差，恰为 _s≈_ 的两个
-- 分量。

realI→cauchy-cong : ∀ {x y} → x ≈ℝ y → realI→cauchy x ≈ realI→cauchy y
realI→cauchy-cong {x} {y} p k =
  let N , h = p k
  in N , λ n n≥N →
    let d : ∣ centre x n - centre y n ∣ < ε k
        d = h n n≥N
        q = centre x n - centre y n
        -- q ≤ ∣q∣ and -q ≤ ∣q∣, hence both directed diffs < ε k.
        -- q and -q are definitionally the two _s≈_ components.
        fwd : q < ε k
        fwd = ≤-<-trans (r≤|r| q) d
        -- Reverse component r2 = centre y n - centre x n. It equals -q,
        -- so ∣r2∣ ≡ ∣q∣, which d bounds strictly.
        r2 = centre y n - centre x n
        bwd : r2 < ε k
        bwd = ≤-<-trans (r≤|r| r2)
                (≤-<-trans (≤-reflexive (sym (cong ∣_∣ (negsub (centre x n) (centre y n)))))
                  (≤-<-trans (≤-reflexive (∣-p∣≡∣p∣ q)) d))
    in (fwd , bwd)

------------------------------------------------------------------------
-- Retract for a sequence with a regular modulus
--
-- For the regularized sequence, the modulus is monotone and dominates
-- the identity. At n ≥ μ z k, both n and M z n are past μ z k (the
-- latter via M z n ≥ μ z (K n) and monotonicity), so the Cauchy
-- condition bounds the sampled centre against the current term.
--
-- 正规模数序列的往返
--
-- 对正规化序列，模数单调且支配恒等。当 n 越过 μ z k 时，n 与
-- M z n 也都越过该阈值，故柯西条件界采样中心与当前项之差。

regular-retract : (x : CauchySeq)
  → realI→cauchy (cauchy→realI (regularize x)) ≈ regularize x
regular-retract x k = μr x k , body
  where
  z = regularize x
  body : (n : ℕ) → n ≥N μr x k →
           _s≈_ (f (realI→cauchy (cauchy→realI z)) n) (f z n) k
  body n n≥N rewrite centre-cauchy→realI z n =
    let -- M z n ≥ μ z (K n) = μr x (K n) ≥ μr x k.
        k≤n : k ≤N n
        k≤n = ≤N-trans (μr≥k x k) n≥N
        k≤Kn : k ≤N K n
        k≤Kn = ≤N-trans k≤n (K≥k n)
        M≥ : M z n ≥N μr x k
        M≥ = ≤N-trans (μr-mono≤ x k (K n) k≤Kn)
               (μ≤M z n)
        d : ∣ f z (M z n) - f z n ∣ < ε k
        d = Real.CauchySeq.cauchy z k (M z n) n M≥ n≥N
        q = f z (M z n) - f z n
        fwd : q < ε k
        fwd = ≤-<-trans (r≤|r| q) d
        r2 = f z n - f z (M z n)
        bwd : r2 < ε k
        bwd = ≤-<-trans (r≤|r| r2)
                (≤-<-trans (≤-reflexive (sym (cong ∣_∣ (negsub (f z (M z n)) (f z n)))))
                  (≤-<-trans (≤-reflexive (∣-p∣≡∣p∣ q)) d))
    in (fwd , bwd)

------------------------------------------------------------------------
-- Reciprocal antitonicity for positive rationals
--
-- 正有理数倒数的反单调性

private
  recip-antitone : ∀ (p q : ℚ) → 0ℚ < p → p ≤ q
    → .{{p-nz : NonZero p}} → .{{q-nz : NonZero q}} → (1/ q) ≤ (1/ p)
  recip-antitone p q 0<p p≤q =
    let iq = 1/ q
        ip = 1/ p
        0<q : 0ℚ < q
        0<q = <-≤-trans 0<p p≤q
        pos-ip : Positive ip
        pos-ip = pos-recip p {{positive 0<p}}
        pos-iq : Positive iq
        pos-iq = pos-recip q {{positive 0<q}}
        0<ip : 0ℚ < ip
        0<ip = positive⁻¹ ip {{pos-ip}}
        0<iq : 0ℚ < iq
        0<iq = positive⁻¹ iq {{pos-iq}}
        0≤iq : 0ℚ ≤ iq
        0≤iq = <⇒≤ 0<iq
        instance nonNeg-iq : NonNegative iq
        nonNeg-iq = nonNegative 0≤iq
        instance nonNeg-ip : NonNegative ip
        nonNeg-ip = nonNegative (<⇒≤ 0<ip)
        inv : iq * q ≡ 1ℚ
        inv = *-inverseˡ q
        t≤1 : iq * p ≤ 1ℚ
        t≤1 = ≤-trans (*-monoˡ-≤-nonNeg iq {{nonNeg-iq}} p≤q)
                (≤-reflexive inv)
    in ≤-trans
         (≤-reflexive (sym (*-identityʳ iq)))
         (≤-trans
           (≤-reflexive (cong (λ v → iq * v) (sym (*-inverseʳ p))))
           (≤-trans
             (≤-reflexive (sym (*-assoc iq p ip)))
             (≤-trans
               (≤-reflexive (*-comm (iq * p) ip))
               (≤-trans
                 (*-monoˡ-≤-nonNeg ip {{nonNeg-ip}} t≤1)
                 (≤-reflexive (*-identityʳ ip))))))

  -- Strict reciprocal antitonicity: 0 < p → p < q → 1/q < 1/p.
  --
  -- 严格倒数反单调
  recip-antitone-strict : ∀ (p q : ℚ)
    → .{{p-nz : NonZero p}} → .{{q-nz : NonZero q}}
    → 0ℚ < p → p < q → (1/ q) {{q-nz}} < (1/ p) {{p-nz}}
  recip-antitone-strict p q 0<p p<q =
    let iq = 1/ q
        ip = 1/ p
        0<q : 0ℚ < q
        0<q = ≤-<-trans (<⇒≤ 0<p) p<q
        pos-ip : Positive ip
        pos-ip = pos-recip p {{positive 0<p}}
        pos-iq : Positive iq
        pos-iq = pos-recip q {{positive 0<q}}
        -- iq*p < iq*q (multiply p<q by positive iq).
        s1 : iq * p < iq * q
        s1 = *-monoʳ-<-pos iq {{pos-iq}} p<q
        -- multiply by positive ip on the left.
        s2 : ip * (iq * p) < ip * (iq * q)
        s2 = *-monoʳ-<-pos ip {{pos-ip}} s1
        -- iq = 1*iq = ((1/p)*p)*iq = (1/p)*(p*iq) = (1/p)*(iq*p).
        lhs : iq ≡ ip * (iq * p)
        lhs = begin
          iq
            ≡⟨ sym (*-identityʳ iq) ⟩
          iq * 1ℚ
            ≡⟨ cong (λ v → iq * v) (sym (*-inverseʳ p)) ⟩
          iq * (p * ip)
            ≡⟨ cong (λ v → iq * v) (*-comm p ip) ⟩
          iq * (ip * p)
            ≡⟨ sym (*-assoc iq ip p) ⟩
          (iq * ip) * p
            ≡⟨ cong (λ v → v * p) (*-comm iq ip) ⟩
          (ip * iq) * p
            ≡⟨ *-assoc ip iq p ⟩
          ip * (iq * p) ∎
        -- ip*(iq*q) = ip*1 = ip.
        rhs : ip * (iq * q) ≡ ip
        rhs = begin
          ip * (iq * q)
            ≡⟨ cong (λ v → ip * v) (*-inverseˡ q) ⟩
          ip * 1ℚ
            ≡⟨ *-identityʳ ip ⟩
          ip ∎
    in ≤-<-trans (≤-reflexive lhs)
         (<-≤-trans s2 (≤-reflexive rhs))

ε≤ : ∀ a b → b ≤N a → ε a ≤ ε b
ε≤ a b b≤a =
  recip-antitone (embed (suc b)) (embed (suc a))
    (positive⁻¹ (embed (suc b))) (embed-mono-≤ (s≤s b≤a))

-- Strict antitonicity of ε.
--
-- ε 严格反单调。
ε< : ∀ a b → b <N a → ε a < ε b
ε< a b b<a =
  recip-antitone-strict (embed (suc b)) (embed (suc a))
    (positive⁻¹ (embed (suc b)))
    (embed-mono-< (s≤s b<a))

-- Absolute value of a non-negative rational is itself.
--
-- 非负有理数的绝对值是其自身。
--
-- Direct alias of the stdlib lemma.
--
-- 直接复用标准库引理。
0≤p⇒∣p∣≡p : ∀ {p} → 0ℚ ≤ p → ∣ p ∣ ≡ p
0≤p⇒∣p∣≡p = Data.Rational.Properties.0≤p⇒∣p∣≡p

-- Absolute value of a non-positive rational is its negation, via
-- ∣-p∣ ≡ ∣p∣ and the non-negative lemma applied to -p.
--
-- 非正有理数的绝对值是其相反数
--
-- 经绝对值对取负不变，对相反数应用非负引理。
p≤0⇒∣p∣≡-p : ∀ {p} → p ≤ 0ℚ → ∣ p ∣ ≡ - p
p≤0⇒∣p∣≡-p {p} p≤0 = begin
  ∣ p ∣     ≡⟨ sym (∣-p∣≡∣p∣ p) ⟩
  ∣ - p ∣   ≡⟨ 0≤p⇒∣p∣≡p (neg-nonNeg p≤0) ⟩
  - p ∎
  where
  -- p ≤ 0 implies 0 ≤ -p, by adding -p on the right.
  --
  -- p ≤ 0 蕴含 0 ≤ -p，在右侧加 -p。
  neg-nonNeg : p ≤ 0ℚ → 0ℚ ≤ - p
  neg-nonNeg p≤0 =
    subst (λ q → q ≤ - p) (+-inverseʳ p)
      (subst (λ q → p + - p ≤ q) (+-identityˡ (- p))
        (+-mono-≤ p≤0 (≤-refl {x = - p})))

-- Both directed bounds imply the absolute bound.
--
-- 两个方向的界蕴含绝对界。
both<⇒abs< : ∀ q e → q < e → - q < e → ∣ q ∣ < e
both<⇒abs< q e fwd bwd with Data.Rational.Properties.≤-total q 0ℚ
... | inj₁ q≤0 =
  ≤-<-trans (≤-reflexive (p≤0⇒∣p∣≡-p q≤0)) bwd
... | inj₂ 0≤q =
  ≤-<-trans (≤-reflexive (0≤p⇒∣p∣≡p 0≤q)) fwd

-- Doubling the left precision keeps ε below ε r, given the strict
-- bound from below.
--
-- 左精度加倍时 ε 仍低于 ε r（前提是严格下界成立）。
2ε<εr : ∀ r n → ε n < ε (suc (2 *ℕ r)) → ε n + ε n < ε r
2ε<εr r n d =
  <-≤-trans (+-mono-< d d)
    (≤-reflexive (ε-half r))

-- The three-term bound telescopes below ε k, given the doubled left
-- bound and the specified reassociation index r.
--
-- 三项界在给定左端加倍界与指定重排下标 r 后仍低于 ε k。
ε3<εk : ∀ r k n → ε n + ε n < ε r →
  r ≡ suc (2 *ℕ suc (2 *ℕ k)) → ε n + ε r + ε n < ε k
ε3<εk r k n d eq =
  let s = suc (2 *ℕ k)
      en = ε n
      er = ε r
      es = ε s
      e1 : en + er + en ≡ er + (en + en)
      e1 = reassoc3 en er en
      strict : er + (en + en) < er + er
      strict = +-monoʳ-< er d
      e2 : er + er ≡ es
      e2 = begin
        er + er
          ≡⟨ cong (λ i → ε i + ε i) eq ⟩
        ε (suc (2 *ℕ s)) + ε (suc (2 *ℕ s))
          ≡⟨ ε-half s ⟩
        es ∎
      e3 : es < ε k
      e3 = ε< s k (≤N-trans (n<1+n k) (s≤s (m≤m+n k (1 *ℕ k))))
  in ≤-<-trans (≤-reflexive e1)
       (<-trans (<-≤-trans strict (≤-reflexive e2)) e3)

------------------------------------------------------------------------
-- cauchy→realI respects ≈
--
-- The proof splits the difference at level n into a telescope through
-- a common index. The two outer legs are bounded by ε (K n), the
-- middle by ε r. For n large, 2 ε (K n) < ε r, and
-- 2 ε r = ε (suc (2k)) < ε k.
--
-- cauchy→realI 保持 ≈
--
-- 在第 n 层把差值拆成经公共下标的望远镜：两条外腿以 ε (K n) 界，
-- 中腿以 ε r 界。n 足够大时两倍外腿界低于 ε r，而两倍 ε r 又低于
-- ε k。

cauchy→realI-cong : ∀ {x y} → x ≈ y → cauchy→realI x ≈ℝ cauchy→realI y
cauchy→realI-cong {x} {y} p k = Nth , body
  where
  r0 : ℕ
  r0 = suc (2 *ℕ suc (2 *ℕ k))
  Nth : ℕ
  Nth = suc (2 *ℕ r0)
  core : ∀ n → n ≥N Nth →
    ∣ f x (M x n) - f y (M y n) ∣ < ε k
  core n n≥N =
    let r = r0
        N0 , w0 = p r
        c = M x n ⊔ M y n ⊔ N0
        c≥Mx : c ≥N M x n
        c≥Mx = ≤N-trans (m≤m⊔n (M x n) (M y n)) (m≤m⊔n (M x n ⊔ M y n) N0)
        c≥My : c ≥N M y n
        c≥My = ≤N-trans (m≤n⊔m (M x n) (M y n)) (m≤m⊔n (M x n ⊔ M y n) N0)
        c≥N0 : c ≥N N0
        c≥N0 = m≤n⊔m (M x n ⊔ M y n) N0
        c≥μxKn : c ≥N μ x (K n)
        c≥μxKn = ≤N-trans (μ≤M x n) c≥Mx
        c≥μyKn : c ≥N μ y (K n)
        c≥μyKn = ≤N-trans (μ≤M y n) c≥My
        -- Outer legs.
        leg1 : ∣ f x (M x n) - f x c ∣ < ε (K n)
        leg1 = cauchy x (K n) (M x n) c (μ≤M x n) c≥μxKn
        leg3 : ∣ f y c - f y (M y n) ∣ < ε (K n)
        leg3 = cauchy y (K n) c (M y n) c≥μyKn (μ≤M y n)
        -- Middle leg.
        fwd , bwd = w0 c c≥N0
        bwd' : - (f x c - f y c) < ε r
        bwd' = ≤-<-trans (≤-reflexive (negsub (f x c) (f y c))) bwd
        mid : ∣ f x c - f y c ∣ < ε r
        mid = both<⇒abs< (f x c - f y c) (ε r) fwd bwd'
        -- Triangle: telescope through four points.
        a = f x (M x n) - f x c
        b = f x c - f y c
        d = f y c - f y (M y n)
        ab-eq : a + b ≡ f x (M x n) - f y c
        ab-eq = telescope (f x (M x n)) (f x c) (f y c)
        t1 : (f x (M x n) - f y c) + d ≡ f x (M x n) - f y (M y n)
        t1 = telescope (f x (M x n)) (f y c) (f y (M y n))
        abd-eq : (a + b) + d ≡ f x (M x n) - f y (M y n)
        abd-eq = trans (cong (λ v → v + d) ab-eq) t1
        abs1 : ∣ a + b ∣ ≤ ∣ a ∣ + ∣ b ∣
        abs1 = ∣p+q∣≤∣p∣+∣q∣ a b
        abs2 : ∣ (a + b) + d ∣ ≤ ∣ a + b ∣ + ∣ d ∣
        abs2 = ∣p+q∣≤∣p∣+∣q∣ (a + b) d
        abs3 : ∣ (a + b) + d ∣ ≤ ∣ a ∣ + ∣ b ∣ + ∣ d ∣
        abs3 = ≤-trans abs2 (+-mono-≤ abs1 ≤-refl)
        tri : ∣ (a + b) + d ∣ < ε (K n) + ε r + ε (K n)
        tri = ≤-<-trans abs3
          (Data.Rational.Properties.+-mono-<
             (Data.Rational.Properties.+-mono-<
                leg1 mid) leg3)
        -- 2 ε (K n) < ε r.
        n<2n : n <N 2 ^ n
        n<2n = n<2^n n
        2n≤Kn : 2 ^ n ≤N K n
        2n≤Kn = ^-monoʳ-≤ 2 (m≤n+m n 2)
        n<Kn : n <N K n
        n<Kn = <N-≤-trans n<2n 2n≤Kn
        Kn> : Nth <N K n
        Kn> = ≤N-<-trans n≥N n<Kn
        eKn< : ε (K n) < ε Nth
        eKn< = ε< (K n) Nth Kn>
        half2 : ε (K n) + ε (K n) < ε r
        half2 = 2ε<εr r (K n) eKn<
        -- Total < ε k.
        total : ε (K n) + ε r + ε (K n) < ε k
        total = ε3<εk r k (K n) half2 refl
        -- The target difference is (a + b) + d.
        goal : ∣ f x (M x n) - f y (M y n) ∣ < ε k
        goal = ≤-<-trans
          (≤-reflexive (cong ∣_∣ (sym abd-eq)))
          (<-trans tri total)
    in goal
  body : ∀ n → n ≥N Nth →
    ∣ centre (cauchy→realI x) n - centre (cauchy→realI y) n ∣ < ε k
  body n n≥Nth
    rewrite centre-cauchy→realI x n | centre-cauchy→realI y n = core n n≥Nth

------------------------------------------------------------------------
-- Final Cauchy-side round-trip
--
-- Route through a regularized sequence z = regularize x, chaining:
-- cauchy→realI-cong, realI→cauchy-cong, regular-retract, regularize≈.
--
-- 最终柯西侧往返
--
-- 经正规化序列 z = regularize x 转接，依次串联
-- cauchy→realI-cong、realI→cauchy-cong、regular-retract 与
-- regularize≈。

realI→cauchy-retract : (x : CauchySeq)
  → realI→cauchy (cauchy→realI x) ≈ x
realI→cauchy-retract x =
  let z = regularize x
      a = realI→cauchy (cauchy→realI x)
      b = realI→cauchy (cauchy→realI z)
      x≈z : x ≈ z
      x≈z = Real.≈-sym {x = x} {y = z} (regularize≈ x)
      step1 : cauchy→realI x ≈ℝ cauchy→realI z
      step1 = cauchy→realI-cong x≈z
      step2 : a ≈ b
      step2 = realI→cauchy-cong step1
      step3 : b ≈ z
      step3 = regular-retract x
      step4 : a ≈ z
      step4 = Real.≈-trans {x = a} {y = b} {z = z} step2 step3
  in Real.≈-trans {x = a} {y = z} {z = x} step4 (regularize≈ x)
