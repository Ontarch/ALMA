------------------------------------------------------------------------
-- A complex 2×2 unitary as a finite measurement instrument
--
-- AmplitudeComp proves that U = [[u, v], [-conj v, conj u]], carried
-- with |u|² + |v|² = 1, conserves total norm on every input pair. Here
-- the same matrix is equipped with the Instrument structure of
-- Measurement: each basis-input column has Born weights summing to one.
--
-- The matrix is held as a Vec of certified-normalised columns and all
-- Fin indexing goes through the polymorphic Vec lookup, so no concrete
-- Fin literal is ever pattern-matched (which Cubical Agda rejects).
-- unitary2-normalized is the same conservation on an arbitrary
-- normalised input pair, interference included.
--
-- 复 2×2 幺正作为有限测量仪器
--
-- AmplitudeComp 已证 U=[[u,v],[-conj v,conj u]] 在 |u|²+|v|²=1 下对任意
-- 输入对保持总范数。此处把同一矩阵装备为 Measurement 的 Instrument：
-- 每个基输入列的 Born 权重和为一。
--
-- 矩阵存为一列列“携带归一证明”的 Vec，所有 Fin 索引经多态 Vec lookup
-- 完成，绝不模式匹配具体 Fin 字面量（Cubical Agda 不支持）。
-- unitary2-normalized 是同一守恒在任意归一输入对上的形式，含干涉。
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module ALMA.Physics.Quantum.UnitaryInstrument where

open import Data.Nat.Base using (ℕ)
open import Data.Fin.Base using (Fin; zero; suc)
open import Data.Product.Base using (Σ; _,_; proj₁; proj₂)
open import Data.Vec using (Vec; []; _∷_; lookup)
open import Data.Rational using (ℚ; 0ℚ; 1ℚ; _+_; _*_; -_)
open import Data.Rational.Properties using
  (+-identityʳ; +-comm; +-identityˡ; +-inverseʳ; +-assoc; neg-distribˡ-*; neg-distribʳ-*)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; sym; trans; cong; cong₂; module ≡-Reasoning)

open import ALMA.Physics.Quantum.Gaussian using
  (ℂ; conj; norm²; norm²-conj; _+ᶜ_; _*ᶜ_)
open import ALMA.Physics.Quantum.FiniteVec using (sumFin)
open import ALMA.Physics.Quantum.Measurement using (Instrument)
open import ALMA.Physics.Quantum.AmplitudeComp using
  (-ᶜ_; unitary2-pres; u₃₄₅; v₃₄₅; pythagoras-345)

private
  -- Double negation and (-x)² = x² over ℚ.
  --
  -- ℚ 上的双重否定与 (-x)² = x²。
  ‿-‿ : ∀ x → - (- x) ≡ x
  ‿-‿ x = let open ≡-Reasoning in begin
    - (- x)
    ≡⟨ sym (+-identityˡ (- (- x))) ⟩
    0ℚ + - (- x)
    ≡⟨ cong (λ z → z + - (- x)) (sym (+-inverseʳ x)) ⟩
    (x + - x) + - (- x)
    ≡⟨ +-assoc x (- x) (- (- x)) ⟩
    x + ((- x) + - (- x))
    ≡⟨ cong (x +_) (+-inverseʳ (- x)) ⟩
    x + 0ℚ
    ≡⟨ +-identityʳ x ⟩
    x ∎

  sq-neg : ∀ x → (- x) * (- x) ≡ x * x
  sq-neg x = let open ≡-Reasoning in begin
    (- x) * (- x)
    ≡⟨ sym (neg-distribˡ-* x (- x)) ⟩
    - (x * (- x))
    ≡⟨ cong -_ (sym (neg-distribʳ-* x x)) ⟩
    - (- (x * x))
    ≡⟨ ‿-‿ (x * x) ⟩
    x * x ∎

  -- Componentwise negation leaves the squared norm fixed.
  --
  -- 逐分量取负不改变平方范数。
  norm²-negᶜ : ∀ z → norm² (-ᶜ z) ≡ norm² z
  norm²-negᶜ (a , b) = cong₂ _+_ (sq-neg a) (sq-neg b)

  -- |-conj z|² = |z|²: conjugation then sign both preserve norm.
  --
  -- |-conj z|² = |z|²：共轭与取负均保范数。
  neg-conj-norm : ∀ z → norm² (-ᶜ conj z) ≡ norm² z
  neg-conj-norm z = trans (norm²-negᶜ (conj z)) (norm²-conj z)

  -- Sum of squared norms along a Vec, polymorphic in its length.
  --
  -- 沿 Vec 的平方范数之和，长度多态。
  sumNorm : ∀ {n} → Vec ℂ n → ℚ
  sumNorm []       = 0ℚ
  sumNorm (x ∷ xs) = norm² x + sumNorm xs

  -- The Vec fold agrees with the Fin sumFin over a polymorphic lookup.
  --
  -- Vec 折叠与经多态 lookup 的 Fin sumFin 一致。
  sumFin≡sumNorm : ∀ {n} (r : Vec ℂ n) →
                   sumFin (λ i → norm² (lookup r i)) ≡ sumNorm r
  sumFin≡sumNorm []       = refl
  sumFin≡sumNorm (x ∷ xs) = let open ≡-Reasoning in begin
    norm² x + sumFin (λ i → norm² (lookup xs i))
    ≡⟨ cong (norm² x +_) (sumFin≡sumNorm xs) ⟩
    norm² x + sumNorm xs ∎

------------------------------------------------------------------------
-- The unitary matrix as an instrument
--
-- 幺正矩阵装配为仪器

-- A column together with a proof that its Born weights sum to one.
--
-- 一列及其 Born 权重和为一的证明。
CertCol : Set
CertCol = Σ (Vec ℂ 2) λ col → sumNorm col ≡ 1ℚ

-- U = [[u, v], [-conj v, conj u]], stored column-wise
--
-- Each column is paired with its normalisation proof derived from
-- |u|² + |v|² = 1.
--
-- U=[[u,v],[-conj v,conj u]]，按列存放
--
-- 每列配对其由 |u|²+|v|²=1 导出的归一证明。
unitaryInstrument : (u v : ℂ) →
                    norm² u + norm² v ≡ 1ℚ → Instrument 2 2
unitaryInstrument u v h = record { amp = amp ; norm = norm }
  where
  col0 : Vec ℂ 2
  col0 = u ∷ (-ᶜ conj v) ∷ []

  col1 : Vec ℂ 2
  col1 = v ∷ conj u ∷ []

  -- Column 0: |u|² + |-conj v|² = |u|² + |v|² = 1.
  --
  -- 第 0 列：|u|² + |-conj v|² = |u|² + |v|² = 1。
  p0 : sumNorm col0 ≡ 1ℚ
  p0 = let open ≡-Reasoning in begin
    sumNorm col0
    ≡⟨ cong (norm² u +_) (+-identityʳ (norm² (-ᶜ conj v))) ⟩
    norm² u + norm² (-ᶜ conj v)
    ≡⟨ cong (norm² u +_) (neg-conj-norm v) ⟩
    norm² u + norm² v
    ≡⟨ h ⟩
    1ℚ ∎

  -- Column 1: |v|² + |conj u|² = |v|² + |u|² = 1.
  --
  -- 第 1 列：|v|² + |conj u|² = |v|² + |u|² = 1。
  p1 : sumNorm col1 ≡ 1ℚ
  p1 = let open ≡-Reasoning in begin
    sumNorm col1
    ≡⟨ cong (norm² v +_) (+-identityʳ (norm² (conj u))) ⟩
    norm² v + norm² (conj u)
    ≡⟨ cong (norm² v +_) (norm²-conj u) ⟩
    norm² v + norm² u
    ≡⟨ +-comm (norm² v) (norm² u) ⟩
    norm² u + norm² v
    ≡⟨ h ⟩
    1ℚ ∎

  cols : Vec CertCol 2
  cols = (col0 , p0) ∷ (col1 , p1) ∷ []

  -- Entry (i , j) is row i of the certified column j.
  --
  -- 表项 (i , j) 即第 j 条认证列的第 i 行。
  amp : Fin 2 → Fin 2 → ℂ
  amp i j = lookup (proj₁ (lookup cols j)) i

  -- Each column's certificate is retrieved polymorphically by j.
  --
  -- 每列的证书按 j 多态取出。
  norm : (j : Fin 2) → sumFin (λ i → norm² (amp i j)) ≡ 1ℚ
  norm j = trans (sumFin≡sumNorm (proj₁ (lookup cols j)))
                 (proj₂ (lookup cols j))

------------------------------------------------------------------------
-- Conservation on an arbitrary normalised input pair
--
-- 任意归一输入对上的守恒

-- A normalised input pair (|α|² + |β|² = 1) is sent to a normalised
-- output pair
--
-- Unlike the basis-column facts this runs over a superposition, so the
-- cancelled terms are the interference cross-terms handled by
-- cross-opposite.
--
-- 归一输入对（|α|²+|β|²=1）映到归一输出对
--
-- 与基列事实不同，它作用于叠加态，被消去的正是 cross-opposite 处理的
-- 干涉交叉项。
unitary2-normalized : ∀ (u v α β : ℂ) →
                      norm² u + norm² v ≡ 1ℚ →
                      norm² α + norm² β ≡ 1ℚ →
                      norm² (u *ᶜ α +ᶜ v *ᶜ β)
                    + norm² ((-ᶜ conj v) *ᶜ α +ᶜ conj u *ᶜ β)
                    ≡ 1ℚ
unitary2-normalized u v α β h hn =
  trans (unitary2-pres u v α β h) hn

------------------------------------------------------------------------
-- Rational-complex instance
--
-- u = 3/5, v = (4/5)i.
--
-- 有理复实例
--
-- u = 3/5、v = (4/5)i。

-- The concrete 3/5–4/5 unitary is a finite instrument with every column
-- of Born weights summing to one.
--
-- 具体的 3/5–4/5 幺正是一个有限仪器，每列 Born 权重和为一。
unitaryInstrument-345 : Instrument 2 2
unitaryInstrument-345 =
  unitaryInstrument u₃₄₅ v₃₄₅ pythagoras-345
