------------------------------------------------------------------------
-- Non-commutative position permutations
--
-- Non-commutativity of the position permutation group Sₙ for n ≥ 3,
-- and the 3-cycle, on the carried M base. The algebra lives in the
-- carried position automorphism group PosAutˢ of ContainerAutomorphism
-- (Part A): a per-shape permutation with a carried two-sided inverse, no
-- naturality / subst field. To keep everything definitional and free of
-- Fin indexed matching (and hence of DecUIP/K), the finite position sets
-- are ordinary non-indexed enumerations Three / Two; matching their
-- constructors is legal under --cubical-compatible, the transpositions
-- are definitionally involutive, the 3-cycle reduces to refl in three
-- clauses, and every disequality is constructive no-confusion absorbed
-- by the empty pattern. This supplies the group-level fact that makes
-- the cosmos-level routing divergence unavoidable for n ≥ 3 (the two
-- orderings of s01, s12 already disagree at position 1), together with
-- the n = 2 abelian threshold.
--
-- 位置置换的非交换性
--
-- 携带式 M 底座上位置置换群 Sₙ 在 n ≥ 3 时的非交换性与 3-循环。代数
-- 落在 ContainerAutomorphism（A 部）的携带位置自同构群 PosAutˢ：携带
-- 双侧逆的逐形状置换，无自然性 / subst 字段。为使一切定义性且免于 Fin
-- 索引匹配（也即免于 DecUIP/K），有限位置集声明为普通的非索引枚举
-- Three / Two；在 --cubical-compatible 下匹配其构造子合法，对换定义性
-- 对合，3-循环三条子句即归约为 refl，每个不等都是构造性无混淆、由空
-- 模式吸收。这供给使宇宙层路由发散在 n ≥ 3 不可避免的群级事实（s01、
-- s12 的两种次序已在位置 1 处不同），以及 n = 2 的阿贝尔阈值。
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module Cosmos.M.PermutationNonCommutative where

open import Agda.Primitive using (lzero)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Sigma using (Σ; _,_)
open import Data.Unit.Polymorphic.Base using (⊤; tt)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥-elim)
open import Function.Base using (_∘_)
open import Relation.Nullary.Negation using (¬_)
open import Relation.Binary.PropositionalEquality.Core using (trans; sym; cong; _≢_)
open import Relation.Binary.PropositionalEquality using (inspect; [_])

import Cosmos.M.ContainerAutomorphism as CA

------------------------------------------------------------------------
-- The two finite position fibres as ordinary non-indexed enumerations
--
-- 两个有限位置纤维，作为普通非索引枚举

data Three : Set where
  t0 t1 t2 : Three

data Two : Set where
  w0 w1 : Two

------------------------------------------------------------------------
-- Part 1
--
-- S₃ is non-abelian and contains a 3-cycle.
--
-- 第一部分
--
-- S₃ 非阿贝尔且含一个 3-循环。

module S₃ where

  open CA.PositionPermutationGroup (⊤ {lzero}) (λ _ → Three) public

  -- s01 swaps t0 ↔ t1, fixing t2; s12 swaps t1 ↔ t2, fixing t0.
  --
  -- s01 交换 t0 ↔ t1、固定 t2；s12 交换 t1 ↔ t2、固定 t0。
  s01 : Three → Three
  s01 t0 = t1
  s01 t1 = t0
  s01 t2 = t2

  s12 : Three → Three
  s12 t0 = t0
  s12 t1 = t2
  s12 t2 = t1

  s01-invol : ∀ x → s01 (s01 x) ≡ x
  s01-invol t0 = refl
  s01-invol t1 = refl
  s01-invol t2 = refl

  s12-invol : ∀ x → s12 (s12 x) ≡ x
  s12-invol t0 = refl
  s12-invol t1 = refl
  s12-invol t2 = refl

  -- Lift an involutive function to a carried position automorphism whose
  -- two-sided inverse is itself.
  --
  -- 把对合函数提升为双侧逆即自身的携带位置自同构。
  mkInvol : (f : Three → Three) → (∀ x → f (f x) ≡ x) → PosAutˢ
  mkInvol f invol = record
    { τ       = λ _ → f
    ; τ⁻¹     = λ _ → f
    ; τ-τ⁻¹   = λ _ x → invol x
    ; τ⁻¹-τ   = λ _ x → invol x
    }

  a01 : PosAutˢ
  a01 = mkInvol s01 s01-invol

  a12 : PosAutˢ
  a12 = mkInvol s12 s12-invol

  c  : PosAutˢ   -- forward permutation s01 ∘ s12
  c  = a01 ∘PosAutˢ a12

  c' : PosAutˢ   -- forward permutation s12 ∘ s01
  c' = a12 ∘PosAutˢ a01

  -- c = s01 ∘ s12 acts as the 3-cycle t0 ↦ t1 ↦ t2 ↦ t0.
  --
  -- c = s01 ∘ s12 作用为 3-循环 t0 ↦ t1 ↦ t2 ↦ t0。
  c-at0 : τ c tt t0 ≡ t1
  c-at0 = refl
  c-at1 : τ c tt t1 ≡ t2
  c-at1 = refl
  c-at2 : τ c tt t2 ≡ t0
  c-at2 = refl

  c'-at1 : τ c' tt t1 ≡ t0
  c'-at1 = refl

  ----------------------------------------------------------------------
  -- Non-commutativity, witnessed at position 1
  --
  -- 非交换性，在位置 1 处见证

  t2≢t0 : ¬ (t2 ≡ t0)
  t2≢t0 ()

  s01-s12-noncommute : ¬ (c ≈PAˢ c')
  s01-s12-noncommute eq = t2≢t0 (trans (eq tt t1) (sym c'-at1))

  -- Σ-witness form: a position at which the two composites disagree.
  --
  -- Σ 见证形式：存在一个位置使两个复合不同。
  noncommute-witness : Σ Three λ x → τ c tt x ≢ τ c' tt x
  noncommute-witness = t1 , λ eq → t2≢t0 (trans eq (sym c'-at1))

  ----------------------------------------------------------------------
  -- Exact period 3 of c = s01 ∘ s12
  --
  -- c = s01 ∘ s12 恰周期 3

  c²-at0 : τ (c ∘PosAutˢ c) tt t0 ≡ t2
  c²-at0 = refl

  c³≈id : ((c ∘PosAutˢ c) ∘PosAutˢ c) ≈PAˢ idPosAutˢ
  c³≈id _ t0 = refl
  c³≈id _ t1 = refl
  c³≈id _ t2 = refl

  t1≢t0 : ¬ (t1 ≡ t0)
  t1≢t0 ()

  -- c ≠ id and c² ≠ id, together with c³ = id, make the order exactly 3.
  --
  -- c ≠ id 且 c² ≠ id，连同 c³ = id，其阶恰为 3。
  c-nonid : ¬ (c ≈PAˢ idPosAutˢ)
  c-nonid eq = t1≢t0 (eq tt t0)

  c²-nonid : ¬ ((c ∘PosAutˢ c) ≈PAˢ idPosAutˢ)
  c²-nonid eq = t2≢t0 (eq tt t0)

  c³-fun : ∀ x → (τ c tt ∘ τ c tt ∘ τ c tt) x ≡ x
  c³-fun t0 = refl
  c³-fun t1 = refl
  c³-fun t2 = refl

  -- Routing divergence precondition for the cosmos-level argument: the
  -- two orderings act differently at position 1.
  --
  -- 宇宙层论证所需的路由发散前提：两种次序在位置 1 处作用不同。
  routing-diverges : τ c tt t1 ≢ τ c' tt t1
  routing-diverges eq = t2≢t0 (trans eq (sym c'-at1))

------------------------------------------------------------------------
-- Part 2
--
-- S₂ = ℤ₂ is abelian (the n = 2 threshold).
--
-- 第二部分
--
-- S₂ = ℤ₂ 阿贝尔（n = 2 阈值）。

module S₂ where

  open CA.PositionPermutationGroup (⊤ {lzero}) (λ _ → Two)

  sw : Two → Two
  sw w0 = w1
  sw w1 = w0

  sw-invol : ∀ x → sw (sw x) ≡ x
  sw-invol w0 = refl
  sw-invol w1 = refl

  swA : PosAutˢ
  swA = record
    { τ       = λ _ → sw
    ; τ⁻¹     = λ _ → sw
    ; τ-τ⁻¹   = λ _ x → sw-invol x
    ; τ⁻¹-τ   = λ _ x → sw-invol x
    }

  w0≢w1 : ¬ (w0 ≡ w1)
  w0≢w1 ()

  w1≢w0 : ¬ (w1 ≡ w0)
  w1≢w0 ()

  -- A carried two-position automorphism is determined by its value at
  -- w0; the carried left-inverse law forces the value at w1 to be sw of
  -- it. Only the left-inverse law and disjointness of the Two
  -- constructors are used.
  --
  -- 携带的二元位置自同构由其在 w0 处的值决定；携带的左逆律强制其在 w1
  -- 处的值为该值的 sw。仅用左逆律与 Two 构造子的不相交性。
  at1-forced : (φ : PosAutˢ)
             → τ φ tt w1 ≡ sw (τ φ tt w0)
  at1-forced φ
    with τ φ tt w0 | τ φ tt w1 | τ⁻¹-τ φ tt w0 | τ⁻¹-τ φ tt w1
  ... | w0 | w0 | g0 | h = ⊥-elim (w0≢w1 (trans (sym g0) h))
  ... | w0 | w1 | _  | _ = refl
  ... | w1 | w0 | _  | _ = refl
  ... | w1 | w1 | g1 | h = ⊥-elim (w1≢w0 (trans (sym h) g1))

  -- Pointwise equality with id / swap given the value at w0 as an
  -- explicit equation.
  --
  -- 给定 w0 处的值等式，给出与恒等 / 交换的逐点相等。
  id-case : (φ : PosAutˢ) → τ φ tt w0 ≡ w0 → φ ≈PAˢ idPosAutˢ
  id-case φ e tt w0 = e
  id-case φ e tt w1 = trans (at1-forced φ) (cong sw e)

  sw-case : (φ : PosAutˢ) → τ φ tt w0 ≡ w1 → φ ≈PAˢ swA
  sw-case φ e tt w0 = e
  sw-case φ e tt w1 = trans (at1-forced φ) (cong sw e)

  -- Every two-position automorphism is either the identity or the swap.
  --
  -- 每个二元位置自同构不是恒等就是该交换。
  classify : (φ : PosAutˢ)
           → (φ ≈PAˢ idPosAutˢ) ⊎ (φ ≈PAˢ swA)
  classify φ with τ φ tt w0 | inspect (τ φ tt) w0
  ... | w0 | [ e ] = inj₁ (id-case φ e)
  ... | w1 | [ e ] = inj₂ (sw-case φ e)

  sw²≈id : (swA ∘PosAutˢ swA) ≈PAˢ idPosAutˢ
  sw²≈id _ w0 = refl
  sw²≈id _ w1 = refl

  -- S₂ is abelian: classifying both factors as id or sw leaves four
  -- cases, each closed by congruence up to pointwise equality (id is
  -- the identity function and sw is an involution).
  --
  -- S₂ 阿贝尔：把两个因子分类为 id 或 sw 后剩四种情形，每种在逐点相等
  -- 下由同余闭合（id 为恒等函数、sw 对合）。
  S₂-abelian : (φ ψ : PosAutˢ)
             → (φ ∘PosAutˢ ψ) ≈PAˢ (ψ ∘PosAutˢ φ)
  S₂-abelian φ ψ with classify φ | classify ψ
  ... | inj₁ φ≈id | inj₁ ψ≈id = λ sh x →
        trans (∘PosAutˢ-resp-≈ {φ = φ} {φ' = idPosAutˢ}
                               {ψ = ψ} {ψ' = idPosAutˢ} φ≈id ψ≈id sh x)
              (sym (∘PosAutˢ-resp-≈ {φ = ψ} {φ' = idPosAutˢ}
                                   {ψ = φ} {ψ' = idPosAutˢ} ψ≈id φ≈id sh x))
  ... | inj₁ φ≈id | inj₂ ψ≈sw = λ sh x →
        trans (∘PosAutˢ-resp-≈ {φ = φ} {φ' = idPosAutˢ}
                               {ψ = ψ} {ψ' = swA} φ≈id ψ≈sw sh x)
              (sym (∘PosAutˢ-resp-≈ {φ = ψ} {φ' = swA}
                                   {ψ = φ} {ψ' = idPosAutˢ} ψ≈sw φ≈id sh x))
  ... | inj₂ φ≈sw | inj₁ ψ≈id = λ sh x →
        trans (∘PosAutˢ-resp-≈ {φ = φ} {φ' = swA}
                               {ψ = ψ} {ψ' = idPosAutˢ} φ≈sw ψ≈id sh x)
              (sym (∘PosAutˢ-resp-≈ {φ = ψ} {φ' = idPosAutˢ}
                                   {ψ = φ} {ψ' = swA} ψ≈id φ≈sw sh x))
  ... | inj₂ φ≈sw | inj₂ ψ≈sw = λ sh x →
        trans (∘PosAutˢ-resp-≈ {φ = φ} {φ' = swA}
                               {ψ = ψ} {ψ' = swA} φ≈sw ψ≈sw sh x)
              (sym (∘PosAutˢ-resp-≈ {φ = ψ} {φ' = swA}
                                   {ψ = φ} {ψ' = swA} ψ≈sw φ≈sw sh x))
