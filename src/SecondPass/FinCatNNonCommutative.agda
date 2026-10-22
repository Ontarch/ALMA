------------------------------------------------------------------------
-- Non-commutative composition of permutation embeddings (n ≥ 3)
-- 置换嵌入的非交换复合（n ≥ 3）
--
-- When n ≥ 3, the permutation group Sₙ is non-abelian. Two results:
--   * Non-commutativity: taking f = swap01, g = swap12 gives
--     f ∘ g ≠ g ∘ f, so the two-layer sequences [f, g] and [g, f]
--     produce non-bisimilar cosmoi
--   * Period 3: c = swap01 ∘ swap12 is a 3-cycle (c³ = id), so the
--     iterated F₀ projection has period 3 rather than 2
-- Threshold: n = 3; for n = 2 the group is ℤ₂, commutative
-- 当 n ≥ 3 时，置换群 Sₙ 非交换。两个结果：
--   * 非交换性：取 f = swap01、g = swap12 时 f ∘ g ≠ g ∘ f，
--     故两层序列 [f,g] 与 [g,f] 给出不互模拟的宇宙
--   * 周期 3：c = swap01 ∘ swap12 是 3-循环（c³ = id），
--     故迭代 F₀ 投影周期为 3 而非 2
-- 阈值在 n = 3；n = 2 时群为 ℤ₂，交换
------------------------------------------------------------------------
{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module SecondPass.FinCatNNonCommutative where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (inspect; [_])
open import Relation.Binary.PropositionalEquality.Core using (cong; sym; trans; _≢_)
open import Relation.Binary.PropositionalEquality.Properties using (module ≡-Reasoning)
open ≡-Reasoning
open import Data.Nat using (ℕ; suc)
open import Data.Nat.Properties using (≤-pred; n≤0⇒n≡0)
open import Data.Product.Base using (proj₂; Σ; _,_)
open import Data.Fin.Base using (Fin; splitAt; join; opposite)
  renaming (zero to fzero; suc to fsuc)
open import Data.Fin.Properties using (join-splitAt; splitAt-join; opposite-involutive; toℕ-injective; toℕ<n)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.List.Base using ([]; _∷_)
open import Function.Base using (_∘_)

open import SecondPass.Terminal using (_≈C_)
open import SecondPass.FinCatNWitness
open import SecondPass.FinCatNTowerLemmas
open import SecondPass.FinCatNDefaultUnif
open import SecondPass.FinCatNPermutedEmbedding

module FinCatNNonCommutative (m' : ℕ) where

  -- m = suc m' gives n = 3 + m', so n ≥ 3
  -- m = suc m' 时 n = 3 + m'，故 n ≥ 3
  open FinCatN (suc m')
  open FinCatNTowerLemmas (suc m')
  open FinCatNPermutedEmbedding (suc m')

  -- swapTail: leave Fin 1, reverse Fin 2
  -- swapTail：Fin 1 不动，Fin 2 反转
  swapTail : Fin 1 ⊎ Fin 2 → Fin 1 ⊎ Fin 2
  swapTail (inj₁ j) = inj₁ j
  swapTail (inj₂ j) = inj₂ (opposite j)

  swapTail-involutive : ∀ x → swapTail (swapTail x) ≡ x
  swapTail-involutive (inj₁ j) = refl
  swapTail-involutive (inj₂ j) = cong inj₂ (opposite-involutive j)

  -- swap12-Fin3: Fin 3, exchange 1↔2, leave 0 fixed
  -- swap12-Fin3：Fin 3 上交换 1↔2，0 不动
  swap12-Fin3 : Fin 3 → Fin 3
  swap12-Fin3 i = join 1 2 (swapTail (splitAt 1 i))

  swap12-Fin3-involutive : ∀ i → swap12-Fin3 (swap12-Fin3 i) ≡ i
  swap12-Fin3-involutive i =
    begin
      swap12-Fin3 (swap12-Fin3 i)
        ≡⟨ refl ⟩
      join 1 2 (swapTail (splitAt 1 (join 1 2 (swapTail (splitAt 1 i)))))
        ≡⟨ cong (join 1 2)
             (cong swapTail (splitAt-join 1 2 (swapTail (splitAt 1 i)))) ⟩
      join 1 2 (swapTail (swapTail (splitAt 1 i)))
        ≡⟨ cong (join 1 2) (swapTail-involutive (splitAt 1 i)) ⟩
      join 1 2 (splitAt 1 i)
        ≡⟨ join-splitAt 1 2 i ⟩
      i
      ∎

  -- swapSum12: apply swap12-Fin3 to Fin 3, leave Fin m' untouched
  -- swapSum12：Fin 3 分量应用 swap12-Fin3，Fin m' 不动
  swapSum12 : Fin 3 ⊎ Fin m' → Fin 3 ⊎ Fin m'
  swapSum12 (inj₁ i) = inj₁ (swap12-Fin3 i)
  swapSum12 (inj₂ k) = inj₂ k

  swapSum12-involutive : ∀ x → swapSum12 (swapSum12 x) ≡ x
  swapSum12-involutive (inj₁ i) = cong inj₁ (swap12-Fin3-involutive i)
  swapSum12-involutive (inj₂ k) = refl

  -- swap12 on Fin n: exchange 1↔2, leave 0 and ≥ 3 fixed
  -- swap12 作用在 Fin n 上：交换 1↔2，0 及 ≥ 3 不动
  swap12 : Fin n → Fin n
  swap12 i = join 3 m' (swapSum12 (splitAt 3 i))

  swap12-involutive : ∀ a → swap12 (swap12 a) ≡ a
  swap12-involutive i =
    begin
      swap12 (swap12 i)
        ≡⟨ refl ⟩
      join 3 m' (swapSum12 (splitAt 3 (join 3 m' (swapSum12 (splitAt 3 i)))))
        ≡⟨ cong (join 3 m')
             (cong swapSum12 (splitAt-join 3 m' (swapSum12 (splitAt 3 i)))) ⟩
      join 3 m' (swapSum12 (swapSum12 (splitAt 3 i)))
        ≡⟨ cong (join 3 m') (swapSum12-involutive (splitAt 3 i)) ⟩
      join 3 m' (splitAt 3 i)
        ≡⟨ join-splitAt 3 m' i ⟩
      i
      ∎

  -- swap12 has period 2 (it is an involution)
  -- swap12 周期为 2（它是对合）
  iterPow-swap12-period2
    : ∀ k (a : Fin n)
    → iterPow (suc (suc k)) swap12 a ≡ iterPow k swap12 a
  iterPow-swap12-period2 = iterPow-involution-period2 swap12 swap12-involutive

  -- The three Fin 3 elements, with explicit types
  -- 三个 Fin 3 元素，显式类型
  Fin3-0 : Fin 3
  Fin3-0 = fzero
  Fin3-1 : Fin 3
  Fin3-1 = fsuc fzero
  Fin3-2 : Fin 3
  Fin3-2 = fsuc (fsuc fzero)

  -- c = swap01 ∘ swap12 acts on the three Fin 3 elements and on raised
  -- elements of Fin m'; each equation is definitional
  -- c = swap01 ∘ swap12 在三个 Fin 3 元素以及提升的 Fin m' 元素上的作用；
  -- 每一条等式都是定义性相等的
  c-at-0 : (swap01 ∘ swap12) (join 3 m' (inj₁ Fin3-0))
         ≡ join 3 m' (inj₁ Fin3-1)
  c-at-0 = refl
  c-at-1 : (swap01 ∘ swap12) (join 3 m' (inj₁ Fin3-1))
         ≡ join 3 m' (inj₁ Fin3-2)
  c-at-1 = refl
  c-at-2 : (swap01 ∘ swap12) (join 3 m' (inj₁ Fin3-2))
         ≡ join 3 m' (inj₁ Fin3-0)
  c-at-2 = refl
  c-at-raise : (j : Fin m')
            → (swap01 ∘ swap12) (join 3 m' (inj₂ j)) ≡ join 3 m' (inj₂ j)
  c-at-raise j = refl

  -- Fin 1 has a unique element: toℕ x = 0, hence x ≡ fzero
  -- Fin 1 只有一个元素：toℕ x = 0，故 x ≡ fzero
  Fin1-≡fzero : ∀ (x : Fin 1) → x ≡ fzero
  Fin1-≡fzero x = toℕ-injective {i = x} {j = fzero}
    (n≤0⇒n≡0 (≤-pred (toℕ<n x)))

  -- If splitAt 1 i = inj₁ x then i ≡ Fin3-0
  -- 若 splitAt 1 i = inj₁ x，则 i ≡ Fin3-0
  splitAt1→0 : ∀ (i : Fin 3) (x : Fin 1) → splitAt 1 i ≡ inj₁ x → i ≡ Fin3-0
  splitAt1→0 i x eq = begin
    i                           ≡⟨ sym (join-splitAt 1 2 i) ⟩
    join 1 2 (splitAt 1 i)      ≡⟨ cong (join 1 2) eq ⟩
    join 1 2 (inj₁ x)           ≡⟨ cong (join 1 2) (cong inj₁ (Fin1-≡fzero x)) ⟩
    join 1 2 (inj₁ fzero)       ≡⟨ refl ⟩
    Fin3-0                      ∎

  -- If splitAt 1 i = inj₂ j and splitAt 1 j = inj₁ x then i ≡ Fin3-1
  -- 若 splitAt 1 i = inj₂ j 且 splitAt 1 j = inj₁ x，则 i ≡ Fin3-1
  splitAt1→1 : ∀ (i : Fin 3) (j : Fin 2) (x : Fin 1)
             → splitAt 1 i ≡ inj₂ j → splitAt 1 j ≡ inj₁ x → i ≡ Fin3-1
  splitAt1→1 i j x eq1 eq2 = begin
    i                                         ≡⟨ sym (join-splitAt 1 2 i) ⟩
    join 1 2 (splitAt 1 i)                    ≡⟨ cong (join 1 2) eq1 ⟩
    join 1 2 (inj₂ j)                         ≡⟨ cong (join 1 2) (cong inj₂ (sym (join-splitAt 1 1 j))) ⟩
    join 1 2 (inj₂ (join 1 1 (splitAt 1 j))) ≡⟨ cong (join 1 2) (cong inj₂ (cong (join 1 1) eq2)) ⟩
    join 1 2 (inj₂ (join 1 1 (inj₁ x)))      ≡⟨ cong (join 1 2) (cong inj₂ (cong (join 1 1) (cong inj₁ (Fin1-≡fzero x)))) ⟩
    join 1 2 (inj₂ (join 1 1 (inj₁ fzero)))  ≡⟨ refl ⟩
    Fin3-1                                    ∎

  -- If splitAt 1 i = inj₂ j and splitAt 1 j = inj₂ x then i ≡ Fin3-2
  -- 若 splitAt 1 i = inj₂ j 且 splitAt 1 j = inj₂ x，则 i ≡ Fin3-2
  splitAt1→2 : ∀ (i : Fin 3) (j : Fin 2) (x : Fin 1)
             → splitAt 1 i ≡ inj₂ j → splitAt 1 j ≡ inj₂ x → i ≡ Fin3-2
  splitAt1→2 i j x eq1 eq2 = begin
    i                                         ≡⟨ sym (join-splitAt 1 2 i) ⟩
    join 1 2 (splitAt 1 i)                    ≡⟨ cong (join 1 2) eq1 ⟩
    join 1 2 (inj₂ j)                         ≡⟨ cong (join 1 2) (cong inj₂ (sym (join-splitAt 1 1 j))) ⟩
    join 1 2 (inj₂ (join 1 1 (splitAt 1 j))) ≡⟨ cong (join 1 2) (cong inj₂ (cong (join 1 1) eq2)) ⟩
    join 1 2 (inj₂ (join 1 1 (inj₂ x)))      ≡⟨ cong (join 1 2) (cong inj₂ (cong (join 1 1) (cong inj₂ (Fin1-≡fzero x)))) ⟩
    join 1 2 (inj₂ (join 1 1 (inj₂ fzero)))  ≡⟨ refl ⟩
    Fin3-2                                    ∎

  -- c = swap01 ∘ swap12
  -- c = swap01 ∘ swap12
  c : Fin n → Fin n
  c = swap01 ∘ swap12

  -- c³ = id on Fin 3 ⊎ Fin m', proved by nested splitAt 1 with inspect;
  -- no Fin constructor is pattern-matched
  -- c³ 在 Fin 3 ⊎ Fin m' 上等于恒等，经嵌套 splitAt 1 与 inspect 证明；
  -- 全程不匹配任何 Fin 构造子
  c₃-helper : ∀ (x : Fin 3 ⊎ Fin m')
            → iterPow 3 c (join 3 m' x) ≡ join 3 m' x
  c₃-helper (inj₂ j) = refl
  c₃-helper (inj₁ i) with splitAt 1 i | inspect (splitAt 1) i
  c₃-helper (inj₁ i) | inj₁ x | [ eq ] rewrite splitAt1→0 i x eq =
    begin
      iterPow 3 c (join 3 m' (inj₁ Fin3-0))
        ≡⟨ cong c (cong c c-at-0) ⟩
      c (c (join 3 m' (inj₁ Fin3-1)))
        ≡⟨ cong c c-at-1 ⟩
      c (join 3 m' (inj₁ Fin3-2))
        ≡⟨ c-at-2 ⟩
      join 3 m' (inj₁ Fin3-0)
    ∎
  c₃-helper (inj₁ i) | inj₂ j | [ eq1 ] with splitAt 1 j | inspect (splitAt 1) j
  c₃-helper (inj₁ i) | inj₂ j | [ eq1 ] | inj₁ x | [ eq2 ]
      rewrite splitAt1→1 i j x eq1 eq2 =
    begin
      iterPow 3 c (join 3 m' (inj₁ Fin3-1))
        ≡⟨ cong c (cong c c-at-1) ⟩
      c (c (join 3 m' (inj₁ Fin3-2)))
        ≡⟨ cong c c-at-2 ⟩
      c (join 3 m' (inj₁ Fin3-0))
        ≡⟨ c-at-0 ⟩
      join 3 m' (inj₁ Fin3-1)
    ∎
  c₃-helper (inj₁ i) | inj₂ j | [ eq1 ] | inj₂ x | [ eq2 ]
      rewrite splitAt1→2 i j x eq1 eq2 =
    begin
      iterPow 3 c (join 3 m' (inj₁ Fin3-2))
        ≡⟨ cong c (cong c c-at-2) ⟩
      c (c (join 3 m' (inj₁ Fin3-0)))
        ≡⟨ cong c c-at-0 ⟩
      c (join 3 m' (inj₁ Fin3-1))
        ≡⟨ c-at-1 ⟩
      join 3 m' (inj₁ Fin3-2)
    ∎

  -- c = swap01 ∘ swap12 is a 3-cycle: c³ = id
  -- c = swap01 ∘ swap12 是 3-循环：c³ = id
  c₃-cycle : ∀ a → iterPow 3 (swap01 ∘ swap12) a ≡ a
  c₃-cycle a = begin
    iterPow 3 c a
      ≡⟨ cong (iterPow 3 c) (sym (join-splitAt 3 m' a)) ⟩
    iterPow 3 c (join 3 m' (splitAt 3 a))
      ≡⟨ c₃-helper (splitAt 3 a) ⟩
    join 3 m' (splitAt 3 a)
      ≡⟨ join-splitAt 3 m' a ⟩
    a ∎

  -- Period 3 of c = swap01 ∘ swap12
  -- c = swap01 ∘ swap12 的周期 3
  iterPow-c₃-period3
    : ∀ k (a : Fin n)
    → iterPow (suc (suc (suc k))) (swap01 ∘ swap12) a
    ≡ iterPow k (swap01 ∘ swap12) a
  iterPow-c₃-period3 k a = c₃-cycle (iterPow k (swap01 ∘ swap12) a)

  fsuc-never-fzero : ∀ {k} {x : Fin k} → fsuc x ≢ fzero
  fsuc-never-fzero ()

  -- Non-commutativity: swap01 ∘ swap12 ≠ swap12 ∘ swap01, witnessed at A = 1
  -- 非交换性：swap01 ∘ swap12 ≠ swap12 ∘ swap01，在 A = 1 处见证
  swap01-swap12-noncommute
    : Σ (Fin n) λ A → (swap01 ∘ swap12) A ≢ (swap12 ∘ swap01) A
  swap01-swap12-noncommute =
    (fsuc fzero) , λ eq → fsuc-never-fzero eq

  -- Two-layer sequences [swap01, swap12] and [swap12, swap01] are not
  -- bisimilar: their F₀ projections differ at A = 1
  -- 两层序列 [swap01, swap12] 与 [swap12, swap01] 不互模拟：
  -- 它们在 A = 1 处的 F₀ 投影不同
  seq-noncommute-diverge
    : ¬ (iterPermutedSeq (swap01 ∷ swap12 ∷ []) cosmos-idN
         ≈C iterPermutedSeq (swap12 ∷ swap01 ∷ []) cosmos-idN)
  seq-noncommute-diverge eq =
    let
      A  = fsuc fzero
      a  = embed-obj 2 A
      sh = embed-shape 2 a
      F₀-eq  = eq ._≈C_.unfoldFunctor₀-eq {A = a} sh
      proj-eq = cong (proj-obj 2) F₀-eq
      left-eq  = iterPermutedSeq-F₀-accum (swap01 ∷ swap12 ∷ []) cosmos-idN A
      right-eq = iterPermutedSeq-F₀-accum (swap12 ∷ swap01 ∷ []) cosmos-idN A
      final = trans (sym left-eq) (trans proj-eq right-eq)
    in swap01-swap12-noncommute .proj₂ final
