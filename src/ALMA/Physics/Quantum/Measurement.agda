------------------------------------------------------------------------
-- Measurement as a weighted, nondeterministic edge family
--
-- An instrument sends each input to every possible outcome, carrying a
-- Gaussian amplitude on each input→outcome edge. The squared amplitudes
-- are the computational-basis Born weights; column normalisation (sum
-- of weights equal to one) is carried as a hypothesis, not assumed for
-- free.
--
-- The structural side of a transition is a FiberAdjˢ, which carries
-- only an equivalence between edge fibres. It has no scalar. The
-- AmplitudeFibre equipment adds the per-edge amplitude, and
-- fibre-gap shows that data is independent: the very same fibre
-- adjacency admits two amplitudes with distinct Born weights.
--
-- 测量即带权非确定边族
--
-- 仪器把每个输入送到所有可能结果，并在每条“输入→结果”边上携带高斯
-- 振幅；振幅平方即计算基 Born 权重，列归一化（权重和为一）作为假设
-- 携带，不免费假定。
--
-- 转移的结构面是 FiberAdjˢ，它只携带边纤维之间的等价，不含标量。
-- AmplitudeFibre 装备补上逐边振幅；fibre-gap 表明该数据独立：同一个
-- 纤维伴随可配两个 Born 权重不同的振幅。
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module ALMA.Physics.Quantum.Measurement where

open import Data.Nat.Base using (ℕ)
open import Data.Fin.Base using (Fin)
open import Data.Product.Base using (_,_)
open import Data.Rational using (ℚ; 0ℚ; 1ℚ; _+_; _*_; _/_)
open import Data.Rational.Properties using (*-zeroˡ; *-identityˡ; +-identityʳ)
open import Data.Integer.Base using (1ℤ)
open import Relation.Binary.PropositionalEquality using
  (_≡_; _≢_; refl; sym; trans; cong; module ≡-Reasoning)
open import Relation.Nullary.Negation.Core using (¬_)

open import ALMA.Base.MCorrSetoid using (EqOn; FiberAdjˢ; idAdjˢ; propEqOn)
open import ALMA.Physics.Quantum.Gaussian using (ℂ; norm²)
open import ALMA.Physics.Quantum.FiniteVec using (sumFin)

------------------------------------------------------------------------
-- Finite instruments and the Born distribution
--
-- 有限仪器与 Born 分布

-- An instrument from n inputs to m outcomes
--
-- amp i j is the amplitude for input j to yield outcome i, with each
-- column normalised.
--
-- 从 n 个输入到 m 个结果的仪器
--
-- amp i j 是输入 j 得结果 i 的振幅，每列归一化。
record Instrument (m n : ℕ) : Set where
  field
    amp  : Fin m → Fin n → ℂ
    norm : (j : Fin n) → sumFin (λ i → norm² (amp i j)) ≡ 1ℚ
open Instrument

-- Born weight of outcome i for input j.
--
-- 输入 j 得结果 i 的 Born 权重。
born : ∀ {m n} → Instrument m n → Fin n → Fin m → ℚ
born M j i = norm² (amp M i j)

-- For every input the Born weights form a probability distribution.
--
-- 对每个输入，Born 权重构成概率分布（和为一）。
born-normalized : ∀ {m n} (M : Instrument m n) (j : Fin n) →
                  sumFin (born M j) ≡ 1ℚ
born-normalized M j = norm M j

------------------------------------------------------------------------
-- Quantitative fibre equipment
--
-- 定量纤维装备

-- A carrier fibre equipped with an equivalence and a Gaussian
-- amplitude on each element
--
-- FiberAdjˢ supplies the structural correspondence between fibres; amp
-- is the additional scalar label that measurement requires and that no
-- adjunction carries.
--
-- 在载体纤维上装备等价与逐元素高斯振幅
--
-- FiberAdjˢ 提供纤维间的结构对应；amp 是测量所需、而任何伴随都不携带
-- 的额外标量标签。
record AmplitudeFibre (P : Set) : Set₁ where
  field
    eqOn : EqOn P
    amp  : P → ℂ

------------------------------------------------------------------------
-- Gap: a fibre adjacency does not determine amplitudes
--
-- 缺口：纤维伴随不决定振幅

-- One third (½ is provided by the standard library).
--
-- 三分之一（½ 由标准库提供）。
private
  ⅓ : ℚ
  ⅓ = 1ℤ / 3

-- norm² of a real amplitude (q , 0) is q².
--
-- 实振幅 (q , 0) 的平方范数为 q²。
norm²-real : ∀ q → norm² (q , 0ℚ) ≡ q * q
norm²-real q = let open ≡-Reasoning in begin
  q * q + 0ℚ * 0ℚ
  ≡⟨ cong (q * q +_) (*-zeroˡ 0ℚ) ⟩
  q * q + 0ℚ
  ≡⟨ +-identityʳ (q * q) ⟩
  q * q ∎

-- The one-outcome edge fibre and its unique structural adjacency.
--
-- 单结果边纤维及其唯一的结构伴随。
Edge : Set
Edge = Fin 1

structural : FiberAdjˢ (propEqOn Edge) (propEqOn Edge)
structural = idAdjˢ (propEqOn Edge)

-- Two real amplitudes over that single edge, of unit and one-third
-- weight respectively.
--
-- 该单条边上的两个实振幅，权重分别为 1 与 1/9。
a₁ a₂ : ℂ
a₁ = (1ℚ , 0ℚ)
a₂ = (⅓ , 0ℚ)

-- The two fibres share the same eqOn (hence the same structural
-- adjacency above); only the amplitude differs
--
-- The amp functions do not inspect the (unique) edge, avoiding
-- constructor-indexed splits.
--
-- 两个纤维共用同一 eqOn（因而共用上面的同一结构伴随），仅振幅不同
--
-- amp 函数不检视（唯一的）边，避免按构造子索引拆分。
fibre₁ : AmplitudeFibre Edge
fibre₁ = record { eqOn = propEqOn Edge ; amp = λ _ → a₁ }

fibre₂ : AmplitudeFibre Edge
fibre₂ = record { eqOn = propEqOn Edge ; amp = λ _ → a₂ }

q₁ q₂ : ℚ
q₁ = 1ℚ
q₂ = ⅓ * ⅓

weight₁ : norm² a₁ ≡ q₁
weight₁ = trans (norm²-real 1ℚ) (*-identityˡ 1ℚ)

weight₂ : norm² a₂ ≡ q₂
weight₂ = norm²-real ⅓

-- 1 ≠ 1/9: in normal form the denominators are 1 (zero) and 9 (suc),
-- distinct constructors, so the assumed equality is itself absurd.
--
-- 1 ≠ 1/9：规范形分母分别为 1（zero）与 9（suc），是异类构造子，
-- 故所假设的等式本身荒谬。
q₁≢q₂ : q₁ ≢ q₂
q₁≢q₂ ()

-- The gap: over the same singleton edge fibre and the same structural
-- adjacency, the two amplitude fibres assign unequal Born weights
--
-- The amplitude (hence the probability) is therefore data that
-- FiberAdjˢ neither carries nor can recover.
--
-- 缺口：在同一条单结果边纤维、同一结构伴随上，两个振幅纤维给出不相等
-- 的 Born 权重
--
-- 故振幅（以及概率）是 FiberAdjˢ 既不携带、也无法恢复的数据。
fibre-gap : ¬ (norm² a₁ ≡ norm² a₂)
fibre-gap eq = q₁≢q₂ (trans (trans (sym weight₁) eq) weight₂)
