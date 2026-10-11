------------------------------------------------------------------------
-- Generic carried terminal coalgebra for an arbitrary setoid edge
-- family
--
-- M is coinductive, hence by construction the greatest fixpoint of the
-- indexed edge-family functor
--   F X i = Σ (A i) λ a → (j : I) → E i a j → X j;
-- guarded corecursion supplies existence and the carried bisimulation
-- _≈Mˢ_ supplies uniqueness. Nothing here assumes determinism: the
-- child map carries the edge witness e rather than the constructive
-- container edge (p , refl), and no equality is matched.
--
-- The deterministic container terminal coalgebra (Cosmos/M) is the
-- specialisation at E i a j = Σ Pos λ p → j ≡ nextOf i a p, where the
-- carried edge is always (p , refl).
--
-- 任意 setoid 边族的泛型携带式终余代数
--
-- M 是余归纳的，故按构造即索引边族函子
-- F X i = Σ (A i) λ a → (j : I) → E i a j → X j 的最大不动点；受保护
-- 余递归给存在性，携带式互模拟 _≈Mˢ_ 给唯一性。此处不假设确定性：
-- child 映射携带边见证 e，而非容器的构造性边 (p , refl)，且不匹配任何
-- 等式。
--
-- 确定性容器终余代数（Cosmos/M）是
-- E i a j = Σ Pos λ p → j ≡ nextOf i a p、携带边恒为 (p , refl) 处的
-- 特例。
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module ALMA.Base.MCorrSetoidCoalg where

open import Agda.Primitive using (Level; lsuc; _⊔_)
open import Agda.Builtin.Sigma using (_,_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality.Core using (cong; sym; trans)

open import Categories.Category.Core using (Category)

open import ALMA.Base.MCorr using (M)
open import ALMA.Base.MCorrSetoid using
  (SysEq; EqOn; _≈Mˢ_; ≈Mˢ-refl; ≈Mˢ-sym; ≈Mˢ-trans; idAdjˢ)
open _≈Mˢ_ public

module _ {i a b ℓa ℓe : Level} (X : SysEq i a b ℓa ℓe) where

  open SysEq X

  -- The carrier trees and the carried bisimulation.
  --
  -- 载体树与携带式互模拟。
  Mˣ : I → Set (i ⊔ a ⊔ b)
  Mˣ = M A E

  ≈ˣ : ∀ {x : I} → Mˣ x → Mˣ x → Set (i ⊔ a ⊔ b ⊔ ℓa ⊔ ℓe)
  ≈ˣ {x = x} = _≈Mˢ_ ≈A ≈E {x = x}

  ≈ˣ-refl : ∀ {x : I} (t : Mˣ x) → ≈ˣ t t
  ≈ˣ-refl = ≈Mˢ-refl ≈A ≈E

  ≈ˣ-sym : ∀ {x : I} {t s : Mˣ x} → ≈ˣ t s → ≈ˣ s t
  ≈ˣ-sym = ≈Mˢ-sym ≈A ≈E

  ≈ˣ-trans : ∀ {x : I} {t m s : Mˣ x} → ≈ˣ t m → ≈ˣ m s → ≈ˣ t s
  ≈ˣ-trans = ≈Mˢ-trans ≈A ≈E

  ----------------------------------------------------------------------
  -- One-step state coalgebra
  --
  -- At index i the state x carries a label and, for every target index
  -- j and edge e out of that label, a child state at j. The edge
  -- witness is data: several e may share a j, so a coalgebra may be
  -- nondeterministic.
  --
  -- 一步状态余代数
  --
  -- 在索引 i，状态 x 携带一个标签，并对每个目标索引 j 与该标签下的每条
  -- 边 e 携带 j 处的子状态。边见证是数据：同一 j 可有多条 e，故余代数
  -- 可以是非确定的。

  record Coalgebra (u : Level) (Xst : I → Set u)
         : Set (i ⊔ u ⊔ a ⊔ b) where
    field
      label : (xᵢ : I) → Xst xᵢ → A xᵢ
      child : (xᵢ : I) (x : Xst xᵢ) (y : I)
              (e : E xᵢ (label xᵢ x) y) → Xst y
  open Coalgebra public

  -- Anamorphism: read the head and, along every carried edge, recurse
  -- into the corresponding child. Copatterns are guarded and match e as
  -- a plain datum.
  --
  -- Anamorphism：读头部，并沿每条携带边递归到相应子状态。copattern
  -- 受保护，且把 e 当作普通数据匹配。
  ana : ∀ {u : Level} {Xst : I → Set u}
        (γ : Coalgebra u Xst)
      → (xᵢ : I) (x : Xst xᵢ) → Mˣ xᵢ
  ana γ xᵢ x .M.here      = label γ xᵢ x
  ana γ xᵢ x .M.below y e = ana γ y (child γ xᵢ x y e)

  -- Observation coalgebra of a node: states are trees, label reads the
  -- head and child is the raw continuation. ana of it rebuilds the
  -- tree.
  --
  -- 节点的观察余代数：状态即树，label 读头部，child 即原始延续。对其
  -- 取 ana 即重建该树。
  unfold-coalgebra : Coalgebra (i ⊔ a ⊔ b) Mˣ
  unfold-coalgebra .label xᵢ t     = M.here t
  unfold-coalgebra .child xᵢ t y e = M.below t y e

  ----------------------------------------------------------------------
  -- Eta / terminality
  --
  -- ana of the observation coalgebra rebuilds a tree bisimilar to the
  -- original, in both directions. The identity edge adjunction aligns
  -- fibres, and every recursive call is guarded.
  --
  -- eta / 终性
  --
  -- 对观察余代数取 ana，重建出与原树双向互模拟的树。恒等边伴随对齐
  -- 纤维，每个递归调用均受保护。

  mutual
    ana-unfold : ∀ {xᵢ : I} (t : Mˣ xᵢ)
               → ≈ˣ (ana unfold-coalgebra xᵢ t) t
    ana-unfold {xᵢ = xᵢ} t .here-eq = EqOn.refl (≈A xᵢ)
    ana-unfold {xᵢ = xᵢ} t .below-eq y =
        idAdjˢ (≈E xᵢ (M.here t) y)
      , ( (λ e → ana-unfold (M.below t y e))
        , (λ e → ana-unfold˘ (M.below t y e)) )

    ana-unfold˘ : ∀ {xᵢ : I} (t : Mˣ xᵢ)
                → ≈ˣ t (ana unfold-coalgebra xᵢ t)
    ana-unfold˘ {xᵢ = xᵢ} t .here-eq = EqOn.refl (≈A xᵢ)
    ana-unfold˘ {xᵢ = xᵢ} t .below-eq y =
        idAdjˢ (≈E xᵢ (M.here t) y)
      , ( (λ e → ana-unfold˘ (M.below t y e))
        , (λ e → ana-unfold (M.below t y e)) )

  ----------------------------------------------------------------------
  -- Category of coalgebras
  --
  -- Objects are one-step coalgebras at the tree's own universe;
  -- morphisms are state maps carrying the bisimulation that the target
  -- anamorphism rebuilds the source one; the observation coalgebra is
  -- the terminal object. Morphism equality is pointwise propositional
  -- equality, so the category laws need no function extensionality;
  -- terminality is up to bisimulation.
  --
  -- 余代数范畴
  --
  -- 对象是树自身宇宙处的一步余代数；态射是状态映射，携带“目标
  -- anamorphism 重建源 anamorphism”这一互模拟；观察余代数为终对象。
  -- 态射相等取逐点命题相等，故范畴律无需函数外延性；终性在互模拟意义
  -- 下成立。

  private
    u0   = i ⊔ a ⊔ b
    ℓh   = i ⊔ a ⊔ b ⊔ ℓa ⊔ ℓe
    ℓo   = lsuc ℓh
    ℓeq  = i ⊔ a ⊔ b

  record CoalgObj : Set ℓo where
    constructor mkCoalg
    field
      Xst : I → Set u0
      γ   : Coalgebra u0 Xst
  open CoalgObj public

  record Coalg⇒ (Y Z : CoalgObj) : Set ℓh where
    field
      map  : ∀ xᵢ → Xst Y xᵢ → Xst Z xᵢ
      comm : ∀ xᵢ (x : Xst Y xᵢ)
           → ≈ˣ (ana (γ Z) xᵢ (map xᵢ x)) (ana (γ Y) xᵢ x)
  open Coalg⇒ public

  idCoalg : ∀ (Y : CoalgObj) → Coalg⇒ Y Y
  idCoalg Y .map _ x = x
  idCoalg Y .comm xᵢ x = ≈ˣ-refl (ana (γ Y) xᵢ x)

  compCoalg : ∀ {Y Z W : CoalgObj}
            → Coalg⇒ Z W → Coalg⇒ Y Z → Coalg⇒ Y W
  compCoalg g f .map xᵢ x = map g xᵢ (map f xᵢ x)
  compCoalg g f .comm xᵢ x =
    ≈ˣ-trans (comm g xᵢ (map f xᵢ x)) (comm f xᵢ x)

  _≈Coalg_ : ∀ {Y Z : CoalgObj} → Coalg⇒ Y Z → Coalg⇒ Y Z → Set ℓeq
  _≈Coalg_ f g = ∀ xᵢ x → map f xᵢ x ≡ map g xᵢ x

  CoalgCatˣ : Category ℓo ℓh ℓeq
  CoalgCatˣ = record
    { Obj       = CoalgObj
    ; _⇒_       = Coalg⇒
    ; _≈_       = _≈Coalg_
    ; id        = λ {Y} → idCoalg Y
    ; _∘_       = λ {Y Z W} g f → compCoalg {Y = Y} {Z = Z} {W = W} g f
    ; assoc     = λ {_ _ _ _} {_ _ _} xᵢ x → refl
    ; sym-assoc = λ {_ _ _ _} {_ _ _} xᵢ x → refl
    ; identityˡ = λ {_ _} {f} xᵢ x → refl
    ; identityʳ = λ {_ _} {f} xᵢ x → refl
    ; identity² = λ {_} xᵢ x → refl
    ; equiv     = record
      { refl  = λ {_} xᵢ x → refl
      ; sym   = λ {_ _} e xᵢ x → sym (e xᵢ x)
      ; trans = λ {_ _ _} e₁ e₂ xᵢ x → trans (e₁ xᵢ x) (e₂ xᵢ x)
      }
    ; ∘-resp-≈  = λ {_ _ _} {f} {k} {g} {j} f≈ g≈ xᵢ x →
        trans (cong (map f xᵢ) (g≈ xᵢ x)) (f≈ xᵢ (map j xᵢ x))
    }

  -- The terminal coalgebra and its unique anamorphism, up to
  -- bisimulation.
  --
  -- 终余代数及其在互模拟意义下唯一的 anamorphism。
  terminal-coalgebra : CoalgObj
  terminal-coalgebra = mkCoalg Mˣ unfold-coalgebra

  ! : ∀ (Y : CoalgObj) → Coalg⇒ Y terminal-coalgebra
  ! Y .map xᵢ x = ana (γ Y) xᵢ x
  ! Y .comm xᵢ x = ana-unfold (ana (γ Y) xᵢ x)

  !-unique : ∀ (Y : CoalgObj)
               (f : Coalg⇒ Y terminal-coalgebra)
               (xᵢ : I) (x : Xst Y xᵢ)
           → ≈ˣ (map f xᵢ x) (ana (γ Y) xᵢ x)
  !-unique Y f xᵢ x =
    ≈ˣ-trans (ana-unfold˘ (map f xᵢ x)) (comm f xᵢ x)

  record IsTerminalUpToBisim : Set ℓo where
    field
      bang        : ∀ (Y : CoalgObj) → Coalg⇒ Y terminal-coalgebra
      bang-unique : ∀ (Y : CoalgObj) (f : Coalg⇒ Y terminal-coalgebra)
                      (xᵢ : I) (x : Xst Y xᵢ)
                  → ≈ˣ (map f xᵢ x) (ana (γ Y) xᵢ x)

  terminalUpToBisim : IsTerminalUpToBisim
  terminalUpToBisim = record
    { bang        = !
    ; bang-unique = !-unique
    }

  ----------------------------------------------------------------------
  -- Lambek's lemma up to bisimulation
  --
  -- The structure map is the observation coalgebra and its inverse is
  -- ana of it; the two round-trips are exactly the eta pair.
  --
  -- Lambek 引理（互模拟意义下）
  --
  -- 结构映射即观察余代数，其逆即对其取 ana；两条往返恰为上述 eta 对。

  lambek-in∘out : ∀ {xᵢ : I} (t : Mˣ xᵢ)
                → ≈ˣ (ana unfold-coalgebra xᵢ t) t
  lambek-in∘out = ana-unfold

  lambek-out∘in : ∀ {xᵢ : I} (t : Mˣ xᵢ)
                → ≈ˣ t (ana unfold-coalgebra xᵢ t)
  lambek-out∘in = ana-unfold˘
