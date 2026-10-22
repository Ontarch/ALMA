------------------------------------------------------------------------
-- FinCat∞ projection: tower embedding, layer-0 projection, and its
-- faithfulness and conservativity
-- FinCat∞ 投影：塔嵌入、层 0 投影，及其忠实性与保守性
--
-- Along the tower family {FinCatN m} (m → ∞), provides the tower-family
-- embedding embedN and colimit injection projN at the functor level,
-- together with the cocone condition projN (suc m) ∘ embedN m ≅ projN m;
-- and the layer-0 projection projCosmos with its faithfulness (separation
-- is preserved) and conservativity (bisimulation is reflected), so that
-- the projection neither erases nor fabricates bisimulation information
-- between FinCatN and FinCat∞
-- 沿塔族 {FinCatN m}（m → ∞），提供函子层面的塔族嵌入 embedN 与余极限注入
-- projN，以及余锥条件 projN (suc m) ∘ embedN m ≅ projN m；
-- 并提供层 0 投影 projCosmos 及其忠实性（区分保持）与保守性（互模拟反映），
-- 使投影在 FinCatN 与 FinCat∞ 之间既不擦除也不捏造互模拟信息
--
-- Zero-subst carried style: the old partial finFromℕ-maybe / fromMaybe /
-- defaultFin (collapse to fzero out of range) machine and its two
-- proof-level subst are replaced by (1) a structurally recursive,
-- Cubical-safe strict dichotomy ≤-or-> (no Dec/Bool match), (2) the total
-- clamp representative cl from Carried.LimitSystem. extendFin reads f in
-- range and is the identity k out of range (the colimit-leg convention
-- needed by projCosmos-id); defaultFin is the total clamp. The Fin 3
-- swap witness is built directly at Fin n by rewrite m=1, deleting the
-- eight subst (λ n' → Fin n' → Fin n') casts.
-- 零 subst 携带式：旧的偏函数 finFromℕ-maybe / fromMaybe / defaultFin
-- （越界塌成 fzero）机器及其两处证明级 subst，替换为 (1) 结构化递归、
-- Cubical 安全的严格二分 ≤-or->（无 Dec/Bool 模式匹配），(2) 来自
-- Carried.LimitSystem 的全函数 clamp 代表 cl。extendFin 范围内读 f、
-- 范围外恒等于 k（projCosmos-id 所需的余极限腿约定）；defaultFin 为
-- 全函数 clamp。Fin 3 swap 见证经 rewrite m=1 直接在 Fin n 上构造，
-- 删除八处 subst (λ n' → Fin n' → Fin n') 搬移。
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module SecondPass.FinCatInfinityProjection where

open import Agda.Primitive using (_⊔_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Level using (lift)
open import Data.Unit.Polymorphic.Base using (⊤; tt)
open import Data.Nat using (ℕ; zero; suc; _∸_; _≤_; _<_; z≤n; s≤s; ≤-pred)
open import Data.Nat.Properties using (≤-trans; 1+n≢n; 1+n≰n)
open import Data.Fin.Base using (Fin; toℕ; inject₁) renaming (zero to fzero; suc to fsuc)
open import Data.Fin.Properties using (toℕ-inject₁; toℕ-injective; toℕ<n)
open import Data.Product.Base using (Σ; _,_; proj₁)
open import Data.Sum.Base using (inj₁; inj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality.Core using (cong; sym; trans; _≢_)
open import Relation.Binary.PropositionalEquality.Properties using (module ≡-Reasoning)
open ≡-Reasoning
open import Function.Base using (_∘_)

open import Categories.Functor.Core using (Functor)
open import Categories.NaturalTransformation.Core using (ntHelper)
open import Categories.NaturalTransformation.NaturalIsomorphism using (NaturalIsomorphism)

open import SecondPass.Cosmos using (Cosmos; out)
open import SecondPass.Unfolding using (Unfolding; module Unfolding)
open import SecondPass.Terminal using (_≈C_)
open _≈C_
open import SecondPass.FinCatNWitness
open import SecondPass.FinCatInfinity
open import Cosmos.Carried.LimitSystem using (cl; cl-toℕ; ≤-or->)

-- Tower-family embedding and colimit injection (functor level)
-- 塔族嵌入与余极限注入（函子层面）
module FinCatInfinityEmbedding (m : ℕ) where

  module M = FinCatN m
  module S = FinCatN (suc m)
  open M

  -- Tower-family embedding: F₀ = inject₁, F₁ = tt
  -- 塔族嵌入：F₀ = inject₁，F₁ = tt
  embedN : Functor M.FinCatN S.FinCatN
  embedN = record
    { F₀           = inject₁
    ; F₁           = λ _ → tt
    ; identity     = refl
    ; homomorphism = refl
    ; F-resp-≈     = λ _ → refl
    }

  -- Colimit injection ι_m : FinCatN m → FinCat∞, F₀ = toℕ
  -- 余极限注入 ι_m : FinCatN m → FinCat∞，F₀ = toℕ
  projN : Functor M.FinCatN FinCat∞
  projN = record
    { F₀           = toℕ
    ; F₁           = λ _ → tt
    ; identity     = refl
    ; homomorphism = refl
    ; F-resp-≈     = λ _ → refl
    }

  projN-suc : Functor S.FinCatN FinCat∞
  projN-suc = record
    { F₀           = toℕ
    ; F₁           = λ _ → tt
    ; identity     = refl
    ; homomorphism = refl
    ; F-resp-≈     = λ _ → refl
    }

  projN∘embedN : Functor M.FinCatN FinCat∞
  projN∘embedN = record
    { F₀           = λ x → toℕ (inject₁ x)
    ; F₁           = λ _ → tt
    ; identity     = refl
    ; homomorphism = refl
    ; F-resp-≈     = λ _ → refl
    }

  -- Cocone condition: toℕ ∘ inject₁ ≡ toℕ
  -- 余锥条件：toℕ ∘ inject₁ ≡ toℕ
  embedN-projN-F₀
    : ∀ (x : Fin M.n)
    → Functor.F₀ projN∘embedN x ≡ Functor.F₀ projN x
  embedN-projN-F₀ x =
    begin
      toℕ (inject₁ x) ≡⟨ toℕ-inject₁ x ⟩
      toℕ x           ∎

  -- projN (suc m) ∘ embedN m ≃ projN m
  embedN-projN-iso : NaturalIsomorphism projN∘embedN projN
  embedN-projN-iso = record
    { F⇒G = ntHelper record
        { η       = λ _ → tt
        ; commute = λ _ → refl
        }
    ; F⇐G = ntHelper record
        { η       = λ _ → tt
        ; commute = λ _ → refl
        }
    ; iso = λ _ → record { isoˡ = refl ; isoʳ = refl }
    }

module FinCatNColimitProjection (m : ℕ) where
  open FinCatN m

  -- extendFin: read f on the in-range representative cl m k; out of range
  -- (suc m < k) be the identity k, which is the colimit-leg convention so
  -- that projecting the identity cosmos agrees with the colimit identity.
  --
  -- extendFin：在范围内的代表 cl m k 上读 f；越界（suc m < k）恒等于 k，
  -- 这是余极限腿约定，使恒等宇宙的投影与余极限恒等一致。
  extendFin : (Fin n → Fin n) → ℕ → ℕ
  extendFin f k with ≤-or-> (suc m) k
  ... | inj₁ _  = toℕ (f (cl m k))
  ... | inj₂ _  = k

  -- defaultFin: total clamp representative (in range exact, out of range
  -- the top element). Replaces the partial fromMaybe-fzero decoder.
  --
  -- defaultFin：全函数 clamp 代表（范围内精确，越界取末位元素）。替代
  -- 偏函数 fromMaybe-fzero 解码器。
  defaultFin : ℕ → Fin n
  defaultFin k = cl m k

  extendFin-id : ∀ k → extendFin (λ x → x) k ≡ k
  extendFin-id k with ≤-or-> (suc m) k
  ... | inj₁ le = cl-toℕ m k le
  ... | inj₂ _  = refl

  -- The clamp representative at the natural reading of a layer element is
  -- that element itself.
  --
  -- 层元素按其自然读数所取的 clamp 代表即其自身。
  cl-self : ∀ (A : Fin n) → cl m (toℕ A) ≡ A
  cl-self A =
    toℕ-injective (cl-toℕ m (toℕ A) (≤-pred (toℕ<n A)))

  -- extendFin f (toℕ A) = toℕ (f A); the out-of-range branch is impossible
  -- because toℕ A ≤ suc m for every A : Fin n.
  --
  -- extendFin f (toℕ A) = toℕ (f A)；越界分支不可能，因对任意
  -- A : Fin n 都有 toℕ A ≤ suc m。
  extendFin-at-toℕ : ∀ (f : Fin n → Fin n) (A : Fin n)
    → extendFin f (toℕ A) ≡ toℕ (f A)
  extendFin-at-toℕ f A with ≤-or-> (suc m) (toℕ A)
  ... | inj₁ _ = cong (toℕ ∘ f) (cl-self A)
  ... | inj₂ gt =
    ⊥-elim (1+n≰n {n = suc m}
              (≤-trans gt (≤-pred (toℕ<n A))))

  -- defaultFin (toℕ A) = A
  -- defaultFin (toℕ A) = A
  defaultFin-toℕ-self : ∀ (A : Fin n) → defaultFin (toℕ A) ≡ A
  defaultFin-toℕ-self A = cl-self A

  -- cosmos-id∞: F₀ = proj₁ on FinCat∞
  -- cosmos-id∞：FinCat∞ 上 F₀ = proj₁ 的宇宙
  cosmos-id∞ : Cosmos FinCat∞ TrivialFC∞
  cosmos-id∞ .out = record
    { unfoldFunctor = record
      { F₀           = proj₁
      ; F₁           = λ _ → tt
      ; identity     = refl
      ; homomorphism = refl
      ; F-resp-≈     = λ _ → refl
      }
    ; unfold-next     = λ _ → cosmos-id∞
    ; pos-to-shape    = λ _ _ → lift tt
    ; pos-actS-compat = λ _ _ _ → refl
    }

  -- cosmos-mapN f: F₀ = f ∘ proj₁, constant unfold-next
  -- cosmos-mapN f：F₀ = f ∘ proj₁，unfold-next 常数
  cosmos-mapN : (Fin n → Fin n) → Cosmos FinCatN TrivialFCN
  cosmos-mapN f .out = record
    { unfoldFunctor = record
      { F₀           = λ { (A , _) → f A }
      ; F₁           = λ _ → tt
      ; identity     = refl
      ; homomorphism = refl
      ; F-resp-≈     = λ _ → refl
      }
    ; unfold-next     = λ _ → cosmos-mapN f
    ; pos-to-shape    = λ _ _ → lift tt
    ; pos-actS-compat = λ _ _ _ → refl
    }

  -- projCosmos: layer-0 projection, F₀ is extendFin of input F₀
  -- projCosmos：层 0 投影，F₀ 为输入 F₀ 的 extendFin
  projCosmos : Cosmos FinCatN TrivialFCN → Cosmos FinCat∞ TrivialFC∞
  projCosmos x .out = record
    { unfoldFunctor = record
      { F₀           = λ { (k , _) →
          extendFin (λ A → Functor.F₀ UX.unfoldFunctor (A , lift tt)) k }
      ; F₁           = λ _ → tt
      ; identity     = refl
      ; homomorphism = refl
      ; F-resp-≈     = λ _ → refl
      }
    ; unfold-next     = λ { {k} _ →
        projCosmos (UX.unfold-next {A = defaultFin k} (lift tt)) }
    ; pos-to-shape    = λ _ _ → lift tt
    ; pos-actS-compat = λ _ _ _ → refl
    }
    where
      UX = out x
      module UX = Unfolding UX

  projCosmos-F₀-spec
    : ∀ (x : Cosmos FinCatN TrivialFCN) (k : ℕ)
    → Functor.F₀ (Unfolding.unfoldFunctor (out (projCosmos x))) (k , lift tt)
      ≡ extendFin (λ A → Functor.F₀ (Unfolding.unfoldFunctor (out x)) (A , lift tt)) k
  projCosmos-F₀-spec x k = refl

  -- projCosmos cosmos-idN ≈C cosmos-id∞
  projCosmos-id : projCosmos cosmos-idN ≈C cosmos-id∞
  projCosmos-id .unfoldFunctor₀-eq {A} _ =
    begin
      extendFin (λ x → x) A ≡⟨ extendFin-id A ⟩
      A                     ∎
  projCosmos-id .pos-to-shape-eq _ _ = refl
  projCosmos-id .unfold-next-eq _    = projCosmos-id

  -- Faithfulness: extendFin separation yields non-bisimilarity
  -- 忠实性：extendFin 的分离蕴含不互模拟
  faithfulness
    : ∀ (f g : Fin n → Fin n)
    → Σ ℕ (λ k → extendFin f k ≢ extendFin g k)
    → ¬ (projCosmos (cosmos-mapN f) ≈C projCosmos (cosmos-mapN g))
  faithfulness f g (k , neq) eq =
    neq (begin
      extendFin f k
        ≡˘⟨ specF ⟩
      Ff
        ≡⟨ eqF ⟩
      Fg
        ≡⟨ specG ⟩
      extendFin g k
      ∎)
    where
      Ff = Functor.F₀ (Unfolding.unfoldFunctor (out (projCosmos (cosmos-mapN f))))
                     (k , lift tt)
      Fg = Functor.F₀ (Unfolding.unfoldFunctor (out (projCosmos (cosmos-mapN g))))
                     (k , lift tt)
      eqF   : Ff ≡ Fg
      eqF   = unfoldFunctor₀-eq eq {A = k} (lift tt)
      specF : Ff ≡ extendFin f k
      specF = projCosmos-F₀-spec (cosmos-mapN f) k
      specG : Fg ≡ extendFin g k
      specG = projCosmos-F₀-spec (cosmos-mapN g) k

  -- Conservativity: projCosmos reflects bisimulation
  -- 保守性：projCosmos 反映互模拟
  projCosmos-conservative
    : ∀ (x y : Cosmos FinCatN TrivialFCN)
    → projCosmos x ≈C projCosmos y → x ≈C y
  projCosmos-conservative x y eq .unfoldFunctor₀-eq {A = A} (lift tt) =
    toℕ-injective (begin
      toℕ (Functor.F₀ (Unfolding.unfoldFunctor (out x)) (A , lift tt))
        ≡˘⟨ extendFin-at-toℕ
              (λ A' → Functor.F₀ (Unfolding.unfoldFunctor (out x)) (A' , lift tt)) A ⟩
      extendFin (λ A' → Functor.F₀ (Unfolding.unfoldFunctor (out x)) (A' , lift tt)) (toℕ A)
        ≡˘⟨ projCosmos-F₀-spec x (toℕ A) ⟩
      Functor.F₀ (Unfolding.unfoldFunctor (out (projCosmos x))) (toℕ A , lift tt)
        ≡⟨ eq .unfoldFunctor₀-eq {A = toℕ A} (lift tt) ⟩
      Functor.F₀ (Unfolding.unfoldFunctor (out (projCosmos y))) (toℕ A , lift tt)
        ≡⟨ projCosmos-F₀-spec y (toℕ A) ⟩
      extendFin (λ A' → Functor.F₀ (Unfolding.unfoldFunctor (out y)) (A' , lift tt)) (toℕ A)
        ≡⟨ extendFin-at-toℕ
             (λ A' → Functor.F₀ (Unfolding.unfoldFunctor (out y)) (A' , lift tt)) A ⟩
      toℕ (Functor.F₀ (Unfolding.unfoldFunctor (out y)) (A , lift tt))
      ∎)
  projCosmos-conservative x y eq .pos-to-shape-eq _ _ = refl
  projCosmos-conservative x y eq .unfold-next-eq {A = k} s
    rewrite sym (defaultFin-toℕ-self k)
    = projCosmos-conservative
        (Unfolding.unfold-next (out x) {A = defaultFin (toℕ k)} (lift tt))
        (Unfolding.unfold-next (out y) {A = defaultFin (toℕ k)} (lift tt))
        (eq .unfold-next-eq {A = toℕ k} s)

  -- Concrete witness: swap01 vs swap12 on Fin 3 differ at k = 1.
  -- The swaps are built directly at Fin n (rewrite m=1 turns n into 3),
  -- so no subst (λ n' → Fin n' → Fin n') cast is needed.
  --
  -- 具体见证：Fin 3 上 swap01 与 swap12 在 k = 1 处不同。swap 直接在
  -- Fin n 上构造（rewrite m=1 把 n 化为 3），无需任何
  -- subst (λ n' → Fin n' → Fin n') 搬移。
  module _ (m=1 : m ≡ 1) where
    private
      swap01 : Fin n → Fin n
      swap01 x rewrite m=1 with toℕ x
      ... | zero        = fsuc fzero
      ... | suc zero    = fzero
      ... | suc (suc _) = fsuc (fsuc fzero)

      swap12 : Fin n → Fin n
      swap12 x rewrite m=1 with toℕ x
      ... | zero        = fzero
      ... | suc zero    = fsuc (fsuc fzero)
      ... | suc (suc _) = fsuc fzero

      -- Composition of the two swaps on Fin 3
      -- Fin 3 上两个对换的复合
      swap01∘swap12 : Fin n → Fin n
      swap01∘swap12 = swap01 ∘ swap12

      swap12∘swap01 : Fin n → Fin n
      swap12∘swap01 = swap12 ∘ swap01

    swap01≢swap12-at-1
      : extendFin swap01 1 ≢ extendFin swap12 1
    swap01≢swap12-at-1 rewrite m=1 = λ ()

    swap01∞≉swap12∞
      : ¬ (projCosmos (cosmos-mapN swap01)
           ≈C
           projCosmos (cosmos-mapN swap12))
    swap01∞≉swap12∞ =
      faithfulness _ _ (1 , swap01≢swap12-at-1)

    -- Non-commutativity separates at k = 0:
    --   extendFin (swap01 ∘ swap12) 0 = 1, extendFin (swap12 ∘ swap01) 0 = 2
    -- 非交换性在 k = 0 处分离：
    --   extendFin (swap01 ∘ swap12) 0 = 1，extendFin (swap12 ∘ swap01) 0 = 2
    swap01∘swap12≠swap12∘swap01-at-0
      : extendFin swap01∘swap12 0 ≢ extendFin swap12∘swap01 0
    swap01∘swap12≠swap12∘swap01-at-0 rewrite m=1 =
      λ eq → 1+n≢n {1} (sym eq)

    -- The projected cosmoi of the two composition orders are non-bisimilar
    -- 两种复合顺序的投影宇宙不互模拟
    swap01∘swap12∞≉swap12∘swap01∞
      : ¬ (projCosmos (cosmos-mapN swap01∘swap12)
           ≈C
           projCosmos (cosmos-mapN swap12∘swap01))
    swap01∘swap12∞≉swap12∘swap01∞ =
      faithfulness _ _ (0 , swap01∘swap12≠swap12∘swap01-at-0)
