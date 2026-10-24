------------------------------------------------------------------------
-- Tower embedding compatibility
--
-- projCosmos (suc m) ∘ embedCosmos m ≈C projCosmos m:
-- embedCosmos m embeds a cosmos on FinCatN m into FinCatN (suc m):
--   F₀ = embedF f: on the inject₁ image apply f then inject₁, the new top
--   element is fixed; unfold-next follows the edge at the total clamp
--   representative cl m (toℕ A) of the source stage
-- The F₀ lemma extendFin-embedF₀ says extendFin′ (embedF f) ≡ extendFin f
-- (read f in range, identity beyond the horizon, new top fixed); the
-- unfold-next lemma cl-embed-default says the two clamp representatives
-- agree across stages. This is the colimit cocone compatibility at the
-- cosmos level.
--
-- 塔嵌入兼容性
--
-- 证明 projCosmos (suc m) ∘ embedCosmos m ≈C projCosmos m：
-- embedCosmos m 将层 m 宇宙嵌入层 suc m：
--   F₀ = embedF f：在 inject₁ 像上先应用 f 再注入，新末位元素固定；
--   unfold-next 在源层的全函数 clamp 代表 cl m (toℕ A) 处跟随边
-- F₀ 引理 extendFin-embedF₀ 表明 extendFin′ (embedF f) ≡ extendFin f
-- （范围内读 f、超出层界恒等、新末位固定）；unfold-next 引理
-- cl-embed-default 表明两个 clamp 代表跨层一致。这是余极限余锥在
-- 宇宙层面的相容性。
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module SecondPass.FinCatInfinityTowerCompat where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Level using (lift)
open import Data.Unit.Polymorphic.Base using (tt)
open import Data.Nat using (ℕ; zero; suc; _≤_; _<_; z≤n; s≤s; _⊓_)
open import Data.Nat.Properties
  using ( ≤-refl; ≤-trans; ≤-antisym; ≤-pred
        ; m≤n⇒m≤1+n; m≤n⇒m<n∨m≡n; m≥n⇒m⊓n≡n
        ; ⊓-assoc; ⊓-comm; 1+n≰n; n≮n )
open import Data.Fin.Base using (Fin; toℕ; inject₁)
open import Data.Fin.Properties using (toℕ-inject₁; toℕ-injective; toℕ<n)
open import Data.Sum.Base using (inj₁; inj₂)
open import Data.Product.Base using (_,_)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Binary.PropositionalEquality.Core using (cong; sym; trans)
open import Relation.Binary.PropositionalEquality.Properties using (module ≡-Reasoning)
open ≡-Reasoning
open import Function.Base using (_∘_)

open import Categories.Functor.Core using (Functor)

open import SecondPass.Cosmos using (Cosmos; out)
open import SecondPass.Unfolding using (Unfolding; module Unfolding)
open import SecondPass.Terminal using (_≈C_)
open _≈C_
open import SecondPass.FinCatNWitness
open import SecondPass.FinCatInfinity
open import SecondPass.FinCatInfinityProjection
open import Cosmos.Carried.LimitSystem
  using (n-at; cl; cl-toℕ; ≤-or->)
open import Cosmos.Carried.FinProj using (clamp-val)
open import Cosmos.Carried.FinColimit using (inj-cl)
open import Cosmos.Carried.FinEmbed
  using (embedF; embedF-newtop; toℕ-embedF-inject₁)

module FinCatTowerCompat (m : ℕ) where
  module M  = FinCatN m
  module S  = FinCatN (suc m)
  module PM = FinCatNColimitProjection m
  module PS = FinCatNColimitProjection (suc m)
  open M
  open S using () renaming (n to n′; FinCatN to FinCatN′; TrivialFCN to TrivialFCN′)
  open PM using ( extendFin; defaultFin; projCosmos; cosmos-mapN
                ; projCosmos-F₀-spec )
  open PS using () renaming ( extendFin to extendFin′; defaultFin to defaultFin′
                            ; projCosmos to projCosmos′; cosmos-mapN to cosmos-mapN′ )

  -- n′ = suc n definitionally (n-at (suc m) = suc (n-at m)).
  -- n′ = suc n（定义性，n-at (suc m) = suc (n-at m)）。

  -- One-step lift of a stage-m endofunction to stage suc m: on the inject₁
  -- image apply f then inject₁, the new top element is fixed.
  --
  -- 层 m 端函数到层 suc m 的一步提升：在 inject₁ 像上先 f 再注入，
  -- 新末位元素固定。
  embedF₀ : (Fin n → Fin n) → Fin n′ → Fin n′
  embedF₀ f = embedF {m = m} f

  -- embedF fixes the new top of stage suc m (the element of stage suc m
  -- whose natural reading is n-at m).
  --
  -- embedF 固定层 suc m 的新末位（自然读数为 n-at m 的元素）。
  embedF-fixes-top : ∀ (f : Fin n → Fin n)
    → embedF₀ f (cl (suc m) (n-at m)) ≡ cl (suc m) (n-at m)
  embedF-fixes-top f =
    embedF-newtop f (cl (suc m) (n-at m))
      (cl-toℕ (suc m) (n-at m) ≤-refl)

  -- Reading the fixed new top back gives n-at m.
  --
  -- 读回被固定的新末位得 n-at m。
  toℕ-embedF-top : ∀ (f : Fin n → Fin n)
    → toℕ (embedF₀ f (cl (suc m) (n-at m))) ≡ n-at m
  toℕ-embedF-top f
    rewrite embedF-fixes-top f = cl-toℕ (suc m) (n-at m) ≤-refl

  -- embedCosmos: embed a cosmos on FinCatN into FinCatN′. The unfold-next
  -- edge is followed at the total stage-m clamp representative of the
  -- stage-(suc m) shape (exact on the inject₁ image, the top dummy on the
  -- new element); this replaces the partial restrictFin decoder.
  --
  -- embedCosmos：将宇宙从 FinCatN 嵌入 FinCatN′。unfold-next 边在层
  -- (suc m) 形状所对应的全函数层 m clamp 代表处跟随（inject₁ 像上精确，
  -- 新元素上取末位哑元）；这替代了偏函数 restrictFin 解码器。
  embedCosmos : Cosmos FinCatN TrivialFCN → Cosmos FinCatN′ TrivialFCN′
  embedCosmos x .out = record
    { unfoldFunctor = record
      { F₀           = λ { (A , _) →
          embedF₀ (λ A₁ → Functor.F₀ UX.unfoldFunctor (A₁ , lift tt)) A }
      ; F₁           = λ _ → tt
      ; identity     = refl
      ; homomorphism = refl
      ; F-resp-≈     = λ _ → refl
      }
    ; unfold-next     = λ { {A} _ →
        embedCosmos (UX.unfold-next {A = cl m (toℕ A)} (lift tt)) }
    ; pos-to-shape    = λ _ _ → lift tt
    ; pos-actS-compat = λ _ _ _ → refl
    }
    where
      UX = out x
      module UX = Unfolding UX

  -- Main F₀ lemma: extendFin′ (embedF₀ f) k ≡ extendFin f k.
  -- Three regions: below the stage-m horizon (read f via inject₁), at the
  -- new top n-at m (fixed, both sides read n-at m), and beyond the
  -- stage-(suc m) horizon (both sides are the identity k).
  --
  -- F₀ 主引理：extendFin′ (embedF₀ f) k ≡ extendFin f k。分三个区域：
  -- 低于层 m 层界（经 inject₁ 读 f）、新末位 n-at m（固定，两侧均读
  -- n-at m）、超出层 (suc m) 层界（两侧均恒等于 k）。
  extendFin-embedF₀ : ∀ (f : Fin n → Fin n) (k : ℕ)
    → extendFin′ (embedF₀ f) k ≡ extendFin f k
  extendFin-embedF₀ f k
    with ≤-or-> (n-at m) k | ≤-or-> (suc m) k
  -- Below the stage-m horizon: read f through inject₁ on both sides.
  -- 低于层 m 层界：两侧均经 inject₁ 读 f。
  ... | inj₁ k≤n  | inj₁ k≤sm =
    begin
      toℕ (embedF₀ f (cl (suc m) k))
        ≡⟨ cong (λ z → toℕ (embedF₀ f z)) (inj-cl m k k≤sm) ⟩
      toℕ (embedF₀ f (inject₁ (cl m k)))
        ≡⟨ toℕ-embedF-inject₁ f (cl m k) ⟩
      toℕ (f (cl m k))
      ∎
  -- At the new top n-at m: embedF fixes it, both sides read n-at m = k.
  -- 新末位 n-at m：embedF 固定它，两侧均读 n-at m = k。
  ... | inj₁ k≤n  | inj₂ sm<k =
    let eq : k ≡ n-at m
        eq = ≤-antisym k≤n sm<k
    in begin
      toℕ (embedF₀ f (cl (suc m) k))
        ≡⟨ cong (λ z → toℕ (embedF₀ f (cl (suc m) z))) eq ⟩
      toℕ (embedF₀ f (cl (suc m) (n-at m)))
        ≡⟨ cong toℕ (embedF-fixes-top f) ⟩
      toℕ (cl (suc m) (n-at m))
        ≡⟨ cl-toℕ (suc m) (n-at m) ≤-refl ⟩
      n-at m
        ≡˘⟨ eq ⟩
      k
      ∎
  -- Beyond the stage-(suc m) horizon: both sides are the identity k.
  -- 超出层 (suc m) 层界：两侧均恒等于 k。
  ... | inj₂ _    | inj₂ _    = refl
  -- Beyond stage suc m but below stage m is impossible (horizons nest).
  -- 超出层 suc m 却低于层 m 不可能（层界嵌套）。
  ... | inj₂ n<k  | inj₁ k≤sm =
    ⊥-elim (1+n≰n {n = n-at m}
      (≤-trans n<k
        (≤-trans k≤sm (m≤n⇒m≤1+n (≤-refl {x = suc m})))))

  -- Cross-stage clamp idempotence, at the natural-number (minimum) level:
  --   cl m (toℕ (cl (suc m) k) = cl m k
  -- Reading at stage suc m then clamping back to stage m is clamping at
  -- stage m directly, because suc m ⊓ (suc (suc m) ⊓ k) = suc m ⊓ k.
  --
  -- 跨层 clamp 幂等，在自然数（最小值）层面：
  --   cl m (toℕ (cl (suc m) k) = cl m k
  -- 先在层 suc m 读数再钳回层 m，等于直接在层 m 钳制，因为
  -- suc m ⊓ (suc (suc m) ⊓ k) = suc m ⊓ k。
  cl-embed-default : ∀ (k : ℕ)
    → cl m (toℕ (cl (suc m) k)) ≡ cl m k
  cl-embed-default k =
    toℕ-injective (begin
      toℕ (cl m (toℕ (cl (suc m) k)))
        ≡⟨ clamp-val {k = suc m} (toℕ (cl (suc m) k)) ⟩
      suc m ⊓ toℕ (cl (suc m) k)
        ≡⟨ cong (suc m ⊓_) (clamp-val {k = suc (suc m)} k) ⟩
      suc m ⊓ (suc (suc m) ⊓ k)
        ≡˘⟨ ⊓-assoc (suc m) (suc (suc m)) k ⟩
      (suc m ⊓ suc (suc m)) ⊓ k
        ≡⟨ cong (_⊓ k)
              (trans (⊓-comm (suc m) (suc (suc m)))
                (m≥n⇒m⊓n≡n {m = suc (suc m)} {n = suc m}
                   (s≤s (m≤n⇒m≤1+n (≤-refl {x = m}))))) ⟩
      suc m ⊓ k
        ≡˘⟨ clamp-val {k = suc m} k ⟩
      toℕ (cl m k)
      ∎)

  -- Main theorem: projCosmos′ (embedCosmos x) ≈C projCosmos x.
  -- Defined by copattern matching so the recursive call is guarded by
  -- .unfold-next-eq (productivity).
  -- 主定理：projCosmos′ (embedCosmos x) ≈C projCosmos x。
  -- 通过 copattern 匹配定义，使递归调用受 .unfold-next-eq 保护（生产性）。
  projCosmos-embed-compat : ∀ (x : Cosmos FinCatN TrivialFCN)
    → projCosmos′ (embedCosmos x) ≈C projCosmos x
  projCosmos-embed-compat x .unfoldFunctor₀-eq {A = k} _ =
    begin
      Functor.F₀ (Unfolding.unfoldFunctor (out (projCosmos′ (embedCosmos x)))) (k , lift tt)
        ≡⟨ PS.projCosmos-F₀-spec (embedCosmos x) k ⟩
      extendFin′ (embedF₀ (λ A₁ → Functor.F₀ (Unfolding.unfoldFunctor (out x)) (A₁ , lift tt))) k
        ≡⟨ extendFin-embedF₀ (λ A₁ → Functor.F₀ (Unfolding.unfoldFunctor (out x)) (A₁ , lift tt)) k ⟩
      extendFin (λ A₁ → Functor.F₀ (Unfolding.unfoldFunctor (out x)) (A₁ , lift tt)) k
        ≡⟨ sym (projCosmos-F₀-spec x k) ⟩
      Functor.F₀ (Unfolding.unfoldFunctor (out (projCosmos x))) (k , lift tt)
    ∎
  projCosmos-embed-compat x .pos-to-shape-eq _ _ = refl
  projCosmos-embed-compat x .unfold-next-eq {A = k} _
    with cl m (toℕ (cl (suc m) k)) | cl-embed-default k
  ... | w | eq rewrite eq =
      projCosmos-embed-compat (UX.unfold-next {A = defaultFin k} (lift tt))
    where
      UX = out x
      module UX = Unfolding UX

  -- Corollary: for cosmos-mapN the compatibility is a direct instance.
  -- 推论：对 cosmos-mapN，相容性是直接实例。
  projCosmos-mapN-embed
    : ∀ (f : Fin n → Fin n)
    → projCosmos′ (embedCosmos (cosmos-mapN f)) ≈C projCosmos (cosmos-mapN f)
  projCosmos-mapN-embed f = projCosmos-embed-compat (cosmos-mapN f)
