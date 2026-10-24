------------------------------------------------------------------------
-- Lambek's lemma for the terminal coalgebra Cosmos
--
-- out : Cosmos → Unfolding Cosmos is a weak isomorphism:
--   in-F ∘ out is bisimilar to id, and out ∘ in-F is US._≈U_-equivalent to id
-- The inverse in-F is obtained from the universal property of the terminal
-- coalgebra. The key identities are:
--   in-F ∘ out ≈C id
--   out ∘ in-F ≈F id
--   out (in-F y) ≡ mapUnfolding (in-F ∘ out) y
--
-- Cosmos 终余代数的 Lambek 引理
--
-- out : Cosmos → Unfolding Cosmos 构成弱同构：
--   in-F ∘ out 与 id 互模拟，展开等价 US._≈U_
-- 逆映射 in-F 由终对象的泛性质构造。关键恒等式为：
--   in-F ∘ out ≈C id
--   out ∘ in-F ≈F id
--   out (in-F y) ≡ mapUnfolding (in-F ∘ out) y
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module SecondPass.Lambek where

open import Agda.Primitive using (Level; lsuc; _⊔_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Sigma using (_,_)
open import Relation.Binary.PropositionalEquality.Core using (cong; sym; trans)
open import Relation.Binary.PropositionalEquality.Properties using (module ≡-Reasoning)
import Relation.Binary.Reasoning.Setoid as SetoidReasoning
open import Relation.Binary.Bundles using (Setoid)
open import Function.Base using (_∘_; id)
open import Function.Bundles using (Func)

open import Categories.Category.Core using (Category)
open import Categories.Functor.Core using (Functor)

open import Equivalence using (module SubstTransport-Left)
open import Cosmos.ContCategory using (ContCat)
open import SecondPass.Unfolding using (Unfolding; mapUnfolding; mapUnfolding-∘; module UnfoldingSetoid)
open import SecondPass.Cosmos using (Cosmos; out)
open import SecondPass.Terminal
  using (Coalgebra; CoalgHom; cosmosCoalg; ana-hom; unique-ana; ana-to; _≈C_; ≈C-sym; cosmosSetoid)

module _ {o h e s p : Level}
         {C : Category o h e}
         {FC : Functor C (ContCat s p)} where
  private
    -- Overall level of objects and carriers.
    --
    -- 由于 Lambek 引理涉及 Unfolding 的载体类型，必须包含所有结构层级。
    L = o ⊔ h ⊔ e ⊔ s ⊔ p
    Lʳ = o ⊔ s ⊔ p

    -- Instantiate unfolding setoid module
    --
    -- 实例化展开集合模块
    module US = UnfoldingSetoid
      {o = o} {h = h} {e = e} {s = s} {p = p} {C = C} {F = FC}

    T  = Cosmos C FC
    FT : Set L
    FT = Unfolding FC T
    FFT : Set L
    FFT = Unfolding FC FT

    CS : Setoid L Lʳ
    CS = cosmosSetoid {o = o} {h = h} {e = e} {s = s} {p = p} {C = C} {FC = FC}

    CC : Coalgebra Lʳ
    CC = cosmosCoalg {o = o} {h = h} {e = e} {s = s} {p = p} {C = C} {FC = FC}

    -- out as a Setoid morphism
    --
    -- out 作为 Setoid 态射
    outF : Func CS (US.unfoldingSetoid CS)
    outF = Coalgebra.α CC

    -- FT-Setoid: FT under propositional equality.
    --
    -- 命题相等的关系层级与载体层级相同，故为 Setoid L L。
    FT-Setoid : Setoid L L
    FT-Setoid = record
      { Carrier       = FT
      ; _≈_           = _≡_ {A = FT}
      ; isEquivalence = record { refl = refl ; sym = sym ; trans = trans }
      }

    ≡→≈F-FT : ∀ {d₁ d₂ : FFT} → d₁ ≡ d₂ → US._≈U_ {X = FT-Setoid} d₁ d₂
    ≡→≈F-FT refl = US.≈U-refl {X = FT-Setoid}

    FT-α : Func FT-Setoid (US.unfoldingSetoid FT-Setoid)
    FT-α = record
      { to   = mapUnfolding out
      ; cong = λ {c₁} {c₂} c₁≡c₂ → ≡→≈F-FT (cong (mapUnfolding out) c₁≡c₂)
      }

  -- coalgebra (F T, F out)
  --
  -- 余代数 (F T, F out)
  FT-Coalg : Coalgebra L
  FT-Coalg = record { Carrier = FT-Setoid ; α = FT-α }

  -- in-F : FT-Coalg → CC by the universal property of the terminal object
  --
  -- in-F : FT-Coalg → CC（由终对象的泛性质构造）
  in-hom : CoalgHom {r₁ = L} {r₂ = Lʳ} FT-Coalg CC
  in-hom = ana-hom FT-Coalg

  in-F : FT → T
  in-F = Func.to (CoalgHom.f in-hom)

  -- in-F preserves ≈F (coinductive, same pattern as ana-cong).
  --
  -- in-F 保持 ≈F（余归纳，与 ana-cong 相同模式）。
  in-F-resp-≈F : ∀ {c₁ c₂} → US._≈U_ {X = CS} c₁ c₂ → in-F c₁ ≈C in-F c₂
  in-F-resp-≈F {c₁} {c₂} eq = helper eq
    where
      open _≈C_
      helper : ∀ {d₁ d₂} → US._≈U_ {X = CS} d₁ d₂ → in-F d₁ ≈C in-F d₂
      helper {d₁} {d₂} eq .unfoldFunctor₀-eq {A} s =
        SubstTransport-Left._≈sl_.shape-eq
          (US._≈U_.sl-eq eq) (A , s)
      helper {d₁} {d₂} eq .pos-to-shape-eq {A} s p =
        SubstTransport-Left._≈sl_.position-eq
          (US._≈U_.sl-eq eq) (A , s) p
      helper {d₁} {d₂} eq .unfold-next-eq {A} s =
        helper (Func.cong outF (US._≈U_.unfold-next-eq eq s))

  -- in-F ∘ out as a self-homomorphism of (T, out)
  --
  -- in-F ∘ out 作为 (T, out) 的自同态
  private
    in∘out-f : Func CS CS
    in∘out-f = record
      { to   = in-F ∘ out
      ; cong = λ {x} {y} x≈y → in-F-resp-≈F (Func.cong outF x≈y)
      }

    in∘out-hom : CoalgHom CC CC
    in∘out-hom = record { f = in∘out-f ; commute = commute-proof }
      where
        commute-proof : ∀ x → mapUnfolding (in-F ∘ out) (out x) ≡ out (in-F (out x))
        commute-proof x = let open ≡-Reasoning in begin
          mapUnfolding (in-F ∘ out) (out x)
            ≡⟨ mapUnfolding-∘ in-F out (out x) ⟩
          mapUnfolding in-F (mapUnfolding out (out x))
            ≡⟨ CoalgHom.commute in-hom (out x) ⟩
          out (in-F (out x))
          ∎

    idFunc : Func CS CS
    idFunc = record { to = id ; cong = λ x≈y → x≈y }

    id-hom : CoalgHom CC CC
    id-hom = record { f = idFunc ; commute = λ _ → refl }

  -- in-F ∘ out ≈C id_T
  --
  -- in-F ∘ out 与恒等互模拟
  in∘out≈id : ∀ x → in-F (out x) ≈C x
  in∘out≈id x =
    let open SetoidReasoning CS in begin
      in-F (out x)        ≈⟨ unique-ana CC in∘out-hom x ⟩
      ana-to CC x         ≈⟨ ≈C-sym (unique-ana CC id-hom x) ⟩
      x                   ∎

  -- out ∘ in-F ≡ F(in-F ∘ out)
  --
  -- out ∘ in-F 与 F(in-F ∘ out) 命题相等
  out∘in≡F∘ : ∀ y → out (in-F y) ≡ mapUnfolding (in-F ∘ out) y
  out∘in≡F∘ y = let open ≡-Reasoning in begin
    out (in-F y)
      ≡⟨ sym (CoalgHom.commute in-hom y) ⟩
    mapUnfolding in-F (mapUnfolding out y)
      ≡⟨ sym (mapUnfolding-∘ in-F out y) ⟩
    mapUnfolding (in-F ∘ out) y
    ∎

  -- F(in-F ∘ out) ≈F id_{F T}
  --
  -- F(in-F ∘ out) 与 F T 上的恒等 ≈F 等价
  private
    open Unfolding using (unfold-next)
    F∘≈Fid : ∀ y → US._≈U_ {X = CS} (mapUnfolding (in-F ∘ out) y) y
    F∘≈Fid y = record
      { sl-eq = record
          { shape-eq    = λ _ → refl
          ; position-eq = λ _ _ → refl
          }
      ; unfold-next-eq = λ {A} s →
          in∘out≈id (unfold-next y s)
      }

  -- out ∘ in-F ≈F id_{F T} (obtained by transferring along the previous equality)
  --
  -- out ∘ in-F 与 F T 上的恒等 ≈F 等价（由前一等式转换得到）
  out∘in≈Fid : ∀ y → US._≈U_ {X = CS} (out (in-F y)) y
  out∘in≈Fid y =
    let open SetoidReasoning (US.unfoldingSetoid CS) in begin
      out (in-F y)                  ≡⟨ out∘in≡F∘ y ⟩
      mapUnfolding (in-F ∘ out) y     ≈⟨ F∘≈Fid y ⟩
      y                             ∎

  -- out is a weak isomorphism (up to the respective equivalences)
  --   in-F ∘ out ≈C id_T
  --   out ∘ in-F ≈F id_{F T}
  --
  -- out 为弱同构（模各自等价关系）
  record LambekIso : Set (lsuc L) where
    field
      inverse      : FT → T
      inverse-left : ∀ x → inverse (out x) ≈C x
      inverse-right : ∀ y → US._≈U_ {X = CS} (out (inverse y)) y

  -- The canonical Lambek isomorphism obtained from the terminal coalgebra
  --
  -- 由终余代数得到的典范 Lambek 同构
  lambekIso : LambekIso
  lambekIso = record
    { inverse      = in-F
    ; inverse-left = in∘out≈id
    ; inverse-right = out∘in≈Fid
    }
