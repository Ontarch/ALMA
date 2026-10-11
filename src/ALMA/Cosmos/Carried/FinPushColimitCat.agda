------------------------------------------------------------------------
-- The Fin push colimit packaged as a standard agda-categories Colimit
-- in DetCat
--
-- DetCat is the category of deterministic systems with forward
-- semiconjugacy maps. The shape ωCat is the free category on the
-- successor edges. Stage m is (Fin (n-at m), t m); the successor arrow
-- is inject₁ with embed-compat as semiconjugacy; the colimit apex is
-- (ℕ, s∞) with legs toℕ and read-coh as their semiconjugacy. A
-- competing cocone's legs are consistent across stages; the mediating
-- map sends v to the stage-v representative natToFin v, and its
-- semiconjugacy uses only s∞ v ≤ v+1 and iterated inject₁. Uniqueness
-- is pointwise at the representatives.
--
-- Fin push 余极限在确定性前向范畴 DetCat 中装配为 agda-categories
-- 标准 Colimit
--
-- DetCat 是带前向半共轭映射的确定性系统范畴。形状 ωCat 是后继边上的
-- 自由范畴。第 m 层为 (Fin (n-at m), t m)，后继箭头为 inject₁（其半
-- 共轭即 embed-compat）；余极限 apex 为 (ℕ, s∞)，腿为 toℕ，其半共轭
-- 即 read-coh。竞争余锥的腿跨阶段一致；mediate 把 v 送到第 v 层代表
-- natToFin v，其半共轭仅用 s∞ v ≤ v+1 与迭代 inject₁。唯一性在代表处
-- 逐点成立。
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module ALMA.Cosmos.Carried.FinPushColimitCat where

open import Agda.Primitive using (lzero; lsuc)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Nat.Base using (ℕ; zero; suc; _≤_; _<_; z≤n)
open import Data.Nat.Properties using
  (≤-pred; ≤-refl; m≤n⇒m≤1+n; m≤n⇒m<n∨m≡n; n≤0⇒n≡0)
open import Data.Fin.Base using (Fin; inject₁; toℕ)
open import Data.Fin.Properties using (toℕ-injective; toℕ-inject₁; toℕ<n)
open import Data.Sum.Base using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality.Core using (cong; cong₂; trans; sym)

open import Categories.Category.Core using (Category)
open import Categories.Functor using (Functor)

open import ALMA.Base.DetCat using (DetSys; DM; idDM; compDM; _≈DM_; DetCat)
open import ALMA.Cosmos.Carried.LimitSystemS using (n-at; natToFin; toℕ-natToFin)
import ALMA.Cosmos.Carried.LimitSystemS as LS

open DetSys using (I) renaming (step to step-det)
open DM

------------------------------------------------------------------------
-- Shape category
--
-- Paths over successor edges.
--
-- 形状范畴
--
-- 后继边上的路径。

data Chain⇒ (m : ℕ) : ℕ → Set where
  stop : Chain⇒ m m
  step : ∀ {n} → Chain⇒ m n → Chain⇒ m (suc n)

infixl 7 _∘ch_
_∘ch_ : ∀ {m y n} → Chain⇒ y n → Chain⇒ m y → Chain⇒ m n
stop    ∘ch f = f
step g  ∘ch f = step (g ∘ch f)

succ : ∀ {m} → Chain⇒ m (suc m)
succ = step stop

private
  idʳ-ch : ∀ {m y} (f : Chain⇒ m y) → f ∘ch stop ≡ f
  idʳ-ch stop     = refl
  idʳ-ch (step g) = cong step (idʳ-ch g)

  assoc-ch : ∀ {a b c d} (f : Chain⇒ a b) (g : Chain⇒ b c)
               (h : Chain⇒ c d)
           → (h ∘ch g) ∘ch f ≡ h ∘ch (g ∘ch f)
  assoc-ch f g stop     = refl
  assoc-ch f g (step h') = cong step (assoc-ch f g h')

ωCat : Category lzero lzero lzero
ωCat = record
  { Obj       = ℕ
  ; _⇒_       = Chain⇒
  ; _≈_       = λ {_ _} → _≡_
  ; id        = stop
  ; _∘_       = _∘ch_
  ; assoc     = λ {_ _ _ _ f g h} → assoc-ch f g h
  ; sym-assoc = λ {_ _ _ _ f g h} → sym (assoc-ch f g h)
  ; identityˡ = λ {_ _ f} → refl
  ; identityʳ = λ {_ _ f} → idʳ-ch f
  ; identity² = refl
  ; equiv     = record { refl = refl ; sym = sym ; trans = trans }
  ; ∘-resp-≈  = λ {_ _ _ f h g i} eqfh eqgi → cong₂ _∘ch_ eqfh eqgi
  }

------------------------------------------------------------------------
-- The Fin diagram and its colimit
--
-- Parameterised by t and embedding compatibility.
--
-- Fin 图及其余极限
--
-- 以 t 与嵌入相容性为参数。

module FinColimit
  (t : (m : ℕ) → Fin (n-at m) → Fin (n-at m))
  (embed-compat :
     (m : ℕ) (x : Fin (n-at m))
   → t (suc m) (inject₁ x) ≡ inject₁ (t m x))
  where

  open LS.LimitSystemS t embed-compat using (s∞; read-coh; cl; cl-toℕ)

  C : Category (lsuc lzero) lzero lzero
  C = DetCat lzero

  StageD : ℕ → DetSys lzero
  StageD m = record { I = Fin (n-at m) ; step = t m }

  Apex : DetSys lzero
  Apex = record { I = ℕ ; step = s∞ }

  -- Successor arrow: inject₁, with embed-compat as semiconjugacy.
  --
  -- 后继箭头：inject₁，embed-compat 即半共轭。
  emb : (m : ℕ) → DM (StageD m) (StageD (suc m))
  emb m = record { q = inject₁ ; coh = λ x → sym (embed-compat m x) }

  foldD : ∀ {m n} → Chain⇒ m n → DM (StageD m) (StageD n)
  foldD stop            = idDM _
  foldD (step {n = n} p) = compDM (emb n) (foldD p)

  foldD-hom : ∀ {m y n} (g : Chain⇒ y n) (f : Chain⇒ m y)
            → foldD (g ∘ch f) ≈DM compDM (foldD g) (foldD f)
  foldD-hom stop     f _ = refl
  foldD-hom (step {n = n} g) f x =
    cong (q (emb n)) (foldD-hom g f x)

  foldD-resp : ∀ {m n} {f g : Chain⇒ m n}
             → f ≡ g → foldD f ≈DM foldD g
  foldD-resp {f = f} {g = g} eq rewrite eq = λ _ → refl

  chainF : Functor ωCat C
  chainF = record
    { F₀          = StageD
    ; F₁          = foldD
    ; identity    = λ _ → refl
    ; homomorphism = λ {_ _ _ f g} → foldD-hom g f
    ; F-resp-≈    = λ {_ _ f g} eq → foldD-resp eq
    }

  -- Canonical legs: toℕ, with read-coh as semiconjugacy.
  --
  -- 规范腿：toℕ，read-coh 即半共轭。
  leg : (m : ℕ) → DM (StageD m) Apex
  leg m = record { q = toℕ ; coh = read-coh m }

  ----------------------------------------------------------------------
  -- A competing cocone
  --
  -- Legs ψ m into an apex Z, with successor coherence
  -- q (ψ (suc m)) (inject₁ x) ≡ q (ψ m) x.
  --
  -- 竞争余锥
  --
  -- 腿 ψ m 进入 apex Z，后继相干
  -- q (ψ (suc m)) (inject₁ x) ≡ q (ψ m) x。

  module WithCocone (Z : DetSys lzero)
    (ψ : (m : ℕ) → DM (StageD m) Z)
    (emb-eq : (m : ℕ) (x : Fin (n-at m))
            → q (ψ (suc m)) (inject₁ x) ≡ q (ψ m) x)
    where

    Q : (m : ℕ) → Fin (n-at m) → I Z
    Q m = q (ψ m)

    q∞ : ℕ → I Z
    q∞ v = Q v (natToFin v)

    private
      -- cl (suc v) k is inject₁ (cl v k) whenever k ≤ v; at k = suc v it
      -- is the stage-(suc v) representative.
      --
      -- k ≤ v 时 cl (suc v) k 即 inject₁ (cl v k)；k = suc v 时为第
      -- suc v 层代表。
      cl-suc : ∀ v k (le : k ≤ v) → cl (suc v) k ≡ inject₁ (cl v k)
      cl-suc v k le =
        toℕ-injective
          (trans (cl-toℕ (suc v) k (m≤n⇒m≤1+n (m≤n⇒m≤1+n le)))
            (sym (trans (toℕ-inject₁ (cl v k))
                        (cl-toℕ v k (m≤n⇒m≤1+n le)))))

      cl-top : ∀ v → cl (suc v) (suc v) ≡ natToFin (suc v)
      cl-top v =
        toℕ-injective
          (trans (cl-toℕ (suc v) (suc v) (m≤n⇒m≤1+n ≤-refl))
                 (sym (toℕ-natToFin (suc v))))

      -- Q at the clamped stage-v representative of k agrees with the
      -- stage-k representative, by iterated successor coherence.
      --
      -- 在 k 的第 v 层钳制代表处，Q 与第 k 层代表一致，由后继相干迭代。
      q-cl : ∀ v k (le : k ≤ v) → Q v (cl v k) ≡ q∞ k
      q-cl zero k le rewrite n≤0⇒n≡0 le =
        cong (Q zero)
          (toℕ-injective
            (trans (cl-toℕ zero zero z≤n) (sym (toℕ-natToFin zero))))
      q-cl (suc v) k le with m≤n⇒m<n∨m≡n le
      ... | inj₁ lt =
        trans (cong (Q (suc v)) (cl-suc v k (≤-pred lt)))
          (trans (emb-eq v (cl v k)) (q-cl v k (≤-pred lt)))
      ... | inj₂ eq rewrite eq =
        cong (Q (suc v)) (cl-top v)

      -- Q v x' ≡ q∞ k when x' at stage v reads as k ≤ v.
      --
      -- 当第 v 层的 x' 读数为 k ≤ v 时，Q v x' ≡ q∞ k。
      align-down : ∀ v k (le : k ≤ v) (x' : Fin (n-at v))
                 → toℕ x' ≡ k → Q v x' ≡ q∞ k
      align-down v k le x' eqx =
        let eqfin : x' ≡ cl v k
            eqfin = toℕ-injective
                      (trans eqx (sym (cl-toℕ v k (m≤n⇒m≤1+n le))))
        in trans (cong (Q v) eqfin) (q-cl v k le)

      -- q∞ (suc v) ≡ Q v x' when x' reads as suc v.
      --
      -- 当 x' 读数为 suc v 时，q∞ (suc v) ≡ Q v x'。
      align-up : ∀ v (x' : Fin (n-at v)) → toℕ x' ≡ suc v
               → q∞ (suc v) ≡ Q v x'
      align-up v x' eqk =
        let eqfin : natToFin (suc v) ≡ inject₁ x'
            eqfin = toℕ-injective
                      (trans (toℕ-natToFin (suc v))
                        (sym (trans (toℕ-inject₁ x') eqk)))
        in trans (cong (Q (suc v)) eqfin) (emb-eq v x')

      -- One step of the mediating semiconjugacy, indexed by the read
      -- value k rather than s∞ v so the case split abstracts only k.
      --
      -- mediate 半共轭的一步，按读数 k（而非 s∞ v）作索引，使分情况
      -- 只抽象 k。
      coh-case : ∀ v k (ek : toℕ (t v (natToFin v)) ≡ k)
                   (lek : k ≤ suc v)
               → q∞ k ≡ step-det Z (q∞ v)
      coh-case v k ek lek with m≤n⇒m<n∨m≡n lek
      ... | inj₁ lt =
        trans (sym (align-down v k (≤-pred lt) (t v (natToFin v)) ek))
              (coh (ψ v) (natToFin v))
      ... | inj₂ eqk rewrite eqk =
        trans (align-up v (t v (natToFin v)) ek)
              (coh (ψ v) (natToFin v))

      -- Triangle at stage m, indexed by the read value k ≤ m+1.
      --
      -- 第 m 层三角，按读数 k ≤ m+1 作索引。
      tri-case : ∀ m (x : Fin (n-at m)) k (ek : toℕ x ≡ k)
                   (lek : k ≤ suc m)
               → q∞ k ≡ Q m x
      tri-case m x k ek lek with m≤n⇒m<n∨m≡n lek
      ... | inj₁ lt = sym (align-down m k (≤-pred lt) x ek)
      ... | inj₂ eqk rewrite eqk = align-up m x ek

    -- Semiconjugacy of the mediating map.
    --
    -- mediate 映射的半共轭。
    q∞-coh : (v : ℕ) → q∞ (s∞ v) ≡ step-det Z (q∞ v)
    q∞-coh v = coh-case v (s∞ v) refl (≤-pred (toℕ<n (t v (natToFin v))))

    mediate : DM Apex Z
    mediate = record { q = q∞ ; coh = q∞-coh }

    -- Mediating triangle: mediate ∘ leg m ≈ ψ m, pointwise.
    --
    -- mediate 三角：mediate ∘ leg m ≈ ψ m，逐点成立。
    triangle : (m : ℕ) → compDM mediate (leg m) ≈DM ψ m
    triangle m x =
      tri-case m x (toℕ x) refl (≤-pred (toℕ<n x))

    -- Pointwise uniqueness against any map satisfying the triangles.
    --
    -- 对任何满足三角等式的映射逐点唯一。
    unique : (f : DM Apex Z)
           → ((m : ℕ) → compDM f (leg m) ≈DM ψ m)
           → ∀ v → q f v ≡ q∞ v
    unique f tri v =
      trans (cong (q f) (sym (toℕ-natToFin v)))
            (tri v (natToFin v))

  ----------------------------------------------------------------------
  -- Standard agda-categories packaging
  --
  -- 标准 agda-categories 装配

  -- Successor coherence of the canonical legs toℕ.
  --
  -- 规范腿 toℕ 的后继相干。
  private
    leg-emb-eq : (m : ℕ) (x : Fin (n-at m))
               → q (leg (suc m)) (inject₁ x) ≡ q (leg m) x
    leg-emb-eq m x = toℕ-inject₁ x

  -- Path coherence for any stage-consistent cocone.
  --
  -- 任意跨阶段相容余锥在路径上的相干。
  coh-path : (Z : DetSys lzero) (ψ : (m : ℕ) → DM (StageD m) Z)
             (emb-eq : (m : ℕ) (x : Fin (n-at m))
                     → q (ψ (suc m)) (inject₁ x) ≡ q (ψ m) x)
             {m n : ℕ} (p : Chain⇒ m n)
           → compDM (ψ n) (foldD p) ≈DM ψ m
  coh-path Z ψ emb-eq stop    _ = refl
  coh-path Z ψ emb-eq (step {n = n} p) x =
    trans (emb-eq n (q (foldD p) x)) (coh-path Z ψ emb-eq p x)

  open import Categories.Diagram.Cocone chainF
  open import Categories.Category.Construction.Cocones chainF using (Cocones)
  open import Categories.Object.Initial Cocones
  open import Categories.Diagram.Colimit chainF using (Colimit)

  mkCocone : Cocone
  mkCocone = record
    { coapex = record
      { ψ       = leg
      ; commute = λ {m n} p → coh-path Apex leg leg-emb-eq p
      }
    }

  -- A competing standard cocone gives exactly the data of WithCocone:
  -- its successor coherence is emb-eq.
  --
  -- 竞争的标准余锥恰好给出 WithCocone 所需数据：其后继相干即 emb-eq。
  private
    module Rep (K : Cocone) where
      embK : (m : ℕ) (x : Fin (n-at m))
           → q (Cocone.ψ K (suc m)) (inject₁ x) ≡ q (Cocone.ψ K m) x
      embK m x = Cocone.commute K (succ {m = m}) x
      open WithCocone (Cocone.N K) (Cocone.ψ K) embK public

  colimit : Colimit
  colimit = record
    { initial = record
      { ⊥ = mkCocone
      ; ⊥-is-initial = record
        { ! = λ {K} → record
          { arr     = Rep.mediate K
          ; commute = λ {m} → Rep.triangle K m
          }
        ; !-unique = λ {K} f v →
            sym (Rep.unique K (Cocone⇒.arr f)
                  (λ m → Cocone⇒.commute f {X = m}) v)
        }
      }
    }
