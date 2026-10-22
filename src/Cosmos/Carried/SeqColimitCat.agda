------------------------------------------------------------------------
-- Sequential colimits in MCorrCatˢ as standard agda-categories Colimits
--
-- The shape is the free category on the successor edges of ℕ:
-- Chain⇒ m is indexed only by its target, with the source m fixed as a
-- parameter (mirroring reflexive-transitive closure). A path is grown by
-- appending at the target, so folding a chain's embeddings along it is
-- structural recursion with no arithmetic cast and no transport. The hom
-- equivalence is propositional equality; the category laws hold by
-- trivial induction. A supplied Colimitˢ (mediate/triangle/unique) makes
-- the colimit cocone initial, yielding a Categories.Diagram.Colimit.
-- Existence is conditional on Colimitˢ.
--
-- MCorrCatˢ 中的序列余极限，装配为 agda-categories 标准 Colimit
--
-- 形状是 ℕ 后继边上的自由范畴：Chain⇒ m 仅以目标为索引，源 m 固定为
-- 参数（镜像自反传递闭包）。路径在目标端追加生长，故沿路径折叠嵌入是
-- 结构化递归，无算术 cast、无传输。hom 等价取命题相等，范畴律由平凡
-- 归纳得到。给定 Colimitˢ（mediate/triangle/unique）即使命题余锥成为
-- 初始对象，从而得到标准 Colimit；存在性以 Colimitˢ 为条件。
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module Cosmos.Carried.SeqColimitCat where

open import Agda.Primitive using (Level; lzero)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Nat.Base using (ℕ; suc)
open import Relation.Binary.PropositionalEquality.Core using (sym; cong; trans)

open import Categories.Category.Core using (Category)
open import Categories.Functor using (Functor)

open import Base.MCorr.Setoid using (SysEq)
open import Base.MCorr.SetoidCat using
  (MCorrCatˢ; FMˢ; idFMˢ; compFMˢ; _≈FM_; ≈FM-refl; ≈FM-sym; ≈FM-trans
  ; ∘-resp-≈FM; sym-assocFM; identityˡFM; identityʳFM)
open import Cosmos.Carried.SeqColimitS using
  (Chainˢ; Coconeˢ; IsColimitˢ; Colimitˢ; X; emb; leg; coc; has; Apex)

------------------------------------------------------------------------
-- Shape category
--
-- Paths over successor edges; source is a parameter.
--
-- 形状范畴
--
-- 后继边上的路径；源端为参数。

data Chain⇒ (m : ℕ) : ℕ → Set where
  stop : Chain⇒ m m
  step : ∀ {n} → Chain⇒ m n → Chain⇒ m (suc n)

-- Composition prepends f to g; it recurses on the target-built g.
--
-- 复合把 f 接到 g 前，对目标端构造的 g 递归。
infixl 7 _∘ch_
_∘ch_ : ∀ {m y n} → Chain⇒ y n → Chain⇒ m y → Chain⇒ m n
stop    ∘ch f = f
step g  ∘ch f = step (g ∘ch f)

-- The one-step successor arrow.
--
-- 一步后继箭头。
succ : ∀ {m} → Chain⇒ m (suc m)
succ = step stop

ch-idˡ : ∀ {m y} (f : Chain⇒ m y) → stop ∘ch f ≡ f
ch-idˡ f = refl

ch-idʳ : ∀ {m y} (f : Chain⇒ m y) → f ∘ch stop ≡ f
ch-idʳ stop     = refl
ch-idʳ (step g) = cong step (ch-idʳ g)

ch-assoc : ∀ {m y z n} (h : Chain⇒ z n) (g : Chain⇒ y z) (f : Chain⇒ m y)
         → (h ∘ch g) ∘ch f ≡ h ∘ch (g ∘ch f)
ch-assoc stop     g f = refl
ch-assoc (step h) g f = cong step (ch-assoc h g f)

ch-resp : ∀ {m y n} {f h : Chain⇒ y n} {g i : Chain⇒ m y}
        → f ≡ h → g ≡ i → (f ∘ch g) ≡ (h ∘ch i)
ch-resp refl refl = refl

ωCat : Category lzero lzero lzero
ωCat = record
  { Obj       = ℕ
  ; _⇒_       = Chain⇒
  ; _≈_       = λ {_ _} → _≡_
  ; id        = stop
  ; _∘_       = _∘ch_
  ; assoc     = λ {_ _ _ _ f g h} → ch-assoc h g f
  ; sym-assoc = λ {_ _ _ _ f g h} → sym (ch-assoc h g f)
  ; identityˡ = λ {_ _ f} → ch-idˡ f
  ; identityʳ = λ {_ _ f} → ch-idʳ f
  ; identity² = refl
  ; equiv     = record { refl = refl ; sym = sym ; trans = trans }
  ; ∘-resp-≈  = λ {_ _ _ _} → ch-resp
  }

------------------------------------------------------------------------
-- Folding a path into iterated carried embeddings
--
-- 把路径折叠为迭代的携带嵌入

module _ {i a b ℓa ℓe : Level} (ch : Chainˢ i a b ℓa ℓe) where

  fold : {m n : ℕ} → Chain⇒ m n → FMˢ (X ch m) (X ch n)
  fold stop          = idFMˢ
  fold (step {n = n} p) = compFMˢ (emb ch n) (fold p)

  fold-id : {m : ℕ} → fold (stop {m = m}) ≈FM idFMˢ
  fold-id {m = m} = ≈FM-refl (fold stop)

  fold-hom : {m y n : ℕ} (g : Chain⇒ y n) (f : Chain⇒ m y)
           → fold (g ∘ch f) ≈FM compFMˢ (fold g) (fold f)
  fold-hom {m = m} {y = y} stop f =
    ≈FM-sym {i = i} {a = a} {b = b} {ℓa = ℓa} {ℓe = ℓe}
            {X = X ch m} {Y = X ch y}
            {f = compFMˢ idFMˢ (fold f)} {g = fold f}
      (identityˡFM {i = i} {a = a} {b = b} {ℓa = ℓa} {ℓe = ℓe}
                   {X = X ch m} {Y = X ch y} {f = fold f})
  fold-hom {m = m} {y = y} (step {n = t} g) f =
    ≈FM-trans {i = i} {a = a} {b = b} {ℓa = ℓa} {ℓe = ℓe}
              {X = X ch m} {Y = X ch (suc t)}
              {f = compFMˢ (emb ch t) (fold (g ∘ch f))}
              {g = compFMˢ (emb ch t) (compFMˢ (fold g) (fold f))}
              {h = compFMˢ (compFMˢ (emb ch t) (fold g)) (fold f)}
      (∘-resp-≈FM {i = i} {a = a} {b = b} {ℓa = ℓa} {ℓe = ℓe}
                  {X = X ch m} {Y = X ch t} {Z = X ch (suc t)}
                  {F₁ = fold (g ∘ch f)}
                  {F₂ = compFMˢ (fold g) (fold f)}
                  {G₁ = emb ch t} {G₂ = emb ch t}
                  (fold-hom g f) (≈FM-refl (emb ch t)))
      (sym-assocFM {i = i} {a = a} {b = b} {ℓa = ℓa} {ℓe = ℓe}
                   {W = X ch m} {X = X ch y} {Y = X ch t} {Z = X ch (suc t)}
                   {f = fold f} {g = fold g} {h = emb ch t})

  fold-resp : {m n : ℕ} {p q : Chain⇒ m n} → p ≡ q → fold p ≈FM fold q
  fold-resp {p = p} refl = ≈FM-refl (fold p)

  chainF : Functor ωCat (MCorrCatˢ i a b ℓa ℓe)
  chainF = record
    { F₀          = X ch
    ; F₁          = fold
    ; identity    = fold-id
    ; homomorphism = λ {m y n f g} → fold-hom g f
    ; F-resp-≈    = λ {m n p q} eq →
                     fold-resp {m = m} {n = n} {p = p} {q = q} eq
    }

  ----------------------------------------------------------------------
  -- One-step coherence lifts to arbitrary paths by induction
  --
  -- 一步相干性经归纳提升为任意路径上的相干性

  leg-coh-path : {L : SysEq i a b ℓa ℓe} (k : Coconeˢ ch L)
                 {m n : ℕ} (p : Chain⇒ m n)
               → compFMˢ (leg k n) (fold p) ≈FM leg k m
  leg-coh-path {L = L} k {m = m} stop =
    identityʳFM {i = i} {a = a} {b = b} {ℓa = ℓa} {ℓe = ℓe}
                {X = X ch m} {Y = L} {f = leg k m}
  leg-coh-path {L = L} k {m = m} (step {n = t} p) =
    ≈FM-trans {i = i} {a = a} {b = b} {ℓa = ℓa} {ℓe = ℓe}
              {X = X ch m} {Y = L}
              {f = compFMˢ (leg k (suc t))
                           (compFMˢ (emb ch t) (fold p))}
              {g = compFMˢ (leg k t) (fold p)}
              {h = leg k m}
      (≈FM-trans {i = i} {a = a} {b = b} {ℓa = ℓa} {ℓe = ℓe}
                 {X = X ch m} {Y = L}
                 {f = compFMˢ (leg k (suc t))
                              (compFMˢ (emb ch t) (fold p))}
                 {g = compFMˢ (compFMˢ (leg k (suc t)) (emb ch t))
                              (fold p)}
                 {h = compFMˢ (leg k t) (fold p)}
         (sym-assocFM {i = i} {a = a} {b = b} {ℓa = ℓa} {ℓe = ℓe}
                      {W = X ch m} {X = X ch t} {Y = X ch (suc t)} {Z = L}
                      {f = fold p} {g = emb ch t} {h = leg k (suc t)})
         (∘-resp-≈FM {i = i} {a = a} {b = b} {ℓa = ℓa} {ℓe = ℓe}
                     {X = X ch m} {Y = X ch t} {Z = L}
                     {F₁ = fold p} {F₂ = fold p}
                     {G₁ = compFMˢ (leg k (suc t)) (emb ch t)}
                     {G₂ = leg k t}
                     (≈FM-refl (fold p)) (Coconeˢ.coh k t)))
      (leg-coh-path {L = L} k p)

------------------------------------------------------------------------
-- A Colimitˢ makes the colimit cocone initial
--
-- Colimitˢ 使余极限余锥成为初始对象

module _ {i a b ℓa ℓe : Level} (ch : Chainˢ i a b ℓa ℓe) where

  private F = chainF ch

  open import Categories.Diagram.Cocone F
  open import Categories.Diagram.Colimit F using (Colimit)

  -- Fold of the successor arrow is the one-step embedding up to id.
  --
  -- 后继箭头的 fold 与一步嵌入仅差一个 id。
  succ-fold : ∀ {m} → fold ch (succ {m = m}) ≈FM emb ch m
  succ-fold {m = m} =
    identityʳFM {X = X ch m} {Y = X ch (suc m)} {f = emb ch m}

  mkCocone : ∀ {L : SysEq i a b ℓa ℓe} (k : Coconeˢ ch L) → Cocone
  mkCocone k = record
    { coapex = record { ψ = leg k ; commute = λ f → leg-coh-path ch k f } }

  fromCocone : (K : Cocone) → Coconeˢ ch (Cocone.N K)
  fromCocone K = record { leg = ψK ; coh = cohK }
    where
    ψK = Cocone.ψ K
    cohK : ∀ m → compFMˢ (ψK (suc m)) (emb ch m) ≈FM ψK m
    cohK m =
      ≈FM-trans {i = i} {a = a} {b = b} {ℓa = ℓa} {ℓe = ℓe}
                {X = X ch m} {Y = Cocone.N K}
                {f = compFMˢ (ψK (suc m)) (emb ch m)}
                {g = compFMˢ (ψK (suc m)) (fold ch (succ {m = m}))}
                {h = ψK m}
        (∘-resp-≈FM {i = i} {a = a} {b = b} {ℓa = ℓa} {ℓe = ℓe}
                    {X = X ch m} {Y = X ch (suc m)} {Z = Cocone.N K}
                    {F₁ = emb ch m} {F₂ = fold ch (succ {m = m})}
                    {G₁ = ψK (suc m)} {G₂ = ψK (suc m)}
                    (≈FM-sym {i = i} {a = a} {b = b} {ℓa = ℓa} {ℓe = ℓe}
                             {X = X ch m} {Y = X ch (suc m)}
                             {f = fold ch (succ {m = m})} {g = emb ch m}
                             (succ-fold {m = m}))
                    (≈FM-refl (ψK (suc m))))
        (Cocone.commute K (succ {m = m}))

  colimit : (cl : Colimitˢ i a b ℓa ℓe ch) → Colimit
  colimit cl = record
    { initial = record
      { ⊥ = mkCocone (coc cl)
      ; ⊥-is-initial = record
        { ! = λ {K} → record
          { arr     = IsColimitˢ.mediate (has cl) (fromCocone K)
          ; commute = λ {m} → IsColimitˢ.triangle (has cl) (fromCocone K) m
          }
        ; !-unique = λ {K} f →
            ≈FM-sym {i = i} {a = a} {b = b} {ℓa = ℓa} {ℓe = ℓe}
                    {X = Apex cl} {Y = Cocone.N K}
                    {f = Cocone⇒.arr f}
                    {g = IsColimitˢ.mediate (has cl) (fromCocone K)}
              (IsColimitˢ.unique (has cl) (Cocone⇒.arr f) (fromCocone K)
                 (λ m → Cocone⇒.commute f))
        }
      }
    }
