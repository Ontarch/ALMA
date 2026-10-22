------------------------------------------------------------------------
-- Permuted embedding: refuting the extended criterion C
-- 置换嵌入：反驳扩展后的判据 C
--
-- For every f : Fin n → Fin n with a left inverse, constructs a
-- tower-specific embedding permuted-embed f (layer-k F₀ maps z to
-- liftF k f (x.F₀ (proj₁ z))) and a liftAt applying invPow k f f⁻¹ to
-- cancel the accumulated f, packaged as PermutedPathWitness
-- When f has a non-fixed point, the embedding does not preserve F₀ at
-- layer 0, while liftAt 0 is the identity and hence injective — refuting
-- criterion C: feasibility does not imply preservation of input F₀
-- The witness is unconditional via swap01
-- 对每个带左逆的 f : Fin n → Fin n，构造塔特定嵌入 permuted-embed f
-- （第 k 层 F₀ 映 z 为 liftF k f (x.F₀ (proj₁ z))）与 liftAt
-- （施加 invPow k f f⁻¹ 抵消累积的 f），打包为 PermutedPathWitness
-- 当 f 有非不动点时，嵌入在层 0 不保持 F₀，而 liftAt 0 为恒等故单射——
-- 反驳判据 C：可行性不蕴含输入 F₀ 的保持
-- 见证经 swap01 无条件成立
-- 参数 m 编码 n = suc (suc m)，使 n ≥ 2 定义性成立
------------------------------------------------------------------------
{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module SecondPass.FinCatNPermutedEmbedding where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Level using (Lift; lift)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality.Core using (sym; cong; _≢_)
open import Relation.Binary.PropositionalEquality.Properties using (module ≡-Reasoning)
open ≡-Reasoning
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product.Base using (proj₁; proj₂; Σ; _,_)
open import Data.Fin.Base using (Fin; splitAt; join; opposite) renaming (zero to fzero)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Fin.Properties using (join-splitAt; splitAt-join; opposite-involutive)
open import Data.Unit.Polymorphic.Base using (tt)
open import Data.List.Base using (List; []; _∷_; length)
open import Function.Base using (_∘_; id)

open import Categories.Category.Core using (Category)
open import Categories.Functor.Core using (Functor)

open import Cosmos.ContCategoryLemmas using (ShapeOf)
open import Cosmos.ContCatEquiv using (ShapeCat)
open import SecondPass.Unfolding using (Unfolding)
open import SecondPass.Cosmos using (Cosmos; out)
open import SecondPass.Terminal using (_≈C_; ≈C-refl; ≈C-trans)
open import SecondPass.CumulativeHierarchy using (EmbeddingData; UniformEmbeddingFamily)
open import SecondPass.StrictLift using (StrictLayer)
open import SecondPass.CumulativeHierarchyLimit using (Tower)
open import SecondPass.FinCatNWitness
open import SecondPass.FinCatNTowerLemmas
open import SecondPass.FinCatNDefaultUnif

module FinCatNPermutedEmbedding (m : ℕ) where

  open FinCatN m
  open FinCatNTowerLemmas m
  open FinCatNDefaultUnif m using (default-unif)

  -- invPow k f f⁻¹ applies f⁻¹ k times; the key property is
  -- invPow (suc k) f f⁻¹ (f a) ≡ invPow k f f⁻¹ a when f⁻¹ (f a) ≡ a
  -- invPow k f f⁻¹ 将 f⁻¹ 施加 k 次；关键性质：
  -- 当 f⁻¹ (f a) ≡ a 时，invPow (suc k) f f⁻¹ (f a) ≡ invPow k f f⁻¹ a
  invPow : (k : ℕ) (f f⁻¹ : Fin n → Fin n) → Fin n → Fin n
  invPow zero    f f⁻¹ a = a
  invPow (suc k) f f⁻¹ a = invPow k f f⁻¹ (f⁻¹ a)

  -- Shape types are constant in the object
  -- 形状类型关于对象是常值
  ShapeOf-const : ∀ k (X Y : Category.Obj (StrictLayer.C (Tower.layer nTower k)))
                → ShapeOf (StrictLayer.FC (Tower.layer nTower k)) X
                ≡ ShapeOf (StrictLayer.FC (Tower.layer nTower k)) Y
  ShapeOf-const zero    X Y = refl
  ShapeOf-const (suc k) (X , _) (Y , _) =
    cong (λ T → Lift _ T) (ShapeOf-const k X Y)

  -- Canonical shape at every layer, independent of the input object
  -- 每层的典范形状，与输入对象无关
  canonicalShape : ∀ k (A : Category.Obj (StrictLayer.C (Tower.layer nTower k)))
                → ShapeOf (StrictLayer.FC (Tower.layer nTower k)) A
  canonicalShape zero    A       = lift tt
  canonicalShape (suc k) (A , _) = lift (canonicalShape k A)

  -- liftF k f acts on the outermost Fin n component and resets the shape
  -- to canonicalShape (the unique choice at every layer)
  -- liftF k f 作用最外层 Fin n 分量，并将形状重置为 canonicalShape
  -- （每层的唯一选择）
  liftF : ∀ k → (f : Fin n → Fin n)
        → Category.Obj (StrictLayer.C (Tower.layer nTower k))
        → Category.Obj (StrictLayer.C (Tower.layer nTower k))
  liftF zero    f A       = f A
  liftF (suc k) f (A , _) = (liftF k f A , canonicalShape k (liftF k f A))

  -- F₁ for liftF: identity, because FinCatN hom-sets are ⊤
  -- liftF 的 F₁：恒等，因 FinCatN 的 hom 集为 ⊤
  liftF-F₁ : ∀ k f {A B}
            (g : Category._⇒_ (StrictLayer.C (Tower.layer nTower k)) A B)
          → Category._⇒_ (StrictLayer.C (Tower.layer nTower k))
                      (liftF k f A) (liftF k f B)
  liftF-F₁ zero    f g       = g
  liftF-F₁ (suc k) f (g , _) =
    ( liftF-F₁ k f g
    , shape-singleton-at k _ _ _ )

  -- proj-obj k commutes with liftF
  -- proj-obj k 与 liftF 交换
  proj-obj-liftF
    : ∀ k (f : Fin n → Fin n)
      (A : Category.Obj (StrictLayer.C (Tower.layer nTower k)))
    → proj-obj k (liftF k f A) ≡ f (proj-obj k A)
  proj-obj-liftF zero    f A       = refl
  proj-obj-liftF (suc k) f (A , s) = proj-obj-liftF k f A

  -- permuted-F₀ k f x z = (liftF k f (x.F₀ (proj₁ z)), canonicalShape k _)
  permuted-F₀
    : ∀ k (f : Fin n → Fin n)
      (x : Cosmos (StrictLayer.C (Tower.layer nTower k))
                  (StrictLayer.FC (Tower.layer nTower k)))
    → Category.Obj (ShapeCat
        (StrictLayer.C (Tower.layer nTower (suc k)))
        (StrictLayer.FC (Tower.layer nTower (suc k))))
    → Category.Obj (StrictLayer.C (Tower.layer nTower (suc k)))
  permuted-F₀ k f x z =
    ( liftF k f (Unfolding.unfoldFunctor (out x) .Functor.F₀ (proj₁ z))
    , canonicalShape k
        (liftF k f (Unfolding.unfoldFunctor (out x) .Functor.F₀ (proj₁ z))) )

  -- permuted-F₁: liftF-F₁ on the first component; shape equation by
  -- shape-singleton-at
  -- permuted-F₁：第一分量用 liftF-F₁；形状等式由 shape-singleton-at 消解
  permuted-F₁
    : ∀ k (f : Fin n → Fin n)
      (x : Cosmos (StrictLayer.C (Tower.layer nTower k))
                  (StrictLayer.FC (Tower.layer nTower k)))
    → {u v : Category.Obj (ShapeCat
        (StrictLayer.C (Tower.layer nTower (suc k)))
        (StrictLayer.FC (Tower.layer nTower (suc k))))}
    → Category._⇒_ (ShapeCat
        (StrictLayer.C (Tower.layer nTower (suc k)))
        (StrictLayer.FC (Tower.layer nTower (suc k)))) u v
    → Category._⇒_ (StrictLayer.C (Tower.layer nTower (suc k)))
        (permuted-F₀ k f x u) (permuted-F₀ k f x v)
  permuted-F₁ k f x {u} {v} fmap =
    ( liftF-F₁ k f (Unfolding.unfoldFunctor (out x) .Functor.F₁ (proj₁ fmap))
    , shape-singleton-at k _ _ _ )

  -- permuted-embed: same structure as dep-embed, but F₀/F₁ are permuted
  -- Functor laws discharged by nTower-collapsible; pos-to-shape reads
  -- canonicalShape; pos-actS-compat by shape-singleton-at
  -- permuted-embed：与 dep-embed 结构相同，但 F₀/F₁ 被置换
  -- 函子律由 nTower-collapsible 消解；pos-to-shape 读 canonicalShape；
  -- pos-actS-compat 由 shape-singleton-at 消解
  permuted-embed
    : ∀ k (f : Fin n → Fin n)
      (x : Cosmos (StrictLayer.C (Tower.layer nTower k))
                  (StrictLayer.FC (Tower.layer nTower k)))
    → EmbeddingData x
    → Cosmos (StrictLayer.C (Tower.layer nTower (suc k)))
             (StrictLayer.FC (Tower.layer nTower (suc k)))
  permuted-embed k f x ed .out =
    let
      C'  = StrictLayer.C (Tower.layer nTower (suc k))
      FC' = StrictLayer.FC (Tower.layer nTower (suc k))
      SC' = ShapeCat C' FC'
      id-SC' = Category.id SC'
      id-C'  = Category.id C'
      pf₁ = permuted-F₁ k f x
    in record
    { unfoldFunctor = record
        { F₀           = permuted-F₀ k f x
        ; F₁           = pf₁
        ; identity = λ {X} →
            nTower-collapsible (suc k)
              (permuted-F₁ k f x (Category.id SC' {A = X}))
              (Category.id C' {A = permuted-F₀ k f x X})
        ; homomorphism = λ {X Y Z f₁ g₁} →
            nTower-collapsible (suc k)
              (pf₁ (Category._∘_ SC' g₁ f₁))
              (Category._∘_ C' (pf₁ g₁) (pf₁ f₁))
        ; F-resp-≈     = λ {X Y f₁ g₁} _ →
            nTower-collapsible (suc k) (pf₁ f₁) (pf₁ g₁)
        }
    ; unfold-next = λ { {A} s →
        permuted-embed k f
          (Unfolding.unfold-next (out x) {A = proj₁ A} (proj₂ A))
          (EmbeddingData.next ed {A = proj₁ A} (proj₂ A)) }
    ; pos-to-shape = λ { {A} s _ →
        canonicalShape (suc k) (permuted-F₀ k f x (A , s)) }
    ; pos-actS-compat = λ { {A} {B} {s} {t} g eq p →
        shape-singleton-at (suc k)
          (permuted-F₀ k f x (B , t)) _ _ }
    }

  -- permuted-liftAt 0 = id; at layer suc k, reads the outermost Fin n
  -- component of x.F₀ at the canonical embed-pair and applies
  -- invPow (suc k) f f⁻¹
  -- permuted-liftAt 0 = id；第 suc k 层读取 x.F₀ 在典范 embed-pair 处的
  -- 最外层 Fin n 分量，并施加 invPow (suc k) f f⁻¹
  permuted-liftAt
    : ∀ (f f⁻¹ : Fin n → Fin n) (f⁻¹∘f : ∀ a → f⁻¹ (f a) ≡ a)
    → ∀ k
    → Cosmos (StrictLayer.C (Tower.layer nTower k))
             (StrictLayer.FC (Tower.layer nTower k))
    → Cosmos FinCatN TrivialFCN
  permuted-liftAt f f⁻¹ f⁻¹∘f zero    x = x
  permuted-liftAt f f⁻¹ f⁻¹∘f (suc k) x .out = record
    { unfoldFunctor = record
        { F₀ = λ { (A , _) →
            invPow (suc k) f f⁻¹
              (proj-obj (suc k)
                (Unfolding.unfoldFunctor (out x) .Functor.F₀
                  (embed-obj (suc k) A ,
                   embed-shape (suc k) (embed-obj (suc k) A)))) }
        ; F₁ = λ _ → tt
        ; identity = refl ; homomorphism = refl ; F-resp-≈ = λ _ → refl
        }
    ; unfold-next = λ { {A = A} _ →
        permuted-liftAt f f⁻¹ f⁻¹∘f (suc k)
          (Unfolding.unfold-next (out x)
            {A = embed-obj (suc k) A}
            (embed-shape (suc k) (embed-obj (suc k) A))) }
    ; pos-to-shape    = λ _ _ → lift tt
    ; pos-actS-compat = λ _ _ _ → refl
    }

  -- proj-obj (suc k) ∘ permuted-F₀ k f x = f ∘ proj-obj k ∘ x.F₀ ∘ proj₁
  proj-obj-permuted-F₀
    : ∀ k (f : Fin n → Fin n)
      (x : Cosmos (StrictLayer.C (Tower.layer nTower k))
                  (StrictLayer.FC (Tower.layer nTower k)))
      (z : Category.Obj (ShapeCat
              (StrictLayer.C (Tower.layer nTower (suc k)))
              (StrictLayer.FC (Tower.layer nTower (suc k)))))
    → proj-obj (suc k) (permuted-F₀ k f x z)
      ≡ f (proj-obj k (Unfolding.unfoldFunctor (out x) .Functor.F₀ (proj₁ z)))
  proj-obj-permuted-F₀ k f x z =
    proj-obj-liftF k f
      (Unfolding.unfoldFunctor (out x) .Functor.F₀ (proj₁ z))

  -- permuted-liftAt-step: the F₀ component cancels via invPow's definition
  -- and f⁻¹∘f = id
  -- permuted-liftAt-step：F₀ 分量经 invPow 定义与 f⁻¹∘f = id 抵消
  permuted-liftAt-step
    : ∀ (f f⁻¹ : Fin n → Fin n) (f⁻¹∘f : ∀ a → f⁻¹ (f a) ≡ a)
    → ∀ k
      (x : Cosmos (StrictLayer.C (Tower.layer nTower k))
                  (StrictLayer.FC (Tower.layer nTower k)))
      (ed : EmbeddingData x)
    → permuted-liftAt f f⁻¹ f⁻¹∘f (suc k) (permuted-embed k f x ed)
      ≈C permuted-liftAt f f⁻¹ f⁻¹∘f k x
  permuted-liftAt-step f f⁻¹ f⁻¹∘f zero x ed
    ._≈C_.unfoldFunctor₀-eq {A} s =
    let z = embed-obj 1 A , embed-shape 1 (embed-obj 1 A)
    in begin
      invPow 1 f f⁻¹ (proj-obj 1
        (Unfolding.unfoldFunctor (out (permuted-embed zero f x ed))
          .Functor.F₀ z))
        ≡⟨ refl ⟩
      invPow 1 f f⁻¹ (proj-obj 1 (permuted-F₀ zero f x z))
        ≡⟨ cong (invPow 1 f f⁻¹) (proj-obj-permuted-F₀ zero f x z) ⟩
      invPow 1 f f⁻¹ (f (proj-obj zero
        (Unfolding.unfoldFunctor (out x) .Functor.F₀ (proj₁ z))))
        ≡⟨ refl ⟩
      invPow 0 f f⁻¹ (f⁻¹ (f (proj-obj zero
        (Unfolding.unfoldFunctor (out x) .Functor.F₀ (proj₁ z)))))
        ≡⟨ cong (invPow 0 f f⁻¹) (f⁻¹∘f (proj-obj zero
             (Unfolding.unfoldFunctor (out x) .Functor.F₀ (proj₁ z)))) ⟩
      invPow 0 f f⁻¹ (proj-obj zero
        (Unfolding.unfoldFunctor (out x) .Functor.F₀ (proj₁ z)))
        ∎
  permuted-liftAt-step f f⁻¹ f⁻¹∘f zero x ed ._≈C_.pos-to-shape-eq s p = refl
  permuted-liftAt-step f f⁻¹ f⁻¹∘f zero x ed ._≈C_.unfold-next-eq {A} s =
    permuted-liftAt-step f f⁻¹ f⁻¹∘f zero
      (Unfolding.unfold-next (out x) {A = A} s)
      (EmbeddingData.next ed {A = A} s)
  permuted-liftAt-step f f⁻¹ f⁻¹∘f (suc m) x ed
    ._≈C_.unfoldFunctor₀-eq {A} s =
    let z = embed-obj (suc (suc m)) A ,
              embed-shape (suc (suc m)) (embed-obj (suc (suc m)) A)
    in begin
      invPow (suc (suc m)) f f⁻¹ (proj-obj (suc (suc m))
        (Unfolding.unfoldFunctor (out (permuted-embed (suc m) f x ed))
          .Functor.F₀ z))
        ≡⟨ refl ⟩
      invPow (suc (suc m)) f f⁻¹ (proj-obj (suc (suc m))
        (permuted-F₀ (suc m) f x z))
        ≡⟨ cong (invPow (suc (suc m)) f f⁻¹)
             (proj-obj-permuted-F₀ (suc m) f x z) ⟩
      invPow (suc (suc m)) f f⁻¹ (f (proj-obj (suc m)
        (Unfolding.unfoldFunctor (out x) .Functor.F₀ (proj₁ z))))
        ≡⟨ refl ⟩
      invPow (suc m) f f⁻¹ (f⁻¹ (f (proj-obj (suc m)
        (Unfolding.unfoldFunctor (out x) .Functor.F₀ (proj₁ z)))))
        ≡⟨ cong (invPow (suc m) f f⁻¹) (f⁻¹∘f (proj-obj (suc m)
             (Unfolding.unfoldFunctor (out x) .Functor.F₀ (proj₁ z)))) ⟩
      invPow (suc m) f f⁻¹ (proj-obj (suc m)
        (Unfolding.unfoldFunctor (out x) .Functor.F₀ (proj₁ z)))
        ∎
  permuted-liftAt-step f f⁻¹ f⁻¹∘f (suc m) x ed
    ._≈C_.pos-to-shape-eq s p = refl
  permuted-liftAt-step f f⁻¹ f⁻¹∘f (suc m) x ed
    ._≈C_.unfold-next-eq {A} s =
    permuted-liftAt-step f f⁻¹ f⁻¹∘f (suc m)
      (Unfolding.unfold-next (out x)
        {A = embed-obj (suc m) A}
        (embed-shape (suc m) (embed-obj (suc m) A)))
      (EmbeddingData.next ed
        {A = embed-obj (suc m) A}
        (embed-shape (suc m) (embed-obj (suc m) A)))

  -- permuted-liftAt preserves _≈C_
  -- permuted-liftAt 保持 _≈C_
  permuted-liftAt-resp
    : ∀ (f f⁻¹ : Fin n → Fin n) (f⁻¹∘f : ∀ a → f⁻¹ (f a) ≡ a)
    → ∀ k {x y : Cosmos (StrictLayer.C (Tower.layer nTower k))
                       (StrictLayer.FC (Tower.layer nTower k))}
    → _≈C_ {C = StrictLayer.C (Tower.layer nTower k)}
           {FC = StrictLayer.FC (Tower.layer nTower k)} x y
    → _≈C_ {C = FinCatN} {FC = TrivialFCN}
           (permuted-liftAt f f⁻¹ f⁻¹∘f k x)
           (permuted-liftAt f f⁻¹ f⁻¹∘f k y)
  permuted-liftAt-resp f f⁻¹ f⁻¹∘f zero    eq = eq
  permuted-liftAt-resp f f⁻¹ f⁻¹∘f (suc k) {x} {y} eq
    ._≈C_.unfoldFunctor₀-eq {A} s =
      let a  = embed-obj (suc k) A
          sh = embed-shape (suc k) a
      in cong (λ b → invPow (suc k) f f⁻¹ (proj-obj (suc k) b))
           (eq ._≈C_.unfoldFunctor₀-eq {A = a} sh)
  permuted-liftAt-resp f f⁻¹ f⁻¹∘f (suc k) eq
    ._≈C_.pos-to-shape-eq s p = refl
  permuted-liftAt-resp f f⁻¹ f⁻¹∘f (suc k) {x} {y} eq
    ._≈C_.unfold-next-eq {A} s =
      permuted-liftAt-resp f f⁻¹ f⁻¹∘f (suc k)
        (eq ._≈C_.unfold-next-eq
              {A = embed-obj (suc k) A}
              (embed-shape (suc k) (embed-obj (suc k) A)))

  -- PreservesF₀At k embed: embed preserves F₀'s first component at layer k
  -- PreservesF₀At k embed：embed 在层 k 保持 F₀ 第一分量
  PreservesF₀At
    : (k : ℕ)
    → (embed : ∀ k
               → (x : Cosmos (StrictLayer.C (Tower.layer nTower k))
                           (StrictLayer.FC (Tower.layer nTower k)))
               → EmbeddingData x
               → Cosmos (StrictLayer.C (Tower.layer nTower (suc k)))
                        (StrictLayer.FC (Tower.layer nTower (suc k))))
    → Set _
  PreservesF₀At k embed =
    ∀ (x : Cosmos (StrictLayer.C (Tower.layer nTower k))
                  (StrictLayer.FC (Tower.layer nTower k)))
      (ed : EmbeddingData x)
      (z : Category.Obj (ShapeCat
            (StrictLayer.C (Tower.layer nTower (suc k)))
            (StrictLayer.FC (Tower.layer nTower (suc k)))))
    → proj₁ (Unfolding.unfoldFunctor (out (embed k x ed)) .Functor.F₀ z)
      ≡ Unfolding.unfoldFunctor (out x) .Functor.F₀ (proj₁ z)

  -- When f has a non-fixed point, permuted-embed does not preserve F₀ at
  -- layer 0; the witness is the probe point a
  -- 当 f 有非不动点时，permuted-embed 在层 0 不保持 F₀；见证为探针点 a
  ¬-preserves-permuted
    : ∀ (f : Fin n → Fin n)
    → Σ (Fin n) (λ a → f a ≢ a)
    → ¬ PreservesF₀At 0 (λ k x ed → permuted-embed k f x ed)
  ¬-preserves-permuted f (a , fa≢a) pres =
    fa≢a (pres x ed z)
    where
      x  = cosmos-idN
      ed = UniformEmbeddingFamily.getData (default-unif 0) x
      z : Category.Obj (ShapeCat
            (StrictLayer.C (Tower.layer nTower 1))
            (StrictLayer.FC (Tower.layer nTower 1)))
      z = (a , lift tt) , lift (lift tt)

  -- Nontrivial permutation: has a non-fixed point
  -- 非平凡置换：有非不动点
  NontrivialPerm : (Fin n → Fin n) → Set
  NontrivialPerm f = Σ (Fin n) (λ a → f a ≢ a)

  -- PermutedPathWitness captures the four properties that refute
  -- criterion C
  -- PermutedPathWitness 捕捉反驳判据 C 的四条性质
  record PermutedPathWitness
      (embed : ∀ k
               → (x : Cosmos (StrictLayer.C (Tower.layer nTower k))
                           (StrictLayer.FC (Tower.layer nTower k)))
               → EmbeddingData x
               → Cosmos (StrictLayer.C (Tower.layer nTower (suc k)))
                        (StrictLayer.FC (Tower.layer nTower (suc k))))
    : Setω where
    field
      liftAt        : ∀ k
                    → Cosmos (StrictLayer.C (Tower.layer nTower k))
                             (StrictLayer.FC (Tower.layer nTower k))
                    → Cosmos FinCatN TrivialFCN
      liftAt-step   : ∀ k x ed → liftAt (suc k) (embed k x ed) ≈C liftAt k x
      liftAt-resp   : ∀ k {x y}
                    → _≈C_ {C = StrictLayer.C (Tower.layer nTower k)}
                           {FC = StrictLayer.FC (Tower.layer nTower k)} x y
                    → liftAt k x ≈C liftAt k y
      liftAt-0-inj  : ∀ {x y} → liftAt 0 x ≈C liftAt 0 y → x ≈C y
      not-preserves : ¬ PreservesF₀At 0 embed

  -- For any nontrivial permutation f with f⁻¹∘f = id, permuted-embed f
  -- and permuted-liftAt f f⁻¹ satisfy liftAt-step / liftAt-resp /
  -- liftAt-0-inj (feasibility), while PreservesF₀At fails — refuting
  -- criterion C: feasibility does not imply preservation of F₀
  -- 对任意满足 f⁻¹∘f = id 的非平凡置换 f，permuted-embed f 与
  -- permuted-liftAt f f⁻¹ 满足 liftAt-step / liftAt-resp / liftAt-0-inj
  -- （可行性），而 PreservesF₀At 失败——反驳判据 C：
  -- 可行性不蕴含 F₀ 的保持
  permuted-path-exists
    : (f f⁻¹ : Fin n → Fin n) (f⁻¹∘f : ∀ a → f⁻¹ (f a) ≡ a)
    → (nontriv : NontrivialPerm f)
    → PermutedPathWitness (λ k x ed → permuted-embed k f x ed)
  permuted-path-exists f f⁻¹ f⁻¹∘f nontriv = record
    { liftAt        = permuted-liftAt f f⁻¹ f⁻¹∘f
    ; liftAt-step   = λ k x ed → permuted-liftAt-step f f⁻¹ f⁻¹∘f k x ed
    ; liftAt-resp   = λ k {x} {y} eq → permuted-liftAt-resp f f⁻¹ f⁻¹∘f k eq
    ; liftAt-0-inj  = λ eq → eq
    ; not-preserves = ¬-preserves-permuted f nontriv
    }

  -- swapSum exchanges the two elements of Fin 2, leaving Fin m untouched
  -- swapSum 交换 Fin 2 的两个元素，Fin m 不动
  swapSum : Fin 2 ⊎ Fin m → Fin 2 ⊎ Fin m
  swapSum (inj₁ i) = inj₁ (opposite i)
  swapSum (inj₂ k) = inj₂ k

  -- swapSum is an involution
  -- swapSum 是对合
  swapSum-involutive : ∀ x → swapSum (swapSum x) ≡ x
  swapSum-involutive (inj₁ i) = cong inj₁ (opposite-involutive i)
  swapSum-involutive (inj₂ k) = refl

  -- swap01 exchanges fzero and fsuc fzero, leaving the rest fixed
  -- swap01 交换 fzero 与 fsuc fzero，其余不动
  swap01 : Fin n → Fin n
  swap01 i = join 2 m (swapSum (splitAt 2 i))

  -- swap01 is an involution
  -- swap01 是对合
  swap01-involutive : ∀ a → swap01 (swap01 a) ≡ a
  swap01-involutive i =
    begin
      swap01 (swap01 i)
        ≡⟨ refl ⟩
      join 2 m (swapSum (splitAt 2 (join 2 m (swapSum (splitAt 2 i)))))
        ≡⟨ cong (join 2 m)
             (cong swapSum (splitAt-join 2 m (swapSum (splitAt 2 i)))) ⟩
      join 2 m (swapSum (swapSum (splitAt 2 i)))
        ≡⟨ cong (join 2 m) (swapSum-involutive (splitAt 2 i)) ⟩
      join 2 m (splitAt 2 i)
        ≡⟨ join-splitAt 2 m i ⟩
      i
      ∎

  -- swap01 has a non-fixed point: fzero ↦ fsuc fzero
  -- swap01 有非不动点：fzero ↦ fsuc fzero
  swap01-nontrivial : NontrivialPerm swap01
  swap01-nontrivial = fzero , fsuc-fzero≠fzero

  -- Unconditional permuted path, specialised to swap01
  -- 置换路径的无条件存在性，特化到 swap01
  nontrivial-path-exists
    : PermutedPathWitness (λ k x ed → permuted-embed k swap01 x ed)
  nontrivial-path-exists =
    permuted-path-exists swap01 swap01 swap01-involutive swap01-nontrivial

  -- listCompose fs = right fold of fs under composition; empty fold is id
  -- listCompose fs = fs 在复合下的右折叠；空折叠为 id
  listCompose : List (Fin n → Fin n) → (Fin n → Fin n)
  listCompose []       = id
  listCompose (f ∷ fs) = f ∘ listCompose fs

  -- iterPermutedSeq fs x applies permuted-embed with fᵢ at layer i;
  -- layer count determined by length fs
  -- iterPermutedSeq fs x 对 fs 中的每个 fᵢ 在第 i 层应用 permuted-embed fᵢ；
  -- 层数由 length fs 决定
  iterPermutedSeq
    : (fs : List (Fin n → Fin n))
    → Cosmos FinCatN TrivialFCN
    → Cosmos (StrictLayer.C (Tower.layer nTower (length fs)))
             (StrictLayer.FC (Tower.layer nTower (length fs)))
  iterPermutedSeq []       x = x
  iterPermutedSeq (f ∷ fs) x =
    permuted-embed (length fs) f (iterPermutedSeq fs x)
      (UniformEmbeddingFamily.getData (default-unif (length fs))
        (iterPermutedSeq fs x))

  -- Accumulation lemma: proj-obj (length fs) ∘ F₀(iterPermutedSeq fs) at
  -- canonical point = listCompose fs ∘ x.F₀
  -- 累积引理：典范点处的 proj-obj (length fs) ∘ F₀(iterPermutedSeq fs)
  -- = listCompose fs ∘ x.F₀
  iterPermutedSeq-F₀-accum
    : ∀ (fs : List (Fin n → Fin n))
      (x : Cosmos FinCatN TrivialFCN) (A : Fin n)
    → proj-obj (length fs)
        (Unfolding.unfoldFunctor (out (iterPermutedSeq fs x)) .Functor.F₀
          (embed-obj (length fs) A ,
           embed-shape (length fs) (embed-obj (length fs) A)))
      ≡ listCompose fs
          (Unfolding.unfoldFunctor (out x) .Functor.F₀ (A , lift tt))
  iterPermutedSeq-F₀-accum []       x A = refl
  iterPermutedSeq-F₀-accum (f ∷ fs) x A =
    let
      k = length fs
      z = embed-obj (suc k) A , embed-shape (suc k) (embed-obj (suc k) A)
      y = iterPermutedSeq fs x
    in begin
      proj-obj (suc k)
        (Unfolding.unfoldFunctor (out (iterPermutedSeq (f ∷ fs) x)) .Functor.F₀ z)
        ≡⟨ refl ⟩
      proj-obj (suc k) (permuted-F₀ k f y z)
        ≡⟨ proj-obj-permuted-F₀ k f y z ⟩
      f (proj-obj k
          (Unfolding.unfoldFunctor (out y) .Functor.F₀
            (embed-obj k A , embed-shape k (embed-obj k A))))
        ≡⟨ cong f (iterPermutedSeq-F₀-accum fs x A) ⟩
      f (listCompose fs
          (Unfolding.unfoldFunctor (out x) .Functor.F₀ (A , lift tt)))
        ≡⟨ refl ⟩
      listCompose (f ∷ fs)
        (Unfolding.unfoldFunctor (out x) .Functor.F₀ (A , lift tt))
        ∎

  -- iterPow k f = f^k (ordinary function iteration)
  -- iterPow k f = f 的 k 次幂（普通函数迭代）
  iterPow : ℕ → (Fin n → Fin n) → (Fin n → Fin n)
  iterPow zero    f = λ a → a
  iterPow (suc k) f = f ∘ iterPow k f

  -- iterPermuted f k x: permuted-embed f iterated k times from layer 0
  -- iterPermuted f k x：从层 0 出发迭代 permuted-embed f k 次
  iterPermuted
    : (f : Fin n → Fin n)
    → ∀ k
    → Cosmos FinCatN TrivialFCN
    → Cosmos (StrictLayer.C (Tower.layer nTower k))
             (StrictLayer.FC (Tower.layer nTower k))
  iterPermuted f zero    x = x
  iterPermuted f (suc k) x =
    permuted-embed k f (iterPermuted f k x)
      (UniformEmbeddingFamily.getData (default-unif k) (iterPermuted f k x))

  -- After k iterations, F₀'s outermost Fin n component at the canonical
  -- embed-point is f^k applied to x.F₀ at (A, lift tt)
  -- 迭代 k 次后，F₀ 在典范嵌入点的最外层 Fin n 分量为 f^k 作用于
  -- x.F₀ (A, lift tt)
  iterPermuted-F₀-accum
    : ∀ (f : Fin n → Fin n) k
      (x : Cosmos FinCatN TrivialFCN) (A : Fin n)
    → proj-obj k
        (Unfolding.unfoldFunctor (out (iterPermuted f k x)) .Functor.F₀
          (embed-obj k A , embed-shape k (embed-obj k A)))
      ≡ iterPow k f
          (Unfolding.unfoldFunctor (out x) .Functor.F₀ (A , lift tt))
  iterPermuted-F₀-accum f zero x A = refl
  iterPermuted-F₀-accum f (suc k) x A =
    let
      z = embed-obj (suc k) A , embed-shape (suc k) (embed-obj (suc k) A)
      y = iterPermuted f k x
    in begin
      proj-obj (suc k)
        (Unfolding.unfoldFunctor (out (iterPermuted f (suc k) x)) .Functor.F₀ z)
        ≡⟨ refl ⟩
      proj-obj (suc k)
        (Unfolding.unfoldFunctor (out (permuted-embed k f y
          (UniformEmbeddingFamily.getData (default-unif k) y))) .Functor.F₀ z)
        ≡⟨ refl ⟩
      proj-obj (suc k) (permuted-F₀ k f y z)
        ≡⟨ proj-obj-permuted-F₀ k f y z ⟩
      f (proj-obj k (Unfolding.unfoldFunctor (out y) .Functor.F₀ (proj₁ z)))
        ≡⟨ refl ⟩
      f (proj-obj k
          (Unfolding.unfoldFunctor (out y) .Functor.F₀
            (embed-obj k A , embed-shape k (embed-obj k A))))
        ≡⟨ cong f (iterPermuted-F₀-accum f k x A) ⟩
      f (iterPow k f
          (Unfolding.unfoldFunctor (out x) .Functor.F₀ (A , lift tt)))
        ≡⟨ refl ⟩
      iterPow (suc k) f
        (Unfolding.unfoldFunctor (out x) .Functor.F₀ (A , lift tt))
        ∎

  -- Single-permutation iteration collapses to the original cosmoi
  -- 单置换迭代坍缩到原始宇宙
  permuted-liftAt-iterPermuted
    : ∀ (f f⁻¹ : Fin n → Fin n) (f⁻¹∘f : ∀ a → f⁻¹ (f a) ≡ a)
      (k : ℕ) (x : Cosmos FinCatN TrivialFCN)
    → permuted-liftAt f f⁻¹ f⁻¹∘f k (iterPermuted f k x) ≈C x
  permuted-liftAt-iterPermuted f f⁻¹ f⁻¹∘f zero x = ≈C-refl
  permuted-liftAt-iterPermuted f f⁻¹ f⁻¹∘f (suc k) x =
    ≈C-trans
      (permuted-liftAt-step f f⁻¹ f⁻¹∘f k (iterPermuted f k x)
        (UniformEmbeddingFamily.getData (default-unif k) (iterPermuted f k x)))
      (permuted-liftAt-iterPermuted f f⁻¹ f⁻¹∘f k x)

  -- Period 2 for any involution: iterPow (k+2) f = iterPow k f
  -- 任意对合的周期 2：iterPow (k+2) f = iterPow k f
  iterPow-involution-period2
    : ∀ (f : Fin n → Fin n)
    → (∀ a → f (f a) ≡ a)
    → ∀ k a → iterPow (suc (suc k)) f a ≡ iterPow k f a
  iterPow-involution-period2 f inv k a =
    begin
      iterPow (suc (suc k)) f a
        ≡⟨ refl ⟩
      f (f (iterPow k f a))
        ≡⟨ inv (iterPow k f a) ⟩
      iterPow k f a
    ∎

  -- F₀ projection of iterPermuted swap01 has period 2: layer (k+2) = layer k
  -- iterPermuted swap01 的 F₀ 投影周期为 2：层 (k+2) = 层 k
  iterPermuted-swap01-F₀-period2
    : ∀ k (x : Cosmos FinCatN TrivialFCN) (A : Fin n)
    → proj-obj (suc (suc k))
        (Unfolding.unfoldFunctor (out (iterPermuted swap01 (suc (suc k)) x))
          .Functor.F₀
          (embed-obj (suc (suc k)) A ,
           embed-shape (suc (suc k)) (embed-obj (suc (suc k)) A)))
      ≡ proj-obj k
          (Unfolding.unfoldFunctor (out (iterPermuted swap01 k x))
            .Functor.F₀
            (embed-obj k A , embed-shape k (embed-obj k A)))
  iterPermuted-swap01-F₀-period2 k x A =
    begin
      proj-obj (suc (suc k))
        (Unfolding.unfoldFunctor (out (iterPermuted swap01 (suc (suc k)) x))
          .Functor.F₀
          (embed-obj (suc (suc k)) A ,
           embed-shape (suc (suc k)) (embed-obj (suc (suc k)) A)))
        ≡⟨ iterPermuted-F₀-accum swap01 (suc (suc k)) x A ⟩
      iterPow (suc (suc k)) swap01
        (Unfolding.unfoldFunctor (out x) .Functor.F₀ (A , lift tt))
        ≡⟨ iterPow-involution-period2 swap01 swap01-involutive k
             (Unfolding.unfoldFunctor (out x) .Functor.F₀ (A , lift tt)) ⟩
      iterPow k swap01
        (Unfolding.unfoldFunctor (out x) .Functor.F₀ (A , lift tt))
        ≡⟨ sym (iterPermuted-F₀-accum swap01 k x A) ⟩
      proj-obj k
        (Unfolding.unfoldFunctor (out (iterPermuted swap01 k x))
          .Functor.F₀
          (embed-obj k A , embed-shape k (embed-obj k A)))
        ∎
