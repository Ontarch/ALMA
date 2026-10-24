------------------------------------------------------------------------
-- Standard model: concrete instantiation of ALMA
--
-- Defines basic attribute types, core beings (stable self and random
-- environment), feedback system frameworks, coherence and consciousness
-- emergence, transient processes with phase transitions, and the
-- standard model overview.
--
-- 标准模型：ALMA 框架的具体实例化
--
-- 定义了基础属性类型、核心存在者（稳定自我与随机环境）、反馈系统框架、
-- 相干性与意识涌现、含相变的瞬态过程，以及标准模型总览。
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --exact-split --guardedness --double-check #-}

module Wellspring.StandardModel where

open import Wellspring.Universe public

-- Basic types
-- 基础类型
Attr2D : Set
Attr2D = Fin 2 → ℕ
Attr1D : Set
Attr1D = Fin 1 → ℕ
State : Set
State = Attr2D × Attr1D

-- Core being definitions
-- 核心存在者定义
stableSelf : Attr2D
stableSelf i = if toℕ i ≡ᵇ 0 then 1 else 42
private
  self-c : ℕ
  self-c = 0
  self-stream : Stream (Attr2D × ℕ)
  self-stream = constStream (stableSelf , self-c)
  self-essence-const : Always (λ x → proj₂ x ≡ self-c) self-stream
  self-essence-const = constStream-always-gen (stableSelf , self-c) refl
  self-init-consistent : proj₁ (head self-stream) ≡ stableSelf
  self-init-consistent = refl
selfBeing : Process Attr2D ℕ
selfBeing = mkProc stableSelf self-c self-stream self-essence-const self-init-consistent
self-being-weak-hom : WeakHom selfBeing
self-being-weak-hom n m = trans (constStream-obsS-constant (stableSelf , self-c) n)
                                (sym (constStream-obsS-constant (stableSelf , self-c) m))
module _ (init : ℕ) (c : ℕ) where
  private
    mkRandomBeing-coalg : ℕ → StreamF (Attr1D × ℕ) ℕ
    mkRandomBeing-coalg n = ((λ _ → n) , c) , suc n
    mkRandomBeing-stream : Stream (Attr1D × ℕ)
    mkRandomBeing-stream = ana mkRandomBeing-coalg init
    mkRandomBeing-essence-const : Always (λ x → proj₂ x ≡ c) mkRandomBeing-stream
    mkRandomBeing-essence-const = helper init
      where
      helper : ∀ n → Always (λ x → proj₂ x ≡ c) (ana mkRandomBeing-coalg n)
      helper n .Always.head = refl
      helper n .Always.tail = helper (suc n)
    mkRandomBeing-init-consistent : proj₁ (head mkRandomBeing-stream) ≡ (λ _ → init)
    mkRandomBeing-init-consistent = refl
    lemma-random-obs : ∀ k n → 
      proj₁ (head (stream-tail-n (ana mkRandomBeing-coalg k) n)) ≡ (λ _ → k + n)
    lemma-random-obs k zero =
      begin
        proj₁ (head (stream-tail-n (ana mkRandomBeing-coalg k) zero))
          ≡⟨ refl ⟩
        (λ _ → k)
          ≡⟨ cong (λ m → λ _ → m) (sym (+-identityʳ k)) ⟩
        (λ _ → k + zero)
      ∎
    lemma-random-obs k (suc n) =
      begin
        proj₁ (head (stream-tail-n (ana mkRandomBeing-coalg k) (suc n)))
          ≡⟨ refl ⟩
        proj₁ (head (stream-tail-n (Stream.tail (ana mkRandomBeing-coalg k)) n))
          ≡⟨ refl ⟩
        proj₁ (head (stream-tail-n (ana mkRandomBeing-coalg (suc k)) n))
          ≡⟨ lemma-random-obs (suc k) n ⟩
        (λ _ → suc k + n)
          ≡⟨ refl ⟩
        (λ _ → suc (k + n))
          ≡⟨ cong (λ m → λ _ → m) (sym (+-suc k n)) ⟩
        (λ _ → k + suc n)
      ∎
  mkRandomBeing : Process Attr1D ℕ
  mkRandomBeing = mkProc (λ _ → init) c mkRandomBeing-stream mkRandomBeing-essence-const mkRandomBeing-init-consistent
  observe-mkRandomBeing : ∀ n → observe mkRandomBeing n ≡ (λ _ → init + n)
  observe-mkRandomBeing n =
    begin
      observe mkRandomBeing n
        ≡⟨ refl ⟩
      proj₁ (head (stream-tail-n mkRandomBeing-stream n))
        ≡⟨ lemma-random-obs init n ⟩
      (λ _ → init + n)
    ∎
  mkRandomBeing-changes : Changes mkRandomBeing
  mkRandomBeing-changes = 0 , λ eq →
    let eq' : init + 0 ≡ init + 1
        eq' = cong (λ f → f zero) (trans (sym (observe-mkRandomBeing 0)) (trans eq (observe-mkRandomBeing 1)))
        eq1 : init ≡ init + 1
        eq1 = trans (sym (+-identityʳ init)) eq'
        eq2 : init ≡ suc init
        eq2 = trans eq1 (trans (+-suc init 0) (cong suc (+-identityʳ init)))
    in n≢sucn init eq2
randomBeing : Process Attr1D ℕ
randomBeing = mkRandomBeing 0 0
observe-random-n : ∀ n → observe randomBeing n ≡ (λ _ → n)
observe-random-n n = observe-mkRandomBeing 0 0 n
random-being-changes : Changes randomBeing
random-being-changes = mkRandomBeing-changes 0 0
random-being-delta : Δ randomBeing
random-being-delta = 0 , 1 , λ eq →
  zero≢suc (cong (λ f → f zero)
    (trans (sym (observe-random-n 0))
           (trans eq (observe-random-n 1))))
same-essence : core selfBeing ≡ core randomBeing
same-essence = refl
self-random-interact : Process (Attr2D × Attr1D) ℕ
self-random-interact = interact selfBeing randomBeing
interact-essence-conserved : core self-random-interact ≡ core selfBeing
interact-essence-conserved = core-interact selfBeing randomBeing

-- Feedback system framework
-- 反馈系统框架
record FeedbackRules : Set where
  field
    nextSelf   : Attr2D → State → Attr2D
    nextRandom : Attr1D → State → Attr1D
    essence    : ℕ
open FeedbackRules public
mkFeedbackCoalg : FeedbackRules → State → StreamF (State × ℕ) State
mkFeedbackCoalg rules (s , r) =
  let s' = rules .nextSelf s (s , r)
      r' = rules .nextRandom r (s , r)
  in (((s , r) , rules .essence) , (s' , r'))
feedback-essence-const-gen : ∀ (rules : FeedbackRules) (init : State)
                           → Always (λ x → proj₂ x ≡ rules .essence)
                                     (ana (mkFeedbackCoalg rules) init)
feedback-essence-const-gen rules init = helper init
  where
    helper : ∀ state → Always (λ x → proj₂ x ≡ rules .essence)
                              (ana (mkFeedbackCoalg rules) state)
    helper state .Always.head = refl
    helper state .Always.tail = helper (proj₂ (mkFeedbackCoalg rules state))
mkFeedbackProcess : FeedbackRules → State → Process State ℕ
mkFeedbackProcess rules init = mkProc
  init
  (rules .essence)
  (ana (mkFeedbackCoalg rules) init)
  (feedback-essence-const-gen rules init)
  refl
unidirectional-rules : FeedbackRules
unidirectional-rules = record
  { nextSelf   = λ self _ → self
  ; nextRandom = λ env _ → λ _ → suc (env zero)
  ; essence    = 0
  }
bidirectional-rules : FeedbackRules
bidirectional-rules = record
  { nextSelf   = λ self _ → self
  ; nextRandom = λ _ (self , _) → λ _ → suc (self zero)
  ; essence    = 0
  }
initSelf : Attr2D
initSelf = stableSelf
initRandom : Attr1D
initRandom = λ _ → 0
initState : State
initState = (initSelf , initRandom)
feedbackProcess : Process State ℕ
feedbackProcess = mkFeedbackProcess unidirectional-rules initState
bidirectionalProcess : Process State ℕ
bidirectionalProcess = mkFeedbackProcess bidirectional-rules initState
PairAt-gen : ∀ (rules : FeedbackRules) (init : State) → ℕ → State
PairAt-gen rules init n = proj₁ (head (stream-tail-n (ana (mkFeedbackCoalg rules) init) n))
SelfAt-gen : ∀ (rules : FeedbackRules) (init : State) → ℕ → Attr2D
SelfAt-gen rules init n = proj₁ (PairAt-gen rules init n)
RandAt-gen : ∀ (rules : FeedbackRules) (init : State) → ℕ → Attr1D
RandAt-gen rules init n = proj₂ (PairAt-gen rules init n)
bidirPairAt : ℕ → State
bidirPairAt = PairAt-gen bidirectional-rules initState
bidirSelfAt : ℕ → Attr2D
bidirSelfAt = SelfAt-gen bidirectional-rules initState
bidirRandAt : ℕ → Attr1D
bidirRandAt = RandAt-gen bidirectional-rules initState
feedbackPairAt : ℕ → State
feedbackPairAt = PairAt-gen unidirectional-rules initState
feedbackSelfAt : ℕ → Attr2D
feedbackSelfAt = SelfAt-gen unidirectional-rules initState
feedbackRandAt : ℕ → Attr1D
feedbackRandAt = RandAt-gen unidirectional-rules initState
SelfAt-const-gen : ∀ (rules : FeedbackRules) (init : State)
                 → (∀ s st → rules .nextSelf s st ≡ s)
                 → ∀ n → SelfAt-gen rules init n ≡ proj₁ init
SelfAt-const-gen rules init nextSelf-id n = helper init n
  where
    helper : ∀ state n → SelfAt-gen rules state n ≡ proj₁ state
    helper state zero = refl
    helper state (suc n) =
      let next-state = proj₂ (mkFeedbackCoalg rules state)
          next-state-preserves-self : proj₁ next-state ≡ proj₁ state
          next-state-preserves-self = nextSelf-id (proj₁ state) state
      in trans (helper next-state n) next-state-preserves-self
RandAt-follows-self-gen : ∀ (rules : FeedbackRules) (init : State)
                        → (∀ s st → rules .nextSelf s st ≡ s)
                        → (∀ r st → (rules .nextRandom r st) zero ≡ suc (proj₁ st zero))
                        → ∀ n → RandAt-gen rules init (suc n) zero ≡ suc (proj₁ init zero)
RandAt-follows-self-gen rules init nextSelf-id nextRandom-follows-self n = helper init n
  where
    helper : ∀ state n → RandAt-gen rules state (suc n) zero ≡ suc (proj₁ state zero)
    helper state zero = nextRandom-follows-self (proj₂ state) state
    helper state (suc n) =
      let next-state = proj₂ (mkFeedbackCoalg rules state)
          next-state-preserves-self : proj₁ next-state ≡ proj₁ state
          next-state-preserves-self = nextSelf-id (proj₁ state) state
      in trans (helper next-state n) (cong (λ x → suc (x zero)) next-state-preserves-self)
RandAt-strictly-increasing-gen : ∀ (rules : FeedbackRules) (init : State)
                               → (∀ r st → (rules .nextRandom r st) zero ≡ suc (r zero))
                               → ∀ n → RandAt-gen rules init (suc n) zero ≡ suc (RandAt-gen rules init n zero)
RandAt-strictly-increasing-gen rules init nextRandom-inc n = helper init n
  where
    helper : ∀ state n → RandAt-gen rules state (suc n) zero ≡ suc (RandAt-gen rules state n zero)
    helper state zero = nextRandom-inc (proj₂ state) state
    helper state (suc n) = helper (proj₂ (mkFeedbackCoalg rules state)) n
bidirSelfAt-const : ∀ n → bidirSelfAt n ≡ initSelf
bidirSelfAt-const = SelfAt-const-gen bidirectional-rules initState (λ _ _ → refl)
bidirRandAt-follows-self : ∀ n → bidirRandAt (suc n) zero ≡ suc (initSelf zero)
bidirRandAt-follows-self = RandAt-follows-self-gen
  bidirectional-rules
  initState
  (λ _ _ → refl)
  (λ _ _ → refl)
feedbackRandAt-strictly-increasing : ∀ n → feedbackRandAt (suc n) zero ≡ suc (feedbackRandAt n zero)
feedbackRandAt-strictly-increasing = RandAt-strictly-increasing-gen 
  unidirectional-rules 
  initState 
  (λ _ _ → refl)

-- Coherence and consciousness emergence
-- 相干性与意识涌现
countOver : (ℕ → Bool) → ℕ → ℕ
countOver P zero    = 0
countOver P (suc n) = (if P n then 1 else 0) + countOver P n
mkInternalCount : (ℕ → Attr2D) → (ℕ → ℕ)
mkInternalCount selfAt steps = 
  countOver (λ k → does (selfAt k zero ≟ selfAt (suc k) zero)) (steps ∸ 1)
mkExternalCount : (ℕ → Attr2D) → (ℕ → ℕ) → (ℕ → ℕ)
mkExternalCount selfAt externalSource steps = 
  countOver (λ k → does (selfAt k zero ≟ externalSource k)) steps
mkCoherenceProof : (ic ec : ℕ → ℕ)
                 → (steps : ℕ)
                 → (n m : ℕ)
                 → ic steps ≡ n
                 → ec steps ≡ m
                 → n > m
                 → ic steps > ec steps
mkCoherenceProof _ _ _ _ _ ic≡n ec≡m n>m =
  subst-inequality ic≡n ec≡m n>m
mkDissipationProof : (ic ec : ℕ → ℕ)
                   → (steps : ℕ)
                   → (n m : ℕ)
                   → ic steps ≡ n
                   → ec steps ≡ m
                   → m > n
                   → ec steps > ic steps
mkDissipationProof _ _ _ _ _ ic≡n ec≡m m>n =
  subst-inequality ec≡m ic≡n m>n
mkConsciousnessEmergence : (ic ec : ℕ → ℕ)
                         → ic 5 > ec 5
                         → ∃ λ steps → ic steps > ec steps
mkConsciousnessEmergence ic ec proof = 5 , proof
randRandom : ℕ → ℕ
randRandom k = observe randomBeing k zero
internalCount : ℕ → ℕ
internalCount = mkInternalCount feedbackSelfAt
externalCount : ℕ → ℕ
externalCount = mkExternalCount feedbackSelfAt randRandom
internal5 : ℕ
internal5 = internalCount 5
internal5≡4 : internal5 ≡ 4
internal5≡4 = refl
external5 : ℕ
external5 = externalCount 5
external5≡1 : external5 ≡ 1
external5≡1 = refl
coherenceProof : internal5 > external5
coherenceProof = mkCoherenceProof internalCount externalCount 5 4 1 refl refl 
  (s≤s (s≤s (z≤n {2})))
consciousnessEmergence : ∃ λ steps → internalCount steps > externalCount steps
consciousnessEmergence = mkConsciousnessEmergence internalCount externalCount coherenceProof
bidirInternalCount : ℕ → ℕ
bidirInternalCount = mkInternalCount bidirSelfAt
bidirExternalCount : ℕ → ℕ
bidirExternalCount = mkExternalCount bidirSelfAt (λ k → bidirRandAt k zero)
bidirInternal5 : ℕ
bidirInternal5 = bidirInternalCount 5
bidirInternal5≡4 : bidirInternal5 ≡ 4
bidirInternal5≡4 = refl
bidirExternal5 : ℕ
bidirExternal5 = bidirExternalCount 5
bidirExternal5≡0 : bidirExternal5 ≡ 0
bidirExternal5≡0 = refl
bidirCoherenceProof : bidirInternal5 > bidirExternal5
bidirCoherenceProof = mkCoherenceProof bidirInternalCount bidirExternalCount 5 4 0 refl refl 
  (s≤s (z≤n {3}))
bidirConsciousnessEmergence : ∃ λ steps → bidirInternalCount steps > bidirExternalCount steps
bidirConsciousnessEmergence = mkConsciousnessEmergence bidirInternalCount bidirExternalCount bidirCoherenceProof
ConsciousnessTheorem : (Process State ℕ → (ℕ → ℕ)) → Process State ℕ → Set
ConsciousnessTheorem external-source p =
  ∃ λ steps →
    let
      pairAt' n = proj₁ (head (stream-tail-n (stream p) n))
      selfAt' n = proj₁ (pairAt' n)
      internal = countOver (λ k → does (selfAt' k zero ≟ selfAt' (suc k) zero)) (steps ∸ 1)
      external = countOver (λ k → does (selfAt' k zero ≟ external-source p k)) steps
    in internal > external
feedback-external-source : Process State ℕ → (ℕ → ℕ)
feedback-external-source _ k = randRandom k
bidirectional-external-source : Process State ℕ → (ℕ → ℕ)
bidirectional-external-source _ k = bidirRandAt k zero
Theorem-holds-for-feedback : ConsciousnessTheorem feedback-external-source feedbackProcess
Theorem-holds-for-feedback = consciousnessEmergence
Theorem-holds-for-bidirectional : ConsciousnessTheorem bidirectional-external-source bidirectionalProcess
Theorem-holds-for-bidirectional = bidirConsciousnessEmergence

-- Transient processes and phase transitions
-- 瞬态过程与相变
env : ℕ → ℕ
env n = observe randomBeing n zero
env≡n : ∀ n → env n ≡ n
env≡n n = cong (λ f → f zero) (observe-random-n n)
v : ℕ → ℕ
v n = if does (n <? 7) then 0 else n
stage : ℕ → ℕ
stage n = if does (n <? 5) then 0
          else (if does (n <? 7) then 1 else 2)
pair→attr : ℕ × ℕ → Attr2D
pair→attr (val , s) i = if toℕ i ≡ᵇ 0 then val else s
transient-coalg : ℕ → StreamF (Attr2D × ℕ) ℕ
transient-coalg n =
  let state = (v n , stage n)
  in ((pair→attr state , 0) , suc n)
transientStream : Stream (Attr2D × ℕ)
transientStream = ana transient-coalg 0
transient-essence-const : Always (λ x → proj₂ x ≡ 0) transientStream
transient-essence-const = helper 0
  where
    helper : ∀ n → Always (λ x → proj₂ x ≡ 0) (ana transient-coalg n)
    helper n .Always.head = refl
    helper n .Always.tail = helper (suc n)
transientBeing : Process Attr2D ℕ
transientBeing = mkProc
  (pair→attr (v 0 , stage 0))
  0
  transientStream
  transient-essence-const
  refl
transientSelfAt : ℕ → Attr2D
transientSelfAt n = observe transientBeing n
cInternal5 : ℕ
cInternal5 = mkInternalCount transientSelfAt 5
cInternal5≡4 : cInternal5 ≡ 4
cInternal5≡4 = refl
cExternal5 : ℕ
cExternal5 = mkExternalCount transientSelfAt env 5
cExternal5≡1 : cExternal5 ≡ 1
cExternal5≡1 = refl
coherence-phase : cInternal5 > cExternal5
coherence-phase = mkCoherenceProof
  (mkInternalCount transientSelfAt)
  (mkExternalCount transientSelfAt env)
  5 4 1 refl refl
  (s≤s (s≤s (z≤n {2})))
dInternal : ℕ
dInternal = countOver (λ k → v (7 + k) ≡ᵇ v (7 + suc k)) 2
dInternal≡0 : dInternal ≡ 0
dInternal≡0 = refl
dExternal : ℕ
dExternal = countOver (λ k → v (7 + k) ≡ᵇ env (7 + k)) 3
dExternal≡3 : dExternal ≡ 3
dExternal≡3 = refl
dissipation-phase : dExternal > dInternal
dissipation-phase = mkDissipationProof
  (λ steps → countOver (λ k → v (7 + k) ≡ᵇ v (7 + suc k)) (steps ∸ 1))
  (λ steps → countOver (λ k → v (7 + k) ≡ᵇ env (7 + k)) steps)
  3 0 3 refl refl
  (s≤s (z≤n {2}))
∃-coherence : ∃ λ steps → countOver (λ k → v k ≡ᵇ v (suc k)) (steps ∸ 1) > countOver (λ k → v k ≡ᵇ env k) steps
∃-coherence = 5 , subst (λ x → x > cExternal5) (sym cInternal5≡4) coherence-phase
∃-dissipation : ∃ λ steps → countOver (λ k → v (7 + k) ≡ᵇ v (7 + suc k)) (steps ∸ 1) < countOver (λ k → v (7 + k) ≡ᵇ env (7 + k)) steps
∃-dissipation = 3 , subst (λ x → dInternal < x) (sym dExternal≡3) dissipation-phase
phase-transition-exists : ∃ λ (p : Process Attr2D ℕ) →
  (∃ λ steps → countOver (λ k → v k ≡ᵇ v (suc k)) (steps ∸ 1) > countOver (λ k → v k ≡ᵇ env k) steps) ×
  (∃ λ steps → countOver (λ k → v (7 + k) ≡ᵇ v (7 + suc k)) (steps ∸ 1) < countOver (λ k → v (7 + k) ≡ᵇ env (7 + k)) steps)
phase-transition-exists = transientBeing , (∃-coherence , ∃-dissipation)

-- Standard model overview
-- 标准模型总览
record StandardModel : Setω where
  field
    indestructibility : Indestructibility-Theorem
    indestructibility-uniqueness : Indestructibility-Uniqueness
    process-uniqueness       : Process-Uniqueness
    core-conservation        : ∀ {ℓ₁ ℓ₂} {O : Set ℓ₁} {C : Set ℓ₂} (p : Process O C) → core (next p) ≡ core p
    self        : Process Attr2D ℕ
    random      : Process Attr1D ℕ
    nonunif     : ∃ λ n1 → ∃ λ n2 → observe random n1 ≢ observe random n2
    conscious   : ∃ λ steps → internalCount steps > externalCount steps
    consciousBidir : ∃ λ steps → bidirInternalCount steps > bidirExternalCount steps
    coherencePhase   : Σ ℕ (λ steps → cInternal5 > cExternal5)
    dissipationPhase : Σ ℕ (λ steps → dExternal > dInternal)
standardModel : StandardModel
standardModel = record
  { indestructibility = indestructibility-proof
  ; indestructibility-uniqueness = indestructibility-uniqueness-proof
  ; process-uniqueness       = process-uniqueness-proof
  ; core-conservation        = c-conservation
  ; self            = selfBeing
  ; random          = randomBeing
  ; nonunif         = 0 , 1 , λ p → zero≢suc (cong (λ f → f zero) p)
  ; conscious       = consciousnessEmergence
  ; consciousBidir  = bidirConsciousnessEmergence
  ; coherencePhase  = 5 , coherence-phase
  ; dissipationPhase = 3 , dissipation-phase
  }
