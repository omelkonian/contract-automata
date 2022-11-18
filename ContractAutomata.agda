open import Prelude.Init; open SetAsType
open import Prelude.Sets
open import Prelude.DecEq
open import Prelude.InferenceRules
open import Prelude.Ord
open import Prelude.Measurable
open import Prelude.Decidable
open import Prelude.Null
open import Prelude.Setoid
open import Prelude.DecLists

-- ** Base DFA

data State : Type where
  Holding Collecting : State
unquoteDecl DecEq-S = DERIVE DecEq [ quote State , DecEq-S ]

data Label : Type where
  Propose Add Pay Cancel : Label
unquoteDecl DecEq-L = DERIVE DecEq [ quote Label , DecEq-L ]

data _—[_]→_ : State → Label → State → Type where
  instance
    Propose : Holding    —[ Propose ]→ Collecting
    Add     : Collecting —[ Add ]→     Collecting
    Pay     : Collecting —[ Pay ]→     Holding
    Cancel  : Collecting —[ Cancel ]→  Holding

Value = ℕ; Key = ℕ; KeyHash = Key; Time = ℕ

-- ** Augmentation ↝ Configurations

record Payment : Type where
  field amount    : Value
        recipient : Key
        deadline  : Time
open Payment

record Augmentable (A : Type) : Type₁ where
  constructor augment
  field _⁺ : Pred₀ A
open Augmentable ⦃...⦄

data State⁺ : Pred₀ State where
  Holding    : State⁺ Holding
  Collecting : Payment → Set⟨ KeyHash ⟩ → State⁺ Collecting

data Label⁺ : Pred₀ Label where
  Propose : Payment → Label⁺ Propose
  Add     : KeyHash → Label⁺ Add
  Pay     : Label⁺ Pay
  Cancel  : Label⁺ Cancel

instance Aug-State = augment State⁺
         Aug-Label = augment Label⁺

Message = Value × KeyHash

mkPayment : Payment → Message
mkPayment p = p .amount , p .recipient

record Duration : Type where
  constructor _,_
  field start : Time
        end   : Time
open Duration

module def where
  inputs  = List Message ∋ []
  outputs = List Message ∋ []
  signers = Set⟨ KeyHash ⟩ ∋ ∅

record Conf (s : State) : Type where
  field state : s ⁺
        value : Value
        inputs : List Message
        outputs : List Message
        duration : Duration
        signers : Set⟨ KeyHash ⟩
open Conf

postulate
  startTime standardInterval : Time
  owner : KeyHash
  authorizedKeys : Set⟨ KeyHash ⟩
  noRequiredSignatures : ℕ

initial : Value → Conf Holding
initial val = record
  { state = Holding
  ; value = val
  ; inputs = [ val , owner ]
  ; outputs = []
  ; duration = startTime , startTime
  ; signers = singleton owner
  }

private variable
  t t′ : Time
  s s′ : State
  l l′ : Label
  v v′ : Value
  d d′ : Duration
  sgs sgs′ keys keys′ : Set⟨ KeyHash ⟩
  payment payment′ : Payment
  key key′ : Key

-- ** Configuration Relation

data _⇒⟨_⟩_ : (src : Conf s) → l ⁺ → (dst : Conf s′)
            → ⦃ s —[ l ]→ s′ ⦄
            → ⦃ src .duration .end < dst .duration .end ⦄
            → Type where

  Propose : ∀ (d≤ : d .end < d′ .end) → let instance _ = d≤ in
    ∙ payment .amount ≤ v
    ∙ payment .deadline > d′ .end
      ─────────────────────────────────────
      record { def
             ; state = Holding
             ; value = v
             ; duration = d
             ; signers = sgs
             }
      ⇒⟨ Propose payment ⟩
      record { def
             ; state = Collecting payment ∅
             ; value = v
             ; duration = d′
             ; signers = sgs
             }

  Add : ∀ (d≤ : d .end < d′ .end) → let instance _ = d≤ in
    ∙ key ∈ˢ authorizedKeys
      ──────────────────────────────────────────────────────────
      record { def
             ; state = Collecting payment keys
             ; value = v
             ; duration = d
             ; signers = sgs
             }
      ⇒⟨ Add key ⟩
      record { def
             ; state = Collecting payment (singleton key ∪ keys)
             ; value = v
             ; duration = d′
             ; signers = sgs
             }

  Pay : ∀ (d≤ : d .end < d′ .end) → let instance _ = d≤ in
    ∙ d′ .end ≤ payment .deadline
    ∙ ∣ keys ∣ > noRequiredSignatures
      ───────────────────────────────────────────────────────────
      record { def
             ; state = Collecting payment keys
             ; value = v
             ; duration = d
             ; signers = sgs
             }
      ⇒⟨ Pay ⟩
      record { def
             ; state = Holding
             ; value = v ∸ payment .amount
             ; duration = d′
             ; signers = sgs
             ; outputs = [ mkPayment payment ]
             }

  Cancel : ∀ (d≤ : d .end < d′ .end) → let instance _ = d≤ in
    d′ .start > payment .deadline
    ───────────────────────────────────────────────────────────
    record { state = Collecting payment keys
           ; value = v
           ; duration = d
           ; signers = sgs
           ; def
           }
    ⇒⟨ Cancel ⟩
    record { state = Holding
           ; value = v
           ; duration = d′
           ; signers = sgs
           ; def
           }

-- ** Contract Implementation

-- transition : Conf s → l ⁺ → List Message → Time → Dec (∃ λ s′ → (s —[ l ]→ s′) × Conf s′)
transition : Conf s → l ⁺ → List Message → Time
           → Maybe (∃ λ s′ → (s —[ l ]→ s′) × Conf s′)
transition {Holding} {Propose} s⁺ (Propose payment) ms t =
  if (0 <ᵇ payment .amount)
   ∧ (payment .amount ≤ᵇ s⁺ .value)
   ∧ (payment .deadline >ᵇ standardInterval)
  then just $ -, it , record
    { def
    ; state = Collecting payment ∅
    ; value = s⁺ .value
    ; duration = t , t + standardInterval
    }
  else
    nothing
transition {Holding} {Add} s⁺ l⁺ ms t = nothing -- no λ where (_ , ())
transition {Holding} {Pay} s⁺ l⁺ ms t = nothing
transition {Holding} {Cancel} s⁺ l⁺ ms t = nothing
transition {Collecting} {Propose} s⁺ l⁺ ms t = nothing
transition {Collecting} {Add} s⁺ (Add key) ms t =
  -- with Collecting payment keys ← s⁺ .state =
  case s⁺ .state of λ where
    (Collecting payment keys) →
      if (ms == []) ∧ ⌊ key ∈ˢ? authorizedKeys ⌋ then
        just $ -, it , record
          { def
          ; state = Collecting payment (keys ∪ singleton key)
          ; value = s⁺ .value
          ; duration = t , t + standardInterval
          ; signers = singleton key
          }
      else nothing
transition {Collecting} {Pay} s⁺ l⁺ ms t =
  case s⁺ .state of λ where
    (Collecting payment keys) →
      if (ms == []) ∧ (∣ keys ∣ ≥ᵇ noRequiredSignatures) ∧ (t <ᵇ payment .deadline) then
        just $ -, it , record
          { def
          ; state = Holding
          ; value = s⁺ .value ∸ payment .amount
          ; outputs = [ mkPayment payment ]
          ; duration = t , min (t + standardInterval) (payment .deadline)
          }
      else nothing
transition {Collecting} {Cancel} s⁺ l⁺ ms t =
  case s⁺ .state of λ where
    (Collecting payment keys) →
      if (ms == []) ∧ (t >ᵇ payment .deadline) then
        just $ -, it , record
          { def
          ; state = Holding
          ; value = s⁺ .value
          ; duration = t , t + standardInterval
          }
      else nothing

validate : s ⁺ → l ⁺ → Conf s′ → Bool
validate {Holding} {Propose} Holding (Propose payment) s⁺′ =
  case s⁺′ .state of λ where
    (Collecting payment keys) →
        (s⁺′ .outputs == [])
      ∧ (0 <ᵇ payment .amount)
      ∧ (payment .amount ≤ᵇ s⁺′ .value)
      ∧ (payment .deadline >ᵇ s⁺′ .duration .end)
      ∧ Nullᵇ keys
    _ → false
validate {Holding} {Add} s⁺ l⁺ s⁺′ = false
validate {Holding} {Pay} s⁺ l⁺ s⁺′ = false
validate {Holding} {Cancel} s⁺ l⁺ s⁺′ = false
validate {Collecting} {Propose} s⁺ l⁺ s⁺′ = false
validate {Collecting} {Add} s⁺ (Add key) s⁺′ =
  case s⁺′ .state of λ where
    (Collecting payment keys) →
        (s⁺′ .outputs == [])
      ∧ ⌊ key ∈ˢ? s⁺′ .signers ⌋
      ∧ ⌊ key ∈ˢ? authorizedKeys ⌋
      ∧ ⌊ key ∈ˢ? keys ⌋
    _ → false
validate {Collecting} {Pay} (Collecting payment keys) l⁺ s⁺′ =
  case s⁺′ .state of λ where
    Holding →
        (∣ keys ∣ ≥ᵇ noRequiredSignatures)
      ∧ (s⁺′ .duration .end ≤ᵇ payment .deadline)
      ∧ (take 1 (s⁺′ .outputs) == [ mkPayment payment ])
    _ → false
validate {Collecting} {Cancel} (Collecting payment keys) l⁺ s⁺′ =
  case s⁺′ .state of λ where
    Holding →
        (s⁺′ .outputs == [])
      ∧ (s⁺′ .duration .start >ᵇ payment .deadline)
    _ → false

-- ** Soundness

postulate
  transition-sound : ∀ {s⁺ : Conf s} {l⁺ : l ⁺} {s⁺′ : Conf s′} {is : List Message} →
    ∀ (s→ : s —[ l ]→ s′) →
    ∙ transition s⁺ l⁺ is t ≡ just (s′ , s→ , s⁺′)
      ────────────────────────────────────────────────────────────────
      ∃ λ (d≤ : s⁺ .duration .end < s⁺′ .duration .end)
      → (s⁺ ⇒⟨ l⁺ ⟩ s⁺′) ⦃ s→ ⦄ ⦃ d≤ ⦄
      × (s⁺′ .inputs ⊆ is)
      × T (validate (s⁺ .state) l⁺ s⁺′)

-- ** Completeness?
