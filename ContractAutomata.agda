open import Prelude.Init; open SetAsType
open Nat using (_⊓_)
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
    Add     : Collecting —[ Add     ]→ Collecting
    Pay     : Collecting —[ Pay     ]→ Holding
    Cancel  : Collecting —[ Cancel  ]→ Holding
unquoteDecl DecEq-—[]→ = DERIVE DecEq [ quote _—[_]→_ , DecEq-—[]→ ]

Value = ℕ; Key = ℕ; KeyHash = Key; Time = ℕ

-- ** Augmentation ↝ Configurations

record Payment : Type where
  field amount    : Value
        recipient : Key
        deadline  : Time
open Payment
unquoteDecl DecEq-Payment = DERIVE DecEq [ quote Payment , DecEq-Payment ]

record Augmentable (A : Type) : Type₁ where
  constructor augment
  field _⁺ : Pred₀ A
open Augmentable ⦃...⦄

data State⁺ : Pred₀ State where
  Holding    : State⁺ Holding
  Collecting : Payment → Set⟨ KeyHash ⟩ → State⁺ Collecting
unquoteDecl DecEq-State⁺ = DERIVE DecEq [ quote State⁺ , DecEq-State⁺ ]

data Label⁺ : Pred₀ Label where
  Propose : Payment → Label⁺ Propose
  Add     : KeyHash → Label⁺ Add
  Pay     : Label⁺ Pay
  Cancel  : Label⁺ Cancel
unquoteDecl DecEq-Label⁺ = DERIVE DecEq [ quote Label⁺ , DecEq-Label⁺ ]

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
unquoteDecl DecEq-Duration = DERIVE DecEq [ quote Duration , DecEq-Duration ]

module def where
  inputs  = List Message ∋ []
  outputs = List Message ∋ []
  signers = Set⟨ KeyHash ⟩ ∋ ∅
module defWith (v : Value) (d : Duration) where
  open def public
  value = v
  duration = d
record Conf (s : State) : Type where
  field state : s ⁺
        value : Value
        inputs : List Message
        outputs : List Message
        duration : Duration
        signers : Set⟨ KeyHash ⟩
open Conf
unquoteDecl DecEq-Conf = DERIVE DecEq [ quote Conf , DecEq-Conf ]

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

  Propose : ∀ (d< : d .end < d′ .end) → let instance _ = d< in
    ∙ payment .amount ≤ v
    ∙ payment .deadline > d′ .end
      ───────────────────────────────────────────────────
      record {defWith v d; state = Holding}
      ⇒⟨ Propose payment ⟩
      record {defWith v d′; state = Collecting payment ∅}

  Add : ∀ (d< : d .end < d′ .end) → let instance _ = d< in
    ∙ key ∈ˢ authorizedKeys
      ────────────────────────────────────────────────────────────
      record { defWith v d; signers = sgs
             ; state = Collecting payment keys }
      ⇒⟨ Add key ⟩
      record { defWith v d′; signers = sgs′
             ; state = Collecting payment (keys ∪ singleton key) }

  Pay : ∀ (d< : d .end < d′ .end) → let instance _ = d< in
    ∙ ∣ keys ∣ ≥ noRequiredSignatures
    ∙ d′ .end ≤ payment .deadline
      ─────────────────────────────────────────────────────
      record {defWith v d; state = Collecting payment keys}
      ⇒⟨ Pay ⟩
      record { defWith (v ∸ payment .amount) d′
             ; state = Holding
             ; outputs = [ mkPayment payment ] }

  Cancel : ∀ (d< : d .end < d′ .end) → let instance _ = d< in
    d′ .start > payment .deadline
    ─────────────────────────────────────────────────────
    record {defWith v d; state = Collecting payment keys}
    ⇒⟨ Cancel ⟩
    record {defWith v d′; state = Holding}

-- ** Contract Implementation

-- transition : (s⁺ : Conf s) (l⁺ : l ⁺) → List Message → Time
--             → Maybe (∃ λ s′ → ∃ λ (s⁺′ : Conf s′) → (s⁺ ⇒⟨ l⁺ ⟩ s⁺′))

transition : Conf s → l ⁺ → List Message → Time
           → Maybe (∃ λ s′ → (s —[ l ]→ s′) × Conf s′)
transition {Holding} {Propose} s⁺ (Propose payment) is t =
  let t′ = t + standardInterval in
  if (s⁺ == record {defWith (s⁺ .value) (s⁺ .duration); state = Holding})
   ∧ (is == [])
   ∧ (s⁺ .duration .end <ᵇ t′)
   --
   ∧ (0 <ᵇ payment .amount)
   ∧ (payment .amount ≤ᵇ s⁺ .value)
   ∧ (payment .deadline >ᵇ t′)
  then just $ -, it , record
    { def
    ; state = Collecting payment ∅
    ; value = s⁺ .value
    ; duration = t , t′
    }
  else
    nothing
transition {Holding} {Add} s⁺ l⁺ is t = nothing -- no λ where (_ , ())
transition {Holding} {Pay} s⁺ l⁺ is t = nothing
transition {Holding} {Cancel} s⁺ l⁺ is t = nothing
transition {Collecting} {Propose} s⁺ l⁺ is t = nothing
transition {Collecting} {Add} s⁺ (Add key) is t =
  let t′ = t + standardInterval in
  -- with Collecting payment keys ← s⁺ .state =
  case s⁺ .state of λ where
    (Collecting payment keys) →
      if (is == [])
       ∧ (s⁺ .inputs == [])
       ∧ (s⁺ .outputs == [])
       ∧ (s⁺ .duration .end <ᵇ t′)
       --
       ∧ ⌊ key ∈ˢ? authorizedKeys ⌋
      then just $ -, it , record
        { def
        ; state = Collecting payment (keys ∪ singleton key)
        ; value = s⁺ .value
        ; duration = t , t′
        ; signers = singleton key
        }
      else nothing
transition {Collecting} {Pay} s⁺ l⁺ is t =
  case s⁺ .state of λ where
    (Collecting payment keys) →
      let t′ = (t + standardInterval) ⊓ payment .deadline in
      if (is == [])
       ∧ (s⁺ .inputs == [])
       ∧ (s⁺ .outputs == [])
       ∧ (s⁺ .signers == ∅)
       ∧ (s⁺ .duration .end <ᵇ t′)
       --
       ∧ (∣ keys ∣ ≥ᵇ noRequiredSignatures)
       ∧ (t <ᵇ payment .deadline)
      then just $ -, it , record
        { def
        ; state = Holding
        ; value = s⁺ .value ∸ payment .amount
        ; outputs = [ mkPayment payment ]
        ; duration = t , t′
        }
      else nothing
transition {Collecting} {Cancel} s⁺ l⁺ is t =
  let t′ = t + standardInterval in
  case s⁺ .state of λ where
    (Collecting payment keys) →
      if (is == [])
       ∧ (s⁺ .inputs == [])
       ∧ (s⁺ .outputs == [])
       ∧ (s⁺ .signers == ∅)
       ∧ (s⁺ .duration .end <ᵇ t′)
       --
       ∧ (t >ᵇ payment .deadline)
      then just $ -, it , record
        { def
        ; state = Holding
        ; value = s⁺ .value
        ; duration = t , t′
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

transition-sound : ∀ {s⁺ : Conf s} {l⁺ : l ⁺} {s⁺′ : Conf s′} {is : List Message} →
  ∀ (s→ : s —[ l ]→ s′) →
  ∙ transition s⁺ l⁺ is t ≡ just (s′ , s→ , s⁺′)
    ────────────────────────────────────────────────────────────────
    ∃ λ (d< : s⁺ .duration .end < s⁺′ .duration .end)
    → (s⁺ ⇒⟨ l⁺ ⟩ s⁺′) ⦃ s→ ⦄ ⦃ d< ⦄
    -- × (s⁺′ .inputs ⊆ is)
    -- × T (validate (s⁺ .state) l⁺ s⁺′)
transition-sound {Holding}{Propose}{s′}{t}{s⁺}{Propose payment}{s⁺′}{is} Propose tr≡
  with yes refl ← s⁺ ≟ record {def; value = s⁺ .value; duration = s⁺ .duration; state = Holding}
  with yes refl ← is ≟ []
  with yes d< ← s⁺ .duration .end <? t + standardInterval
  with yes p₁ ← 0 <? payment .amount
  with yes p₂ ← payment .amount ≤? s⁺ .value
  with yes p₃ ← payment .deadline >? t + standardInterval
  with refl ← tr≡
  = d< , Propose d< p₂ p₃
transition-sound {Collecting}{Add}{s′}{t}{s⁺}{Add key}{s⁺′}{is} Add tr≡
  with Collecting payment keys ← s⁺ .state in st≡
  with yes refl ← is ≟ []
  with yes refl ← s⁺ .inputs ≟ []
  with yes refl ← s⁺ .outputs ≟ []
  with yes d< ← s⁺ .duration .end <? t + standardInterval
  with yes k∈ ← key ∈ˢ? authorizedKeys
  with refl ← tr≡
  rewrite st≡
  = d< , Add d< k∈
transition-sound {Collecting}{Pay}{s′}{t}{s⁺}{Pay}{s⁺′}{is} Pay tr≡
  with Collecting payment keys ← s⁺ .state in st≡
  with yes refl ← is ≟ []
  with yes refl ← s⁺ .inputs ≟ []
  with yes refl ← s⁺ .outputs ≟ []
  with yes refl ← s⁺ .signers ≟ ∅
  with yes d< ← s⁺ .duration .end <? (t + standardInterval) ⊓ payment .deadline
  with yes k> ← ∣ keys ∣ ≥? noRequiredSignatures
  with yes t< ← t <? payment .deadline
  with refl ← tr≡
  rewrite st≡
  = d< , Pay d< k> (Nat.m⊓n≤n (t + standardInterval) (payment .deadline))
transition-sound {Collecting}{Cancel}{s′}{t}{s⁺}{Cancel}{s⁺′}{is} Cancel tr≡
  with Collecting payment keys ← s⁺ .state in st≡
  with yes refl ← is ≟ []
  with yes refl ← s⁺ .inputs ≟ []
  with yes refl ← s⁺ .outputs ≟ []
  with yes refl ← s⁺ .signers ≟ ∅
  with yes d< ← s⁺ .duration .end <? t + standardInterval
  with yes t< ← t >? payment .deadline
  with refl ← tr≡
  rewrite st≡
  = d< , Cancel d< t<

-- ** Completeness?
