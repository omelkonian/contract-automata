{-# OPTIONS --allow-unsolved-metas #-}
open import Prelude.Init; open SetAsType
open Nat using (_⊓_)
open import Prelude.Sets
open import Prelude.DecEq
open import Prelude.InferenceRules
open import Prelude.Ord
open import Prelude.Measurable
open import Prelude.Decidable
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

data _⇒[_]_ : Conf s → l ⁺ → Conf s′ → ⦃ s —[ l ]→ s′ ⦄ → Type where

  Propose :
    ∙ 0 < payment .amount
    ∙ payment .amount ≤ v
    ∙ payment .deadline > d′ .end
      ───────────────────────────────────────────────────
      record {defWith v d; state = Holding}
      ⇒[ Propose payment ]
      record {defWith v d′; state = Collecting payment ∅}

  Add :
    ∙ key ∈ˢ sgs′
    ∙ key ∈ˢ authorizedKeys
      ───────────────────────────────────────────────────────────
      record { defWith v d; signers = sgs
            ; state = Collecting payment keys }
      ⇒[ Add key ]
      record { defWith v d′; signers = sgs′
            ; state = Collecting payment (keys ∪ singleton key) }

  Pay :
    ∙ ∣ keys ∣ ≥ noRequiredSignatures
    ∙ d′ .end ≤ payment .deadline
      ─────────────────────────────────────────────────────
      record {defWith v d; state = Collecting payment keys}
      ⇒[ Pay ]
      record { defWith (v ∸ payment .amount) d′
             ; state = Holding
             ; outputs = [ mkPayment payment ] }

  Cancel :
    d′ .start > payment .deadline
    ─────────────────────────────────────────────────────
    record {defWith v d; state = Collecting payment keys}
    ⇒[ Cancel ]
    record {defWith v d′; state = Holding}

_⇒⟨_⟩_ : (cs : Conf s) → (l⁺ : l ⁺) → (cs′ : Conf s′) → ⦃ s —[ l ]→ s′ ⦄ → Type
cs ⇒⟨ l⁺ ⟩ cs′ = (cs .duration .end < cs′ .duration .end) × (cs ⇒[ l⁺ ] cs′)

-- ** Contract Implementation

-- transition : (cs : Conf s) (l⁺ : l ⁺) → List Message → Time
--             → Maybe (∃ λ s′ → ∃ λ (cs′ : Conf s′) → (cs ⇒⟨ l⁺ ⟩ cs′))

transition : Conf s → l ⁺ → List Message → Time
           → Maybe (∃ λ s′ → (s —[ l ]→ s′) × Conf s′)
transition {Holding} {Propose} cs (Propose payment) is t =
  let t′ = t + standardInterval in
  if (cs == record {defWith (cs .value) (cs .duration); state = Holding})
   ∧ (is == [])
   ∧ (cs .duration .end <ᵇ t′)
   --
   ∧ (0 <ᵇ payment .amount)
   ∧ (payment .amount ≤ᵇ cs .value)
   ∧ (payment .deadline >ᵇ t′)
  then just $ -, it , record
    { def
    ; state = Collecting payment ∅
    ; value = cs .value
    ; duration = t , t′
    }
  else
    nothing
transition {Holding} {Add} cs l⁺ is t = nothing -- no λ where (_ , ())
transition {Holding} {Pay} cs l⁺ is t = nothing
transition {Holding} {Cancel} cs l⁺ is t = nothing
transition {Collecting} {Propose} cs l⁺ is t = nothing
transition {Collecting} {Add} cs (Add key) is t =
  let t′ = t + standardInterval in
  -- with Collecting payment keys ← cs .state =
  case cs .state of λ where
    (Collecting payment keys) →
      if (is == [])
       ∧ (cs .inputs == [])
       ∧ (cs .outputs == [])
       ∧ (cs .duration .end <ᵇ t′)
       --
       ∧ ⌊ key ∈ˢ? authorizedKeys ⌋
      then just $ -, it , record
        { def
        ; state = Collecting payment (keys ∪ singleton key)
        ; value = cs .value
        ; duration = t , t′
        ; signers = singleton key
        }
      else nothing
transition {Collecting} {Pay} cs l⁺ is t =
  case cs .state of λ where
    (Collecting payment keys) →
      let t′ = (t + standardInterval) ⊓ payment .deadline in
      if (is == [])
       ∧ (cs .inputs == [])
       ∧ (cs .outputs == [])
       ∧ (cs .signers == ∅)
       ∧ (cs .duration .end <ᵇ t′)
       --
       ∧ (∣ keys ∣ ≥ᵇ noRequiredSignatures)
       ∧ (t <ᵇ payment .deadline)
      then just $ -, it , record
        { def
        ; state = Holding
        ; value = cs .value ∸ payment .amount
        ; outputs = [ mkPayment payment ]
        ; duration = t , t′
        }
      else nothing
transition {Collecting} {Cancel} cs l⁺ is t =
  let t′ = t + standardInterval in
  case cs .state of λ where
    (Collecting payment keys) →
      if (is == [])
       ∧ (cs .inputs == [])
       ∧ (cs .outputs == [])
       ∧ (cs .signers == ∅)
       ∧ (cs .duration .end <ᵇ t′)
       --
       ∧ (t >ᵇ payment .deadline)
      then just $ -, it , record
        { def
        ; state = Holding
        ; value = cs .value
        ; duration = t , t′
        }
      else nothing

validate : s ⁺ → l ⁺ → Conf s′ → Bool
validate {Holding} {Propose} Holding (Propose payment) cs′ =
  case cs′ .state of λ where
    (Collecting payment′ keys) →
        (payment == payment′)
      ∧ (keys == ∅)
      ∧ (cs′ .inputs == [])
      ∧ (cs′ .outputs == [])
      ∧ (cs′ .signers == ∅)
      ∧ (0 <ᵇ payment .amount)
      ∧ (payment .amount ≤ᵇ cs′ .value)
      ∧ (payment .deadline >ᵇ cs′ .duration .end)
    _ → false
validate {Holding} {Add} s⁺ l⁺ cs′ = false
validate {Holding} {Pay} s⁺ l⁺ cs′ = false
validate {Holding} {Cancel} s⁺ l⁺ cs′ = false
validate {Collecting} {Propose} s⁺ l⁺ cs′ = false
validate {Collecting} {Add} s⁺ (Add key) cs′ =
  case cs′ .state of λ where
    (Collecting _ keys) →
        (cs′ .outputs == [])
      ∧ ⌊ key ∈ˢ? cs′ .signers ⌋
      ∧ ⌊ key ∈ˢ? authorizedKeys ⌋
      ∧ ⌊ key ∈ˢ? keys ⌋
    _ → false
validate {Collecting} {Pay} (Collecting payment keys) l⁺ cs′ =
  case cs′ .state of λ where
    Holding →
        (∣ keys ∣ ≥ᵇ noRequiredSignatures)
      ∧ (cs′ .duration .end ≤ᵇ payment .deadline)
      ∧ (take 1 (cs′ .outputs) == [ mkPayment payment ])
    _ → false
validate {Collecting} {Cancel} (Collecting payment keys) l⁺ cs′ =
  case cs′ .state of λ where
    Holding →
        (cs′ .outputs == [])
      ∧ (cs′ .duration .start >ᵇ payment .deadline)
    _ → false

-- ** Soundness

validation-sound : ∀ {s⁺ : s ⁺} {l⁺ : l ⁺} {cs′ : Conf s′} →
  T (validate s⁺ l⁺ cs′)
  ─────────────────────────
  ∃ λ (s→ : s —[ l ]→ s′) →
  ∃ λ (cs : Conf s) →
    (cs ⇒⟨ l⁺ ⟩ cs′) ⦃ s→ ⦄
validation-sound {Holding} {Propose} {s′} {Holding} {Propose payment} {cs′} val≡
  with Collecting payment′ keys ← cs′ .state in st≡
  with yes refl ← payment ≟ payment′
  with yes refl ← keys ≟ ∅
  with yes refl ← cs′ .inputs ≟ []
  with yes refl ← cs′ .outputs ≟ []
  with yes refl ← cs′ .signers ≟ ∅
  with yes p₁ ← 0 <? payment .amount
  with yes p₂ ← payment .amount ≤? cs′ .value
  with yes p₃ ← payment .deadline >? cs′ .duration .end
  rewrite st≡
  = Propose
  , (record {defWith (cs′ .value) {!!}; state = Holding})
  , {!!}
  , Propose p₁ p₂ p₃
validation-sound {Collecting} {Add} {s′} {s⁺} {Add x} {cs′} val≡ = {!!}
validation-sound {Collecting} {Pay} {s′} {s⁺} {Pay} {cs′} val≡ = {!!}
validation-sound {Collecting} {Cancel} {s′} {s⁺} {Cancel} {cs′} val≡ = {!!}

transition-sound : ∀ {cs : Conf s} {l⁺ : l ⁺} {cs′ : Conf s′} {is : List Message} →
  ∀ (s→ : s —[ l ]→ s′) →

  transition cs l⁺ is t ≡ just (s′ , s→ , cs′)
  ────────────────────────────────────────────
  (cs ⇒⟨ l⁺ ⟩ cs′) ⦃ s→ ⦄
  -- × (cs′ .inputs ⊆ is)
  -- × T (validate (cs .state) l⁺ cs′)
transition-sound {Holding}{Propose}{s′}{t}{cs}{Propose payment}{cs′}{is} Propose tr≡
  with yes refl ← cs ≟ record {def; value = cs .value; duration = cs .duration; state = Holding}
  with yes refl ← is ≟ []
  with yes d< ← cs .duration .end <? t + standardInterval
  with yes p₁ ← 0 <? payment .amount
  with yes p₂ ← payment .amount ≤? cs .value
  with yes p₃ ← payment .deadline >? t + standardInterval
  with refl ← tr≡
  = d< , Propose p₁ p₂ p₃
transition-sound {Collecting}{Add}{s′}{t}{cs}{Add key}{cs′}{is} Add tr≡
  with Collecting payment keys ← cs .state in st≡
  with yes refl ← is ≟ []
  with yes refl ← cs .inputs ≟ []
  with yes refl ← cs .outputs ≟ []
  with yes d< ← cs .duration .end <? t + standardInterval
  with yes k∈ ← key ∈ˢ? authorizedKeys
  with refl ← tr≡
  rewrite st≡
  = d< , Add ∈ˢ-singleton k∈
transition-sound {Collecting}{Pay}{s′}{t}{cs}{Pay}{cs′}{is} Pay tr≡
  with Collecting payment keys ← cs .state in st≡
  with yes refl ← is ≟ []
  with yes refl ← cs .inputs ≟ []
  with yes refl ← cs .outputs ≟ []
  with yes refl ← cs .signers ≟ ∅
  with yes d< ← cs .duration .end <? (t + standardInterval) ⊓ payment .deadline
  with yes k> ← ∣ keys ∣ ≥? noRequiredSignatures
  with yes t< ← t <? payment .deadline
  with refl ← tr≡
  rewrite st≡
  = d< , Pay k> (Nat.m⊓n≤n (t + standardInterval) (payment .deadline))
transition-sound {Collecting}{Cancel}{s′}{t}{cs}{Cancel}{cs′}{is} Cancel tr≡
  with Collecting payment keys ← cs .state in st≡
  with yes refl ← is ≟ []
  with yes refl ← cs .inputs ≟ []
  with yes refl ← cs .outputs ≟ []
  with yes refl ← cs .signers ≟ ∅
  with yes d< ← cs .duration .end <? t + standardInterval
  with yes t< ← t >? payment .deadline
  with refl ← tr≡
  rewrite st≡
  = d< , Cancel t<

-- ** Completeness

validation-complete : ∀ {s→ : s —[ l ]→ s′} (cs : Conf s) (l⁺ : l ⁺) (cs′ : Conf s′) →

  (cs ⇒⟨ l⁺ ⟩ cs′) ⦃ s→ ⦄
  ───────────────────────────────
  T (validate (cs .state) l⁺ cs′)
validation-complete {Holding} {Propose} {.Collecting}
  cs
  (Propose payment)
  cs′@(record {state = .(Collecting payment ∅); outputs = .[]})
  (d< , Propose p₁ p₂ p₃)
  rewrite ≟-refl payment
        | dec-yes (0 <? payment .amount) p₁ .proj₂
        | dec-yes (payment .amount ≤? cs′ .value) p₂ .proj₂
        | dec-yes (payment .deadline >? cs′ .duration .end) p₃ .proj₂
        = tt
validation-complete {Collecting} {Add} {s′}
  cs@(record {state = .(Collecting _ keys)})
  (Add key)
  cs′@(record {state = .(Collecting _ (keys ∪ singleton key))})
  (d< , Add {keys = keys} k∈ k∈auth)
  rewrite dec-yes (key ∈ˢ? cs′ .signers) k∈ .proj₂
        | dec-yes (key ∈ˢ? authorizedKeys) k∈auth .proj₂
        | dec-yes (key ∈ˢ? keys ∪ singleton key)
                  (∈-∪⁺ʳ key keys (singleton key) ∈ˢ-singleton) .proj₂
        = tt
validation-complete {Collecting} {Pay} {s′}
  cs@(record {state = .(Collecting payment keys)})
  Pay
  cs′@(record {state = .Holding})
  (d< , Pay {keys = keys} {payment = payment} k≥ d≤)
  rewrite dec-yes (∣ keys ∣ ≥? noRequiredSignatures) k≥ .proj₂
        | dec-yes (cs′ .duration .end ≤? payment .deadline) d≤ .proj₂
        | dec-yes (take 1 (cs′ .outputs) ≟ [ mkPayment payment ]) refl .proj₂
        = tt
validation-complete {Collecting} {Cancel} {s′}
  cs@(record {state = .(Collecting payment keys)})
  Cancel
  cs′@(record {state = .Holding})
  (d< , Cancel {payment = payment} {keys = keys} d>)
  rewrite dec-yes (cs′ .duration .start >? payment .deadline) d> .proj₂
        = tt

transition-complete : ∀ {cs : Conf s} {l⁺ : l ⁺} {cs′ : Conf s′} {is : List Message} →
  ∀ (s→ : s —[ l ]→ s′) →

  ∙ (cs ⇒⟨ l⁺ ⟩ cs′) ⦃ s→ ⦄
  -- ∙ (cs′ .inputs ⊆ is)
  -- ∙ T (validate (cs .state) l⁺ cs′)
  ────────────────────────────────────────────────────────────────
  transition cs l⁺ is t ≡ just (s′ , s→ , cs′)
transition-complete {Holding} {Propose} {s′} {t} {cs} {Propose payment} {cs′} {is}
  s→ (d< , Propose p₁ p₂ p₃)
  rewrite dec-yes (cs ≟ record {def; value = cs .value; duration = cs .duration; state = Holding}) refl .proj₂
        | dec-yes (is ≟ []) {!!} .proj₂
        | dec-yes (cs .duration .end <? t + standardInterval) {!!} .proj₂
        | dec-yes (0 <? payment .amount) p₁ .proj₂
        | dec-yes (payment .amount ≤? cs .value) p₂ .proj₂
        | dec-yes (payment .deadline >? t + standardInterval) {!p₃!} .proj₂
        | (cs′ .duration ≡ (t , t + standardInterval)) ∋ {!!}
        = refl
transition-complete {Collecting} {Add} {s′} {t} {cs} {l⁺} {cs′} {is} s→ s⇒ = {!!}
transition-complete {Collecting} {Pay} {s′} {t} {cs} {l⁺} {cs′} {is} s→ s⇒ = {!!}
transition-complete {Collecting} {Cancel} {s′} {t} {cs} {l⁺} {cs′} {is} s→ s⇒ = {!!}
