import Complexity.TMVerifier.TuringToolkit.TrueUniformSeekTerminal

/-!
# Concrete T1c-2 terminal execution probes

Named specializations of success, nonempty-OOB and empty-OOB restoration.
They end at literal accept/reject states but do not compose from initialConfig
or claim the final public-clock acceptance equivalence.
-/

namespace Pnp3.Internal.PsubsetPpoly.TM

/-- Selected slot 2 contains true. -/
def t1c2SuccessRequest : T1Request := ⟨2, [false, false, true]⟩

def t1c2SuccessTerminal :=
  t1CS_terminal_success_exact t1c2SuccessRequest true rfl

def t1c2SuccessOutputAt :=
  t1CS_success_final_tape_at t1c2SuccessRequest true
    ⟨t1OutputPosition t1c2SuccessRequest,
      t1OutputPosition_safe t1c2SuccessRequest⟩ rfl

/-- Three index units but only two data cells. -/
def t1c2OobRequest : T1Request := ⟨3, [true, false]⟩

def t1c2OobTerminal :=
  t1CS_terminal_oob_exact t1c2OobRequest false rfl (by decide)

/-- Empty data: the input tape remains unchanged and the machine rejects. -/
def t1c2EmptyRequest : T1Request := ⟨2, []⟩

def t1c2EmptyTerminal :=
  t1CS_terminal_oob_empty_exact t1c2EmptyRequest rfl

end Pnp3.Internal.PsubsetPpoly.TM
