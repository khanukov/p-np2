import Complexity.TMVerifier.TuringToolkit.TrueUniformSeekMutation

/-!
# T1a/T1b-A true uniform-seek examples

The first example retains the canonical codec probe.  The named T1b-A probes
specialize genuine `TM.runConfig` execution theorems at index zero, a nonzero
index, and the empty-data out-of-bounds path.  They do not claim the T1b-B
loop invariant, restoration, output, or acceptance.
-/

namespace Pnp3.Internal.PsubsetPpoly.TM

/-- A small canonical request used to instantiate the T1a codec theorem. -/
def t1aExampleRequest : T1Request := ⟨2, [true, false, true]⟩

example : decodeT1Tape? (encodeT1 t1aExampleRequest) = some t1aExampleRequest :=
  decodeT1Tape_encode t1aExampleRequest

/-- Genuine initial-configuration cursor installation at runtime index zero. -/
def t1bIndexZeroRequest : T1Request := ⟨0, [true, false]⟩

def t1bIndexZero_install :=
  t1CS_runConfig_install_first_cursor_exact
    t1bIndexZeroRequest true [false] rfl

/-- Genuine initial-configuration cursor installation at a nonzero index. -/
def t1bNonzeroIndexRequest : T1Request := ⟨2, [true, false, true]⟩

def t1bNonzeroIndex_install :=
  t1CS_runConfig_install_first_cursor_exact
    t1bNonzeroIndexRequest true [false, true] rfl

/-- Exact finite-prefix empty-data execution reaches the OOB boundary.  The
former full-public-clock probe is gone: T1c-1 activated that boundary, so the
machine no longer stays there for the rest of the clock. -/
def t1bEmptyDataRequest : T1Request := ⟨2, []⟩

def t1bEmptyData_oob_exact :=
  t1CS_oob_empty_data_exact t1bEmptyDataRequest rfl

end Pnp3.Internal.PsubsetPpoly.TM
