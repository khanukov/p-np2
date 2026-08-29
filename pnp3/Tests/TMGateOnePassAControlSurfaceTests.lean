import Complexity.TMVerifier.TuringToolkit.GateOnePassAControl

/-!
# G1 dormant pass-A control: surface tests

Import-side contracts for the S1b1 slice's executed layer: the two one-step
atoms of the dormant pass-A entry, the A-specific tag recount, the whole entry,
the local `const` rejection, and the six all-literal probes.

Every run pinned here starts from a **caller-supplied** aligned configuration.
Nothing here starts from `G1M.initialConfig`, and nothing could: the twelve
pass-A modes are unreachable from the live control
(`g1Advance_passA`, `g1Transition_passA_closed`), and `readAStart` — the handoff
S1b2 will turn into the dispatch that reaches `aBof` — is **still idle**.

Deliberately absent, here and in the module it audits: any operand-1 read, walk,
invariant, repair or out-of-range branch; any combine step, output write,
`TM.accepts`, full-clock or acceptance-gate claim; and any statement about a run
from the real initial configuration.  The `const` rejection is a local fact
about a configuration nothing reaches, not a claim that the machine rejects
`const` requests.

This is an audit surface: it pins public signatures, it does not prove anything
new.
-/

namespace Pnp3.Tests.TMGateOnePassAControlSurface

open Pnp3.Internal.PsubsetPpoly.TM
open Pnp3.Internal.PsubsetPpoly.TM.G1PassAControlExamples

-- The executed layer of the dormant entry.
#check @g1CS_step_aOp
#check @g1CS_runConfig_aInstall_idle
#check @g1CS_aTagRescan_exact
#check @g1CS_passA_entry_exact
#check @g1CS_passA_entry_ctx
#check @g1CS_passA_const_reject_exact

-- The six all-literal probes and the literal requests behind them.
#check @aInputExample
#check @aNotExample
#check @aAndExample
#check @aOrExample
#check @aConstExample
#check @examples_canonical
#check @example_lengths
#check @probe_safe
#check @input_latch
#check @not_latch
#check @and_false_latch
#check @and_true_latch
#check @or_true_latch
#check @const_reject
#check @latched_residuals_distinct

/-! ## Exact theorem-contract pins -/

/-- **The operation latch, executed.**  One stationary step; the tape, the head
and `vB` are untouched, and only the pair `(pass, crossed)` changes. -/
theorem check_g1CS_step_aOp (n h : Nat) (hh : h < G1M.tapeLength n)
    (tape : Fin (G1M.tapeLength n) → Bool) (t : G1Tag) (ht : t ≠ .const)
    (ctx : G1Ctx) :
    G1M.runConfig
        (g1AlignedConfig n h hh tape (g1AOpMode t) .p0 false false false ctx)
        1 =
      g1AlignedConfig n h hh tape .aInstallStart .p0 false false false
        (ctx.withRes (g1Residual t ctx.vB)) :=
  g1CS_step_aOp n h hh tape t ht ctx

/-- **The install handoff is idle for the whole remaining budget.**  This is the
honest boundary of the dormant entry: operand 1 is not read. -/
theorem check_g1CS_runConfig_aInstall_idle (n h : Nat)
    (hh : h < G1M.tapeLength n) (tape : Fin (G1M.tapeLength n) → Bool)
    (ctx : G1Ctx) (k : Nat) :
    G1M.runConfig
        (g1AlignedConfig n h hh tape .aInstallStart .p0 false false false ctx)
        k =
      g1AlignedConfig n h hh tape .aInstallStart .p0 false false false ctx :=
  g1CS_runConfig_aInstall_idle n h hh tape ctx k

/-- **The whole dormant pass-A entry, executed.**  Exactly `4u + 9` steps from
the anchor read to the install handoff, on the caller's frame word, with the
tape bit-for-bit unchanged. -/
theorem check_g1CS_passA_entry_exact (n : Nat) (pre suffix : List G1Frame)
    (r : G1Request) (ht : r.tag ≠ .const) (ctx : G1Ctx)
    (hsafe : 4 * (pre.length + (r.tag.units + 2)) < G1M.tapeLength n) :
    G1M.runConfig
        (g1AlignedConfig n (4 * pre.length) (by omega)
          (g1ListTape (n := n)
            ((pre ++ g1TagRouteFrames r ++ suffix).flatMap G1Frame.bits))
          .aBof .p0 false false false ctx)
        (4 * (r.tag.units + 2) + 1) =
      g1AlignedConfig n (4 * (pre.length + (r.tag.units + 2))) hsafe
        (g1ListTape (n := n)
          ((pre ++ g1TagRouteFrames r ++ suffix).flatMap G1Frame.bits))
        .aInstallStart .p0 false false false
        (ctx.withRes (g1Residual r.tag ctx.vB)) :=
  g1CS_passA_entry_exact n pre suffix r ht ctx hsafe

/-- **What the entry leaves behind**: the gate's residual in the two spare
context bits, and the operand-2 value still in `vB`. -/
theorem check_g1CS_passA_entry_ctx (r : G1Request) (ctx : G1Ctx) :
    (ctx.withRes (g1Residual r.tag ctx.vB)).res = g1Residual r.tag ctx.vB ∧
      (ctx.withRes (g1Residual r.tag ctx.vB)).vB = ctx.vB :=
  g1CS_passA_entry_ctx r ctx

/-- **The four literal probes latch four different residuals**, so the table is
not vacuous, and the five literal requests are genuinely canonical. -/
theorem check_probe_residuals :
    (g1Residual aInputExample.tag false = .idA ∧
        g1Residual aNotExample.tag false = .notA ∧
        g1Residual aAndExample.tag false = .constFalse ∧
        g1Residual aOrExample.tag true = .constTrue ∧
        ({.idA, .notA, .constFalse, .constTrue} : Finset G1Residual).card = 4) ∧
      (aInputExample.Canonical ∧ aNotExample.Canonical ∧
        aAndExample.Canonical ∧ aOrExample.Canonical ∧
        aConstExample.Canonical) :=
  ⟨latched_residuals_distinct, examples_canonical⟩

end Pnp3.Tests.TMGateOnePassAControlSurface
