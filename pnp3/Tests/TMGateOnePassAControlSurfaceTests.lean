import Complexity.TMVerifier.TuringToolkit.GateOnePassAControl

/-!
# G1 live pass-A entry: surface tests

Import-side contracts for the pass-A executed layer: the two one-step atoms of
the live entry, the A-specific tag recount, the whole entry,
the local `const` rejection, and the six all-literal probes.

The caller-supplied rescan contracts remain pinned, together with the S1b2b
activation from the real `G1M.initialConfig`: non-`const` routes enter `aBof`
and reach `aInstallStart` with the exact residual, while `const` reaches the
result-ready combine boundary.  S4 adds the one exact entry step from that
boundary to aligned `aInsSeek`; scan/probe/writer execution is audited by the
installation surface.

Deliberately absent, here and in the module it audits: any installation scan,
normal walk, repair or out-of-range branch; any combine step, output write,
`TM.accepts`, full-clock or acceptance-gate claim.  The `const` rejection is a
local fact about the A-specific recount, not a claim that the machine rejects
canonical `const` requests: the live result-ready route bypasses that recount.

This is an audit surface: it pins public signatures, it does not prove anything
new.
-/

namespace Pnp3.Tests.TMGateOnePassAControlSurface

open Pnp3.Internal.PsubsetPpoly
open Pnp3.Internal.PsubsetPpoly.TM
open Pnp3.Internal.PsubsetPpoly.TM.G1PassAControlExamples

-- The executed layer of the live entry.
#check @g1CS_step_aOp
#check @g1CS_step_aInstallStart
#check @g1CS_aTagRescan_exact
#check @g1CS_passA_entry_exact
#check @g1CS_passA_entry_ctx
#check @g1CS_passA_const_reject_exact
#check @g1ABofConfig
#check @g1AInstallConfig
#check @g1AInstallSeekConfig
#check @g1CombineConfig
#check @g1ABofConfig_head
#check @g1ABofConfig_ctx
#check @g1AInstallConfig_head
#check @g1AInstallConfig_res
#check @g1AInstallConfig_vB
#check @g1AInstallSeekConfig_head
#check @g1AInstallSeekConfig_res
#check @g1AInstallSeekConfig_vB
#check @g1CombineConfig_ctx
#check @g1UActivatedSteps
#check @g1BActivatedSteps
#check @g1ConstActivatedSteps
#check @g1CS_activate_unary_exact
#check @g1CS_activate_binary_exact
#check @g1CS_activate_const_exact
#check @g1CS_install_binary_exact
#check @g1CS_aInstall_entry_initial_exact

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

/-- The generic unary route extends its repaired endpoint by exactly one step
to the live pass-A anchor, on the real initial tape. -/
theorem check_g1CS_activate_unary_exact (r : G1Request) (hc : r.Canonical)
    (ht : r.tag = .input ∨ r.tag = .not) :
    G1M.runConfig (G1M.initialConfig (g1Point (encodeG1 r)))
        (g1UActivatedSteps r) = g1ABofConfig r false :=
  g1CS_activate_unary_exact r hc ht

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

/-- **The live install entry.**  One stationary step preserves the complete
configuration payload and enters aligned `aInsSeek`. -/
theorem check_g1CS_step_aInstallStart (n h : Nat)
    (hh : h < G1M.tapeLength n) (tape : Fin (G1M.tapeLength n) → Bool)
    (ctx : G1Ctx) :
    G1M.runConfig
        (g1AlignedConfig n h hh tape .aInstallStart .p0 false false false ctx)
        1 =
      g1AlignedConfig n h hh tape .aInsSeek .p0 false false false ctx :=
  g1CS_step_aInstallStart n h hh tape ctx

theorem check_g1AInstallSeekConfig_head (r : G1Request) (b : Bool) :
    ((g1AInstallSeekConfig r b).head : Nat) = 4 * (r.tag.units + 2) :=
  g1AInstallSeekConfig_head r b

theorem check_g1AInstallSeekConfig_res (r : G1Request) (b : Bool) :
    (g1AInstallSeekConfig r b).state.snd.ctx.res = g1Residual r.tag b :=
  g1AInstallSeekConfig_res r b

theorem check_g1AInstallSeekConfig_vB (r : G1Request) (b : Bool) :
    (g1AInstallSeekConfig r b).state.snd.ctx.vB = b :=
  g1AInstallSeekConfig_vB r b

theorem check_g1CS_aInstall_entry_initial_exact (r : G1Request) (b : Bool) :
    TM.runConfig (M := G1M) (g1AInstallConfig r b) 1 =
      g1AInstallSeekConfig r b :=
  g1CS_aInstall_entry_initial_exact r b

/-- **The whole pass-A entry, executed.**  Exactly `4u + 9` steps from
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

/-- The live-anchor adapter uses the exact initial tape and reaches the exact
residual-latched install configuration. -/
theorem check_g1CS_passA_entry_initial_exact (r : G1Request)
    (ht : r.tag ≠ .const) (b : Bool) :
    TM.runConfig (M := G1M) (g1ABofConfig r b)
        (4 * (r.tag.units + 2) + 1) = g1AInstallConfig r b :=
  g1CS_passA_entry_initial_exact r ht b

/-- **What the entry leaves behind**: the gate's residual in the two spare
context bits, and the operand-2 value still in `vB`. -/
theorem check_g1CS_passA_entry_ctx (r : G1Request) (ctx : G1Ctx) :
    (ctx.withRes (g1Residual r.tag ctx.vB)).res = g1Residual r.tag ctx.vB ∧
      (ctx.withRes (g1Residual r.tag ctx.vB)).vB = ctx.vB :=
  g1CS_passA_entry_ctx r ctx

/-- The generic successful binary route reaches the exact live anchor boundary
in one step beyond the merged repaired endpoint. -/
theorem check_g1CS_activate_binary_exact (r : G1Request) (hc : r.Canonical)
    (ht : r.tag = .and ∨ r.tag = .or) (b : Bool)
    (hb : r.vals[r.arg2]? = some b) :
    G1M.runConfig (G1M.initialConfig (g1Point (encodeG1 r)))
        (g1BActivatedSteps r) = g1ABofConfig r b :=
  g1CS_activate_binary_exact r hc ht b hb

/-- A successful binary activation is exactly at the A anchor and not at the
result boundary. -/
theorem check_g1CS_activate_binary_not_result (r : G1Request)
    (hc : r.Canonical) (ht : r.tag = .and ∨ r.tag = .or) (b : Bool)
    (hb : r.vals[r.arg2]? = some b) :
    (TM.runConfig (M := G1M) (G1M.initialConfig (g1Point (encodeG1 r)))
        (g1BActivatedSteps r)).state.snd.mode = .aBof ∧
      (TM.runConfig (M := G1M) (G1M.initialConfig (g1Point (encodeG1 r)))
        (g1BActivatedSteps r)).state.snd.mode ≠ .combineStart :=
  g1CS_activate_binary_not_result r hc ht b hb

/-- The unary route reaches the exact residual-latched install configuration
on the unchanged initial tape. -/
theorem check_g1CS_install_unary_exact (r : G1Request) (hc : r.Canonical)
    (ht : r.tag = .input ∨ r.tag = .not) :
    TM.runConfig (M := G1M) (G1M.initialConfig (g1Point (encodeG1 r)))
        (g1UActivatedSteps r + (4 * (r.tag.units + 2) + 1)) =
      g1AInstallConfig r false :=
  g1CS_install_unary_exact r hc ht

/-- The same route then reaches the residual-latched install boundary, with
operand 1 still unread. -/
theorem check_g1CS_install_binary_exact (r : G1Request) (hc : r.Canonical)
    (ht : r.tag = .and ∨ r.tag = .or) (b : Bool)
    (hb : r.vals[r.arg2]? = some b) :
    G1M.runConfig (G1M.initialConfig (g1Point (encodeG1 r)))
        (g1BActivatedSteps r + (4 * (r.tag.units + 2) + 1)) =
      g1AInstallConfig r b :=
  g1CS_install_binary_exact r hc ht b hb

/-- `const` takes the result branch and preserves `g1ResultCtx`. -/
theorem check_g1CS_activate_const_exact (r : G1Request) (hc : r.Canonical)
    (ht : r.tag = .const) (b : Bool) (hs : r.spec = some b) :
    G1M.runConfig (G1M.initialConfig (g1Point (encodeG1 r)))
        (g1ConstActivatedSteps r) = g1CombineConfig r b :=
  g1CS_activate_const_exact r hc ht b hs

/-- The full activated unary prefix fits the unchanged public clock. -/
theorem check_g1UActivatedSteps_le_clock (r : G1Request) :
    g1UActivatedSteps r + (4 * (r.tag.units + 2) + 1) ≤
      g1Clock (encodeG1 r).length :=
  g1UActivatedSteps_le_clock r

/-- The activated constant bypass fits the unchanged public clock. -/
theorem check_g1ConstActivatedSteps_le_clock (r : G1Request) :
    g1ConstActivatedSteps r ≤ g1Clock (encodeG1 r).length :=
  g1ConstActivatedSteps_le_clock r

/-- The full activated binary prefix fits the unchanged public clock. -/
theorem check_g1BActivatedSteps_le_clock (r : G1Request) :
    g1BActivatedSteps r + (4 * (r.tag.units + 2) + 1) ≤
      g1Clock (encodeG1 r).length :=
  g1BActivatedSteps_le_clock r

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
