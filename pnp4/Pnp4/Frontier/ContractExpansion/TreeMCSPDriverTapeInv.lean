import Pnp4.Frontier.ContractExpansion.TreeMCSPEncodePreorder
import Pnp4.Frontier.ContractExpansion.TreeMCSPDriveStep
import Pnp4.Frontier.ContractExpansion.TreeMCSPPushCtrlFrameRealizes
import Pnp4.Frontier.ContractExpansion.TreeMCSPGateStreamLayout
import Pnp4.Frontier.ContractExpansion.TreeMCSPNatStack
import Pnp4.Frontier.ContractExpansion.TreeMCSPCtrlFrameStack

/-!
# `driverTapeInv` — D2t-5b: the driver configuration's tape-layout invariant

The on-tape D2t-5b driver maintains its abstract state (`DriveState`: unread tokens, WORK, value/control
stacks) across four contiguous tape regions of the layout
`[ input | certificate | WORK | STACK_val | STACK_ctrl | scratch ]`.  `driverTapeInv` is the **geometric
invariant** tying a tape to a `DriveState`: each region spells the corresponding codec image.  It is the
spine the per-step body-realization lemmas (and the loop discharge) will thread.

The predicate is **machine-agnostic** — stated over a bare `tape : Fin L → Bool`, a read `cursor`, and the
region base offsets (a `DriverLayout`) — so it is well-typed *now*, before the driver TM is assembled, and
the eventual `Configuration`-level statement instantiates `tape := cfg.tape`, `cursor := cfg.head`.

* `driverTapeInv` — the region-**contents** conjunction: the certificate **from the cursor** spells
  `encodePreorder` of the unread tokens (#1604), and the WORK / value-stack / control-stack regions spell
  `encodeGateRecordStream` / `encodeNatStack` / `encodeCtrlStack` of the abstract fields.
* `DriverLayout.WellFormed` — the region **geometry**: the ordering `certBase ≤ workBase ≤ valBase ≤
  ctrlBase ≤ L`, kept separate from the contents invariant (length-aware non-overlap deferred until a
  step-realization proof needs it).
* `windowSpells_nil` — an empty region just needs its base to lie on the tape (the spine for the empty
  initial WORK/stacks).
* `driverTapeInv_init` — **the invariant holds at start**: with the certificate `encodeCircuitTree c` laid
  out and the WORK/stack regions empty, the initial driver state `⟨preorder c, [], [], [], false⟩` satisfies
  `driverTapeInv` (the certificate clause is exactly `encodePreorder_preorder`, #1604).

**Progress classification (AGENTS.md): Infrastructure** — a tape-layout invariant definition + its
initial-state lemma, proven against the verified codecs; builds no machine and proves no separation.
Standard `[propext, Classical.choice, Quot.sound]` triple only.  **No `P ≠ NP` claim.**
-/

namespace Pnp4
namespace Frontier
namespace ContractExpansion

open Pnp3.Internal.PsubsetPpoly.TM.Encoding

/-- Base offsets of the driver's four state regions on the tape (the layout
`[ input | certificate | WORK | STACK_val | STACK_ctrl | scratch ]`).  `certBase` is the certificate
region's start — the **initial** read cursor (the live cursor advances rightward as tokens are consumed;
see `driverTapeInv`). -/
structure DriverLayout where
  certBase : Nat
  workBase : Nat
  valBase : Nat
  ctrlBase : Nat

/-- **Layout well-formedness (region ordering).**  The four regions sit in order on a length-`L` tape:
`certBase ≤ workBase ≤ valBase ≤ ctrlBase ≤ L`.  This is the structural/ordering part the geometry-dependent
proofs need (and what gives `certBase` its role — the left anchor).  The *length-aware* non-overlap (each
region ends before the next begins, e.g. `workBase + (encodeGateRecordStream out).length ≤ valBase`) is
deliberately **deferred** until a step-realization proof consumes it: it depends on the still-unfixed region
capacities, and baking it in now would burden every `DriverLayout` with arithmetic obligations nothing yet
uses. -/
def DriverLayout.WellFormed (lay : DriverLayout) (L : Nat) : Prop :=
  lay.certBase ≤ lay.workBase ∧ lay.workBase ≤ lay.valBase ∧ lay.valBase ≤ lay.ctrlBase
    ∧ lay.ctrlBase ≤ L

/-- **The driver's tape-layout invariant** (region *contents*).  Relative to the region offsets `lay` and
the **dynamic** certificate read `cursor`, the tape spells the `DriveState` `st`: the certificate *from the
cursor* spells `encodePreorder` of the unread tokens, and the WORK / value-stack / control-stack regions
spell the codec images of `st.out` / `st.val` / `st.ctrl`.  The certificate clause is anchored at the live
`cursor` (which advances as tokens are read), **not** `lay.certBase` — `certBase` is the *initial* cursor
(`driverTapeInv_init` sets `cursor := lay.certBase`) and the left end of `DriverLayout.WellFormed`'s
ordering.  This predicate constrains region *contents* only; region *geometry* (ordering/bounds) is the
separate `DriverLayout.WellFormed`, kept apart so content-only lemmas carry no spacing obligations.  (The
`settling` flag and the head/cursor coupling live in the later machine layer.) -/
def driverTapeInv {n L : Nat} (width : Nat) (h_width : n ≤ 2 ^ width)
    (lay : DriverLayout) (tape : Fin L → Bool) (cursor : Nat) (st : DriveState n) : Prop :=
  windowSpells tape cursor (encodePreorder width h_width st.toks)
  ∧ windowSpells tape lay.workBase (encodeGateRecordStream st.out)
  ∧ windowSpells tape lay.valBase (encodeNatStack st.val)
  ∧ windowSpells tape lay.ctrlBase (encodeCtrlStack st.ctrl)

/-- An **empty region** spells `[]` exactly when its base lies on the tape — the window is vacuous. -/
theorem windowSpells_nil {L : Nat} (tape : Fin L → Bool) (base : Nat) (h : base ≤ L) :
    windowSpells tape base [] := by
  refine ⟨by simpa using h, fun q hlo hhi => ?_⟩
  simp only [List.length_nil, Nat.add_zero] at hhi
  omega

/-- **The tape invariant holds at the start.**  Given the layout is well-formed (`lay.WellFormed L`, which
bounds every region base by `L`) and the certificate `encodeCircuitTree c` is laid out at `lay.certBase`,
the initial driver state `⟨preorder c, [], [], [], false⟩` satisfies `driverTapeInv` with the cursor at
`lay.certBase`.  The certificate clause is `encodePreorder_preorder` (#1604: `encodePreorder (preorder c)
= encodeCircuitTree c`); the WORK / value / control clauses are `windowSpells_nil` (empty regions, their
bases on the tape by well-formedness). -/
theorem driverTapeInv_init {n L : Nat} (width : Nat) (h_width : n ≤ 2 ^ width)
    (lay : DriverLayout) (tape : Fin L → Bool) (c : CircuitTree n)
    (hwf : lay.WellFormed L)
    (hcert : windowSpells tape lay.certBase (encodeCircuitTree width h_width c)) :
    driverTapeInv width h_width lay tape lay.certBase
      (⟨preorder c, [], [], [], false⟩ : DriveState n) := by
  obtain ⟨_, hwv, hvc, hcL⟩ := hwf
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [encodePreorder_preorder]; exact hcert
  · simpa [encodeGateRecordStream] using windowSpells_nil tape lay.workBase (by omega)
  · simpa [encodeNatStack] using windowSpells_nil tape lay.valBase (by omega)
  · simpa [encodeCtrlStack] using windowSpells_nil tape lay.ctrlBase (by omega)

end ContractExpansion
end Frontier
end Pnp4
