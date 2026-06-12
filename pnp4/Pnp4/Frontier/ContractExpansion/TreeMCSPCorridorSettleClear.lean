import Pnp4.Frontier.ContractExpansion.TreeMCSPCorridorDecStep

/-!
# The settle-clear keystone — D2t-5b (Block A4c): `DriveState.step`'s empty-stack settling branch

`DriveState.step`'s settling arm has three sub-branches (`TreeMCSPDriveStep`):

* **control stack empty** — the completion cascade is finished; clear the `settling` flag and resume
  reading (`⟨toks, out, [], val, true⟩ → ⟨toks, out, [], val, false⟩`);
* **top frame `rem ≥ 2`** — decrement the frame, clear the flag (`corridorInv_decStep`, Block A4b);
* **top frame `rem = 1`** — emit the gate over the value-stack operands, pop the frame, push the new
  index, stay settling (the settle-EMIT keystone, the remaining core).

This module supplies the first of those: the **empty-stack settle-clear** keystone.  It is the
cheapest branch — the cascade has fully resolved, so the on-tape machine performs **no tape write**
(only a finite-control flag flip).  Concretely the abstract state changes only its `settling` flag
`true → false` with `toks`, `out`, `ctrl = []`, and `val` all unchanged, so the tape is **literally
unchanged**.

`corridorInv_settleClearStep` therefore re-establishes `driverCorridorInv` for the stepped state with
the *same* tape: every region clause is the very hypothesis from `hinv` (the certificate, output,
value, and control windows, the dead corridors, the markers, and `ValidCertTokens` all reference
`toks`/`out`/`[]`/`val`, untouched), and the only clause that mentions `settling` — the settling
coherence `st.settling = true → st.val ≠ []` — becomes vacuous once `settling = false`.

**Progress classification (AGENTS.md): Infrastructure** — a tape-level invariant-preservation
keystone over the verified codecs; builds no machine and proves no separation.  Standard `[propext,
Classical.choice, Quot.sound]` triple only.  **No `P ≠ NP` claim.**
-/

namespace Pnp4
namespace Frontier
namespace ContractExpansion

open Pnp3.Internal.PsubsetPpoly.TM.Encoding

/-- **The settle-clear keystone.**  For a settling state with an **empty** control stack, clearing the
`settling` flag (the on-tape machine writes nothing — the cascade is done) re-establishes
`driverCorridorInv` for the stepped state `⟨toks, out, [], val, false⟩` on the *same* tape.  Every
region clause is inherited verbatim from `hinv`; the settling-coherence clause is now vacuous. -/
theorem corridorInv_settleClearStep {n L : Nat} (width : Nat) (h_width : n ≤ 2 ^ width)
    (z : DriverCorridor) (toks : List (PreToken n)) (out : List (SLGate n))
    (val : List Nat) (tape : Fin L → Bool)
    (hinv : driverCorridorInv width h_width z tape
      (⟨toks, out, [], val, true⟩ : DriveState n)) :
    driverCorridorInv width h_width z tape
      (⟨toks, out, [], val, false⟩ : DriveState n) := by
  obtain ⟨hwf, hcert, hcfit, hmark, hcorr, hout, hofit, hFM, hffit, hfzeros, hval, hvfit, hvzeros,
    hshw, hsfit, hszeros, hctrl, hcfit2, hvalid, _hcoh⟩ := hinv
  dsimp only [driverCorridorInv]
  refine ⟨hwf, hcert, hcfit, hmark, hcorr, hout, hofit, hFM, hffit, hfzeros, hval, hvfit, hvzeros,
    hshw, hsfit, hszeros, hctrl, hcfit2, hvalid, ?_⟩
  intro hs; cases hs

end ContractExpansion
end Frontier
end Pnp4
