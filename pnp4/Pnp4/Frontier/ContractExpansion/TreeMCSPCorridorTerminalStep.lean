import Pnp4.Frontier.ContractExpansion.TreeMCSPCorridorPopStep

/-!
# The terminal no-op keystone — D2t-5b (Block A4f): `DriveState.step`'s terminal branch on tape

The reading arm with an **empty token stream** (`toks = []`, `settling = false`) is the driver's
terminal/idle state: `DriveState.step` fixes it (`DriveState.step_terminal`), so the tape is literally
unchanged and `driverCorridorInv` transports verbatim.  This is the seventh and last per-branch
keystone, completing Block A4: every branch of `DriveState.step` now has a tape-level
invariant-preservation keystone, so the on-tape `driverBody` (Block A5) can be assembled from them.

The companion trivial keystone — settling with an empty control stack (clear the flag, also no tape
change) — is `corridorInv_settleClearStep` (`TreeMCSPCorridorSettleClear.lean`).

**Progress classification (AGENTS.md): Infrastructure** — a tape-level invariant-preservation
keystone over the verified codecs; builds no machine and proves no separation.  Standard `[propext,
Classical.choice, Quot.sound]` triple only.  **No `P ≠ NP` claim.**
-/

namespace Pnp4
namespace Frontier
namespace ContractExpansion

open Pnp3.Internal.PsubsetPpoly.TM.Encoding

/-- **The terminal no-op keystone.**  At a terminal reading state (`toks = []`, not settling),
`DriveState.step` is the identity, so `driverCorridorInv` holds for the stepped state with the same
tape. -/
theorem corridorInv_terminalStep {n L : Nat} (width : Nat) (h_width : n ≤ 2 ^ width)
    (z : DriverCorridor) (out : List (SLGate n)) (ctrl : List (ITag × Nat)) (val : List Nat)
    (tape : Fin L → Bool)
    (hinv : driverCorridorInv width h_width z tape
      (⟨[], out, ctrl, val, false⟩ : DriveState n)) :
    driverCorridorInv width h_width z tape
      ((⟨[], out, ctrl, val, false⟩ : DriveState n).step) := by
  rw [DriveState.step_terminal _ ⟨rfl, rfl⟩]
  exact hinv

end ContractExpansion
end Frontier
end Pnp4
