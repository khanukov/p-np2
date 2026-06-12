import Pnp4.Frontier.ContractExpansion.TreeMCSPCorridorPushFrame
import Pnp4.Frontier.ContractExpansion.TreeMCSPTreeTagDispatch

/-!
# Corridor token dispatch — D2t-5b (Block A4a): the trie reads the next token's tag

The reading arm enters at the cursor (one right of the marker `M`) and dispatches on the next
token's 3 tag cells — `treeTagDispatch` (D2t-1) is the proven trie; this module ties its cell
hypotheses to `driverCorridorInv`'s certificate clause: the unread suffix spells
`encodePreorder (tok :: toks)`, whose first three cells are the token's tag bits
(`encodePreToken`'s prefix, per constructor).

`corridor_dispatch_node`: for a node token, the trie run from the cursor reaches that tag's accept
phase with the head on the token's **last** tag cell + 1 … i.e. advanced by 3, tape unchanged — the
hand-off into `eraseLeftMark 3` (which plants the new marker on the last consumed cell, one left of
the post-trie head).

**Progress classification (AGENTS.md): Infrastructure** — verifier machine run-throughs; build no
verifier and prove no separation.  Standard `[propext, Classical.choice, Quot.sound]` triple only.
**No `P ≠ NP` claim.**
-/

namespace Pnp4
namespace Frontier
namespace ContractExpansion

open Pnp3.Internal.PsubsetPpoly Pnp3.Internal.PsubsetPpoly.TM
open Pnp3.Internal.PsubsetPpoly.TM.ConstStatePhasedProgram
open Pnp3.Internal.PsubsetPpoly.TM.Encoding

/-- A spelled window pins any in-range cell to the spelled bit (`getD` form). -/
theorem windowSpells_cell {L : Nat} (tape : Fin L → Bool) (base : Nat) (bits : List Bool)
    (h : windowSpells tape base bits) (i : Nat) (hi : i < bits.length) :
    ∀ p : Fin L, (p : Nat) = base + i → tape p = bits.getD i false := by
  intro p hp
  obtain ⟨hfit, hcells⟩ := h
  rw [hcells p (by omega) (by omega)]
  congr 1
  omega

/-- **The corridor node dispatch** (`tnot` shown; `tand`/`tor` are the sibling lemmas).  With the
invariant for a state whose next token is `node ITag.tnot`, the trie run from the cursor reaches the
`not` accept phase (`8`), head advanced by 3, tape unchanged. -/
theorem corridor_dispatch_tnot {n L : Nat} (width : Nat) (h_width : n ≤ 2 ^ width)
    (z : DriverCorridor) (toks : List (PreToken n)) (out : List (SLGate n))
    (ctrl : List (ITag × Nat)) (val : List Nat)
    (c0 : Configuration (M := treeTagDispatch.toPhased.toTM) L)
    (hinv : driverCorridorInv width h_width z c0.tape
      (⟨PreToken.node ITag.tnot :: toks, out, ctrl, val, false⟩ : DriveState n))
    (htoks : toks ≠ [])
    (hphase : (c0.state.fst : Nat) = 0)
    (hhead : (c0.head : Nat) = z.certEnd
      - (encodePreorder width h_width (PreToken.node ITag.tnot :: toks)).length) :
    (((TM.runConfig (M := treeTagDispatch.toPhased.toTM) c0 3).state).fst : Nat) = 8
      ∧ ((TM.runConfig (M := treeTagDispatch.toPhased.toTM) c0 3).head : Nat) = (c0.head : Nat) + 3
      ∧ (TM.runConfig (M := treeTagDispatch.toPhased.toTM) c0 3).tape = c0.tape := by
  obtain ⟨hwf, hcert, hcfit, hM, hczeros, hout, hFM, hffit, hfzeros, hval, hvfit, hvzeros,
    hshw, hsfit, hszeros, hctrl, hcfit2, hvalid, hcoh⟩ := hinv
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ := hwf
  replace hcert : windowSpells c0.tape
      (z.certEnd - (encodePreorder width h_width (PreToken.node ITag.tnot :: toks)).length)
      (encodePreorder width h_width (PreToken.node ITag.tnot :: toks)) := hcert
  replace hvalid : ValidCertTokens (PreToken.node ITag.tnot :: toks) := hvalid
  -- The certificate window's first three cells are the tag bits [0,1,0].
  have hbits : encodePreorder width h_width (PreToken.node ITag.tnot :: toks)
      = [false, true, false] ++ encodePreorder width h_width toks := by
    rw [encodePreorder_cons]
    rfl
  have hlen : 3 ≤ (encodePreorder width h_width (PreToken.node ITag.tnot :: toks)).length := by
    rw [hbits]; simp
  have hfit := hcert.1
  -- The tail is nonempty (the node's child follows), giving strict room past the tag cells.
  have htail : 1 ≤ (encodePreorder width h_width toks).length := by
    have hv : ValidCertTokens toks := fun t ht => hvalid t (List.mem_cons_of_mem _ ht)
    have := validCertTokens_length_le width h_width hv
    have hne : 1 ≤ toks.length := by
      cases toks with
      | nil => exact absurd rfl htoks
      | cons a l => simp
    omega
  have henc : (encodePreorder width h_width (PreToken.node ITag.tnot :: toks)).length
      = 3 + (encodePreorder width h_width toks).length := by
    rw [hbits, List.length_append]
    rfl
  apply treeTagDispatch_runConfig_not c0 hphase (by omega)
  · intro p hp
    have := windowSpells_cell c0.tape _ _ hcert 0 (by omega) p (by omega)
    rw [this, hbits]
    rfl
  · intro p hp
    have := windowSpells_cell c0.tape _ _ hcert 1 (by omega) p (by omega)
    rw [this, hbits]
    rfl
  · intro p hp
    have := windowSpells_cell c0.tape _ _ hcert 2 (by omega) p (by omega)
    rw [this, hbits]
    rfl

/-- Sibling of `corridor_dispatch_tand` for `tand`: accept phase `9`. -/
theorem corridor_dispatch_tand {n L : Nat} (width : Nat) (h_width : n ≤ 2 ^ width)
    (z : DriverCorridor) (toks : List (PreToken n)) (out : List (SLGate n))
    (ctrl : List (ITag × Nat)) (val : List Nat)
    (c0 : Configuration (M := treeTagDispatch.toPhased.toTM) L)
    (hinv : driverCorridorInv width h_width z c0.tape
      (⟨PreToken.node ITag.tand :: toks, out, ctrl, val, false⟩ : DriveState n))
    (htoks : toks ≠ [])
    (hphase : (c0.state.fst : Nat) = 0)
    (hhead : (c0.head : Nat) = z.certEnd
      - (encodePreorder width h_width (PreToken.node ITag.tand :: toks)).length) :
    (((TM.runConfig (M := treeTagDispatch.toPhased.toTM) c0 3).state).fst : Nat) = 9
      ∧ ((TM.runConfig (M := treeTagDispatch.toPhased.toTM) c0 3).head : Nat) = (c0.head : Nat) + 3
      ∧ (TM.runConfig (M := treeTagDispatch.toPhased.toTM) c0 3).tape = c0.tape := by
  obtain ⟨hwf, hcert, hcfit, hM, hczeros, hout, hFM, hffit, hfzeros, hval, hvfit, hvzeros,
    hshw, hsfit, hszeros, hctrl, hcfit2, hvalid, hcoh⟩ := hinv
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ := hwf
  replace hcert : windowSpells c0.tape
      (z.certEnd - (encodePreorder width h_width (PreToken.node ITag.tand :: toks)).length)
      (encodePreorder width h_width (PreToken.node ITag.tand :: toks)) := hcert
  replace hvalid : ValidCertTokens (PreToken.node ITag.tand :: toks) := hvalid
  -- The certificate window's first three cells are the tag bits [0,1,0].
  have hbits : encodePreorder width h_width (PreToken.node ITag.tand :: toks)
      = [false, true, true] ++ encodePreorder width h_width toks := by
    rw [encodePreorder_cons]
    rfl
  have hlen : 3 ≤ (encodePreorder width h_width (PreToken.node ITag.tand :: toks)).length := by
    rw [hbits]; simp
  have hfit := hcert.1
  -- The tail is nonempty (the node's child follows), giving strict room past the tag cells.
  have htail : 1 ≤ (encodePreorder width h_width toks).length := by
    have hv : ValidCertTokens toks := fun t ht => hvalid t (List.mem_cons_of_mem _ ht)
    have := validCertTokens_length_le width h_width hv
    have hne : 1 ≤ toks.length := by
      cases toks with
      | nil => exact absurd rfl htoks
      | cons a l => simp
    omega
  have henc : (encodePreorder width h_width (PreToken.node ITag.tand :: toks)).length
      = 3 + (encodePreorder width h_width toks).length := by
    rw [hbits, List.length_append]
    rfl
  apply treeTagDispatch_runConfig_and c0 hphase (by omega)
  · intro p hp
    have := windowSpells_cell c0.tape _ _ hcert 0 (by omega) p (by omega)
    rw [this, hbits]
    rfl
  · intro p hp
    have := windowSpells_cell c0.tape _ _ hcert 1 (by omega) p (by omega)
    rw [this, hbits]
    rfl
  · intro p hp
    have := windowSpells_cell c0.tape _ _ hcert 2 (by omega) p (by omega)
    rw [this, hbits]
    rfl

/-- Sibling of `corridor_dispatch_tor` for `tor`: accept phase `10`. -/
theorem corridor_dispatch_tor {n L : Nat} (width : Nat) (h_width : n ≤ 2 ^ width)
    (z : DriverCorridor) (toks : List (PreToken n)) (out : List (SLGate n))
    (ctrl : List (ITag × Nat)) (val : List Nat)
    (c0 : Configuration (M := treeTagDispatch.toPhased.toTM) L)
    (hinv : driverCorridorInv width h_width z c0.tape
      (⟨PreToken.node ITag.tor :: toks, out, ctrl, val, false⟩ : DriveState n))
    (htoks : toks ≠ [])
    (hphase : (c0.state.fst : Nat) = 0)
    (hhead : (c0.head : Nat) = z.certEnd
      - (encodePreorder width h_width (PreToken.node ITag.tor :: toks)).length) :
    (((TM.runConfig (M := treeTagDispatch.toPhased.toTM) c0 3).state).fst : Nat) = 10
      ∧ ((TM.runConfig (M := treeTagDispatch.toPhased.toTM) c0 3).head : Nat) = (c0.head : Nat) + 3
      ∧ (TM.runConfig (M := treeTagDispatch.toPhased.toTM) c0 3).tape = c0.tape := by
  obtain ⟨hwf, hcert, hcfit, hM, hczeros, hout, hFM, hffit, hfzeros, hval, hvfit, hvzeros,
    hshw, hsfit, hszeros, hctrl, hcfit2, hvalid, hcoh⟩ := hinv
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ := hwf
  replace hcert : windowSpells c0.tape
      (z.certEnd - (encodePreorder width h_width (PreToken.node ITag.tor :: toks)).length)
      (encodePreorder width h_width (PreToken.node ITag.tor :: toks)) := hcert
  replace hvalid : ValidCertTokens (PreToken.node ITag.tor :: toks) := hvalid
  -- The certificate window's first three cells are the tag bits [0,1,0].
  have hbits : encodePreorder width h_width (PreToken.node ITag.tor :: toks)
      = [true, false, false] ++ encodePreorder width h_width toks := by
    rw [encodePreorder_cons]
    rfl
  have hlen : 3 ≤ (encodePreorder width h_width (PreToken.node ITag.tor :: toks)).length := by
    rw [hbits]; simp
  have hfit := hcert.1
  -- The tail is nonempty (the node's child follows), giving strict room past the tag cells.
  have htail : 1 ≤ (encodePreorder width h_width toks).length := by
    have hv : ValidCertTokens toks := fun t ht => hvalid t (List.mem_cons_of_mem _ ht)
    have := validCertTokens_length_le width h_width hv
    have hne : 1 ≤ toks.length := by
      cases toks with
      | nil => exact absurd rfl htoks
      | cons a l => simp
    omega
  have henc : (encodePreorder width h_width (PreToken.node ITag.tor :: toks)).length
      = 3 + (encodePreorder width h_width toks).length := by
    rw [hbits, List.length_append]
    rfl
  apply treeTagDispatch_runConfig_or c0 hphase (by omega)
  · intro p hp
    have := windowSpells_cell c0.tape _ _ hcert 0 (by omega) p (by omega)
    rw [this, hbits]
    rfl
  · intro p hp
    have := windowSpells_cell c0.tape _ _ hcert 1 (by omega) p (by omega)
    rw [this, hbits]
    rfl
  · intro p hp
    have := windowSpells_cell c0.tape _ _ hcert 2 (by omega) p (by omega)
    rw [this, hbits]
    rfl

end ContractExpansion
end Frontier
end Pnp4
