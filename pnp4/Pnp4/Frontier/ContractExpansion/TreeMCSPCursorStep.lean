import Pnp4.Frontier.ContractExpansion.TreeMCSPDriverCorridor

/-!
# `cursorStepTape` — D2t-5b (Block A4a): consuming a certificate token, re-anchored

Every reading arm (`node`, `const`, `input`) advances the cursor the same way: consume the `tlen`-cell
token, zero its cells and the old marker, plant the new marker on the token's last cell.
`cursorStepTape tape cur tlen` is that transformer, and `cursorStepTape_cert` re-establishes the four
**certificate-region** clauses of `driverCorridorInv` for the consumed token list `toks'` — the shared
spine the three leaf/settle keystones reuse (the output / value / control regions are handled by their
own transformers, disjoint from the cursor area).

**Progress classification (AGENTS.md): Infrastructure** — a pure tape-window re-anchoring lemma for
the verified certificate codec; builds no machine and proves no separation.  Standard `[propext,
Classical.choice, Quot.sound]` triple only.  **No `P ≠ NP` claim.**
-/

namespace Pnp4
namespace Frontier
namespace ContractExpansion

open Pnp3.Internal.PsubsetPpoly.TM.Encoding

/-- A window's spelling depends only on the cells it covers: if `f` and `g` agree on `[base, base +
|bits|)` and `g` spells `bits` there, so does `f`. -/
theorem windowSpells_congr {L : Nat} (f g : Fin L → Bool) (base : Nat) (bits : List Bool)
    (hg : windowSpells g base bits)
    (hfg : ∀ q : Fin L, base ≤ (q : Nat) → (q : Nat) < base + bits.length → f q = g q) :
    windowSpells f base bits := by
  obtain ⟨hfit, hc⟩ := hg
  exact ⟨hfit, fun q hlo hhi => by rw [hfg q hlo hhi]; exact hc q hlo hhi⟩

/-- The cursor-area marker update for a `tlen`-cell token (`tlen ≥ 1`): plant the new marker on the
token's last cell (`cur + tlen − 1`), zero the old marker and the token's preceding cells
(`[cur − 1, cur + tlen − 1)`). -/
def cursorStepTape {L : Nat} (tape : Fin L → Bool) (cur tlen : Nat) (q : Fin L) : Bool :=
  if (q : Nat) = cur + tlen - 1 then true
  else if cur - 1 ≤ (q : Nat) ∧ (q : Nat) < cur + tlen - 1 then false
  else tape q

/-- The cursor update is the identity off `[cur − 1, cur + tlen − 1]`. -/
theorem cursorStepTape_off {L : Nat} (tape : Fin L → Bool) (cur tlen : Nat) (q : Fin L)
    (h1 : (q : Nat) ≠ cur + tlen - 1) (h2 : ¬ (cur - 1 ≤ (q : Nat) ∧ (q : Nat) < cur + tlen - 1)) :
    cursorStepTape tape cur tlen q = tape q := by
  unfold cursorStepTape
  rw [if_neg h1, if_neg h2]

/-- **The cursor re-anchoring keystone.**  Consuming a `tlen`-cell token (`1 ≤ tlen`) whose tape image
is the certificate's leading `tlen` cells, with `tail` nonempty (`1 ≤ |encodePreorder toks'|`) and the
cursor area sitting strictly right of the corridor's content end `cbound`, the `cursorStepTape`
re-establishes the four certificate-region clauses for `toks'`:

* the unread suffix `encodePreorder toks'` now spells the window ending at `certEnd`, anchored at the
  advanced cursor `cur + tlen` (`= certEnd − |encodePreorder toks'|`);
* the certificate fit;
* the new marker at `(cur + tlen) − 1`;
* the consumed/dead corridor `[cbound, (cur + tlen) − 1)` is all `0`.

Here `cur = certEnd − |encodePreorder (tok :: toks')|` and the token image has length `tlen`
(`encodePreorder (tok :: toks') = tagImage ++ encodePreorder toks'`, `|tagImage| = tlen`). -/
theorem cursorStepTape_cert {n L : Nat} (width : Nat) (h_width : n ≤ 2 ^ width)
    (tape : Fin L → Bool) (certEnd cbound tlen : Nat) (tok : PreToken n) (toks' : List (PreToken n))
    (htlen : (encodePreToken width h_width tok).length = tlen) (htpos : 1 ≤ tlen)
    (hsep : cbound < certEnd - (encodePreorder width h_width (tok :: toks')).length - 1)
    (hcwin : windowSpells tape (certEnd - (encodePreorder width h_width (tok :: toks')).length)
      (encodePreorder width h_width (tok :: toks')))
    (hcfit : 0 + (encodePreorder width h_width (tok :: toks')).length ≤ certEnd)
    (hcorr : ∀ q : Fin L, cbound ≤ (q : Nat) →
      (q : Nat) < certEnd - (encodePreorder width h_width (tok :: toks')).length - 1 →
      tape q = false) :
    let cur := certEnd - (encodePreorder width h_width (tok :: toks')).length
    windowSpells (cursorStepTape tape cur tlen) (cur + tlen)
        (encodePreorder width h_width toks')
    ∧ (encodePreorder width h_width toks').length ≤ certEnd - (cur + tlen) + (cur + tlen)
    ∧ (∀ q : Fin L, (q : Nat) = (cur + tlen) - 1 → cursorStepTape tape cur tlen q = true)
    ∧ (∀ q : Fin L, cbound ≤ (q : Nat) → (q : Nat) < (cur + tlen) - 1 →
        cursorStepTape tape cur tlen q = false) := by
  intro cur
  -- Length bookkeeping.
  have hbits : encodePreorder width h_width (tok :: toks')
      = encodePreToken width h_width tok ++ encodePreorder width h_width toks' :=
    encodePreorder_cons width h_width _ _
  have hlenc : (encodePreorder width h_width (tok :: toks')).length
      = tlen + (encodePreorder width h_width toks').length := by
    rw [hbits, List.length_append, htlen]
  have hcurB : cur + tlen = certEnd - (encodePreorder width h_width toks').length := by
    show certEnd - (encodePreorder width h_width (tok :: toks')).length + tlen = _
    omega
  refine ⟨?_, ?_, ?_, ?_⟩
  -- 1. The suffix window at the advanced cursor.
  · have hsuf := windowSpells_append_right tape cur _ _ (by rw [← hbits]; exact hcwin)
    rw [htlen] at hsuf
    refine windowSpells_congr _ tape (cur + tlen) _ hsuf (fun q hlo hhi => ?_)
    apply cursorStepTape_off
    · omega
    · -- q ≥ cur + tlen > cur + tlen - 1, so not in the zeroed band
      have := hsuf.1; omega
  -- 2. The fit.
  · omega
  -- 3. The new marker.
  · intro q hq
    unfold cursorStepTape
    rw [if_pos (by omega)]
  -- 4. The consumed/dead corridor.
  · intro q hlo hhi
    unfold cursorStepTape
    rw [if_neg (by omega)]
    by_cases hband : cur - 1 ≤ (q : Nat) ∧ (q : Nat) < cur + tlen - 1
    · rw [if_pos hband]
    · rw [if_neg hband]
      -- q is left of the old marker `cur - 1`: it was a corridor `0`.
      exact hcorr q hlo (by omega)

end ContractExpansion
end Frontier
end Pnp4
