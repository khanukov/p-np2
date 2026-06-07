import Complexity.TMVerifier.TuringToolkit.Encoding
import Mathlib.Tactic.Ring

/-!
# `counterValue` ↔ `decodeFin` bridge (NP-verifier track — D2t-3 `ζ`)

The pure-spec identity closing `ζ`: the on-tape little-endian counter value `counterValue` agrees with the
formal decoder `Encoding.decodeFin`.  `tapeBits` reads the width-`w` window as a little-endian bit list,
and `decodeFin_tapeBits` shows `decodeFin w (tapeBits …) = some ⟨counterValue …, _⟩` — i.e.
`counterValue = (decodeFin w …).val`.  `counterValue_lsb_shift` is the supporting little-endian shift
(`value (w+1) = lowbit + 2 · value w` on the shifted window).

Combined with `binToUnaryLoopFullScan_reachesSink_output` (`|U| = u₀ + counterValue B`), this gives the
`ζ` bridge `|U| = value(B) = (decodeFin w …).val`.  Pure `BinaryCounter`/`Encoding` arithmetic — no
machine/run content.

**Progress classification (AGENTS.md): Infrastructure.**  Standard `[propext, Classical.choice,
Quot.sound]` triple only.  **No `P ≠ NP` claim.**
-/

namespace Pnp3
namespace Internal
namespace PsubsetPpoly
namespace TM
namespace BinaryCounter

open Pnp3.Internal.PsubsetPpoly Pnp3.Internal.PsubsetPpoly.TM Pnp3.Internal.PsubsetPpoly.TM.Encoding

/-- Little-endian LSB-shift for `counterValue`: the value of the width-`w+1` window at `start` is the low
bit at `start` plus twice the value of the width-`w` window at `start+1`. -/
theorem counterValue_lsb_shift {M : TM.{u}} {n : Nat}
    (c : Configuration (M := M) n) (start : Nat) :
    ∀ w, counterValue c start (w + 1)
      = (if h : start < M.tapeLength n then (if c.tape ⟨start, h⟩ then 1 else 0) else 0)
        + 2 * counterValue c (start + 1) w := by
  intro w
  induction w with
  | zero =>
      rw [counterValue_succ, counterValue_zero, counterValue_zero]
      simp only [Nat.add_zero, pow_zero, Nat.mul_zero, Nat.zero_add]
  | succ w ih =>
      rw [counterValue_succ, ih, counterValue_succ]
      have hfe : start + 1 + w = start + (w + 1) := by omega
      rw [hfe]
      by_cases hd : start + (w + 1) < M.tapeLength n
      · rw [dif_pos hd, dif_pos hd, pow_succ]; split_ifs <;> ring
      · rw [dif_neg hd, dif_neg hd]; ring

/-- Tape bit list (little-endian, LSB first): the width-`w` window at `start`. -/
def tapeBits {M : TM.{u}} {n : Nat} (c : Configuration (M := M) n) (start : Nat) : Nat → List Bool
  | 0 => []
  | w + 1 => (if h : start < M.tapeLength n then c.tape ⟨start, h⟩ else false) :: tapeBits c (start + 1) w

set_option linter.unusedSimpArgs false in
/-- **ζ decode bridge.**  Decoding the tape's width-`w` window (as a little-endian bit list) recovers the
counter value: `decodeFin w (tapeBits …) = some ⟨counterValue …, _⟩`, i.e. `counterValue` agrees with the
formal `Encoding.decodeFin`. -/
theorem decodeFin_tapeBits {M : TM.{u}} {n : Nat}
    (c : Configuration (M := M) n) (start : Nat) :
    ∀ w, (h : counterValue c start w < 2 ^ w) →
      decodeFin w (tapeBits c start w) = some ⟨counterValue c start w, h⟩ := by
  intro w
  induction w generalizing start with
  | zero => intro h; simp [tapeBits, decodeFin, counterValue_zero]
  | succ w ih =>
      intro h
      have hcvw : counterValue c (start + 1) w < 2 ^ w := counterValue_lt_two_pow c (start + 1) w
      rw [tapeBits, decodeFin, ih (start + 1) hcvw]
      apply Option.some_inj.mpr
      apply Fin.ext
      simp only [Fin.val_mk]
      rw [counterValue_lsb_shift c start w]
      by_cases hd : start < M.tapeLength n
      · rw [dif_pos hd, dif_pos hd]
      · rw [dif_neg hd, dif_neg hd]; simp

end BinaryCounter
end TM
end PsubsetPpoly
end Internal
end Pnp3
