import PCoP.Complement
import PCoP.Parity

/-!
# Final statements and axiom audit

The two headline theorems, restated at top level so that an auditor can
check them (and their axiom footprint) in one place:

* `PCoP.P_closed_under_complement : ∀ L, P L → P L.complement`
* `PCoP.P_eq_coP : ∀ L, P L ↔ P L.complement`

Both are *unconditional*: no axiom declarations, no unfinished proofs,
no hypotheses beyond the definitions in this library.  The
`#print axioms` commands below make
the kernel report the exact axiom footprint; the expected output is a
subset of Lean's three standard axioms (`propext`, `Classical.choice`,
`Quot.sound`).

To re-verify from scratch:

```
cd pcop
lake build        # elaborates and kernel-checks every proof
```
-/

namespace PCoP

/-- Sanity restatement with the complement spelled out literally, so that
no auxiliary definition sits between the reader and the claim: if `L` is
in `P`, then so is the language `fun n x => !(L n x)`. -/
theorem P_closed_under_complement_explicit (L : Language) (hL : P L) :
    P (fun n x => !(L n x)) :=
  P_closed_under_complement L hL

end PCoP

/--
info: 'PCoP.P_closed_under_complement' depends on axioms: [propext]
-/
#guard_msgs in #print axioms PCoP.P_closed_under_complement

/--
info: 'PCoP.P_closed_under_complement_explicit' depends on axioms: [propext]
-/
#guard_msgs in #print axioms PCoP.P_closed_under_complement_explicit

/--
info: 'PCoP.P_eq_coP' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in #print axioms PCoP.P_eq_coP

/--
info: 'PCoP.parity_in_P' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in #print axioms PCoP.parity_in_P

/--
info: 'PCoP.parity_complement_in_P' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in #print axioms PCoP.parity_complement_in_P

/--
info: 'PCoP.const_in_P' depends on axioms: [propext]
-/
#guard_msgs in #print axioms PCoP.const_in_P
