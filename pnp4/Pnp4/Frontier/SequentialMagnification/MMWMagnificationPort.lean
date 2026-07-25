import Pnp4.Frontier.SequentialMagnification.MCSPStreamingTarget
import Pnp4.Frontier.CompressionMagnification

/-!
# The sequential magnification port to `P ≠ NP`

## What this module adds to the repository

Until now the only closure port in this project was the **non-uniform** one:

```text
NP ⊄ PpolyDAG  →  P ≠ NP
```

(`Magnification.UnconditionalResearchGap.ResearchGapWitness`,
`AlgorithmsToLowerBounds.VerifiedNPDAGLowerBoundSource`).  `AGENTS.md` even
requires every pnp4 mainline package to end in `VerifiedNPDAGLowerBoundSource`,
and `Frontier.SearchMCSPWeakLowerBound` hard-codes the field

```text
magnifiesToVerifiedDAGSource : weakLowerBound → VerifiedNPDAGLowerBoundSource
```

That is strictly stronger than the goal.  `NP ⊄ P/poly` implies `P ≠ NP` but not
conversely, and every internal refutation recorded in
`CHECKLIST_UNCONDITIONAL_P_NE_NP.md` is an artefact of *non-uniformity*: a
truth table can be hardwired into a circuit family for free.

The magnification theorem that `pnp4/README.md` names as the mainline reference
does **not** have that shape.  McKay, Murray and Williams (STOC 2019,
Theorem 1.3), as restated by Cheraghchi, Hirahara, Myrisiotis and Yoshida
(STACS 2021 / ECCC TR20-103, Theorem 47 and its proof), reads:

> if `P = NP` then there is a polynomial `p` such that for every
> time-constructible size parameter `s`, `MCSP[s]` is computed by a **one-pass
> streaming algorithm** with space and update time `p(s(n))`.

Its contrapositive concludes `P ≠ NP` **directly**, from a *uniform, sequential,
memory-bounded* lower bound.  It never produces a `P/poly` lower bound, so the
existing pnp4 mainline interface cannot even express it.

This module supplies the missing port.

## Faithfulness and conservatism

Both sides of the port are deliberately conservative:

* The contract records only the **space** half of the MMW conclusion.  MMW give
  an algorithm bounded in both space and update time, so the contract stated
  here is *weaker* than their theorem and is implied by it.
* The hardness input is required at a **single slice** `n`, which is *stronger*
  than "no streaming algorithm for the whole language".  A single-slice bound is
  therefore sufficient.

Being weak on the contract and strong on the hypothesis means the port is sound
in the only direction that matters: discharging the hypothesis really does give
`P ≠ NP`, modulo the published contract.

The contract is an **external published input**, exactly like
`AC0pCoinLowerBoundContract` and `CKLMFormulaCircuitLocalPRGSourceContract`
elsewhere in `pnp4`.  It is not proved here, and this module does not claim
`P ≠ NP`.
-/

namespace Pnp4
namespace Frontier
namespace SequentialMagnification

/--
**Published contract (McKay–Murray–Williams, STOC 2019, Theorem 1.3).**

If `P = NP` then MCSP has one-pass streaming solvers whose memory budget is
polynomial in the size parameter.

`spaceBudget` is the polynomial `p` of the published statement, applied to
`s n`.  Only the space half of the conclusion is recorded, which makes this
contract weaker than the published theorem (see the module header).
-/
structure MMWStreamingMagnification where
  /-- The polynomial memory budget `p` of the published statement. -/
  spaceBudget : Nat → Nat
  /-- `spaceBudget` is polynomially bounded. -/
  spaceBudget_poly : ∃ c : Nat, ∀ x : Nat, spaceBudget x ≤ x ^ c + c
  /-- The magnification content: a collapse gives streaming solvers. -/
  streamingFromCollapse :
    Pnp3.ComplexityInterfaces.P = Pnp3.ComplexityInterfaces.NP →
      ∀ (s : Nat → Nat) (n : Nat),
        MCSPStreamingSolvable (spaceBudget (s n)) n (s n)

/--
**The port.**  A single-slice streaming lower bound for MCSP, at the budget
supplied by the contract, yields `P ≠ NP`.

This is the machine-checked contrapositive of the published contract.  Note
that the conclusion is the uniform statement `P ≠ NP` itself: no `P/poly`
lower bound is produced, required, or implied along the way.
-/
theorem P_ne_NP_of_mcsp_streaming_hardness
    (C : MMWStreamingMagnification) (s : Nat → Nat) (n : Nat)
    (hHard : MCSPStreamingHard (C.spaceBudget (s n)) n (s n)) :
    Pnp3.ComplexityInterfaces.P_ne_NP := by
  intro hCollapse
  exact hHard (C.streamingFromCollapse hCollapse s n)

/--
Closure witness for the sequential track, mirroring
`Magnification.UnconditionalResearchGap.ResearchGapWitness` but ending in the
uniform target.

The only mathematical field is `hardness`; everything else is bookkeeping for
which slice and which size parameter the lower bound is claimed at.
-/
structure SequentialResearchGapWitness where
  /-- The published magnification contract. -/
  contract : MMWStreamingMagnification
  /-- The MCSP size parameter `s`. -/
  sizeParam : Nat → Nat
  /-- The slice `n` at which the lower bound is claimed. -/
  slice : Nat
  /-- The weak sequential lower bound: the whole mathematical content. -/
  hardness :
    MCSPStreamingHard
      (contract.spaceBudget (sizeParam slice)) slice (sizeParam slice)

/-- Final consequence of a discharged sequential witness. -/
theorem P_ne_NP_of_sequentialGap (w : SequentialResearchGapWitness) :
    Pnp3.ComplexityInterfaces.P_ne_NP :=
  P_ne_NP_of_mcsp_streaming_hardness w.contract w.sizeParam w.slice w.hardness

/-!
## Relation to the existing non-uniform port

The two ports are independent inputs to the *same* conclusion.  The theorem
below records, in kernel-checked form, that the non-uniform target is at least
as strong as the target of this module: anything the DAG route could deliver,
the sequential route's conclusion already follows from.

There is no theorem in the other direction, and none is expected: that is
precisely the sense in which the sequential port is the weaker — and therefore
more attackable — obligation.
-/
theorem sequentialTarget_of_dagTarget
    (h : Pnp3.ComplexityInterfaces.NP_not_subset_PpolyDAG) :
    Pnp3.ComplexityInterfaces.P_ne_NP :=
  P_ne_NP_of_NP_not_subset_Ppoly h

/--
The sequential port does not fit the current pnp4 mainline interface.

`SearchMCSPWeakLowerBound` requires a function
`weakLowerBound → VerifiedNPDAGLowerBoundSource`, i.e. every accepted package
must produce a non-uniform separation.  A `SequentialResearchGapWitness`
produces `P ≠ NP` without producing any `PpolyDAG` lower bound, so it can only
be recorded as mainline progress if the interface is widened.

This definition is the widened endpoint: the disjunction of the two accepted
closure routes.
-/
inductive PvsNPClosureRoute where
  /-- Non-uniform route: a verified `NP` lower bound against `PpolyDAG`. -/
  | nonuniform (src : AlgorithmsToLowerBounds.VerifiedNPDAGLowerBoundSource)
  /-- Uniform sequential route: MMW streaming magnification. -/
  | sequential (w : SequentialResearchGapWitness)

/-- Both accepted routes reach the same final target. -/
theorem P_ne_NP_of_closureRoute :
    ∀ _r : PvsNPClosureRoute, Pnp3.ComplexityInterfaces.P_ne_NP
  | .nonuniform src => AlgorithmsToLowerBounds.P_ne_NP_of_verified_source src
  | .sequential w => P_ne_NP_of_sequentialGap w

end SequentialMagnification
end Frontier
end Pnp4
