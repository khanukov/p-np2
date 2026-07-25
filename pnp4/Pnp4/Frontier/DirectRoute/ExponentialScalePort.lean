import Complexity.Interfaces
import Pnp4.Frontier.DirectRoute.ScaleDichotomy

/-!
# The exponential-scale port: `EXP ≠ NEXP → P ≠ NP`

## Why this port exists

`ScaleDichotomy.lean` isolates the whole difficulty of the direct route in one
parameter: the exponent `c` of the assumed `SAT` algorithm.  When `c = 1` the
assumption is free and any positive gain refutes it; when `c` is unbounded no
fixed gain ever does (`fixed_gain_insufficient`).

There are two ways to reach `c = 1`, and only one is available.

*Bootstrapping `c` downwards* is not available: padding enlarges instances, so it
moves the exponent the wrong way, and the Cook–Levin route is circular.

*Raising the ambient scale* is available and is what the successful literature
actually does.  At ambient resource `2^(n^a)`, one invocation of the assumed
polynomial-time algorithm costs `poly(n)`, which is sub-polynomial in the
resource — the effective `c` is `1`.  This is exactly why Williams' algorithmic
method reaches `NEXP ⊄ ACC⁰` while nothing comparable exists at polynomial
scale, and it is the same reason Paul–Pippenger–Szemerédi–Trotter succeeds at
`c = 1` and stops.

This module records the resulting target.

## The trade, stated honestly

```text
EXP ≠ NEXP   ⟹   P ≠ NP        (padding)
```

but no converse is known.  So this port asks for something **stronger** than
`P ≠ NP` — the opposite trade from Mainline A, which also asked for something
stronger (`NP ⊄ P/poly`) but got nothing in return.  Here the compensation is
concrete and named: at exponential scale the assumption stops multiplying, which
is the single property `ScaleDichotomy` shows every successful direct separation
has.

Whether that compensation is worth the extra strength is a research judgement,
not a theorem.  What is a theorem is the bridge below, and what is documented is
the reason to consider it at all.

## Status

* `EXP`, `NEXP` are defined here in the repository's own Turing-machine model,
  mirroring `polyTimeDecider` and `NP_TM` exactly.
* `PaddingTranslation` is an **external published contract** (`P = NP ⟹
  EXP = NEXP`, the standard padding argument).  It is not proved here; proving
  it means building the padded machine and bounding its runtime in the internal
  TM model, which is a substantial independent development.
* The bridge from the contract to `P ≠ NP` is proved.

Nothing here proves `P ≠ NP` or `EXP ≠ NEXP`.
-/

namespace Pnp4
namespace Frontier
namespace DirectRoute

open Pnp3.ComplexityInterfaces

/-- The Turing-machine model used by the repository's `P` and `NP`. -/
abbrev BaseTM := Pnp3.Internal.PsubsetPpoly.TM.{0}

/-!
### Exponential time
-/

/--
Deterministic exponential time: a machine deciding `L` within
`2 ^ (n ^ c + c) + c` steps.

This mirrors `Internal.PsubsetPpoly.Complexity.polyTimeDecider` with the
polynomial bound `n ^ c + c` replaced by its exponential analogue.
-/
def expTimeDecider (L : Language) : Prop :=
  ∃ (M : BaseTM) (c : Nat),
    (∀ n, M.runTime n ≤ 2 ^ (n ^ c + c) + c) ∧
    (∀ n (x : Bitstring n),
      Pnp3.Internal.PsubsetPpoly.TM.accepts (M := M) (n := n) x = L n x)

/-- The class `EXP`. -/
def EXP (L : Language) : Prop := expTimeDecider L

/-- Certificate length at exponential scale. -/
def expCertificateLength (n k : Nat) : Nat := 2 ^ (n ^ k + k)

/--
Nondeterministic exponential time, in verifier form.

This mirrors `ComplexityInterfaces.NP_TM` with both the certificate length and
the runtime bound replaced by their exponential analogues.
-/
def NEXP (L : Language) : Prop :=
  ∃ (M : BaseTM) (c k : Nat),
    (∀ n,
      M.runTime (n + expCertificateLength n k) ≤
        2 ^ ((n + expCertificateLength n k) ^ c + c) + c) ∧
    (∀ n (x : Bitstring n),
      L n x = true ↔
        ∃ w : Bitstring (expCertificateLength n k),
          Pnp3.Internal.PsubsetPpoly.TM.accepts
              (M := M)
              (n := n + expCertificateLength n k)
              (concatBitstring x w) = true)

/-- The exponential-scale separation target. -/
def EXP_ne_NEXP : Prop := EXP ≠ NEXP

/-!
### The published contract and the bridge
-/

/--
**Published contract: upward translation by padding.**

If `P = NP` then `EXP = NEXP`.  This is the standard padding argument: a
`NEXP` machine on input `x` becomes an `NP` machine on `x` padded to the length
of its own running time, and a polynomial-time decider for the padded language
yields an exponential-time decider for the original.

It is recorded here as an external input, in the same style as
`MMWStreamingMagnification`.  Formalizing it means constructing the padded
machine inside `Pnp3.Internal.PsubsetPpoly.TM` and bounding its runtime, which
is a substantial independent development.
-/
structure PaddingTranslation where
  /-- The padding argument. -/
  collapse : Pnp3.ComplexityInterfaces.P = Pnp3.ComplexityInterfaces.NP →
    EXP = NEXP

/--
**The exponential-scale port.**

A separation at exponential scale yields `P ≠ NP`.  This is the machine-checked
contrapositive of the padding contract.
-/
theorem P_ne_NP_of_EXP_ne_NEXP (C : PaddingTranslation) (h : EXP_ne_NEXP) :
    Pnp3.ComplexityInterfaces.P_ne_NP := by
  intro hCollapse
  exact h (C.collapse hCollapse)

/-- Closure witness for the exponential-scale route. -/
structure ExponentialScaleWitness where
  /-- The padding contract. -/
  contract : PaddingTranslation
  /-- The separation at exponential scale: the whole mathematical content. -/
  separation : EXP_ne_NEXP

/-- Final consequence of a discharged exponential-scale witness. -/
theorem P_ne_NP_of_exponentialScaleWitness (w : ExponentialScaleWitness) :
    Pnp3.ComplexityInterfaces.P_ne_NP :=
  P_ne_NP_of_EXP_ne_NEXP w.contract w.separation

/-!
### Why this scale, formally

The link back to `ScaleDichotomy` is the following reading, which the calculus
makes precise rather than proves about Turing machines:

* at polynomial scale the assumption contributes the factor `c` to every cycle,
  and `fixed_gain_insufficient` applies;
* at exponential scale the same assumption contributes `poly(n)` to a resource
  of size `2^(n^a)`, i.e. a factor of `1` at the level of resource exponents,
  which is the hypothesis `CostFree` of `refutes_of_costFree`.

So the port is not a change of subject.  It is the *only* currently reachable
instance of the condition under which the direct method has ever worked.
-/

/-- The cost regime this port targets: the assumption is free. -/
theorem exponentialScale_is_costFree : CostFree 1 := rfl

/-- At that regime, any positive gain refutes the assumption. -/
theorem exponentialScale_any_gain_refutes {k : Nat} {δ α : ℚ}
    (hδ : 0 < δ) (hα : 0 < α) :
    ∃ β : ℚ, β < α ∧ Derives 1 k δ (Resource.dtime α) (Resource.dtime β) :=
  refutes_of_costFree exponentialScale_is_costFree hδ hα

end DirectRoute
end Frontier
end Pnp4
