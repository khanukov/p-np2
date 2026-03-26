import Complexity.Promise
import Counting.ShannonCounting

namespace Pnp3
namespace LowerBounds

open Core
open Complexity
open Models

/--
Generic accepted-family certificate on one fixed Gap-PartialMCSP slice.

This is the intended weak final consumer shape for the nonuniform DAG route:
it speaks only about a finite family of total truth tables whose accepted size
already exceeds the counting capacity of all circuits of size `≤ sNO - 1`.
-/
structure AcceptedFamilyCertificate
    {p : GapPartialMCSPParams}
    (f : Core.BitVec (partialInputLen p) → Bool) : Type where
  family : Finset (Core.BitVec (Partial.tableLen p.n))
  hLarge :
    Models.circuitCountBound p.n (p.sNO - 1) < family.card
  hAccept :
    ∀ g : Core.BitVec (Partial.tableLen p.n),
      g ∈ family →
        f (encodeTotalAsPartial g) = true

/--
Generic accepted-family contradiction theorem.

If a solver for `GapPartialMCSPPromise p` accepts more total truth tables than
all functions computable by circuits of size `≤ sNO - 1`, one accepted member
must be a NO-instance, contradicting correctness.
-/
theorem no_function_solves_mcsp_of_acceptedFamilyCertificate
    {p : GapPartialMCSPParams}
    (f : Core.BitVec (partialInputLen p) → Bool)
    (cert : AcceptedFamilyCertificate f)
    (hCorrect : SolvesPromise (GapPartialMCSPPromise p) f) :
    False := by
  obtain ⟨g, hgMem, hgNo⟩ :=
    Counting.exists_hard_function_of_large_family p cert.family cert.hLarge
  have hAccepts : f (encodeTotalAsPartial g) = true :=
    cert.hAccept g hgMem
  have hNoInput : encodeTotalAsPartial g ∈ (GapPartialMCSPPromise p).No := by
    apply gapPartialMCSP_no_of_large
    simpa [decodePartial_encodeTotal] using hgNo
  have hRejects : f (encodeTotalAsPartial g) = false :=
    hCorrect.2 _ hNoInput
  exact Bool.false_ne_true (hRejects.symm.trans hAccepts)

end LowerBounds
end Pnp3
