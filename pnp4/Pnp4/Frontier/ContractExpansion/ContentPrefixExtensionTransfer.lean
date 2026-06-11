import Pnp4.Frontier.ContractExpansion.ContentPrefixExtensionCoincidence
import Pnp4.Frontier.ContractExpansion.NoSolverContrapositive
import Pnp4.Frontier.ContractExpansion.ExtractedScheduleGrowth

/-!
# Decision→search extraction transfer to the content-truthful language — §13 repair, brick R4

The existing extraction consumes a `PpolyDAG` decider for the **length-gated** language and only
ever evaluates it on *constructed, parseable* queries (`prefixStateQueryValue`).  By the coincidence
lemma (brick R3) the content-truthful language `L'` agrees with the original on exactly those
queries — so a `PpolyDAG` decider for `L'` drives the *same* greedy machinery:

* `DecidesContentPrefixExtensionLanguage` — the `L'`-decider hypothesis;
* `correctNextBitDecider_of_decidesContentLanguage` — the next-bit discharge (mirror of Block 8b,
  with the coincidence rewrite at the constructed query);
* `boundedSearchSolver_of_deciderFamilyCT` — the solver assembly (mirror of Block 9);
* `boundedSearchSolver_of_PpolyDAG_contentPrefixExtension` — the forward bridge (mirror of 9b);
* `not_PpolyDAG_contentPrefixExtension_of_noExtractedScheduleSolver` /
  `not_PpolyDAG_contentPrefixExtension_of_noPolynomialBoundedSearchSolver` — the contrapositives:
  the **same** open lower-bound hypotheses now also pin `L'` outside `PpolyDAG`.

Combined with `contentPrefixExtensionLanguage_in_NP_of_witness` (brick R2), this re-routes the
conditional chain through `L'`, whose NP-witness is achievable by a length-blind machine (§13.1).

**Progress classification (AGENTS.md): Infrastructure** — specification repair for the NP-verifier
track; all lower-bound inputs remain explicit hypotheses; proves no separation.  Standard
`[propext, Classical.choice, Quot.sound]` triple only.  **No `P ≠ NP` claim.**
-/

namespace Pnp4
namespace Frontier
namespace ContractExpansion

open AlgorithmsToLowerBounds

variable {threshold : Nat → Nat}

/-- `dec` decides the **content-truthful** prefix-extension language at the convention length. -/
def DecidesContentPrefixExtensionLanguage
    (codec : TreeCircuitWitnessCodec threshold)
    (n : Nat)
    (dec : C_DAG.Family (treeMCSPPrefixM codec n)) : Prop :=
  ∀ y : PrefixBitVec (treeMCSPPrefixM codec n),
    C_DAG.eval dec y
      = ContentPrefixExtensionLanguage codec (treeMCSPPrefixM codec n) y

/-- **Next-bit discharge from an `L'`-decider** (mirror of Block 8b).  On the constructed query the
content-truthful language coincides with the length-gated one (brick R3), so an `L'`-decider is a
correct next-bit decider for the same greedy machinery. -/
theorem correctNextBitDecider_of_decidesContentLanguage
    (codec : TreeCircuitWitnessCodec threshold)
    (n : Nat)
    (dec : C_DAG.Family (treeMCSPPrefixM codec n))
    (x : PrefixBitVec (Pnp3.Models.Partial.tableLen n))
    (hdec : DecidesContentPrefixExtensionLanguage codec n dec) :
    CorrectNextBitDecider codec n x dec := by
  intro i hi p
  rw [hdec (prefixStateQueryValue codec n (i + 1) hi x (Fin.snoc p true)),
      ContentPrefixExtensionLanguage_eq_of_parse codec
        (prefixStateQueryValue codec n (i + 1) hi x (Fin.snoc p true))
        (CanonicalRawTreeMCSPPrefixFields.toPrefixInput codec
          (prefixStateFields codec n (i + 1) hi x (Fin.snoc p true)))
        (parse_prefixStateQueryValue codec n (i + 1) hi x (Fin.snoc p true)) rfl,
      PrefixExtensionLanguage_accepts_iff]
  constructor
  · rintro ⟨input, hparse, hext⟩
    have hpeq : parsePrefixInput (treeMCSPConcretePrefixParser threshold codec)
          (prefixStateQueryValue codec n (i + 1) hi x (Fin.snoc p true))
          = some (CanonicalRawTreeMCSPPrefixFields.toPrefixInput codec
              (prefixStateFields codec n (i + 1) hi x (Fin.snoc p true))) :=
      parse_prefixStateQueryValue codec n (i + 1) hi x (Fin.snoc p true)
    rw [hpeq] at hparse
    obtain rfl := Option.some.inj hparse.symm
    exact (prefixExtendableInput_iff_witnessPrefixExtendable _).mp hext
  · intro hwit
    exact ⟨_, parse_prefixStateQueryValue codec n (i + 1) hi x (Fin.snoc p true),
      (prefixExtendableInput_iff_witnessPrefixExtendable _).mpr hwit⟩

/-- **Bounded-solver assembly from an `L'`-decider family** (mirror of Block 9). -/
def boundedSearchSolver_of_deciderFamilyCT
    (codec : TreeCircuitWitnessCodec threshold)
    (dec : ∀ n, C_DAG.Family (treeMCSPPrefixM codec n))
    (decSizeBound : Nat → Nat)
    (hlang : ∀ n, DecidesContentPrefixExtensionLanguage codec n (dec n))
    (hsize : ∀ n, C_DAG.size (dec n) ≤ decSizeBound n) :
    BoundedSearchSolver (treeProblem codec) C_DAG (boundedSolverSizeBound codec decSizeBound) where
  outputCircuit := fun n i => greedyTrueOutputCircuit codec n (dec n) i
  size_le := fun n i => by
    refine le_trans (size_greedyTrueOutputCircuit_le codec n (dec n) i) ?_
    unfold boundedSolverSizeBound
    gcongr
    exact hsize n
  solves := fun n x hpromise =>
    greedyTrueOutputCircuit_solves codec n (dec n) x hpromise
      (correctNextBitDecider_of_decidesContentLanguage codec n (dec n) x (hlang n))

/-- **Forward `PpolyDAG`→solver bridge for `L'`** (mirror of Block 9b): if the content-truthful
language is in `PpolyDAG`, the same extracted solver schedule is realized. -/
theorem boundedSearchSolver_of_PpolyDAG_contentPrefixExtension
    (codec : TreeCircuitWitnessCodec threshold)
    (hPpoly : Pnp3.ComplexityInterfaces.PpolyDAG (ContentPrefixExtensionLanguage codec)) :
    ∃ c : Nat,
      Nonempty
        (BoundedSearchSolver (treeProblem codec) C_DAG
          (fun n =>
            codec.witnessBits n *
                ((treeMCSPPrefixM codec n) ^ c + c + 2 * treeMCSPPrefixM codec n)
              + 1)) := by
  obtain ⟨c, hc⟩ := PpolyDAG_decider_as_C_DAG_decider hPpoly
  have hc' : ∀ n, ∃ C : C_DAG.Family (treeMCSPPrefixM codec n),
      C_DAG.size C ≤ (treeMCSPPrefixM codec n) ^ c + c
        ∧ ∀ x, C_DAG.eval C x
            = ContentPrefixExtensionLanguage codec (treeMCSPPrefixM codec n) x :=
    fun n => hc (treeMCSPPrefixM codec n)
  choose dec hsize hlang using hc'
  exact ⟨c, ⟨boundedSearchSolver_of_deciderFamilyCT codec dec
    (fun n => (treeMCSPPrefixM codec n) ^ c + c) hlang hsize⟩⟩

/-- **Exact-schedule contrapositive for `L'`** (mirror of Block 9c). -/
theorem not_PpolyDAG_contentPrefixExtension_of_noExtractedScheduleSolver
    (codec : TreeCircuitWitnessCodec threshold)
    (hNo : NoExtractedScheduleSolver codec) :
    ¬ Pnp3.ComplexityInterfaces.PpolyDAG (ContentPrefixExtensionLanguage codec) := by
  intro hPpoly
  obtain ⟨c, hSolver⟩ := boundedSearchSolver_of_PpolyDAG_contentPrefixExtension codec hPpoly
  exact hNo c hSolver

/-- **Polynomial-target contrapositive for `L'`**: under the growth assumptions, the *same* open
no-polynomial-solver hypothesis pins the content-truthful language outside `PpolyDAG`. -/
theorem not_PpolyDAG_contentPrefixExtension_of_noPolynomialBoundedSearchSolver
    (codec : TreeCircuitWitnessCodec threshold)
    (hGrowth : TreeMCSPExtractionGrowthAssumptions codec)
    (hNoPoly : NoPolynomialBoundedSearchSolver codec) :
    ¬ Pnp3.ComplexityInterfaces.PpolyDAG (ContentPrefixExtensionLanguage codec) :=
  not_PpolyDAG_contentPrefixExtension_of_noExtractedScheduleSolver codec
    (noExtractedScheduleSolver_of_noPolynomial codec hGrowth hNoPoly)

end ContractExpansion
end Frontier
end Pnp4
