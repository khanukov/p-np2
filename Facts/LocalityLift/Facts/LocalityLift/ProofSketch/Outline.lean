/-!
  # Proof sketch for the locality-lift theorem

  The purpose of this blueprint is to pin down the structure of the argument
  that will eventually discharge the axiom `Facts.LocalityLift.locality_lift`.

  *Reference sources*
  * Ryan Williams, “Nonuniform ACC Circuit Lower Bounds”, JACM 61(1):4, 2014.
    Theorem 5.1 provides the deterministic locality-lift used in the magnification
    pipeline.
  * Cody Murray and Ryan Williams, “Circuit Lower Bounds for Nondeterministic
    Quasi-Polytime”, STOC 2018.  Theorem 3.2 extends the lift and confirms the
    parameter relationships adopted here.

  ## Outline

  1. **Switching lemma / shrinkage**.
     Import a multi-switching lemma for local circuits to obtain a partial
     decision tree that queries at most `polylogBudget (inputLen p)` variables
     on average.  The tree isolates a small set of coordinates to be fixed.
     - *Planned Lean landing spot:* `Proof/ShrinkageWitness.lean` will accept a
       `Restriction` whose `alive` coordinates and stability certificate supply
       the semantic shrinkage data.
     - *Current surrogate:* `ShrinkageWitness.canonical` provides a placeholder
       restriction and summary.
  2. **Extraction of the test set `T`**.
     Convert the partial decision tree into a collection of input restrictions.
     The leaves hit by the gap instances form the required test set `T`, whose
     cardinality is bounded by the polylogarithmic budget.
     - *Lean scaffolding:* `Proof/TestSetExtraction.lean` implements
       `testSetOfAlive` and proves `card_testSetOfAlive`.
  3. **Construction of the local solver**.
     For each assignment to the coordinates outside of `T`, specialise the
     original general circuit.  The switching lemma ensures that one of these
     specialisations witnesses a local solver of depth at most `general.params.depth`.
     - *Lean scaffolding:* `Proof/Blueprint.lean` packages the numeric data
       into a `LocalityWitness`.
  4. **Parameter bookkeeping**.
     The size blow-up is controlled by the number of relevant leaves in the
     decision tree; the locality equals `|T|`.  A separate arithmetic module
     will confirm the inequalities `hT`, `hM`, `hℓ`, and `hdepth`.
     - *Lean scaffolding:* `Proof/Arithmetic.lean` contains the inequalities
       used by `ShrinkageSummary.smallEnough`.
  5. **Contrapositive wrapper**.
     Once a constructive proof of `locality_lift` is in place, derive
     `no_general_solver_of_no_local` by contradiction: given a general solver,
     produce a local one and clash with the Step C lower bound.
     - *Lean scaffolding:* `Proof/Summary.lean` and `Proof/Witness.lean`
       export the current witness-building API and are the intended hook for
       the final contrapositive statement.

  Each bullet point above will eventually turn into a Lean lemma.  Keeping the
  blueprint next to the interface makes it easier to distribute the work across
  contributors.
-/
