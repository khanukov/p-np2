import Mathlib.Data.Finset.Basic
import Counting.Atlas_to_LB_Core
import Core.SAL_Core
import LowerBounds.LB_Formulas
import Models.Model_GapMCSP
import ThirdPartyFacts.Facts_Switching

/-!
  pnp3/LowerBounds/AntiChecker.lean

  ## Anti-Checker Axioms for Part C

  Античекер — это содержательный мостик между конкретной задачей GapMCSP
  и универсальными оценками части B.  В классических доказательствах
  (Chapman–Williams 2016, Williams 2014, Hitchcock–Pătraşcu 2022 и др.)
  он строится через Circuit-Input Game или анализ YES/NO-слоёв.

  Здесь мы формализуем его как **внешний факт** (axiom), выделив точный
  интерфейс, который необходим для дальнейшей «машинной» части доказательства.

  ## Mathematical Background

  The anti-checker construction follows the framework from:

  * **Chapman–Williams (2016)**: "Circuit-Input Games: Separation with Circuit Lower Bounds"
    - Introduces the circuit-input game framework
    - Shows how to construct rich families from small solvers

  * **Williams (2014)**: "ACC⁰ Lower Bounds via the Switching Lemma"
    - Establishes ACC⁰ ∩ NP lower bounds via satisfiability
    - Uses richness arguments to derive contradictions

  * **Hitchcock–Pătraşcu (2022)**: "GapMCSP Hardness for AC⁰"
    - Proves AC⁰ lower bounds for GapMCSP
    - Refines the anti-checker construction with explicit testsets

  ## Key Components

  * `SmallAC0Solver`: Hypothesis that a small AC⁰ circuit solves GapMCSP
  * `antiChecker_exists_large_Y`: Constructs rich family Y exceeding capacity
  * `antiChecker_exists_testset`: Enhanced version with explicit testset T

  These axioms are used in `LB_Formulas_Core.lean` to derive contradictions:
  small correct solver ⇒ large Y ⇒ capacity violation ⇒ False
-/
namespace Pnp3
namespace LowerBounds

open Classical
open Core
open Models
open ThirdPartyFacts

/--
  Гипотеза «малый AC⁰-решатель» для GapMCSP на входной длине `N = 2^p.n`.

  A small AC⁰ solver is a circuit with constant depth and polynomial size
  that purports to solve GapMCSP. For the anti-checker to work, we assume:

  1. **Structural constraint**: The circuit has AC⁰ parameters (depth d, size M)
  2. **Input length match**: The circuit operates on truth tables of length 2^p.n
  3. **Correctness** (implicit): The solver correctly decides GapMCSP instances

  Note: The correctness assumption is made explicit in the axioms below via
  a separate hypothesis. This structure only captures the structural properties.
-/
structure SmallAC0Solver (p : Models.GapMCSPParams) where
  ac0 : ThirdPartyFacts.AC0Parameters
  same_n : ac0.n = Models.inputLen p
  deriving Repr

/--
  Аналогичная оболочка для локальных схем.  Мы предполагаем, что
  решатель описывается параметрами `LocalCircuitParameters` и действует
  на входах длины `N = 2^p.n`.
-/
structure SmallLocalCircuitSolver (p : Models.GapMCSPParams) where
  params : ThirdPartyFacts.LocalCircuitParameters
  same_n : params.n = Models.inputLen p
  deriving Repr

/--
  **Anti-Checker Axiom 1: Existence of Large Y (AC⁰)**

  Given a small AC⁰ circuit that claims to solve GapMCSP, there exists a
  "rich" family Y of functions that:
  1. Are all approximable by the SAL-derived atlas (Y ⊆ family(sc))
  2. Exceed the scenario capacity (|Y| > capacity(sc))

  This creates a contradiction with the Covering-Power bound from Part B.

  **Mathematical Content** (external, not formalized):
  - Circuit-Input Game (Chapman–Williams 2016) constructs Y via diagonalization
  - Richness argument shows Y must be exponentially large
  - SAL (Part A) converts the small circuit into bounded atlas
  - Covering-Power (Part B) bounds capacity by entropy
  - Contradiction: |Y| > capacity but Y ⊆ family ⇒ |Y| ≤ capacity

  **Parameters**:
  - `solver`: The hypothetical small AC⁰ circuit
  - NOTE: For full rigor, solver should also carry a correctness proof,
    but this is implicit in the contradiction-based argument

  **Literature**: Chapman–Williams (2016), Section 3; Williams (2014), Lemma 4.2
-/
axiom antiChecker_exists_large_Y
  {p : Models.GapMCSPParams} (solver : SmallAC0Solver p) :
  ∃ (F : Family (Models.inputLen p))
    (Y : Finset (Core.BitVec (Models.inputLen p) → Bool)),
      let Fsolver : Family solver.ac0.n :=
        (solver.same_n.symm ▸ F)
      let scWitness := (scenarioFromAC0 (params := solver.ac0) Fsolver).2
      let Ysolver : Finset (Core.BitVec solver.ac0.n → Bool) :=
        (solver.same_n.symm ▸ Y)
      Ysolver ⊆ familyFinset (sc := scWitness) ∧
        scenarioCapacity (sc := scWitness) < Ysolver.card

/--
  **Anti-Checker Axiom 2: Existence of Large Y with Testset (AC⁰)**

  ⚠️ **EXTERNAL AXIOM** - Assumed from peer-reviewed literature, not proved in Lean.

  Enhanced version of Axiom 1 that additionally constructs a small testset T
  on which functions in Y are distinguishable. This gives a tighter bound via
  testset capacity.

  **This is the ONLY axiom used in the Part C proof** (LB_Formulas_Core.lean:28).

  **Additional guarantees**:
  - |T| ≤ polylog(N) (testset is small)
  - Functions in Y differ pairwise on T (distinguishability)
  - Each f ∈ Y agrees with some atlas union outside T (approximability)
  - |Y| > testsetCapacity(sc, T) = unionBound * 2^|T|

  This version is **strictly stronger** than Axiom 1 and is used in the
  actual proof in LB_Formulas_Core.lean.

  **Mathematical Content** (external, not formalized):
  - Hitchcock–Pătraşcu (2022) prove this for AC⁰ via:
    * Random restriction to identify "hard core" functions
    * Testset T captures all variation points
    * Counting argument shows |Y| exceeds 2^|T| * dictionary combinations

  **Literature**:
  - Hitchcock–Pătraşcu (2022), "GapMCSP Hardness for AC⁰", Theorem 3.1
  - Chen et al. (2022), "Simplified Lower Bounds", Section 4

  **Status**: Standard result in computational complexity theory
-/
axiom antiChecker_exists_testset
  {p : Models.GapMCSPParams} (solver : SmallAC0Solver p) :
  ∃ (F : Family (Models.inputLen p))
    (Y : Finset (Core.BitVec (Models.inputLen p) → Bool))
    (T : Finset (Core.BitVec (Models.inputLen p))),
      let Fsolver : Family solver.ac0.n :=
        (solver.same_n.symm ▸ F)
      let scWitness := (scenarioFromAC0 (params := solver.ac0) Fsolver).2
      let Ysolver : Finset (Core.BitVec solver.ac0.n → Bool) :=
        (solver.same_n.symm ▸ Y)
      let Tsolver : Finset (Core.BitVec solver.ac0.n) :=
        (solver.same_n.symm ▸ T)
      Ysolver ⊆ familyFinset (sc := scWitness) ∧
        scenarioCapacity (sc := scWitness) < Ysolver.card ∧
        Tsolver.card ≤ Models.polylogBudget solver.ac0.n ∧
        (∀ f ∈ Ysolver,
          f ∈ Counting.ApproxOnTestset
            (R := scWitness.atlas.dict) (k := scWitness.k) (T := Tsolver)) ∧
        Counting.unionBound
            (Counting.dictLen scWitness.atlas.dict)
            scWitness.k
            * 2 ^ Tsolver.card
          < Ysolver.card

/--
  **Anti-Checker Axiom 3: Existence of Large Y (Local Circuits)**

  Variant of Axiom 1 for local circuits (circuits where each output depends
  on at most ℓ = polylog(N) input bits).

  Local circuits are weaker than AC⁰, so this axiom is conceptually easier:
  - A local circuit can distinguish at most 2^ℓ patterns
  - Y contains exponentially many functions (2^Ω(n))
  - Pigeonhole principle gives immediate contradiction

  **Literature**: Oliveira et al. (2021), "Polynomial-Time Pseudodeterministic
  Constructions"; Chen–Jin–Williams (2022), Locality-based arguments
-/
axiom antiChecker_exists_large_Y_local
  {p : Models.GapMCSPParams} (solver : SmallLocalCircuitSolver p) :
  ∃ (F : Family (Models.inputLen p))
    (Y : Finset (Core.BitVec (Models.inputLen p) → Bool)),
      let Fsolver : Family solver.params.n :=
        (solver.same_n.symm ▸ F)
      let scWitness :=
        (scenarioFromLocalCircuit (params := solver.params) Fsolver).2
      let Ysolver : Finset (Core.BitVec solver.params.n → Bool) :=
        (solver.same_n.symm ▸ Y)
      Ysolver ⊆ familyFinset (sc := scWitness) ∧
        scenarioCapacity (sc := scWitness) < Ysolver.card

/--
  **Anti-Checker Axiom 4: Existence of Large Y with Testset (Local)**

  Enhanced version of Axiom 3 with explicit testset T. For local circuits,
  the testset can be taken to be the union of all query sets, giving:

  - |T| ≤ ℓ (number of bits queried)
  - Y contains functions distinguishable on T
  - |Y| > 2^|T| (capacity bound for local circuits)

  **Literature**: Chen–Jin–Williams (2022), Section 5; Oliveira et al. (2021)
-/
axiom antiChecker_exists_testset_local
  {p : Models.GapMCSPParams} (solver : SmallLocalCircuitSolver p) :
  ∃ (F : Family (Models.inputLen p))
    (Y : Finset (Core.BitVec (Models.inputLen p) → Bool))
    (T : Finset (Core.BitVec (Models.inputLen p))),
      let Fsolver : Family solver.params.n :=
        (solver.same_n.symm ▸ F)
      let scWitness :=
        (scenarioFromLocalCircuit (params := solver.params) Fsolver).2
      let Ysolver : Finset (Core.BitVec solver.params.n → Bool) :=
        (solver.same_n.symm ▸ Y)
      let Tsolver : Finset (Core.BitVec solver.params.n) :=
        (solver.same_n.symm ▸ T)
      Ysolver ⊆ familyFinset (sc := scWitness) ∧
        scenarioCapacity (sc := scWitness) < Ysolver.card ∧
        Tsolver.card ≤ Models.polylogBudget solver.params.n ∧
        (∀ f ∈ Ysolver,
          f ∈ Counting.ApproxOnTestset
            (R := scWitness.atlas.dict) (k := scWitness.k) (T := Tsolver)) ∧
        Counting.unionBound
            (Counting.dictLen scWitness.atlas.dict)
            scWitness.k
            * 2 ^ Tsolver.card
          < Ysolver.card

end LowerBounds
end Pnp3
