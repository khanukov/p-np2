import ThirdPartyFacts.AC0Witness
import ThirdPartyFacts.HastadMSL
import Core.ShrinkageWitness
import Models.Model_GapMCSP
import AC0.Formulas

/-!
  pnp3/Core/ShrinkageAC0.lean

  Interface glue between the abstract multi-switching lemma and the rest of the
  shrinkage pipeline.  The heavy combinatorics is encapsulated in
  `ThirdPartyFacts.HastadMSL`: once a witness is available, the present module
  merely re-packages it into the typeclass world and exposes a few convenient
  projections.

  The design deliberately mirrors the layout promised in the roadmap.  Even
  though the actual construction is currently assumed via axioms, the
  bookkeeping follows the structure needed for the eventual formal proof and can
  therefore already serve the rest of the development.
-/

namespace Pnp3
namespace Core

open Classical
open ThirdPartyFacts
open Models

variable (params : AC0Parameters) (F : Family params.n)

/--
Extract the partial witness delivered by the multi-switching lemma.  The
existence of such a witness is expressed via the typeclass
`ThirdPartyFacts.HasMultiSwitchingWitness`; currently it is instantiated by the
explicit "perfect" witness from `ThirdPartyFacts.HastadMSL`.  The definition is
kept abstract so that the eventual constructive multi-switching lemma can drop
in without touching the surrounding API.
-/
noncomputable def multiSwitchingPartialWitness
    [ThirdPartyFacts.HasMultiSwitchingWitness params F] :
    AC0PartialWitness params F :=
  (ThirdPartyFacts.multiSwitchingWitness (params := params) (F := F)).witness

/--
  The default instance exposing the AC⁰ shrinkage witness now depends only on
  the abstract multi-switching interface.  At the moment this expands to the
  perfect (depth-`n`) witness; future work will swap in the polylogarithmic
  certificate with no further changes required here.
-/
noncomputable instance instHasAC0PartialWitness
    [ThirdPartyFacts.HasMultiSwitchingWitness params F] :
    HasAC0PartialWitness params F :=
  ⟨multiSwitchingPartialWitness (params := params) (F := F)⟩

section OracleLift

/--
Owing to future applications, we keep the oracle-augmented interface from the
previous iteration.  An `OraclePartialWitness` augments the base witness with an
explicit bound on the fan-in of oracle leaves.
-/
structure OracleParameters where
  maxArity : Nat
  deriving Repr

structure OraclePartialWitness
    (params : AC0Parameters)
    (oracle : OracleParameters)
    (F : Family params.n) where
  base : AC0PartialWitness params F
  level_le_oracle : base.level ≤ oracle.maxArity
  oracle_le_polylog : oracle.maxArity
      ≤ polylogBudget (Nat.pow 2 params.n)

/-- Packaging the oracle witness inside a typeclass keeps the downstream API
uniform. -/
class HasOraclePartialWitness
    (params : AC0Parameters)
    (oracle : OracleParameters)
    (F : Family params.n) : Type where
  witness : OraclePartialWitness params oracle F

variable {params oracle F}

/-- Project the plain certificate out of an oracle witness. -/
noncomputable def oracleWitnessCertificate
    (W : OraclePartialWitness params oracle F) :
    PartialCertificate params.n W.base.tailDepth F :=
  W.base.certificate

lemma oracleWitness_level_le_maxArity
    (W : OraclePartialWitness params oracle F) :
    W.base.level ≤ oracle.maxArity :=
  W.level_le_oracle

lemma oracleWitness_polylog_bound
    (W : OraclePartialWitness params oracle F) :
    oracle.maxArity ≤ polylogBudget (Nat.pow 2 params.n) :=
  W.oracle_le_polylog

end OracleLift

end Core
end Pnp3
