import Tests.PartACanonicalAuditSupport

/-! Infrastructure regression: the first audit must not freeze the environment
before the named declarations below. No original Part A proof is changed. -/
#print axioms True.intro
#partA_axioms "True.intro"

namespace PartACanonical.Audit.CacheRegression

def lateIdentity (n : Nat) : Nat := n
theorem lateIdentity_eq (n : Nat) : lateIdentity n = n := rfl
theorem lateIdentity_eq_full (n : Nat) : lateIdentity n = n := lateIdentity_eq n

def check_lateIdentity : Nat → Nat := lateIdentity
def check_lateIdentity_eq : ∀ (n : Nat), lateIdentity n = n := lateIdentity_eq
def check_lateIdentity_eq_full : ∀ (n : Nat), lateIdentity n = n := lateIdentity_eq_full

private def privateValue : Nat := 7
def check_privateValue : Nat := privateValue
def «7» : Nat := 7
def check_quotedSeven : Nat := «7»
def «with.dot» : Nat := 3
def check_quotedDot : Nat := «with.dot»

#check (check_lateIdentity : Nat → Nat)
#check (check_lateIdentity_eq : ∀ (n : Nat), lateIdentity n = n)
#check (check_lateIdentity_eq_full : ∀ (n : Nat), lateIdentity n = n)
#check (privateValue : Nat)
#check (check_privateValue : Nat)
#check (check_quotedSeven : Nat)
#check (check_quotedDot : Nat)

#print axioms lateIdentity
#print axioms lateIdentity_eq
#print axioms lateIdentity_eq_full
#print axioms check_lateIdentity
#print axioms check_lateIdentity_eq
#print axioms check_lateIdentity_eq_full
#print axioms privateValue
#print axioms check_privateValue
#print axioms «7»
#print axioms check_quotedSeven
#print axioms «with.dot»
#print axioms check_quotedDot

#partA_axioms "PartACanonical.Audit.CacheRegression.lateIdentity"
#partA_axioms "PartACanonical.Audit.CacheRegression.lateIdentity_eq"
#partA_axioms "PartACanonical.Audit.CacheRegression.lateIdentity_eq_full"
#partA_axioms "PartACanonical.Audit.CacheRegression.check_lateIdentity"
#partA_axioms "PartACanonical.Audit.CacheRegression.check_lateIdentity_eq"
#partA_axioms "PartACanonical.Audit.CacheRegression.check_lateIdentity_eq_full"
#partA_axioms "_private.Tests.PartACanonicalAuditCacheTests.0.PartACanonical.Audit.CacheRegression.privateValue"
#partA_axioms "PartACanonical.Audit.CacheRegression.check_privateValue"
#partA_axioms "PartACanonical.Audit.CacheRegression.«7»"
#partA_axioms "PartACanonical.Audit.CacheRegression.check_quotedSeven"
#partA_axioms "PartACanonical.Audit.CacheRegression.«with.dot»"
#partA_axioms "PartACanonical.Audit.CacheRegression.check_quotedDot"

end PartACanonical.Audit.CacheRegression

/-! Production capstone: the invocation-local index is reused within a batch,
then discarded before every subsequent command/environment replacement. -/
namespace PartACanonical.Audit.BatchRegression
open Lean Elab Command

def check_printDirectBatch : Array String → CommandElabM Nat :=
  PartACanonical.Audit.printDirectBatch
def check_directAxiomsBatch : Lean.ParserDescr :=
  PartACanonical.Audit.directAxiomsBatch
def check_elaborateDirectAxiomsBatch : CommandElab :=
  PartACanonical.Audit.elaborateDirectAxiomsBatch

#check (check_printDirectBatch : Array String → CommandElabM Nat)
#check (check_directAxiomsBatch : Lean.ParserDescr)
#check (check_elaborateDirectAxiomsBatch : CommandElab)

private noncomputable def choiceFixture : Nat := Classical.choice ⟨0⟩
#check (choiceFixture : Nat)

private def addFixture (name : Name) (value : Expr) : CommandElabM Unit := do
  liftCoreM <| Lean.addDecl (.defnDecl {
    name := name
    levelParams := []
    type := mkConst ``Nat
    value := value
    hints := .opaque
    safety := .safe })

private def expectRejection (text expectedPrefix : String) : CommandElabM Unit := do
  let message ← try
    discard <| printDirectBatch #[text]
    pure none
  catch exception =>
    pure (some (← exception.toMessageData.toString))
  match message with
  | none => throwError "Expected rejection for {text}"
  | some message =>
    unless message.startsWith expectedPrefix do
      throwError "Wrong rejection for {text}: {message}"

run_cmd do
  if Lean.debug.skipKernelTC.get (← getOptions) then
    throwError "Kernel checking must remain enabled"
  let base ← getEnv
  let size := base.constants.toList.length
  let visits ← printDirectBatch #["True.intro", "True.intro"]
  unless visits == size do throwError "Repeated traversal within one batch"
  logInfo m!"CACHE_CAPSTONE_REUSE: roots=2; visited={visits}; environment={size}"

  let inserted := `PartACanonical.Audit.BatchFixture.inserted
  addFixture inserted (mkRawNatLit 0)
  let afterInsert ← getEnv
  let insertedVisits ← printDirectBatch #[inserted.toString]
  unless insertedVisits == size + 1 && afterInsert.contains inserted do
    throwError "Late-declaration fixture/index mismatch"
  setEnv base
  expectRejection inserted.toString "Missing or nonexact direct axiom root"
  logInfo "CACHE_CAPSTONE_ADD_REMOVE_OK"

  let leftName := `PartACanonical.Audit.BatchFixture.left
  let rightName := `PartACanonical.Audit.BatchFixture.right
  addFixture leftName (mkRawNatLit 0)
  let left ← getEnv
  discard <| printDirectBatch #[leftName.toString]
  setEnv base
  addFixture rightName (mkRawNatLit 1)
  let right ← getEnv
  discard <| printDirectBatch #[rightName.toString]
  unless left.constants.toList.length == right.constants.toList.length do
    throwError "Replacement fixture must have equal cardinality"
  expectRejection leftName.toString "Missing or nonexact direct axiom root"
  logInfo "CACHE_CAPSTONE_EQUAL_SIZE_REPLACEMENT_OK"
  setEnv base

  let sameName := `PartACanonical.Audit.BatchFixture.replacedBody
  addFixture sameName (mkRawNatLit 0)
  let old ← getEnv
  discard <| printDirectBatch #[sameName.toString]
  let oldAxioms ← collectAxioms sameName
  setEnv base
  addFixture sameName (mkConst ``choiceFixture)
  let fresh ← getEnv
  discard <| printDirectBatch #[sameName.toString]
  let newAxioms ← collectAxioms sameName
  unless old.constants.toList.length == fresh.constants.toList.length &&
      !oldAxioms.contains ``Classical.choice && newAxioms.contains ``Classical.choice do
    throwError "Same-FQN body replacement must use current axiom dependencies"
  logInfo "CACHE_CAPSTONE_SAME_FQN_CHANGED_AXIOMS_OK"
  setEnv base

  let collisionLeft := Name.str (Name.str .anonymous "PartABatchCollision.scope") "_inaccessible"
  let collisionRight := Name.str (Name.str (Name.str .anonymous "PartABatchCollision") "scope") "_inaccessible"
  unless collisionLeft != collisionRight && collisionLeft.toString == collisionRight.toString do
    throwError "Distinct-name rendering-collision fixture invalid"
  addFixture collisionLeft (mkRawNatLit 0)
  addFixture collisionRight (mkRawNatLit 1)
  expectRejection collisionLeft.toString "Ambiguous exact FQN"
  setEnv base
  expectRejection "PartACanonical.Audit.CacheRegression.7" "Missing or nonexact direct axiom root"
  expectRejection "PartACanonical.Audit.CacheRegression.07" "Missing or nonexact direct axiom root"
  logInfo "CACHE_CAPSTONE_COLLISION_NUMERIC_GUARDS_OK"

#print axioms PartACanonical.Audit.printDirectBatch
#print axioms PartACanonical.Audit.directAxiomsBatch
#print axioms PartACanonical.Audit.elaborateDirectAxiomsBatch
#print axioms check_printDirectBatch
#print axioms check_directAxiomsBatch
#print axioms check_elaborateDirectAxiomsBatch
#partA_axioms_batch [
  "PartACanonical.Audit.printDirectBatch",
  "PartACanonical.Audit.directAxiomsBatch",
  "PartACanonical.Audit.elaborateDirectAxiomsBatch",
  "PartACanonical.Audit.BatchRegression.check_printDirectBatch",
  "PartACanonical.Audit.BatchRegression.check_directAxiomsBatch",
  "PartACanonical.Audit.BatchRegression.check_elaborateDirectAxiomsBatch"
]
end PartACanonical.Audit.BatchRegression

#check (PartACanonical.Audit.printDirectBatch : Array String → Lean.Elab.Command.CommandElabM Nat)
#check (PartACanonical.Audit.directAxiomsBatch : Lean.ParserDescr)
#check (PartACanonical.Audit.elaborateDirectAxiomsBatch : Lean.Elab.Command.CommandElab)
