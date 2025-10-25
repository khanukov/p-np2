import ExampleProofs.Examples

namespace Facts
namespace PsubsetPpoly
namespace Tests

open Complexity
open TM
open scoped Classical

/--
Assert that the `actual` and `expected` values coincide.  The helper prints a
short success message and throws a descriptive `IO` error otherwise.
-/
def assertEq {α : Type _} [DecidableEq α] (msg : String)
    (actual expected : α) : IO Unit := do
  if actual = expected then
    IO.println s!"[ok] {msg}"
  else
    throw <| IO.userError s!"[failed] {msg}"

/-- Log that a proof has been checked.  This lets the executable surface the
purely propositional checks that rely on the non-computational witnesses. -/
def logProof {α : Sort _} {β : Sort _} (msg : String)
    {a b : α} (h : a = b) : IO Unit := do
  -- Force Lean to elaborate the argument before discarding it.
  let _ := h
  IO.println s!"[proved] {msg}"

abbrev emptyBitstring : Bitstring 0 := fun i => False.elim
  (Nat.not_lt_zero _ i.2)

abbrev zeroBit : Bitstring 1 := bitstring₁ false
abbrev bit10 : Bitstring 2 := bitstring₂ true false
abbrev bit01 : Bitstring 2 := bitstring₂ false true

/--
Sanity checks covering the constantly-true language example.
-/
def runConstTrueChecks : IO Unit := do
  IO.println "Constant language checks"
  assertEq "machine accepts length-1 zero input"
    (TM.accepts (M := constTrueTM) (n := 1) zeroBit) true
  assertEq "language ignores the concrete input"
    (constTrueLanguage 2 bit10) true
  logProof "non-uniform circuit agrees with the language on a sample"
    (by
      have h := constTrue_inPpoly.correct (n := 2) (x := bit10)
      simpa [constTrueLanguage_eval] using h)

/--
Regression tests for the first-bit language and its straight-line witness.
-/
def runFirstBitChecks : IO Unit := do
  IO.println "First-bit language checks"
  assertEq "language rejects the empty input"
    (firstBitLanguage 0 emptyBitstring) false
  assertEq "machine accepts when the first bit is one"
    (TM.accepts (M := firstBitTM) (n := 2) bit10) true
  assertEq "machine rejects when the first bit is zero"
    (TM.accepts (M := firstBitTM) (n := 2) bit01) false
  logProof "circuits reproduce the machine on a positive example"
    (by
      have h := firstBit_inPpoly.correct (n := 2) (x := bit10)
      have hPos : 0 < 2 := by decide
      simpa [firstBitLanguage, bit10, bitstring₂, hPos]
        using h)

/-- Entry point for the example-based regression suite. -/
def main : IO Unit := do
  IO.println "Running FactPsubsetPpoly regression checks..."
  runConstTrueChecks
  runFirstBitChecks
  IO.println "All checks completed successfully."

#eval Facts.PsubsetPpoly.Tests.runConstTrueChecks
#eval Facts.PsubsetPpoly.Tests.runFirstBitChecks
#eval IO.println "[info] Example regression checks evaluated"

end Tests
end PsubsetPpoly
end Facts
