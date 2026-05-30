import Complexity.TMVerifier.TuringToolkit.Foundation
import Complexity.TMVerifier.TuringToolkit.BinaryCounter
import Complexity.TMVerifier.TuringToolkit.Encoding
import Complexity.TMVerifier.TuringToolkit.AtomicPrograms
import Complexity.TMVerifier.TuringToolkit.UnaryAtOffset
import Complexity.TMVerifier.TuringToolkit.CopyAtOffset
import Complexity.TMVerifier.TuringToolkit.CombineAtOffset
import Complexity.TMVerifier.TuringToolkit.GateWrappers
import Complexity.TMVerifier.TuringToolkit.ConstStatePhasedProgram

/-!
# Turing toolkit — aggregator

This file used to contain the full Turing toolkit in a single 7 000+
line module.  It has been split into dedicated submodules under
`Complexity/TMVerifier/TuringToolkit/` for maintainability.

Importing this file re-exports everything the toolkit provides.

Logical dependency order:

1. `Foundation`                — `PhasedProgram` + compilation + `Pilot`
                                  (smoke tests) + `Configuration` invariants.
2. `BinaryCounter`             — `incrementProgram` and its full correctness
                                  proof + the `readFirstBit` Pilot.
3. `Encoding`                  — `CircuitTree`, `SLProgram`, and tape-layout
                                  structures (`TapeLayout`, `TapeMatches`).
4. `AtomicPrograms`            — the four single-step primitives
                                  (`seekRightProgram`, `writeBitProgram`,
                                  `seekLeftProgram`, `readBitProgram`).
5. `UnaryAtOffset`             — three 1-offset compounds
                                  (`writeAtOffsetProgram`,
                                   `readAtOffsetProgram`,
                                   `notAtOffsetProgram`).
6. `CopyAtOffset`              — `copyAtOffsetProgram`.
7. `CombineAtOffset`           — parameterized 2-input compound
                                  (`combineAtOffsetProgram`).
8. `GateWrappers`              — `AndAtOffset`, `OrAtOffset`,
                                  `NotSrcDstAtOffset`, and per-`SLGate`
                                  evaluator wrappers.
9. `ConstStatePhasedProgram`   — uniform-state restriction and `seq`
                                  combinator.
-/
