import Complexity.TMVerifier.TuringToolkit.GateNRuntimeGrammar

/-!
# GN-E2-1c finite stage-zero reverse locator grammar (2026-09-02)

**Progress classification: infrastructure, not P-vs-NP mainline progress.**

This module is the pure grammar for the live, read-only pass from the first
scratch cell back to the first gate record.  It contains only finite modes and
at most three buffered bits.  In particular, no mode or payload contains a
natural number, base, index, width, request, or list.

The grammar is deliberately stage-zero strict.  It first requires the exact
terminal suffix `finish · output false · separator` in reverse reading order,
then accepts only canonical record bodies.  Locally it stops on any `cursor`
encountered in a legal tag-count mode, or on the immediately preceding
`separator` when the record region is empty.  The designated first cursor and
its global uniqueness are conclusions only for canonical encoded nonempty
programs, via the split/uniqueness theorems and capstones in
`GateNScratchBootstrap`.  Blank, data, either output in record mode, spent,
misplaced delimiters, and every undecodable word reject.  Later-stage marker
shortcuts are not part of this switch.
-/

namespace Pnp3.Internal.PsubsetPpoly.TM

/-- Finite modes of the strict stage-zero right-to-left locator. -/
inductive GNLocateMode where
  | tailFinish | tailOutput | tailSeparator | recordEdge | moreRecord
  | arg2 | arg1 | tag0 | tag1 | tag2 | tag3 | tag4 | tag5
  | firstRecord | noGate | reject
  deriving Fintype, DecidableEq, Repr

/-- The four reverse frame positions and their at-most-three-bit buffer. -/
inductive GNLocateBuffer where
  | r3
  | r2 (b3 : Bool)
  | r1 (b2 b3 : Bool)
  | r0 (b1 b2 b3 : Bool)
  deriving Fintype, DecidableEq, Repr

/-- The complete finite locator payload. -/
structure GNLocateState where
  mode : GNLocateMode
  buffer : GNLocateBuffer
  deriving Fintype, DecidableEq, Repr

/-- Only the three fixed endpoints stop a reverse frame completion. -/
def GNLocateMode.Stop : GNLocateMode → Prop
  | .firstRecord | .noGate | .reject => True
  | _ => False

/-- Exactly the modes in which a reverse frame may be read. -/
def GNLocateMode.Reverse : GNLocateMode → Prop
  | .firstRecord | .noGate | .reject => False
  | _ => True

/-- Strict frame-level stage-zero reverse decision. -/
def gnLocateAdvance : GNLocateMode → G1Frame → GNLocateMode
  | .tailFinish, .finish => .tailOutput
  | .tailOutput, .output false => .tailSeparator
  | .tailSeparator, .separator => .recordEdge
  | .recordEdge, .separator => .noGate
  | .recordEdge, .finish => .arg2
  | .moreRecord, .finish => .arg2
  | .arg2, .index => .arg2
  | .arg2, .argSep => .arg1
  | .arg1, .index => .arg1
  | .arg1, .argSep => .tag0
  | .tag0, .tag => .tag1
  | .tag1, .tag => .tag2
  | .tag2, .tag => .tag3
  | .tag3, .tag => .tag4
  | .tag4, .tag => .tag5
  | .tag1, .bof => .moreRecord
  | .tag2, .bof => .moreRecord
  | .tag3, .bof => .moreRecord
  | .tag4, .bof => .moreRecord
  | .tag5, .bof => .moreRecord
  | .tag1, .cursor => .firstRecord
  | .tag2, .cursor => .firstRecord
  | .tag3, .cursor => .firstRecord
  | .tag4, .cursor => .firstRecord
  | .tag5, .cursor => .firstRecord
  | _, _ => .reject

/-- Bit-level completion; every reserved/undecodable window rejects. -/
def gnLocateComplete (mode : GNLocateMode) (b0 b1 b2 b3 : Bool) :
    GNLocateMode :=
  match decodeG1Frame? [b0, b1, b2, b3] with
  | some frame => gnLocateAdvance mode frame
  | none => .reject

/-- Pure right-to-left path in reading order. -/
def GNLocateRevPathFrom : GNLocateMode → List G1Frame → Prop
  | _, [] => True
  | mode, frame :: rest =>
      mode.Reverse ∧ ¬(gnLocateAdvance mode frame).Stop ∧
        GNLocateRevPathFrom (gnLocateAdvance mode frame) rest

/-- A left-to-right list is valid when its reverse is a valid reading path. -/
def GNLocateRevValidPath (mode : GNLocateMode) (frames : List G1Frame) : Prop :=
  GNLocateRevPathFrom mode frames.reverse

/-- Pure mode fold over a left-to-right list read from the right. -/
def gnLocateAdvanceList (mode : GNLocateMode) (frames : List G1Frame) :
    GNLocateMode :=
  frames.reverse.foldl gnLocateAdvance mode

/-- All three reserved codec words reject from every live reverse mode. -/
theorem gnLocateComplete_reserved (mode : GNLocateMode) :
    gnLocateComplete mode true true false true = .reject ∧
      gnLocateComplete mode true true true false = .reject ∧
        gnLocateComplete mode true true true true = .reject := by
  cases mode <;> simp [gnLocateComplete, decodeG1Frame?]

/-- The tail order is exact, and the record edge has only the two stage-zero
doors. -/
theorem gnLocateAdvance_tail_and_edge :
    gnLocateAdvance .tailFinish .finish = .tailOutput ∧
      gnLocateAdvance .tailOutput (.output false) = .tailSeparator ∧
      gnLocateAdvance .tailSeparator .separator = .recordEdge ∧
      gnLocateAdvance .recordEdge .separator = .noGate ∧
      gnLocateAdvance .recordEdge .finish = .arg2 := by
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- Representative forbidden stage-zero frames all reject. -/
theorem gnLocateAdvance_stageZero_malformed :
    gnLocateAdvance .tailFinish .blank = .reject ∧
      gnLocateAdvance .tailFinish (.output false) = .reject ∧
      gnLocateAdvance .tailOutput (.output true) = .reject ∧
      gnLocateAdvance .recordEdge .blank = .reject ∧
      gnLocateAdvance .recordEdge (.data false) = .reject ∧
      gnLocateAdvance .recordEdge (.output false) = .reject ∧
      gnLocateAdvance .recordEdge (.output true) = .reject ∧
      gnLocateAdvance .recordEdge .spent = .reject := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end Pnp3.Internal.PsubsetPpoly.TM
