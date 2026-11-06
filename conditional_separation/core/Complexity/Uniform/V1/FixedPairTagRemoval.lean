import Complexity.Uniform.V1.FixedPairSeparatorHole
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Prod
import Mathlib.Tactic.Ring
/-!
# Fixed pair tag removal
A closed nine-state phase consumes `FixedPairSeparatorHole`'s exact final
configuration and removes every query tag by right-to-left compaction.  It
runs for `n * (n + 5) + 2` steps and leaves
`[n+1 blanks][x][w][marker][blanks]`, accepting at the origin.  Thus the query
and witness content is contiguous but offset by `n+1` blanks; compaction to an
origin-aligned headerless prefix remains open and is not claimed here.
The final origin test uses the left clamp exactly once, at `clock n - 2`; no
right clamp fires, including for `B = 0`.  The generic shift/clamp-necessity
appendix and packed-pair injectivity are deliberately deferred.  All results
include the `n = 0`, `m = 0`, and `B = 0` cases.
-/
namespace Pnp3.Complexity.Uniform.V1
namespace FixedPairTagRemoval
open PairEncoding
abbrev removalStateCount : Nat := 9
def qStart : Fin removalStateCount := ⟨0, by decide⟩
private def qFetch : Fin removalStateCount := ⟨1, by decide⟩
private def qCarryF : Fin removalStateCount := ⟨2, by decide⟩
private def qCarryT : Fin removalStateCount := ⟨3, by decide⟩
private def qDropF : Fin removalStateCount := ⟨4, by decide⟩
private def qDropT : Fin removalStateCount := ⟨5, by decide⟩
private def qReturn : Fin removalStateCount := ⟨6, by decide⟩
def qAccept : Fin removalStateCount := ⟨7, by decide⟩
def qReject : Fin removalStateCount := ⟨8, by decide⟩
private def removalRawStep (q : Fin removalStateCount) (scanned : Option Bool) :
    Fin removalStateCount × Option Bool × Move :=
  match q.val with
  | 0 =>
      match scanned with
      | none => (qFetch, none, .left)
      | some b => (qReject, some b, .stay)
  | 1 =>
      match scanned with
      | none => (qAccept, none, .stay)
      | some false => (qCarryF, none, .right)
      | some true => (qCarryT, none, .right)
  | 2 =>
      match scanned with
      | none => (qCarryF, none, .right)
      | some b => (qDropF, some b, .left)
  | 3 =>
      match scanned with
      | none => (qCarryT, none, .right)
      | some b => (qDropT, some b, .left)
  | 4 =>
      match scanned with
      | none => (qReturn, some false, .left)
      | some b => (qReject, some b, .stay)
  | 5 =>
      match scanned with
      | none => (qReturn, some true, .left)
      | some b => (qReject, some b, .stay)
  | 6 =>
      match scanned with
      | none => (qReturn, none, .left)
      | some false => (qFetch, none, .left)
      | some true => (qReject, some true, .stay)
  | 7 => (qAccept, scanned, .stay)
  | _ => (qReject, scanned, .stay)
/-- The closed nine-state tag-removal machine. -/
def machine : UniformTM where
  stateCount := removalStateCount
  start := qStart
  accept := qAccept
  reject := qReject
  accept_ne_reject := by decide
  rawStep := removalRawStep
/-- Exhaustive pin for all nine rows of the installed raw table.  Work rows are
named by their numeric control: 1 fetch, 2/3 carry, 4/5 drop, 6 return. -/
theorem removalRawStep_table :
    (∀ s, machine.rawStep qStart s =
      match s with
      | none => (⟨1, by decide⟩, none, .left)
      | some b => (qReject, some b, .stay)) ∧
    (∀ s, machine.rawStep ⟨1, by decide⟩ s =
      match s with
      | none => (qAccept, none, .stay)
      | some false => (⟨2, by decide⟩, none, .right)
      | some true => (⟨3, by decide⟩, none, .right)) ∧
    (∀ s, machine.rawStep ⟨2, by decide⟩ s =
      match s with
      | none => (⟨2, by decide⟩, none, .right)
      | some b => (⟨4, by decide⟩, some b, .left)) ∧
    (∀ s, machine.rawStep ⟨3, by decide⟩ s =
      match s with
      | none => (⟨3, by decide⟩, none, .right)
      | some b => (⟨5, by decide⟩, some b, .left)) ∧
    (∀ s, machine.rawStep ⟨4, by decide⟩ s =
      match s with
      | none => (⟨6, by decide⟩, some false, .left)
      | some b => (qReject, some b, .stay)) ∧
    (∀ s, machine.rawStep ⟨5, by decide⟩ s =
      match s with
      | none => (⟨6, by decide⟩, some true, .left)
      | some b => (qReject, some b, .stay)) ∧
    (∀ s, machine.rawStep ⟨6, by decide⟩ s =
      match s with
      | none => (⟨6, by decide⟩, none, .left)
      | some false => (⟨1, by decide⟩, none, .left)
      | some true => (qReject, some true, .stay)) ∧
    (∀ s, machine.rawStep qAccept s = (qAccept, s, .stay)) ∧
    (∀ s, machine.rawStep qReject s = (qReject, s, .stay)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals
    intro s
    rfl
/-- Exact finite-control and transition-table resource pins. -/
theorem machine_resource_pins :
    machine.stateCount = 9 ∧ machine.start = qStart ∧
    machine.accept = qAccept ∧ machine.reject = qReject ∧
    qStart.val = 0 ∧ qAccept.val = 7 ∧ qReject.val = 8 ∧
    Fintype.card (Fin machine.stateCount × Option Bool) = 27 := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
  change Fintype.card (Fin 9 × Option Bool) = 27
  decide
/-! ## Handoff, clock, and final layout -/
/-- The phase-start configuration: the hole phase's exact valid final head and
tape with only the finite control replaced.  This is a proof-level phase
boundary, not a transition of either machine. -/
def startConfig {n m : Nat} (B : Nat) (x : Bitstring n) (w : Bitstring m) :
    Config removalStateCount (pairLength n m) B where
  state := qStart
  head := (FixedPairSeparatorHole.finalConfig B x w).head
  tape := (FixedPairSeparatorHole.finalConfig B x w).tape
/-- Exact handoff from the proved hole run: the hole machine halts in its own
literal accept, and the start configuration carries its exact head (the hole
address `2*n`) and tape, scanning the blank hole. -/
theorem startConfig_of_hole_run {n m B : Nat}
    (x : Bitstring n) (w : Bitstring m) :
    let holeFinal := FixedPairSeparatorHole.machine.run
      FixedPairSeparatorHole.clock (FixedPairSeparatorHole.startConfig B x w)
    holeFinal.state = FixedPairSeparatorHole.qAccept ∧
    (startConfig B x w).state = qStart ∧
    (startConfig B x w).head = holeFinal.head ∧
    (startConfig B x w).tape = holeFinal.tape ∧
    (startConfig B x w).head.val = 2 * n ∧
    (startConfig B x w).tape (startConfig B x w).head = none := by
  dsimp
  rw [FixedPairSeparatorHole.run_encoded_exact]
  refine ⟨rfl, rfl, rfl, rfl, rfl, ?_⟩
  show FixedPairSeparatorHole.holeTape B x w
    ⟨2 * n, by unfold tapeLength pairLength; omega⟩ = none
  simp [FixedPairSeparatorHole.holeTape]
/-- Exact deadline: two transitions plus `2k+6` for each round `k < n`. -/
def clock (n : Nat) : Nat :=
  n * (n + 5) + 2
/-- Closed form and structural reading of the clock. -/
theorem clock_structural (n : Nat) :
    clock n = n * n + 5 * n + 2 ∧ clock 0 = 2 ∧
    clock (n + 1) = clock n + (2 * n + 6) := by
  unfold clock
  refine ⟨by ring, rfl, by ring⟩
/-- The exact final layout: `n+1` blank cells, the query data on `n+1..2n`,
and the untouched witness, marker, and blank suffix. -/
def compactTape {n m : Nat} (B : Nat) (x : Bitstring n) (w : Bitstring m) :
    Fin (tapeLength (pairLength n m) B) → Option Bool :=
  fun i =>
    if h1 : i.val ≤ n then none
    else if h2 : i.val ≤ 2 * n then some (x ⟨i.val - n - 1, by omega⟩)
    else FixedPairConcatSentinel.sentinelTape B (encodePair x w) i
/-- Exact successful postconfiguration: literal accept, head at the origin,
and the compact layout. -/
def finalConfig {n m : Nat} (B : Nat) (x : Bitstring n) (w : Bitstring m) :
    Config removalStateCount (pairLength n m) B where
  state := qAccept
  head := ⟨0, by unfold tapeLength; omega⟩
  tape := compactTape B x w
private def queryBit {n : Nat} (x : Bitstring n) (j : Nat) : Bool :=
  if h : j < n then x ⟨j, h⟩ else false
private theorem queryBit_lt {n : Nat} (x : Bitstring n) (j : Nat) (h : j < n) :
    queryBit x j = x ⟨j, h⟩ := by
  unfold queryBit
  rw [dif_pos h]
private def baseCell {n m : Nat} (x : Bitstring n) (w : Bitstring m)
    (k : Nat) : Option Bool :=
  if h : k < pairLength n m then some (encodePair x w ⟨k, h⟩)
  else if k = pairLength n m then some true
  else none
private theorem sentinelTape_eq_baseCell {n m B : Nat}
    (x : Bitstring n) (w : Bitstring m)
    (i : Fin (tapeLength (pairLength n m) B)) :
    FixedPairConcatSentinel.sentinelTape B (encodePair x w) i =
      baseCell x w i.val :=
  rfl
private theorem baseCell_tag {n m : Nat} (x : Bitstring n) (w : Bitstring m)
    (i : Nat) (hi : i < n) : baseCell x w (2 * i) = some false := by
  unfold baseCell
  rw [dif_pos (show 2 * i < pairLength n m by unfold pairLength; omega)]
  exact congrArg some (encodePair_tag x w ⟨i, hi⟩)
private theorem baseCell_data {n m : Nat} (x : Bitstring n) (w : Bitstring m)
    (i : Nat) (hi : i < n) :
    baseCell x w (2 * i + 1) = some (queryBit x i) := by
  unfold baseCell
  rw [dif_pos (show 2 * i + 1 < pairLength n m by unfold pairLength; omega),
    queryBit_lt x i hi]
  exact congrArg some (encodePair_data x w ⟨i, hi⟩)
private theorem baseCell_witness {n m : Nat} (x : Bitstring n) (w : Bitstring m)
    (j : Nat) (hj : j < m) :
    baseCell x w (2 * n + 1 + j) = some (w ⟨j, hj⟩) := by
  unfold baseCell
  rw [dif_pos (show 2 * n + 1 + j < pairLength n m by unfold pairLength; omega)]
  exact congrArg some (encodePair_witness x w ⟨j, hj⟩)
private theorem baseCell_marker {n m : Nat} (x : Bitstring n)
    (w : Bitstring m) : baseCell x w (pairLength n m) = some true := by
  unfold baseCell
  rw [dif_neg (lt_irrefl _), if_pos rfl]
private theorem baseCell_beyond {n m : Nat} (x : Bitstring n) (w : Bitstring m)
    (k : Nat) (hk : pairLength n m < k) : baseCell x w k = none := by
  unfold baseCell
  rw [dif_neg (by omega), if_neg (by omega)]
private theorem baseCell_isSome {n m : Nat} (x : Bitstring n) (w : Bitstring m)
    (k : Nat) (hk : k ≤ pairLength n m) : ∃ c, baseCell x w k = some c := by
  unfold baseCell
  by_cases h : k < pairLength n m
  · exact ⟨_, by rw [dif_pos h]⟩
  · exact ⟨true, by rw [dif_neg h, if_pos (by omega)]⟩
private def segCell {n m : Nat} (x : Bitstring n) (w : Bitstring m)
    (L R k : Nat) : Option Bool :=
  if k < L then baseCell x w k
  else if k ≤ R then none
  else if k ≤ 2 * n then some (queryBit x (k - n - 1))
  else baseCell x w k
private theorem segCell_lt {n m : Nat} (x : Bitstring n) (w : Bitstring m)
    {L R k : Nat} (hk : k < L) : segCell x w L R k = baseCell x w k := by
  unfold segCell
  rw [if_pos hk]
private theorem segCell_blank {n m : Nat} (x : Bitstring n) (w : Bitstring m)
    {L R k : Nat} (hL : L ≤ k) (hR : k ≤ R) : segCell x w L R k = none := by
  unfold segCell
  rw [if_neg (Nat.not_lt.mpr hL), if_pos hR]
private theorem segCell_block {n m : Nat} (x : Bitstring n) (w : Bitstring m)
    {L R k : Nat} (hL : L ≤ k) (hR : R < k) (hn : k ≤ 2 * n) :
    segCell x w L R k = some (queryBit x (k - n - 1)) := by
  unfold segCell
  rw [if_neg (Nat.not_lt.mpr hL), if_neg (Nat.not_le.mpr hR), if_pos hn]
private theorem segCell_above {n m : Nat} (x : Bitstring n) (w : Bitstring m)
    {L R k : Nat} (hL : L ≤ 2 * n) (hR : R ≤ 2 * n) (hn : 2 * n < k) :
    segCell x w L R k = baseCell x w k := by
  unfold segCell
  rw [if_neg (by omega), if_neg (by omega), if_neg (Nat.not_le.mpr hn)]
private theorem segCell_extend_left {n m : Nat} (x : Bitstring n)
    (w : Bitstring m) {L R k : Nat} (hL : 0 < L) (hk : k ≠ L - 1) :
    segCell x w (L - 1) R k = segCell x w L R k := by
  unfold segCell
  by_cases h1 : k < L - 1
  · rw [if_pos h1, if_pos (show k < L by omega)]
  · rw [if_neg h1, if_neg (show ¬ k < L by omega)]
private theorem segCell_shrink_right {n m : Nat} (x : Bitstring n)
    (w : Bitstring m) {L R k : Nat} (hR : 0 < R) (hk : k ≠ R) :
    segCell x w L (R - 1) k = segCell x w L R k := by
  unfold segCell
  by_cases h1 : k < L
  · rw [if_pos h1, if_pos h1]
  · rw [if_neg h1, if_neg h1]
    by_cases h2 : k ≤ R - 1
    · rw [if_pos h2, if_pos (show k ≤ R by omega)]
    · rw [if_neg h2, if_neg (show ¬ k ≤ R by omega)]
private def segTape {n m : Nat} (B : Nat) (x : Bitstring n) (w : Bitstring m)
    (L R : Nat) : Fin (tapeLength (pairLength n m) B) → Option Bool :=
  fun i => segCell x w L R i.val
private theorem segTape_above {n m B : Nat} (x : Bitstring n) (w : Bitstring m)
    {L R : Nat} (hL : L ≤ 2 * n) (hR : R ≤ 2 * n)
    (i : Fin (tapeLength (pairLength n m) B)) (hi : 2 * n < i.val) :
    segTape B x w L R i =
      FixedPairConcatSentinel.sentinelTape B (encodePair x w) i := by
  rw [sentinelTape_eq_baseCell]
  exact segCell_above x w hL hR hi
private theorem holeTape_eq_segTape {n m B : Nat}
    (x : Bitstring n) (w : Bitstring m) :
    FixedPairSeparatorHole.holeTape B x w = segTape B x w (2 * n) (2 * n) := by
  funext i
  unfold FixedPairSeparatorHole.holeTape segTape
  by_cases hi : i.val = 2 * n
  · rw [if_pos hi, segCell_blank x w (by omega) (by omega)]
  · rw [if_neg hi, sentinelTape_eq_baseCell]
    rcases Nat.lt_or_gt_of_ne hi with hlt | hgt
    · rw [segCell_lt x w hlt]
    · rw [segCell_above x w (le_refl _) (le_refl _) hgt]
private theorem compactTape_blank {n m B : Nat} (x : Bitstring n)
    (w : Bitstring m) (i : Fin (tapeLength (pairLength n m) B))
    (hi : i.val ≤ n) : compactTape B x w i = none := by
  unfold compactTape
  rw [dif_pos hi]
private theorem compactTape_query {n m B : Nat} (x : Bitstring n)
    (w : Bitstring m) (i : Fin (tapeLength (pairLength n m) B)) (j : Nat)
    (hj : j < n) (hi : i.val = n + 1 + j) :
    compactTape B x w i = some (x ⟨j, hj⟩) := by
  unfold compactTape
  rw [dif_neg (by omega), dif_pos (by omega)]
  exact congrArg (fun t => some (x t)) (Fin.ext (by show i.val - n - 1 = j; omega))
private theorem compactTape_sentinel {n m B : Nat} (x : Bitstring n)
    (w : Bitstring m) (i : Fin (tapeLength (pairLength n m) B))
    (hi : 2 * n < i.val) : compactTape B x w i = baseCell x w i.val := by
  unfold compactTape
  rw [dif_neg (by omega), dif_neg (by omega)]
  rfl
private theorem segTape_last_eq_compactTape {n m B : Nat}
    (x : Bitstring n) (w : Bitstring m) :
    segTape B x w 0 n = compactTape B x w := by
  funext i
  show segCell x w 0 n i.val = compactTape B x w i
  by_cases h1 : i.val ≤ n
  · rw [compactTape_blank x w i h1, segCell_blank x w (Nat.zero_le _) h1]
  · by_cases h2 : i.val ≤ 2 * n
    · rw [compactTape_query x w i (i.val - n - 1) (by omega) (by omega),
        segCell_block x w (Nat.zero_le _) (by omega) h2,
        queryBit_lt x _ (by omega)]
    · rw [compactTape_sentinel x w i (by omega),
        segCell_above x w (Nat.zero_le _) (by omega) (by omega)]
private theorem erase_data_eq {n m B : Nat} (x : Bitstring n) (w : Bitstring m)
    {k : Nat} (hk : k < n) (h : Fin (tapeLength (pairLength n m) B))
    (hh : h.val = 2 * (n - k) - 1) :
    (fun i => if i = h then none else segTape B x w (2 * (n - k)) (2 * n - k) i) =
      segTape B x w (2 * (n - k) - 1) (2 * n - k) := by
  funext i
  unfold segTape
  by_cases hi : i = h
  · rw [if_pos hi, hi, hh, segCell_blank x w (le_refl _) (by omega)]
  · rw [if_neg hi]
    exact (segCell_extend_left x w (by omega)
      (fun heq => hi (Fin.ext (heq.trans hh.symm)))).symm
private theorem drop_eq {n m B : Nat} (x : Bitstring n) (w : Bitstring m)
    {k : Nat} (hk : k < n) (h : Fin (tapeLength (pairLength n m) B))
    (hh : h.val = 2 * n - k) :
    (fun i => if i = h then some (queryBit x (n - k - 1))
      else segTape B x w (2 * (n - k) - 1) (2 * n - k) i) =
      segTape B x w (2 * (n - k) - 1) (2 * n - k - 1) := by
  funext i
  unfold segTape
  by_cases hi : i = h
  · rw [if_pos hi, hi, hh, segCell_block x w (by omega) (by omega) (by omega),
      show 2 * n - k - n - 1 = n - k - 1 by omega]
  · rw [if_neg hi]
    exact (segCell_shrink_right x w (by omega)
      (fun heq => hi (Fin.ext (heq.trans hh.symm)))).symm
private theorem erase_tag_eq {n m B : Nat} (x : Bitstring n) (w : Bitstring m)
    {k : Nat} (hk : k < n) (h : Fin (tapeLength (pairLength n m) B))
    (hh : h.val = 2 * (n - k) - 2) :
    (fun i => if i = h then none
      else segTape B x w (2 * (n - k) - 1) (2 * n - k - 1) i) =
      segTape B x w (2 * (n - (k + 1))) (2 * n - (k + 1)) := by
  funext i
  unfold segTape
  rw [show 2 * (n - (k + 1)) = 2 * (n - k) - 2 by omega,
    show 2 * n - (k + 1) = 2 * n - k - 1 by omega]
  by_cases hi : i = h
  · rw [if_pos hi, hi, hh, segCell_blank x w (le_refl _) (by omega)]
  · rw [if_neg hi]
    have hstep := segCell_extend_left x w (L := 2 * (n - k) - 1)
      (R := 2 * n - k - 1) (k := i.val) (by omega)
      (fun heq => hi (Fin.ext (by omega)))
    rw [show 2 * (n - k) - 1 - 1 = 2 * (n - k) - 2 by omega] at hstep
    exact hstep.symm
private theorem config_ext {N B : Nat} {c d : Config removalStateCount N B}
    (hstate : c.state = d.state) (hhead : c.head = d.head)
    (htape : c.tape = d.tape) : c = d := by
  cases c
  cases d
  cases hstate
  cases hhead
  cases htape
  rfl
private theorem stepConfig_eq {N B : Nat} (c : Config removalStateCount N B)
    (q' : Fin removalStateCount) (s' : Option Bool) (mv : Move)
    (haction : machine.step c.state (c.tape c.head) = (q', s', mv)) :
    machine.stepConfig c =
      ({ state := q', head := moveHead c.head mv,
         tape := fun i => if i = c.head then s' else c.tape i } :
        Config removalStateCount N B) := by
  apply config_ext
  · show (machine.step c.state (c.tape c.head)).1 = q'
    rw [haction]
  · show moveHead c.head (machine.step c.state (c.tape c.head)).2.2 =
      moveHead c.head mv
    rw [haction]
  · funext i
    show (if i = c.head then (machine.step c.state (c.tape c.head)).2.1
      else c.tape i) = (if i = c.head then s' else c.tape i)
    rw [haction]
private theorem step_keep {N B : Nat} (c : Config removalStateCount N B)
    (q' : Fin removalStateCount) (mv : Move)
    (haction : machine.step c.state (c.tape c.head) = (q', c.tape c.head, mv)) :
    machine.stepConfig c =
      ({ state := q', head := moveHead c.head mv, tape := c.tape } :
        Config removalStateCount N B) := by
  rw [stepConfig_eq c _ _ _ haction]
  apply config_ext
  · rfl
  · rfl
  · change (fun i => if i = c.head then c.tape c.head else c.tape i) = c.tape
    funext i
    by_cases hi : i = c.head <;> simp [hi]
private theorem moveHead_right_val {L : Nat} (h : Fin L) (hlt : h.val + 1 < L) :
    (moveHead h .right).val = h.val + 1 := by
  unfold moveHead
  rw [dif_pos hlt]
private def carryState (b : Bool) : Fin removalStateCount :=
  if b then qCarryT else qCarryF
private def dropState (b : Bool) : Fin removalStateCount :=
  if b then qDropT else qDropF
private theorem carryState_blank (b : Bool) :
    machine.step (carryState b) none = (carryState b, none, .right) := by
  cases b <;> rfl
private theorem carryState_nonblank (b c : Bool) :
    machine.step (carryState b) (some c) = (dropState b, some c, .left) := by
  cases b <;> cases c <;> rfl
private theorem dropState_blank (b : Bool) :
    machine.step (dropState b) none = (qReturn, some b, .left) := by
  cases b <;> rfl
private def fetchConfig {n m : Nat} (B : Nat) (x : Bitstring n)
    (w : Bitstring m) (k : Nat) :
    Config removalStateCount (pairLength n m) B where
  state := qFetch
  head := ⟨2 * (n - k) - 1, by unfold tapeLength pairLength; omega⟩
  tape := segTape B x w (2 * (n - k)) (2 * n - k)
private def carryConfig {n m : Nat} (B : Nat) (x : Bitstring n)
    (w : Bitstring m) (k j : Nat) (hk : k < n) (hj : j ≤ k + 1) :
    Config removalStateCount (pairLength n m) B where
  state := carryState (queryBit x (n - k - 1))
  head := ⟨2 * (n - k) + j, by unfold tapeLength pairLength; omega⟩
  tape := segTape B x w (2 * (n - k) - 1) (2 * n - k)
private def dropConfig {n m : Nat} (B : Nat) (x : Bitstring n)
    (w : Bitstring m) (k : Nat) (hk : k < n) :
    Config removalStateCount (pairLength n m) B where
  state := dropState (queryBit x (n - k - 1))
  head := ⟨2 * n - k, by unfold tapeLength pairLength; omega⟩
  tape := segTape B x w (2 * (n - k) - 1) (2 * n - k)
private def returnConfig {n m : Nat} (B : Nat) (x : Bitstring n)
    (w : Bitstring m) (k j : Nat) (hk : k < n) (hj : j ≤ k + 1) :
    Config removalStateCount (pairLength n m) B where
  state := qReturn
  head := ⟨2 * n - k - 1 - j, by unfold tapeLength pairLength; omega⟩
  tape := segTape B x w (2 * (n - k) - 1) (2 * n - k - 1)
private theorem start_action {n m B : Nat} (x : Bitstring n) (w : Bitstring m) :
    machine.step (startConfig B x w).state
        ((startConfig B x w).tape (startConfig B x w).head) =
      (qFetch, (startConfig B x w).tape (startConfig B x w).head, .left) := by
  rw [(startConfig_of_hole_run x w).2.2.2.2.2]
  rfl
private theorem fetch_action {n m B : Nat} (x : Bitstring n) (w : Bitstring m)
    {k : Nat} (hk : k < n) :
    machine.step (fetchConfig B x w k).state
        ((fetchConfig B x w k).tape (fetchConfig B x w k).head) =
      (carryState (queryBit x (n - k - 1)), none, .right) := by
  have hread : (fetchConfig B x w k).tape (fetchConfig B x w k).head =
      some (queryBit x (n - k - 1)) := by
    show segCell x w (2 * (n - k)) (2 * n - k) (2 * (n - k) - 1) = _
    rw [segCell_lt x w (by omega),
      show 2 * (n - k) - 1 = 2 * (n - k - 1) + 1 by omega]
    exact baseCell_data x w _ (by omega)
  rw [hread]
  unfold carryState
  cases queryBit x (n - k - 1) <;> rfl
private theorem fetch_last_action {n m B : Nat} (x : Bitstring n)
    (w : Bitstring m) :
    machine.step (fetchConfig B x w n).state
        ((fetchConfig B x w n).tape (fetchConfig B x w n).head) =
      (qAccept, (fetchConfig B x w n).tape (fetchConfig B x w n).head, .stay) := by
  have hread : (fetchConfig B x w n).tape (fetchConfig B x w n).head = none := by
    show segCell x w (2 * (n - n)) (2 * n - n) (2 * (n - n) - 1) = none
    exact segCell_blank x w (by omega) (by omega)
  rw [hread]
  rfl
private theorem carry_action {n m B : Nat} (x : Bitstring n) (w : Bitstring m)
    {k j : Nat} (hk : k < n) (hj : j ≤ k) :
    machine.step (carryConfig B x w k j hk (by omega)).state
        ((carryConfig B x w k j hk (by omega)).tape
          (carryConfig B x w k j hk (by omega)).head) =
      (carryState (queryBit x (n - k - 1)),
        (carryConfig B x w k j hk (by omega)).tape
          (carryConfig B x w k j hk (by omega)).head, .right) := by
  have hread : (carryConfig B x w k j hk (by omega)).tape
      (carryConfig B x w k j hk (by omega)).head = none := by
    show segCell x w (2 * (n - k) - 1) (2 * n - k) (2 * (n - k) + j) = none
    exact segCell_blank x w (by omega) (by omega)
  rw [hread]
  exact carryState_blank _
private theorem carry_end_action {n m B : Nat} (x : Bitstring n)
    (w : Bitstring m) {k : Nat} (hk : k < n) :
    machine.step (carryConfig B x w k (k + 1) hk (le_refl _)).state
        ((carryConfig B x w k (k + 1) hk (le_refl _)).tape
          (carryConfig B x w k (k + 1) hk (le_refl _)).head) =
      (dropState (queryBit x (n - k - 1)),
        (carryConfig B x w k (k + 1) hk (le_refl _)).tape
          (carryConfig B x w k (k + 1) hk (le_refl _)).head, .left) := by
  obtain ⟨c, hread⟩ : ∃ c, (carryConfig B x w k (k + 1) hk (le_refl _)).tape
      (carryConfig B x w k (k + 1) hk (le_refl _)).head = some c := by
    show ∃ c, segCell x w (2 * (n - k) - 1) (2 * n - k) (2 * (n - k) + (k + 1)) =
      some c
    by_cases hk0 : k = 0
    · subst hk0
      rw [segCell_above x w (by omega) (by omega) (by omega)]
      exact baseCell_isSome x w _ (by unfold pairLength; omega)
    · rw [segCell_block x w (by omega) (by omega) (by omega)]
      exact ⟨_, rfl⟩
  rw [hread]
  exact carryState_nonblank _ _
private theorem drop_action {n m B : Nat} (x : Bitstring n) (w : Bitstring m)
    {k : Nat} (hk : k < n) :
    machine.step (dropConfig B x w k hk).state
        ((dropConfig B x w k hk).tape (dropConfig B x w k hk).head) =
      (qReturn, some (queryBit x (n - k - 1)), .left) := by
  have hread : (dropConfig B x w k hk).tape (dropConfig B x w k hk).head =
      none := by
    show segCell x w (2 * (n - k) - 1) (2 * n - k) (2 * n - k) = none
    exact segCell_blank x w (by omega) (le_refl _)
  rw [hread]
  exact dropState_blank _
private theorem return_action {n m B : Nat} (x : Bitstring n) (w : Bitstring m)
    {k j : Nat} (hk : k < n) (hj : j ≤ k) :
    machine.step (returnConfig B x w k j hk (by omega)).state
        ((returnConfig B x w k j hk (by omega)).tape
          (returnConfig B x w k j hk (by omega)).head) =
      (qReturn, (returnConfig B x w k j hk (by omega)).tape
        (returnConfig B x w k j hk (by omega)).head, .left) := by
  have hread : (returnConfig B x w k j hk (by omega)).tape
      (returnConfig B x w k j hk (by omega)).head = none := by
    show segCell x w (2 * (n - k) - 1) (2 * n - k - 1) (2 * n - k - 1 - j) = none
    exact segCell_blank x w (by omega) (by omega)
  rw [hread]
  rfl
private theorem return_end_action {n m B : Nat} (x : Bitstring n)
    (w : Bitstring m) {k : Nat} (hk : k < n) :
    machine.step (returnConfig B x w k (k + 1) hk (le_refl _)).state
        ((returnConfig B x w k (k + 1) hk (le_refl _)).tape
          (returnConfig B x w k (k + 1) hk (le_refl _)).head) =
      (qFetch, none, .left) := by
  have hread : (returnConfig B x w k (k + 1) hk (le_refl _)).tape
      (returnConfig B x w k (k + 1) hk (le_refl _)).head = some false := by
    show segCell x w (2 * (n - k) - 1) (2 * n - k - 1) (2 * n - k - 1 - (k + 1)) =
      some false
    rw [segCell_lt x w (by omega),
      show 2 * n - k - 1 - (k + 1) = 2 * (n - k - 1) by omega]
    exact baseCell_tag x w _ (by omega)
  rw [hread]
  rfl
private theorem step_start {n m B : Nat} (x : Bitstring n) (w : Bitstring m) :
    machine.stepConfig (startConfig B x w) = fetchConfig B x w 0 := by
  rw [step_keep _ _ _ (start_action x w)]
  apply config_ext
  · rfl
  · apply Fin.ext
    show 2 * n - 1 = 2 * (n - 0) - 1
    omega
  · show FixedPairSeparatorHole.holeTape B x w = segTape B x w (2 * (n - 0)) (2 * n - 0)
    rw [Nat.sub_zero, Nat.sub_zero]
    exact holeTape_eq_segTape x w
private theorem step_fetch {n m B : Nat} (x : Bitstring n) (w : Bitstring m)
    {k : Nat} (hk : k < n) :
    machine.stepConfig (fetchConfig B x w k) =
      carryConfig B x w k 0 hk (Nat.zero_le _) := by
  rw [stepConfig_eq _ _ _ _ (fetch_action x w hk)]
  apply config_ext
  · rfl
  · apply Fin.ext
    rw [moveHead_right_val _ (by
      show 2 * (n - k) - 1 + 1 < tapeLength (pairLength n m) B
      unfold tapeLength pairLength
      omega)]
    show 2 * (n - k) - 1 + 1 = 2 * (n - k) + 0
    omega
  · exact erase_data_eq x w hk _ rfl
private theorem step_fetch_last {n m B : Nat} (x : Bitstring n)
    (w : Bitstring m) :
    machine.stepConfig (fetchConfig B x w n) = finalConfig B x w := by
  rw [step_keep _ _ _ (fetch_last_action x w)]
  apply config_ext
  · rfl
  · apply Fin.ext
    show 2 * (n - n) - 1 = 0
    omega
  · show segTape B x w (2 * (n - n)) (2 * n - n) = compactTape B x w
    rw [Nat.sub_self, Nat.mul_zero, show 2 * n - n = n by omega]
    exact segTape_last_eq_compactTape x w
private theorem step_carry {n m B : Nat} (x : Bitstring n) (w : Bitstring m)
    {k j : Nat} (hk : k < n) (hj : j ≤ k) :
    machine.stepConfig (carryConfig B x w k j hk (by omega)) =
      carryConfig B x w k (j + 1) hk (by omega) := by
  rw [step_keep _ _ _ (carry_action x w hk hj)]
  apply config_ext
  · rfl
  · apply Fin.ext
    rw [moveHead_right_val _ (by
      show 2 * (n - k) + j + 1 < tapeLength (pairLength n m) B
      unfold tapeLength pairLength
      omega)]
    rfl
  · rfl
private theorem step_carry_end {n m B : Nat} (x : Bitstring n) (w : Bitstring m)
    {k : Nat} (hk : k < n) :
    machine.stepConfig (carryConfig B x w k (k + 1) hk (le_refl _)) =
      dropConfig B x w k hk := by
  rw [step_keep _ _ _ (carry_end_action x w hk)]
  apply config_ext
  · rfl
  · apply Fin.ext
    show 2 * (n - k) + (k + 1) - 1 = 2 * n - k
    omega
  · rfl
private theorem step_drop {n m B : Nat} (x : Bitstring n) (w : Bitstring m)
    {k : Nat} (hk : k < n) :
    machine.stepConfig (dropConfig B x w k hk) =
      returnConfig B x w k 0 hk (Nat.zero_le _) := by
  rw [stepConfig_eq _ _ _ _ (drop_action x w hk)]
  apply config_ext
  · rfl
  · apply Fin.ext
    show 2 * n - k - 1 = 2 * n - k - 1 - 0
    omega
  · exact drop_eq x w hk _ rfl
private theorem step_return {n m B : Nat} (x : Bitstring n) (w : Bitstring m)
    {k j : Nat} (hk : k < n) (hj : j ≤ k) :
    machine.stepConfig (returnConfig B x w k j hk (by omega)) =
      returnConfig B x w k (j + 1) hk (by omega) := by
  rw [step_keep _ _ _ (return_action x w hk hj)]
  apply config_ext
  · rfl
  · apply Fin.ext
    show 2 * n - k - 1 - j - 1 = 2 * n - k - 1 - (j + 1)
    omega
  · rfl
private theorem step_return_end {n m B : Nat} (x : Bitstring n)
    (w : Bitstring m) {k : Nat} (hk : k < n) :
    machine.stepConfig (returnConfig B x w k (k + 1) hk (le_refl _)) =
      fetchConfig B x w (k + 1) := by
  rw [stepConfig_eq _ _ _ _ (return_end_action x w hk)]
  apply config_ext
  · rfl
  · apply Fin.ext
    show 2 * n - k - 1 - (k + 1) - 1 = 2 * (n - (k + 1)) - 1
    omega
  · exact erase_tag_eq x w hk _
      (by show 2 * n - k - 1 - (k + 1) = 2 * (n - k) - 2; omega)
private theorem run_to_carry {n m B : Nat} (x : Bitstring n) (w : Bitstring m)
    {k : Nat} (hk : k < n) (j : Nat) (hj : j ≤ k + 1) :
    machine.run (j + 1) (fetchConfig B x w k) = carryConfig B x w k j hk hj := by
  induction j with
  | zero => exact step_fetch x w hk
  | succ j ih =>
      rw [UniformTM.run, ih (by omega)]
      exact step_carry x w hk (by omega)
private theorem run_to_drop {n m B : Nat} (x : Bitstring n) (w : Bitstring m)
    {k : Nat} (hk : k < n) :
    machine.run (k + 3) (fetchConfig B x w k) = dropConfig B x w k hk := by
  rw [show k + 3 = (k + 1 + 1) + 1 by omega, UniformTM.run,
    run_to_carry x w hk (k + 1) (le_refl _)]
  exact step_carry_end x w hk
private theorem run_to_return {n m B : Nat} (x : Bitstring n) (w : Bitstring m)
    {k : Nat} (hk : k < n) (j : Nat) (hj : j ≤ k + 1) :
    machine.run (k + 4 + j) (fetchConfig B x w k) =
      returnConfig B x w k j hk hj := by
  induction j with
  | zero =>
      rw [show k + 4 + 0 = (k + 3) + 1 by omega, UniformTM.run, run_to_drop x w hk]
      exact step_drop x w hk
  | succ j ih =>
      rw [show k + 4 + (j + 1) = (k + 4 + j) + 1 by omega, UniformTM.run,
        ih (by omega)]
      exact step_return x w hk (by omega)
private theorem run_round {n m B : Nat} (x : Bitstring n) (w : Bitstring m)
    {k : Nat} (hk : k < n) :
    machine.run (2 * k + 6) (fetchConfig B x w k) = fetchConfig B x w (k + 1) := by
  rw [show 2 * k + 6 = (k + 4 + (k + 1)) + 1 by omega, UniformTM.run,
    run_to_return x w hk (k + 1) (le_refl _)]
  exact step_return_end x w hk
private def roundStart : Nat → Nat
  | 0 => 1
  | k + 1 => roundStart k + (2 * k + 6)
private theorem roundStart_succ (k : Nat) :
    roundStart (k + 1) = roundStart k + (2 * k + 6) :=
  rfl
private theorem roundStart_closed (k : Nat) : roundStart k = 1 + k * (k + 5) := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [roundStart_succ, ih]
      ring
private theorem clock_eq_roundStart (n : Nat) : clock n = roundStart n + 1 := by
  rw [roundStart_closed]
  unfold clock
  omega
private theorem roundStart_lt {k k' : Nat} (h : k < k') :
    roundStart k < roundStart k' := by
  rw [roundStart_closed, roundStart_closed]
  have := Nat.mul_le_mul (Nat.succ_le_of_lt h) (Nat.add_le_add_right h.le 5)
  rw [Nat.succ_mul] at this
  omega
private theorem run_fetch {n m B : Nat} (x : Bitstring n) (w : Bitstring m)
    {k : Nat} (hk : k ≤ n) :
    machine.run (roundStart k) (startConfig B x w) = fetchConfig B x w k := by
  induction k with
  | zero => exact step_start x w
  | succ k ih =>
      rw [roundStart_succ, machine.run_add, ih (by omega)]
      exact run_round x w (by omega)
/-! ## Exact valid run -/
/-- Required exact full-configuration theorem, for every query length, witness
length, and allocation, including `n = 0`, `m = 0`, and `B = 0`. -/
theorem run_encoded_exact {n m : Nat} (B : Nat)
    (x : Bitstring n) (w : Bitstring m) :
    machine.run (clock n) (startConfig B x w) = finalConfig B x w := by
  rw [clock_eq_roundStart, machine.run_add, run_fetch x w (le_refl n)]
  exact step_fetch_last x w
/-- Literal final fields: accept control, head at the origin, compact tape. -/
theorem final_literal_fields {n m B : Nat} (x : Bitstring n) (w : Bitstring m) :
    (machine.run (clock n) (startConfig B x w)).state = qAccept ∧
    (machine.run (clock n) (startConfig B x w)).state = machine.accept ∧
    (machine.run (clock n) (startConfig B x w)).head.val = 0 ∧
    (machine.run (clock n) (startConfig B x w)).tape = compactTape B x w := by
  rw [run_encoded_exact]
  exact ⟨rfl, rfl, rfl, rfl⟩
/-- Post-clock behavior: the accepting configuration is absorbing. -/
theorem run_after_clock {n m B : Nat} (x : Bitstring n) (w : Bitstring m)
    (extra : Nat) :
    machine.run (clock n + extra) (startConfig B x w) = finalConfig B x w := by
  rw [machine.run_add, run_encoded_exact,
    machine.run_accept (finalConfig B x w) rfl extra]
private theorem run_in_round {n m : Nat} (x : Bitstring n) (w : Bitstring m)
    {k : Nat} (hk : k < n) (d : Nat) (hd : d ≤ 2 * k + 5) :
    d = 0 ∨
    (∃ j, ∃ hj : j ≤ k + 1, d = j + 1 ∧
      ∀ B, machine.run d (fetchConfig B x w k) = carryConfig B x w k j hk hj) ∨
    (d = k + 3 ∧
      ∀ B, machine.run d (fetchConfig B x w k) = dropConfig B x w k hk) ∨
    (∃ j, ∃ hj : j ≤ k + 1, d = k + 4 + j ∧
      ∀ B, machine.run d (fetchConfig B x w k) =
        returnConfig B x w k j hk hj) := by
  by_cases h0 : d = 0
  · exact Or.inl h0
  · by_cases h1 : d ≤ k + 2
    · obtain ⟨j, rfl⟩ : ∃ j, d = j + 1 := ⟨d - 1, by omega⟩
      exact Or.inr (Or.inl
        ⟨j, by omega, rfl, fun B => run_to_carry x w hk j (by omega)⟩)
    · by_cases h2 : d = k + 3
      · subst h2
        exact Or.inr (Or.inr (Or.inl ⟨rfl, fun B => run_to_drop x w hk⟩))
      · obtain ⟨j, rfl⟩ : ∃ j, d = k + 4 + j := ⟨d - (k + 4), by omega⟩
        exact Or.inr (Or.inr (Or.inr
          ⟨j, by omega, rfl, fun B => run_to_return x w hk j (by omega)⟩))
private theorem roundStart_decompose (s : Nat) (hs : 1 ≤ s) :
    ∃ k d, d ≤ 2 * k + 5 ∧ s = roundStart k + d := by
  induction s with
  | zero => omega
  | succ s ih =>
      by_cases hs0 : s = 0
      · subst hs0
        exact ⟨0, 0, by omega, rfl⟩
      · obtain ⟨k, d, hd, rfl⟩ := ih (by omega)
        by_cases hd' : d + 1 ≤ 2 * k + 5
        · exact ⟨k, d + 1, hd', by omega⟩
        · refine ⟨k + 1, 0, by omega, ?_⟩
          rw [roundStart_succ]
          omega
private theorem run_trace_cases {n m : Nat} (x : Bitstring n) (w : Bitstring m)
    (s : Nat) (hs : s ≤ clock n) :
    (s = 0 ∧ ∀ B, machine.run s (startConfig B x w) = startConfig B x w) ∨
    (∃ k, ∃ hk : k < n, ∃ j, ∃ hj : j ≤ k + 1,
      ∀ B, machine.run s (startConfig B x w) = carryConfig B x w k j hk hj) ∨
    (∃ k, ∃ hk : k < n,
      ∀ B, machine.run s (startConfig B x w) = dropConfig B x w k hk) ∨
    (∃ k, ∃ hk : k < n, ∃ j, ∃ hj : j ≤ k + 1, s = roundStart k + (k + 4 + j) ∧
      ∀ B, machine.run s (startConfig B x w) = returnConfig B x w k j hk hj) ∨
    (∃ k, k ≤ n ∧ ∀ B, machine.run s (startConfig B x w) = fetchConfig B x w k) ∨
    (s = clock n ∧
      ∀ B, machine.run s (startConfig B x w) = finalConfig B x w) := by
  by_cases h0 : s = 0
  · subst h0
    exact Or.inl ⟨rfl, fun B => rfl⟩
  by_cases hclock : s = clock n
  · subst hclock
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      ⟨rfl, fun B => run_encoded_exact B x w⟩))))
  have hs' : s ≤ roundStart n := by
    rw [clock_eq_roundStart] at hs hclock
    omega
  obtain ⟨k, d, hd, rfl⟩ := roundStart_decompose s (by omega)
  have hkn : k ≤ n := by
    by_contra hgt
    have := roundStart_lt (show n < k by omega)
    omega
  have hrun : ∀ B, machine.run (roundStart k + d) (startConfig B x w) =
      machine.run d (fetchConfig B x w k) := by
    intro B
    rw [machine.run_add, run_fetch x w hkn]
  by_cases hlt : k < n
  · rcases run_in_round x w hlt d hd with
      hd0 | ⟨j, hj, rfl, hc⟩ | ⟨rfl, hc⟩ | ⟨j, hj, rfl, hc⟩
    · subst hd0
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        ⟨k, hkn, fun B => (hrun B).trans rfl⟩))))
    · exact Or.inr (Or.inl ⟨k, hlt, j, hj, fun B => (hrun B).trans (hc B)⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨k, hlt, fun B => (hrun B).trans (hc B)⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inl
        ⟨k, hlt, j, hj, rfl, fun B => (hrun B).trans (hc B)⟩)))
  · have hkeq : k = n := by omega
    subst hkeq
    have hd0 : d = 0 := by omega
    subst hd0
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      ⟨k, le_refl _, fun B => (hrun B).trans rfl⟩))))
private theorem clock_succ_sub_two (k : Nat) :
    clock (k + 1) - 2 = roundStart k + (k + 4 + (k + 1)) := by
  rw [clock_eq_roundStart, roundStart_succ]
  omega
private theorem trace_facts {n m B : Nat} (x : Bitstring n) (w : Bitstring m)
    (s : Nat) (hs : s ≤ clock n) :
    let c := machine.run s (startConfig B x w)
    (s < clock n → c.state.val ≤ 6) ∧
    c.head.val ≤ 2 * n + 1 ∧
    (∀ i : Fin (tapeLength (pairLength n m) B), 2 * n < i.val →
      c.tape i = FixedPairConcatSentinel.sentinelTape B (encodePair x w) i) ∧
    ((machine.step c.state (c.tape c.head)).2.2 = .right → c.head.val ≤ 2 * n) ∧
    (s ≠ clock n - 2 →
      (machine.step c.state (c.tape c.head)).2.2 = .left → 0 < c.head.val) := by
  dsimp
  rcases run_trace_cases x w s hs with
    ⟨hs0, h⟩ | ⟨k, hk, j, hj, h⟩ | ⟨k, hk, h⟩ | ⟨k, hk, j, hj, hst, h⟩ |
    ⟨k, hk, h⟩ | ⟨hs', h⟩
  · rw [h B, start_action x w]
    refine ⟨fun _ => Nat.zero_le _, by show 2 * n ≤ 2 * n + 1; omega,
      fun i hi => ?_, fun hmv => by simp at hmv, fun hne _ => ?_⟩
    · show FixedPairSeparatorHole.holeTape B x w i = _
      unfold FixedPairSeparatorHole.holeTape
      rw [if_neg (by omega)]
    · show 0 < 2 * n
      subst hs0
      rcases Nat.eq_zero_or_pos n with hn | hn
      · subst hn
        exact absurd rfl hne
      · omega
  · rw [h B]
    refine ⟨fun _ => ?_, by show 2 * (n - k) + j ≤ 2 * n + 1; omega,
      fun i hi => segTape_above x w (by omega) (by omega) i hi, ?_, ?_⟩
    · show (carryState (queryBit x (n - k - 1))).val ≤ 6
      unfold carryState
      cases queryBit x (n - k - 1) <;> decide
    · by_cases hjk : j ≤ k
      · rw [carry_action x w hk hjk]
        intro _
        show 2 * (n - k) + j ≤ 2 * n
        omega
      · obtain rfl : j = k + 1 := by omega
        rw [carry_end_action x w hk]
        intro hmv
        simp at hmv
    · by_cases hjk : j ≤ k
      · rw [carry_action x w hk hjk]
        intro _ hmv
        simp at hmv
      · obtain rfl : j = k + 1 := by omega
        rw [carry_end_action x w hk]
        intro _ _
        show 0 < 2 * (n - k) + (k + 1)
        omega
  · rw [h B, drop_action x w hk]
    refine ⟨fun _ => ?_, by show 2 * n - k ≤ 2 * n + 1; omega,
      fun i hi => segTape_above x w (by omega) (by omega) i hi,
      fun hmv => by simp at hmv, fun _ _ => by show 0 < 2 * n - k; omega⟩
    show (dropState (queryBit x (n - k - 1))).val ≤ 6
    unfold dropState
    cases queryBit x (n - k - 1) <;> decide
  · rw [h B]
    refine ⟨fun _ => le_refl _, by show 2 * n - k - 1 - j ≤ 2 * n + 1; omega,
      fun i hi => segTape_above x w (by omega) (by omega) i hi, ?_, ?_⟩
    · by_cases hjk : j ≤ k
      · rw [return_action x w hk hjk]
        intro hmv
        simp at hmv
      · obtain rfl : j = k + 1 := by omega
        rw [return_end_action x w hk]
        intro hmv
        simp at hmv
    · by_cases hjk : j ≤ k
      · rw [return_action x w hk hjk]
        intro _ _
        show 0 < 2 * n - k - 1 - j
        omega
      · obtain rfl : j = k + 1 := by omega
        rw [return_end_action x w hk]
        intro hne _
        show 0 < 2 * n - k - 1 - (k + 1)
        by_cases hkn : k + 1 = n
        · exfalso
          apply hne
          rw [hst, ← hkn, clock_succ_sub_two]
        · omega
  · rw [h B]
    refine ⟨fun _ => by show 1 ≤ 6; decide,
      by show 2 * (n - k) - 1 ≤ 2 * n + 1; omega,
      fun i hi => segTape_above x w (by omega) (by omega) i hi, ?_, ?_⟩
    · by_cases hkn : k < n
      · rw [fetch_action x w hkn]
        intro _
        show 2 * (n - k) - 1 ≤ 2 * n
        omega
      · obtain rfl : k = n := by omega
        rw [fetch_last_action x w]
        intro hmv
        simp at hmv
    · by_cases hkn : k < n
      · rw [fetch_action x w hkn]
        intro _ hmv
        simp at hmv
      · obtain rfl : k = n := by omega
        rw [fetch_last_action x w]
        intro _ hmv
        simp at hmv
  · rw [h B]
    refine ⟨fun hlt => absurd hs' (Nat.ne_of_lt hlt), Nat.zero_le _,
      fun i hi => ?_, fun _ => Nat.zero_le _, fun _ hleft => ?_⟩
    · show compactTape B x w i = _
      unfold compactTape
      rw [dif_neg (by omega), dif_neg (by omega)]
    · rw [show (finalConfig B x w).state = machine.accept from rfl,
        machine.step_accept] at hleft
      cases hleft
/-! ## Footprint, terminal behavior, boundaries, and budget independence -/
/-- Strict terminal behavior: neither verdict control appears before the
clock. -/
theorem noEarlyTerminal {n m B : Nat} (x : Bitstring n) (w : Bitstring m)
    (s : Nat) (hs : s < clock n) :
    (machine.run s (startConfig B x w)).state ≠ qAccept ∧
    (machine.run s (startConfig B x w)).state ≠ qReject := by
  have hwork := (trace_facts (B := B) x w s (Nat.le_of_lt hs)).1 hs
  constructor
  · intro h
    rw [h] at hwork
    exact absurd hwork (by decide)
  · intro h
    rw [h] at hwork
    exact absurd hwork (by decide)
/-- Sharp footprint: the head never passes cell `2n+1`, that bound is attained
at time three on every nonempty query, and every cell above `2n` (witness,
marker, blank suffix) is literally untouched at every time through the
clock. -/
theorem footprint_through_clock {n m B : Nat}
    (x : Bitstring n) (w : Bitstring m) :
    (∀ s, s ≤ clock n →
      (machine.run s (startConfig B x w)).head.val ≤ 2 * n + 1) ∧
    (0 < n → (machine.run 3 (startConfig B x w)).head.val = 2 * n + 1) ∧
    (∀ s, s ≤ clock n → ∀ i : Fin (tapeLength (pairLength n m) B),
      2 * n < i.val →
      (machine.run s (startConfig B x w)).tape i =
        FixedPairConcatSentinel.sentinelTape B (encodePair x w) i) := by
  refine ⟨fun s hs => (trace_facts (B := B) x w s hs).2.1, fun hn => ?_,
    fun s hs i hi => (trace_facts (B := B) x w s hs).2.2.1 i hi⟩
  rw [show (3 : Nat) = roundStart 0 + (1 + 1) from rfl, machine.run_add,
    run_fetch x w (Nat.zero_le _), run_to_carry x w hn 1 (by omega)]
  show 2 * (n - 0) + 1 = 2 * n + 1
  omega
/-- Boundary behavior.  Every right move starts at or below cell `2n`, so the
right clamp of `moveHead` never fires on any budget including `B = 0`.  The
left clamp fires at exactly one time on every valid pair: at `clock n - 2` the
head is at cell `0` and the fired row moves left (the origin test; for `n = 0`
this is the start transition), and every other left move through the clock
starts at a positive address. -/
theorem boundary_clamps {n m B : Nat} (x : Bitstring n) (w : Bitstring m) :
    (∀ s, s < clock n →
      let c := machine.run s (startConfig B x w)
    (machine.step c.state (c.tape c.head)).2.2 = .right →
        c.head.val ≤ 2 * n ∧ c.head.val + 1 < tapeLength (pairLength n m) B) ∧
    (∀ s, s < clock n → s ≠ clock n - 2 →
      let c := machine.run s (startConfig B x w)
      (machine.step c.state (c.tape c.head)).2.2 = .left → 0 < c.head.val) ∧
    (let c := machine.run (clock n - 2) (startConfig B x w)
     c.head.val = 0 ∧ (machine.step c.state (c.tape c.head)).2.2 = .left) := by
  dsimp
  refine ⟨fun s hs hmv => ?_, fun s hs hne hmv =>
    (trace_facts (B := B) x w s (Nat.le_of_lt hs)).2.2.2.2 hne hmv, ?_⟩
  · have hle := (trace_facts (B := B) x w s (Nat.le_of_lt hs)).2.2.2.1 hmv
    refine ⟨hle, ?_⟩
    unfold tapeLength pairLength
    omega
  · cases n with
    | zero =>
        rw [show clock 0 - 2 = 0 from rfl]
        refine ⟨rfl, ?_⟩
        show (machine.step (startConfig B x w).state
          ((startConfig B x w).tape (startConfig B x w).head)).2.2 = .left
        rw [start_action x w]
    | succ k =>
        rw [clock_succ_sub_two, machine.run_add, run_fetch x w (Nat.le_succ k),
          run_to_return x w (Nat.lt_succ_self k) (k + 1) (le_refl _),
          return_end_action x w (Nat.lt_succ_self k)]
        refine ⟨?_, rfl⟩
        show 2 * (k + 1) - k - 1 - (k + 1) = 0
        omega
/-- Execution is independent of padding: state and natural head agree, and
every pair of common addresses holds the same symbol, at every time through the
clock, including the minimal allocation `B = 0`. -/
theorem run_budget_independent {n m : Nat}
    (B B' : Nat) (x : Bitstring n) (w : Bitstring m)
    (s : Nat) (hs : s ≤ clock n) :
    (machine.run s (startConfig B x w)).state =
      (machine.run s (startConfig B' x w)).state ∧
    (machine.run s (startConfig B x w)).head.val =
      (machine.run s (startConfig B' x w)).head.val ∧
    (∀ (i : Fin (tapeLength (pairLength n m) B))
        (i' : Fin (tapeLength (pairLength n m) B')),
      i.val = i'.val →
      (machine.run s (startConfig B x w)).tape i =
        (machine.run s (startConfig B' x w)).tape i') := by
  rcases run_trace_cases x w s hs with
    ⟨_, h⟩ | ⟨k, hk, j, hj, h⟩ | ⟨k, hk, h⟩ | ⟨k, hk, j, hj, _, h⟩ |
    ⟨k, hk, h⟩ | ⟨_, h⟩
  all_goals rw [h B, h B']
  all_goals refine ⟨rfl, rfl, fun i i' hii' => ?_⟩
  · show FixedPairSeparatorHole.holeTape B x w i =
      FixedPairSeparatorHole.holeTape B' x w i'
    simp [FixedPairSeparatorHole.holeTape, FixedPairConcatSentinel.sentinelTape,
      hii']
  all_goals first
    | (show compactTape B x w i = compactTape B' x w i'
       simp [compactTape, FixedPairConcatSentinel.sentinelTape, hii'])
    | (show segCell x w _ _ i.val = segCell x w _ _ i'.val
       rw [hii'])
/-! ## Exact final tape -/
/-- Pointwise final layout `[n+1 blanks][x][w][marker][blanks]`: cells `0..n`
are blank, the query data occupies `n+1..2n`, the witness `2n+1..2n+m`, the
marker is at `pairLength n m`, and every cell above it is blank. -/
theorem final_tape_behavior {n m B : Nat} (x : Bitstring n) (w : Bitstring m) :
    let cF := machine.run (clock n) (startConfig B x w)
    (∀ i : Fin (tapeLength (pairLength n m) B), i.val ≤ n → cF.tape i = none) ∧
    (∀ j : Fin n,
      cF.tape ⟨n + 1 + j.val, by unfold tapeLength pairLength; omega⟩ =
        some (x j)) ∧
    (∀ j : Fin m,
      cF.tape ⟨2 * n + 1 + j.val, by unfold tapeLength pairLength; omega⟩ =
        some (w j)) ∧
    cF.tape ⟨pairLength n m, by unfold tapeLength; omega⟩ = some true ∧
    (∀ i : Fin (tapeLength (pairLength n m) B),
      pairLength n m < i.val → cF.tape i = none) := by
  dsimp
  rw [(final_literal_fields x w).2.2.2]
  refine ⟨fun i hi => compactTape_blank x w i hi,
    fun j => compactTape_query x w _ j.val j.isLt rfl, fun j => ?_, ?_,
    fun i hi => ?_⟩
  · rw [compactTape_sentinel x w _ (by show 2 * n < 2 * n + 1 + j.val; omega)]
    exact baseCell_witness x w j.val j.isLt
  · rw [compactTape_sentinel x w _
      (by show 2 * n < pairLength n m; unfold pairLength; omega)]
    exact baseCell_marker x w
  · rw [compactTape_sentinel x w i (by unfold pairLength at hi; omega)]
    exact baseCell_beyond x w i.val hi
/-- The query and the witness are physically contiguous: cells `n+1..2n+m`
hold `Fin.append x w` in order.  The prefix `0..n` is blank, so this is the
compacted content offset by `n+1` cells, not yet the headerless layout
`x ++ w` at the origin. -/
theorem final_content_contiguous {n m B : Nat}
    (x : Bitstring n) (w : Bitstring m) (j : Fin (n + m)) :
    (machine.run (clock n) (startConfig B x w)).tape
      ⟨n + 1 + j.val, by unfold tapeLength pairLength; omega⟩ =
        some (Fin.append x w j) := by
  rw [(final_literal_fields x w).2.2.2]
  by_cases hj : j.val < n
  · have hcast : j = Fin.castAdd m ⟨j.val, hj⟩ := Fin.ext rfl
    have happ := Fin.append_left x w ⟨j.val, hj⟩
    rw [← hcast] at happ
    rw [happ]
    exact compactTape_query x w _ j.val hj rfl
  · have hcast : j = Fin.natAdd n ⟨j.val - n, by omega⟩ :=
      Fin.ext (by show j.val = n + (j.val - n); omega)
    have happ := Fin.append_right x w ⟨j.val - n, by omega⟩
    rw [← hcast] at happ
    rw [happ, compactTape_sentinel x w _ (by show 2 * n < n + 1 + j.val; omega)]
    show baseCell x w (n + 1 + j.val) = some (w ⟨j.val - n, by omega⟩)
    rw [show n + 1 + j.val = 2 * n + 1 + (j.val - n) by omega]
    exact baseCell_witness x w (j.val - n) (by omega)
/-! ## Zero cases and bundled contract -/
/-- Explicit zero cases.  Empty query: two transitions leave the hole tape
unchanged and halt at the origin, which is the hole.  Empty witness: the
compacted query is immediately followed by the marker, which the first round's
lookahead reads at `2n+1`.  Zero budget: the allocation is exactly `N + 1`
cells and the phase runs exactly, because the head never passes `2n+1 ≤ N`. -/
theorem zero_cases {n m : Nat} (B : Nat) :
    (∀ (x : Bitstring 0) (w : Bitstring m),
      clock 0 = 2 ∧
      machine.run (clock 0) (startConfig B x w) = finalConfig B x w ∧
      (machine.run (clock 0) (startConfig B x w)).head.val = 0 ∧
      (machine.run (clock 0) (startConfig B x w)).tape =
        (startConfig B x w).tape) ∧
    (∀ (x : Bitstring n) (w : Bitstring 0),
      pairLength n 0 = 2 * n + 1 ∧
      machine.run (clock n) (startConfig B x w) = finalConfig B x w ∧
      (machine.run (clock n) (startConfig B x w)).tape
        ⟨2 * n + 1, by unfold tapeLength pairLength; omega⟩ = some true) ∧
    (∀ (x : Bitstring n) (w : Bitstring m),
      tapeLength (pairLength n m) 0 = pairLength n m + 1 ∧
      machine.run (clock n) (startConfig 0 x w) = finalConfig 0 x w) := by
  refine ⟨fun x w => ⟨rfl, run_encoded_exact B x w, ?_, ?_⟩,
    fun x w => ⟨rfl, run_encoded_exact B x w,
      (final_tape_behavior x w).2.2.2.1⟩,
    fun x w => ⟨rfl, run_encoded_exact 0 x w⟩⟩
  · rw [run_encoded_exact]
    rfl
  · rw [(final_literal_fields x w).2.2.2]
    show compactTape B x w = FixedPairSeparatorHole.holeTape B x w
    funext i
    unfold compactTape FixedPairSeparatorHole.holeTape
    by_cases hi : i.val = 0
    · rw [dif_pos (show i.val ≤ 0 by omega), if_pos (show i.val = 2 * 0 by omega)]
    · rw [dif_neg (show ¬ i.val ≤ 0 by omega),
        dif_neg (show ¬ i.val ≤ 2 * 0 by omega),
        if_neg (show ¬ i.val = 2 * 0 by omega)]
/-- The bundled valid-pair contract: exact hole handoff, exact final
configuration at the structural clock, strict preterminality, sharp footprint,
literal preservation of every cell above `2n` throughout, literal acceptance at
the origin, the blank prefix `0..n`, and the contiguous content block at
`n+1..2n+m`.  Boundary behavior and budget independence are proved separately
by `boundary_clamps` and `run_budget_independent`. -/
theorem phase_contract {n m B : Nat} (x : Bitstring n) (w : Bitstring m) :
    let c₀ := startConfig B x w
    c₀.head = (FixedPairSeparatorHole.finalConfig B x w).head ∧
    c₀.tape = (FixedPairSeparatorHole.finalConfig B x w).tape ∧
    machine.run (clock n) c₀ = finalConfig B x w ∧
    (∀ s, s < clock n →
      (machine.run s c₀).state ≠ qAccept ∧ (machine.run s c₀).state ≠ qReject) ∧
    (∀ s, s ≤ clock n → (machine.run s c₀).head.val ≤ 2 * n + 1) ∧
    (∀ s, s ≤ clock n → ∀ i : Fin (tapeLength (pairLength n m) B),
      2 * n < i.val →
      (machine.run s c₀).tape i =
        FixedPairConcatSentinel.sentinelTape B (encodePair x w) i) ∧
    (machine.run (clock n) c₀).state = qAccept ∧
    (machine.run (clock n) c₀).head.val = 0 ∧
    (∀ i : Fin (tapeLength (pairLength n m) B), i.val ≤ n →
      (machine.run (clock n) c₀).tape i = none) ∧
    (∀ j : Fin (n + m),
      (machine.run (clock n) c₀).tape
        ⟨n + 1 + j.val, by unfold tapeLength pairLength; omega⟩ =
          some (Fin.append x w j)) := by
  dsimp
  exact ⟨rfl, rfl, run_encoded_exact B x w, fun s hs => noEarlyTerminal x w s hs,
    (footprint_through_clock x w).1, (footprint_through_clock x w).2.2,
    (final_literal_fields x w).1, (final_literal_fields x w).2.2.1,
    (final_tape_behavior x w).1, fun j => final_content_contiguous x w j⟩
end FixedPairTagRemoval
end Pnp3.Complexity.Uniform.V1
