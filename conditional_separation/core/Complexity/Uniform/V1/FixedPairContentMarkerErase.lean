import Complexity.Uniform.V1.FixedPairOriginAlignment
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Prod

/-!
# Fixed trailing content-marker erasure

This closed phase consumes the exact output of `FixedPairOriginAlignment`.
It scans without inspecting Boolean values, stops at the first physical blank,
steps left to the structurally last nonblank cell, and accepts only after
checking that this cell is `some true` and erasing it.  Thus data bits equal to
`true` are never treated as markers merely because of their value.
-/

namespace Pnp3.Complexity.Uniform.V1
namespace FixedPairContentMarkerErase

open PairEncoding

abbrev eraseStateCount : Nat := 4

def qScan : Fin eraseStateCount := ⟨0, by decide⟩
def qErase : Fin eraseStateCount := ⟨1, by decide⟩
def qAccept : Fin eraseStateCount := ⟨2, by decide⟩
def qReject : Fin eraseStateCount := ⟨3, by decide⟩

private def raw (q : Fin eraseStateCount) (scanned : Option Bool) :
    Fin eraseStateCount × Option Bool × Move :=
  match q.val with
  | 0 =>
      match scanned with
      | none => (qErase, none, .left)
      | some b => (qScan, some b, .right)
  | 1 =>
      match scanned with
      | some true => (qAccept, none, .stay)
      | some false => (qReject, some false, .stay)
      | none => (qReject, none, .stay)
  | 2 => (qAccept, scanned, .stay)
  | _ => (qReject, scanned, .stay)

def machine : UniformTM where
  stateCount := eraseStateCount
  start := qScan
  accept := qAccept
  reject := qReject
  accept_ne_reject := by decide
  rawStep := raw

/-- Exhaustive transition table together with all finite-control resource
pins.  In particular malformed candidates in the erase state reject. -/
theorem table_and_resource_pins :
    (∀ scanned, machine.rawStep qScan scanned =
      match scanned with
      | none => (qErase, none, .left)
      | some b => (qScan, some b, .right)) ∧
    machine.rawStep qErase (some true) = (qAccept, none, .stay) ∧
    machine.rawStep qErase (some false) = (qReject, some false, .stay) ∧
    machine.rawStep qErase none = (qReject, none, .stay) ∧
    (∀ scanned, machine.rawStep qAccept scanned =
      (qAccept, scanned, .stay)) ∧
    (∀ scanned, machine.rawStep qReject scanned =
      (qReject, scanned, .stay)) ∧
    machine.stateCount = 4 ∧ machine.start = qScan ∧
    machine.accept = qAccept ∧ machine.reject = qReject ∧
    qScan.val = 0 ∧ qErase.val = 1 ∧ qAccept.val = 2 ∧ qReject.val = 3 ∧
    Fintype.card (Fin machine.stateCount × Option Bool) = 12 := by
  refine ⟨?_, rfl, rfl, rfl, ?_, ?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    rfl, ?_⟩
  · intro scanned
    cases scanned with
    | none => rfl
    | some b => cases b <;> rfl
  · intro scanned
    rfl
  · intro scanned
    rfl
  · change Fintype.card (Fin 4 × Option Bool) = 12
    decide

private theorem scan_some_action (b : Bool) :
    machine.step qScan (some b) = (qScan, some b, .right) := by
  cases b <;> rfl

private theorem scan_none_action :
    machine.step qScan none = (qErase, none, .left) := by rfl

private theorem erase_true_action :
    machine.step qErase (some true) = (qAccept, none, .stay) := by rfl

def retag {N B : Nat}
    (c : Config FixedPairOriginAlignment.alignmentStateCount N B) :
    Config eraseStateCount N B where
  state := qScan
  head := c.head
  tape := c.tape

def startConfig {n m : Nat} (B : Nat) (x : Bitstring n) (w : Bitstring m) :
    Config eraseStateCount (pairLength n m) B :=
  retag (FixedPairOriginAlignment.finalConfig B x w)

def clock (n m : Nat) : Nat := n + m + 3

theorem clock_exact (n m : Nat) : clock n m = n + m + 3 := rfl

/-- Headerless concatenated content on the predecessor's complete physical
allocation.  `none` remains distinct from the data value `some false`. -/
def contentTape {n m : Nat} (B : Nat) (x : Bitstring n) (w : Bitstring m) :
    Fin (tapeLength (pairLength n m) B) → Option Bool := fun i =>
  if h : i.val < n + m then some (Fin.append x w ⟨i.val, h⟩) else none

def finalConfig {n m : Nat} (B : Nat) (x : Bitstring n) (w : Bitstring m) :
    Config eraseStateCount (pairLength n m) B where
  state := qAccept
  head := ⟨n + m, by unfold tapeLength pairLength; omega⟩
  tape := contentTape B x w

private def sourceTape {n m : Nat} (B : Nat) (x : Bitstring n)
    (w : Bitstring m) :
    Fin (tapeLength (pairLength n m) B) → Option Bool := fun i =>
  if h : i.val < n + m then some (Fin.append x w ⟨i.val, h⟩)
  else if i.val = n + m then some true else none

private theorem aligned_eq_source {n m B : Nat} (x : Bitstring n)
    (w : Bitstring m) :
    FixedPairOriginAlignment.alignedTape B x w = sourceTape B x w := by
  funext i
  have hlayout := FixedPairOriginAlignment.final_fields_and_layout
    (B := B) x w
  rw [FixedPairOriginAlignment.run_exact] at hlayout
  by_cases hi : i.val < n + m
  · by_cases hx : i.val < n
    · let j : Fin n := ⟨i.val, hx⟩
      have hij : i = ⟨j.val, by unfold tapeLength pairLength; omega⟩ :=
        Fin.ext rfl
      have hv := hlayout.2.2.2.2.2.2.1 j
      change FixedPairOriginAlignment.alignedTape B x w _ = some (x j) at hv
      rw [hij, hv]
      unfold sourceTape
      rw [dif_pos (by dsimp [j]; omega)]
      congr 2
      exact (Fin.append_left x w j).symm
    · let j : Fin m := ⟨i.val - n, by omega⟩
      have hij : i = ⟨n + j.val, by unfold tapeLength pairLength; omega⟩ :=
        Fin.ext (by dsimp [j]; omega)
      have hv := hlayout.2.2.2.2.2.2.2.1 j
      change FixedPairOriginAlignment.alignedTape B x w _ = some (w j) at hv
      rw [hij, hv]
      unfold sourceTape
      rw [dif_pos (by dsimp [j]; omega)]
      congr 2
      exact (Fin.append_right x w j).symm
  · by_cases heq : i.val = n + m
    · have hij : i = ⟨n + m, by unfold tapeLength pairLength; omega⟩ :=
        Fin.ext heq
      have hv := hlayout.2.2.2.2.2.2.2.2.1
      change FixedPairOriginAlignment.alignedTape B x w _ = some true at hv
      rw [hij, hv]
      simp [sourceTape]
    · have hgt : n + m + 1 ≤ i.val := by omega
      have hv := hlayout.2.2.2.2.2.2.2.2.2 i hgt
      change FixedPairOriginAlignment.alignedTape B x w i = none at hv
      rw [hv]
      simp [sourceTape, hi, heq]

private theorem source_read_content {n m B : Nat} (x : Bitstring n)
    (w : Bitstring m) {k : Nat} (hk : k < n + m)
    (hfit : k < tapeLength (pairLength n m) B) :
    sourceTape B x w ⟨k, hfit⟩ = some (Fin.append x w ⟨k, hk⟩) := by
  simp [sourceTape, hk]

private theorem source_read_marker {n m B : Nat} (x : Bitstring n)
    (w : Bitstring m) :
    sourceTape B x w
      ⟨n + m, by unfold tapeLength pairLength; omega⟩ = some true := by
  simp [sourceTape]

private theorem source_read_blank {n m B : Nat} (x : Bitstring n)
    (w : Bitstring m) :
    sourceTape B x w
      ⟨n + m + 1, by unfold tapeLength pairLength; omega⟩ = none := by
  simp [sourceTape]

private theorem append_left_at {n m : Nat} (x : Bitstring n) (w : Bitstring m)
    (j : Fin n) (h : j.val < n + m) :
    Fin.append x w ⟨j.val, h⟩ = x j := by
  rw [show (⟨j.val, h⟩ : Fin (n + m)) = Fin.castAdd m j by
    apply Fin.ext
    rfl]
  exact Fin.append_left x w j

private theorem append_right_at {n m : Nat} (x : Bitstring n) (w : Bitstring m)
    (j : Fin m) (h : n + j.val < n + m) :
    Fin.append x w ⟨n + j.val, h⟩ = w j := by
  rw [show (⟨n + j.val, h⟩ : Fin (n + m)) = Fin.natAdd n j by
    apply Fin.ext
    rfl]
  exact Fin.append_right x w j

private theorem content_read_append {n m B : Nat} (x : Bitstring n)
    (w : Bitstring m) (j : Fin (n + m)) :
    contentTape B x w
      ⟨j.val, by unfold tapeLength pairLength; omega⟩ =
      some (Fin.append x w j) := by
  unfold contentTape
  rw [dif_pos j.isLt]

private theorem source_blank_above {n m B : Nat} (x : Bitstring n)
    (w : Bitstring m) (i : Fin (tapeLength (pairLength n m) B))
    (hi : n + m < i.val) : sourceTape B x w i = none := by
  simp [sourceTape, show ¬i.val < n + m by omega,
    show i.val ≠ n + m by omega]

private theorem content_blank_from {n m B : Nat} (x : Bitstring n)
    (w : Bitstring m) (i : Fin (tapeLength (pairLength n m) B))
    (hi : n + m ≤ i.val) : contentTape B x w i = none := by
  simp [contentTape, show ¬i.val < n + m by omega]

private def scanConfig {n m : Nat} (B : Nat) (x : Bitstring n)
    (w : Bitstring m) (k : Nat) (hk : k ≤ n + m + 1) :
    Config eraseStateCount (pairLength n m) B where
  state := qScan
  head := ⟨k, by unfold tapeLength pairLength; omega⟩
  tape := sourceTape B x w

private def eraseConfig {n m : Nat} (B : Nat) (x : Bitstring n)
    (w : Bitstring m) : Config eraseStateCount (pairLength n m) B where
  state := qErase
  head := ⟨n + m, by unfold tapeLength pairLength; omega⟩
  tape := sourceTape B x w

private theorem config_ext {n m B : Nat}
    {c d : Config eraseStateCount (pairLength n m) B}
    (hs : c.state = d.state) (hh : c.head = d.head) (ht : c.tape = d.tape) :
    c = d := by
  cases c
  cases d
  cases hs
  cases hh
  cases ht
  rfl

private theorem stepConfig_state {n m B : Nat}
    (c : Config eraseStateCount (pairLength n m) B) :
    (machine.stepConfig c).state =
      (machine.step c.state (c.tape c.head)).1 := rfl

private theorem stepConfig_head {n m B : Nat}
    (c : Config eraseStateCount (pairLength n m) B) :
    (machine.stepConfig c).head =
      moveHead c.head (machine.step c.state (c.tape c.head)).2.2 := rfl

private theorem stepConfig_tape {n m B : Nat}
    (c : Config eraseStateCount (pairLength n m) B)
    (i : Fin (tapeLength (pairLength n m) B)) :
    (machine.stepConfig c).tape i =
      if i = c.head then (machine.step c.state (c.tape c.head)).2.1
      else c.tape i := rfl

private theorem start_eq_scan_zero {n m B : Nat} (x : Bitstring n)
    (w : Bitstring m) : startConfig B x w = scanConfig B x w 0 (by omega) := by
  refine config_ext (c := startConfig B x w)
    (d := scanConfig B x w 0 (by omega)) rfl rfl ?_
  exact aligned_eq_source x w

private theorem step_scan {n m B : Nat} (x : Bitstring n) (w : Bitstring m)
    (k : Nat) (hk : k ≤ n + m) :
    machine.stepConfig (scanConfig B x w k (by omega)) =
      scanConfig B x w (k + 1) (by omega) := by
  obtain ⟨b, hread⟩ : ∃ b,
      (scanConfig B x w k (by omega)).tape
        (scanConfig B x w k (by omega)).head = some b := by
    by_cases hlt : k < n + m
    · refine ⟨Fin.append x w ⟨k, hlt⟩, ?_⟩
      exact source_read_content x w hlt _
    · have heq : k = n + m := by omega
      subst k
      exact ⟨true, source_read_marker x w⟩
  have haction : machine.step
      (scanConfig B x w k (by omega)).state
      ((scanConfig B x w k (by omega)).tape
        (scanConfig B x w k (by omega)).head) =
      (qScan, some b, .right) := by
    rw [hread]
    rfl
  apply config_ext
  · rw [stepConfig_state, haction]
    rfl
  · rw [stepConfig_head, haction]
    change moveHead ⟨k, by unfold tapeLength pairLength; omega⟩ .right =
      (⟨k + 1, by unfold tapeLength pairLength; omega⟩ :
        Fin (tapeLength (pairLength n m) B))
    unfold moveHead
    have hright : k + 1 < tapeLength (pairLength n m) B := by
      unfold tapeLength pairLength
      omega
    rw [dif_pos hright]
  · funext i
    rw [stepConfig_tape, haction]
    change (if i = (scanConfig B x w k (by omega)).head then some b
      else sourceTape B x w i) = sourceTape B x w i
    by_cases hi : i = (scanConfig B x w k (by omega)).head
    · rw [if_pos hi]
      simpa only [hi] using hread.symm
    · rw [if_neg hi]

private theorem run_scan {n m B : Nat} (x : Bitstring n) (w : Bitstring m)
    (k : Nat) (hk : k ≤ n + m + 1) :
    machine.run k (startConfig B x w) = scanConfig B x w k hk := by
  induction k with
  | zero => exact start_eq_scan_zero x w
  | succ k ih =>
      rw [UniformTM.run, ih (by omega)]
      exact step_scan x w k (by omega)

private theorem step_blank {n m B : Nat} (x : Bitstring n) (w : Bitstring m) :
    machine.stepConfig (scanConfig B x w (n + m + 1) (by omega)) =
      eraseConfig B x w := by
  have hread : (scanConfig B x w (n + m + 1) (by omega)).tape
      (scanConfig B x w (n + m + 1) (by omega)).head = none :=
    source_read_blank x w
  have haction : machine.step
      (scanConfig B x w (n + m + 1) (by omega)).state
      ((scanConfig B x w (n + m + 1) (by omega)).tape
        (scanConfig B x w (n + m + 1) (by omega)).head) =
      (qErase, none, .left) := by rw [hread]; rfl
  apply config_ext
  · rw [stepConfig_state, haction]
    rfl
  · rw [stepConfig_head, haction]
    change moveHead
      ⟨n + m + 1, by unfold tapeLength pairLength; omega⟩ .left =
      (⟨n + m, by unfold tapeLength pairLength; omega⟩ :
        Fin (tapeLength (pairLength n m) B))
    apply Fin.ext
    change n + m + 1 - 1 = n + m
    omega
  · funext i
    rw [stepConfig_tape, haction]
    change (if i = (scanConfig B x w (n + m + 1) (by omega)).head
      then none else sourceTape B x w i) = sourceTape B x w i
    by_cases hi : i = (scanConfig B x w (n + m + 1) (by omega)).head
    · rw [if_pos hi]
      simpa only [hi] using hread.symm
    · rw [if_neg hi]

private theorem erase_source_eq_content {n m B : Nat} (x : Bitstring n)
    (w : Bitstring m) :
    (fun i : Fin (tapeLength (pairLength n m) B) =>
      if i = ⟨n + m, by unfold tapeLength pairLength; omega⟩
      then none else sourceTape B x w i) = contentTape B x w := by
  funext i
  by_cases hi : i.val < n + m
  · have hne : i ≠ ⟨n + m, by unfold tapeLength pairLength; omega⟩ := by
      intro h
      have heq : i.val = n + m := congrArg Fin.val h
      omega
    rw [if_neg hne]
    simp [sourceTape, contentTape, hi]
  · have hs : sourceTape B x w i =
        if i.val = n + m then some true else none := by
      simp [sourceTape, hi]
    have hc : contentTape B x w i = none := by simp [contentTape, hi]
    rw [hc]
    by_cases heq : i.val = n + m
    · have hcell : i = ⟨n + m, by unfold tapeLength pairLength; omega⟩ :=
        Fin.ext heq
      rw [if_pos hcell]
    · have hcell : i ≠ ⟨n + m, by unfold tapeLength pairLength; omega⟩ := by
        intro h
        exact heq (congrArg Fin.val h)
      rw [if_neg hcell, hs, if_neg heq]

private theorem step_erase {n m B : Nat} (x : Bitstring n) (w : Bitstring m) :
    machine.stepConfig (eraseConfig B x w) = finalConfig B x w := by
  have hread : (eraseConfig B x w).tape (eraseConfig B x w).head = some true :=
    source_read_marker x w
  have haction : machine.step (eraseConfig B x w).state
      ((eraseConfig B x w).tape (eraseConfig B x w).head) =
      (qAccept, none, .stay) := by rw [hread]; rfl
  apply config_ext
  · rw [stepConfig_state, haction]
    rfl
  · rw [stepConfig_head, haction]
    change moveHead
      ⟨n + m, by unfold tapeLength pairLength; omega⟩ .stay =
      (⟨n + m, by unfold tapeLength pairLength; omega⟩ :
        Fin (tapeLength (pairLength n m) B))
    rfl
  · funext i
    rw [stepConfig_tape, haction]
    exact congrFun (erase_source_eq_content x w) i

private theorem run_erase {n m B : Nat} (x : Bitstring n) (w : Bitstring m) :
    machine.run (n + m + 2) (startConfig B x w) = eraseConfig B x w := by
  rw [show n + m + 2 = (n + m + 1) + 1 by omega, machine.run_add,
    run_scan x w (n + m + 1) (by omega)]
  simpa only [UniformTM.run] using step_blank x w

private theorem trace {n m B : Nat} (x : Bitstring n) (w : Bitstring m)
    (s : Nat) (hs : s ≤ clock n m) :
    machine.run s (startConfig B x w) =
      if h : s ≤ n + m + 1 then scanConfig B x w s h
      else if s = n + m + 2 then eraseConfig B x w else finalConfig B x w := by
  by_cases hscan : s ≤ n + m + 1
  · rw [dif_pos hscan, run_scan x w s hscan]
  · rw [dif_neg hscan]
    by_cases herase : s = n + m + 2
    · rw [if_pos herase]
      subst s
      exact run_erase x w
    · rw [if_neg herase]
      have hsclock : s = clock n m := by
        have hs' : s ≤ n + m + 3 := by simpa [clock] using hs
        unfold clock
        omega
      subst s
      unfold clock
      rw [show n + m + 3 = (n + m + 2) + 1 by omega, machine.run_add,
        run_erase x w]
      simpa only [UniformTM.run] using step_erase x w

/-- Exact predecessor run and field-for-field retagged handoff. -/
theorem handoff_exact {n m B : Nat} (x : Bitstring n) (w : Bitstring m) :
    let p := FixedPairOriginAlignment.machine.run
      (FixedPairOriginAlignment.clock n m)
      (FixedPairOriginAlignment.startConfig B x w)
    let c₀ := startConfig B x w
    p = FixedPairOriginAlignment.finalConfig B x w ∧
    p.state = FixedPairOriginAlignment.qAccept ∧
    c₀ = retag p ∧ c₀.state = qScan ∧ c₀.head = p.head ∧ c₀.tape = p.tape := by
  dsimp
  rw [FixedPairOriginAlignment.run_exact]
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The exact `n+m+3` endpoint, including the entire tape and numeric head. -/
theorem run_exact {n m : Nat} (B : Nat) (x : Bitstring n) (w : Bitstring m) :
    machine.run (clock n m) (startConfig B x w) = finalConfig B x w := by
  simpa [clock] using trace (B := B) x w (clock n m) (le_refl _)

/-- Literal final fields, headerless `Fin.append` content, and a blank suffix
over every allocated cell beginning exactly at `n+m`. -/
theorem final_fields_and_layout {n m B : Nat} (x : Bitstring n)
    (w : Bitstring m) :
    let c := machine.run (clock n m) (startConfig B x w)
    c = finalConfig B x w ∧ c.state = qAccept ∧ c.state = machine.accept ∧
    c.head = (⟨n + m, by unfold tapeLength pairLength; omega⟩ :
      Fin (tapeLength (pairLength n m) B)) ∧ c.head.val = n + m ∧
    c.tape = contentTape B x w ∧
    (∀ j : Fin (n + m), c.tape
      ⟨j.val, by unfold tapeLength pairLength; omega⟩ =
        some (Fin.append x w j)) ∧
    (∀ j : Fin n, c.tape
      ⟨j.val, by unfold tapeLength pairLength; omega⟩ = some (x j)) ∧
    (∀ j : Fin m, c.tape
      ⟨n + j.val, by unfold tapeLength pairLength; omega⟩ = some (w j)) ∧
    (∀ i : Fin (tapeLength (pairLength n m) B),
      n + m ≤ i.val → c.tape i = none) := by
  dsimp
  rw [run_exact]
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_, ?_, ?_⟩
  · intro j
    exact content_read_append x w j
  · intro j
    have h := content_read_append (B := B) x w (Fin.castAdd m j)
    simpa only [Fin.append_left] using h
  · intro j
    have h := content_read_append (B := B) x w (Fin.natAdd n j)
    simpa only [Fin.append_right] using h
  · intro i hi
    exact content_blank_from x w i hi

/-- The exact clock is the strict first time either terminal state appears. -/
theorem strict_first_terminal {n m B : Nat} (x : Bitstring n)
    (w : Bitstring m) :
    (∀ s, s < clock n m →
      (machine.run s (startConfig B x w)).state ≠ qAccept ∧
      (machine.run s (startConfig B x w)).state ≠ qReject) ∧
    (machine.run (clock n m) (startConfig B x w)).state = qAccept := by
  constructor
  · intro s hs
    rw [trace x w s (Nat.le_of_lt hs)]
    by_cases hscan : s ≤ n + m + 1
    · rw [dif_pos hscan]
      change qScan ≠ qAccept ∧ qScan ≠ qReject
      decide
    · rw [dif_neg hscan]
      have heq : s = n + m + 2 := by unfold clock at hs; omega
      rw [if_pos heq]
      change qErase ≠ qAccept ∧ qErase ≠ qReject
      decide
  · rw [run_exact]
    rfl

/-- Literal acceptance absorbs every post-clock run without changing any
field. -/
theorem post_clock_absorption {n m B : Nat} (x : Bitstring n)
    (w : Bitstring m) (extra : Nat) :
    machine.run (clock n m + extra) (startConfig B x w) = finalConfig B x w := by
  rw [machine.run_add, run_exact,
    machine.run_accept (finalConfig B x w) rfl extra]

/-- Exact head footprint, its rightmost attainment, preservation of the
blank suffix, and all scan-prefix visits through the deadline. -/
theorem full_footprint {n m B : Nat} (x : Bitstring n) (w : Bitstring m) :
    (∀ s, s ≤ clock n m →
      (machine.run s (startConfig B x w)).head.val =
        if s ≤ n + m + 1 then s else n + m) ∧
    (machine.run (n + m + 1) (startConfig B x w)).head.val = n + m + 1 ∧
    (∀ k, k ≤ n + m + 1 →
      (machine.run k (startConfig B x w)).head.val = k) ∧
    (∀ s, s ≤ clock n m → ∀ i : Fin (tapeLength (pairLength n m) B),
      n + m < i.val → (machine.run s (startConfig B x w)).tape i = none) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro s hs
    rw [trace x w s hs]
    by_cases hscan : s ≤ n + m + 1
    · rw [dif_pos hscan, if_pos hscan]
      change s = s
      rfl
    · rw [dif_neg hscan, if_neg hscan]
      split <;> change n + m = n + m <;> rfl
  · rw [run_scan x w (n + m + 1) (by omega)]
    rfl
  · intro k hk
    rw [run_scan x w k hk]
    rfl
  · intro s hs i hi
    rw [trace x w s hs]
    by_cases hscan : s ≤ n + m + 1
    · rw [dif_pos hscan]
      exact source_blank_above x w i hi
    · rw [dif_neg hscan]
      by_cases he : s = n + m + 2
      · rw [if_pos he]
        exact source_blank_above x w i hi
      · rw [if_neg he]
        exact content_blank_from x w i (by omega)

/-- No transition before the clock uses either finite-tape boundary clamp,
including when `n=m=B=0`. -/
theorem no_boundary_clamp {n m B : Nat} (x : Bitstring n) (w : Bitstring m)
    (s : Nat) (hs : s < clock n m) :
    let c := machine.run s (startConfig B x w)
    let move := (machine.step c.state (c.tape c.head)).2.2
    (move = .right → c.head.val + 1 < tapeLength (pairLength n m) B) ∧
    (move = .left → 0 < c.head.val) := by
  dsimp
  rw [trace x w s (Nat.le_of_lt hs)]
  by_cases hscan : s ≤ n + m + 1
  · rw [dif_pos hscan]
    by_cases hlast : s = n + m + 1
    · subst s
      change ((machine.step qScan (sourceTape B x w
          ⟨n + m + 1, by unfold tapeLength pairLength; omega⟩)).2.2 = .right →
          n + m + 2 < tapeLength (pairLength n m) B) ∧
        ((machine.step qScan (sourceTape B x w
          ⟨n + m + 1, by unfold tapeLength pairLength; omega⟩)).2.2 = .left →
          0 < n + m + 1)
      rw [source_read_blank]
      rw [scan_none_action]
      exact ⟨by simp, by intro _; omega⟩
    · have hsle : s ≤ n + m := by omega
      by_cases hlt : s < n + m
      · change ((machine.step qScan (sourceTape B x w
            ⟨s, by unfold tapeLength pairLength; omega⟩)).2.2 = .right →
            s + 1 < tapeLength (pairLength n m) B) ∧
          ((machine.step qScan (sourceTape B x w
            ⟨s, by unfold tapeLength pairLength; omega⟩)).2.2 = .left → 0 < s)
        rw [source_read_content x w hlt, scan_some_action]
        exact ⟨by intro _; unfold tapeLength pairLength; omega, by simp⟩
      · have heq : s = n + m := by omega
        subst s
        change ((machine.step qScan (sourceTape B x w
            ⟨n + m, by unfold tapeLength pairLength; omega⟩)).2.2 = .right →
            n + m + 1 < tapeLength (pairLength n m) B) ∧
          ((machine.step qScan (sourceTape B x w
            ⟨n + m, by unfold tapeLength pairLength; omega⟩)).2.2 = .left →
            0 < n + m)
        rw [source_read_marker, scan_some_action]
        exact ⟨by intro _; unfold tapeLength pairLength; omega, by simp⟩
  · rw [dif_neg hscan]
    have heq : s = n + m + 2 := by unfold clock at hs; omega
    rw [if_pos heq]
    change ((machine.step qErase (sourceTape B x w
        ⟨n + m, by unfold tapeLength pairLength; omega⟩)).2.2 = .right →
        n + m + 1 < tapeLength (pairLength n m) B) ∧
      ((machine.step qErase (sourceTape B x w
        ⟨n + m, by unfold tapeLength pairLength; omega⟩)).2.2 = .left →
        0 < n + m)
    rw [source_read_marker, erase_true_action]
    exact ⟨by simp, by simp⟩

private theorem tape_common_source {n m : Nat} (B B' : Nat)
    (x : Bitstring n) (w : Bitstring m)
    (i : Fin (tapeLength (pairLength n m) B))
    (i' : Fin (tapeLength (pairLength n m) B')) (h : i.val = i'.val) :
    sourceTape B x w i = sourceTape B' x w i' := by
  by_cases hi : i.val < n + m
  · have hi' : i'.val < n + m := by omega
    unfold sourceTape
    rw [dif_pos hi, dif_pos hi']
    congr 2
    apply Fin.ext
    exact h
  · have hi' : ¬i'.val < n + m := by omega
    unfold sourceTape
    rw [dif_neg hi, dif_neg hi']
    by_cases heq : i.val = n + m
    · have heq' : i'.val = n + m := by omega
      rw [if_pos heq, if_pos heq']
    · have heq' : i'.val ≠ n + m := by omega
      rw [if_neg heq, if_neg heq']

private theorem tape_common_content {n m : Nat} (B B' : Nat)
    (x : Bitstring n) (w : Bitstring m)
    (i : Fin (tapeLength (pairLength n m) B))
    (i' : Fin (tapeLength (pairLength n m) B')) (h : i.val = i'.val) :
    contentTape B x w i = contentTape B' x w i' := by
  by_cases hi : i.val < n + m
  · have hi' : i'.val < n + m := by omega
    unfold contentTape
    rw [dif_pos hi, dif_pos hi']
    congr 2
    apply Fin.ext
    exact h
  · have hi' : ¬i'.val < n + m := by omega
    unfold contentTape
    rw [dif_neg hi, dif_neg hi']

/-- At every time through the clock, control, numeric head, and every
equal-address tape value are independent of the ambient budget. -/
theorem budget_independence {n m : Nat} (B B' : Nat) (x : Bitstring n)
    (w : Bitstring m) (s : Nat) (hs : s ≤ clock n m) :
    (machine.run s (startConfig B x w)).state =
        (machine.run s (startConfig B' x w)).state ∧
    (machine.run s (startConfig B x w)).head.val =
        (machine.run s (startConfig B' x w)).head.val ∧
    ∀ (i : Fin (tapeLength (pairLength n m) B))
        (i' : Fin (tapeLength (pairLength n m) B')),
      i.val = i'.val →
      (machine.run s (startConfig B x w)).tape i =
        (machine.run s (startConfig B' x w)).tape i' := by
  rw [trace x w s hs, trace x w s hs]
  by_cases hscan : s ≤ n + m + 1
  · rw [dif_pos hscan, dif_pos hscan]
    exact ⟨rfl, rfl, tape_common_source B B' x w⟩
  · rw [dif_neg hscan, dif_neg hscan]
    by_cases he : s = n + m + 2
    · rw [if_pos he, if_pos he]
      exact ⟨rfl, rfl, tape_common_source B B' x w⟩
    · rw [if_neg he, if_neg he]
      exact ⟨rfl, rfl, tape_common_content B B' x w⟩

/-- Recovery and injectivity are asserted only at one fixed pair of extents;
there is deliberately no comparison between different splits. -/
theorem fixed_extent_recovery {n m B : Nat} (x : Bitstring n)
    (w : Bitstring m) :
    (∀ j : Fin n, contentTape B x w
      ⟨j.val, by unfold tapeLength pairLength; omega⟩ = some (x j)) ∧
    (∀ j : Fin m, contentTape B x w
      ⟨n + j.val, by unfold tapeLength pairLength; omega⟩ = some (w j)) ∧
    (∀ (x' : Bitstring n) (w' : Bitstring m),
      contentTape B x w = contentTape B x' w' → x = x' ∧ w = w') := by
  have hx : ∀ j : Fin n, contentTape B x w
      ⟨j.val, by unfold tapeLength pairLength; omega⟩ = some (x j) := by
    intro j
    have h := content_read_append (B := B) x w (Fin.castAdd m j)
    simpa only [Fin.append_left] using h
  have hw : ∀ j : Fin m, contentTape B x w
      ⟨n + j.val, by unfold tapeLength pairLength; omega⟩ = some (w j) := by
    intro j
    have h := content_read_append (B := B) x w (Fin.natAdd n j)
    simpa only [Fin.append_right] using h
  refine ⟨hx, hw, ?_⟩
  intro x' w' heq
  constructor <;> funext j
  · have h := congrFun heq
      (⟨j.val, by unfold tapeLength pairLength; omega⟩ :
        Fin (tapeLength (pairLength n m) B))
    have hx' : contentTape B x' w'
        ⟨j.val, by unfold tapeLength pairLength; omega⟩ = some (x' j) := by
      have hread := content_read_append (B := B) x' w' (Fin.castAdd m j)
      simpa only [Fin.append_left] using hread
    rw [hx j, hx'] at h
    exact Option.some.inj h
  · have h := congrFun heq
      (⟨n + j.val, by unfold tapeLength pairLength; omega⟩ :
        Fin (tapeLength (pairLength n m) B))
    have hw' : contentTape B x' w'
        ⟨n + j.val, by unfold tapeLength pairLength; omega⟩ = some (w' j) := by
      have hread := content_read_append (B := B) x' w' (Fin.natAdd n j)
      simpa only [Fin.append_right] using hread
    rw [hw j, hw'] at h
    exact Option.some.inj h

/-- Fully explicit zero-length, zero-budget trace.  The two-cell allocation
is `[marker][blank]`; the right and left moves are both strict. -/
theorem empty_zero_budget_trace (x : Bitstring 0) (w : Bitstring 0) :
    clock 0 0 = 3 ∧
    (machine.run 0 (startConfig 0 x w)).state = qScan ∧
    (machine.run 0 (startConfig 0 x w)).head.val = 0 ∧
    (machine.run 0 (startConfig 0 x w)).tape
      ⟨0, by unfold tapeLength pairLength; omega⟩ = some true ∧
    (machine.run 1 (startConfig 0 x w)).state = qScan ∧
    (machine.run 1 (startConfig 0 x w)).head.val = 1 ∧
    (machine.run 1 (startConfig 0 x w)).tape
      ⟨1, by unfold tapeLength pairLength; omega⟩ = none ∧
    (machine.run 2 (startConfig 0 x w)).state = qErase ∧
    (machine.run 2 (startConfig 0 x w)).head.val = 0 ∧
    machine.run 3 (startConfig 0 x w) = finalConfig 0 x w ∧
    (∀ i : Fin (tapeLength (pairLength 0 0) 0),
      (machine.run 3 (startConfig 0 x w)).tape i = none) := by
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [run_scan x w 0 (by omega)]
    rfl
  · rw [run_scan x w 0 (by omega)]
    rfl
  · rw [run_scan x w 0 (by omega)]
    change sourceTape 0 x w
      ⟨0, by unfold tapeLength pairLength; omega⟩ = some true
    exact source_read_marker x w
  · rw [run_scan x w 1 (by omega)]
    rfl
  · rw [run_scan x w 1 (by omega)]
    rfl
  · rw [run_scan x w 1 (by omega)]
    change sourceTape 0 x w
      ⟨1, by unfold tapeLength pairLength; omega⟩ = none
    exact source_read_blank x w
  · simpa using congrArg Config.state (run_erase (B := 0) x w)
  · simpa using congrArg (fun c => c.head.val) (run_erase (B := 0) x w)
  · simpa [clock] using run_exact 0 x w
  · intro i
    have hr := run_exact (n := 0) (m := 0) 0 x w
    simp only [clock] at hr
    rw [hr]
    exact content_blank_from x w i (by omega)

/-- Bundled operational phase contract. -/
theorem phase_contract {n m B : Nat} (x : Bitstring n) (w : Bitstring m) :
    let p := FixedPairOriginAlignment.machine.run
      (FixedPairOriginAlignment.clock n m)
      (FixedPairOriginAlignment.startConfig B x w)
    let c₀ := startConfig B x w
    p = FixedPairOriginAlignment.finalConfig B x w ∧
    p.state = FixedPairOriginAlignment.qAccept ∧ c₀ = retag p ∧
    machine.run (n + m + 3) c₀ = finalConfig B x w ∧
    (∀ s, s < n + m + 3 →
      (machine.run s c₀).state ≠ qAccept ∧
      (machine.run s c₀).state ≠ qReject) ∧
    (∀ s, s ≤ n + m + 3 →
      (machine.run s c₀).head.val ≤ n + m + 1) ∧
    (∀ s, s < n + m + 3 →
      let c := machine.run s c₀
      let move := (machine.step c.state (c.tape c.head)).2.2
      (move = .right → c.head.val + 1 < tapeLength (pairLength n m) B) ∧
      (move = .left → 0 < c.head.val)) ∧
    (machine.run (n + m + 3) c₀).head.val = n + m ∧
    (machine.run (n + m + 3) c₀).tape = contentTape B x w ∧
    (∀ i : Fin (tapeLength (pairLength n m) B), n + m ≤ i.val →
      (machine.run (n + m + 3) c₀).tape i = none) ∧
    (∀ j : Fin (n + m), (machine.run (n + m + 3) c₀).tape
      ⟨j.val, by unfold tapeLength pairLength; omega⟩ =
        some (Fin.append x w j)) ∧
    (∀ extra, machine.run (n + m + 3 + extra) c₀ = finalConfig B x w) ∧
    (∀ B' s, s ≤ n + m + 3 →
      (machine.run s c₀).state =
          (machine.run s (startConfig B' x w)).state ∧
      (machine.run s c₀).head.val =
          (machine.run s (startConfig B' x w)).head.val ∧
      ∀ (i : Fin (tapeLength (pairLength n m) B))
          (i' : Fin (tapeLength (pairLength n m) B')),
        i.val = i'.val →
        (machine.run s c₀).tape i =
          (machine.run s (startConfig B' x w)).tape i') := by
  dsimp
  refine ⟨(handoff_exact x w).1, (handoff_exact x w).2.1,
    (handoff_exact x w).2.2.1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [clock] using run_exact B x w
  · simpa [clock] using (strict_first_terminal (B := B) x w).1
  · intro s hs
    have h := (full_footprint (B := B) x w).1 s (by simpa [clock] using hs)
    rw [h]
    split <;> omega
  · intro s hs
    exact no_boundary_clamp x w s (by simpa [clock] using hs)
  · exact (final_fields_and_layout (B := B) x w).2.2.2.2.1
  · exact (final_fields_and_layout (B := B) x w).2.2.2.2.2.1
  · intro i hi
    exact (final_fields_and_layout (B := B) x w).2.2.2.2.2.2.2.2.2 i hi
  · intro j
    exact (final_fields_and_layout (B := B) x w).2.2.2.2.2.2.1 j
  · intro extra
    simpa [clock] using post_clock_absorption (B := B) x w extra
  · intro B' s hs
    exact budget_independence B B' x w s (by simpa [clock] using hs)

end FixedPairContentMarkerErase
end Pnp3.Complexity.Uniform.V1
