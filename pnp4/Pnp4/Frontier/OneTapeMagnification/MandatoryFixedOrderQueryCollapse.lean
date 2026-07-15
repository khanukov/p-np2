import Mathlib.Tactic
import Pnp4.Frontier.OneTapeMagnification.ExactMasterGuardedCanonicalComponent

namespace Pnp4
namespace Frontier
namespace OneTapeMagnification

/-!
# Collapsing optional queries to a mandatory fixed order

The rejecting master guard still has one physical layer for every layer of
the underlying verifier, including layers which do not query the input.  This
file records the finite syntactic conversion which skips those silent layers.

For a duplicate-free master list, we first append every unread input
coordinate.  The resulting program has exactly `n` layers and queries exactly
one coordinate at every layer.  Its live state is either a physical layer and
an underlying state, or a completed Boolean answer.  Thus the construction
has exact homogeneous width `L * program.width + 2`.

The construction below is a deterministic mandatory fixed-order ROBP in the
local `LayeredQueryProgram` model.  It is not, by itself, an invocation of any
external branching-program theorem.
-/

namespace LayeredQueryProgram

/-- Coordinates not already present in a finite master order. -/
def masterUnreadSuffix {n : Nat} (master : List (Fin n)) : List (Fin n) :=
  (List.finRange n).filter fun coordinate => decide (coordinate ∉ master)

/-- Complete a master prefix by appending every unread coordinate in the
canonical `finRange` order. -/
def completeMasterOrder {n : Nat} (master : List (Fin n)) : List (Fin n) :=
  master ++ masterUnreadSuffix master

theorem masterUnreadSuffix_nodup {n : Nat} (master : List (Fin n)) :
    (masterUnreadSuffix master).Nodup := by
  exact (List.nodup_finRange n).filter _

theorem master_disjoint_masterUnreadSuffix {n : Nat}
    (master : List (Fin n)) :
    master.Disjoint (masterUnreadSuffix master) := by
  rw [List.disjoint_left]
  intro coordinate hmaster hunread
  have hnotMaster : coordinate ∉ master :=
    of_decide_eq_true (List.mem_filter.mp hunread).2
  exact hnotMaster hmaster

/-- A duplicate-free master prefix completed by its unread suffix is a
permutation of all input coordinates. -/
theorem completeMasterOrder_perm_finRange_of_nodup {n : Nat}
    (master : List (Fin n)) (hmaster : master.Nodup) :
    List.Perm (completeMasterOrder master) (List.finRange n) := by
  have hcomplete : (completeMasterOrder master).Nodup := by
    exact hmaster.append (masterUnreadSuffix_nodup master)
      (master_disjoint_masterUnreadSuffix master)
  apply (List.perm_ext_iff_of_nodup hcomplete
    (List.nodup_finRange n)).2
  intro coordinate
  constructor
  · intro _
    exact List.mem_finRange coordinate
  · intro _
    by_cases hmem : coordinate ∈ master
    · exact List.mem_append_left _ hmem
    · apply List.mem_append_right
      exact List.mem_filter.mpr ⟨List.mem_finRange coordinate,
        decide_eq_true hmem⟩

@[simp]
theorem completeMasterOrder_length_of_nodup {n : Nat}
    (master : List (Fin n)) (hmaster : master.Nodup) :
    (completeMasterOrder master).length = n := by
  simpa using
    (completeMasterOrder_perm_finRange_of_nodup master hmaster).length_eq

/-- The mandatory coordinate at a layer of the completed order. -/
def completeMasterQuery {n : Nat} (master : List (Fin n))
    (hmaster : master.Nodup) (layer : Fin n) : Fin n :=
  (completeMasterOrder master).get
    ⟨layer.val, by
      rw [completeMasterOrder_length_of_nodup master hmaster]
      exact layer.isLt⟩

/-- While silent physical layers are being skipped, the collapsed program is
either poised at a real physical query or has already computed its answer. -/
abbrev MandatoryQueryCollapseState {n L : Nat}
    (program : LayeredQueryProgram n L) :=
  Sum (Fin L × program.State) Bool

/-- Starting at physical layer `physical`, run at most `fuel` remaining
physical layers until the next real query.  A query is exposed only when it
is the next entry of `master`; a mismatch is completed rejection. -/
def mandatoryQuerySeek {n L : Nat} (program : LayeredQueryProgram n L)
    (master : List (Fin n)) (queryCount : Nat) :
    (fuel physical : Nat) → physical + fuel = L → program.State →
      MandatoryQueryCollapseState program
  | 0, _, _, state => Sum.inr (program.output state)
  | fuel + 1, physical, hphysical, state =>
      let layer : Fin L := ⟨physical, by omega⟩
      match program.query? layer state with
      | none =>
          mandatoryQuerySeek program master queryCount fuel (physical + 1)
            (by omega) (program.next layer state none)
      | some actual =>
          if hcount : queryCount < master.length then
            if actual = master.get ⟨queryCount, hcount⟩ then
              Sum.inl (layer, state)
            else
              Sum.inr false
          else
            Sum.inr false

/-- Resume immediately after consuming the mandatory bit at a physical query
layer, then silently seek the next real query. -/
def mandatoryQueryResume {n L : Nat} (program : LayeredQueryProgram n L)
    (master : List (Fin n)) (queryCount : Nat)
    (running : Fin L × program.State) (bit : Bool) :
    MandatoryQueryCollapseState program :=
  mandatoryQuerySeek program master (queryCount + 1)
    (L - (running.1.val + 1)) (running.1.val + 1) (by omega)
    (program.next running.1 running.2 (some bit))

/-- Collapse every silent layer of `program`, reject every deviation from the
master prefix, and pad with ignored mandatory queries over unread variables.

There are exactly `n` target layers.  `Sum.inr true/false` is an absorbing
completed answer, so padding after early termination cannot change semantics.
-/
def collapseToMandatoryFixedOrder {n L : Nat}
    (program : LayeredQueryProgram n L) (master : List (Fin n))
    (hmaster : master.Nodup) : LayeredQueryProgram n n where
  State := MandatoryQueryCollapseState program
  stateFintype := by
    letI := program.stateFintype
    infer_instance
  start := mandatoryQuerySeek program master 0 L 0 (by omega) program.start
  query? := fun layer _ => some (completeMasterQuery master hmaster layer)
  next := fun layer state answer =>
    match state, answer with
    | Sum.inl running, some bit =>
        mandatoryQueryResume program master layer.val running bit
    | Sum.inl _, none => Sum.inr false
    | Sum.inr done, _ => Sum.inr done
  output := fun state =>
    match state with
    | Sum.inl _ => false
    | Sum.inr done => done

/-- Every target layer has the advertised mandatory completed-order query. -/
theorem collapseToMandatoryFixedOrder_hasFixedQueryOrder {n L : Nat}
    (program : LayeredQueryProgram n L) (master : List (Fin n))
    (hmaster : master.Nodup) :
    (collapseToMandatoryFixedOrder program master hmaster).HasFixedQueryOrder
      (fun layer => some (completeMasterQuery master hmaster layer)) := by
  intro layer state
  rfl

/-- The completed mandatory order is literally the completed master list. -/
theorem listOfFn_completeMasterQuery {n : Nat}
    (master : List (Fin n)) (hmaster : master.Nodup) :
    List.ofFn (completeMasterQuery master hmaster) =
      completeMasterOrder master := by
  apply List.ext_get
  · simp [completeMasterOrder_length_of_nodup master hmaster]
  · intro index hleft hright
    simp [completeMasterQuery]

/-- A completed duplicate-free master order is still duplicate-free. -/
theorem completeMasterOrder_nodup {n : Nat}
    (master : List (Fin n)) (hmaster : master.Nodup) :
    (completeMasterOrder master).Nodup := by
  exact (completeMasterOrder_perm_finRange_of_nodup master hmaster).symm.nodup
    (List.nodup_finRange n)

/-- A duplicate-free list of `Fin n` coordinates has length at most `n`. -/
theorem master_length_le_of_nodup {n : Nat}
    (master : List (Fin n)) (hmaster : master.Nodup) :
    master.length ≤ n := by
  have hlength := completeMasterOrder_length_of_nodup master hmaster
  simp only [completeMasterOrder, List.length_append] at hlength
  omega

/-- Before the end of the master prefix, completion does not change the
coordinate at that position. -/
theorem completeMasterQuery_eq_master_get_of_lt {n : Nat}
    (master : List (Fin n)) (hmaster : master.Nodup) (layer : Fin n)
    (hlayer : layer.val < master.length) :
    completeMasterQuery master hmaster layer =
      master.get ⟨layer.val, hlayer⟩ := by
  simp [completeMasterQuery, completeMasterOrder, hlayer]

/-- The collapsed program is read-once: it makes every query exactly once,
including semantically ignored padding after it has completed. -/
theorem collapseToMandatoryFixedOrder_isReadOnce {n L : Nat}
    (program : LayeredQueryProgram n L) (master : List (Fin n))
    (hmaster : master.Nodup) :
    (collapseToMandatoryFixedOrder program master hmaster).IsReadOnce := by
  apply isReadOnce_of_fixedQueryOrder_nodup
    (collapseToMandatoryFixedOrder program master hmaster)
    (fun layer => some (completeMasterQuery master hmaster layer))
    (collapseToMandatoryFixedOrder_hasFixedQueryOrder
      program master hmaster)
  have horder :
      (List.ofFn fun layer : Fin n =>
        some (completeMasterQuery master hmaster layer)).filterMap id =
          List.ofFn (completeMasterQuery master hmaster) := by
    simp [List.ofFn_eq_map]
  rw [horder, listOfFn_completeMasterQuery master hmaster]
  exact completeMasterOrder_nodup master hmaster

/-! ## Denotational correctness of the silent-layer coroutine -/

/-- Direct physical-layer semantics with the rejecting master discipline.
This is the Boolean computation which both the strict guard and the collapsed
mandatory program implement. -/
def rejectingMasterPhysicalResult {n L : Nat}
    (program : LayeredQueryProgram n L) (master : List (Fin n))
    (input : Fin n → Bool) (queryCount : Nat) :
    (fuel physical : Nat) → physical + fuel = L → program.State → Bool
  | 0, _, _, state => program.output state
  | fuel + 1, physical, hphysical, state =>
      let layer : Fin L := ⟨physical, by omega⟩
      match program.query? layer state with
      | none =>
          rejectingMasterPhysicalResult program master input queryCount
            fuel (physical + 1) (by omega) (program.next layer state none)
      | some actual =>
          if hcount : queryCount < master.length then
            if actual = master.get ⟨queryCount, hcount⟩ then
              rejectingMasterPhysicalResult program master input
                (queryCount + 1) fuel (physical + 1) (by omega)
                (program.next layer state (some (input actual)))
            else
              false
          else
            false

/-- Interpret a suspended collapsed state using the still-unread input. -/
def mandatoryQueryStateResult {n L : Nat}
    (program : LayeredQueryProgram n L) (master : List (Fin n))
    (input : Fin n → Bool) (queryCount : Nat) :
    MandatoryQueryCollapseState program → Bool
  | Sum.inr done => done
  | Sum.inl running =>
      if hcount : queryCount < master.length then
        rejectingMasterPhysicalResult program master input (queryCount + 1)
          (L - (running.1.val + 1)) (running.1.val + 1) (by omega)
          (program.next running.1 running.2
            (some (input (master.get ⟨queryCount, hcount⟩))))
      else
        false

/-- A suspended real-query state really exposes the indicated next master
coordinate. -/
def MandatoryQueryStateValid {n L : Nat}
    (program : LayeredQueryProgram n L) (master : List (Fin n))
    (queryCount : Nat) : MandatoryQueryCollapseState program → Prop
  | Sum.inr _ => True
  | Sum.inl running =>
      ∃ hcount : queryCount < master.length,
        program.query? running.1 running.2 =
          some (master.get ⟨queryCount, hcount⟩)

/-- `mandatoryQuerySeek` either finishes or suspends at precisely the next
master query. -/
theorem mandatoryQuerySeek_valid {n L : Nat}
    (program : LayeredQueryProgram n L) (master : List (Fin n))
    (queryCount fuel physical : Nat) (hphysical : physical + fuel = L)
    (state : program.State) :
    MandatoryQueryStateValid program master queryCount
      (mandatoryQuerySeek program master queryCount fuel physical
        hphysical state) := by
  induction fuel generalizing physical state with
  | zero =>
      simp [mandatoryQuerySeek, MandatoryQueryStateValid]
  | succ fuel ih =>
      let layer : Fin L := ⟨physical, by omega⟩
      cases hquery : program.query? layer state with
      | none =>
          have hquery' : program.query? (⟨physical, by omega⟩ : Fin L)
              state = none := by
            simpa [layer] using hquery
          rw [mandatoryQuerySeek, hquery']
          change MandatoryQueryStateValid program master queryCount
            (mandatoryQuerySeek program master queryCount fuel
              (physical + 1) (by omega)
              (program.next (⟨physical, by omega⟩ : Fin L) state none))
          simpa [layer] using
            ih (physical + 1) (by omega)
              (program.next layer state none)
      | some actual =>
          have hquery' : program.query? (⟨physical, by omega⟩ : Fin L)
              state = some actual := by
            simpa [layer] using hquery
          by_cases hcount : queryCount < master.length
          · by_cases heq : actual = master.get ⟨queryCount, hcount⟩
            · rw [mandatoryQuerySeek, hquery']
              change MandatoryQueryStateValid program master queryCount
                (if h : queryCount < master.length then
                  if actual = master.get ⟨queryCount, h⟩ then
                    Sum.inl ((⟨physical, by omega⟩ : Fin L), state)
                  else Sum.inr false
                else Sum.inr false)
              rw [dif_pos hcount, if_pos heq]
              simp only [MandatoryQueryStateValid]
              refine ⟨hcount, ?_⟩
              simpa [heq] using hquery'
            · rw [mandatoryQuerySeek, hquery']
              change MandatoryQueryStateValid program master queryCount
                (if h : queryCount < master.length then
                  if actual = master.get ⟨queryCount, h⟩ then
                    Sum.inl ((⟨physical, by omega⟩ : Fin L), state)
                  else Sum.inr false
                else Sum.inr false)
              rw [dif_pos hcount, if_neg heq]
              trivial
          · rw [mandatoryQuerySeek, hquery']
            change MandatoryQueryStateValid program master queryCount
              (if h : queryCount < master.length then
                if actual = master.get ⟨queryCount, h⟩ then
                  Sum.inl ((⟨physical, by omega⟩ : Fin L), state)
                else Sum.inr false
              else Sum.inr false)
            rw [dif_neg hcount]
            trivial

/-- Interpreting the state returned by `seek` is exactly the direct physical
rejecting-master computation. -/
theorem mandatoryQuerySeek_result {n L : Nat}
    (program : LayeredQueryProgram n L) (master : List (Fin n))
    (input : Fin n → Bool) (queryCount fuel physical : Nat)
    (hphysical : physical + fuel = L) (state : program.State) :
    mandatoryQueryStateResult program master input queryCount
        (mandatoryQuerySeek program master queryCount fuel physical
          hphysical state) =
      rejectingMasterPhysicalResult program master input queryCount
        fuel physical hphysical state := by
  induction fuel generalizing physical state with
  | zero =>
      simp [mandatoryQuerySeek, mandatoryQueryStateResult,
        rejectingMasterPhysicalResult]
  | succ fuel ih =>
      let layer : Fin L := ⟨physical, by omega⟩
      cases hquery : program.query? layer state with
      | none =>
          have hquery' : program.query? (⟨physical, by omega⟩ : Fin L)
              state = none := by
            simpa [layer] using hquery
          rw [mandatoryQuerySeek, rejectingMasterPhysicalResult,
            hquery']
          change mandatoryQueryStateResult program master input queryCount
              (mandatoryQuerySeek program master queryCount fuel
                (physical + 1) (by omega)
                (program.next (⟨physical, by omega⟩ : Fin L) state none)) =
            rejectingMasterPhysicalResult program master input queryCount
              fuel (physical + 1) (by omega)
              (program.next (⟨physical, by omega⟩ : Fin L) state none)
          simpa [layer] using
            ih (physical + 1) (by omega)
              (program.next layer state none)
      | some actual =>
          have hquery' : program.query? (⟨physical, by omega⟩ : Fin L)
              state = some actual := by
            simpa [layer] using hquery
          by_cases hcount : queryCount < master.length
          · by_cases heq : actual = master.get ⟨queryCount, hcount⟩
            · rw [mandatoryQuerySeek, rejectingMasterPhysicalResult,
                hquery']
              change mandatoryQueryStateResult program master input queryCount
                  (if h : queryCount < master.length then
                    if actual = master.get ⟨queryCount, h⟩ then
                      Sum.inl ((⟨physical, by omega⟩ : Fin L), state)
                    else Sum.inr false
                  else Sum.inr false) =
                (if h : queryCount < master.length then
                  if actual = master.get ⟨queryCount, h⟩ then
                    rejectingMasterPhysicalResult program master input
                      (queryCount + 1) fuel (physical + 1) (by omega)
                      (program.next (⟨physical, by omega⟩ : Fin L) state
                        (some (input actual)))
                  else false
                else false)
              rw [dif_pos hcount, if_pos heq, dif_pos hcount, if_pos heq]
              rw [mandatoryQueryStateResult, dif_pos hcount]
              have hfuel : L - (physical + 1) = fuel := by omega
              subst fuel
              subst actual
              rfl
            · rw [mandatoryQuerySeek, rejectingMasterPhysicalResult,
                hquery']
              change mandatoryQueryStateResult program master input queryCount
                  (if h : queryCount < master.length then
                    if actual = master.get ⟨queryCount, h⟩ then
                      Sum.inl ((⟨physical, by omega⟩ : Fin L), state)
                    else Sum.inr false
                  else Sum.inr false) =
                (if h : queryCount < master.length then
                  if actual = master.get ⟨queryCount, h⟩ then
                    rejectingMasterPhysicalResult program master input
                      (queryCount + 1) fuel (physical + 1) (by omega)
                      (program.next (⟨physical, by omega⟩ : Fin L) state
                        (some (input actual)))
                  else false
                else false)
              rw [dif_pos hcount, if_neg heq, dif_pos hcount, if_neg heq]
              rfl
          · rw [mandatoryQuerySeek, rejectingMasterPhysicalResult,
              hquery']
            change mandatoryQueryStateResult program master input queryCount
                (if h : queryCount < master.length then
                  if actual = master.get ⟨queryCount, h⟩ then
                    Sum.inl ((⟨physical, by omega⟩ : Fin L), state)
                  else Sum.inr false
                else Sum.inr false) =
              (if h : queryCount < master.length then
                if actual = master.get ⟨queryCount, h⟩ then
                  rejectingMasterPhysicalResult program master input
                    (queryCount + 1) fuel (physical + 1) (by omega)
                    (program.next (⟨physical, by omega⟩ : Fin L) state
                      (some (input actual)))
                else false
              else false)
            rw [dif_neg hcount, dif_neg hcount]
            rfl

/-- One mandatory target query preserves the denotational result and the
validity invariant. -/
theorem collapseToMandatoryFixedOrder_step {n L : Nat}
    (program : LayeredQueryProgram n L) (master : List (Fin n))
    (hmaster : master.Nodup) (input : Fin n → Bool)
    (layer : Fin n) (state : MandatoryQueryCollapseState program)
    (hvalid : MandatoryQueryStateValid program master layer.val state) :
    let nextState :=
      (collapseToMandatoryFixedOrder program master hmaster).next layer state
        (some (input (completeMasterQuery master hmaster layer)))
    MandatoryQueryStateValid program master (layer.val + 1) nextState ∧
      mandatoryQueryStateResult program master input layer.val state =
        mandatoryQueryStateResult program master input (layer.val + 1)
          nextState := by
  cases state with
  | inr done =>
      simp [collapseToMandatoryFixedOrder, MandatoryQueryStateValid,
        mandatoryQueryStateResult]
  | inl running =>
      simp only [MandatoryQueryStateValid] at hvalid
      choose hcount hquery using hvalid
      have hcoordinate : completeMasterQuery master hmaster layer =
          master.get ⟨layer.val, hcount⟩ :=
        completeMasterQuery_eq_master_get_of_lt master hmaster layer hcount
      constructor
      · simpa [collapseToMandatoryFixedOrder, mandatoryQueryResume,
          hcoordinate] using
          mandatoryQuerySeek_valid program master (layer.val + 1)
            (L - (running.1.val + 1)) (running.1.val + 1) (by omega)
            (program.next running.1 running.2
              (some (input (master.get ⟨layer.val, hcount⟩))))
      · rw [mandatoryQueryStateResult]
        rw [dif_pos hcount]
        rw [hcoordinate]
        symm
        simpa [collapseToMandatoryFixedOrder, mandatoryQueryResume,
          hcoordinate] using
          mandatoryQuerySeek_result program master input (layer.val + 1)
            (L - (running.1.val + 1)) (running.1.val + 1) (by omega)
            (program.next running.1 running.2
              (some (input (master.get ⟨layer.val, hcount⟩))))

/-- Every executed target prefix remains a valid suspension, while its
interpreted Boolean result stays constant. -/
theorem collapseToMandatoryFixedOrder_executePrefix_invariant {n L : Nat}
    (program : LayeredQueryProgram n L) (master : List (Fin n))
    (hmaster : master.Nodup) (input : Fin n → Bool)
    (k : Nat) (hk : k ≤ n) :
    let target := collapseToMandatoryFixedOrder program master hmaster
    let executed := target.executePrefix input k hk
    MandatoryQueryStateValid program master k executed.1 ∧
      mandatoryQueryStateResult program master input 0 target.start =
        mandatoryQueryStateResult program master input k executed.1 := by
  induction k with
  | zero =>
      dsimp only
      simp only [executePrefix]
      constructor
      · exact mandatoryQuerySeek_valid program master 0 L 0 (by omega)
          program.start
      · trivial
  | succ k ih =>
      let target := collapseToMandatoryFixedOrder program master hmaster
      let previous := target.executePrefix input k (by omega)
      let layer : Fin n := ⟨k, by omega⟩
      have hprevious := ih (by omega)
      dsimp only at hprevious
      have hstep := collapseToMandatoryFixedOrder_step program master hmaster
        input layer previous.1 hprevious.1
      dsimp only at hstep
      dsimp only
      simp only [executePrefix]
      change MandatoryQueryStateValid program master (k + 1)
          (target.next layer previous.1
            (some (input (completeMasterQuery master hmaster layer)))) ∧
        mandatoryQueryStateResult program master input 0 target.start =
          mandatoryQueryStateResult program master input (k + 1)
            (target.next layer previous.1
              (some (input (completeMasterQuery master hmaster layer))))
      exact ⟨hstep.1, hprevious.2.trans hstep.2⟩

/-- The mandatory program evaluates to the direct rejecting-master physical
semantics.  This theorem closes the optional-layer-to-mandatory-layer part of
the conversion, independently of the strict guard wrapper. -/
theorem collapseToMandatoryFixedOrder_eval_eq_physicalResult {n L : Nat}
    (program : LayeredQueryProgram n L) (master : List (Fin n))
    (hmaster : master.Nodup) (input : Fin n → Bool) :
    (collapseToMandatoryFixedOrder program master hmaster).eval input =
      rejectingMasterPhysicalResult program master input 0 L 0 (by omega)
        program.start := by
  let target := collapseToMandatoryFixedOrder program master hmaster
  let final := target.executePrefix input n le_rfl
  have hinvariant :=
    collapseToMandatoryFixedOrder_executePrefix_invariant
      program master hmaster input n le_rfl
  dsimp only at hinvariant
  have houtput : target.output final.1 =
      mandatoryQueryStateResult program master input n final.1 := by
    cases hstate : final.1 with
    | inr done =>
        rfl
    | inl running =>
        have hstate' :
            ((collapseToMandatoryFixedOrder program master hmaster).executePrefix
              input n le_rfl).1 = Sum.inl running := by
          simpa [final, target] using hstate
        rw [hstate'] at hinvariant
        have hvalid : MandatoryQueryStateValid program master n
            (Sum.inl running) := by
          exact hinvariant.1
        simp only [MandatoryQueryStateValid] at hvalid
        choose hcount _ using hvalid
        have hlength := master_length_le_of_nodup master hmaster
        omega
  unfold eval finalState
  change target.output final.1 = _
  rw [houtput, ← hinvariant.2]
  simpa [target, collapseToMandatoryFixedOrder] using
    mandatoryQuerySeek_result program master input 0 L 0 (by omega)
      program.start

/-! ## Identification with the strict rejecting guard -/

/-- Execute a suffix of physical layers from an arbitrary live state. -/
def executePhysicalStateFrom {n L : Nat}
    (program : LayeredQueryProgram n L) (input : Fin n → Bool) :
    (fuel physical : Nat) → physical + fuel = L → program.State →
      program.State
  | 0, _, _, state => state
  | fuel + 1, physical, hphysical, state =>
      let layer : Fin L := ⟨physical, by omega⟩
      executePhysicalStateFrom program input fuel (physical + 1) (by omega)
        (program.next layer state ((program.query? layer state).map input))

/-- Running the suffix after an ordinary prefix reaches the ordinary final
state. -/
theorem executePhysicalStateFrom_executePrefix {n L : Nat}
    (program : LayeredQueryProgram n L) (input : Fin n → Bool)
    (fuel physical : Nat) (hphysical : physical + fuel = L) :
    executePhysicalStateFrom program input fuel physical hphysical
        (program.executePrefix input physical (by omega)).1 =
      (program.executePrefix input L le_rfl).1 := by
  induction fuel generalizing physical with
  | zero =>
      have hphysicalEq : physical = L := by omega
      subst physical
      rfl
  | succ fuel ih =>
      rw [executePhysicalStateFrom]
      have hprefix :
          program.next (⟨physical, by omega⟩ : Fin L)
              (program.executePrefix input physical (by omega)).1
              ((program.query? (⟨physical, by omega⟩ : Fin L)
                (program.executePrefix input physical (by omega)).1).map
                  input) =
            (program.executePrefix input (physical + 1) (by omega)).1 := by
        rfl
      rw [hprefix]
      exact ih (physical + 1) (by omega)

/-- The strict guard's rejection sink remains a sink under every physical
suffix. -/
theorem rejectingGuard_executePhysicalStateFrom_none {n L : Nat}
    (program : LayeredQueryProgram n L) (master : List (Fin n))
    (input : Fin n → Bool) (fuel physical : Nat)
    (hphysical : physical + fuel = L) :
    executePhysicalStateFrom (rejectingGuardByMasterOrder program master)
      input fuel physical hphysical none = none := by
  induction fuel generalizing physical with
  | zero => rfl
  | succ fuel ih =>
      rw [executePhysicalStateFrom]
      change executePhysicalStateFrom
        (rejectingGuardByMasterOrder program master) input fuel
          (physical + 1) (by omega) none = none
      exact ih (physical + 1) (by omega)

/-- Starting from a live strict-guard state, physical suffix execution has
exactly the direct rejecting-master result. -/
theorem rejectingGuard_executePhysicalStateFrom_some {n L : Nat}
    (program : LayeredQueryProgram n L) (master : List (Fin n))
    (input : Fin n → Bool) (fuel physical : Nat)
    (hphysical : physical + fuel = L) (state : program.State)
    (cursor : MasterCursor master) :
    (rejectingGuardByMasterOrder program master).output
        (executePhysicalStateFrom
          (rejectingGuardByMasterOrder program master) input fuel physical
          hphysical (some (state, cursor))) =
      rejectingMasterPhysicalResult program master input cursor.val
        fuel physical hphysical state := by
  induction fuel generalizing physical state cursor with
  | zero =>
      rfl
  | succ fuel ih =>
      let layer : Fin L := ⟨physical, by omega⟩
      cases hbase : program.query? layer state with
      | none =>
          have hbase' : program.query? (⟨physical, by omega⟩ : Fin L)
              state = none := by
            simpa [layer] using hbase
          rw [executePhysicalStateFrom, rejectingMasterPhysicalResult,
            hbase']
          simp only [rejectingGuardByMasterOrder,
            rejectingMasterGuardQuery?, rejectingMasterGuardNext,
            masterGuardedQuery?, hbase', Option.map_none]
          change (rejectingGuardByMasterOrder program master).output
              (executePhysicalStateFrom
                (rejectingGuardByMasterOrder program master) input fuel
                (physical + 1) (by omega)
                (some
                  (program.next (⟨physical, by omega⟩ : Fin L) state none,
                    cursor))) =
            rejectingMasterPhysicalResult program master input cursor.val
              fuel (physical + 1) (by omega)
              (program.next (⟨physical, by omega⟩ : Fin L) state none)
          exact ih (physical + 1) (by omega)
            (program.next (⟨physical, by omega⟩ : Fin L) state none) cursor
      | some actual =>
          have hbase' : program.query? (⟨physical, by omega⟩ : Fin L)
              state = some actual := by
            simpa [layer] using hbase
          cases hmasterQuery : masterCursorQuery? master cursor with
          | none =>
              have hnot : ¬cursor.val < master.length := by
                intro hlt
                simp [masterCursorQuery?, hlt] at hmasterQuery
              rw [executePhysicalStateFrom, rejectingMasterPhysicalResult,
                hbase']
              simp only [rejectingGuardByMasterOrder,
                rejectingMasterGuardQuery?, rejectingMasterGuardNext,
                masterGuardedQuery?, hbase', hmasterQuery,
                Option.map_none]
              change (rejectingGuardByMasterOrder program master).output
                  (executePhysicalStateFrom
                    (rejectingGuardByMasterOrder program master) input fuel
                    (physical + 1) (by omega) none) =
                (if h : cursor.val < master.length then
                  if actual = master.get ⟨cursor.val, h⟩ then
                    rejectingMasterPhysicalResult program master input
                      (cursor.val + 1) fuel (physical + 1) (by omega)
                      (program.next (⟨physical, by omega⟩ : Fin L) state
                        (some (input actual)))
                  else false
                else false)
              rw [dif_neg hnot,
                rejectingGuard_executePhysicalStateFrom_none]
              rfl
          | some expected =>
              have hlt : cursor.val < master.length := by
                by_contra hnot
                simp [masterCursorQuery?, hnot] at hmasterQuery
              have hget : master.get ⟨cursor.val, hlt⟩ = expected := by
                simpa [masterCursorQuery?, hlt] using hmasterQuery
              by_cases heq : actual = expected
              · have hactual : actual = master.get ⟨cursor.val, hlt⟩ :=
                  heq.trans hget.symm
                have hexpected : expected = master.get ⟨cursor.val, hlt⟩ :=
                  hget.symm
                have hnext := ih (physical + 1) (by omega)
                  (program.next (⟨physical, by omega⟩ : Fin L) state
                    (some (input actual)))
                  (advanceMasterCursor master cursor)
                rw [advanceMasterCursor_val_of_lt master cursor hlt] at hnext
                rw [executePhysicalStateFrom, rejectingMasterPhysicalResult,
                  hbase']
                simpa [rejectingGuardByMasterOrder,
                  rejectingMasterGuardQuery?, rejectingMasterGuardNext,
                  masterGuardedQuery?, hbase', hmasterQuery, heq, hlt,
                  hget, hactual, hexpected] using hnext
              · have hactual : actual ≠ master.get ⟨cursor.val, hlt⟩ := by
                  intro hsame
                  apply heq
                  exact hsame.trans hget
                rw [executePhysicalStateFrom, rejectingMasterPhysicalResult,
                  hbase']
                simp only [rejectingGuardByMasterOrder,
                  rejectingMasterGuardQuery?, rejectingMasterGuardNext,
                  masterGuardedQuery?, hbase', hmasterQuery, heq]
                change (rejectingGuardByMasterOrder program master).output
                    (executePhysicalStateFrom
                      (rejectingGuardByMasterOrder program master) input fuel
                      (physical + 1) (by omega) none) =
                  (if h : cursor.val < master.length then
                    if actual = master.get ⟨cursor.val, h⟩ then
                      rejectingMasterPhysicalResult program master input
                        (cursor.val + 1) fuel (physical + 1) (by omega)
                        (program.next (⟨physical, by omega⟩ : Fin L) state
                          (some (input actual)))
                    else false
                  else false)
                rw [dif_pos hlt, if_neg hactual,
                  rejectingGuard_executePhysicalStateFrom_none]
                rfl

/-- The ordinary `eval` of the strict rejecting guard is the same direct
physical rejecting-master computation used by the collapse. -/
theorem rejectingGuardByMasterOrder_eval_eq_physicalResult {n L : Nat}
    (program : LayeredQueryProgram n L) (master : List (Fin n))
    (input : Fin n → Bool) :
    (rejectingGuardByMasterOrder program master).eval input =
      rejectingMasterPhysicalResult program master input 0 L 0 (by omega)
        program.start := by
  let guarded := rejectingGuardByMasterOrder program master
  let cursor : MasterCursor master := ⟨0, Nat.zero_lt_succ _⟩
  have hrun := rejectingGuard_executePhysicalStateFrom_some
    program master input L 0 (by omega) program.start cursor
  have hprefix := executePhysicalStateFrom_executePrefix
    guarded input L 0 (by omega)
  unfold eval finalState
  rw [← hprefix]
  simpa [guarded, cursor, executePrefix, rejectingGuardByMasterOrder] using
    hrun

/-- Full semantic bridge: collapsing optional physical layers, completing the
master to a mandatory permutation, and ignoring the dummy suffix preserves
exactly the strict rejecting guard's Boolean function. -/
theorem collapseToMandatoryFixedOrder_eval_eq_rejectingGuard {n L : Nat}
    (program : LayeredQueryProgram n L) (master : List (Fin n))
    (hmaster : master.Nodup) (input : Fin n → Bool) :
    (collapseToMandatoryFixedOrder program master hmaster).eval input =
      (rejectingGuardByMasterOrder program master).eval input := by
  calc
    (collapseToMandatoryFixedOrder program master hmaster).eval input =
        rejectingMasterPhysicalResult program master input 0 L 0 (by omega)
          program.start :=
      collapseToMandatoryFixedOrder_eval_eq_physicalResult
        program master hmaster input
    _ = (rejectingGuardByMasterOrder program master).eval input :=
      (rejectingGuardByMasterOrder_eval_eq_physicalResult
        program master input).symm

/-- Exact width of the silent-query collapse.  The two completed states are
shared across all layers. -/
@[simp]
theorem collapseToMandatoryFixedOrder_width {n L : Nat}
    (program : LayeredQueryProgram n L) (master : List (Fin n))
    (hmaster : master.Nodup) :
    (collapseToMandatoryFixedOrder program master hmaster).width =
      L * program.width + 2 := by
  simp [collapseToMandatoryFixedOrder, MandatoryQueryCollapseState,
    LayeredQueryProgram.width]

end LayeredQueryProgram
end OneTapeMagnification
end Frontier
end Pnp4
