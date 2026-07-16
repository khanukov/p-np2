import Pnp4.Frontier.OneTapeMagnification.LayeredQueryProgram

namespace Pnp4
namespace Frontier
namespace OneTapeMagnification

/-!
# A fixed-order obstruction to bounded conflict-coordinate grouping

Pairwise unambiguity supplies an opposite input coordinate for every pair of
disjoint accepting path cells.  It does not make that coordinate uniform.
The zero input and the unit inputs are the sharp elementary obstruction: the
pair consisting of zero and the `i`-th unit input conflicts only at `i`.
Consequently, any grouping which assigns one common conflict coordinate to
each group needs at least `n` groups.

The small layered program at the end of the file records why a fixed query
order does not remove the obstruction.  It is a width-four, read-once program
for the usual "at most one true bit" scan.  On the last query, the two
different productive states `noneSeen` and `oneSeen` coalesce on the same
`false` answer.  Thus backward same-label coalescence is compatible with a
fixed read-once order.  This module deliberately makes no claim that the
particular program is definitionally the mandatory one-tape compiler output;
such a claim would require a compiler-level trace theorem.
-/

namespace FiniteFixedOrderSiblingConflictCoverObstruction

/-- The all-false Boolean input. -/
def zeroBooleanInput (n : Nat) : Fin n -> Bool :=
  fun _ => false

/-- The Boolean unit input supported at exactly `index`. -/
def unitBooleanInput {n : Nat} (index : Fin n) : Fin n -> Bool :=
  fun coordinate => decide (coordinate = index)

@[simp]
theorem zeroBooleanInput_apply (n : Nat) (coordinate : Fin n) :
    zeroBooleanInput n coordinate = false := rfl

@[simp]
theorem unitBooleanInput_apply_self {n : Nat} (index : Fin n) :
    unitBooleanInput index index = true := by
  simp [unitBooleanInput]

/-- Zero and the `index`-th unit input disagree at exactly `index`. -/
theorem zeroBooleanInput_ne_unitBooleanInput_iff
    {n : Nat} (index coordinate : Fin n) :
    zeroBooleanInput n coordinate != unitBooleanInput index coordinate <->
      coordinate = index := by
  simp [zeroBooleanInput, unitBooleanInput]

/-- Data of a proposed grouping of all zero/unit pairs, together with the
single coordinate advertised for each group. -/
def ZeroUnitCommonConflictGrouping
    (n : Nat) (Group : Type*) (groupOf : Fin n -> Group)
    (coordinate : Group -> Fin n) : Prop :=
  forall index,
    zeroBooleanInput n (coordinate (groupOf index)) !=
      unitBooleanInput index (coordinate (groupOf index))

/-- A valid common-conflict grouping separates every two unit indices.
Hence no group can contain two of the zero/unit point rectangles. -/
theorem zeroUnitCommonConflictGrouping_groupOf_injective
    {n : Nat} {Group : Type*} {groupOf : Fin n -> Group}
    {coordinate : Group -> Fin n}
    (hgrouping : ZeroUnitCommonConflictGrouping
      n Group groupOf coordinate) :
    Function.Injective groupOf := by
  intro left right hequal
  have hleft : coordinate (groupOf left) = left :=
    (zeroBooleanInput_ne_unitBooleanInput_iff
      left (coordinate (groupOf left))).1 (hgrouping left)
  have hright : coordinate (groupOf right) = right :=
    (zeroBooleanInput_ne_unitBooleanInput_iff
      right (coordinate (groupOf right))).1 (hgrouping right)
  exact hleft.symm.trans ((congrArg coordinate hequal).trans hright)

/-- **No bounded conflict-coordinate cover.**  Covering the `n` zero/unit
point rectangles by groups with one common conflict coordinate requires at
least `n` groups. -/
theorem card_group_ge_of_zeroUnitCommonConflictGrouping
    {n : Nat} {Group : Type*} [Fintype Group]
    (groupOf : Fin n -> Group) (coordinate : Group -> Fin n)
    (hgrouping : ZeroUnitCommonConflictGrouping
      n Group groupOf coordinate) :
    n <= Fintype.card Group := by
  rw [<- Fintype.card_fin n]
  exact Fintype.card_le_of_injective groupOf
    (zeroUnitCommonConflictGrouping_groupOf_injective hgrouping)

/-! ## A fixed-order same-label merge -/

/-- Four scan states for the at-most-one predicate.  `accepted` and
`rejected` are used only after the last query. -/
inductive AtMostOneMergeState where
  | noneSeen
  | oneSeen
  | accepted
  | rejected
deriving DecidableEq, Fintype

/-- Update before the last input coordinate. -/
def atMostOneInteriorStep : AtMostOneMergeState -> Bool ->
    AtMostOneMergeState
  | .noneSeen, false => .noneSeen
  | .noneSeen, true => .oneSeen
  | .oneSeen, false => .oneSeen
  | .oneSeen, true => .rejected
  | .accepted, _ => .accepted
  | .rejected, _ => .rejected

/-- Update at the last coordinate.  The two productive prefix states merge
on the same `false` label. -/
def atMostOneFinalStep : AtMostOneMergeState -> Bool ->
    AtMostOneMergeState
  | .noneSeen, _ => .accepted
  | .oneSeen, false => .accepted
  | .oneSeen, true => .rejected
  | .accepted, _ => .accepted
  | .rejected, _ => .rejected

/-- A width-four oblivious scan.  For positive `n`, the last layer performs
the coalescing final transition above. -/
def atMostOneFixedOrderProgram (n : Nat) : LayeredQueryProgram n n where
  State := AtMostOneMergeState
  stateFintype := inferInstance
  start := .noneSeen
  query? := fun layer _ => some layer
  next := fun layer state answer =>
    match answer with
    | none => .rejected
    | some bit =>
        if layer.val + 1 = n then
          atMostOneFinalStep state bit
        else
          atMostOneInteriorStep state bit
  output := fun state => state == .accepted

/-- The scan exposes the identity query order, independently of its state. -/
theorem atMostOneFixedOrderProgram_hasFixedQueryOrder (n : Nat) :
    (atMostOneFixedOrderProgram n).HasFixedQueryOrder
      (fun layer => some layer) := by
  intro layer state
  rfl

/-- In particular, the program is syntactically read-once. -/
theorem atMostOneFixedOrderProgram_isReadOnce (n : Nat) :
    (atMostOneFixedOrderProgram n).IsReadOnce := by
  apply LayeredQueryProgram.isReadOnce_of_fixedQueryOrder_nodup
    (program := atMostOneFixedOrderProgram n)
    (order := fun layer : Fin n => some layer)
      (atMostOneFixedOrderProgram_hasFixedQueryOrder n)
  have hmap : List.ofFn (fun layer : Fin n => some layer) =
      (List.ofFn fun layer : Fin n => layer).map some := by
    rw [List.map_ofFn]
    rfl
  rw [hmap]
  have hfilter :
      List.filterMap id ((List.ofFn fun layer : Fin n => layer).map some) =
        List.ofFn (fun layer : Fin n => layer) := by
    rw [List.filterMap_map]
    simpa only [Function.comp_apply, id_eq] using
      (List.filterMap_some :
        List.filterMap some (List.ofFn fun layer : Fin n => layer) =
          List.ofFn (fun layer : Fin n => layer))
  rw [hfilter]
  exact List.nodup_ofFn.mpr
    (show Function.Injective (fun layer : Fin n => layer) from
      Function.injective_id)

/-- The two productive prefix states take the same false-labelled final edge
to the common accepting state. -/
theorem atMostOneFixedOrderProgram_final_sameLabel_merge
    (n : Nat) (hn : 0 < n) :
    let finalLayer : Fin n := ⟨n - 1, by omega⟩
    (atMostOneFixedOrderProgram n).next finalLayer
          .noneSeen (some false) = .accepted /\
      (atMostOneFixedOrderProgram n).next finalLayer
          .oneSeen (some false) = .accepted /\
      (.noneSeen : AtMostOneMergeState) != .oneSeen := by
  dsimp only
  have hlast : n - 1 + 1 = n := by omega
  simp [atMostOneFixedOrderProgram, hlast, atMostOneFinalStep]

end FiniteFixedOrderSiblingConflictCoverObstruction
end OneTapeMagnification
end Frontier
end Pnp4
