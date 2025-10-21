import Core.PDT
import Core.BooleanBasics
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Zip
import Mathlib.Tactic

/-!
# Trunk builder utilities for partial decision trees

This auxiliary module introduces a handful of purely combinatorial tools that
are convenient when turning partial assignments into explicit trunks of partial
decision trees.  The eventual multi-switching lemma will repeatedly extend a
common trunk by fixing a short list of variables.  In Lean it is helpful to have
self-contained constructors for the corresponding `PDT`s together with their
basic combinatorial properties (depth, leaf dictionary, and uniform branching).

The definitions below intentionally avoid any probabilistic language; they are
agnostic of the shrinkage pipeline and simply provide deterministic building
blocks.  In particular we work with the naive "canonical" trunk that queries the
variables in a prescribed order and stores on each branch the subcube obtained
by fixing the variables encountered so far.

These utilities do not yet prove the multi-switching lemma, but they discharge a
non-trivial amount of bookkeeping that would otherwise obscure the future proof.
Once the constructive argument is ported, the helper lemmas from this file will
be the workhorses for gluing the trunk with the tail witnesses delivered by the
(classical) switching lemma.
-/

namespace Pnp3
namespace Core

open Classical

variable {n : Nat}

/--
`canonicalBase` is the maximally unconstrained subcube on `n` variables.  It is
convenient to keep it as a named definition because many helper lemmas below
reason by induction over the list of trunk variables and explicitly re-use this
starting point.
-/
@[simp] def canonicalBase (n : Nat) : Subcube n := fun _ => (none : Option Bool)

/--
Extend a subcube `β` by fixing the variable `i` to the Boolean value `b`.  The
result is again a subcube; we deliberately avoid `Subcube.assign` and write down
an explicit closed form that is computationally convenient inside proofs.  When
multiple assignments are chained, the "latest" value wins, exactly mirroring the
behaviour of the usual restriction operations used in the switching-lemma
literature.
-/
@[simp] def extendSubcube (β : Subcube n) (i : Fin n) (b : Bool) : Subcube n :=
  fun j => if j = i then some b else β j

/--
Given a list of variable indices `vars`, construct the canonical trunk that
queries them one by one.  The leaves store the subcubes obtained after fixing
all encountered variables according to the path.  The base case corresponds to a
single leaf, whereas the inductive step creates a binary node that branches on
`i` and recursively builds the remaining trunk for the updated subcubes.
-/
def trunkOfList : Subcube n → List (Fin n) → PDT n
  | β, [] => PDT.leaf β
  | β, i :: rest =>
      let β0 := extendSubcube β i false
      let β1 := extendSubcube β i true
      PDT.node i (trunkOfList β0 rest) (trunkOfList β1 rest)

@[simp] lemma trunkOfList_nil (β : Subcube n) :
    trunkOfList (n := n) β [] = PDT.leaf β := rfl

@[simp] lemma trunkOfList_cons (β : Subcube n) (i : Fin n) (rest : List (Fin n)) :
    trunkOfList (n := n) β (i :: rest)
      = PDT.node i (trunkOfList (n := n) (extendSubcube β i false) rest)
          (trunkOfList (n := n) (extendSubcube β i true) rest) := rfl

/-- The depth of the canonical trunk equals the length of the variable list. -/
lemma depth_trunkOfList :
    ∀ vars (β : Subcube n),
      PDT.depth (trunkOfList (n := n) β vars) = vars.length := by
  intro vars
  induction vars with
  | nil =>
      intro β
      simp [trunkOfList, PDT.depth]
  | cons i rest ih =>
      intro β
      have hfalse := ih (extendSubcube β i false)
      have htrue := ih (extendSubcube β i true)
      calc
        PDT.depth (trunkOfList (n := n) β (i :: rest))
            = Nat.succ
                (Nat.max (PDT.depth (trunkOfList (extendSubcube β i false) rest))
                  (PDT.depth (trunkOfList (extendSubcube β i true) rest))) := by
              simp [trunkOfList, PDT.depth]
        _ = Nat.succ (Nat.max rest.length rest.length) := by
              simp [hfalse, htrue]
        _ = Nat.succ rest.length := by simp
        _ = (i :: rest).length := by simp

/--
Enumerate all subcubes that appear as leaves of the canonical trunk.  The
construction mirrors `trunkOfList`: at each recursive step we duplicate the list
and extend the running subcube with the two possible Boolean assignments for the
current variable.
-/
def trunkLeaves : Subcube n → List (Fin n) → List (Subcube n)
  | β, [] => [β]
  | β, i :: rest =>
      let β0 := extendSubcube β i false
      let β1 := extendSubcube β i true
      trunkLeaves β0 rest ++ trunkLeaves β1 rest

@[simp] lemma trunkLeaves_nil (β : Subcube n) :
    trunkLeaves (n := n) β [] = [β] := rfl

@[simp] lemma trunkLeaves_cons (β : Subcube n) (i : Fin n) (rest : List (Fin n)) :
    trunkLeaves (n := n) β (i :: rest)
      = trunkLeaves (n := n) (extendSubcube β i false) rest
          ++ trunkLeaves (n := n) (extendSubcube β i true) rest := rfl

/--
The leaves of the canonical trunk are exactly the subcubes listed by
`trunkLeaves`.  This is an entirely syntactic statement proved by structural
induction.
-/
lemma leaves_trunkOfList :
    ∀ vars (β : Subcube n),
      PDT.leaves (trunkOfList (n := n) β vars)
        = trunkLeaves (n := n) β vars := by
  intro vars
  induction vars with
  | nil =>
      intro β
      simp [trunkOfList, trunkLeaves, PDT.leaves]
  | cons i rest ih =>
      intro β
      have hfalse := ih (extendSubcube β i false)
      have htrue := ih (extendSubcube β i true)
      simp [trunkOfList, trunkLeaves, PDT.leaves, hfalse, htrue]

/--
The canonical trunk on `vars` has exactly `2 ^ vars.length` leaves.  This will be
handy when reasoning about the size of the dictionary exported by the eventual
multi-switching witness.
-/
lemma length_trunkLeaves :
    ∀ vars (β : Subcube n),
      (trunkLeaves (n := n) β vars).length = Nat.pow 2 vars.length := by
  intro vars
  induction vars with
  | nil =>
      intro β
      simp [trunkLeaves]
  | cons i rest ih =>
      intro β
      have hfalse := ih (extendSubcube β i false)
      have htrue := ih (extendSubcube β i true)
      simp [trunkLeaves, hfalse, htrue, Nat.pow_succ, List.length_append,
        Nat.mul_comm, two_mul]

/--
Specialisation of the depth formula to the canonical base.  The statement is
isolated because the multi-switching witness will almost always start from the
maximally unconstrained cube.
-/
lemma depth_trunkOfList_base (vars : List (Fin n)) :
    PDT.depth (trunkOfList (n := n) (canonicalBase n) vars)
        = vars.length :=
  depth_trunkOfList (n := n) vars (canonicalBase n)

/--
Convenient alias: the canonical trunk that starts from the full cube and queries
variables according to `vars`.
-/
@[simp] def canonicalTrunk (vars : List (Fin n)) : PDT n :=
  trunkOfList (n := n) (canonicalBase n) vars

lemma depth_canonicalTrunk (vars : List (Fin n)) :
    PDT.depth (canonicalTrunk (n := n) vars) = vars.length := by
  simpa [canonicalTrunk] using depth_trunkOfList_base (n := n) vars

lemma leaves_canonicalTrunk (vars : List (Fin n)) :
    PDT.leaves (canonicalTrunk (n := n) vars)
      = trunkLeaves (n := n) (canonicalBase n) vars := by
  simpa [canonicalTrunk] using
    leaves_trunkOfList (n := n) vars (canonicalBase n)

lemma length_leaves_canonicalTrunk (vars : List (Fin n)) :
    (PDT.leaves (canonicalTrunk (n := n) vars)).length
      = Nat.pow 2 vars.length := by
  have hlen := length_trunkLeaves (n := n) vars (canonicalBase n)
  have hleaves := congrArg List.length
    (leaves_canonicalTrunk (n := n) vars)
  simpa [canonicalTrunk] using hleaves.trans hlen

/--
  Refining the canonical trunk on `vars₁` with the canonical extensions on `vars₂`
  reconstructs the canonical trunk on the concatenated list.  This lemma is the
  workhorse behind splitting a full decision tree into a short trunk with
  uniform tails and will be reused when turning perfect certificates into
  partial witnesses.
-/
lemma refine_trunkOfList_append
    (β : Subcube n) (vars₁ vars₂ : List (Fin n)) :
    PDT.refine (trunkOfList (n := n) β vars₁)
        (fun γ _ => trunkOfList (n := n) γ vars₂)
      = trunkOfList (n := n) β (vars₁ ++ vars₂) := by
  induction vars₁ generalizing β with
  | nil =>
      simp [trunkOfList, PDT.refine]
  | cons i rest ih =>
      simp [trunkOfList, PDT.refine, ih, List.cons_append]

/--
`extendSubcubeMany` iteratively applies `extendSubcube` along a list of
assignments.  We represent assignments as pairs `(i, b)` where `i` is the
queried variable and `b` is the Boolean value taken along the branch.  This
definition mirrors the behaviour of `Subcube.assignMany`, but it never fails:
the more permissive semantics (later assignments override earlier ones) match
what `trunkOfList` uses internally.
-/
def extendSubcubeMany : Subcube n → List (BitFix n) → Subcube n
  | β, [] => β
  | β, (i, b) :: rest => extendSubcubeMany (extendSubcube β i b) rest

@[simp] lemma extendSubcubeMany_nil (β : Subcube n) :
    extendSubcubeMany (n := n) β [] = β := rfl

@[simp] lemma extendSubcubeMany_cons (β : Subcube n) (i : Fin n)
    (b : Bool) (rest : List (BitFix n)) :
    extendSubcubeMany (n := n) β ((i, b) :: rest)
      = extendSubcubeMany (n := n)
          (extendSubcube β i b) rest := rfl

/--
  A helper family enumerating all Boolean vectors of length `ℓ`.  The definition
  is intentionally lightweight: it is a straightforward recursion that keeps the
  combinatorics explicit and amenable to rewriting with `simp`.
-/
@[simp] def boolVectors : Nat → List (List Bool)
  | 0 => [[]]
  | Nat.succ ℓ =>
      (boolVectors ℓ).map (List.cons false)
        ++ (boolVectors ℓ).map (List.cons true)

lemma mem_boolVectors_length :
    ∀ {ℓ : Nat} {bits : List Bool}, bits ∈ boolVectors ℓ →
        bits.length = ℓ := by
  intro ℓ
  induction ℓ with
  | zero =>
      intro bits hbits
      have hmem : bits = [] := by
        simpa using hbits
      simpa [hmem]
  | succ ℓ ih =>
      intro bits hbits
      have hdef :
          boolVectors (Nat.succ ℓ) =
            (boolVectors ℓ).map (List.cons false)
              ++ (boolVectors ℓ).map (List.cons true) := rfl
      have hcases : bits ∈ (boolVectors ℓ).map (List.cons false)
            ∨ bits ∈ (boolVectors ℓ).map (List.cons true) :=
        List.mem_append.mp (by simpa [hdef] using hbits)
      rcases hcases with hfalse | htrue
      · obtain ⟨tail, htail, rfl⟩ := List.mem_map.mp hfalse
        have hlen := ih htail
        simp [hlen]
      · obtain ⟨tail, htail, rfl⟩ := List.mem_map.mp htrue
        have hlen := ih htail
        simp [hlen]

lemma boolVectors_length (ℓ : Nat) :
    (boolVectors ℓ).length = Nat.pow 2 ℓ := by
  induction ℓ with
  | zero => simp
  | succ ℓ ih =>
      simp [boolVectors, List.length_map, List.length_append, ih,
        Nat.pow_succ, Nat.mul_comm, two_mul]

/--
  Interpret a list of Boolean choices as a sequence of assignments to a fixed
  list of variables.  The recursion is perfectly aligned with `extendSubcube`:
  each step fixes the head variable to the head Boolean and continues with the
  tail.
-/
def extendSubcubeWithBits (β : Subcube n) :
    List (Fin n) → List Bool → Subcube n
  | [], _ => β
  | _ :: _, [] => β
  | i :: vars, b :: bits =>
      extendSubcubeWithBits (extendSubcube β i b) vars bits

@[simp] lemma extendSubcubeWithBits_nil_vars (β : Subcube n)
    (bits : List Bool) :
    extendSubcubeWithBits (n := n) β [] bits = β := rfl

@[simp] lemma extendSubcubeWithBits_nil_bits (β : Subcube n)
    (i : Fin n) (vars : List (Fin n)) :
    extendSubcubeWithBits (n := n) β (i :: vars) [] = β := rfl

@[simp] lemma extendSubcubeWithBits_cons (β : Subcube n) (i : Fin n)
    (vars : List (Fin n)) (b : Bool) (bits : List Bool) :
    extendSubcubeWithBits (n := n) β (i :: vars) (b :: bits)
      = extendSubcubeWithBits (n := n)
          (extendSubcube β i b) vars bits := rfl

/--
  Each leaf of the canonical trunk corresponds to one Boolean vector describing
  the choices taken along the branches.  This lemma packages the correspondence
  by rewriting the leaf dictionary as the image of `extendSubcubeWithBits` over
  all Boolean vectors of the appropriate length.
-/
lemma trunkLeaves_as_boolVectors :
    ∀ vars : List (Fin n), ∀ β : Subcube n,
      trunkLeaves (n := n) β vars
        = (boolVectors vars.length).map
            (fun bits => extendSubcubeWithBits (n := n) β vars bits) := by
  intro vars
  induction vars with
  | nil =>
      intro β
      simp
  | cons i rest ih =>
      intro β
      have hfalse := ih (extendSubcube β i false)
      have htrue := ih (extendSubcube β i true)
      let L := boolVectors rest.length
      let f := fun bits => extendSubcubeWithBits (n := n) β (i :: rest) bits
      have hfalse' : trunkLeaves (n := n) (extendSubcube β i false) rest
          = List.map (f ∘ List.cons false) L := by
        simpa [L, f, List.map_map, Function.comp,
          extendSubcubeWithBits_cons] using hfalse
      have htrue' : trunkLeaves (n := n) (extendSubcube β i true) rest
          = List.map (f ∘ List.cons true) L := by
        simpa [L, f, List.map_map, Function.comp,
          extendSubcubeWithBits_cons] using htrue
      have hdecomp :
          List.map (f ∘ List.cons false) L ++ List.map (f ∘ List.cons true) L
            = List.map f (boolVectors (Nat.succ rest.length)) := by
        simp [L, f, boolVectors, List.map_append, List.map_map,
          Function.comp]
      calc
        trunkLeaves (n := n) β (i :: rest)
            = trunkLeaves (n := n) (extendSubcube β i false) rest
                ++ trunkLeaves (n := n) (extendSubcube β i true) rest := by
                  simp [trunkLeaves]
        _ = List.map (f ∘ List.cons false) L
              ++ List.map (f ∘ List.cons true) L := by
                  simp [hfalse', htrue']
        _ = List.map f (boolVectors (Nat.succ rest.length)) := hdecomp
        _ = (boolVectors (Nat.succ rest.length)).map
              (fun bits => extendSubcubeWithBits (n := n) β (i :: rest) bits) := by
                simp [f]
        _ = (boolVectors (i :: rest).length).map
              (fun bits => extendSubcubeWithBits (n := n) β (i :: rest) bits) := by
                simp

lemma leaves_canonicalTrunk_as_boolVectors (vars : List (Fin n)) :
    PDT.leaves (canonicalTrunk (n := n) vars)
      = (boolVectors vars.length).map
          (fun bits => extendSubcubeWithBits (n := n)
            (canonicalBase n) vars bits) := by
  have hLeaves := leaves_canonicalTrunk (n := n) vars
  have hDict := trunkLeaves_as_boolVectors (n := n) (vars := vars)
      (β := canonicalBase n)
  simpa [canonicalTrunk] using hLeaves.trans hDict

/--
  A convenient combinatorial dictionary: the number of Boolean vectors of
  length `ℓ` is `2^ℓ`.  This mirrors the `length_trunkLeaves` lemma and keeps
  both views (as vectors and as trunk leaves) in sync.
-/
lemma boolVectors_length_canonical (vars : List (Fin n)) :
    (boolVectors vars.length).length = Nat.pow 2 vars.length := by
  simpa using boolVectors_length vars.length

/--
  `freeOn β vars` states that a subcube assigns `none` to every variable from
  `vars`.  The predicate is tailored to reason about sequences of compatible
  assignments and behaves well under extensions of the subcube.
-/
def freeOn (β : Subcube n) (vars : List (Fin n)) : Prop :=
  ∀ i ∈ vars, β i = none

lemma freeOn_nil (β : Subcube n) :
    freeOn (n := n) β [] := by
  intro i hi
  cases hi

lemma freeOn_cons_head {β : Subcube n} {i : Fin n} {vars : List (Fin n)}
    (h : freeOn (n := n) β (i :: vars)) : β i = none := by
  exact h _ (by simp)

lemma freeOn_cons_tail {β : Subcube n} {i : Fin n} {vars : List (Fin n)}
    (h : freeOn (n := n) β (i :: vars)) :
    freeOn (n := n) β vars := by
  intro j hj
  exact h _ (List.mem_cons.mpr (Or.inr hj))

lemma canonicalBase_freeOn (vars : List (Fin n)) :
    freeOn (n := n) (canonicalBase n) vars := by
  intro i hi
  simp [canonicalBase]

lemma extendSubcube_apply_eq (β : Subcube n) (i : Fin n)
    (b : Bool) : extendSubcube β i b i = some b := by
  simp [extendSubcube]

lemma extendSubcube_apply_ne {β : Subcube n} {i j : Fin n}
    {b : Bool} (hji : j ≠ i) :
    extendSubcube β i b j = β j := by
  simp [extendSubcube, hji]

lemma freeOn_extend_subcube {β : Subcube n} {i : Fin n}
    {vars : List (Fin n)} {b : Bool}
    (hfree : freeOn (n := n) β (i :: vars))
    (hnot : i ∉ vars) :
    freeOn (n := n) (extendSubcube β i b) vars := by
  intro j hj
  have hjne : j ≠ i := by
    intro hji
    exact hnot (by simpa [hji] using hj)
  have htail := freeOn_cons_tail (n := n) (β := β) (i := i) (vars := vars) hfree
  have hβ := htail j hj
  simpa [extendSubcube, hjne] using hβ

lemma assign_extend_eq_extendSubcube
    {β : Subcube n} {i : Fin n} {b : Bool}
    (h : β i = none) :
    Subcube.assign β i b = some (extendSubcube β i b) := by
  unfold Subcube.assign
  have hfun : (fun j => if j = i then some b else β j)
      = extendSubcube β i b := by
    funext j; simp [extendSubcube]
  simpa [h, hfun]

lemma assignMany_freeOn_eq_extend
    {cube : Subcube n} {vars : List (Fin n)} {bits : List Bool}
    (hfree : freeOn (n := n) cube vars)
    (hndVars : vars.Nodup)
    (hlen : bits.length = vars.length) :
    Subcube.assignMany cube (List.zip vars bits)
      = some (extendSubcubeWithBits (n := n) cube vars bits) := by
  induction vars generalizing cube bits with
  | nil =>
      cases bits with
      | nil =>
          simp
      | cons b tail =>
          have : tail.length.succ = 0 := by simpa using hlen
          cases this
  | cons i rest ih =>
      cases bits with
      | nil =>
          have : (0 : Nat) = rest.length.succ := by simpa using hlen
          cases this
      | cons b tail =>
          have hlen' : tail.length = rest.length := by
            have : tail.length.succ = rest.length.succ := by simpa using hlen
            exact Nat.succ.inj this
          have hβi : cube i = none :=
            freeOn_cons_head (n := n) (β := cube) (i := i) (vars := rest) hfree
          have hrest_free : freeOn (n := n) cube rest :=
            freeOn_cons_tail (n := n) (β := cube) (i := i) (vars := rest) hfree
          have hnodup := List.nodup_cons.mp hndVars
          have htail_nodup : rest.Nodup := hnodup.2
          have hnot_mem : i ∉ rest := hnodup.1
          have hassign := assign_extend_eq_extendSubcube (n := n)
            (β := cube) (i := i) (b := b) hβi
          have hfree_next :
              freeOn (n := n) (extendSubcube cube i b) rest :=
            freeOn_extend_subcube (n := n) (β := cube) (i := i)
              (vars := rest) (b := b) hfree hnot_mem
          have hind := ih (cube := extendSubcube cube i b) (bits := tail)
            hfree_next htail_nodup hlen'
          have hzip :
              List.zip (i :: rest) (b :: tail)
                = (i, b) :: List.zip rest tail := rfl
          have hbits :
              extendSubcubeWithBits (n := n) cube (i :: rest) (b :: tail)
                = extendSubcubeWithBits (n := n)
                    (extendSubcube cube i b) rest tail := by
            simp
          simpa [Subcube.assignMany, hzip, hassign, hbits]
            using hind

lemma assignMany_canonicalBase_eq_extend
    {vars : List (Fin n)} {bits : List Bool}
    (hnd : vars.Nodup)
    (hlen : bits.length = vars.length) :
    Subcube.assignMany (canonicalBase n) (List.zip vars bits)
      = some (extendSubcubeWithBits (n := n)
          (canonicalBase n) vars bits) := by
  have hfree := canonicalBase_freeOn (n := n) vars
  exact assignMany_freeOn_eq_extend (n := n)
    (cube := canonicalBase n) (vars := vars) (bits := bits)
    hfree hnd hlen

/--
  Interpret a Boolean list of length `n` as a bit vector.  The definition is
  intentionally explicit: we take the element of `bits` at position `i` and use
  it as the `i`-th coordinate of the resulting `BitVec`.  The length witness
  `hlen` ensures that the index is always within bounds.
-/
@[simp] def bitVecOfList (bits : List Bool) (hlen : bits.length = n) : BitVec n :=
  fun i =>
    have hi : i.val < bits.length := by
      simpa [hlen] using i.isLt
    bits.get ⟨i.val, hi⟩

lemma bitVecOfList_cons_head {bits : List Bool} {n : Nat}
    (b : Bool) {hlen : (b :: bits).length = Nat.succ n} :
    bitVecOfList (n := Nat.succ n) (b :: bits) hlen 0 = b := by
  have hlen' : (b :: bits).length = Nat.succ n := hlen
  have hzero : (0 : Fin (Nat.succ n)).val < (b :: bits).length := by
    simpa [hlen'] using (Fin.zero_lt (Nat.succ n))
  simp [bitVecOfList, hlen', hzero]

lemma bitVecOfList_cons_succ {bits : List Bool} {n : Nat}
    (b : Bool) (i : Fin n)
    {hlen : (b :: bits).length = Nat.succ n} :
    bitVecOfList (n := Nat.succ n) (b :: bits) hlen i.succ
      = bitVecOfList (n := n) bits (by
          have hlen' : (b :: bits).length = Nat.succ n := hlen
          have : bits.length = n := by
            simpa using Nat.succ.inj hlen'
          simpa [this]) i := by
  -- Temporarily name the proof of `bits.length = n` to keep subsequent rewrites
  -- compact.  The `Nat.succ.inj` used above is safe because the list length is
  -- non-zero in the `succ` case.
  have hlen_list : bits.length = n := by
    have hlen' : (b :: bits).length = Nat.succ n := hlen
    simpa using Nat.succ.inj hlen'
  have hi : i.val < bits.length := by
    simpa [hlen_list] using i.isLt
  have hisucc : i.succ.val < (b :: bits).length := by
    simpa [Nat.succ_eq_add_one, hlen_list] using Nat.succ_lt_succ i.isLt
  simp [bitVecOfList, hisucc, hlen, hlen_list, hi]

/--
  Sequential assignments along `vars`/`bits` can be expressed either via the
  specialised recursion `extendSubcubeWithBits` or via the generic
  `extendSubcubeMany` helper that works with lists of `(Fin n, Bool)` pairs.  The
  statement below keeps the two constructions interchangeable.
-/
lemma extendSubcubeWithBits_eq_extendSubcubeMany
    (β : Subcube n) (vars : List (Fin n)) (bits : List Bool) :
    extendSubcubeWithBits (n := n) β vars bits
      = extendSubcubeMany (n := n) β (List.zip vars bits) := by
  revert bits
  induction vars generalizing β with
  | nil =>
      intro bits
      cases bits with
      | nil => simp [extendSubcubeWithBits, extendSubcubeMany]
      | cons b tail => simp [extendSubcubeWithBits, extendSubcubeMany]
  | cons i rest ih =>
      intro bits
      cases bits with
      | nil =>
          simp [extendSubcubeWithBits, extendSubcubeMany]
      | cons b tail =>
          simp [extendSubcubeWithBits, extendSubcubeMany, ih,
            List.zip_cons_cons]

/--
  Evaluating `extendSubcubeMany` at an index unaffected by the assignment list
  keeps the original value.  We use this frequently when reasoning about leaves
  of canonical trunks where each variable is queried at most once.
-/
lemma extendSubcubeMany_preserve
    (β : Subcube n) (assigns : List (BitFix n)) (i : Fin n)
    (hdisjoint : ∀ u ∈ assigns, u.1 ≠ i) :
    extendSubcubeMany (n := n) β assigns i = β i := by
  revert β
  induction assigns with
  | nil => simp
  | cons head tail ih =>
      intro β
      rcases head with ⟨j, b⟩
      have htail : ∀ u ∈ tail, u.1 ≠ i := by
        intro u hu
        exact hdisjoint u (List.mem_cons.mpr (Or.inr hu))
      have hji : j ≠ i := by
        have := hdisjoint ⟨j, b⟩ (by simp)
        exact this
      have hij : i ≠ j := by
        intro h
        exact hji h.symm
      have hstep := ih (β := extendSubcube β j b) htail
      have hrewrite : (extendSubcube β j b) i = β i := by
        simp [extendSubcube_apply_ne, hij]
      have hEval : extendSubcubeMany β ((j, b) :: tail) i
          = extendSubcubeMany (extendSubcube β j b) tail i := by
        simp [extendSubcubeMany]
      calc
        extendSubcubeMany β ((j, b) :: tail) i
            = extendSubcubeMany (extendSubcube β j b) tail i := hEval
        _ = (extendSubcube β j b) i := hstep
        _ = β i := hrewrite

/--
  Zipping after mapping the first list is equivalent to zipping first and then
  mapping the resulting pairs.  This is a tiny helper tailored to the
  `Fin.succ` reindexing that appears when peeling a canonical trunk.
-/
lemma zip_map_left_eq_map_zip {α β γ : Type*} (f : α → γ) :
    ∀ xs ys,
      List.zip (xs.map f) ys
        = (List.zip xs ys).map (fun v : α × β => (f v.1, v.2)) := by
  intro xs
  induction xs with
  | nil => intro ys; cases ys <;> simp
  | cons x tail ih =>
      intro ys
      cases ys with
      | nil => simp
      | cons y ys =>
          simp [ih, List.map_map, Function.comp]

/--
  The zipped enumeration of `finRange` together with any Boolean list contains
  each variable exactly once.  The lemma produces the concrete member for the
  index `i`, conveniently expressed in terms of `bitVecOfList`.
-/
lemma mem_zip_finRange_bitVec
    (bits : List Bool) (hlen : bits.length = n) (i : Fin n) :
    (i, bitVecOfList (n := n) bits hlen i)
      ∈ List.zip (List.finRange n) bits := by
  classical
  revert bits hlen i
  induction n with
  | zero =>
      intro bits hlen i
      exact Fin.elim0 i
  | succ n ih =>
      intro bits hlen i
      cases bits with
      | nil =>
          cases hlen
      | cons b tail =>
          have hbLen : (b :: tail).length = Nat.succ n := by
            simpa [List.length_cons] using hlen
          have hlenTail : tail.length = n := by
            simpa using Nat.succ.inj hbLen
          refine Fin.cases ?case0 ?casesucc i
          · have hb := bitVecOfList_cons_head (n := n) (bits := tail) (b := b)
              (hlen := hbLen)
            simp [List.finRange_succ, List.zip_cons_cons, hb]
          · intro j
            have hmem := ih tail hlenTail j
            have hbit := bitVecOfList_cons_succ (n := n) (bits := tail)
              (b := b) (i := j)
              (hlen := hbLen)
            have hmap : (Fin.succ j, bitVecOfList tail hlenTail j)
                ∈ (List.zip (List.finRange n) tail).map
                    (fun v : Fin n × Bool => (Fin.succ v.1, v.2)) := by
              exact List.mem_map.mpr ⟨⟨j, bitVecOfList tail hlenTail j⟩,
                hmem, rfl⟩
            have hrewrite := zip_map_left_eq_map_zip (α := Fin n) (β := Bool)
              (γ := Fin (Nat.succ n)) (f := Fin.succ)
              (xs := List.finRange n) (ys := tail)
            simpa [List.finRange_succ, List.zip_cons_cons, hrewrite, hbit]
              using hmap

/--
  The membership criterion from the previous lemma immediately forces equality
  with the `BitVec` reconstructed from the Boolean list.  This is the key step
  in identifying canonical trunk leaves with point subcubes.
-/
lemma bitVec_eq_of_zip_condition
    (bits : List Bool) (hlen : bits.length = n)
    {x : BitVec n}
    (hzip : ∀ u ∈ List.zip (List.finRange n) bits, x u.1 = u.2) :
    x = bitVecOfList (n := n) bits hlen := by
  funext i
  have hmem := mem_zip_finRange_bitVec (n := n) (bits := bits)
    (hlen := hlen) i
  have hx := hzip (i, bitVecOfList (n := n) bits hlen i) hmem
  simpa using hx

/--
  Conversely, if a vector is reconstructed via `bitVecOfList`, then it satisfies
  the compatibility conditions with the zipped enumeration of variables and
  Boolean values.
-/
lemma zip_condition_bitVecOfList
    {n : Nat} {bits : List Bool} (hlen : bits.length = n) :
    ∀ u ∈ List.zip (List.finRange n) bits,
      bitVecOfList (n := n) bits hlen u.1 = u.2 := by
  revert n
  induction bits with
  | nil =>
      intro n hlen u hu
      have : List.zip (List.finRange n) ([] : List Bool) = [] := by
        simp [List.zip, hlen]
      simpa [this] using hu
  | cons b tail ih =>
      intro n hlen u hu
      have hsucc : tail.length.succ = n := by
        simpa [List.length_cons] using hlen
      subst hsucc
      have hzip :
          List.zip (List.finRange (tail.length.succ)) (b :: tail)
            = (0, b)
                :: (List.zip (List.finRange tail.length) tail).map
                    (fun v => (Fin.succ v.1, v.2)) := by
        have := zip_map_left_eq_map_zip (α := Fin tail.length) (β := Bool)
          (γ := Fin tail.length.succ) (f := Fin.succ)
            (xs := List.finRange tail.length) (ys := tail)
        simp [List.finRange_succ, List.zip_cons_cons, this]
      have hcases : u = (0, b)
          ∨ u ∈ (List.zip (List.finRange tail.length) tail).map
              (fun v => (Fin.succ v.1, v.2)) := by
        simpa [hzip] using hu
      cases hcases with
      | inl hfirst =>
          cases hfirst
          have hbLen : (b :: tail).length = tail.length.succ := by
            simp [List.length_cons]
          have hb := bitVecOfList_cons_head (n := tail.length) (bits := tail) (b := b)
            (hlen := hbLen)
          simp [List.finRange_succ, List.zip_cons_cons, hb]
      | inr hrest =>
          obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hrest
          have htail := ih (n := tail.length) (hlen := by rfl) v hv
          have hbLen : (b :: tail).length = tail.length.succ := by
            simp [List.length_cons]
          have hbit := bitVecOfList_cons_succ (n := tail.length) (bits := tail)
            (b := b) (i := v.1) (hlen := hbLen)
          simpa [hbit] using htail

lemma zip_condition_of_bitVec
    (bits : List Bool) (hlen : bits.length = n)
    {x : BitVec n}
    (hx : x = bitVecOfList (n := n) bits hlen) :
    ∀ u ∈ List.zip (List.finRange n) bits, x u.1 = u.2 := by
  intro u hu
  subst hx
  exact zip_condition_bitVecOfList (n := n) (bits := bits) hlen u hu

/--
  Membership in the subcube generated by `extendSubcubeWithBits` along
  `finRange` is equivalent to being exactly the bit vector reconstructed from the
  Boolean choices.  This is the principal interface used when selecting leaves
  for the perfect certificate.
-/
lemma mem_extendSubcubeWithBits_finRange_iff
    (bits : List Bool) (hlen : bits.length = n)
    (x : BitVec n) :
    mem (extendSubcubeWithBits (n := n)
      (canonicalBase n) (List.finRange n) bits) x
      ↔ x = bitVecOfList (n := n) bits hlen := by
  classical
  have hassign := assignMany_canonicalBase_eq_extend (n := n)
    (vars := List.finRange n) (bits := bits)
    (hnd := List.nodup_finRange n)
    (hlen := by simpa [List.length_finRange] using hlen)
  have hmem := mem_assignMany_iff (n := n)
    (β := canonicalBase n) (γ := extendSubcubeWithBits (n := n)
      (canonicalBase n) (List.finRange n) bits)
    (updates := List.zip (List.finRange n) bits) hassign x
  constructor
  · intro hx
    have hx' := (hmem.mp hx).2
    exact bitVec_eq_of_zip_condition (n := n) (bits := bits) (hlen := hlen) hx'
  · intro hx
    have hx' := zip_condition_of_bitVec (n := n) (bits := bits)
      (hlen := hlen) (x := x) hx
    have hbase : mem (canonicalBase n) x := by
      simp [mem, memB, canonicalBase]
    exact (hmem.mpr ⟨hbase, hx'⟩)

end Core
end Pnp3
