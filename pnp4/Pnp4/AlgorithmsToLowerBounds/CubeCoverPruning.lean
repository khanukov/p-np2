import Pnp4.AlgorithmsToLowerBounds.SymmetricWitnessPruning

/-!
# Cube-cover pruning: poly-DNF and poly-CNF languages lie in `PpolyDAG`

Third structural ratchet on the input-1 witness space, strictly
generalizing the sparse/co-sparse pruning of `SparseWitnessPruning.lean`:

* `PpolyDAG_of_dnfBounded`: a language whose slices are unions of at most
  `n ^ c + c` subcubes (i.e. have polynomial DNF size) lies in `PpolyDAG`;
* `PpolyDAG_of_cnfBounded`: dually for intersections of clauses
  (polynomial CNF size), via the complement-closure law;
* `VerifiedNPDAGLowerBoundSource.not_dnfBounded` / `.not_cnfBounded`:
  any valid witness for `NP_not_subset_PpolyDAG` must have
  superpolynomial DNF *and* superpolynomial CNF complexity at infinitely
  many lengths.

Sparse languages are exactly the unions of *full* cubes (single points),
so this subsumes the earlier pruning; the excluded family is now the much
larger class of languages with any polynomial-size depth-2 representation.

A subcube is carried as a `List (Fin n × Bool)` of literals; its
indicator circuit is the conjunction of literal circuits, and a DNF is
the disjunction of cube indicators — all built from the verified
combinator layer with the same `5n + 4` per-term size budget as the
sparse construction, so the master schedule `n ^ (9c+13) + (9c+13)`
is reused verbatim.
-/

namespace Pnp4
namespace AlgorithmsToLowerBounds

open Pnp3.ComplexityInterfaces
open Pnp3.ComplexityInterfaces.DagCircuit

/-! ### Subcube indicators -/

/-- Boolean semantics of a literal list: all listed literals are satisfied. -/
def cubePred {n : Nat} (l : List (Fin n × Bool)) (x : Bitstring n) : Bool :=
  l.all (fun ib => x ib.1 == ib.2)

/-- The indicator circuit of a subcube. -/
def cubeCircuit {n : Nat} (l : List (Fin n × Bool)) : DagCircuit n :=
  andList (l.map (fun ib => literalCircuit ib.1 ib.2))

theorem eval_cubeCircuit {n : Nat} (l : List (Fin n × Bool)) (x : Bitstring n) :
    eval (cubeCircuit l) x = cubePred l x := by
  rw [cubeCircuit, eval_andList, List.all_map, cubePred]
  congr 1
  funext ib
  exact eval_literalCircuit ib.1 ib.2 x

theorem size_cubeCircuit_le {n : Nat} (l : List (Fin n × Bool))
    (hl : l.length ≤ n) :
    size (cubeCircuit l) ≤ 5 * n + 2 := by
  have hbound : ∀ ib ∈ l,
      ((fun C => size C + 2) ∘ fun ib : Fin n × Bool =>
        literalCircuit ib.1 ib.2) ib ≤ 5 := by
    intro ib _
    have := size_literalCircuit_le ib.1 ib.2
    simp only [Function.comp_apply]
    omega
  have hsum := sum_map_le_of_forall_le l
    ((fun C => size C + 2) ∘ fun ib : Fin n × Bool =>
      literalCircuit ib.1 ib.2) 5 hbound
  have h := size_andList_le (l.map (fun ib : Fin n × Bool =>
    literalCircuit ib.1 ib.2))
  rw [List.map_map] at h
  have hlen : l.length * 5 ≤ n * 5 := Nat.mul_le_mul_right 5 hl
  simp only [cubeCircuit]
  omega

/-! ### DNF- and CNF-bounded languages -/

/--
A language has polynomially bounded DNF complexity: every slice is a
union of at most `n ^ c + c` subcubes, each carried by at most `n`
literals.
-/
def DNFBounded (L : Language) : Prop :=
  ∃ c : Nat, ∀ n : Nat, ∃ LL : List (List (Fin n × Bool)),
    LL.length ≤ n ^ c + c ∧ (∀ l ∈ LL, l.length ≤ n) ∧
    ∀ x : Bitstring n, L n x = LL.any (fun l => cubePred l x)

/--
A language has polynomially bounded CNF complexity: its complement has
polynomially bounded DNF complexity (clauses dualize to cubes).
-/
def CNFBounded (L : Language) : Prop :=
  DNFBounded (complLanguage L)

/-- Sanity inclusion: polynomially sparse languages are DNF-bounded
(each accepted point is a full cube). -/
theorem dnfBounded_of_polySparse {L : Language} (h : PolySparse L) :
    DNFBounded L := by
  classical
  obtain ⟨c, hc⟩ := h
  refine ⟨c, fun n => ?_⟩
  refine ⟨(acceptedSet L n).toList.map
    (fun a => (List.finRange n).map (fun i => (i, a i))), ?_, ?_, ?_⟩
  · rw [List.length_map, Finset.length_toList]
    exact hc n
  · intro l hl
    rcases List.mem_map.mp hl with ⟨a, -, rfl⟩
    simp [List.length_finRange]
  · intro x
    rcases hx : L n x with _ | _
    · symm
      rw [List.any_eq_false]
      intro l hl hpred
      rcases List.mem_map.mp hl with ⟨a, ha, rfl⟩
      have hxa : x = a := by
        funext i
        have hall := List.all_eq_true.mp hpred (i, a i)
          (List.mem_map.mpr ⟨i, List.mem_finRange i, rfl⟩)
        exact eq_of_beq hall
      rw [Finset.mem_toList, mem_acceptedSet] at ha
      rw [← hxa, hx] at ha
      exact Bool.noConfusion ha
    · symm
      rw [List.any_eq_true]
      refine ⟨(List.finRange n).map (fun i => (i, x i)),
        List.mem_map.mpr ⟨x, ?_, rfl⟩, ?_⟩
      · rw [Finset.mem_toList, mem_acceptedSet]
        exact hx
      · rw [cubePred, List.all_eq_true]
        intro ib hib
        rcases List.mem_map.mp hib with ⟨i, -, rfl⟩
        simp

/-! ### Main theorems -/

/--
**DNF upper bound**: every language with polynomial DNF complexity lies
in `PpolyDAG`.
-/
theorem PpolyDAG_of_dnfBounded {L : Language} (h : DNFBounded L) :
    PpolyDAG L := by
  classical
  obtain ⟨c, hc⟩ := h
  choose LL hlen hwidth hcorrect using hc
  refine ⟨⟨fun n => n ^ (9 * c + 13) + (9 * c + 13),
          ⟨9 * c + 13, fun n => Nat.le_refl _⟩,
          fun n => orList ((LL n).map cubeCircuit), ?_, ?_⟩, trivial⟩
  · intro n
    show size (orList ((LL n).map cubeCircuit))
      ≤ n ^ (9 * c + 13) + (9 * c + 13)
    have hbound : ∀ C ∈ (LL n).map cubeCircuit,
        size C + 2 ≤ (5 * n + 2) + 2 := by
      intro C hC
      rcases List.mem_map.mp hC with ⟨l, hl, rfl⟩
      have := size_cubeCircuit_le l (hwidth n l hl)
      omega
    have hsum := sum_map_le_of_forall_le ((LL n).map cubeCircuit)
      (fun C => size C + 2) ((5 * n + 2) + 2) hbound
    have horl := size_orList_le ((LL n).map cubeCircuit)
    have hlen2 : ((LL n).map cubeCircuit).length ≤ n ^ c + c := by
      rw [List.length_map]
      exact hlen n
    have hmul : ((LL n).map cubeCircuit).length * ((5 * n + 2) + 2)
        ≤ (n ^ c + c) * (5 * n + 4) := by
      have := Nat.mul_le_mul_right ((5 * n + 2) + 2) hlen2
      omega
    have hmaster := master_poly_bound c n
    omega
  · intro n x
    show eval (orList ((LL n).map cubeCircuit)) x = L n x
    rw [eval_orList, List.any_map, hcorrect n x]
    congr 1
    funext l
    exact (eval_cubeCircuit l x : _)

/--
**CNF upper bound**: every language with polynomial CNF complexity lies
in `PpolyDAG`, via complement closure.
-/
theorem PpolyDAG_of_cnfBounded {L : Language} (h : CNFBounded L) :
    PpolyDAG L := by
  have h2 := PpolyDAG_of_dnfBounded h
  exact (PpolyDAG_compl_iff L).mp h2

/-! ### Route pruning corollaries -/

/-- Hard languages have superpolynomial DNF complexity. -/
theorem not_dnfBounded_of_not_PpolyDAG {L : Language}
    (h : ¬ PpolyDAG L) : ¬ DNFBounded L :=
  fun hd => h (PpolyDAG_of_dnfBounded hd)

/-- Hard languages have superpolynomial CNF complexity. -/
theorem not_cnfBounded_of_not_PpolyDAG {L : Language}
    (h : ¬ PpolyDAG L) : ¬ CNFBounded L :=
  fun hd => h (PpolyDAG_of_cnfBounded hd)

/-- Any valid source witness has superpolynomial DNF complexity. -/
theorem VerifiedNPDAGLowerBoundSource.not_dnfBounded
    (src : VerifiedNPDAGLowerBoundSource) : ¬ DNFBounded src.L :=
  not_dnfBounded_of_not_PpolyDAG src.notInPpolyDAG

/-- Any valid source witness has superpolynomial CNF complexity. -/
theorem VerifiedNPDAGLowerBoundSource.not_cnfBounded
    (src : VerifiedNPDAGLowerBoundSource) : ¬ CNFBounded src.L :=
  not_cnfBounded_of_not_PpolyDAG src.notInPpolyDAG

/-- The unconditional diagonal witness has superpolynomial DNF complexity. -/
theorem dagHardLanguage_not_dnfBounded : ¬ DNFBounded dagHardLanguage :=
  not_dnfBounded_of_not_PpolyDAG dagHardLanguage_not_PpolyDAG

/-- The unconditional diagonal witness has superpolynomial CNF complexity. -/
theorem dagHardLanguage_not_cnfBounded : ¬ CNFBounded dagHardLanguage :=
  not_cnfBounded_of_not_PpolyDAG dagHardLanguage_not_PpolyDAG

end AlgorithmsToLowerBounds
end Pnp4
