import Complexity.Uniform.V1.Examples
import Mathlib.Data.Set.Countable
import Mathlib.Data.Fintype.Option

/-!
# Countability and no length advice for Uniform P V1

The finite machine record is injected into an explicit dependent code after
erasing only its proof field.  This makes the versioned machine class, and
therefore its genuinely decided languages, countable.  A direct Boolean
diagonal then produces a length-only language outside versioned `UniformP`.
-/

namespace Pnp3.Complexity.Uniform.V1

/-- The three moves are countable via their distinct natural-number codes. -/
instance : Countable Move :=
  (show Function.Injective
      (fun m : Move => match m with
        | .left => (0 : Nat)
        | .stay => 1
        | .right => 2) from by
    intro a b h
    cases a <;> cases b <;> simp_all).countable

/-- Explicit proof-erasing code for a finite uniform machine.  The tuple order
is start state, accept state, reject state, then the raw transition table. -/
def UniformTM.data (M : UniformTM) :
    Σ k : Nat, Fin k × Fin k × Fin k ×
      (Fin k → Option Bool → Fin k × Option Bool × Move) :=
  ⟨M.stateCount, M.start, M.accept, M.reject, M.rawStep⟩

/-- The explicit machine code loses only a proposition-valued proof field, so
proof irrelevance makes it injective. -/
theorem UniformTM.data_injective : Function.Injective UniformTM.data := by
  intro M N h
  cases M with
  | mk mk ms ma mr mh mstep =>
      cases N with
      | mk nk ns na nr nh nstep =>
          simp only [UniformTM.data] at h
          cases h
          rfl

/-- Finite uniform machines form a countable type. -/
theorem uniformTM_countable : Countable UniformTM :=
  UniformTM.data_injective.countable

instance : Countable UniformTM := uniformTM_countable

private instance acceptsAtDecidable (M : UniformTM) {n budget steps : Nat}
    (x : Bitstring n) : Decidable (AcceptsAt M budget steps x) := by
  unfold AcceptsAt
  infer_instance

/-- The total language returned by the exact clock deadline.  A timeout maps
to false; only machines that genuinely decide are used below. -/
def machineLanguage (M : UniformTM) (c : Nat) : Language := fun n x =>
  decide (AcceptsAt M (polyClock c n) (polyClock c n) x)

/-- On either genuine exact verdict, the total deadline language returns that
verdict.  The false case uses literal rejection, not mere nonacceptance. -/
theorem machineLanguage_eq_of_decidesAt (M : UniformTM) (c : Nat)
    {n : Nat} (x : Bitstring n) (answer : Bool)
    (h : DecidesAt M (polyClock c n) (polyClock c n) x answer) :
    machineLanguage M c n x = answer := by
  cases answer with
  | false =>
      rw [machineLanguage, decide_eq_false_iff_not]
      intro ha
      have hr : RejectsAt M (polyClock c n) (polyClock c n) x := by
        simpa [DecidesAt] using h
      exact not_acceptsAt_and_rejectsAt M x ⟨ha, hr⟩
  | true =>
      rw [machineLanguage, decide_eq_true_eq]
      simpa [DecidesAt] using h

/-- Every versioned `UniformP` language is the total deadline language of one
machine and one exponent. -/
theorem uniformP_exists_machineLanguage (L : Language) (h : UniformP L) :
    ∃ M c, L = machineLanguage M c := by
  rcases (uniformP_iff_exists_decidesAt L).1 h with ⟨M, c, hM⟩
  refine ⟨M, c, ?_⟩
  funext n x
  exact (machineLanguage_eq_of_decidesAt M c x (L n x) (hM n x)).symm

/-- The set of languages in versioned `UniformP` is countable. -/
theorem uniformP_languages_countable :
    Set.Countable {L : Language | UniformP L} := by
  let enumerate : UniformTM × Nat → Language := fun p =>
    machineLanguage p.1 p.2
  apply (Set.countable_range enumerate).mono
  intro L hL
  rcases uniformP_exists_machineLanguage L hL with ⟨M, c, hEq⟩
  exact ⟨(M, c), hEq.symm⟩

/-- Embed a Boolean sequence as a language that ignores every input bit. -/
def lengthOnly (A : Nat → Bool) : Language := fun n _ => A n

/-- Length-only languages retain their defining sequence, including at length
zero, by evaluation on the canonical all-false input. -/
theorem lengthOnly_injective : Function.Injective lengthOnly := by
  intro A B h
  funext n
  have hn := congrFun (congrFun h n) (fun _ : Fin n => false)
  simpa [lengthOnly] using hn

/-- A direct Cantor diagonal against any countable set of languages. -/
theorem exists_lengthOnly_not_mem {S : Set Language} (hS : S.Countable) :
    ∃ A : Nat → Bool, lengthOnly A ∉ S := by
  rcases Set.countable_iff_exists_subset_range.1 hS with ⟨f, hf⟩
  let A : Nat → Bool := fun i => !(f i i (fun _ => false))
  refine ⟨A, ?_⟩
  intro hmem
  rcases hf hmem with ⟨i, hi⟩
  have hdiag : f i i (fun _ => false) = !(f i i (fun _ => false)) := by
    simpa [A, lengthOnly] using
      congrFun (congrFun hi i) (fun _ : Fin i => false)
  exact (Bool.eq_not_self _).1 hdiag

/-- Some length-only Boolean language is not in versioned `UniformP`. -/
theorem exists_lengthOnly_not_uniformP :
    ∃ A : Nat → Bool, ¬ UniformP (fun n _ => A n) := by
  rcases exists_lengthOnly_not_mem uniformP_languages_countable with ⟨A, hA⟩
  exact ⟨A, by simpa [lengthOnly] using hA⟩

/-- Equivalently, versioned `UniformP` cannot contain every length-only
Boolean language. -/
theorem not_forall_lengthOnly_uniformP :
    ¬ ∀ A : Nat → Bool, UniformP (fun n _ => A n) := by
  rintro h
  rcases exists_lengthOnly_not_uniformP with ⟨A, hA⟩
  exact hA (h A)

end Pnp3.Complexity.Uniform.V1
