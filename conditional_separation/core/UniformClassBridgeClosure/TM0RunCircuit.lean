import UniformClassBridgeClosure.TM0RawInput

namespace UniformClassBridgeClosure.TM0DAG.Window
open Turing Pnp3.ComplexityInterfaces Pnp3.ComplexityInterfaces.DagCircuit

private theorem centers_full {Λ : Type} (labels : List Λ) (complete : ∀ q, q ∈ labels)
    (a : Center Λ) : a ∈ centers labels := by
  have hs (x : Symbol) : x ∈ symbols := by
    rcases x with ⟨b,o⟩
    cases b <;> cases o with
    | none => decide
    | some c => cases c <;> decide
  rcases a with ⟨h,q,x⟩
  cases h <;> simp [centers,complete,hs]

private def readAccepted {Λ : Type} [DecidableEq Λ] (labels : List Λ) (accept : Λ) :
    DagCircuit (width labels 0) :=
  bigOrCircuit ((List.finRange (centers labels).length).map fun i =>
    if (centers labels)[i].1 = true ∧ (centers labels)[i].2.1 = accept
    then inputProj (tagWire labels 0 i) else constCircuit _ false)

private theorem read_correct {Λ : Type} [DecidableEq Λ] (labels : List Λ)
    (complete : ∀ q, q ∈ labels) (accept : Λ) (s : Bool × TM0.Cfg Symbol Λ) :
    DagCircuit.eval (readAccepted labels accept) (encodeWindow labels 0 s) =
      (s.1 && decide (s.2.q=accept)) := by
  apply Bool.eq_iff_iff.mpr
  simp only [readAccepted,eval_bigOrCircuit_map,List.any_eq_true,List.mem_finRange,
    true_and,Bool.and_eq_true,decide_eq_true_eq]
  constructor
  · rintro ⟨i,hi⟩
    split at hi
    · rw [eval_inputProj] at hi
      simp only [encodeWindow,tagWire,Fin.addCases_left] at hi
      have e := of_decide_eq_true hi
      rename_i cond
      simpa [e,center] using cond
    · simp at hi
  · intro hs
    obtain ⟨i,ei⟩ := List.get_of_mem (centers_full labels complete (center s))
    change (centers labels)[i.val] = center s at ei
    refine ⟨i,?_⟩
    simp [ei,center,hs,encodeWindow,tagWire]

private theorem product_length {α β : Type} (xs : List α) (ys : List β) :
    (xs.product ys).length = xs.length*ys.length := by
  change (xs ×ˢ ys).length = _
  exact List.length_product xs ys

private theorem read_gates {Λ : Type} [DecidableEq Λ] (labels : List Λ) (accept : Λ) :
    (readAccepted labels accept).gates ≤ 1+24*labels.length := by
  rw [readAccepted,bigOrCircuit_gates]
  simp only [List.map_map]
  have h : ∀ i : Fin (centers labels).length,
      ((if (centers labels)[i].1=true ∧ (centers labels)[i].2.1=accept
       then inputProj (tagWire labels 0 i) else constCircuit _ false).gates+1) ≤ 2 := by
    intro i; split_ifs <;> simp [inputProj,constCircuit]
  calc
    _ ≤ 1 + ((List.finRange (centers labels).length).map (fun _ => 2)).sum := by
      apply Nat.add_le_add_left
      exact List.sum_le_sum (fun i _ => h i)
    _ = _ := by simp [centers,symbols,product_length];omega

/-- Construction depends on the table, finite labels, control, clock and length only. -/
def rawCircuit {Λ : Type} [Inhabited Λ] [DecidableEq Λ]
    (labels : List Λ) (T : TM0.Machine Symbol Λ) (accept : Λ) (B N : Nat) : DagCircuit N :=
  substInputsWithBundle (readAccepted labels accept)
    (substBundle (runWindow labels T 0 (B+1)) (inputBundle labels N (0+(B+1))))

theorem raw_circuit_value {Λ : Type} [Inhabited Λ] [DecidableEq Λ]
    (labels : List Λ) (complete : ∀ q, q ∈ labels) (T : TM0.Machine Symbol Λ)
    (accept : Λ) (B N : Nat) (y : Bitstring N) :
    DagCircuit.eval (rawCircuit labels T accept B N) y =
      ((saturatedRun T (B+1) (false,inputConfig y)).1 &&
        decide ((saturatedRun T (B+1) (false,inputConfig y)).2.q=accept)) := by
  have h : (substBundle (runWindow labels T 0 (B+1)) (inputBundle labels N (0+(B+1)))).evalFun y =
      encodeWindow labels 0 (saturatedRun T (B+1) (false,inputConfig y)) := by
    funext o
    rw [DagBundle.evalFun_apply,evalOutput_substBundle]
    change (runWindow labels T 0 (B+1)).evalFun ((inputBundle labels N (0+(B+1))).evalFun y) o = _
    rw [input_correct]
    exact congrFun (run_correct labels complete T 0 (B+1) (false,inputConfig y)) o
  rw [rawCircuit,eval_substInputsWithBundle]
  change DagCircuit.eval (readAccepted labels accept)
    ((substBundle (runWindow labels T 0 (B+1)) (inputBundle labels N (0+(B+1)))).evalFun y) = _
  rw [h,read_correct labels complete]

theorem raw_circuit_correct {Λ : Type} [Inhabited Λ] [DecidableEq Λ]
    (labels : List Λ) (complete : ∀ q, q ∈ labels) (T : TM0.Machine Symbol Λ)
    (accept reject : Λ) (different : accept ≠ reject) (B N : Nat) (y : Bitstring N)
    (answer : Bool) (t : Nat) (last : TM0.Cfg Symbol Λ)
    (ht : t ≤ B) (trace : rawTrace T t (inputConfig y) = some last)
    (verdict : last.q = if answer then accept else reject) (stop : TM0.step T last = none) :
    DagCircuit.eval (rawCircuit labels T accept B N) y = answer := by
  rw [rawCircuit,eval_substInputsWithBundle]
  have init : (inputBundle labels N (0+(B+1))).evalFun y =
      encodeWindow labels (0+(B+1)) (false,inputConfig y) := input_correct labels N (0+(B+1)) y
  have run : (substBundle (runWindow labels T 0 (B+1)) (inputBundle labels N (0+(B+1)))).evalFun y =
      encodeWindow labels 0 (true,last) := by
    funext o
    rw [DagBundle.evalFun_apply,evalOutput_substBundle]
    change (runWindow labels T 0 (B+1)).evalFun ((inputBundle labels N (0+(B+1))).evalFun y) o = _
    rw [init]
    exact congrFun (clock_halt labels complete T 0 B t (inputConfig y) last ht trace stop) o
  change DagCircuit.eval (readAccepted labels accept)
    ((substBundle (runWindow labels T 0 (B+1)) (inputBundle labels N (0+(B+1)))).evalFun y) = _
  rw [run,read_correct labels complete]
  cases answer with
  | false => simp_all [Ne.symm different]
  | true => simp_all

theorem raw_circuit_size {Λ : Type} [Inhabited Λ] [DecidableEq Λ]
    (labels : List Λ) (T : TM0.Machine Symbol Λ) (accept : Λ) (B N : Nat) :
    (rawCircuit labels T accept B N).size ≤
      2+24*labels.length + (B+1)*(12*labels.length+6*(2*(B+1)+1))*(1+144*labels.length)
        + 6*(12*labels.length+6*(2*(B+1)+1)) := by
  have hi := input_gates labels N (0+(B+1))
  have hr := run_gates_le labels T 0 (B+1)
  have ho := read_gates labels accept
  simp only [Nat.zero_add] at hr
  simp only [Nat.zero_add,width_formula] at hi
  change (inputBundle labels N (0+(B+1))).gates + (runWindow labels T 0 (B+1)).gates +
    (readAccepted labels accept).gates + 1 ≤ _
  omega

-- SG4_LITERAL_AUDIT: mechanical checks, not independent mathematical reproof.
theorem check_raw_circuit_value {Λ : Type} [Inhabited Λ] [DecidableEq Λ]
    (labels : List Λ) (complete : ∀ q, q ∈ labels) (T : TM0.Machine Symbol Λ)
    (accept : Λ) (B N : Nat) (y : Bitstring N) :
    DagCircuit.eval (rawCircuit labels T accept B N) y =
      ((saturatedRun T (B+1) (false,inputConfig y)).1 &&
        decide ((saturatedRun T (B+1) (false,inputConfig y)).2.q=accept)) :=
  raw_circuit_value labels complete T accept B N y

theorem check_raw_circuit_correct {Λ : Type} [Inhabited Λ] [DecidableEq Λ]
    (labels : List Λ) (complete : ∀ q, q ∈ labels) (T : TM0.Machine Symbol Λ)
    (accept reject : Λ) (different : accept ≠ reject) (B N : Nat) (y : Bitstring N)
    (answer : Bool) (t : Nat) (last : TM0.Cfg Symbol Λ)
    (ht : t ≤ B) (trace : rawTrace T t (inputConfig y) = some last)
    (verdict : last.q = if answer then accept else reject) (stop : TM0.step T last = none) :
    DagCircuit.eval (rawCircuit labels T accept B N) y = answer :=
  raw_circuit_correct labels complete T accept reject different B N y answer t last ht trace verdict stop

theorem check_raw_circuit_size {Λ : Type} [Inhabited Λ] [DecidableEq Λ]
    (labels : List Λ) (T : TM0.Machine Symbol Λ) (accept : Λ) (B N : Nat) :
    (rawCircuit labels T accept B N).size ≤
      2+24*labels.length + (B+1)*(12*labels.length+6*(2*(B+1)+1))*(1+144*labels.length)
        + 6*(12*labels.length+6*(2*(B+1)+1)) :=
  raw_circuit_size labels T accept B N

#check (@centers_full : ∀ {_Λ : Type} (_labels : List _Λ) (_complete : ∀ q, q ∈ _labels)
    (_a : Center _Λ),
    _a ∈ centers _labels)
#check (@readAccepted : ∀ {_Λ : Type} [DecidableEq _Λ] (_labels : List _Λ) (_accept : _Λ),
    DagCircuit (width _labels 0))
#check (@read_correct : ∀ {_Λ : Type} [DecidableEq _Λ] (_labels : List _Λ)
    (_complete : ∀ q, q ∈ _labels) (_accept : _Λ) (_s : Bool × TM0.Cfg Symbol _Λ),
    DagCircuit.eval (readAccepted _labels _accept) (encodeWindow _labels 0 _s) =
      (_s.1 && decide (_s.2.q=_accept)))
#check (@product_length : ∀ {_α _β : Type} (_xs : List _α) (_ys : List _β),
    (_xs.product _ys).length = _xs.length*_ys.length)
#check (@read_gates : ∀ {_Λ : Type} [DecidableEq _Λ] (_labels : List _Λ) (_accept : _Λ),
    (readAccepted _labels _accept).gates ≤ 1+24*_labels.length)
#check (@rawCircuit : ∀ {_Λ : Type} [Inhabited _Λ] [DecidableEq _Λ]
    (_labels : List _Λ) (_T : TM0.Machine Symbol _Λ) (_accept : _Λ) (_B _N : Nat),
    DagCircuit _N)
#check (@raw_circuit_value : ∀ {_Λ : Type} [Inhabited _Λ] [DecidableEq _Λ]
    (_labels : List _Λ) (_complete : ∀ q, q ∈ _labels) (_T : TM0.Machine Symbol _Λ)
    (_accept : _Λ) (_B _N : Nat) (_y : Bitstring _N),
    DagCircuit.eval (rawCircuit _labels _T _accept _B _N) _y =
      ((saturatedRun _T (_B+1) (false,inputConfig _y)).1 &&
        decide ((saturatedRun _T (_B+1) (false,inputConfig _y)).2.q=_accept)))
#check (@raw_circuit_correct : ∀ {_Λ : Type} [Inhabited _Λ] [DecidableEq _Λ]
    (_labels : List _Λ) (_complete : ∀ q, q ∈ _labels) (_T : TM0.Machine Symbol _Λ)
    (_accept _reject : _Λ) (_different : _accept ≠ _reject) (_B _N : Nat) (_y : Bitstring _N)
    (_answer : Bool) (_t : Nat) (_last : TM0.Cfg Symbol _Λ)
    (_ht : _t ≤ _B) (_trace : rawTrace _T _t (inputConfig _y) = some _last)
    (_verdict : _last.q = if _answer then _accept else _reject) (_stop : TM0.step _T _last = none),
    DagCircuit.eval (rawCircuit _labels _T _accept _B _N) _y = _answer)
#check (@raw_circuit_size : ∀ {_Λ : Type} [Inhabited _Λ] [DecidableEq _Λ]
    (_labels : List _Λ) (_T : TM0.Machine Symbol _Λ) (_accept : _Λ) (_B _N : Nat),
    (rawCircuit _labels _T _accept _B _N).size ≤
      2+24*_labels.length + (_B+1)*(12*_labels.length+6*(2*(_B+1)+1))*(1+144*_labels.length)
        + 6*(12*_labels.length+6*(2*(_B+1)+1)))
#check (@check_raw_circuit_value : ∀ {_Λ : Type} [Inhabited _Λ] [DecidableEq _Λ]
    (_labels : List _Λ) (_complete : ∀ q, q ∈ _labels) (_T : TM0.Machine Symbol _Λ)
    (_accept : _Λ) (_B _N : Nat) (_y : Bitstring _N),
    DagCircuit.eval (rawCircuit _labels _T _accept _B _N) _y =
      ((saturatedRun _T (_B+1) (false,inputConfig _y)).1 &&
        decide ((saturatedRun _T (_B+1) (false,inputConfig _y)).2.q=_accept)))
#check (@check_raw_circuit_correct : ∀ {_Λ : Type} [Inhabited _Λ] [DecidableEq _Λ]
    (_labels : List _Λ) (_complete : ∀ q, q ∈ _labels) (_T : TM0.Machine Symbol _Λ)
    (_accept _reject : _Λ) (_different : _accept ≠ _reject) (_B _N : Nat) (_y : Bitstring _N)
    (_answer : Bool) (_t : Nat) (_last : TM0.Cfg Symbol _Λ)
    (_ht : _t ≤ _B) (_trace : rawTrace _T _t (inputConfig _y) = some _last)
    (_verdict : _last.q = if _answer then _accept else _reject) (_stop : TM0.step _T _last = none),
    DagCircuit.eval (rawCircuit _labels _T _accept _B _N) _y = _answer)
#check (@check_raw_circuit_size : ∀ {_Λ : Type} [Inhabited _Λ] [DecidableEq _Λ]
    (_labels : List _Λ) (_T : TM0.Machine Symbol _Λ) (_accept : _Λ) (_B _N : Nat),
    (rawCircuit _labels _T _accept _B _N).size ≤
      2+24*_labels.length + (_B+1)*(12*_labels.length+6*(2*(_B+1)+1))*(1+144*_labels.length)
        + 6*(12*_labels.length+6*(2*(_B+1)+1)))
#print axioms centers_full
#print axioms readAccepted
#print axioms read_correct
#print axioms product_length
#print axioms read_gates
#print axioms rawCircuit
#print axioms raw_circuit_value
#print axioms raw_circuit_correct
#print axioms raw_circuit_size
#print axioms check_raw_circuit_value
#print axioms check_raw_circuit_correct
#print axioms check_raw_circuit_size

end UniformClassBridgeClosure.TM0DAG.Window
