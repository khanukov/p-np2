import UniformClassBridgeClosure.TM0Iteration

namespace UniformClassBridgeClosure.TM0DAG.Window
open Turing Pnp3.ComplexityInterfaces Pnp3.ComplexityInterfaces.DagCircuit

/-- Literal raw initialization, with the unchanged six-symbol input encoding. -/
def inputConfig {Λ : Type} [Inhabited Λ] {N : Nat} (y : Bitstring N) : TM0.Cfg Symbol Λ :=
  TM0.init ((List.ofFn y).map (fun b => (false,some b)))

private def symbolAt {N : Nat} (y : Bitstring N) (z : Int) : Symbol :=
  if h : 0 ≤ z ∧ z.toNat < N then (false,some (y ⟨z.toNat,h.2⟩)) else (false,none)

private theorem input_nth {Λ : Type} [Inhabited Λ] {N : Nat} (y : Bitstring N) (z : Int) :
    (inputConfig (Λ:=Λ) y).Tape.nth z = symbolAt y z := by
  cases z with
  | ofNat n =>
    change (Tape.mk₂ [] ((List.ofFn y).map (fun b => (false,some b)))).nth (n : Int) = _
    simp only [Tape.mk₂,Tape.mk'_nth_nat,ListBlank.nth_mk]
    by_cases h : n < N
    · simp [List.getI_eq_getElem, h, symbolAt]
    · rw [List.getI_eq_default _ (by simpa using Nat.le_of_not_gt h)]
      change (false,none) = symbolAt y (n : Int)
      simp [symbolAt,h]
  | negSucc n =>
    simp [inputConfig,TM0.init,Tape.mk₁,Tape.mk₂,Tape.nth,Tape.mk',symbolAt]
    rfl

private def atCircuit (N : Nat) (z : Int) (f : Symbol → Bool) : DagCircuit N :=
  if h : 0 ≤ z ∧ z.toNat < N then
    substInputs muxCircuit ![inputProj ⟨z.toNat,h.2⟩,
      constCircuit N (f (false,some true)),constCircuit N (f (false,some false))]
  else constCircuit N (f (false,none))

private theorem at_correct {N : Nat} (z : Int) (f : Symbol → Bool) (y : Bitstring N) :
    DagCircuit.eval (atCircuit N z f) y = f (symbolAt y z) := by
  unfold atCircuit symbolAt
  split_ifs with h
  · simp only [eval_substInputs,eval_muxCircuit]
    cases e : y ⟨z.toNat,h.2⟩ <;> simp [e]
  · exact eval_constCircuit _ _

private theorem at_gates (N : Nat) (z : Int) (f : Symbol → Bool) :
    (atCircuit N z f).gates ≤ 6 := by
  unfold atCircuit
  split_ifs with h
  · change (bundleOfFamily 3 ![inputProj ⟨z.toNat,h.2⟩,
        constCircuit N (f (false,some true)),constCircuit N (f (false,some false))]).gates + 4 ≤ 6
    rw [bundleOfFamily_gates]
    simp [Fin.sum_univ_succ,inputProj,constCircuit]
  · exact (by decide : 1 ≤ 6)

/-- Every tag and tape rail depends on at most one raw input bit and constants. -/
def inputBundle {Λ : Type} [Inhabited Λ] [DecidableEq Λ]
    (labels : List Λ) (N r : Nat) : DagBundle N (width labels r) :=
  bundleOfFamily (width labels r)
    (Fin.addCases
      (fun j => atCircuit N 0 (fun a => decide ((centers labels)[j] = (false,default,a))))
      (fun j => let p := finProdFinEquiv.symm j
                atCircuit N (coord r p.1) (fun a => decide (symbols[p.2] = a))))

theorem input_correct {Λ : Type} [Inhabited Λ] [DecidableEq Λ]
    (labels : List Λ) (N r : Nat) (y : Bitstring N) :
    (inputBundle labels N r).evalFun y = encodeWindow labels r (false,inputConfig y) := by
  funext o
  induction o using Fin.addCases with
  | left j =>
    simp only [inputBundle,DagBundle.evalFun,evalOutput_bundleOfFamily,Fin.addCases_left]
    rw [at_correct]
    simp [encodeWindow,center,← input_nth (Λ:=Λ) y 0,inputConfig,TM0.init]
  | right j =>
    simp only [inputBundle,DagBundle.evalFun,evalOutput_bundleOfFamily,Fin.addCases_right]
    rw [at_correct]
    simp [encodeWindow,input_nth]

theorem input_gates {Λ : Type} [Inhabited Λ] [DecidableEq Λ]
    (labels : List Λ) (N r : Nat) : (inputBundle labels N r).gates ≤ 6*width labels r := by
  rw [inputBundle,bundleOfFamily_gates]
  calc
    _ ≤ ∑ _i : Fin (width labels r), 6 := by
      apply Finset.sum_le_sum
      intro i _
      induction i using Fin.addCases <;> simp only [Fin.addCases_left,Fin.addCases_right] <;> apply at_gates
    _ = _ := by simp [Nat.mul_comm]

-- SG4_LITERAL_AUDIT: mechanical checks, not independent mathematical reproof.
theorem check_input_correct {Λ : Type} [Inhabited Λ] [DecidableEq Λ]
    (labels : List Λ) (N r : Nat) (y : Bitstring N) :
    (inputBundle labels N r).evalFun y = encodeWindow labels r (false,inputConfig y) :=
  input_correct labels N r y

theorem check_input_gates {Λ : Type} [Inhabited Λ] [DecidableEq Λ]
    (labels : List Λ) (N r : Nat) :
    (inputBundle labels N r).gates ≤ 6*width labels r :=
  input_gates labels N r

#check (@inputConfig : ∀ {_Λ : Type} [Inhabited _Λ] {_N : Nat} (_y : Bitstring _N),
    TM0.Cfg Symbol _Λ)
#check (@symbolAt : ∀ {_N : Nat} (_y : Bitstring _N) (_z : Int),
    Symbol)
#check (@input_nth : ∀ {_Λ : Type} [Inhabited _Λ] {_N : Nat} (_y : Bitstring _N) (_z : Int),
    (inputConfig (Λ:=_Λ) _y).Tape.nth _z = symbolAt _y _z)
#check (@atCircuit : ∀ (_N : Nat) (_z : Int) (_f : Symbol → Bool),
    DagCircuit _N)
#check (@at_correct : ∀ {_N : Nat} (_z : Int) (_f : Symbol → Bool) (_y : Bitstring _N),
    DagCircuit.eval (atCircuit _N _z _f) _y = _f (symbolAt _y _z))
#check (@at_gates : ∀ (_N : Nat) (_z : Int) (_f : Symbol → Bool),
    (atCircuit _N _z _f).gates ≤ 6)
#check (@inputBundle : ∀ {_Λ : Type} [Inhabited _Λ] [DecidableEq _Λ]
    (_labels : List _Λ) (_N _r : Nat),
    DagBundle _N (width _labels _r))
#check (@input_correct : ∀ {_Λ : Type} [Inhabited _Λ] [DecidableEq _Λ]
    (_labels : List _Λ) (_N _r : Nat) (_y : Bitstring _N),
    (inputBundle _labels _N _r).evalFun _y = encodeWindow _labels _r (false,inputConfig _y))
#check (@input_gates : ∀ {_Λ : Type} [Inhabited _Λ] [DecidableEq _Λ]
    (_labels : List _Λ) (_N _r : Nat),
    (inputBundle _labels _N _r).gates ≤ 6*width _labels _r)
#check (@check_input_correct : ∀ {_Λ : Type} [Inhabited _Λ] [DecidableEq _Λ]
    (_labels : List _Λ) (_N _r : Nat) (_y : Bitstring _N),
    (inputBundle _labels _N _r).evalFun _y = encodeWindow _labels _r (false,inputConfig _y))
#check (@check_input_gates : ∀ {_Λ : Type} [Inhabited _Λ] [DecidableEq _Λ]
    (_labels : List _Λ) (_N _r : Nat),
    (inputBundle _labels _N _r).gates ≤ 6*width _labels _r)
#print axioms inputConfig
#print axioms symbolAt
#print axioms input_nth
#print axioms atCircuit
#print axioms at_correct
#print axioms at_gates
#print axioms inputBundle
#print axioms input_correct
#print axioms input_gates
#print axioms check_input_correct
#print axioms check_input_gates

end UniformClassBridgeClosure.TM0DAG.Window
