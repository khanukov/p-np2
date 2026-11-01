import UniformClassBridgeClosure.TM0WindowBundle

namespace UniformClassBridgeClosure.TM0DAG.Window
open Turing Pnp3.ComplexityInterfaces Pnp3.ComplexityInterfaces.DagCircuit

/-- Shared composition, shrinking one cell of radius at each actual TM0 step. -/
def runWindow {Λ : Type} [Inhabited Λ] [DecidableEq Λ]
    (labels : List Λ) (T : TM0.Machine Symbol Λ) (r : Nat) :
    (n : Nat) → DagBundle (width labels (r+n)) (width labels r)
  | 0 => identityBundle (width labels r)
  | n+1 => substBundle (runWindow labels T r n) (windowBundle labels T (r+n))

private theorem compose_eval {a b c : Nat} (S : DagBundle b c) (B : DagBundle a b)
    (x : Bitstring a) : (substBundle S B).evalFun x = S.evalFun (B.evalFun x) := by
  funext o;exact evalOutput_substBundle S B o x

theorem run_correct {Λ : Type} [Inhabited Λ] [DecidableEq Λ]
    (labels : List Λ) (complete : ∀ q, q ∈ labels) (T : TM0.Machine Symbol Λ)
    (r n : Nat) (s : Bool × TM0.Cfg Symbol Λ) :
    (runWindow labels T r n).evalFun (encodeWindow labels (r+n) s) =
      encodeWindow labels r (saturatedRun T n s) := by
  induction n generalizing s with
  | zero => exact evalFun_identityBundle _ _
  | succ n ih =>
    change (substBundle (runWindow labels T r n) (windowBundle labels T (r+n))).evalFun _ = _
    rw [compose_eval]
    change (runWindow labels T r n).evalFun
      ((windowBundle labels T (r+n)).evalFun (encodeWindow labels ((r+n)+1) s)) = _
    rw [window_correct labels complete T (r+n) s,ih]
    rfl

theorem run_gates {Λ : Type} [Inhabited Λ] [DecidableEq Λ]
    (labels : List Λ) (T : TM0.Machine Symbol Λ) (r n : Nat) :
    (runWindow labels T r n).gates =
      ∑ i ∈ Finset.range n, width labels (r+i)*(1+144*labels.length) := by
  induction n with
  | zero => simp [runWindow,identityBundle]
  | succ n ih =>
    simp only [runWindow,substBundle_gates,window_gates,ih,Finset.sum_range_succ]
    omega

theorem run_gates_le {Λ : Type} [Inhabited Λ] [DecidableEq Λ]
    (labels : List Λ) (T : TM0.Machine Symbol Λ) (r n : Nat) :
    (runWindow labels T r n).gates ≤
      n*(12*labels.length+6*(2*(r+n)+1))*(1+144*labels.length) := by
  rw [run_gates]
  calc
    _ ≤ ∑ _i ∈ Finset.range n, width labels (r+n)*(1+144*labels.length) := by
      apply Finset.sum_le_sum
      intro i hi
      apply Nat.mul_le_mul_right
      have h := Finset.mem_range.mp hi
      simp only [width_formula];omega
    _ = _ := by simp [width_formula,Nat.mul_assoc]
/-- Real halting detection, including a halt occurring exactly at the clock. -/
theorem saturated_add {Λ : Type} [Inhabited Λ] (T : TM0.Machine Symbol Λ)
    (a b : Nat) (s : Bool × TM0.Cfg Symbol Λ) :
    saturatedRun T (a+b) s = saturatedRun T b (saturatedRun T a s) := by
  induction a generalizing s with
  | zero => simp only [Nat.zero_add,saturatedRun]
  | succ a ih => simpa only [Nat.succ_add,saturatedRun] using ih (saturatedStep T s)

theorem run_after_halt {Λ : Type} [Inhabited Λ] [DecidableEq Λ]
    (labels : List Λ) (complete : ∀ q, q ∈ labels) (T : TM0.Machine Symbol Λ)
    (r t extra : Nat) (s last : TM0.Cfg Symbol Λ)
    (h : rawTrace T t s = some last) (stop : TM0.step T last = none) :
    (runWindow labels T r (t+1+extra)).evalFun
      (encodeWindow labels (r+(t+1+extra)) (false,s)) = encodeWindow labels r (true,last) := by
  rw [run_correct labels complete,saturated_add,halted_after T t s last h stop,saturatedRun_true]

theorem clock_halt {Λ : Type} [Inhabited Λ] [DecidableEq Λ]
    (labels : List Λ) (complete : ∀ q, q ∈ labels) (T : TM0.Machine Symbol Λ)
    (r B t : Nat) (s last : TM0.Cfg Symbol Λ) (le : t ≤ B)
    (h : rawTrace T t s = some last) (stop : TM0.step T last = none) :
    (runWindow labels T r (B+1)).evalFun
      (encodeWindow labels (r+(B+1)) (false,s)) = encodeWindow labels r (true,last) := by
  have e : t+1+(B-t) = B+1 := by omega
  exact e ▸ run_after_halt labels complete T r t (B-t) s last h stop

-- SG3_LITERAL_AUDIT: mechanical checks, not independent mathematical reproof.
theorem check_run_correct {Λ : Type} [Inhabited Λ] [DecidableEq Λ]
    (labels : List Λ) (complete : ∀ q, q ∈ labels) (T : TM0.Machine Symbol Λ)
    (r n : Nat) (s : Bool × TM0.Cfg Symbol Λ) :
    (runWindow labels T r n).evalFun (encodeWindow labels (r+n) s) =
      encodeWindow labels r (saturatedRun T n s) :=
  run_correct labels complete T r n s

theorem check_run_gates {Λ : Type} [Inhabited Λ] [DecidableEq Λ]
    (labels : List Λ) (T : TM0.Machine Symbol Λ) (r n : Nat) :
    (runWindow labels T r n).gates =
      ∑ i ∈ Finset.range n, width labels (r+i)*(1+144*labels.length) :=
  run_gates labels T r n

theorem check_run_gates_le {Λ : Type} [Inhabited Λ] [DecidableEq Λ]
    (labels : List Λ) (T : TM0.Machine Symbol Λ) (r n : Nat) :
    (runWindow labels T r n).gates ≤
      n*(12*labels.length+6*(2*(r+n)+1))*(1+144*labels.length) :=
  run_gates_le labels T r n

theorem check_saturated_add {Λ : Type} [Inhabited Λ] (T : TM0.Machine Symbol Λ)
    (a b : Nat) (s : Bool × TM0.Cfg Symbol Λ) :
    saturatedRun T (a+b) s = saturatedRun T b (saturatedRun T a s) :=
  saturated_add T a b s

theorem check_run_after_halt {Λ : Type} [Inhabited Λ] [DecidableEq Λ]
    (labels : List Λ) (complete : ∀ q, q ∈ labels) (T : TM0.Machine Symbol Λ)
    (r t extra : Nat) (s last : TM0.Cfg Symbol Λ)
    (h : rawTrace T t s = some last) (stop : TM0.step T last = none) :
    (runWindow labels T r (t+1+extra)).evalFun
      (encodeWindow labels (r+(t+1+extra)) (false,s)) = encodeWindow labels r (true,last) :=
  run_after_halt labels complete T r t extra s last h stop

theorem check_clock_halt {Λ : Type} [Inhabited Λ] [DecidableEq Λ]
    (labels : List Λ) (complete : ∀ q, q ∈ labels) (T : TM0.Machine Symbol Λ)
    (r B t : Nat) (s last : TM0.Cfg Symbol Λ) (le : t ≤ B)
    (h : rawTrace T t s = some last) (stop : TM0.step T last = none) :
    (runWindow labels T r (B+1)).evalFun
      (encodeWindow labels (r+(B+1)) (false,s)) = encodeWindow labels r (true,last) :=
  clock_halt labels complete T r B t s last le h stop

#check (@runWindow : ∀ {_Λ : Type} [Inhabited _Λ] [DecidableEq _Λ]
    (_labels : List _Λ) (_T : TM0.Machine Symbol _Λ) (_r : Nat),
    (n : Nat) → DagBundle (width _labels (_r+n)) (width _labels _r))
#check (@compose_eval : ∀ {_a _b _c : Nat} (_S : DagBundle _b _c) (_B : DagBundle _a _b)
    (_x : Bitstring _a),
    (substBundle _S _B).evalFun _x = _S.evalFun (_B.evalFun _x))
#check (@run_correct : ∀ {_Λ : Type} [Inhabited _Λ] [DecidableEq _Λ]
    (_labels : List _Λ) (_complete : ∀ q, q ∈ _labels) (_T : TM0.Machine Symbol _Λ)
    (_r _n : Nat) (_s : Bool × TM0.Cfg Symbol _Λ),
    (runWindow _labels _T _r _n).evalFun (encodeWindow _labels (_r+_n) _s) =
      encodeWindow _labels _r (saturatedRun _T _n _s))
#check (@run_gates : ∀ {_Λ : Type} [Inhabited _Λ] [DecidableEq _Λ]
    (_labels : List _Λ) (_T : TM0.Machine Symbol _Λ) (_r _n : Nat),
    (runWindow _labels _T _r _n).gates =
      ∑ i ∈ Finset.range _n, width _labels (_r+i)*(1+144*_labels.length))
#check (@run_gates_le : ∀ {_Λ : Type} [Inhabited _Λ] [DecidableEq _Λ]
    (_labels : List _Λ) (_T : TM0.Machine Symbol _Λ) (_r _n : Nat),
    (runWindow _labels _T _r _n).gates ≤
      _n*(12*_labels.length+6*(2*(_r+_n)+1))*(1+144*_labels.length))
#check (@saturated_add : ∀ {_Λ : Type} [Inhabited _Λ] (_T : TM0.Machine Symbol _Λ)
    (_a _b : Nat) (_s : Bool × TM0.Cfg Symbol _Λ),
    saturatedRun _T (_a+_b) _s = saturatedRun _T _b (saturatedRun _T _a _s))
#check (@run_after_halt : ∀ {_Λ : Type} [Inhabited _Λ] [DecidableEq _Λ]
    (_labels : List _Λ) (_complete : ∀ q, q ∈ _labels) (_T : TM0.Machine Symbol _Λ)
    (_r _t _extra : Nat) (_s _last : TM0.Cfg Symbol _Λ)
    (_h : rawTrace _T _t _s = some _last) (_stop : TM0.step _T _last = none),
    (runWindow _labels _T _r (_t+1+_extra)).evalFun
      (encodeWindow _labels (_r+(_t+1+_extra)) (false,_s)) = encodeWindow _labels _r (true,_last))
#check (@clock_halt : ∀ {_Λ : Type} [Inhabited _Λ] [DecidableEq _Λ]
    (_labels : List _Λ) (_complete : ∀ q, q ∈ _labels) (_T : TM0.Machine Symbol _Λ)
    (_r _B _t : Nat) (_s _last : TM0.Cfg Symbol _Λ) (_le : _t ≤ _B)
    (_h : rawTrace _T _t _s = some _last) (_stop : TM0.step _T _last = none),
    (runWindow _labels _T _r (_B+1)).evalFun
      (encodeWindow _labels (_r+(_B+1)) (false,_s)) = encodeWindow _labels _r (true,_last))
#check (@check_run_correct : ∀ {_Λ : Type} [Inhabited _Λ] [DecidableEq _Λ]
    (_labels : List _Λ) (_complete : ∀ q, q ∈ _labels) (_T : TM0.Machine Symbol _Λ)
    (_r _n : Nat) (_s : Bool × TM0.Cfg Symbol _Λ),
    (runWindow _labels _T _r _n).evalFun (encodeWindow _labels (_r+_n) _s) =
      encodeWindow _labels _r (saturatedRun _T _n _s))
#check (@check_run_gates : ∀ {_Λ : Type} [Inhabited _Λ] [DecidableEq _Λ]
    (_labels : List _Λ) (_T : TM0.Machine Symbol _Λ) (_r _n : Nat),
    (runWindow _labels _T _r _n).gates =
      ∑ i ∈ Finset.range _n, width _labels (_r+i)*(1+144*_labels.length))
#check (@check_run_gates_le : ∀ {_Λ : Type} [Inhabited _Λ] [DecidableEq _Λ]
    (_labels : List _Λ) (_T : TM0.Machine Symbol _Λ) (_r _n : Nat),
    (runWindow _labels _T _r _n).gates ≤
      _n*(12*_labels.length+6*(2*(_r+_n)+1))*(1+144*_labels.length))
#check (@check_saturated_add : ∀ {_Λ : Type} [Inhabited _Λ] (_T : TM0.Machine Symbol _Λ)
    (_a _b : Nat) (_s : Bool × TM0.Cfg Symbol _Λ),
    saturatedRun _T (_a+_b) _s = saturatedRun _T _b (saturatedRun _T _a _s))
#check (@check_run_after_halt : ∀ {_Λ : Type} [Inhabited _Λ] [DecidableEq _Λ]
    (_labels : List _Λ) (_complete : ∀ q, q ∈ _labels) (_T : TM0.Machine Symbol _Λ)
    (_r _t _extra : Nat) (_s _last : TM0.Cfg Symbol _Λ)
    (_h : rawTrace _T _t _s = some _last) (_stop : TM0.step _T _last = none),
    (runWindow _labels _T _r (_t+1+_extra)).evalFun
      (encodeWindow _labels (_r+(_t+1+_extra)) (false,_s)) = encodeWindow _labels _r (true,_last))
#check (@check_clock_halt : ∀ {_Λ : Type} [Inhabited _Λ] [DecidableEq _Λ]
    (_labels : List _Λ) (_complete : ∀ q, q ∈ _labels) (_T : TM0.Machine Symbol _Λ)
    (_r _B _t : Nat) (_s _last : TM0.Cfg Symbol _Λ) (_le : _t ≤ _B)
    (_h : rawTrace _T _t _s = some _last) (_stop : TM0.step _T _last = none),
    (runWindow _labels _T _r (_B+1)).evalFun
      (encodeWindow _labels (_r+(_B+1)) (false,_s)) = encodeWindow _labels _r (true,_last))
#print axioms runWindow
#print axioms compose_eval
#print axioms run_correct
#print axioms run_gates
#print axioms run_gates_le
#print axioms saturated_add
#print axioms run_after_halt
#print axioms clock_halt
#print axioms check_run_correct
#print axioms check_run_gates
#print axioms check_run_gates_le
#print axioms check_saturated_add
#print axioms check_run_after_halt
#print axioms check_clock_halt

end UniformClassBridgeClosure.TM0DAG.Window
