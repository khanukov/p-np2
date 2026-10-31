import UniformClassBridgeClosure.TM0Spatial

namespace UniformClassBridgeClosure.TM0DAG.Window
open Turing Pnp3.ComplexityInterfaces Pnp3.ComplexityInterfaces.DagCircuit

private def andAt {n : Nat} (i j : Fin n) : DagCircuit n where
  gates := 1
  gate := fun _ => .and (.input i) (.input j)
  output := .gate ⟨0, by omega⟩
private theorem eval_andAt {n : Nat} (i j : Fin n) (x : Bitstring n) :
    eval (andAt i j) x = (x i && x j) := by
  simp [andAt, DagCircuit.eval, DagCircuit.eval.evalGateAt]

private def row {A B C : Type} [DecidableEq C] {n : Nat}
    (as : List A) (bs : List B) (wa : Fin as.length → Fin n)
    (wb : Fin as.length → Fin bs.length → Fin n) (f : A → B → C) (c : C) :
    DagCircuit n :=
  bigOrCircuit ((List.finRange (as.length*bs.length)).map fun k =>
    let p := finProdFinEquiv.symm k
    if f as[p.1] bs[p.2] = c then andAt (wa p.1) (wb p.1 p.2)
    else constCircuit n false)

private theorem row_correct {A B C : Type} [DecidableEq A] [DecidableEq B]
    [DecidableEq C] {n : Nat} (as : List A) (bs : List B)
    (wa : Fin as.length → Fin n) (wb : Fin as.length → Fin bs.length → Fin n)
    (f : A → B → C) (c : C) (x : Bitstring n) (a : A) (v : A → B)
    (ha : a ∈ as) (hb : ∀ a, v a ∈ bs)
    (hta : ∀ i, x (wa i) = decide (as[i] = a))
    (htb : ∀ i j, x (wb i j) = decide (bs[j] = v as[i])) :
    eval (row as bs wa wb f c) x = decide (f a (v a) = c) := by
  obtain ⟨i, ei⟩ := List.get_of_mem ha
  obtain ⟨j, ej⟩ := List.get_of_mem (hb a)
  change as[i] = a at ei
  change bs[j] = v a at ej
  apply Bool.eq_iff_iff.mpr
  simp only [row, eval_bigOrCircuit_map, List.any_eq_true, List.mem_finRange,
    true_and, decide_eq_true_eq]
  constructor
  · rintro ⟨k,hk⟩
    split at hk
    · rw [eval_andAt, hta, htb] at hk
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hk
      rcases hk with ⟨e1,e2⟩
      simpa only [e1,e2] using ‹f as[(finProdFinEquiv.symm k).1] bs[(finProdFinEquiv.symm k).2] = c›
    · simp at hk
  · intro h
    refine ⟨finProdFinEquiv (i,j), ?_⟩
    simp only [Equiv.symm_apply_apply]
    have hc : f as[i] bs[j] = c := by simpa only [ei,ej] using h
    rw [if_pos hc, eval_andAt, hta, htb]
    simp [ei,ej]

private theorem row_gates {A B C : Type} [DecidableEq C] {n : Nat}
    (as : List A) (bs : List B) (wa : Fin as.length → Fin n)
    (wb : Fin as.length → Fin bs.length → Fin n) (f : A → B → C) (c : C) :
    (row as bs wa wb f c).gates = 1 + 2*(as.length*bs.length) := by
  rw [row, bigOrCircuit_gates, List.map_map]
  have aux : ∀ ks : List (Fin (as.length*bs.length)),
      (ks.map (fun k => ((if f as[(finProdFinEquiv.symm k).1]
        bs[(finProdFinEquiv.symm k).2] = c then
        andAt (wa (finProdFinEquiv.symm k).1)
          (wb (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2)
        else constCircuit n false).gates+1))).sum = 2*ks.length := by
    intro ks; induction ks with
    | nil => rfl
    | cons k ks ih =>
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      split <;> change 1+1+_ = _ <;> rw [ih] <;> omega
  simpa only [Function.comp_def, List.length_finRange] using
    congrArg (fun a => 1+a) (aux (List.finRange (as.length*bs.length)))

private theorem symbol_mem (a : Symbol) : a ∈ symbols := by
  rcases a with ⟨b,a⟩;cases b <;> cases a with
  | none => decide
  | some a => cases a <;> decide
private theorem tag_mem {Λ : Type} (labels : List Λ) (complete : ∀ q, q ∈ labels)
    (t : Center Λ) : t ∈ centers labels := by
  rcases t with ⟨h,q,a⟩
  cases h <;> simp [centers,complete,symbol_mem]
private theorem product_length {A B : Type} (as : List A) (bs : List B) :
    (as.product bs).length = as.length*bs.length := by
  change (as ×ˢ bs).length = _
  exact List.length_product as bs
private theorem centers_length {Λ : Type} (labels : List Λ) :
    (centers labels).length = 12*labels.length := by
  simp [centers, symbols, product_length];omega

def outputCircuit {Λ : Type} [Inhabited Λ] [DecidableEq Λ]
    (labels : List Λ) (T : TM0.Machine Symbol Λ) (r : Nat) :
    Fin (width labels r) → DagCircuit (width labels (r+1)) :=
  Fin.addCases
    (fun o => row (centers labels) symbols (tagWire labels (r+1))
      (fun t a => cellWire labels (r+1) (near r (direction T (centers labels)[t])) a)
      (nextTag T) (centers labels)[o])
    (fun o => let p := finProdFinEquiv.symm o
              row (centers labels) symbols (tagWire labels (r+1))
                (fun t a => cellWire labels (r+1) (slot r p.1 (direction T (centers labels)[t])) a)
                (nextCell T r p.1) symbols[p.2])

def windowBundle {Λ : Type} [Inhabited Λ] [DecidableEq Λ]
    (labels : List Λ) (T : TM0.Machine Symbol Λ) (r : Nat) :
    DagBundle (width labels (r+1)) (width labels r) :=
  bundleOfFamily _ (outputCircuit labels T r)

theorem window_correct {Λ : Type} [Inhabited Λ] [DecidableEq Λ]
    (labels : List Λ) (complete : ∀ q, q ∈ labels) (T : TM0.Machine Symbol Λ)
    (r : Nat) (s : Bool × TM0.Cfg Symbol Λ) :
    (windowBundle labels T r).evalFun (encodeWindow labels (r+1) s) =
      encodeWindow labels r (saturatedStep T s) := by
  funext o
  rw [DagBundle.evalFun_apply, windowBundle, evalOutput_bundleOfFamily]
  refine Fin.addCases ?_ ?_ o
  · intro j
    simp only [outputCircuit, Fin.addCases_left]
    rw [row_correct _ _ _ _ _ _ _ (center s)
      (fun t => s.2.Tape.nth (coord (r+1) (near r (direction T t))))
      (tag_mem labels complete _) (fun _ => symbol_mem _)]
    · simp only [tag_spec]
      simp [encodeWindow,eq_comm]
    · intro i; simp [encodeWindow,tagWire]
    · intro i a; simp only [encodeWindow,cellWire,Fin.addCases_right,Equiv.symm_apply_apply]
  · intro j
    simp only [outputCircuit, Fin.addCases_right]
    rw [row_correct _ _ _ _ _ _ _ (center s)
      (fun t => s.2.Tape.nth (coord (r+1)
        (slot r (finProdFinEquiv.symm j).1 (direction T t))))
      (tag_mem labels complete _) (fun _ => symbol_mem _)]
    · simp only [cell_spec]
      simp [encodeWindow,eq_comm]
    · intro i; simp [encodeWindow,tagWire]
    · intro i a; simp only [encodeWindow,cellWire,Fin.addCases_right,Equiv.symm_apply_apply]

theorem width_formula {Λ : Type} (labels : List Λ) (r : Nat) :
    width labels r = 12*labels.length + 6*(2*r+1) := by
  simp [width, centers_length, symbols];ring

theorem window_gates {Λ : Type} [Inhabited Λ] [DecidableEq Λ]
    (labels : List Λ) (T : TM0.Machine Symbol Λ) (r : Nat) :
    (windowBundle labels T r).gates = width labels r * (1+144*labels.length) := by
  rw [windowBundle, bundleOfFamily_gates]
  have h (o : Fin (width labels r)) :
      (outputCircuit labels T r o).gates = 1+144*labels.length := by
    refine Fin.addCases ?_ ?_ o
    · intro j; simp [outputCircuit, row_gates, centers_length, symbols];ring
    · intro j; simp [outputCircuit, row_gates, centers_length, symbols];ring
  simp only [h, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
-- SG3_LITERAL_AUDIT: mechanical checks, not independent mathematical reproof.
theorem check_window_correct {Λ : Type} [Inhabited Λ] [DecidableEq Λ]
    (labels : List Λ) (complete : ∀ q, q ∈ labels) (T : TM0.Machine Symbol Λ)
    (r : Nat) (s : Bool × TM0.Cfg Symbol Λ) :
    (windowBundle labels T r).evalFun (encodeWindow labels (r+1) s) =
      encodeWindow labels r (saturatedStep T s) :=
  window_correct labels complete T r s

theorem check_width_formula {Λ : Type} (labels : List Λ) (r : Nat) :
    width labels r = 12*labels.length + 6*(2*r+1) :=
  width_formula labels r

theorem check_window_gates {Λ : Type} [Inhabited Λ] [DecidableEq Λ]
    (labels : List Λ) (T : TM0.Machine Symbol Λ) (r : Nat) :
    (windowBundle labels T r).gates = width labels r * (1+144*labels.length) :=
  window_gates labels T r

#check (@andAt : ∀ {_n : Nat} (_i _j : Fin _n),
    DagCircuit _n)
#check (@eval_andAt : ∀ {_n : Nat} (_i _j : Fin _n) (_x : Bitstring _n),
    eval (andAt _i _j) _x = (_x _i && _x _j))
#check (@row : ∀ {_A _B _C : Type} [DecidableEq _C] {_n : Nat}
    (_as : List _A) (_bs : List _B) (_wa : Fin _as.length → Fin _n)
    (_wb : Fin _as.length → Fin _bs.length → Fin _n) (_f : _A → _B → _C) (_c : _C),
    DagCircuit _n)
#check (@row_correct : ∀ {_A _B _C : Type} [DecidableEq _A] [DecidableEq _B]
    [DecidableEq _C] {_n : Nat} (_as : List _A) (_bs : List _B)
    (_wa : Fin _as.length → Fin _n) (_wb : Fin _as.length → Fin _bs.length → Fin _n)
    (_f : _A → _B → _C) (_c : _C) (_x : Bitstring _n) (_a : _A) (_v : _A → _B)
    (_ha : _a ∈ _as) (_hb : ∀ _a, _v _a ∈ _bs)
    (_hta : ∀ i, _x (_wa i) = decide (_as[i] = _a))
    (_htb : ∀ i j, _x (_wb i j) = decide (_bs[j] = _v _as[i])),
    eval (row _as _bs _wa _wb _f _c) _x = decide (_f _a (_v _a) = _c))
#check (@row_gates : ∀ {_A _B _C : Type} [DecidableEq _C] {_n : Nat}
    (_as : List _A) (_bs : List _B) (_wa : Fin _as.length → Fin _n)
    (_wb : Fin _as.length → Fin _bs.length → Fin _n) (_f : _A → _B → _C) (_c : _C),
    (row _as _bs _wa _wb _f _c).gates = 1 + 2*(_as.length*_bs.length))
#check (@symbol_mem : ∀ (_a : Symbol),
    _a ∈ symbols)
#check (@tag_mem : ∀ {_Λ : Type} (_labels : List _Λ) (_complete : ∀ q, q ∈ _labels)
    (_t : Center _Λ),
    _t ∈ centers _labels)
#check (@product_length : ∀ {_A _B : Type} (_as : List _A) (_bs : List _B),
    (_as.product _bs).length = _as.length*_bs.length)
#check (@centers_length : ∀ {_Λ : Type} (_labels : List _Λ),
    (centers _labels).length = 12*_labels.length)
#check (@outputCircuit : ∀ {_Λ : Type} [Inhabited _Λ] [DecidableEq _Λ]
    (_labels : List _Λ) (_T : TM0.Machine Symbol _Λ) (_r : Nat),
    Fin (width _labels _r) → DagCircuit (width _labels (_r+1)))
#check (@windowBundle : ∀ {_Λ : Type} [Inhabited _Λ] [DecidableEq _Λ]
    (_labels : List _Λ) (_T : TM0.Machine Symbol _Λ) (_r : Nat),
    DagBundle (width _labels (_r+1)) (width _labels _r))
#check (@window_correct : ∀ {_Λ : Type} [Inhabited _Λ] [DecidableEq _Λ]
    (_labels : List _Λ) (_complete : ∀ q, q ∈ _labels) (_T : TM0.Machine Symbol _Λ)
    (_r : Nat) (_s : Bool × TM0.Cfg Symbol _Λ),
    (windowBundle _labels _T _r).evalFun (encodeWindow _labels (_r+1) _s) =
      encodeWindow _labels _r (saturatedStep _T _s))
#check (@width_formula : ∀ {_Λ : Type} (_labels : List _Λ) (_r : Nat),
    width _labels _r = 12*_labels.length + 6*(2*_r+1))
#check (@window_gates : ∀ {_Λ : Type} [Inhabited _Λ] [DecidableEq _Λ]
    (_labels : List _Λ) (_T : TM0.Machine Symbol _Λ) (_r : Nat),
    (windowBundle _labels _T _r).gates = width _labels _r * (1+144*_labels.length))
#check (@check_window_correct : ∀ {_Λ : Type} [Inhabited _Λ] [DecidableEq _Λ]
    (_labels : List _Λ) (_complete : ∀ q, q ∈ _labels) (_T : TM0.Machine Symbol _Λ)
    (_r : Nat) (_s : Bool × TM0.Cfg Symbol _Λ),
    (windowBundle _labels _T _r).evalFun (encodeWindow _labels (_r+1) _s) =
      encodeWindow _labels _r (saturatedStep _T _s))
#check (@check_width_formula : ∀ {_Λ : Type} (_labels : List _Λ) (_r : Nat),
    width _labels _r = 12*_labels.length + 6*(2*_r+1))
#check (@check_window_gates : ∀ {_Λ : Type} [Inhabited _Λ] [DecidableEq _Λ]
    (_labels : List _Λ) (_T : TM0.Machine Symbol _Λ) (_r : Nat),
    (windowBundle _labels _T _r).gates = width _labels _r * (1+144*_labels.length))
#print axioms andAt
#print axioms eval_andAt
#print axioms row
#print axioms row_correct
#print axioms row_gates
#print axioms symbol_mem
#print axioms tag_mem
#print axioms product_length
#print axioms centers_length
#print axioms outputCircuit
#print axioms windowBundle
#print axioms window_correct
#print axioms width_formula
#print axioms window_gates
#print axioms check_window_correct
#print axioms check_width_formula
#print axioms check_window_gates

end UniformClassBridgeClosure.TM0DAG.Window
