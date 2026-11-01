import VirtualFinalClosure.ModeRows
namespace VirtualFinalClosure.MarkerState
open Lean Elab Command
set_option autoImplicit false
run_cmd do
  let env ← getEnv
  for key in ["flag","mode","phase","seen","bad","changeMeta","encodeMeta"] do
    let found:=env.constants.toList.filter fun (n,_)=>
      n.toString.startsWith "_private.VirtualFinalClosure.ElasticMachine." &&
      n.toString.endsWith (".VirtualFinalClosure.Elastic."++key)
    match found with
    | [(n,.defnInfo ci)]=>
      logInfo m!"private-term|{n}|kind=definition|type={ci.type}"
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous key) n::st.openDecls}
    | _=>throwError "Nonunique actual finite metadata field {key}"
private theorem encode_fields (f v p s b : Nat)
    (hf : f < 4) (hv : v < 3) (hp : p < 3) (hs : s < 2) (hb : b < 2) :
    flag (encodeMeta f v p s b)=f ∧ mode (encodeMeta f v p s b)=v ∧
      phase (encodeMeta f v p s b)=p ∧ seen (encodeMeta f v p s b)=s ∧ bad (encodeMeta f v p s b)=b := by
  have bound : f+4*v+12*p+36*s+72*b < 144 := by omega
  have lower12 : f+4*v < 12 := by omega
  have lower36 : f+4*v+12*p < 36 := by omega
  have lower72 : f+4*v+12*p+36*s < 72 := by omega
  dsimp only [encodeMeta,flag,mode,phase,seen,bad]
  rw [Nat.mod_eq_of_lt bound]
  have q4 : (f+4*v+12*p+36*s+72*b)/4=v+3*p+9*s+18*b := by omega
  have q12 : (f+4*v+12*p+36*s+72*b)/12=p+3*s+6*b := by omega
  have q36 : (f+4*v+12*p+36*s+72*b)/36=s+2*b := by omega
  have q72 : (f+4*v+12*p+36*s+72*b)/72=b := by omega
  rw [q4,q12,q36,q72]
  omega
private theorem bit_change (m : Nat) (b : Bool) :
    flag (changeMeta (if b then 2 else 1) m)=flag m ∧
    mode (changeMeta (if b then 2 else 1) m)=(if b then 1 else 0) ∧
    phase (changeMeta (if b then 2 else 1) m)=phase m ∧
    seen (changeMeta (if b then 2 else 1) m)=(if b then 1 else seen m) ∧
    bad (changeMeta (if b then 2 else 1) m)=bad m := by
  have hf : flag m < 4 := Nat.mod_lt _ (by decide)
  have hp : phase m < 3 := Nat.mod_lt _ (by decide)
  have hs : seen m < 2 := Nat.mod_lt _ (by decide)
  have hb : bad m < 2 := Nat.mod_lt _ (by decide)
  cases b
  · exact encode_fields (flag m) 0 (phase m) (seen m) (bad m) hf (by decide) hp hs hb
  · exact encode_fields (flag m) 1 (phase m) 1 (bad m) hf (by decide) hp (by decide) hb
private theorem bit_bound (m : Nat) (b : Bool) : changeMeta (if b then 2 else 1) m < 144 := by
  cases b
  · change changeMeta 1 m < 144
    dsimp only [changeMeta,encodeMeta]
    exact Nat.mod_lt _ (by decide)
  · change changeMeta 2 m < 144
    dsimp only [changeMeta,encodeMeta]
    exact Nat.mod_lt _ (by decide)
/-- Proof-side index for the successive ACTUAL finite controls. Neither beta
nor the iteration counter is passed to the transition constructor. -/
private def modes (m : Nat) (beta : Nat → Bool) : Nat → Nat
  | 0=>m
  | j+1=>changeMeta (if beta j then 2 else 1) (modes m beta j)
private theorem modes_bound (m : Nat) (beta : Nat → Bool) (j : Nat) (initial : m < 144) :
    modes m beta j < 144 := by
  cases j with
  | zero=>exact initial
  | succ j=>
    rw [modes]
    exact bit_bound _ _
private theorem modes_mode (m : Nat) (beta : Nat → Bool) (j : Nat) (positive : 0 < j) :
    mode (modes m beta j)=(if beta (j-1) then 1 else 0) := by
  cases j with
  | zero=>omega
  | succ j=>exact (bit_change (modes m beta j) (beta j)).2.1
private theorem modes_fields (m : Nat) (beta : Nat → Bool) (j : Nat) :
    flag (modes m beta j)=flag m ∧ phase (modes m beta j)=phase m ∧ bad (modes m beta j)=bad m := by
  induction j with
  | zero=>exact ⟨rfl,rfl,rfl⟩
  | succ j ih=>
    have next:=bit_change (modes m beta j) (beta j)
    exact ⟨next.1.trans ih.1,next.2.2.1.trans ih.2.1,next.2.2.2.2.trans ih.2.2⟩
private theorem modes_seen_zero (m : Nat) (beta : Nat → Bool) (j : Nat) (zero : seen m=0) :
    seen (modes m beta j)=0 ↔ ∀ i,i < j → beta i=false := by
  induction j with
  | zero=>simp [modes,zero]
  | succ j ih=>
    have next:seen (modes m beta (j+1))=(if beta j then 1 else seen (modes m beta j)) :=
      (bit_change (modes m beta j) (beta j)).2.2.2.1
    rw [next]
    cases bit : beta j
    · change seen (modes m beta j)=0 ↔ _
      rw [ih]
      constructor
      · intro previous i hi
        by_cases last : i=j
        · simpa only [last] using bit
        · exact previous i (by omega)
      · intro bitsZero i hi
        exact bitsZero i (by omega)
    · change (1:Nat)=0 ↔ _
      constructor
      · omega
      · intro bitsZero
        have impossible:=bitsZero j (by omega)
        rw [bit] at impossible
        contradiction
#print axioms bit_change
#print axioms modes_bound
#print axioms modes_mode
#print axioms modes_fields
#print axioms modes_seen_zero
end VirtualFinalClosure.MarkerState
