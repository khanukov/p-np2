import VirtualFinalClosure.MetaFields
namespace VirtualFinalClosure.TableFlagMeaning
open Lean Elab Command
set_option autoImplicit false
run_cmd do
  let env ← getEnv
  let found:=env.constants.toList.filter fun (name,_)=>name.toString.startsWith "_private.VirtualFinalClosure.ElasticMachine." && name.toString.endsWith ".VirtualFinalClosure.Elastic.updateFlag"
  match found with
  | [(name,.defnInfo ci)]=>
    logInfo m!"private-term|{name}|kind=definition|type={ci.type}"
    modifyScope fun st=>{st with openDecls:=.explicit `updateFlag name::st.openDecls}
  | _=>throwError "Nonunique literal paid-table flag updater"
private def expected (f : Fin 4) : Bool:=decide (2 ≤ f.val)
private def matched (f : Fin 4) : Bool:=f.val%2==1
private def next (f : Fin 4) (b : Bool) : Fin 4:=
  ⟨((if expected f then 0 else 2)+(if matched f && b==expected f then 1 else 0))%4,Nat.mod_lt _ (by decide)⟩
private def folded (bits : Nat → Bool) : Nat → Fin 4
  | 0=>⟨1,by decide⟩
  | r+1=>next (folded bits r) (bits r)
private def expected_type : Fin 4 → Bool:=expected
private def matched_type : Fin 4 → Bool:=matched
private def next_type : Fin 4 → Bool → Fin 4:=next
private def folded_type : (Nat → Bool) → Nat → Fin 4:=folded
/-- Exact finite UPDATE used by the frozen runtime, for all four flag states.
No source stream or successful table traversal is assumed by this equality. -/
private theorem actual_update (f : Fin 4) (b : Bool) : updateFlag (8+f.val) b=8+(next f b).val:=by
  fin_cases f <;> cases b <;> decide
private theorem next_expected (f : Fin 4) (b : Bool) : expected (next f b)= !(expected f):=by
  fin_cases f <;> cases b <;> decide
private theorem next_matched (f : Fin 4) (b : Bool) : matched (next f b)= (matched f && b==expected f):=by
  fin_cases f <;> cases b <;> decide
private theorem testbit_succ (r : Nat) : Nat.testBit (r+1) 0= !(Nat.testBit r 0):=by
  have range:=Nat.mod_lt r (by decide : 0 < 2)
  by_cases odd : r%2=1
  · have after : (r+1)%2=0:=by omega
    simp [Nat.testBit_zero,odd,after]
  · have after : (r+1)%2=1:=by omega
    simp [Nat.testBit_zero,odd,after]
private theorem expected_fold (bits : Nat → Bool) (r : Nat) : expected (folded bits r)=Nat.testBit r 0:=by
  induction r with
  | zero=>rfl
  | succ r ih=>rw [folded,next_expected,ih,testbit_succ]
private theorem bool_match (b e : Bool) : (b==e)=true ↔ b=e:=by cases b <;> cases e <;> decide
/-- Exact whole-table mismatch invariant for the literal finite updater.
The separate physical orbit proof must establish ONE actual call per paid row;
this lemma does not replace that execution obligation. -/
private theorem matched_fold (bits : Nat → Bool) (r : Nat) :
    matched (folded bits r)=true ↔ ∀ j,j < r → bits j=Nat.testBit j 0:=by
  induction r with
  | zero=>
    constructor
    · intro _h j hj;omega
    · intro _h;rfl
  | succ r ih=>
    rw [folded,next_matched,Bool.and_eq_true,ih,expected_fold,bool_match]
    constructor
    · rintro ⟨before,last⟩ j hj
      by_cases endpoint : j=r
      · simpa only [endpoint] using last
      · exact before j (by omega)
    · intro allBits
      exact ⟨fun j hj=>allBits j (by omega),allBits r (by omega)⟩
private theorem whole_table (n : Nat) (bits : Nat → Bool) :
    matched (folded bits (2^n))=true ↔ ∀ j : Fin (2^n),bits j.val=Nat.testBit j.val 0:=by
  rw [matched_fold]
  constructor
  · exact fun h j=>h j.val j.isLt
  · exact fun h j hj=>h ⟨j,hj⟩
#print axioms expected_type
#print axioms matched_type
#print axioms next_type
#print axioms folded_type
#print axioms actual_update
#print axioms next_expected
#print axioms next_matched
#print axioms testbit_succ
#print axioms expected_fold
#print axioms bool_match
#print axioms matched_fold
#print axioms whole_table
end VirtualFinalClosure.TableFlagMeaning
