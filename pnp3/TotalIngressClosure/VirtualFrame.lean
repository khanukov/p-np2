import TotalIngressClosure.EofTotal
import TotalIngressClosure.VirtualTail
namespace TotalIngressClosure
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier Pnp4.Frontier.ContractExpansion
open Pnp4.AlgorithmsToLowerBounds PairEncoding Lean Elab Command
run_cmd do
  let env ← getEnv
  for (key,aliasName) in [("actual_cells","actualCells"),("Cells.arena","arenaCell"),
      ("Cells.sep","sepCell"),("Cells.right","rightCell")] do
    let found:=env.constants.toList.filter fun (n,_)=>n.toString.startsWith "_private.AllArityWorkspace.Runtime." &&
      n.toString.endsWith (".AllArityWorkspace."++key)
    match found with
    | [(n,.thmInfo ci)]=>
      logInfo m!"private-term|{n}|kind=theorem|type={ci.type}"
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous aliasName) n::st.openDecls}
    | _=>throwError "Nonunique actual restored assignment frame {key}: {found.map Prod.fst}"
private theorem virtual_frame {a m z n:Nat}(x:Bitstring a)(w:Bitstring m)
    (gamma:FixedContentGammaTerminator.gammaZeros? (Fin.append x w)=some z)
    (cap:n < FixedRawLengthFence.capacity a m z)
    (rows:2^n ≤ FixedRawLengthFence.fencePos (pairLength a m)-(a+m+z+n+3)-1) :
    let S:=a+m;let L:=S+z+2;let F:=FixedRawLengthFence.fencePos (pairLength a m)
    let B:=FixedRawLengthFence.allocation (pairLength a m)
    let U:=Body.extend (Body.installedTape (SmallIngress.prepared B x w z n) L n)
    let V:=Stream.Target.image U S z n (9+2*z) (2^n) (2^n) false
    S+z+n+3+2^n < F ∧ V L=none ∧ V (S+z+n+3)=none ∧
      ∀ j:Fin n,V (S+z+n+3-1-j.val)=some false:=by
  intro S L F B U V
  obtain ⟨cells,_short,_fresh⟩:=actualCells x w gamma cap rows
  refine ⟨arenaCell cells,sepCell cells,rightCell cells,?_⟩
  intro j
  have lower:L < S+z+n+3-1-j.val:=by dsimp only [L];omega
  have upper:S+z+n+3-1-j.val < L+n+1:=by dsimp only [L];omega
  dsimp only [V,Stream.Target.image]
  rw [if_pos ⟨lower,upper⟩,CappedWorkspace.overflow_bits]
  simp [List.getElem!_eq_getElem?_getD,List.getElem?_replicate]
  split_ifs <;> rfl
private theorem clear_frame (T:Nat → Option Bool)(k S n z F:Nat)
    (beyond:S ≤ Cursor.Target.M k n z) (room:S+z+n+3 < F) :
    Cursor.Target.image T k S n z F (S+z+2)=T (S+z+2) ∧
    Cursor.Target.image T k S n z F (S+z+n+3)=T (S+z+n+3) ∧
    ∀ j:Fin n,Cursor.Target.image T k S n z F (S+z+n+3-1-j.val)=T (S+z+n+3-1-j.val):=by
  have low(i:Nat)(lo:S ≤ i)(hi:i ≤ S+z+n+3):Cursor.Target.image T k S n z F i=T i:=by
    dsimp only [Cursor.Target.image]
    rw [if_neg (by omega)]
    split_ifs
    · dsimp only [Cursor.Target.scratch]
      rw [if_neg (by omega)]
    · rfl
  exact ⟨low _ (by omega) (by omega),low _ (by omega) (by omega),fun j=>low _ (by omega) (by omega)⟩
end TotalIngressClosure
