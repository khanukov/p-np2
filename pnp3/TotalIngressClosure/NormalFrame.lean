import TotalIngressClosure.Header
import FullIngressClosure.Frame
namespace TotalIngressClosure
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier Pnp4.Frontier.ContractExpansion
open Pnp4.AlgorithmsToLowerBounds PairEncoding Lean Elab Command
run_cmd do
  let env ← getEnv
  let specs := ["InstallerFrame","InstallerFrame.mk","ready","ready_low","ready_assignment","ready_bank1","ready_tail",
    "ready_delimiters","ready_banks","actual_source","arena_room"].map fun key =>
    ("FullIngressClosure.Frame","FullIngressClosure",key,if key="InstallerFrame.mk" then "installerMk" else key)
  let fields := [("arena","oldArena"),("eof","oldEOF"),("reg","oldReg"),("sep","oldSep"),
    ("right","oldRight"),("marks","oldMarks"),("gap","oldGap"),("fence","oldFence")]
  let specs := specs ++ fields.map (fun (key,aliasName) =>
    ("AllArityBitLength.Raw","AllArityBitLength","Cells."++key,aliasName))
  let specs:=specs++[("AllArityBitLength.Raw","AllArityBitLength","actual_cells","oldCells"),
    ("TotalIngressClosure.Header","TotalIngressClosure","table_budget_width","tableWidth")]
  for (mod,ns,key,aliasName) in specs do
    let found:=env.constants.toList.filter fun (n,_)=>
      n.toString.startsWith ("_private."++mod++".") && n.toString.endsWith ("."++ns++"."++key)
    match found with
    | [(n,ci)]=>
      logInfo m!"private-term|{n}|type={ci.type}"
      modifyScope fun s=>{s with openDecls:=.explicit (Name.str .anonymous aliasName) n::s.openDecls}
    | _=>throwError "Nonunique same actual ready frame {mod}/{key}: {found.map Prod.fst}"
set_option maxRecDepth 10000 in
private theorem normal_frame (k : Nat) {a m n0 z : Nat} (x : Bitstring a) (w : Bitstring m)
    (gamma:FixedContentGammaTerminator.gammaZeros? (Fin.append x w)=some z)
    (capacity:n0 < FixedRawLengthFence.capacity a m z)
    (rows:2^n0 ≤ FixedRawLengthFence.fencePos (pairLength a m)-(a+m+z+n0+3)-1) :
    let S:=a+m; let R:=pairLength a m; let B:=FixedRawLengthFence.allocation R
    let n:=n0; let L:=S+z+2; let F:=FixedRawLengthFence.fencePos R
    let p:=min (9+2*z+2^n) S; let r:=S-p
    let U:=Body.extend (Body.installedTape (SmallIngress.prepared B x w z n) L n)
    let V:=Stream.Target.image U S z n (9+2*z) (2^n) (2^n) false
    let I:=ready V L n F r (n^k+k) (Cursor.Target.W k n)
    p < S → bitLength n ≤ r → Cursor.Target.W k n ≤ r →
    InstallerFrame R S z n p (n^k+k) (Cursor.Target.W k n) (2^n) (Fin.append x w) I ∧
    Cursor.Target.M k n z=p+bitLength (Cursor.Target.W k n)+Cursor.Target.W k n ∧
    SerializedBody.sourceMode (Fin.append x w) (Cursor.Target.M k n z)=
      SerializedBody.sourceMode (Fin.append x w) (p+bitLength (Cursor.Target.W k n)+Cursor.Target.W k n) := by
  intro S R B n L F p r U V I phys ellFits wFits
  have sr : S ≤ R := by dsimp only [S,R,pairLength]; omega
  obtain ⟨cells,_short,fresh⟩:=oldCells x w gamma capacity rows
  have arena:=oldArena cells
  change S+z+n+3+2^n < F at arena
  have nr:n ≤ R:=tableWidth R S z n (by dsimp only [R,pairLength];omega) arena
  have room : L+n+1 < F := arena_room S z n (2^n) F arena
  have rp : 0 < r := Nat.sub_pos_of_lt phys
  have positive : 1 ≤ R := by dsimp only [R,pairLength]; omega
  have gFits : n^k+k ≤ r := by
    have h:=Nat.mul_le_mul_right (n^k+k) (show 1 ≤ bitLength n+4 by omega)
    dsimp only [Cursor.Target.W] at wFits
    omega
  have fit:=BodyIngress.workspace_room R r n positive ((Nat.sub_le S p).trans sr) nr
  change SerializedBody.delimiter F r n 12 < tapeLength R B at fit
  have extendFresh (i : Nat) (lo : F < i) (hi : i ≤ SerializedBody.delimiter F r n 12) : V i=none :=
    fresh ⟨i,lt_of_le_of_lt hi fit⟩ lo
  have base (i : Nat) (hi : i ≤ F) (outside : i ≤ L ∨ L+n+1 ≤ i) : I i=V i :=
    ready_low V L n F r (n^k+k) (Cursor.Target.W k n) i room hi outside
  have bn:=ready_banks V L n F r (n^k+k) (Cursor.Target.W k n) room
  have mExact : Cursor.Target.M k n z=p+bitLength (Cursor.Target.W k n)+Cursor.Target.W k n := by
    have before : 9+2*z+2^n < S := by dsimp only [p] at phys; omega
    dsimp only [Cursor.Target.M,p]
    rw [Nat.min_eq_left (Nat.le_of_lt before)]
  refine ⟨?_,mExact,congrArg (SerializedBody.sourceMode (Fin.append x w)) mExact⟩
  refine installerMk positive sr nr phys gFits wFits ellFits (by positivity) arena ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ bn.1 ?_ bn.2.1 bn.2.2.1 bn.2.2.2 ?_
  · intro i lo hi
    have before : 9+2*z+2^n < S := by dsimp only [p] at phys; omega
    have eqp : p=9+2*z+2^n := Nat.min_eq_left (Nat.le_of_lt before)
    have above : 9+2*z ≤ i := by
      rw [eqp] at lo
      exact (Nat.le_add_right (9+2*z) (2^n)).trans lo
    rw [base i (by omega) (Or.inl (by dsimp only [L]; omega))]
    exact actual_source x w gamma (FixedRawLengthFence.resource_bounds R).1 (Nat.le_of_lt capacity) i above hi
  · rw [base S (by omega) (Or.inl (by dsimp only [L]; omega))]
    exact oldEOF cells
  · intro i lo hi
    rw [base i (by omega) (Or.inl (by dsimp only [L] at hi ⊢; omega))]
    exact oldReg cells i lo hi
  · rw [base L (by omega) (Or.inl le_rfl)]
    exact oldSep cells
  · rw [base (S+z+n+3) (by omega) (Or.inr (by dsimp only [L]; omega))]
    exact oldRight cells
  · intro j
    exact ready_assignment V L n F r (n^k+k) (Cursor.Target.W k n) _ room (by have h:=j.isLt; dsimp only [L]; omega) (by dsimp only [L]; omega)
  · intro i lo hi
    rw [base i (by omega) (Or.inr (by dsimp only [L]; omega))]
    exact oldMarks cells i lo hi
  · intro i lo hi
    rw [base i (by omega) (Or.inr (by
      have a : L+n+1=S+z+n+3 := by dsimp only [L]; omega
      rw [a]
      exact (Nat.le_add_right (S+z+n+3) (2^n)).trans (Nat.le_of_lt lo)))]
    exact oldGap cells i lo hi
  · rw [base F le_rfl (Or.inr (by omega))]
    exact oldFence cells
  · intro j hj
    apply ready_delimiters V L n F r (n^k+k) (Cursor.Target.W k n) room rp
    · intro i lo
      by_cases hi : i < tapeLength R B
      · exact fresh ⟨i,hi⟩ lo
      · dsimp only [V,Stream.Target.image,U,Body.extend]
        rw [if_neg (by omega),if_neg (by omega)]
        change (if h : i < tapeLength R B then _ else none)=none
        rw [dif_neg hi]
    · exact hj
  · intro i lo hi
    exact ready_bank1 V L n F r (n^k+k) (Cursor.Target.W k n) i room ellFits lo hi
  · intro i lo hi
    change ready V L n F r (n^k+k) (Cursor.Target.W k n) i=none
    rw [ready_tail V L n F r (n^k+k) (Cursor.Target.W k n) i room lo]
    exact extendFresh i (by omega) hi

end TotalIngressClosure
