import FullIngressClosure.Target
import BodyIngress.Raw
namespace FullIngressClosure
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier Pnp4.Frontier.ContractExpansion
open Pnp4.AlgorithmsToLowerBounds PairEncoding Lean Elab Command
set_option maxRecDepth 10000
run_cmd do
  let env ← getEnv
  for (mod,ns,key,aliasName) in [
      ("VirtualLeaf.Raw","VirtualLeaf","width","oldWidth"),
      ("AllArityBitLength.Raw","AllArityBitLength","actual_cells","oldCells"),
      ("AllArityBitLength.Raw","AllArityBitLength","Cells.arena","oldArena"),
      ("AllArityBitLength.Raw","AllArityBitLength","Cells.eof","oldEOF"),
      ("AllArityBitLength.Raw","AllArityBitLength","Cells.reg","oldReg"),
      ("AllArityBitLength.Raw","AllArityBitLength","Cells.sep","oldSep"),
      ("AllArityBitLength.Raw","AllArityBitLength","Cells.right","oldRight"),
      ("AllArityBitLength.Raw","AllArityBitLength","Cells.marks","oldMarks"),
      ("AllArityBitLength.Raw","AllArityBitLength","Cells.gap","oldGap"),
      ("AllArityBitLength.Raw","AllArityBitLength","Cells.fence","oldFence")] do
    let found := env.constants.toList.filter fun (name,_) =>
      name.toString.startsWith ("_private."++mod++".") &&
      name.toString.endsWith ("."++ns++"."++key)
    match found with
    | [(name,ci)] =>
      logInfo m!"private-term|{name}|type={ci.type}"
      modifyScope fun st => {st with openDecls:=.explicit (Name.str .anonymous aliasName) name :: st.openDecls}
    | _ => throwError "Nonunique ordinary frame term {mod}/{key}: {found.map Prod.fst}"
private def seed (V : Nat → Option Bool) (L n F r : Nat) : Nat → Option Bool :=
  AllArityBitLength.Target.seedImage (RuntimeBitLength.Target.fullImage
    (CappedWorkspace.Target.image (SuffixCap.Target.image V F r) L n F r) L n F r) F r n
private def ready (V : Nat → Option Bool) (L n F r g W : Nat) : Nat → Option Bool :=
  CarryWindow.Target.image (CappedWeight.Target.image (seed V L n F r) L n F r 0 g W 0 0)
    F r n g (bitLength W) 0 0 W
private theorem ready_low (V : Nat → Option Bool) (L n F r g W i : Nat)
    (_room : L+n+1 < F) (hi : i ≤ F) (outside : i ≤ L ∨ L+n+1 ≤ i) :
    ready V L n F r g W i=V i := by
  dsimp only [ready,CarryWindow.Target.image,CappedWeight.Target.image,seed,
    AllArityBitLength.Target.seedImage,RuntimeBitLength.Target.fullImage,
    CappedWorkspace.Target.image,SuffixCap.Target.image]
  repeat' rw [if_neg (by omega)]
private theorem ready_assignment (V : Nat → Option Bool) (L n F r g W i : Nat)
    (room : L+n+1 < F) (lo : L < i) (hi : i < L+n+1) :
    ready V L n F r g W i=some false := by
  dsimp only [ready,CarryWindow.Target.image,CappedWeight.Target.image]
  rw [if_neg (by omega),if_neg (by omega),if_neg (by omega),if_neg (by omega),if_neg (by omega)]
  rw [if_pos ⟨lo,hi⟩,decide_eq_false (by omega)]
private theorem ready_bank1 (V : Nat → Option Bool) (L n F r g W i : Nat)
    (room : L+n+1 < F) (fits : bitLength n ≤ r)
    (lo : F+r+2 < i) (hi : i < F+r+n+3) :
    ready V L n F r g W i=some false := by
  dsimp only [ready,CarryWindow.Target.image,CappedWeight.Target.image,seed,
    AllArityBitLength.Target.seedImage,RuntimeBitLength.Target.fullImage]
  rw [if_neg (by omega),if_neg (by omega),if_neg (by omega),if_neg (by omega),if_neg (by omega)]
  rw [if_neg (by omega),if_neg (by omega),if_neg (by omega),if_neg (by omega),if_neg (by omega)]
  rw [if_neg (by omega),if_neg (by omega),if_pos ⟨lo,hi⟩]
  simp only [show ¬r < bitLength n by omega,false_and,decide_false]
private theorem ready_tail (V : Nat → Option Bool) (L n F r g W i : Nat)
    (room : L+n+1 < F) (hi : F+5*r+n+7 < i) :
    ready V L n F r g W i=V i := by
  have minBound:=Nat.min_le_right (bitLength n) r
  dsimp only [ready,CarryWindow.Target.image,CappedWeight.Target.image,seed,
    AllArityBitLength.Target.seedImage,RuntimeBitLength.Target.fullImage,
    CappedWorkspace.Target.image,SuffixCap.Target.image]
  repeat' rw [if_neg (by omega)]
private theorem ready_delimiters (V : Nat → Option Bool) (L n F r g W : Nat)
    (_room : L+n+1 < F) (rp : 0 < r)
    (fresh : ∀ i, F < i → V i=none) (j : Nat) (hj : j ≤ 6) :
    ready V L n F r g W (SerializedBody.delimiter F r n j)=none := by
  have minBound:=Nat.min_le_right (bitLength n) r
  interval_cases j
  all_goals dsimp only [ready,CarryWindow.Target.image,CappedWeight.Target.image,seed,
    AllArityBitLength.Target.seedImage,RuntimeBitLength.Target.fullImage,
    CappedWorkspace.Target.image,SuffixCap.Target.image,SerializedBody.delimiter]
  all_goals repeat' rw [if_neg (by omega)]
  all_goals exact fresh _ (by omega)
private theorem ready_banks (V : Nat → Option Bool) (L n F r g W : Nat)
    (_room : L+n+1 < F) :
    (∀ i, F+1 < i → i < F+r+2 → ready V L n F r g W i=some (decide (i-(F+1) ≤ g))) ∧
    (∀ i, F+r+n+3 < i → i < F+2*r+n+4 → ready V L n F r g W i=some (decide (i-(F+r+n+3) ≤ bitLength W))) ∧
    (∀ i, F+2*r+n+4 < i → i < F+4*r+n+6 → i ≠ F+3*r+n+5 → ready V L n F r g W i=some false) ∧
    (∀ i, F+4*r+n+6 < i → i < F+5*r+n+7 → ready V L n F r g W i=some (decide (i-(F+4*r+n+6) ≤ W))) := by
  refine ⟨?_,?_,?_,?_⟩
  all_goals intro i lo hi
  · dsimp only [ready,CarryWindow.Target.image]
    rw [if_pos ⟨lo,hi⟩]
    congr 1
    exact decide_eq_decide.mpr (by omega)
  · dsimp only [ready,CarryWindow.Target.image]
    rw [if_neg (by omega),if_pos ⟨lo,hi⟩]
    congr 1
    exact decide_eq_decide.mpr (by omega)
  · intro ne
    dsimp only [ready,CarryWindow.Target.image]
    split_ifs <;> first | rfl | (exfalso; omega) | (rw [decide_eq_false (by omega)])
  · dsimp only [ready,CarryWindow.Target.image]
    rw [if_neg (by omega),if_neg (by omega),if_neg (by omega),if_neg (by omega),if_pos ⟨lo,hi⟩]
    congr 1
    exact decide_eq_decide.mpr (by omega)
private structure InstallerFrame (R S z n p g W Q : Nat) (source : Fin S → Bool)
    (T : Nat → Option Bool) : Prop where
  positive : 1 ≤ R
  sourceWidth : S ≤ R
  width : n ≤ R
  physical : p < S
  gFits : g ≤ S-p
  wFits : W ≤ S-p
  ellFits : bitLength n ≤ S-p
  paid : 0 < Q
  arena : S+z+n+3+Q < FixedRawLengthFence.fencePos R
  sourceCells : ∀ i, p ≤ i → ∀ hi : i < S, T i=some (source ⟨i,hi⟩)
  eof : T S=none
  register : ∀ i, S < i → i < S+z+2 → T i=some false
  separator : T (S+z+2)=none
  headBlank : T (S+z+n+3)=none
  assignment : ∀ j : Fin n, T (S+z+n+3-1-j.val)=some false
  marks : ∀ i, S+z+n+3 < i → i ≤ S+z+n+3+Q → T i=some true
  gap : ∀ i, S+z+n+3+Q < i → i < FixedRawLengthFence.fencePos R → T i=none
  fence : T (FixedRawLengthFence.fencePos R)=some false
  delimiters : ∀ j, j ≤ 6 → T (SerializedBody.delimiter (FixedRawLengthFence.fencePos R) (S-p) n j)=none
  bank0 : ∀ i, FixedRawLengthFence.fencePos R+1 < i → i < FixedRawLengthFence.fencePos R+(S-p)+2 →
    T i=some (decide (i-(FixedRawLengthFence.fencePos R+1) ≤ g))
  bank1 : ∀ i, FixedRawLengthFence.fencePos R+(S-p)+2 < i → i < FixedRawLengthFence.fencePos R+(S-p)+n+3 → T i=some false
  bank2 : ∀ i, FixedRawLengthFence.fencePos R+(S-p)+n+3 < i → i < FixedRawLengthFence.fencePos R+2*(S-p)+n+4 →
    T i=some (decide (i-(FixedRawLengthFence.fencePos R+(S-p)+n+3) ≤ bitLength W))
  bank34 : ∀ i, FixedRawLengthFence.fencePos R+2*(S-p)+n+4 < i → i < FixedRawLengthFence.fencePos R+4*(S-p)+n+6 →
    i ≠ FixedRawLengthFence.fencePos R+3*(S-p)+n+5 → T i=some false
  bank5 : ∀ i, FixedRawLengthFence.fencePos R+4*(S-p)+n+6 < i → i < FixedRawLengthFence.fencePos R+5*(S-p)+n+7 →
    T i=some (decide (i-(FixedRawLengthFence.fencePos R+4*(S-p)+n+6) ≤ W))
  fresh : ∀ i, FixedRawLengthFence.fencePos R+5*(S-p)+n+7 < i →
    i ≤ SerializedBody.delimiter (FixedRawLengthFence.fencePos R) (S-p) n 12 → T i=none
private theorem actual_source {a m B z n : Nat} (x : Bitstring a) (w : Bitstring m)
    (gamma : FixedContentGammaTerminator.gammaZeros? (Fin.append x w)=some z)
    (resource : 2*pairLength a m+2 ≤ B) (cap : n ≤ FixedRawLengthFence.capacity a m z)
    (i : Nat) (lo : 9+2*z ≤ i) (hi : i < a+m) :
    let U:=Body.extend (Body.installedTape (SmallIngress.prepared B x w z n) (a+m+z+2) n)
    Stream.Target.image U (a+m) z n (9+2*z) (2^n) (2^n) false i=some ((Fin.append x w) ⟨i,hi⟩) := by
  intro U
  have fit : i < tapeLength (pairLength a m) B := by unfold tapeLength pairLength; omega
  dsimp only [Stream.Target.image]
  rw [if_neg (by omega),if_neg (by omega)]
  change U i=_
  rw [show U i=Body.installedTape (SmallIngress.prepared B x w z n) (a+m+z+2) n ⟨i,fit⟩ from Body.extend_read _ ⟨i,fit⟩]
  dsimp only [Body.installedTape,SmallIngress.prepared]
  rw [if_neg (by omega),if_neg (by omega)]
  exact Body.raw_source_after_header x w gamma resource cap ⟨i,fit⟩ (by change 8+2*z+1 ≤ i; omega) hi
private theorem arena_room (S z n Q F : Nat) (h : S+z+n+3+Q < F) :
    (S+z+2)+n+1 < F := by omega
private theorem accepted_frame (k : Nat) {a m : Nat} (x : Bitstring a) (w : Bitstring m)
    (accepted : PartAEndpoint.thresholdContentWitnessRelation k a m x w=true)
    (pr : AcceptedBody.Parsed k)
    (parsed : contentInput? (treeCircuitWitnessCodec (thresholdPoly k)) (Fin.append x w)=some pr)
    (z : Nat) (gamma : FixedContentGammaTerminator.gammaZeros? (Fin.append x w)=some z) :
    let S:=a+m; let R:=pairLength a m; let B:=FixedRawLengthFence.allocation R
    let n:=pr.2.n; let L:=S+z+2; let F:=FixedRawLengthFence.fencePos R
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
  have ns := oldWidth x w accepted parsed
  change n ≤ S at ns
  have nr:=ns.trans sr
  have capacity:=AcceptedBody.strict_capacity x w gamma ns
  have rows:=Stream.accepted_rows_fit k x w accepted parsed gamma
  obtain ⟨cells,_short,fresh⟩:=oldCells x w gamma capacity rows
  have arena:=oldArena cells
  change S+z+n+3+2^n < F at arena
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
  refine ⟨positive,sr,nr,phys,gFits,wFits,ellFits,by positivity,arena,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,bn.1,?_,bn.2.1,bn.2.2.1,bn.2.2.2,?_⟩
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

end FullIngressClosure
