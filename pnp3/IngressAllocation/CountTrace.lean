import IngressAllocation.ArithmeticPaths
namespace IngressAllocation
open Pnp3.Complexity.Uniform.V1 Lean Elab Command
run_cmd do
  let env ← getEnv
  for (mod,ns,key,aliasName) in [
      ("SuffixCap.Kernel","SuffixCap","Frame","CountFrame"),
      ("SuffixCap.Kernel","SuffixCap","Frame.mk","countFrame"),
      ("SuffixCap.Kernel","SuffixCap","base","countBase"),
      ("SuffixCap.Kernel","SuffixCap","keep","countKeep"),
      ("SuffixCap.Kernel","SuffixCap","hop","countHop"),
      ("SuffixCap.Kernel","SuffixCap","small_mod","smallMod"),
      ("SuffixCap.Kernel","SuffixCap","count_iteration","countIteration"),
      ("SuffixCap.Kernel","SuffixCap","Path.append","pathAppend"),
      ("IngressAllocation.ArithmeticPaths","IngressAllocation.SuffixStage","every_head","pathHeads")] do
    let found:=env.constants.toList.filter fun (n,_) =>
      n.toString.startsWith ("_private."++mod++".") && n.toString.endsWith ("."++ns++"."++key)
    match found with
    | [(n,ci)] =>
      logInfo m!"private-term|{n}|type={ci.type}"
      modifyScope fun st => {st with openDecls:=.explicit (Name.str .anonymous aliasName) n :: st.openDecls}
    | _=>throwError "Nonunique same-table counted path interface {mod}/{key}: {found.map Prod.fst}"
private theorem counted_heads (k N B p S z n Q F : Nat) (T : Nat → Option Bool)
    (pos : 0 < p) (physical : p < S) (paid : 0 < Q) (room : S+z+n+3+Q < F)
    (source : ∀ i,p ≤ i → i < S → ∃ b,T i=some b) (eof : T S=none)
    (reg : ∀ i,S < i → i < S+z+2 → T i=some false) (sep : T (S+z+2)=none)
    (assn : ∀ i,S+z+2 < i → i < S+z+n+3 → ∃ b,T i=some b)
    (right : T (S+z+n+3)=none)
    (marks : ∀ i,S+z+n+3 < i → i ≤ S+z+n+3+Q → T i=some true)
    (gap : ∀ i,S+z+n+3+Q < i → i < F → T i=none) (fence : T F=some false)
    (fresh : ∀ i,F < i → i ≤ F+(S-p)+2 → T i=none)
    (fit : F+(S-p)+2 < tapeLength N B) :
    ∀ u,u ≤ 2+(S-p)*(2*(F-p)+6) →
      ((Cursor.machine k).run u
        (⟨Cursor.q k 58,⟨p,by omega⟩,fun i=>T i.val⟩ : Config (Cursor.machine k).stateCount N B)).head.val ≤ F+(S-p)+2 := by
  let r:=S-p
  have fr : CountFrame T p S z n Q F r:=
    countFrame pos physical rfl paid room source eof reg sep assn right marks gap fence fresh
  obtain ⟨b,hb⟩:=source p le_rfl physical
  have same:=countKeep (Cursor.q k 58) (Cursor.q k 64) p p T .stay
    (by simp only [Cursor.q,smallMod k 58 (by omega)];omega)
    (P:=F+r+2) (by dsimp only [r];omega) (by dsimp only [r];omega)
    (by rw [hb];exact (SuffixCap.entry_rows k b).1) rfl
  have lift:=countHop (Cursor.q k 64) (Cursor.q k (countBase b)) p (p+1) T none .right
    (by simp only [Cursor.q,smallMod k 64 (by omega)];omega)
    (P:=F+r+2) (by dsimp only [r];omega) (by dsimp only [r];omega)
    (by rw [hb];exact (SuffixCap.entry_rows k b).2) rfl
  have rest:=countIteration k T p S z n Q F r fr r 0 (by dsimp only [r];omega) (by omega) b (by simpa using hb)
  have zeroImage : SuffixCap.Target.image T F 0=T := by
    funext i
    simp [SuffixCap.Target.image,show ¬(F+2 ≤ i ∧ i < F+0+2) by omega]
  simp only [Nat.add_zero,zeroImage] at rest
  have path:=pathAppend (pathAppend same lift) rest
  have time : 1+1+r*(2*(F-p)+6)=2+(S-p)*(2*(F-p)+6):=rfl
  rw [time] at path
  exact pathHeads path fit (by change p < tapeLength N B;omega)
end IngressAllocation
