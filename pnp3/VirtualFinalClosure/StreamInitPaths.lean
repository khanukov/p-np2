import VirtualFinalClosure.StreamActivePaths
import Stream.Kernel
namespace VirtualFinalClosure.StreamInitPaths
open Pnp3.Complexity.Uniform.V1 Lean Elab Command
set_option autoImplicit false
run_cmd do
  let env ← getEnv
  for (mod,ns,key,aliasName,kind) in [
      ("VirtualFinalClosure.StreamActivePaths","VirtualFinalClosure.StreamActivePaths","q","q",(0:Nat)),
      ("VirtualFinalClosure.StreamActivePaths","VirtualFinalClosure.StreamActivePaths","pure_row","pureRow",1),
      ("Stream.Kernel","Stream","carryCost","carryCost",0),
      ("Stream.Kernel","Stream","modeOf","modeOf",0),
      ("SmallIngress.Runtime","SmallIngress","Path","GPath",2),
      ("SmallIngress.Runtime","SmallIngress","Path.nil","nilPath",3),
      ("SmallIngress.Runtime","SmallIngress","Path.append","joinPath",1),
      ("SmallIngress.Runtime","SmallIngress","Node.mk","node",3),
      ("SmallIngress.Runtime","SmallIngress","put","put",0),
      ("SmallIngress.Runtime","SmallIngress","hop","hop",1),
      ("SmallIngress.Runtime","SmallIngress","keep","keep",1),
      ("SmallIngress.Runtime","SmallIngress","sweepR","sweepR",1),
      ("SmallIngress.Runtime","SmallIngress","sweepL","sweepL",1),
      ("SmallIngress.Runtime","SmallIngress","dest","dest",0) ] do
    let found:=env.constants.toList.filter fun (name,_)=>name.toString.startsWith ("_private."++mod++".") && name.toString.endsWith ("."++ns++"."++key)
    match found with
    | [(name,ci)]=>
      let actual : Nat:=match ci with | .defnInfo _=>0 | .thmInfo _=>1 | .inductInfo _=>2 | .ctorInfo _=>3 | _=>9
      unless actual=kind do throwError "Wrong SAME counter/source phase interface {name}"
      logInfo m!"private-term|{name}|kind={actual}|type={ci.type}"
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous aliasName) name::st.openDecls}
    | _=>throwError "Nonunique SAME counter/source phase interface {mod}/{key}"
private theorem append {M : UniformTM} {P t u : Nat} {c d e}
    (h : GPath (M:=M) P t c d) (g : GPath (M:=M) P u d e) : GPath (M:=M) P (t+u) c e:=joinPath h g
private theorem put_same (T : Nat → Option Bool) (h : Nat) : put T h (T h)=T:=by
  funext i;by_cases hi : i=h <;> simp [put,hi]
private theorem seek_path (k : Nat) (f : Fin 4) (T : Nat → Option Bool) (p S z n : Nat) (hp : 2 ≤ p) (hps : p ≤ S) (hole : T (p-2)=none) (marker : T (p-1)=some true)
    (source : ∀ i, p ≤ i → i < S → ∃ b, T i=some b) (eof : T S=none) (reg : ∀ i, S < i → i < S+z+2 → T i=some false) (sep : T (S+z+2)=none)
    (assn : ∀ i, S+z+2 < i → i < S+z+n+3 → ∃ b, T i=some b) (right : T (S+z+n+3)=none) :
    GPath (S+z+n+3) (n+z+(S-p)+7) (node ((q k f) 2) (S+z+n+3) (T)) (node ((q k f) 7) (p) (T)) := by
  let P := S+z+n+3
  have a := keep ((q k f) 2) ((q k f) 3) P (P-1) T .left (P := P) le_rfl (by omega) (by rw [right];apply pureRow <;> decide) rfl
  have b := sweepL ((q k f) 3) T (S+z+2) n (P := P) (by dsimp [P]; omega) (by
    intro i hl hu; obtain ⟨v,hv⟩ := assn i hl (by omega)
    rw [hv]; cases v <;> apply pureRow <;> decide)
  have ab : P-1=S+z+2+n := by dsimp [P]; omega
  rw [ab] at a
  have c := keep ((q k f) 3) ((q k f) 4) (S+z+2) (S+z+1) T .left (P := P) (by dsimp [P]; omega) (by dsimp [P]; omega) (by rw [sep];apply pureRow <;> decide) (by simp [dest])
  have d := sweepL ((q k f) 4) T S (z+1) (P := P) (by dsimp [P]; omega) (by
    intro i hl hu; rw [reg i hl (by omega)];apply pureRow <;> decide)
  have e := keep ((q k f) 4) ((q k f) 5) S (S-1) T .left (P := P) (by dsimp [P]; omega) (by dsimp [P]; omega) (by rw [eof];apply pureRow <;> decide) rfl
  have backSource := sweepL ((q k f) 5) T (p-2) (S-p+1) (P := P) (by dsimp [P]; omega) (by
    intro i hl hu
    have occ : ∃ b, T i=some b := by
      by_cases hi : i=p-1
      · exact ⟨true,hi ▸ marker⟩
      · exact source i (by omega) (by omega)
    obtain ⟨v,hv⟩ := occ; rw [hv]; cases v <;> apply pureRow <;> decide)
  have ef : p-2+(S-p+1)=S-1 := by omega
  rw [ef] at backSource
  have g := keep ((q k f) 5) ((q k f) 6) (p-2) (p-1) T .right (P := P) (by dsimp [P]; omega) (by dsimp [P]; omega) (by rw [hole];apply pureRow <;> decide) (by simp [dest]; omega)
  have h := keep ((q k f) 6) ((q k f) 7) (p-1) p T .right (P := P) (by dsimp [P]; omega) (by dsimp [P]; omega) (by rw [marker];apply pureRow <;> decide) (by simp [dest]; omega)
  have eqD : S+(z+1)=S+z+1 := by omega
  rw [eqD] at d
  convert ((((((a.append b).append c).append d).append e).append backSource).append g).append h using 1; omega
private theorem seed_path (k : Nat) (f : Fin 4) (T : Nat → Option Bool) (h n : Nat) (marks : ∀ i, h ≤ i → i < h+n → T i=some true) (endBlank : T (h+n)=none) :
    GPath (h+n) (n+1) (node ((q k f) 1) (h) (T)) (node ((q k f) 2) (h+n) (Body.clear T h n)) := by
  induction n generalizing T h with
  | zero =>
    have one := hop ((q k f) 1) ((q k f) 2) h h T none .stay (P := h) le_rfl le_rfl (by rw [show T h=none by simpa using endBlank];apply pureRow <;> decide) rfl
    have hb : T h=none := by simpa using endBlank
    rw [← hb,put_same] at one
    have hz : Body.clear T h 0=T := by funext i; simp [Body.clear]
    simpa [hz] using one
  | succ n ih =>
    have hb := marks h le_rfl (by omega)
    let U := put T h (some false)
    have one := hop ((q k f) 1) ((q k f) 1) h (h+1) T (some false) .right (P := h+(n+1)) (by omega) (by omega) (by rw [hb];apply pureRow <;> decide) rfl
    have rest := ih U (h+1) (by intro i h1 h2; dsimp [U]; rw [put,if_neg (by omega)]; exact marks i (by omega) (by omega))
      (by dsimp [U]; rw [put,if_neg (by omega)]; simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using endBlank)
    have eqP : h+1+n=h+(n+1) := by omega
    rw [eqP] at rest
    have clearstep : Body.clear (put T h (some false)) (h+1) n = Body.clear T h (n+1) := Body.clear_step T h n
    simpa only [U,clearstep,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using one.append rest
/-- Installation consumes actual unary marks, without assuming precleared scratch. -/
private theorem install_path (k : Nat) (f : Fin 4) (T : Nat → Option Bool) (left n : Nat) (startBlank : T left=none) (marks : ∀ i, left < i → i < left+n+1 → T i=some true)
    (endBlank : T (left+n+1)=none) :
    GPath (left+n+1) (n+2) (node ((q k f) 0) left T)
      (node ((q k f) 2) (left+n+1) (Body.clear T (left+1) n)) := by
  have one := hop ((q k f) 0) ((q k f) 1) left (left+1) T none .right (P := left+n+1) (by omega) (by omega) (by rw [startBlank];apply pureRow <;> decide) rfl
  rw [← startBlank,put_same] at one
  have rest := (seed_path k f) T (left+1) n (by intro i h1 h2; exact marks i (by omega) (by omega)) (by simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using endBlank)
  have eqP : left+1+n=left+n+1 := by omega
  rw [eqP] at rest
  simpa [Nat.add_comm,Nat.add_left_comm,Nat.add_assoc] using one.append rest
#print axioms append
#print axioms put_same
#print axioms seek_path
#print axioms seed_path
#print axioms install_path
end VirtualFinalClosure.StreamInitPaths
