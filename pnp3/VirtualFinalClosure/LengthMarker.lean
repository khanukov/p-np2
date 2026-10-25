import VirtualFinalClosure.LengthBanks
import VirtualFinalClosure.InterceptRows
namespace VirtualFinalClosure.LengthMarker
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier.ContractExpansion PairEncoding Lean Elab Command
set_option autoImplicit false
run_cmd do
  let env ← getEnv
  for (mod,ns,key,aliasName,kind) in [
      ("SmallIngress.Runtime","SmallIngress","Node.mk","node",(3:Nat)),
      ("SmallIngress.Runtime","SmallIngress","Path","GPath",2),
      ("SmallIngress.Runtime","SmallIngress","Path.append","joinPath",1),
      ("SmallIngress.Runtime","SmallIngress","keep","keep",1),
      ("VirtualFinalClosure.LengthFrame","VirtualFinalClosure.LengthFrame","actual_length_frame","actualFrame",1),
      ("VirtualFinalClosure.LengthBanks","VirtualFinalClosure.LengthBanks","actual_bank1","actualBank1",1),
      ("VirtualFinalClosure.LengthBanks","VirtualFinalClosure.LengthBanks","masked","masked",0),
      ("VirtualFinalClosure.LengthBanks","VirtualFinalClosure.LengthBanks","masked_low","maskedLow",1),
      ("VirtualFinalClosure.Geometry","VirtualFinalClosure.Geometry","protected_frame","protect",1),
      ("VirtualFinalClosure.CapEntry","VirtualFinalClosure.CapEntry","from_d2","routeD2",1),
      ("VirtualFinalClosure.InterceptRows","VirtualFinalClosure.InterceptRows","length_step","capRow",1),
      ("VirtualFinalClosure.ElasticMachine","VirtualFinalClosure.Elastic","table","tableControl",0),
      ("VirtualFinalClosure.ElasticMachine","VirtualFinalClosure.Elastic","mode","sourceMode",0),
      ("VirtualFinalClosure.ElasticMachine","VirtualFinalClosure.Elastic","seen","seen",0),
      ("VirtualFinalClosure.MarkerImages","VirtualFinalClosure.MarkerImages","image","image",0),
      ("VirtualFinalClosure.MarkerState","VirtualFinalClosure.MarkerState","modes","modes",0),
      ("VirtualFinalClosure.MarkerEnd","VirtualFinalClosure.MarkerEnd","marked_source","markSource",1),
      ("VirtualFinalClosure.Paths","VirtualFinalClosure.Paths","C","C",0),
      ("VirtualFinalClosure.Paths","VirtualFinalClosure.Paths","nc","nc",0)] do
    let found:=env.constants.toList.filter fun (n,_)=>n.toString.startsWith ("_private."++mod++".") && n.toString.endsWith ("."++ns++"."++key)
    match found with
    | [(name,ci)]=>
      let actual : Nat:=match ci with | .defnInfo _=>0 | .thmInfo _=>1 | .inductInfo _=>2 | .ctorInfo _=>3 | _=>9
      unless actual=kind do throwError "Wrong actual length marker interface {name}"
      logInfo m!"private-term|{name}|kind={actual}|type={ci.type}"
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous aliasName) name::st.openDecls}
    | _=>throwError "Nonunique actual length marker interface {mod}/{key}"
/-- Exact all-r execution following the actual original cap image; its backing
is the specified blank extension of that BEFORE-run image, never a chosen
post-run tape. Raw-origin composition is supplied by LengthConnected. -/
private theorem length_marker (k : Nat) {a m z n : Nat} (x : Bitstring a) (w : Bitstring m)
    (gamma : FixedContentGammaTerminator.gammaZeros? (Fin.append x w)=some z)
    (cap : n < FixedRawLengthFence.capacity a m z)
    (rows : 2^n≤FixedRawLengthFence.fencePos (pairLength a m)-(a+m+z+n+3)-1)
    (physical : min (9+2*z+2^n) (a+m) < a+m) (f : Fin 4) :
    let S:=a+m;let R:=pairLength a m;let B:=FixedRawLengthFence.allocation R
    let L:=S+z+2;let F:=3*R+2;let r:=S-min (9+2*z+2^n) S
    let P:=F+5*r+n+7
    let U:=Body.extend (Body.installedTape (SmallIngress.prepared B x w z n) L n)
    let V:=Stream.Target.image U S z n (9+2*z) (2^n) (2^n) false
    let Y:=RuntimeBitLength.Target.fullImage
      (CappedWorkspace.Target.image (SuffixCap.Target.image V F r) L n F r) L n F r
    let T:=masked Y (tapeLength R B)
    let bits:=fun j=>(T (S-1-j)).getD false
    ∃ d,d≤n+r+7+r*(2*r+2*(F-S)+14)+(F-S)+r+7 ∧
      GPath (M:=machine k) P d
        (node (control k (tableControl k (if (r+1)%2=1 then 250 else 304)) ⟨8+f.val,by have h:=f.isLt;omega⟩)
          (F+r+n+3) T)
        (C k 40 (modes (8+f.val) bits r) (S-r) (image T F r S r)) ∧
      sourceMode (modes (8+f.val) bits r)=(if bits (r-1) then 1 else 0) ∧
      (seen (modes (8+f.val) bits r)=0 ↔ ∀ j,j < r → bits j=false) := by
  intro S R B L F r P U V Y T bits
  let H:=L+n+1
  obtain ⟨fr,gap,positive,source,b0,d1,cells⟩:=actualFrame x w gamma cap rows physical
  obtain ⟨fit,d2,b1⟩:=actualBank1 x w gamma cap rows
  change P < tapeLength R B at fit
  have F1 : F+1≤P := by dsimp only [P];omega
  have smallS : S < P := by dsimp only [S,L,H,F,P,R,pairLength];omega
  have same (i : Nat) (hi : i≤P) : T i=Y i := maskedLow Y (tapeLength R B) i (lt_of_le_of_lt hi fit)
  have framed:=protect fr (by intro i _lo hi;exact same i (hi.trans F1))
  have bank : ∀ i,F+1 < i → i < F+r+2 → T i=some true := by
    intro i lo hi
    rw [same i (by dsimp only [P];omega)]
    exact b0 i lo hi
  have last : T (F+r+2)=none := by rw [same _ (by dsimp only [P];omega)];exact d1
  have bank1 : ∀ i,F+r+2 < i → i < F+r+n+3 → ∃ b,T i=some b := by
    intro i lo hi
    rw [same i (by dsimp only [P];omega)]
    exact b1 i lo hi
  have last2 : T (F+r+n+3)=none := by rw [same _ (by dsimp only [P];omega)];exact d2
  have selected : ∀ j,j < r → T (S-1-j)=some (bits j) := by
    intro j hj
    obtain ⟨b,cell⟩:=cells j hj
    have read : T (S-1-j)=some b := (same _ (by omega)).trans cell
    change T (S-1-j)=some ((T (S-1-j)).getD false)
    rw [read]
    rfl
  have hm : 8+f.val < 144 := by have h:=f.isLt;omega
  have eof : sourceMode (8+f.val)=2 := by fin_cases f <;> decide
  have unseen : seen (8+f.val)=0 := by fin_cases f <;> decide
  have mf:=framed
  obtain ⟨_sl,_lh,_paid,_room,_eof,_sep,_h,d0,_f,_reg,_assn,_marks,_gap⟩:=mf
  have entry:=keep (M:=machine k) (P:=P)
    (control k (tableControl k (if (r+1)%2=1 then 250 else 304)) ⟨8+f.val,by have h:=f.isLt;omega⟩)
    (nc k 0 (8+f.val)) (F+r+n+3) (F+r+n+3) T .stay
    (by dsimp only [P];omega) (by dsimp only [P];omega)
    (by rw [last2];exact capRow k (if (r+1)%2=1 then 250 else 304) f (by split <;> simp)) rfl
  have route:=routeD2 k P F r n f T (by dsimp only [P];omega) d0 last last2
    (by intro i lo hi;exact ⟨true,bank i lo hi⟩) bank1
  obtain ⟨d,price,marked,mode,zero⟩:=markSource k P (8+f.val) S L H (2^n) F r T bits hm eof unseen
    framed gap positive source (by dsimp only [P];omega) bank last selected
  have path:=joinPath (joinPath entry route) marked
  refine ⟨1+(n+r+6)+d,?_,path,mode,zero⟩
  omega
#print axioms length_marker
end VirtualFinalClosure.LengthMarker
