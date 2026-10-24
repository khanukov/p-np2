import VirtualFinalClosure.RawPaidCounted
import VirtualFinalClosure.Recompute
import VirtualFinalClosure.Geometry
namespace VirtualFinalClosure.RawPaidLength
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier.ContractExpansion PairEncoding Lean Elab Command
set_option autoImplicit false
run_cmd do
  let env ← getEnv
  let specs:=[
      ("VirtualFinalClosure.RawPaidCounted","VirtualFinalClosure.RawPaidCounted","raw_counted","rawCounted",(1:Nat)),
      ("VirtualFinalClosure.Recompute","VirtualFinalClosure.Recompute","prepared","recompute",1),
      ("VirtualFinalClosure.SourceWalk","VirtualFinalClosure.SourceWalk","Frame.mk","frameMk",3),
      ("VirtualFinalClosure.Geometry","VirtualFinalClosure.Geometry","protected_frame","protect",1),
      ("VirtualFinalClosure.Geometry","VirtualFinalClosure.Geometry","actual_width","actualWidth",1),
      ("VirtualFinalClosure.LengthPrefix","VirtualFinalClosure.LengthPrefix","small_le_new","smallBudget",1),
      ("AllArityWorkspace.Runtime","AllArityWorkspace","actual_cells","actualCells",1),
      ("VirtualFinalClosure.StreamActiveOrbit","VirtualFinalClosure.StreamActiveOrbit","bits","bits",0),
      ("VirtualFinalClosure.TableFlagMeaning","VirtualFinalClosure.TableFlagMeaning","folded","folded",0),
      ("VirtualFinalClosure.ElasticMachine","VirtualFinalClosure.Elastic","table","tableControl",0)]
  let fields:=["arena","source","eof","reg","sep","assn","right","marks","gap","fence"]
  let specs:=specs++fields.map (fun field=>("AllArityWorkspace.Runtime","AllArityWorkspace","Cells."++field,"cell_"++field,1))
  for (mod,ns,key,aliasName,kind) in specs do
    let found:=env.constants.toList.filter fun (name,_)=>name.toString.startsWith ("_private."++mod++".") && name.toString.endsWith ("."++ns++"."++key)
    match found with
    | [(name,ci)]=>
      let actual : Nat:=match ci with | .defnInfo _=>0 | .thmInfo _=>1 | .ctorInfo _=>3 | _=>9
      unless actual=kind do throwError "Wrong raw computed-length flag term {name}"
      logInfo m!"private-term|{name}|kind={actual}|type={ci.type}"
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous aliasName) name::st.openDecls}
    | _=>throwError "Nonunique raw computed-length flag term {mod}/{key}"
private theorem low (V : Nat → Option Bool) (F r i : Nat) (hi : i ≤ F+1) :
    SuffixCap.Target.image V F r i=V i:=by
  dsimp only [SuffixCap.Target.image]
  rw [if_neg (by omega)]
private theorem assn_false (U : Nat → Option Bool) (S z n A i : Nat)
    (lo : S+z+2 < i) (hi : i < S+z+n+3) :
    Stream.Target.image U S z n A (2^n) (2^n) false i=some false:=by
  dsimp only [Stream.Target.image]
  rw [if_pos (by omega),CappedWorkspace.overflow_bits]
  simp only [List.getElem!_eq_getElem?_getD,List.getElem?_replicate]
  split <;> rfl
private theorem price (R n r t d : Nat) (nr : n ≤ R) (rr : r ≤ R)
    (tp : t ≤ 8192*(R+1)^2) (dp : d ≤ 4096*(n+r+1)*(3*R+2+5*r+n+9)) :
    t+d ≤ 4194304*(R+1)^3:=by
  have prod:=Nat.mul_le_mul (Nat.mul_le_mul_left 4096 (show n+r+1 ≤ 2*(R+1) by omega))
    (show 3*R+2+5*r+n+9 ≤ 11*(R+1) by omega)
  nlinarith only [tp,dp,prod,Nat.zero_le R,Nat.zero_le (R^2),Nat.zero_le (R^3)]
/-- The complete physically paid flag survives the SAME suffix count,
workspace setup and entire alternating bitLength computation. All three real
length outcomes are retained; no fit/success premise or host observation fold
is supplied to this raw execution theorem. -/
private theorem raw_length (k : Nat) {a m n consumed z : Nat} (x : Bitstring a) (w : Bitstring m)
    (canonical : m=a+1) (header : contentHeader? (Fin.append x w)=some (n,consumed))
    (tag : FixedContentTagGate.tagMatches (Fin.append x w)=true)
    (gamma : FixedContentGammaTerminator.gammaZeros? (Fin.append x w)=some z)
    (firstPhysical : z=0 ∨ 9+z < a+m) (cap : n < FixedRawLengthFence.capacity a m z)
    (rows : 2^n ≤ FixedRawLengthFence.fencePos (pairLength a m)-(a+m+z+n+3)-1)
    (physical : min (9+2*z+2^n) (a+m) < a+m) :
    let S:=a+m;let R:=pairLength a m;let C:=FixedRawLengthFence.allocation R
    let B:=allocation k R;let F:=3*R+2;let A:=9+2*z;let Q:=2^n
    let L:=S+z+2;let p:=Stream.Target.cursor A S Q;let r:=S-p
    let U:=Body.extend (Body.installedTape (SmallIngress.prepared C x w z n) L n)
    let V:=Stream.Target.image U S z n A Q Q false
    let X:=CappedWorkspace.Target.image (SuffixCap.Target.image V F r) L n F r
    let Y:=RuntimeBitLength.Target.fullImage X L n F r
    let f:=folded (bits U (min A S) S) Q
    let code:=if bitLength n ≤ r then 308 else if (r+1)%2=1 then 250 else 304
    let h:=if bitLength n ≤ r then L else F+r+n+3
    let c:=initialConfig (machine k) B (encodePair x w)
    ∃ (t : Nat) (hf : h < tapeLength R B),t ≤ 4194304*(R+1)^3 ∧
      (machine k).run t c=⟨control k (tableControl k code) ⟨8+f.val,by have h:=f.isLt;omega⟩,
        ⟨h,hf⟩,fun i=>Y i.val⟩ ∧
      (∀ u,u ≤ t → ((machine k).run u c).head.val ≤ 12*(R+1)^2) ∧
      (f.val%2=1 ↔ ∀ j : Fin Q,padRead (Fin.append x w) (A+j.val)=Nat.testBit j.val 0):=by
  intro S R C B F A Q L p r U V X Y f code h c
  obtain ⟨t,hS,tp,at98,oldHeads,meaning⟩:=rawCounted k x w canonical header tag gamma firstPhysical cap rows physical
  obtain ⟨cells,_short,fresh⟩:=actualCells x w gamma cap rows
  change ∀ i : Fin (tapeLength R C),F < i.val → V i.val=none at fresh
  obtain ⟨_tail,oldFit⟩:=Cursor.raw_tail_blank x w gamma cap rows
  change F+5*r+n+7 < tapeLength R C at oldFit
  have finite : F+5*r+n+7 < tapeLength R B:=by
    have budget:=smallBudget k R
    dsimp only [tapeLength] at oldFit ⊢
    omega
  have room : L+n+1+Q < F:=by have h:=cell_arena cells;change S+z+n+3+Q < F at h;dsimp only [L];omega
  have below : L+n+1 < F:=by have paid:=Nat.two_pow_pos n;omega
  have d0 : V (F+1)=none:=fresh ⟨F+1,by omega⟩ (by change F < F+1;omega)
  have fr:=frameMk (T:=V) (S:=S) (L:=L) (H:=L+n+1) (Q:=Q) (F:=F)
    (by dsimp only [L];omega) (by omega) (Nat.two_pow_pos n) room
    (cell_eof cells) (cell_sep cells) (by
      have eq : L+n+1=S+z+n+3:=by dsimp only [L];omega
      rw [eq]
      exact cell_right cells)
    d0 (cell_fence cells) (by intro i lo hi;exact ⟨false,cell_reg cells i lo hi⟩)
    (by intro i lo hi;exact cell_assn cells i lo (by dsimp only [L] at hi;omega))
    (by intro i lo hi;exact cell_marks cells i (by dsimp only [L] at lo;omega) (by dsimp only [L] at hi;omega))
    (by intro i lo hi;exact cell_gap cells i (by dsimp only [L] at lo;omega) hi)
  let G:=SuffixCap.Target.image V F r
  have fg:=protect fr (by intro i _lo hi;exact low V F r i hi)
  have reg (i : Nat) (lo : S < i) (hi : i < L) : G i=some false:=
    (low V F r i (by omega)).trans (cell_reg cells i lo hi)
  have assn (i : Nat) (lo : L < i) (hi : i < L+n+1) : G i=some false:=by
    exact (low V F r i (by omega)).trans (assn_false U S z n A i lo (by dsimp only [L] at hi;omega))
  have b0 (i : Nat) (lo : F+1 < i) (hi : i < F+r+2) : G i=some true:=by
    dsimp only [G,SuffixCap.Target.image]
    rw [if_pos (by omega)]
  have blank (i : Nat) (lo : F+r+2 ≤  i) (hi : i ≤ F+5*r+n+7) : G i=none:=by
    dsimp only [G,SuffixCap.Target.image]
    rw [if_neg (by omega)]
    exact fresh ⟨i,lt_of_le_of_lt hi oldFit⟩ (by change F < i;omega)
  let md : Fin 144:=⟨8+f.val,by have h:=f.isLt;omega⟩
  obtain ⟨d,hf,dp,done,heads,_first,_trace⟩:=recompute k R B S L n Q F r G md
    (by dsimp only [r,p,Stream.Target.cursor];omega) fg reg assn b0 blank finite
  have sr : S ≤ R:=by dsimp only [S,R,pairLength];omega
  have nr : n ≤ R:=actualWidth R S z n sr physical
  have rr : r ≤ R:=(Nat.sub_le _ _).trans sr
  have envelope : F+5*r+n+7 ≤ 12*(R+1)^2:=by
    dsimp only [F]
    nlinarith only [nr,rr,Nat.zero_le R,Nat.zero_le (R^2)]
  refine ⟨t+d,hf,price R n r t d nr rr tp dp,?_,?_,meaning⟩
  · rw [UniformTM.run_add,at98]
    exact done
  · intro u hu
    by_cases early : u ≤ t
    · exact oldHeads u early
    · rw [show u=t+(u-t) by omega,UniformTM.run_add,at98]
      exact (heads (u-t) (by omega)).trans envelope
#print axioms low
#print axioms assn_false
#print axioms price
#print axioms raw_length
end VirtualFinalClosure.RawPaidLength
