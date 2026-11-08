import VirtualFinalClosure.LengthGrowFrame
import VirtualFinalClosure.GrowOnce
namespace VirtualFinalClosure.RawLengthGrow
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier.ContractExpansion PairEncoding Lean Elab Command
set_option autoImplicit false
run_cmd do
  let env ← getEnv
  for (mod,ns,key,aliasName,kind) in [
      ("VirtualFinalClosure.LengthConnected","VirtualFinalClosure.LengthConnected","raw_marked_length","rawMarked",(1:Nat)),
      ("VirtualFinalClosure.GrowOnce","VirtualFinalClosure.GrowOnce","grow_once","growOnce",1),
      ("VirtualFinalClosure.LengthFrame","VirtualFinalClosure.LengthFrame","actual_length_frame","actualFrame",1),
      ("VirtualFinalClosure.LengthBanks","VirtualFinalClosure.LengthBanks","actual_bank1","actualBank1",1),
      ("AllArityWorkspace.Runtime","AllArityWorkspace","actual_cells","actualCells",1),
      ("AllArityWorkspace.Runtime","AllArityWorkspace","Cells.arena","arenaCell",1),
      ("VirtualFinalClosure.LengthGrowFrame","VirtualFinalClosure.LengthGrowFrame","banks","banks",1),
      ("VirtualFinalClosure.LengthGrowFrame","VirtualFinalClosure.LengthGrowFrame","marked_banks","markedBanks",1),
      ("VirtualFinalClosure.Geometry","VirtualFinalClosure.Geometry","protected_frame","protect",1),
      ("VirtualFinalClosure.Geometry","VirtualFinalClosure.Geometry","actual_width","actualWidth",1),
      ("VirtualFinalClosure.SourceLoop","VirtualFinalClosure.SourceLoop","protected_image","protectedImage",1),
      ("VirtualFinalClosure.MarkerImages","VirtualFinalClosure.MarkerImages","image","image",0),
      ("VirtualFinalClosure.MarkerImages","VirtualFinalClosure.MarkerImages","unary","unary",0),
      ("VirtualFinalClosure.MarkerImages","VirtualFinalClosure.MarkerImages","lifted","lifted",0),
      ("VirtualFinalClosure.MarkerState","VirtualFinalClosure.MarkerState","modes","modes",0),
      ("VirtualFinalClosure.MarkerState","VirtualFinalClosure.MarkerState","modes_bound","modeBound",1),
      ("VirtualFinalClosure.LengthBanks","VirtualFinalClosure.LengthBanks","masked","masked",0),
      ("VirtualFinalClosure.LengthBanks","VirtualFinalClosure.LengthBanks","masked_low","maskedLow",1),
      ("VirtualFinalClosure.LengthPrefix","VirtualFinalClosure.LengthPrefix","small_le_new","smallBudget",1),
      ("VirtualFinalClosure.GrowDouble","VirtualFinalClosure.GrowDouble","doubled","doubled",0),
      ("VirtualFinalClosure.PaintPath","VirtualFinalClosure.PaintPath","block","block",0),
      ("VirtualFinalClosure.ElasticMachine","VirtualFinalClosure.Elastic","table","tableControl",0),
      ("VirtualFinalClosure.ElasticMachine","VirtualFinalClosure.Elastic","changeMeta","changeMeta",0),
      ("VirtualFinalClosure.ElasticMachine","VirtualFinalClosure.Elastic","seen","seen",0),
      ("VirtualFinalClosure.Native","VirtualFinalClosure.Native","changed_bound","metaBound",1),
      ("VirtualFinalClosure.Paths","VirtualFinalClosure.Paths","nc","nc",0),
      ("SmallIngress.Runtime","SmallIngress","Path.execute","execute",1),
      ("VirtualFinalClosure.PathTrace","VirtualFinalClosure.PathTrace","through","through",1)] do
    let found:=env.constants.toList.filter fun (name,_)=>name.toString.startsWith ("_private."++mod++".") && name.toString.endsWith ("."++ns++"."++key)
    match found with
    | [(name,ci)]=>
      let actual : Nat:=match ci with | .defnInfo _=>0 | .thmInfo _=>1 | _=>9
      unless actual=kind do throwError "Wrong actual raw capacity-growth composition {name}"
      logInfo m!"private-term|{name}|kind={actual}|type={ci.type}"
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous aliasName) name::st.openDecls}
    | _=>throwError "Nonunique actual raw capacity-growth composition {mod}/{key}"
private theorem phase_price (R F S p r n e : Nat) (hn : n≤R) (hr : r≤R) (fence : F=3*R+2)
    (price : e≤(F-p+5)+(r*(4*r+7)+2*n+14*r+27)+(F-S+3)+1) : e≤128*(R+1)^2 := by
  have product:=Nat.mul_le_mul hr (show 4*r+7≤4*R+7 by omega)
  have a : F-p≤3*R+2 := by omega
  have b : F-S≤3*R+2 := by omega
  nlinarith only [price,product,a,b,hn,hr,Nat.zero_le R,Nat.zero_le (R^2)]
private theorem total_price (R t e : Nat) (ht : t≤8388608*(R+1)^3) (he : e≤128*(R+1)^2) :
    t+e≤16777216*(R+1)^3 := by
  nlinarith only [ht,he,Nat.zero_le R,Nat.zero_le (R^2),Nat.zero_le (R^3)]
private theorem raw_length_growth (k : Nat) {a m n consumed z : Nat} (x : Bitstring a) (w : Bitstring m)
    (canonical : m=a+1) (header : contentHeader? (Fin.append x w)=some (n,consumed))
    (tag : FixedContentTagGate.tagMatches (Fin.append x w)=true)
    (gamma : FixedContentGammaTerminator.gammaZeros? (Fin.append x w)=some z)
    (firstPhysical : z=0 ∨ 9+z < a+m) (cap : n < FixedRawLengthFence.capacity a m z)
    (rows : 2^n≤FixedRawLengthFence.fencePos (pairLength a m)-(a+m+z+n+3)-1)
    (physical : min (9+2*z+2^n) (a+m) < a+m)
    (shortage : a+m-min (9+2*z+2^n) (a+m) < bitLength n) :
    let S:=a+m;let R:=pairLength a m;let C:=FixedRawLengthFence.allocation R
    let B:=allocation k R;let L:=S+z+2;let F:=3*R+2;let r:=S-min (9+2*z+2^n) S
    let P:=F+5*r+n+7
    let U:=Body.extend (Body.installedTape (SmallIngress.prepared C x w z n) L n)
    let V:=Stream.Target.image U S z n (9+2*z) (2^n) (2^n) false
    let Y:=RuntimeBitLength.Target.fullImage
      (CappedWorkspace.Target.image (SuffixCap.Target.image V F r) L n F r) L n F r
    let T:=masked Y (tapeLength R C);let bits:=fun j=>(T (S-1-j)).getD false
    let c:=initialConfig (machine k) B (encodePair x w)
    S < Cursor.Target.M k n z ∧
    ∃ (g t d : Nat) (f : Fin 4) (hp : S-r < tapeLength R B),
      g+t+d≤8388608*(R+1)^3 ∧
      (machine k).run (g+t+d) c=
        ⟨nc k 40 (modes (8+f.val) bits r),⟨S-r,hp⟩,fun j=>image T F r S r j.val⟩ ∧
      ((∀ j,j < r → bits j=false) ∨
        ∃ (e : Nat) (hs : S < tapeLength R B),e≤128*(R+1)^2 ∧
          g+t+d+e≤16777216*(R+1)^3 ∧
          (∀ u,u≤g+t+d+e → ((machine k).run u c).head.val≤12*(R+1)^2) ∧
          (∀ u,u≤e → ((machine k).run (g+t+d+u) c).head.val≤P) ∧
          (machine k).run (g+t+d+e) c=
            ⟨control k (tableControl k 98)
                ⟨changeMeta 4 (modes (8+f.val) bits r),metaBound 4 _⟩,
              ⟨S,hs⟩,fun j=>block (doubled (image T F r S r) F r n) (L+1) n (some false) j.val⟩) := by
  intro S R C B L F r P U V Y T bits c
  let H:=L+n+1
  obtain ⟨virtual,g,t,d,f,hp,gPrice,tPrice,dPrice,totalPrice,prefixHeads,atMarker,markerHeads,mode,zero⟩:=
    rawMarked k x w canonical header tag gamma firstPhysical cap rows physical shortage
  refine ⟨virtual,g,t,d,f,hp,totalPrice,atMarker,?_⟩
  by_cases noTrue : seen (modes (8+f.val) bits r)=0
  · exact Or.inl (zero.mp noTrue)
  · right
    let md:=modes (8+f.val) bits r
    let A:=image T F r S r
    have observed : seen md=1 := by dsimp only [seen] at noTrue ⊢;omega
    have hm : md < 144 := modeBound (8+f.val) bits r (by have h:=f.isLt;omega)
    obtain ⟨fr,gap,positive,source,_b0,_d1,cells⟩:=actualFrame x w gamma cap rows physical
    obtain ⟨oldFit,_d2,_b1⟩:=actualBank1 x w gamma cap rows
    change P < tapeLength R C at oldFit
    have fit : P < tapeLength R B := by
      have grow:=smallBudget k R
      simp only [tapeLength] at oldFit ⊢
      omega
    have same (i : Nat) (hi : i≤P) : T i=Y i := maskedLow Y (tapeLength R C) i (lt_of_le_of_lt hi oldFit)
    have smallS : S < P := by dsimp only [S,R,F,P,pairLength];omega
    have sourceF : S ≤ F := by dsimp only [S,R,F,pairLength];omega
    have framedT:=protect fr (by intro i _lo hi;exact same i (by dsimp only [P];omega))
    have framedA:=protect framedT (by intro i lo hi;exact protectedImage T F r S r i source lo hi)
    obtain ⟨actual,_short,fresh⟩:=actualCells x w gamma cap rows
    change ∀ i : Fin (tapeLength R C),F < i.val → V i.val=none at fresh
    have room : L+n+1 < F := by
      have arena:=arenaCell actual
      change S+z+n+3+2^n < F at arena
      dsimp only [L]
      have paid:=Nat.two_pow_pos n
      omega
    have zeroV : ∀ i,F < i → i≤P → V i=none := by
      intro i lo hi
      exact fresh ⟨i,lt_of_le_of_lt hi oldFit⟩ lo
    obtain ⟨delimiters,digits⟩:=banks V L n F r room zeroV
    have indexFit (j : Nat) (hj : j≤6) : SerializedBody.delimiter F r n j≤P := by
      interval_cases j <;> dsimp only [SerializedBody.delimiter,P] <;> omega
    have blankT : ∀ j,j≤6 → T (SerializedBody.delimiter F r n j)=none := by
      intro j hj
      rw [same _ (indexFit j hj)]
      exact delimiters j hj
    have cellsT : ∀ j,j<6 → ∀ i,SerializedBody.delimiter F r n j < i →
        i < SerializedBody.delimiter F r n (j+1) → ∃ b,T i=some b := by
      intro j hj i lo hi
      rw [same i (by have h:=indexFit (j+1) (by omega);omega)]
      exact digits j hj i lo hi
    obtain ⟨blankA,cellsA⟩:=markedBanks T F r S n sourceF blankT cellsT
    have hole : A (S-r)=none := by
      dsimp only [A,image,unary,lifted]
      rw [if_neg (by omega),if_pos ⟨positive,rfl⟩]
    have suffix : ∀ i,S-r < i → i < S → ∃ b,A i=some b := by
      intro i lo hi
      have ji : S-1-i < r := by omega
      obtain ⟨b,cell⟩:=cells (S-1-i) ji
      have address : S-1-(S-1-i)=i := by omega
      refine ⟨b,?_⟩
      dsimp only [A,image,unary,lifted]
      rw [if_neg (by omega),if_neg (by omega),same i (by omega)]
      exact (congrArg Y address.symm).trans cell
    obtain ⟨e,price,path,_phase,_flag⟩:=growOnce k P md S L H (2^n) F (S-r) r A
      hm observed framedA gap (by omega) hole suffix positive
      (by dsimp only [P,H];omega)
      (by simpa only [show H-L-1=n by dsimp only [H];omega] using blankA)
      (by simpa only [show H-L-1=n by dsimp only [H];omega] using cellsA)
    rw [show H-L-1=n by dsimp only [H];omega] at price path
    have pair : S≤R := by dsimp only [S,R,pairLength];omega
    have nr : n≤R := actualWidth R S z n pair physical
    have rr : r≤R := (Nat.sub_le _ _).trans pair
    have ep : e≤128*(R+1)^2 := phase_price R F S (S-r) r n e nr rr rfl price
    have envelope : P≤12*(R+1)^2 := by
      dsimp only [P,F]
      nlinarith only [nr,rr,Nat.zero_le R,Nat.zero_le (R^2)]
    have run:=execute (N:=R) (B:=B) path fit
    have heads:=through (N:=R) (B:=B) path fit
    refine ⟨e,lt_trans smallS fit,ep,total_price R (g+t+d) e totalPrice ep,?_,?_,?_⟩
    · intro u hu
      by_cases before : u≤g+t+d
      · exact prefixHeads u before
      · rw [show u=(g+t+d)+(u-(g+t+d)) by omega,UniformTM.run_add,atMarker]
        exact (heads (u-(g+t+d)) (by omega)).trans envelope
    · intro u hu
      rw [UniformTM.run_add,atMarker]
      exact heads u hu
    · rw [UniformTM.run_add,atMarker]
      exact run
#print axioms phase_price
#print axioms total_price
#print axioms raw_length_growth
end VirtualFinalClosure.RawLengthGrow
