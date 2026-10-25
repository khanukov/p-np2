import RawCallerClosure.Images
namespace RawCallerClosure
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier Pnp4.Frontier.ContractExpansion
open Pnp4.AlgorithmsToLowerBounds PairEncoding Lean Elab Command
run_cmd do
  let e←getEnv
  for (owner,ns,leaf,aliasName,kind) in [
    (`PhysicalCallerClosure.AllRows,`PhysicalCallerClosure,"Layout","Layout","inductive"),
    (`PhysicalCallerClosure.AllRows,`PhysicalCallerClosure,"Layout.mk","layoutMk","constructor"),
    (`TotalIngressClosure.NormalFrame,`TotalIngressClosure,"normal_frame","normalFrame","theorem"),
    (`RawCallerClosure.Images,`RawCallerClosure,"ready","ready","definition"),
    (`RawCallerClosure.Images,`RawCallerClosure,"table","table","definition"),
    (`RawCallerClosure.Images,`RawCallerClosure,"source_all","sourceAll","theorem"),
    (`RawCallerClosure.Images,`RawCallerClosure,"gamma_holes","gammaHoles","theorem"),
    (`RawCallerClosure.Images,`RawCallerClosure,"tail_all","tailAll","theorem"),
    (`RawCallerClosure.Arithmetic,`RawCallerClosure,"large_budget","largeBudget","theorem"),
    (`RawCallerClosure.Arithmetic,`RawCallerClosure,"metadata_room","metadataRoom","theorem"),
    (`RawCallerClosure.Arithmetic,`RawCallerClosure,"window_positive","windowPositive","theorem")] do
    let found:=e.constants.toList.filter fun (n,_)=>n.toString.startsWith ("_private."++owner.toString++".") && n.toString.endsWith ("."++ns.toString++"."++leaf)
    let [(n,ci)]:=found | throwError "Nonunique physical frame {owner}/{leaf}"
    let actual:=match ci with|.defnInfo _=>"definition"|.thmInfo _=>"theorem"|.inductInfo _=>"inductive"|.ctorInfo _=>"constructor"|_=>"other"
    unless actual==kind do throwError "Wrong physical frame kind"
    let some i:=e.getModuleIdxFor? n | throwError "Missing owner"
    unless i.toNat<e.header.moduleNames.size && e.header.moduleNames[i]! == owner do throwError "Wrong physical frame owner"
    logInfo m!"ordinary-frame|{n}|{kind}|{ci.type}"
    modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous aliasName) n::st.openDecls}
private theorem metadata_after (F r n i : Nat) (lo:SerializedBody.delimiter F r n 12 < i) :
    F+5*r+n+7 < i := by
  change F+13*r+2*n+16 < i at lo
  omega
private theorem normal_layout (k : Nat) {a m n z : Nat} (x : Bitstring a) (w : Bitstring m)
    (gamma:FixedContentGammaTerminator.gammaZeros? (Fin.append x w)=some z)
    (header:contentHeader? (Fin.append x w)=some (n,2*z+1))
    (capacity:n < FixedRawLengthFence.capacity a m z)
    (arena:a+m+z+n+3+2^n < FixedRawLengthFence.fencePos (pairLength a m))
    (physical:min (9+2*z+2^n) (a+m) < a+m)
    (ellFits:bitLength n ≤ a+m-min (9+2*z+2^n) (a+m))
    (wFits:Cursor.Target.W k n ≤ a+m-min (9+2*z+2^n) (a+m)) :
    let R:=pairLength a m;let S:=a+m;let p:=min (9+2*z+2^n) S;let r:=S-p
    let F:=FixedRawLengthFence.fencePos R;let B0:=FixedRawLengthFence.allocation R
    let I:=ready (table B0 x w z n) (S+z+2) n F r (n^k+k) (Cursor.Target.W k n)
    Layout (allocation k R) R S z n r (n^k+k) (Cursor.Target.W k n) (Cursor.Target.M k n z)
      (9+2*z) (2^n) (Fin.append x w) I := by
  intro R S p r F B0 I
  obtain ⟨base,mExact,_modeEq⟩:=normalFrame k x w gamma capacity (by omega) physical ellFits wFits
  change Cursor.Target.M k n z=p+bitLength (Cursor.Target.W k n)+Cursor.Target.W k n at mExact
  change p < S at physical
  rcases base with ⟨rp,sr,nr,_phys,gf,wf,ef,qp,paid,source,eof,reg,left,right,beta,marks,gap,fence,
    _delim,_b0,_b1,_b2,_b34,_b5,_fresh⟩
  change 1 ≤ R at rp
  change S ≤ R at sr
  change n ≤ R at nr
  change n^k+k ≤ r at gf
  change Cursor.Target.W k n ≤ r at wf
  change bitLength n ≤ r at ef
  change S+z+n+3+2^n < F at paid
  have rr:r≤R:=(Nat.sub_le S p).trans sr
  have fit0:SerializedBody.delimiter F r n 12+6<tapeLength R B0:=metadataRoom R r n rp rr nr
  have budget:B0≤allocation k R:=largeBudget k R
  have fit:SerializedBody.delimiter F r n 12+6<tapeLength R (allocation k R):=by
    unfold tapeLength at fit0 ⊢
    omega
  have pEq:p=9+2*z+2^n:=Nat.min_eq_left (by omega)
  have before:9+2*z<S:=by rw [pEq] at physical;have power:=Nat.two_pow_pos n;omega
  have holes:=gammaHoles x w (n^k+k) (Cursor.Target.W k n) r gamma header before (by omega)
  have hH:S+z+n+3<tapeLength R (allocation k R):=by
    have base: S+z+n+3 < SerializedBody.delimiter F r n 12+6 := by
      change S+z+n+3<F+13*r+2*n+16+6
      omega
    omega
  refine layoutMk rp (Nat.sub_le S p) sr gf (windowPositive k n) wf ef ?_ (by omega) (by omega) ?_
    qp paid holes.1 holes.2 ?_ eof reg left right ?_ marks gap fence ?_ fit hH
  · have mp:p≤Cursor.Target.M k n z:=by omega
    change S-min (Cursor.Target.M k n z) S≤S-p
    omega
  · rw [pEq] at mExact
    have wp:=windowPositive k n
    omega
  · intro i lo hi
    exact sourceAll x w (n^k+k) (Cursor.Target.W k n) r gamma capacity (by omega) i lo hi
  · intro j
    simpa only [show S+z+n+3-1-j.val=S+z+n+2-j.val by omega] using beta j
  · intro i lo _hi
    exact tailAll x w (n^k+k) (Cursor.Target.W k n) r gamma capacity arena i (metadata_after F r n i lo)
end RawCallerClosure
