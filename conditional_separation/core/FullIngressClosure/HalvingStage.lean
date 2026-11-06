import Complexity.PrivateInterfaceLookupResolvedHalving
import FullIngressClosure.HalfDriver
import FullIngressClosure.PaintCertificates
namespace FullIngressClosure
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier.ContractExpansion Lean Elab Command
set_option maxRecDepth 10000
run_cmd do
  let checked ← PartAPrivateHalving.bindings `FullIngressClosure.HalvingStage
  let env ← getEnv
  for (n,aliasName) in checked do
    let some ci := env.find? n | throwError "validated halving identity disappeared"
    logInfo m!"private-term|{n}|type={ci.type}"
    modifyScope fun st => {st with openDecls:=.explicit (Name.str .anonymous aliasName) n :: st.openDecls}
private theorem painted_bank (T : Nat → Option Bool) (D : Nat → Nat) (a w : Nat) (value : Bool)
    (len : D (a+1)=D a+w+1) :
    painted T (D a) w value=setBank T D a (if value then w else 0) := by
  funext i
  dsimp only [painted,setBank]
  by_cases inside : D a < i ∧ i < D (a+1)
  · rw [if_pos inside,if_pos (by omega)]
    cases value
    · change some false=some (decide (i-D a ≤ 0))
      rw [decide_eq_false (by omega)]
    · change some true=some (decide (i-D a ≤ w))
      rw [decide_eq_true (by omega)]
  · rw [if_neg inside,if_neg (by omega)]
private theorem full_bitLength {k lo P D} (n r : Nat) (T : Nat → Option Bool) (grid : Grid D T)
    (lenA : D 2=D 1+n+1) (lenB : D 9=D 8+n+1) (lenC : D 3=D 2+r+1)
    (lower : lo ≤ D 0) (upper : D 12 ≤ P) (fits : bitLength n ≤ r)
    (emptyB : BankUnary D T 8 0) (emptyC : BankUnary D T 2 0) :
    ∃ t,t ≤ 1024*(n+1)*(P+16) ∧ PPath k lo P t
      (pNode (st k 1176) (D 1) T)
      (pNode (st k 1311) (D 1) (halfPhase T D true 0 (bitLength n))) := by
  have low:=lower.trans (gridMono grid 0 1 (by decide) (by decide))
  have high : D 1+n+1 ≤ P:=by rw [← lenA]; exact (gridMono grid 2 12 (by decide) le_rfl).trans upper
  have paintPath:=paint (k:=k) (lo:=lo) (P:=P) (paint1176 k) T (D 1) n low high
    (gridBlank grid 1 (by decide)) (by rw [← lenA]; exact gridBlank grid 2 (by decide))
    (by intro i il iu; exact gridCells grid 1 i (by decide) il (by rwa [lenA]))
  rw [painted_bank T D 1 n true lenA] at paintPath
  have grid1:=bankGrid grid 1 n (by decide)
  have jump:=pKeep (k:=k) (lo:=lo) (hi:=P) (st k 1179) (st k 1180) (D 1) (D 1) (setBank T D 1 n) .stay
    ⟨(safeNative k 1179 (by decide)).1,(safeNative k 1179 (by decide)).2.1⟩
    (safeNative k 1179 (by decide)).2.2 ⟨low,by omega⟩ ⟨low,by omega⟩
    (by rw [gridBlank grid1 1 (by decide),stSmall k 1179 (by decide),nativeRow]; rfl) rfl
  have B : BankUnary D (setBank T D 1 n) 8 0:=
    bankOther grid 8 1 0 n (by decide) (by decide) (by decide) emptyB
  have C : BankUnary D (setBank T D 1 n) 2 0:=
    bankOther grid 2 1 0 n (by decide) (by decide) (by decide) emptyC
  have C' : BankUnary D (setBank (setBank T D 1 n) D 8 0) 2 0:=
    bankOther grid1 2 8 0 0 (by decide) (by decide) (by decide) C
  have eq : halfPhase T D true n 0=setBank T D 1 n := by
    change setBank (setBank (setBank T D 1 n) D 8 0) D 2 0=setBank T D 1 n
    rw [bankOriginal C',bankOriginal B]
  obtain ⟨t,price,path⟩:=alternatingHalving (k:=k) n r lenA lenB lenC lower upper T grid n true 0 le_rfl (by omega)
  rw [eq] at path
  simp only [Nat.zero_add] at path
  refine ⟨_,?_,pAppend paintPath (pAppend jump path)⟩
  have bound : n ≤ P:=by omega
  nlinarith only [price,bound]
end FullIngressClosure
