import Complexity.PrivateInterfaceLookupResolvedRuntime
import FullWeight.Body
namespace FullWeight
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier.ContractExpansion Lean Elab Tactic
set_option maxRecDepth 10000
run_cmd do
  let groups : List (String × List String) := [("Kernel",["Path.nil","Path","Path.append","K","Frame","D","atD"]),("Body",["N","J","V","incAdd","addCap","rowTac","put3true","decRest","put5false","put3true","route398","incRest","route406","incFour","route336","route344","route352","route360","decInner","route390","route416","route374","incOut","put4true","route380","incTemp","put5true","route386","route422","put3false","decOuter","put2false","route368","put2true","route330"])]
  let rows := groups.flatMap fun (m,keys) => keys.map fun s =>
    (Name.str `FullWeight m,(s.splitOn ".").foldl Name.str `FullWeight)
  let _ ← ofExcept (PartAPrivateRuntime.batch (← getEnv) rows)
  for (m,keys) in [("Kernel",["Path.nil","Path","Path.append","K","Frame","D","atD"]),("Body",["N","J","V","incAdd","addCap","rowTac","put3true","decRest","put5false","put3true","route398","incRest","route406","incFour","route336","route344","route352","route360","decInner","route390","route416","route374","incOut","put4true","route380","incTemp","put5true","route386","route422","put3false","decOuter","put2false","route368","put2true","route330"])] do
    for s in keys do
      let owner := Name.str `FullWeight m
      let user := (s.splitOn ".").foldl Name.str `FullWeight
      let n ← ofExcept (PartAPrivateRuntime.lookup (← getEnv) owner user)
      let ns := [n]
      logInfo m!"private-term|{ns.head!}"
      Lean.Elab.Command.modifyScope fun st => {st with openDecls := .explicit ((s.splitOn ".").foldl Name.str Name.anonymous) ns.head! :: st.openDecls}
private theorem addPrice (P r a s u : Nat) (ha : a ≤ r) (hr : r ≤ P) (hu : u ≤ 16*(s+1)*(P+1)) :
    2*a+3+1+u ≤ 16*(s+2)*(P+1) := by nlinarith only [ha,hr,hu]
private theorem capPrice (P r a s u : Nat) (ha : a ≤ r) (hr : r ≤ P) (hu : u ≤ 8*(P+1)) :
    2*a+3+u ≤ 16*(s+2)*(P+1) := by nlinarith only [ha,hr,hu,Nat.zero_le s,Nat.zero_le (s*P)]
private theorem copyBasePrice (P e u v w : Nat) (hu : u ≤ 8*(P+1)) (hv : v ≤ 64*(e+1)*(P+1)) (hw : w ≤ 8*(P+1)) :
    3+u+v+w ≤ 512*(0+1)*(P+1)+128*e*(P+1) := by nlinarith only [hu,hv,hw,Nat.zero_le e,Nat.zero_le P,Nat.zero_le (e*P)]
private theorem copyPrice (P r v c e u w z d : Nat) (hc : c ≤ r) (cap : v+1+e ≤ r) (hr : r ≤ P)
    (hu : u ≤ 8*(P+1)) (hw : w ≤ 8*(P+1)) (hz : z ≤ 8*(P+1)) (hd : d ≤ 512*(v+1)*(P+1)+128*(e+1)*(P+1)) :
    2*(v+1)+3+u+(2*c+3)+w+(2*e+3)+z+d ≤ 512*(v+2)*(P+1)+128*e*(P+1) := by nlinarith only [hc,cap,hr,hu,hw,hz,hd]
private theorem copyCapPrice (P r v c e u w : Nat) (hc : c ≤ r) (cap : v+1+e ≤ r) (hr : r ≤ P)
    (hu : u ≤ 8*(P+1)) (hw : w ≤ 8*(P+1)) :
    2*(v+1)+3+u+(2*c+3)+w ≤ 512*(v+2)*(P+1)+128*e*(P+1) := by
  nlinarith only [hc,cap,hr,hu,hw,Nat.zero_le P,Nat.zero_le v,Nat.zero_le e,Nat.zero_le (v*P),Nat.zero_le (e*P)]
private theorem multPrice (P r a b u v w : Nat) (ha : a+1 ≤ r) (hb : b ≤ r) (hr : r ≤ P)
    (hu : u ≤ 8*(P+1)) (hv : v ≤ 512*(b+1)*(P+1)) (hw : w ≤ 4096*(a+1)*(r+1)*(P+1)) :
    2*(a+1)+3+u+v+w ≤ 4096*(a+2)*(r+1)*(P+1) := by
  have mul:=Nat.mul_le_mul_right (P+1) hb
  nlinarith only [ha,hr,hu,hv,hw,mul,Nat.zero_le P,Nat.zero_le r,Nat.zero_le (r*P)]
private theorem tailPrice (P r k a u v w z : Nat) (ha : a ≤ r)
    (hu : u ≤ 16*(k+1)*(P+1)) (hv : v ≤ 8*(P+1)) (hw : w ≤ 80*(P+1)) (hz : z ≤ 4096*(a+1)*(r+1)*(P+1)) :
    1+u+v+w+z ≤ 1048576*(k+1)*(r+1)^2*(P+2) := by
  have mul:=Nat.mul_le_mul_right (4096*(r+1)*(P+1)) (show a+1 ≤ r+1 by omega)
  nlinarith only [hu,hv,hw,hz,mul,Nat.zero_le k,Nat.zero_le P,Nat.zero_le r,Nat.zero_le (k*r),Nat.zero_le (k*P),Nat.zero_le (k*r*P),Nat.zero_le (k*r^2),Nat.zero_le (k*r^2*P),Nat.zero_le (r^2),Nat.zero_le (r*P),Nat.zero_le (r^2*P)]
private theorem addLoop {k L n Q F r : Nat} (T : Nat → Option Bool) (fr : Frame T L n Q F r)
    (a : Nat) (j s b : Nat) (sum : j+s=k) (hb : b  ≤  r) :
    let P:=F+5*r+n+7
    ∃ t, t  ≤  16*(s+1)*(P+1) ∧
      ((b+s  ≤  r ∧ Path k P t (N (Cursor.q k (330+82*k+11*j)) (D F r n 3) (J T L n F r a b 0 0))
        (N (Cursor.q k (330+93*k)) (D F r n 3) (J T L n F r a (b+s) 0 0))) ∨
       (∃ e, e < s ∧ b+e=r ∧ Path k P t (N (Cursor.q k (330+82*k+11*j)) (D F r n 3) (J T L n F r a b 0 0))
        (N (Cursor.q k (798+93*k)) (D F r n 0) (J T L n F r a r 0 0)))) := by
  let P:=F+5*r+n+7
  have rp : r  ≤  P := by dsimp only [P];omega
  induction s generalizing j b with
  | zero =>
    have eq : 330+82*k+11*j=330+93*k := by omega
    refine ⟨0,by positivity,Or.inl ⟨by omega,?_⟩⟩
    rw [eq,Nat.add_zero];exact Path.nil _ (by dsimp only [N,D,P];omega)
  | succ s ih =>
    have hk : j < k := by omega
    have one:=incAdd T fr hk a b 0 0 hb
    by_cases fits : b < r
    · simp only [if_pos fits,put3true fr a b 0 0 fits] at one
      have jump:=K (k:=k) (P:=P) (334+82*k+11*j) (330+82*k+11*(j+1)) (D F r n 3) (D F r n 3)
        (J T L n F r a (b+1) 0 0) none .stay (by omega) (by dsimp only [N,D,P];omega) (by dsimp only [N,D,P];omega)
        (atD fr (V a (b+1) 0 0) 3 (by omega)) (by run_tac rowTac) rfl
      obtain ⟨u,pu,branch⟩:=ih (j+1) (b+1) (by omega) (by omega)
      change u  ≤  16*(s+1)*(P+1) at pu
      refine ⟨2*b+3+1+u,by exact addPrice P r b s u hb rp pu,?_⟩
      rcases branch with ⟨ok,path⟩|⟨e,he,eq,path⟩
      · exact Or.inl ⟨by omega,by simpa only [show b+1+s=b+(s+1) by omega] using one.append jump |>.append path⟩
      · exact Or.inr ⟨e+1,by omega,by omega,one.append jump |>.append path⟩
    · have eq : b=r := by omega
      simp only [if_neg fits] at one
      obtain ⟨u,pu,path⟩:=addCap T fr hk a b 0 0
      change u  ≤  8*(P+1) at pu
      refine ⟨2*b+3+u,by exact capPrice P r b s u hb rp pu,Or.inr ⟨0,by omega,by omega,?_⟩⟩
      simpa only [eq] using one.append path
private theorem restorePrice (P r b d u v w : Nat) (room : b+(d+1) ≤ r) (hr : r ≤ P)
    (hu : u ≤ 8*(P+1)) (hv : v ≤ 8*(P+1)) (hw : w ≤ 64*(d+1)*(P+1)) :
    2*(d+1)+3+u+(2*b+3)+v+w ≤ 64*(d+2)*(P+1) := by nlinarith only [room,hr,hu,hv,hw]
private theorem restore {k L n Q F r : Nat} (T : Nat → Option Bool) (fr : Frame T L n Q F r)
    (a b c d : Nat) (room : b+d  ≤  r) :
    let P:=F+5*r+n+7
    ∃ t, t  ≤  64*(d+1)*(P+1) ∧ Path k P t
      (N (Cursor.q k (394+93*k)) (D F r n 5) (J T L n F r a b c d))
      (N (Cursor.q k (416+93*k)) (D F r n 5) (J T L n F r a (b+d) c 0)) := by
  let P:=F+5*r+n+7
  have rp : r  ≤  P := by dsimp only [P];omega
  induction d generalizing b with
  | zero =>
    have one:=decRest (k:=k) T fr a b c 0 (by omega)
    dsimp only at one
    exact ⟨3,by nlinarith only [Nat.zero_le P],one⟩
  | succ d ih =>
    have one:=decRest (k:=k) T fr a b c (d+1) (by omega)
    simp only [if_neg (by omega : d+1  ≠  0)] at one
    rw [show D F r n 5+(d+1)=D F r n 5+d+1 by omega,put5false fr a b c d (by omega)] at one
    obtain ⟨u,pu,p1⟩:=route398 (k:=k) T fr a b c d
    have two:=incRest (k:=k) T fr a b c d (by omega)
    simp only [if_pos (by omega : b < r),put3true fr a b c d (by omega)] at two
    obtain ⟨v,pv,p2⟩:=route406 (k:=k) T fr a (b+1) c d
    obtain ⟨w,pw,p3⟩:=ih (b+1) (by omega)
    change u  ≤  8*(P+1) at pu
    change v  ≤  8*(P+1) at pv
    change w  ≤  64*(d+1)*(P+1) at pw
    refine ⟨2*(d+1)+3+u+(2*b+3)+v+w,?_,?_⟩
    · exact restorePrice P r b d u v w room rp pu pv pw
    · simpa only [show b+1+d=b+(d+1) by omega] using one.append p1 |>.append two |>.append p2 |>.append p3
private theorem copyLoop {k L n Q F r : Nat} (T : Nat → Option Bool) (fr : Frame T L n Q F r)
    (a v c e : Nat) (cap : v+e  ≤  r) (hc : c  ≤  r) :
    let P:=F+5*r+n+7
    ∃ t, t  ≤  512*(v+1)*(P+1)+128*e*(P+1) ∧
      ((c+v  ≤  r ∧ Path k P t (N (Cursor.q k (370+93*k)) (D F r n 3) (J T L n F r a v c e))
        (N (Cursor.q k (364+93*k)) (D F r n 2) (J T L n F r a (v+e) (c+v) 0))) ∨
       (∃ h, h < v ∧ r=c+h ∧ Path k P t (N (Cursor.q k (370+93*k)) (D F r n 3) (J T L n F r a v c e))
        (N (Cursor.q k (798+93*k)) (D F r n 0) (J T L n F r a (v-h-1) r (e+h))))) := by
  let P:=F+5*r+n+7
  have rp : r  ≤  P := by dsimp only [P];omega
  induction v generalizing c e with
  | zero =>
    have one:=decInner (k:=k) T fr a 0 c e (by omega)
    dsimp only at one
    obtain ⟨u,pu,p1⟩:=route390 (k:=k) T fr a 0 c e
    obtain ⟨v,pv,p2⟩:=restore (k:=k) T fr a 0 c e (by omega)
    simp only [Nat.zero_add] at p2
    obtain ⟨w,pw,p3⟩:=route416 (k:=k) T fr a e c 0
    change u  ≤  8*(P+1) at pu
    change v  ≤  64*(e+1)*(P+1) at pv
    change w  ≤  8*(P+1) at pw
    refine ⟨3+u+v+w,by exact copyBasePrice P e u v w pu pv pw,Or.inl ⟨by omega,?_⟩⟩
    simpa only [Nat.zero_add,Nat.add_zero] using one.append p1 |>.append p2 |>.append p3
  | succ v ih =>
    have one:=decInner (k:=k) T fr a (v+1) c e (by omega)
    simp only [if_neg (by omega : v+1 ≠ 0)] at one
    rw [show D F r n 3+(v+1)=D F r n 3+v+1 by omega,put3false fr a v c e (by omega)] at one
    obtain ⟨u,pu,p1⟩:=route374 (k:=k) T fr a v c e
    have two:=incOut (k:=k) T fr a v c e hc
    change u  ≤  8*(P+1) at pu
    by_cases fits : c < r
    · simp only [if_pos fits,put4true fr a v c e fits] at two
      obtain ⟨w,pw,p2⟩:=route380 (k:=k) T fr a v (c+1) e
      have three:=incTemp (k:=k) T fr a v (c+1) e (by omega)
      simp only [if_pos (by omega : e < r),put5true fr a v (c+1) e (by omega)] at three
      obtain ⟨z,pz,p3⟩:=route386 (k:=k) T fr a v (c+1) (e+1)
      obtain ⟨d,pd,branch⟩:=ih (c+1) (e+1) (by omega) (by omega)
      change w  ≤  8*(P+1) at pw
      change z  ≤  8*(P+1) at pz
      change d  ≤  512*(v+1)*(P+1)+128*(e+1)*(P+1) at pd
      refine ⟨2*(v+1)+3+u+(2*c+3)+w+(2*e+3)+z+d,?_,?_⟩
      · exact copyPrice P r v c e u w z d hc cap rp pu pw pz pd
      · have path:=one.append p1 |>.append two |>.append p2 |>.append three |>.append p3
        rcases branch with ⟨ok,rest⟩|⟨h,hh,eq,rest⟩
        · exact Or.inl ⟨by omega,by simpa only [show v+(e+1)=v+1+e by omega,show c+1+v=c+(v+1) by omega] using path.append rest⟩
        · refine Or.inr ⟨h+1,by omega,by omega,?_⟩
          simpa only [show v-h-1=(v+1)-(h+1)-1 by omega,show e+1+h=e+(h+1) by omega] using path.append rest
    · have eq : c=r := by omega
      simp only [if_neg fits] at two
      obtain ⟨w,pw,p2⟩:=route422 (k:=k) T fr a v c e
      change w  ≤  8*(P+1) at pw
      refine ⟨2*(v+1)+3+u+(2*c+3)+w,by exact copyCapPrice P r v c e u w hc cap rp pu pw,Or.inr ⟨0,by omega,by omega,?_⟩⟩
      simpa only [eq,Nat.sub_zero,Nat.add_zero,Nat.add_sub_cancel] using one.append p1 |>.append two |>.append p2
private theorem multiply {k L n Q F r : Nat} (T : Nat → Option Bool) (fr : Frame T L n Q F r)
    (a b c : Nat) (ha : a  ≤  r) (hb : b  ≤  r) (hc : c  ≤  r) :
    let P:=F+5*r+n+7
    ∃ t, t  ≤  4096*(a+1)*(r+1)*(P+1) ∧
      ((a*b+c  ≤  r ∧ Path k P t (N (Cursor.q k (364+93*k)) (D F r n 2) (J T L n F r a b c 0))
        (N (Cursor.q k (430+93*k)) (D F r n 2) (J T L n F r 0 b (a*b+c) 0))) ∨
       (∃ u e, u < a ∧ e < b ∧ r=c+u*b+e ∧ Path k P t (N (Cursor.q k (364+93*k)) (D F r n 2) (J T L n F r a b c 0))
        (N (Cursor.q k (798+93*k)) (D F r n 0) (J T L n F r (a-u-1) (b-e-1) r e)))) := by
  let P:=F+5*r+n+7
  have rp : r  ≤  P := by dsimp only [P];omega
  induction a generalizing c with
  | zero =>
    have one:=decOuter (k:=k) T fr 0 b c 0 (by omega)
    dsimp only at one
    exact ⟨3,by nlinarith only [Nat.zero_le r,Nat.zero_le P],Or.inl ⟨by omega,by simpa only [Nat.zero_mul,Nat.zero_add] using one⟩⟩
  | succ a ih =>
    have one:=decOuter (k:=k) T fr (a+1) b c 0 ha
    simp only [if_neg (by omega : a+1 ≠ 0)] at one
    rw [show D F r n 2+(a+1)=D F r n 2+a+1 by omega,put2false fr a b c 0 (by omega)] at one
    obtain ⟨u,pu,p1⟩:=route368 (k:=k) T fr a b c 0
    obtain ⟨v,pv,branch⟩:=copyLoop (k:=k) T fr a b c 0 (by omega) hc
    change u  ≤  8*(P+1) at pu
    have pv0 : v ≤ 512*(b+1)*(P+1) := by simpa only [Nat.mul_zero,Nat.zero_mul,Nat.add_zero] using pv
    rcases branch with ⟨ok,p2⟩|⟨e,he,eq,p2⟩
    · obtain ⟨w,pw,branch⟩:=ih (c+b) (by omega) ok
      change w  ≤  4096*(a+1)*(r+1)*(P+1) at pw
      have p2' : Path k P v (N (Cursor.q k (370+93*k)) (D F r n 3) (J T L n F r a b c 0))
          (N (Cursor.q k (364+93*k)) (D F r n 2) (J T L n F r a b (c+b) 0)) := by simpa only [Nat.add_zero] using p2
      refine ⟨2*(a+1)+3+u+v+w,by exact multPrice P r a b u v w ha hb rp pu pv0 pw,?_⟩
      rcases branch with ⟨final,path⟩|⟨q,e,hq,he,eq,path⟩
      · exact Or.inl ⟨by nlinarith only [final],by simpa only [show a*b+(c+b)=(a+1)*b+c by ring] using one.append p1 |>.append p2' |>.append path⟩
      · refine Or.inr ⟨q+1,e,by omega,he,by nlinarith only [eq],?_⟩
        simpa only [show a-q-1=(a+1)-(q+1)-1 by omega] using one.append p1 |>.append p2' |>.append path
    · simp only [Nat.zero_add] at p2
      refine ⟨2*(a+1)+3+u+v,by simpa only [Nat.add_zero] using multPrice P r a b u v 0 ha hb rp pu pv0 (by positivity),Or.inr ⟨0,e,by omega,he,by omega,?_⟩⟩
      simpa only [Nat.add_zero,Nat.sub_zero,Nat.add_sub_cancel,Nat.zero_mul] using one.append p1 |>.append p2
private theorem fourCap {k L n Q F r j : Nat} (T : Nat → Option Bool) (fr : Frame T L n Q F r) (hj : j < 4) (a b : Nat) :
    let P:=F+5*r+n+7
    ∃ t, t  ≤  8*(P+1) ∧ Path k P t (N (Cursor.q k (336+8*j+93*k)) (D F r n 2) (J T L n F r a b 0 0))
      (N (Cursor.q k (798+93*k)) (D F r n 0) (J T L n F r a b 0 0)) := by
  interval_cases j
  · exact route336 T fr a b 0 0
  · exact route344 T fr a b 0 0
  · exact route352 T fr a b 0 0
  · exact route360 T fr a b 0 0
private theorem fourLoop {k L n Q F r : Nat} (T : Nat → Option Bool) (fr : Frame T L n Q F r)
    (j s a b : Nat) (sum : j+s=4) (ha : a  ≤  r) :
    let P:=F+5*r+n+7
    ∃ t, t  ≤  16*(s+1)*(P+1) ∧
      ((a+s  ≤  r ∧ Path k P t (N (Cursor.q k (332+8*j+93*k)) (D F r n 2) (J T L n F r a b 0 0))
        (N (Cursor.q k (364+93*k)) (D F r n 2) (J T L n F r (a+s) b 0 0))) ∨
       (∃ e, e < s ∧ a+e=r ∧ Path k P t (N (Cursor.q k (332+8*j+93*k)) (D F r n 2) (J T L n F r a b 0 0))
        (N (Cursor.q k (798+93*k)) (D F r n 0) (J T L n F r r b 0 0)))) := by
  let P:=F+5*r+n+7
  have rp : r  ≤  P := by dsimp only [P];omega
  induction s generalizing j a with
  | zero =>
    have eq : 332+8*j+93*k=364+93*k := by omega
    refine ⟨0,by positivity,Or.inl ⟨by omega,?_⟩⟩
    rw [eq,Nat.add_zero];exact Path.nil _ (by dsimp only [N,D,P];omega)
  | succ s ih =>
    have hj : j < 4 := by omega
    have one:=incFour (k:=k) T fr hj a b 0 0 ha
    by_cases fits : a < r
    · simp only [if_pos fits,put2true fr a b 0 0 fits] at one
      obtain ⟨u,pu,branch⟩:=ih (j+1) (a+1) (by omega) (by omega)
      change u  ≤  16*(s+1)*(P+1) at pu
      have eq : 340+8*j+93*k=332+8*(j+1)+93*k := by omega
      rw [eq] at one
      refine ⟨2*a+3+u,by have h:=addPrice P r a s u ha rp pu;exact le_trans (by omega) h,?_⟩
      rcases branch with ⟨ok,path⟩|⟨e,he,eq,path⟩
      · exact Or.inl ⟨by omega,by simpa only [show a+1+s=a+(s+1) by omega] using one.append path⟩
      · exact Or.inr ⟨e+1,by omega,by omega,one.append path⟩
    · have eq : a=r := by omega
      simp only [if_neg fits] at one
      obtain ⟨u,pu,path⟩:=fourCap (k:=k) T fr hj a b
      change u  ≤  8*(P+1) at pu
      refine ⟨2*a+3+u,by exact capPrice P r a s u ha rp pu,Or.inr ⟨0,by omega,by omega,?_⟩⟩
      simpa only [eq] using one.append path
private theorem tail {k L n Q F r : Nat} (T : Nat → Option Bool) (fr : Frame T L n Q F r)
    (ell b : Nat) (he : ell  ≤  r) (hb : b  ≤  r) :
    let P:=F+5*r+n+7
    ∃ t, t  ≤  1048576*(k+1)*(r+1)^2*(P+2) ∧
      ((((ell+4)*(b+k)  ≤  r) ∧ Path k P t
        (N (Cursor.q k (329+82*k)) (D F r n 3) (J T L n F r ell b 0 0))
        (N (Cursor.q k (430+93*k)) (D F r n 2) (J T L n F r 0 (b+k) ((ell+4)*(b+k)) 0))) ∨
       (∃ v2 v3 v4 v5, (
         (∃ j, j < k ∧ b+j=r ∧ v2=ell ∧ v3=r ∧ v4=0 ∧ v5=0) ∨
         (∃ j, j < 4 ∧ ell+j=r ∧ v2=r ∧ v3=b+k ∧ v4=0 ∧ v5=0) ∨
         (∃ a e, a < ell+4 ∧ e < b+k ∧ r=a*(b+k)+e ∧ v2=ell+4-a-1 ∧ v3=b+k-e-1 ∧ v4=r ∧ v5=e)) ∧
         Path k P t (N (Cursor.q k (329+82*k)) (D F r n 3) (J T L n F r ell b 0 0))
           (N (Cursor.q k (798+93*k)) (D F r n 0) (J T L n F r v2 v3 v4 v5)))) := by
  let P:=F+5*r+n+7
  have rp : r  ≤  P := by dsimp only [P];omega
  have one:=K (k:=k) (P:=P) (329+82*k) (330+82*k) (D F r n 3) (D F r n 3)
    (J T L n F r ell b 0 0) none .stay (by omega) (by dsimp only [N,D,P];omega) (by dsimp only [N,D,P];omega)
    (atD fr (V ell b 0 0) 3 (by omega)) (by run_tac rowTac) rfl
  obtain ⟨u,pu,add⟩:=addLoop (k:=k) T fr ell 0 k b (by omega) hb
  change u  ≤  16*(k+1)*(P+1) at pu
  rcases add with ⟨ok,p1⟩|⟨j,hj,eq,p1⟩
  · obtain ⟨v,pv,p2⟩:=route330 (k:=k) T fr ell (b+k) 0 0
    obtain ⟨w,pw,four⟩:=fourLoop (k:=k) T fr 0 4 ell (b+k) rfl he
    change v  ≤  8*(P+1) at pv
    change w  ≤  80*(P+1) at pw
    rcases four with ⟨fit,p3⟩|⟨j,hj,eq,p3⟩
    · obtain ⟨z,pz,mul⟩:=multiply (k:=k) T fr (ell+4) (b+k) 0 fit ok (by omega)
      change z  ≤  4096*(ell+4+1)*(r+1)*(P+1) at pz
      have bound : 1+u+v+w+z ≤ 1048576*(k+1)*(r+1)^2*(P+2) := tailPrice P r k (ell+4) u v w z fit pu pv pw pz
      refine ⟨1+u+v+w+z,bound,?_⟩
      rcases mul with ⟨final,p4⟩|⟨a,e,ha,hx,eq,p4⟩
      · exact Or.inl ⟨by simpa only [Nat.add_zero] using final,by simpa only [Nat.zero_add,Nat.add_zero,Nat.mul_zero] using one.append p1 |>.append p2 |>.append p3 |>.append p4⟩
      · refine Or.inr ⟨_,_,_,_,Or.inr (Or.inr ⟨a,e,ha,hx,by simpa only [Nat.zero_add] using eq,rfl,rfl,rfl,rfl⟩),?_⟩
        simpa only [Nat.add_zero,Nat.zero_add] using one.append p1 |>.append p2 |>.append p3 |>.append p4
    · refine ⟨1+u+v+w,?_,Or.inr ⟨r,b+k,0,0,Or.inr (Or.inl ⟨j,hj,eq,rfl,rfl,rfl,rfl⟩),?_⟩⟩
      · simpa only [Nat.add_zero] using tailPrice P r k 0 u v w 0 (by omega) pu pv pw (by positivity)
      · exact one.append p1 |>.append p2 |>.append p3
  · refine ⟨1+u,?_,Or.inr ⟨ell,r,0,0,Or.inl ⟨j,hj,eq,rfl,rfl,rfl,rfl⟩,?_⟩⟩
    · simpa only [Nat.add_zero] using tailPrice P r k 0 u 0 0 0 (by omega) pu (by positivity) (by positivity) (by positivity)
    · simpa only [Nat.zero_add] using one.append p1
end FullWeight
