import VirtualFinalClosure.ElasticRows
namespace VirtualFinalClosure.Elastic
open Pnp3.Complexity.Uniform.V1 Lean Elab Command
run_cmd do
  let entries := (← getEnv).constants.toList.filter fun (n,_) =>
    n.toString.startsWith "_private.VirtualFinalClosure.ElasticRows." &&
    n.toString.endsWith ".VirtualFinalClosure.Elastic.nativeRows"
  match entries with
  | [(n,.defnInfo ci)] =>
    logInfo m!"private-term|{n}|kind=definition|type={ci.type}"
    modifyScope fun st => {st with openDecls := .explicit `nativeRows n :: st.openDecls}
  | _ => throwError "Ambiguous finite ROM definition"
private def romPin : Array (Nat × Nat × Nat × Nat) := nativeRows
private def metaCount : Nat := 144
private def tailCount : Nat := 239
private def encodeMeta (f mode phase seen bad : Nat) : Nat :=
  (f+4*mode+12*phase+36*seen+72*bad)%144
private def flag (m : Nat) := m%4
private def mode (m : Nat) := (m/4)%3
private def phase (m : Nat) := (m/12)%3
private def seen (m : Nat) := (m/36)%2
private def bad (m : Nat) := (m/72)%2
private def changeMeta (op m : Nat) : Nat :=
  let f:=flag m; let v:=mode m;let p:=phase m;let s:=seen m;let b:=bad m
  match op with
  | 1 => encodeMeta f 0 p s b
  | 2 => encodeMeta f 1 p 1 b
  | 3 => encodeMeta f 2 p s b
  | 4 => encodeMeta f v 1 s b
  | 5 => encodeMeta f v p s 1
  | 6 => encodeMeta f v p 0 b
  | 7 => encodeMeta f v 2 s b
  | 8 => encodeMeta f v p s (if v=1 then 1 else b)
  | _ => m%144
private def table (k i : Nat) : Fin (CertificateGuardClosure.machine k).stateCount :=
  CertificateGuardClosure.old k (TotalIngressClosure.old k (BodyIngress.old k
    (CarryWindow.embed k (VirtualLeaf.embed k
      (IngressRepair.producer.seqRight (Cursor.machine k) (Cursor.q k i))))))
private def leaf (k : Nat) (b : Bool) : Fin (CertificateGuardClosure.machine k).stateCount :=
  CertificateGuardClosure.old k (TotalIngressClosure.old k (BodyIngress.old k
    (CarryWindow.embed k (CanonicalLeaf.result k b))))
private def body (k : Nat) (m : Fin 3) : Fin (CertificateGuardClosure.machine k).stateCount :=
  CertificateGuardClosure.old k (TotalIngressClosure.old k (BodyIngress.body k (SerializedBody.entry m)))
private def count (k : Nat) : Nat := 144*((CertificateGuardClosure.machine k).stateCount+tailCount)
private def pack (k q m : Nat) : Fin (count k) :=
  ⟨(144*q+m)%count k,Nat.mod_lt _ (by dsimp [count,tailCount];omega)⟩
private def resolve (k targetCode m : Nat) : Nat :=
  let S:=(CertificateGuardClosure.machine k).stateCount
  match targetCode with
  | 239 => (CertificateGuardClosure.machine k).reject.val
  | 240 => S+(if phase m=1 then 52 else 5)
  | 241 => S+(if mode m=2 then 18 else 19)
  | 242 => S+(if seen m=1 then 41 else 50)
  | 243 => (table k 98).val
  | 244 => S+(if mode m=1 then 137 else 152)
  | 245 => S+(if mode m=2 then 166 else 167)
  | 246 => S+(if mode m=2 then 231 else 195)
  | 247 => (table k (798+93*k)).val
  | _ => S+targetCode
private def symbol (s m : Nat) : Option Bool :=
  if s=3 then if mode m=2 then none else some (mode m=1)
  else if s=0 then none else some (s=2)
private def direction (s : Nat) : Move :=
  if s=0 then .left else if s=2 then .right else .stay
private def tailStep (k q m : Nat) (b : Option Bool) : Nat × Nat × Option Bool × Move :=
  let sym := match b with | none=>0 | some false=>1 | some true=>2
  let row := romPin[q*3+sym]?.getD (239,0,1,5)
  let next := changeMeta row.2.2.2 m
  (resolve k row.1 next,next,symbol row.2.1 m,direction row.2.2.1)
private def updateFlag (m : Nat) (observed : Bool) : Nat :=
  let f:=flag m
  let expected:=decide (2 ≤ f)
  let matched:=f%2==1
  encodeMeta ((if expected then 0 else 2)+(if matched && observed==expected then 1 else 0))
    (mode m) (phase m) (seen m) (bad m)
private def oldStep (k q m : Nat) (b : Option Bool) : Nat × Nat × Option Bool × Move :=
  let O:=CertificateGuardClosure.machine k
  let s:Fin O.stateCount:=⟨q%O.stateCount,Nat.mod_lt _ (by have h:=O.start.isLt;omega)⟩
  if s=leaf k false ∨ s=leaf k true then
    ((if flag m%2=1 ∧ bad m=0 then O.accept else O.reject).val,m,b,.stay)
  else if phase m≠2 ∧ b=none ∧ (s=table k 250 ∨ s=table k 304) then
    (O.stateCount+0,m,b,.stay)
  else if phase m≠2 ∧ b=none ∧ s=table k (798+93*k) then
    (O.stateCount+4,m,b,.stay)
  else if phase m=1 ∧ s=table k (430+93*k) then
    let a:=(Cursor.machine k).step (Cursor.q k (430+93*k)) b
    ((table k a.1.val).val,m,a.2)
  else if phase m=1 ∧ b=none ∧ s=table k (613+93*k) then
    (O.stateCount+89,m,b,.stay)
  else
    let a:=O.step s b
    let next:=if ∃ j : Fin 3,a.1=body k j then encodeMeta 0 2 0 0 0
      else if b=none ∧ s=table k 43 then updateFlag m false
      else if b=none ∧ s=table k 47 then updateFlag m true
      else if b=none ∧ s=table k 51 then updateFlag m false
      else m
    (a.1.val,next,a.2)
private def rawStep (k : Nat) (s : Fin (count k)) (b : Option Bool) :
    Fin (count k) × Option Bool × Move :=
  let O:=CertificateGuardClosure.machine k
  let q:=s.val/144;let m:=s.val%144
  let a:=if q<O.stateCount then oldStep k q m b else tailStep k (q-O.stateCount) m b
  let next:=if a.1=O.accept.val ∨ a.1=O.reject.val then encodeMeta 0 2 0 0 0 else a.2.1
  (pack k a.1 next,a.2.2)
/-- PRE-FREEZE physical elastic-capacity candidate. All operands are tape data;
only k and fixed finite controls occur in the transition constructor. -/
private def candidateMachine (k : Nat) : UniformTM where
  stateCount:=count k
  start:=pack k (CertificateGuardClosure.machine k).start.val (encodeMeta 1 2 0 0 0)
  accept:=pack k (CertificateGuardClosure.machine k).accept.val (encodeMeta 0 2 0 0 0)
  reject:=pack k (CertificateGuardClosure.machine k).reject.val (encodeMeta 0 2 0 0 0)
  accept_ne_reject:=by
    intro equal
    have av:(CertificateGuardClosure.machine k).accept.val<(CertificateGuardClosure.machine k).stateCount:=Fin.isLt _
    have rv:(CertificateGuardClosure.machine k).reject.val<(CertificateGuardClosure.machine k).stateCount:=Fin.isLt _
    have h:=congrArg Fin.val equal
    dsimp only [pack,encodeMeta,count,tailCount] at h
    norm_num at h
    rw [Nat.mod_eq_of_lt (by omega),Nat.mod_eq_of_lt (by omega)] at h
    have same:(CertificateGuardClosure.machine k).accept=(CertificateGuardClosure.machine k).reject:=Fin.ext (by omega)
    exact (CertificateGuardClosure.machine k).accept_ne_reject same
  rawStep:=rawStep k
#eval do
  IO.println "engineering|ELASTIC-CANDIDATE|NOT-FROZEN|NO-RAW-PROOF"
  for k in [0,1,2,64] do
    let O:=CertificateGuardClosure.machine k
    let P:=candidateMachine k
    IO.println s!"elastic-meta|{k}|{P.stateCount}|{P.start.val}|{P.accept.val}|{P.reject.val}|{O.stateCount}"
    for t in [98,250,304,430+93*k,613+93*k,798+93*k] do
      let c:=Cursor.q k t
      for b in [none,some false,some true] do
        let a:=(Cursor.machine k).step c b
        let sym:=match b with | none=>0 | some false=>1 | some true=>2
        let out:=match a.2.1 with | none=>0 | some false=>1 | some true=>2
        let mv:Int:=match a.2.2 with | .left=> -1 | .stay=>0 | .right=>1
        IO.println s!"cursor-native|{k}|{c.val}|{sym}|{a.1.val}|{out}|{mv}"
  -- Export actual native rows at every finite metadata variant. k=0 suffices for
  -- this fixed ROM; all k-dependent old-control indices are separately exported.
  for q in [:239] do
    for m in [:144] do
      for b in [none,some false,some true] do
        let a:=rawStep 0 (pack 0 ((CertificateGuardClosure.machine 0).stateCount+q) m) b
        let sym:=match b with | none=>0 | some false=>1 | some true=>2
        let out:=match a.2.1 with | none=>0 | some false=>1 | some true=>2
        let mv:Int:=match a.2.2 with | .left=> -1 | .stay=>0 | .right=>1
        IO.println s!"elastic-native|{q}|{m}|{sym}|{a.1.val}|{out}|{mv}"
end VirtualFinalClosure.Elastic
