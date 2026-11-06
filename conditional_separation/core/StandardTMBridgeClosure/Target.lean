import StandardTMBridgeClosure.Machine
namespace StandardTMBridgeClosure
open Pnp3.Complexity.Uniform.V1 Turing
open Pnp4.Frontier Pnp4.Frontier.ContractExpansion Pnp4.AlgorithmsToLowerBounds PairEncoding
/-- Transparent overhead absorption, fixed before the raw input. -/
def degree (k : Nat) : Nat := 4*NormalClockClosure.degree k+4
namespace Target
/-- Exact sealed NORMAL source witnesses, including its original full image,
parsed source, sound rejection and both virtual work bits. Proof specification. -/
def Source (k N : Nat) (y : Bitstring N) (d t : Nat) : Prop :=
  let G:=RawCallerClosure.allocation k N
  let M:=NormalFinalClosure.machine2 k
  let C:=initialConfig M G y
  let O:=RawCallerClosure.machine k
  let oldC:=initialConfig O G y
  let rows:=RawCallerClosure.callerState k (PhysicalCallerClosure.rowsDone k)
  let virtual (b : Bool):=RawCallerClosure.old k (CertificateGuardClosure.old k (TotalIngressClosure.old k
    (BodyIngress.old k (CarryWindow.embed k (CanonicalLeaf.result k b)))))
  d ≤ t ∧ t ≤ 17592186044416*(k+1)*(N+1)^8 ∧
    (∀ u,u ≤ d → (NormalFinalClosure.machine2 k).run u C=
      NormalFinalClosure.config2 k (O.run u oldC)) ∧
    (∀ u,u ≤ d → (O.run u oldC).state≠O.accept) ∧
    (∀ u,u < d → (O.run u oldC).state≠O.reject ∧ (O.run u oldC).state≠rows ∧
      ∀ b,(O.run u oldC).state≠virtual b) ∧
    (∀ u,u < t → ((NormalFinalClosure.machine2 k).run u C).state≠(NormalFinalClosure.machine2 k).accept ∧
      ((NormalFinalClosure.machine2 k).run u C).state≠(NormalFinalClosure.machine2 k).reject ∧
      ∀ b,((NormalFinalClosure.machine2 k).run u C).state≠NormalFinalClosure.old2 k (virtual b)) ∧
    ((t=d ∧ (∃ b,(O.run d oldC).state=virtual b) ∧
      (NormalFinalClosure.machine2 k).run t C=NormalFinalClosure.config2 k (O.run d oldC)) ∨
     (t=d ∧ (O.run d oldC).state=O.reject ∧
      encodedRelationLanguage (PartAEndpoint.thresholdContentWitnessRelation k) N y=false ∧
      (NormalFinalClosure.machine2 k).run t C=NormalFinalClosure.config2 k (O.run d oldC)) ∨
     (∃ (a m : Nat) (x : Bitstring a) (w : Bitstring m) (hN : pairLength a m=N),
      decodePair y=some ((⟨a,x⟩,⟨m,w⟩):DecodedPair) ∧ y=(hN ▸ encodePair x w) ∧ m=a+1 ∧
      ∃ n z, FixedContentTagGate.tagMatches (Fin.append x w)=true ∧
      FixedContentGammaTerminator.gammaZeros? (Fin.append x w)=some z ∧
      contentHeader? (Fin.append x w)=some (n,2*z+1) ∧
      let S:=a+m;let F:=FixedRawLengthFence.fencePos N;let r:=S-min (9+2*z+2^n) S
      let W:=Cursor.Target.W k n
      min (9+2*z+2^n) S < S ∧ bitLength n ≤ r ∧ W ≤ r ∧
      (O.run d oldC).state=rows ∧
      ∃ hH:S+z+2+n+1 < tapeLength N G,
      (O.run d oldC).head=⟨S+z+2+n+1,hH⟩ ∧
      ∃ answer : Bool,
      answer=encodedRelationLanguage (PartAEndpoint.thresholdContentWitnessRelation k) N y ∧
      answer=PartAEndpoint.thresholdContentWitnessRelation k a m x w ∧
      (answer=true ↔ NormalFinalClosure.Target.PrefixOK (Fin.append x w) n z W) ∧
      (NormalFinalClosure.machine2 k).run t C=
        ⟨if answer then (NormalFinalClosure.machine2 k).accept else (NormalFinalClosure.machine2 k).reject,
          ⟨S+z+2+n+1,hH⟩,NormalFinalClosure.Target.cleared (O.run d oldC).tape F r n⟩))
/-- Exact elementary TM0 trace from the real library init. All midpoint tapes
are included; the input-origin flag is installed by the boot row. -/
def Simulation (M : UniformTM) : Prop :=
  ∀ (N B t : Nat) (y : Bitstring N),
  let c:=initialConfig M B y
  let start : TM0.Cfg (Bool × Option Bool) (Option (Fin M.stateCount × Fin 4)):=
    TM0.init (encode (List.ofFn y))
  (∀ u,u < t → (M.run u c).state≠M.accept ∧ (M.run u c).state≠M.reject) →
  (∀ u,u < t → (M.step (M.run u c).state ((M.run u c).tape (M.run u c).head)).2.2=Move.right →
    (M.run u c).head.val+1 < tapeLength N B) →
  (∀ u,u ≤ t → ∃ v,steps M (1+2*u) start=some v ∧ Represents M (M.run u c) v) ∧
  (∀ u,u < t →
    let s:=M.run u c
    let a:=M.step s.state (s.tape s.head)
    ∃ v,steps M (2+2*u) start=some v ∧
      v.q=some (a.1,match a.2.2 with | .left=>1 | .stay=>2 | .right=>3) ∧
      ∀ i : Int,v.Tape.nth i=
        if i=0 then (decide (s.head.val=0),a.2.1)
        else if h:0 ≤ (s.head.val : Int)+i ∧ (s.head.val : Int)+i < (tapeLength N B : Int)
        then (decide ((s.head.val : Int)+i=0),s.tape ⟨((s.head.val : Int)+i).toNat,by omega⟩)
        else (false,none))
/-- Unconditional all-original-raw NORMAL compiler capstone on the actual
Mathlib machine. Virtual controls remain live; a literal control halt is used
as decision convention. No claim about TM0.eval's tape output is made. -/
def Raw (k : Nat) : Prop :=
  ∀ (N : Nat) (y : Bitstring N),
  let M:=NormalFinalClosure.machine2 k
  let G:=RawCallerClosure.allocation k N
  let c:=initialConfig M G y
  let start : TM0.Cfg (Bool × Option Bool) (Option (Fin M.stateCount × Fin 4)):=
    TM0.init (encode (List.ofFn y))
  let virtual (b : Bool):=NormalFinalClosure.old2 k (RawCallerClosure.old k
    (CertificateGuardClosure.old k (TotalIngressClosure.old k
      (BodyIngress.old k (CarryWindow.embed k (CanonicalLeaf.result k b))))))
  ∃ (d t : Nat) (last : TM0.Cfg (Bool × Option Bool) (Option (Fin M.stateCount × Fin 4))),
    Source k N y d t ∧
    1+2*t ≤ polyClock (degree k) N ∧
    steps M (1+2*t) start=some last ∧ Represents M (M.run t c) last ∧
    (∀ u,u ≤ t → ∃ v,steps M (1+2*u) start=some v ∧ Represents M (M.run u c) v) ∧
    (∀ j,j ≤ 1+2*t → ∃ v,steps M j start=some v) ∧
    (∀ j,j < 1+2*t → ∀ v,steps M j start=some v →
      v.q≠some (M.accept,0) ∧ v.q≠some (M.reject,0) ∧ ∀ b,v.q≠some (virtual b,0)) ∧
    ((∃ b,last.q=some (virtual b,0) ∧ TM0.step (compile M) last≠none) ∨
     (∃ answer : Bool,answer=encodedRelationLanguage (PartAEndpoint.thresholdContentWitnessRelation k) N y ∧
       last.q=some ((if answer then M.accept else M.reject),0) ∧
       TM0.step (compile M) last=none))
end Target
end StandardTMBridgeClosure
