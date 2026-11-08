import CappedWeight.Fixtures
namespace CappedWeight
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier Pnp4.Frontier.ContractExpansion
open Pnp4.AlgorithmsToLowerBounds PairEncoding
theorem check_phase_row (k i code : Nat) (b : Option Bool) (hk : 0<k)
    (lo : 329 ≤ i) (hi : i<411)
    (got : (instructions k)[3*(i-329)+(match (generalizing := false) b with | none => 0 | some false => 1 | some true => 2)]?=some code) :
    (Cursor.machine k).step (Cursor.q k i) b=
      (Cursor.q k (code/9),(if code/3%3=0 then none else some (decide (code/3%3=2))),
        if code%3=0 then Move.left else if code%3=1 then Move.stay else Move.right) := by
  exact phase_row k i code b hk lo hi got
theorem check_first_product (k N B L n Q F r : Nat) (T : Nat → Option Bool) (hk : 0 < k) (hr : 0 < r)
    (paid : 0 < Q) (room : L+n+1+Q < F) (sep : T L=none) (right : T (L+n+1)=none)
    (marks : ∀ i, L+n+1 < i → i ≤ L+n+1+Q → T i=some true)
    (gap : ∀ i, L+n+1+Q < i → i < F → T i=none) (fence : T F=some false)
    (delims : ∀ i, i=F+1 ∨ i=F+r+2 ∨ i=F+r+n+3 ∨ i=F+2*r+n+4 ∨
      i=F+3*r+n+5 ∨ i=F+4*r+n+6 ∨ i=F+5*r+n+7 → T i=none)
    (b0 : ∀ i, F+1 < i → i < F+r+2 → T i=some true)
    (b1 : ∀ i, F+r+2 < i → i < F+r+n+3 → T i=some false)
    (initial : Target.image T L n F r (Pnp4.Frontier.ContractExpansion.bitLength n) 1 0 0 0=T) :

  ∀ (fit : F+5*r+n+7 < tapeLength N B),
  ∃ t, t≤1024*(n+r+1)^2*(F+5*r+n+9) ∧
    (Cursor.machine k).run t
      (⟨Cursor.q k 329,⟨F+2*r+n+4,by omega⟩,fun i => T i.val⟩ : Config (Cursor.machine k).stateCount N B)=
      ⟨Cursor.q k (if n≤r then 411 else 798+93*k),
        ⟨if n≤r then F+2*r+n+4 else F+1,by split <;> omega⟩,
        fun i => Target.image T L n F r (bitLength n) (if n≤r then n else 0) (if n≤r then 0 else r) 0 (if n≤r then 0 else r+1) i.val⟩ ∧
    (∀ u, u<t → ((Cursor.machine k).run u
      (⟨Cursor.q k 329,⟨F+2*r+n+4,by omega⟩,fun i => T i.val⟩ : Config (Cursor.machine k).stateCount N B)).state.val<411) := by
  exact first_product k N B L n Q F r T hk hr paid room sep right marks gap fence delims b0 b1 initial
theorem check_accepted_first_product (k : Nat) (hk : 0 < k) :
  ∀ {a m : Nat} (x : Bitstring a) (w : Bitstring m),
    PartAEndpoint.thresholdContentWitnessRelation k a m x w=true →
    ∃ pr : (Sigma fun r : Nat => PrefixInput
      (treeMCSPSearchProblem (thresholdPoly k)
        (TreeMCSPSearchWitnessEncoding.ofCodec (treeCircuitWitnessCodec (thresholdPoly k))))
      (treeMCSPPrefixM (treeCircuitWitnessCodec (thresholdPoly k)) r)),
      contentInput? (treeCircuitWitnessCodec (thresholdPoly k)) (Fin.append x w)=some pr ∧
      Pnp3.Models.Partial.tableLen pr.2.n ≤ a+m ∧
      ∃ (z : Nat)
        (hH : a+m+z+pr.2.n+3 < tapeLength (pairLength a m) (FixedRawLengthFence.allocation (pairLength a m))),
        FixedContentGammaTerminator.gammaZeros? (Fin.append x w)=some z ∧
        let S := a+m
        let R := pairLength a m
        let B := FixedRawLengthFence.allocation R
        let F := FixedRawLengthFence.fencePos R
        let n := pr.2.n
        let L := S+z+2
        let U := Body.extend (Body.installedTape (SmallIngress.prepared B x w z n) L n)
        let V := Stream.Target.image U S z n (9+2*z) (2^n) (2^n) false
        let p := min (9+2*z+2^n) S
        let r := S-p
        let X := CappedWorkspace.Target.image (SuffixCap.Target.image V F r) L n F r
        let Y := RuntimeBitLength.Target.fullImage X L n F r
        let c := initialConfig (AllArityCursor.machine k) B (encodePair x w)
        (p=S → ∃ t, t ≤ 67108864*(R+1)^4 ∧ S ≤ Cursor.Target.M k n z ∧
          padRead (Fin.append x w) (Cursor.Target.M k n z)=false ∧
          (AllArityCursor.machine k).run t c=SmallIngress.producer.seqEmbedRight (Cursor.machine k)
            ⟨Cursor.mReady k ⟨2,by decide⟩,⟨S+z+n+3,hH⟩,fun i => V i.val⟩) ∧
        (p<S → ∃ (t : Nat)
          (h : (if bitLength n ≤ r then F+2*r+n+4 else F+r+n+3) < tapeLength R B),
          t ≤ 67108864*(R+1)^4 ∧ F+5*r+n+7 < tapeLength R B ∧
          (AllArityCursor.machine k).run t c=SmallIngress.producer.seqEmbedRight (Cursor.machine k)
            ⟨Cursor.q k (if bitLength n ≤ r then 329 else if (r+1)%2=1 then 250 else 304),
              ⟨if bitLength n ≤ r then F+2*r+n+4 else F+r+n+3,h⟩,
              fun i => (if bitLength n ≤ r then AllArityBitLength.Target.seedImage Y F r n else Y) i.val⟩ ∧
          (∀ u, u<t → ((AllArityCursor.machine k).run u c).state≠
            SmallIngress.producer.seqRight (Cursor.machine k) (Cursor.q k 329)) ∧
          (r<bitLength n → S<Cursor.Target.M k n z) ∧
          (bitLength n≤r → ∀ (fit : F+5*r+n+7 < tapeLength R B), ∃ d, d≤1024*(n+r+1)^2*(F+5*r+n+9) ∧
            (AllArityCursor.machine k).run (t+d) c=SmallIngress.producer.seqEmbedRight (Cursor.machine k)
              ⟨Cursor.q k (if n≤r then 411 else 798+93*k),
                ⟨if n≤r then F+2*r+n+4 else F+1,
                  by exact lt_of_le_of_lt (by split <;> omega : (if n≤r then F+2*r+n+4 else F+1) ≤ F+5*r+n+7) fit⟩,
                fun i => Target.image (AllArityBitLength.Target.seedImage Y F r n) L n F r (bitLength n)
                  (if n≤r then n else 0) (if n≤r then 0 else r) 0 (if n≤r then 0 else r+1) i.val⟩ ∧
            t+d≤268435456*(R+1)^4 ∧
            (∀ u, u<d → ((AllArityCursor.machine k).run (t+u) c).state.val<699) ∧
            (r<n → S<Cursor.Target.M k n z))) := by
  exact accepted_first_product k hk
theorem check_canonical_outcome (k : Nat) (hk : 0 < k) (n : Fin 3) (b : Bool) :
    let codec:=treeCircuitWitnessCodec (thresholdPoly k)
    let a:=treeMCSPPrefixM codec n.val
    let m:=Pnp3.ComplexityInterfaces.certificateLength a 1
    let x:=zeroPrefixQueryValue codec n.val (fun _ => b)
    ∃ w : Bitstring m, PartAEndpoint.thresholdContentWitnessRelation k a m x w=true ∧
      ∃ t, t ≤ 268435456*(pairLength a m+1)^4 ∧
        let c:=initialConfig (AllArityCursor.machine k) (FixedRawLengthFence.allocation (pairLength a m)) (encodePair x w)
        (((AllArityCursor.machine k).run t c).state=SmallIngress.producer.seqRight (Cursor.machine k) (Cursor.q k 411) ∨
         ((AllArityCursor.machine k).run t c).state=SmallIngress.producer.seqRight (Cursor.machine k) (Cursor.q k (798+93*k)) ∨
         ((AllArityCursor.machine k).run t c).state=SmallIngress.producer.seqRight (Cursor.machine k) (Cursor.q k 250) ∨
         ((AllArityCursor.machine k).run t c).state=SmallIngress.producer.seqRight (Cursor.machine k) (Cursor.q k 304) ∨
         ((AllArityCursor.machine k).run t c).state=SmallIngress.producer.seqRight (Cursor.machine k) (Cursor.mReady k ⟨2,by decide⟩)) := by
  exact canonical_outcome k hk n b
#check (Target.image : (Nat → Option Bool) → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Option Bool)
#check (Target.Cap : Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Prop)
#check (Target.FullRaw : Nat → Prop)
#check (Target.FirstProduct : Nat → Nat → Nat → Nat → Nat → Nat → Nat → (Nat → Option Bool) → Prop)
#check (Target.RawProduct : Nat → Prop)
#check (instructions : Nat → List Nat)
#print axioms Target.image
#print axioms Target.Cap
#print axioms Target.FullRaw
#print axioms Target.FirstProduct
#print axioms Target.RawProduct
#print axioms instructions
#print axioms phase_row
#print axioms check_phase_row
#print axioms first_product
#print axioms check_first_product
#print axioms accepted_first_product
#print axioms check_accepted_first_product
#print axioms canonical_outcome
#print axioms check_canonical_outcome
/-- Full independent equation mirror for the compiler-generated public equation. -/
theorem check_instructions_equation (k : Nat) : instructions k = [
  (2972), (2975), (2978), (2979), (2982), (2978), (3430), 364, (2991),
  (2998), (2991), (2994), (3006), (3009), (3012), (3016), (3009), (3012),
  (3024), (3027), (3030), (3034), (3027), (3030), (3042), (3045), (3048),
  (3052), (3045), (3048), (3060), (3063), (3066), 361, (3072), 367,
  (3069), 364, (3084), (3088), 364, (3084), (3096), (3099), (3102),
  (3350), (3113), (3102), (3115), (3110), (3113), (3125), (3128), (3131),
  (3125), (3137), (3131), (3143), (3146), (3149), (3151), (3146), (3149),
  (3161), (3164), (3167), (3169), (3164), (3167), (3179), (3182), (3185),
  (3187), (3182), (3185), (3197), (3200), (3203), (3205), (3200), (3203),
  (3215), (3218), (3221), (3231), (3228), (3221), (3241), (3225), (3228),
  (3628), (3234), (3237), (3249), (3252), (3255), (3259), (3252), (3255),
  (3267), (3270), (3273), (3277), (3270), (3273), (3285), (3288), (3291),
  (3295), (3288), (3291), (3303), (3306), (3309), (3313), (3306), (3309),
  (3321), (3324), (3327), 361, (3333), 367, (3330), 364, (3345),
  (3088), 364, (3345), (3358), (3353), (3353), (3368), (3371), (3374),
  (3368), (3380), (3374), (3386), (3389), (3392), (3394), (3389), (3392),
  (3404), (3407), (3410), (3412), (3407), (3410), (3422), (3425), (3428),
  (2962), (3425), (3428), (3440), (3443), (3446), (3448), (3443), (3446),
  (3458), (3461), (3464), (3465), (3468), (3464), (3610), 364, (3477),
  (3484), (3477), (3480), (3492), (3495), (3498), (3502), (3495), (3498),
  (3512), (3515), (3518), (3528), (3525), (3518), (3538), (3522), (3525),
  (3556), (3531), (3534), (3548), (3551), (3554), (3448), (3551), (3554),
  (3564), (3567), (3570), (3574), (3567), (3570), (3582), (3585), (3588),
  (3592), (3585), (3588), (3600), (3603), (3606), (7183+837*k), (3603), (3606),
  (3618), (3621), (3624), (3700), (3621), (3624), (3636), (3639), (3642),
  (3646), (3639), (3642), (3654), (3657), (3660), (3664), (3657), (3660),
  (3672), (3675), (3678), (3682), (3675), (3678), (3690), (3693), (3696),
  (7183+837*k), (3693), (3696)
] := by
  exact instructions.eq_1 k
#print axioms instructions.eq_1
#print axioms check_instructions_equation
end CappedWeight
