import Tests.PartAR1ConsumerTypes
import FullFinalClosure.Surface
import NormalClockClosure.Pins
import Tests.PartABodySurfaceTests
import Tests.PartAInputReadSurfaceTests
import Tests.PartACanonicalRootTests
import Tests.PartACanonicalApiSmoke
import Tests.PartACanonicalPublicInventory
import Tests.PartACanonicalSupport

/-! Infrastructure: literal, explicitly typed links to exact existing private
owners. No original module/name/number is copied or renamed; no proof graph is
reconstructed. Each value is one existing constant checked against this type. -/
set_option autoImplicit false
-- Exact private ABI: _private.AllArityBitLength.Rows.0.AllArityBitLength.decode_row.match_1; owner AllArityBitLength.Rows.
noncomputable abbrev PartACanonical.PrivateABI.a0001.{u_1} :
(motive : Option.{0} Bool → Sort u_1) →
  (b : Option.{0} Bool) →
    (Unit → motive Option.none.{0}) →
      (Unit → motive (Option.some.{0} Bool.false)) → (Unit → motive (Option.some.{0} Bool.true)) → motive b :=
  @(partA_private% "_private.AllArityBitLength.Rows.0.AllArityBitLength.decode_row.match_1" owner% "AllArityBitLength.Rows")

-- Exact private ABI: _private.BitLengthDriver.Rows.0.BitLengthDriver.decode_row.match_1; owner BitLengthDriver.Rows.
noncomputable abbrev PartACanonical.PrivateABI.a0002.{u_1} :
(motive : Option.{0} Bool → Sort u_1) →
  (b : Option.{0} Bool) →
    (Unit → motive Option.none.{0}) →
      (Unit → motive (Option.some.{0} Bool.false)) → (Unit → motive (Option.some.{0} Bool.true)) → motive b :=
  @(partA_private% "_private.BitLengthDriver.Rows.0.BitLengthDriver.decode_row.match_1" owner% "BitLengthDriver.Rows")

-- Exact private ABI: _private.BodyIngress.Machine.0.BodyIngress.nativeCount; owner BodyIngress.Machine.
noncomputable abbrev PartACanonical.PrivateABI.a0003 :
Nat :=
  @(partA_private% "_private.BodyIngress.Machine.0.BodyIngress.nativeCount" owner% "BodyIngress.Machine")

-- Exact private ABI: _private.CappedWeight.Rows.0.CappedWeight.decode_row.match_1; owner CappedWeight.Rows.
noncomputable abbrev PartACanonical.PrivateABI.a0004.{u_1} :
(motive : Option.{0} Bool → Sort u_1) →
  (b : Option.{0} Bool) →
    (Unit → motive Option.none.{0}) →
      (Unit → motive (Option.some.{0} Bool.false)) → (Unit → motive (Option.some.{0} Bool.true)) → motive b :=
  @(partA_private% "_private.CappedWeight.Rows.0.CappedWeight.decode_row.match_1" owner% "CappedWeight.Rows")

-- Exact private ABI: _private.CappedWorkspace.Kernel.0.CappedWorkspace.Node; owner CappedWorkspace.Kernel.
noncomputable abbrev PartACanonical.PrivateABI.a0006 :
Nat → Type :=
  @(partA_private% "_private.CappedWorkspace.Kernel.0.CappedWorkspace.Node" owner% "CappedWorkspace.Kernel")

-- Exact private ABI: _private.CappedWorkspace.Kernel.0.CappedWorkspace.Edge; owner CappedWorkspace.Kernel.
noncomputable abbrev PartACanonical.PrivateABI.a0005 :
(k : Nat) →
  Nat →
    PartACanonical.PrivateABI.a0006 k →
      PartACanonical.PrivateABI.a0006 k → Prop :=
  @(partA_private% "_private.CappedWorkspace.Kernel.0.CappedWorkspace.Edge" owner% "CappedWorkspace.Kernel")

-- Exact private ABI: _private.CappedWorkspace.Kernel.0.CappedWorkspace.Node.head; owner CappedWorkspace.Kernel.
noncomputable abbrev PartACanonical.PrivateABI.a0007 :
{k : Nat} → PartACanonical.PrivateABI.a0006 k → Nat :=
  @(partA_private% "_private.CappedWorkspace.Kernel.0.CappedWorkspace.Node.head" owner% "CappedWorkspace.Kernel")

-- Exact private ABI: _private.CappedWorkspace.Kernel.0.CappedWorkspace.Path; owner CappedWorkspace.Kernel.
noncomputable abbrev PartACanonical.PrivateABI.a0008 :
(k : Nat) →
  Nat →
    Nat →
      PartACanonical.PrivateABI.a0006 k →
        PartACanonical.PrivateABI.a0006 k → Prop :=
  @(partA_private% "_private.CappedWorkspace.Kernel.0.CappedWorkspace.Path" owner% "CappedWorkspace.Kernel")

-- Exact private ABI: _private.CappedWorkspace.Kernel.0.CappedWorkspace.Path.append; owner CappedWorkspace.Kernel.
noncomputable abbrev PartACanonical.PrivateABI.a0009 :
∀ {k P t u : Nat} {c d e : PartACanonical.PrivateABI.a0006 k},
  PartACanonical.PrivateABI.a0008 k P t c d →
    PartACanonical.PrivateABI.a0008 k P u d e →
      PartACanonical.PrivateABI.a0008 k P (HAdd.hAdd.{0, 0, 0} t u) c e :=
  @(partA_private% "_private.CappedWorkspace.Kernel.0.CappedWorkspace.Path.append" owner% "CappedWorkspace.Kernel")

-- Exact private ABI: _private.CappedWorkspace.Kernel.0.CappedWorkspace.Path.bounds; owner CappedWorkspace.Kernel.
noncomputable abbrev PartACanonical.PrivateABI.a0010 :
∀ {k P t : Nat} {c d : PartACanonical.PrivateABI.a0006 k},
  PartACanonical.PrivateABI.a0008 k P t c d →
    And (LE.le.{0} (PartACanonical.PrivateABI.a0007 c) P)
      (LE.le.{0} (PartACanonical.PrivateABI.a0007 d) P) :=
  @(partA_private% "_private.CappedWorkspace.Kernel.0.CappedWorkspace.Path.bounds" owner% "CappedWorkspace.Kernel")

-- Exact private ABI: _private.CappedWorkspace.Kernel.0.CappedWorkspace.embed; owner CappedWorkspace.Kernel.
noncomputable abbrev PartACanonical.PrivateABI.a0013 :
{k N B : Nat} →
  (c : PartACanonical.PrivateABI.a0006 k) →
    LT.lt.{0} (PartACanonical.PrivateABI.a0007 c)
        (Pnp3.Complexity.Uniform.V1.tapeLength N B) →
      Pnp3.Complexity.Uniform.V1.Config (Cursor.stateCount k) N B :=
  @(partA_private% "_private.CappedWorkspace.Kernel.0.CappedWorkspace.embed" owner% "CappedWorkspace.Kernel")

-- Exact private ABI: _private.CappedWorkspace.Kernel.0.CappedWorkspace.Path.execute; owner CappedWorkspace.Kernel.
noncomputable abbrev PartACanonical.PrivateABI.a0011 :
∀ {k N B P t : Nat} {c d : PartACanonical.PrivateABI.a0006 k}
  (h : PartACanonical.PrivateABI.a0008 k P t c d)
  (hp : LT.lt.{0} P (Pnp3.Complexity.Uniform.V1.tapeLength N B)),
  Eq.{1}
    (Pnp3.Complexity.Uniform.V1.UniformTM.run (Cursor.machine k) t
      (PartACanonical.PrivateABI.a0013 c
        (lt_of_le_of_lt.{0} (And.left (PartACanonical.PrivateABI.a0010 h)) hp)))
    (PartACanonical.PrivateABI.a0013 d
      (lt_of_le_of_lt.{0} (And.right (PartACanonical.PrivateABI.a0010 h)) hp)) :=
  @(partA_private% "_private.CappedWorkspace.Kernel.0.CappedWorkspace.Path.execute" owner% "CappedWorkspace.Kernel")

-- Exact private ABI: _private.CappedWorkspace.Kernel.0.CappedWorkspace.Path.first; owner CappedWorkspace.Kernel.
noncomputable abbrev PartACanonical.PrivateABI.a0012 :
∀ {k N B P t : Nat} {c d : PartACanonical.PrivateABI.a0006 k}
  (path : PartACanonical.PrivateABI.a0008 k P t c d)
  (hp : LT.lt.{0} P (Pnp3.Complexity.Uniform.V1.tapeLength N B)) (u : Nat),
  LT.lt.{0} u t →
    LT.lt.{0}
      (Fin.val
        (Pnp3.Complexity.Uniform.V1.Config.state
          (Pnp3.Complexity.Uniform.V1.UniformTM.run (Cursor.machine k) u
            (PartACanonical.PrivateABI.a0013 c
              (lt_of_le_of_lt.{0} (And.left (PartACanonical.PrivateABI.a0010 path))
                hp)))))
      (OfNat.ofNat.{0} (nat_lit 201)) :=
  @(partA_private% "_private.CappedWorkspace.Kernel.0.CappedWorkspace.Path.first" owner% "CappedWorkspace.Kernel")

-- Exact private ABI: _private.CappedWorkspace.Rows.0.CappedWorkspace.decode_row.match_1; owner CappedWorkspace.Rows.
noncomputable abbrev PartACanonical.PrivateABI.a0014.{u_1} :
(motive : Option.{0} Bool → Sort u_1) →
  (b : Option.{0} Bool) →
    (Unit → motive Option.none.{0}) →
      (Unit → motive (Option.some.{0} Bool.false)) → (Unit → motive (Option.some.{0} Bool.true)) → motive b :=
  @(partA_private% "_private.CappedWorkspace.Rows.0.CappedWorkspace.decode_row.match_1" owner% "CappedWorkspace.Rows")

-- Exact private ABI: _private.CarryReadyCompletion.Closure.0.CarryReadyCompletion.normal_extension._proof_1; owner CarryReadyCompletion.Closure.
noncomputable abbrev PartACanonical.PrivateABI.a0015 :
∀ (k : Nat) {a m : Nat}
  (pr :
    (q : Nat) ×
      Pnp4.Frontier.ContractExpansion.PrefixInput
        (Pnp4.Frontier.treeMCSPSearchProblem (Pnp4.Frontier.ContractExpansion.thresholdPoly k)
          (Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
            (Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
              (Pnp4.Frontier.ContractExpansion.thresholdPoly k))))
        (Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
          (Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec (Pnp4.Frontier.ContractExpansion.thresholdPoly k))
          q))
  (z : Nat),
  Not
      (LE.le.{0}
        (HAdd.hAdd.{0, 0, 0}
          (HAdd.hAdd.{0, 0, 0}
            (HAdd.hAdd.{0, 0, 0}
              (Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.fencePos
                (Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength a m))
              (HSub.hSub.{0, 0, 0} (HAdd.hAdd.{0, 0, 0} a m)
                (Min.min.{0}
                  (HAdd.hAdd.{0, 0, 0}
                    (HAdd.hAdd.{0, 0, 0} (OfNat.ofNat.{0} (nat_lit 9))
                      (HMul.hMul.{0, 0, 0} (OfNat.ofNat.{0} (nat_lit 2)) z))
                    (HPow.hPow.{0, 0, 0} (OfNat.ofNat.{0} (nat_lit 2))
                      (Pnp4.Frontier.ContractExpansion.PrefixInput.n (Sigma.snd.{0, 0} pr))))
                  (HAdd.hAdd.{0, 0, 0} a m))))
            (Pnp4.Frontier.ContractExpansion.PrefixInput.n (Sigma.snd.{0, 0} pr)))
          (OfNat.ofNat.{0} (nat_lit 3)))
        (HAdd.hAdd.{0, 0, 0}
          (HAdd.hAdd.{0, 0, 0}
            (HAdd.hAdd.{0, 0, 0}
              (Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.fencePos
                (Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength a m))
              (HMul.hMul.{0, 0, 0} (OfNat.ofNat.{0} (nat_lit 5))
                (HSub.hSub.{0, 0, 0} (HAdd.hAdd.{0, 0, 0} a m)
                  (Min.min.{0}
                    (HAdd.hAdd.{0, 0, 0}
                      (HAdd.hAdd.{0, 0, 0} (OfNat.ofNat.{0} (nat_lit 9))
                        (HMul.hMul.{0, 0, 0} (OfNat.ofNat.{0} (nat_lit 2)) z))
                      (HPow.hPow.{0, 0, 0} (OfNat.ofNat.{0} (nat_lit 2))
                        (Pnp4.Frontier.ContractExpansion.PrefixInput.n (Sigma.snd.{0, 0} pr))))
                    (HAdd.hAdd.{0, 0, 0} a m)))))
            (Pnp4.Frontier.ContractExpansion.PrefixInput.n (Sigma.snd.{0, 0} pr)))
          (OfNat.ofNat.{0} (nat_lit 7)))) →
    False :=
  @(partA_private% "_private.CarryReadyCompletion.Closure.0.CarryReadyCompletion.normal_extension._proof_1" owner% "CarryReadyCompletion.Closure")

-- Exact private ABI: _private.CarryReadyCompletion.Closure.0.CarryReadyCompletion.normal_extension._proof_2; owner CarryReadyCompletion.Closure.
noncomputable abbrev PartACanonical.PrivateABI.a0016 :
∀ (k : Nat) {a m : Nat}
  (pr :
    (q : Nat) ×
      Pnp4.Frontier.ContractExpansion.PrefixInput
        (Pnp4.Frontier.treeMCSPSearchProblem (Pnp4.Frontier.ContractExpansion.thresholdPoly k)
          (Pnp4.Frontier.TreeMCSPSearchWitnessEncoding.ofCodec
            (Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
              (Pnp4.Frontier.ContractExpansion.thresholdPoly k))))
        (Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM
          (Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec (Pnp4.Frontier.ContractExpansion.thresholdPoly k))
          q))
  (z : Nat),
  Not
      (LE.le.{0}
        (HAdd.hAdd.{0, 0, 0}
          (Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.fencePos
            (Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength a m))
          (OfNat.ofNat.{0} (nat_lit 1)))
        (HAdd.hAdd.{0, 0, 0}
          (HAdd.hAdd.{0, 0, 0}
            (HAdd.hAdd.{0, 0, 0}
              (Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.fencePos
                (Pnp3.Complexity.Uniform.V1.PairEncoding.pairLength a m))
              (HMul.hMul.{0, 0, 0} (OfNat.ofNat.{0} (nat_lit 5))
                (HSub.hSub.{0, 0, 0} (HAdd.hAdd.{0, 0, 0} a m)
                  (Min.min.{0}
                    (HAdd.hAdd.{0, 0, 0}
                      (HAdd.hAdd.{0, 0, 0} (OfNat.ofNat.{0} (nat_lit 9))
                        (HMul.hMul.{0, 0, 0} (OfNat.ofNat.{0} (nat_lit 2)) z))
                      (HPow.hPow.{0, 0, 0} (OfNat.ofNat.{0} (nat_lit 2))
                        (Pnp4.Frontier.ContractExpansion.PrefixInput.n (Sigma.snd.{0, 0} pr))))
                    (HAdd.hAdd.{0, 0, 0} a m)))))
            (Pnp4.Frontier.ContractExpansion.PrefixInput.n (Sigma.snd.{0, 0} pr)))
          (OfNat.ofNat.{0} (nat_lit 7)))) →
    False :=
  @(partA_private% "_private.CarryReadyCompletion.Closure.0.CarryReadyCompletion.normal_extension._proof_2" owner% "CarryReadyCompletion.Closure")

-- Exact private ABI: _private.CertificateGuardClosure.Machine.0.CertificateGuardClosure.qa; owner CertificateGuardClosure.Machine.
noncomputable abbrev PartACanonical.PrivateABI.a0017 :
Fin (OfNat.ofNat.{0} (nat_lit 67)) :=
  @(partA_private% "_private.CertificateGuardClosure.Machine.0.CertificateGuardClosure.qa" owner% "CertificateGuardClosure.Machine")

-- Exact private ABI: _private.CertificateGuardClosure.Machine.0.CertificateGuardClosure.qr; owner CertificateGuardClosure.Machine.
noncomputable abbrev PartACanonical.PrivateABI.a0018 :
Fin (OfNat.ofNat.{0} (nat_lit 67)) :=
  @(partA_private% "_private.CertificateGuardClosure.Machine.0.CertificateGuardClosure.qr" owner% "CertificateGuardClosure.Machine")

-- Exact private ABI: _private.CertificateGuardClosure.Machine.0.CertificateGuardClosure.raw; owner CertificateGuardClosure.Machine.
noncomputable abbrev PartACanonical.PrivateABI.a0019 :
Fin (OfNat.ofNat.{0} (nat_lit 67)) →
  Option.{0} Bool →
    Prod.{0, 0} (Fin (OfNat.ofNat.{0} (nat_lit 67))) (Prod.{0, 0} (Option.{0} Bool) Pnp3.Complexity.Uniform.V1.Move) :=
  @(partA_private% "_private.CertificateGuardClosure.Machine.0.CertificateGuardClosure.raw" owner% "CertificateGuardClosure.Machine")

-- Exact private ABI: _private.Cursor.Machine.0.Cursor.decode; owner Cursor.Machine.
noncomputable abbrev PartACanonical.PrivateABI.a0020 :
(k : Nat) →
  Array.{0} Nat →
    Fin (Cursor.stateCount k) →
      Option.{0} Bool →
        Prod.{0, 0} (Fin (Cursor.stateCount k)) (Prod.{0, 0} (Option.{0} Bool) Pnp3.Complexity.Uniform.V1.Move) :=
  @(partA_private% "_private.Cursor.Machine.0.Cursor.decode" owner% "Cursor.Machine")

-- Exact private ABI: _private.Cursor.Machine.0.Cursor.program; owner Cursor.Machine.
noncomputable abbrev PartACanonical.PrivateABI.a0021 :
Nat → Array.{0} Nat :=
  @(partA_private% "_private.Cursor.Machine.0.Cursor.program" owner% "Cursor.Machine")

-- Exact private ABI: _private.Cursor.Proof.0.Cursor.er; owner Cursor.Proof.
noncomputable abbrev PartACanonical.PrivateABI.a0022 :
(k : Nat) →
  Fin (Pnp3.Complexity.Uniform.V1.UniformTM.stateCount Stream.rawMachine) →
    Fin (Pnp3.Complexity.Uniform.V1.UniformTM.stateCount (Cursor.rawMachine k)) :=
  @(partA_private% "_private.Cursor.Proof.0.Cursor.er" owner% "Cursor.Proof")

-- Exact private ABI: _private.Cursor.Proof.0.Cursor.er_initial; owner Cursor.Proof.
noncomputable abbrev PartACanonical.PrivateABI.a0023 :
∀ (k : Nat) {N B : Nat} (y : Pnp3.Complexity.Uniform.V1.Bitstring N),
  Eq.{1}
    (Pnp3.Complexity.Uniform.V1.Config.mk
      (PartACanonical.PrivateABI.a0022 k
        (Pnp3.Complexity.Uniform.V1.Config.state (Pnp3.Complexity.Uniform.V1.initialConfig Stream.rawMachine B y)))
      (Pnp3.Complexity.Uniform.V1.Config.head (Pnp3.Complexity.Uniform.V1.initialConfig Stream.rawMachine B y))
      (Pnp3.Complexity.Uniform.V1.Config.tape (Pnp3.Complexity.Uniform.V1.initialConfig Stream.rawMachine B y)))
    (Pnp3.Complexity.Uniform.V1.initialConfig (Cursor.rawMachine k) B y) :=
  @(partA_private% "_private.Cursor.Proof.0.Cursor.er_initial" owner% "Cursor.Proof")

-- Exact private ABI: _private.Cursor.Proof.0.Cursor.er_val; owner Cursor.Proof.
noncomputable abbrev PartACanonical.PrivateABI.a0024 :
∀ (k : Nat) (s : Fin (Pnp3.Complexity.Uniform.V1.UniformTM.stateCount Stream.rawMachine)),
  Eq.{1} (Fin.val (PartACanonical.PrivateABI.a0022 k s)) (Fin.val s) :=
  @(partA_private% "_private.Cursor.Proof.0.Cursor.er_val" owner% "Cursor.Proof")

-- Exact private ABI: _private.Cursor.Proof.0.Cursor.exits; owner Cursor.Proof.
noncomputable abbrev PartACanonical.PrivateABI.a0025 :
Fin (Pnp3.Complexity.Uniform.V1.UniformTM.stateCount Stream.rawMachine) → Prop :=
  @(partA_private% "_private.Cursor.Proof.0.Cursor.exits" owner% "Cursor.Proof")

-- Exact private ABI: _private.Cursor.Proof.0.Cursor.old_inert; owner Cursor.Proof.
noncomputable abbrev PartACanonical.PrivateABI.a0026 :
∀ {N B : Nat}
  (c : Pnp3.Complexity.Uniform.V1.Config (Pnp3.Complexity.Uniform.V1.UniformTM.stateCount Stream.rawMachine) N B),
  PartACanonical.PrivateABI.a0025 (Pnp3.Complexity.Uniform.V1.Config.state c) →
    Eq.{1} (Pnp3.Complexity.Uniform.V1.UniformTM.stepConfig Stream.rawMachine c) c :=
  @(partA_private% "_private.Cursor.Proof.0.Cursor.old_inert" owner% "Cursor.Proof")

-- Exact private ABI: _private.Cursor.Proof.0.Cursor.raw_row; owner Cursor.Proof.
noncomputable abbrev PartACanonical.PrivateABI.a0027 :
∀ (k : Nat) (s : Fin (Pnp3.Complexity.Uniform.V1.UniformTM.stateCount Stream.rawMachine)),
  Not (PartACanonical.PrivateABI.a0025 s) →
    ∀ (b : Option.{0} Bool),
      Eq.{1} (Pnp3.Complexity.Uniform.V1.UniformTM.step (Cursor.rawMachine k) (PartACanonical.PrivateABI.a0022 k s) b)
        (Prod.mk.{0, 0}
          (PartACanonical.PrivateABI.a0022 k
            (Prod.fst.{0, 0} (Pnp3.Complexity.Uniform.V1.UniformTM.step Stream.rawMachine s b)))
          (Prod.snd.{0, 0} (Pnp3.Complexity.Uniform.V1.UniformTM.step Stream.rawMachine s b))) :=
  @(partA_private% "_private.Cursor.Proof.0.Cursor.raw_row" owner% "Cursor.Proof")

-- Exact private ABI: _private.PhysicalCallerClosure.CallerTarget.0.PhysicalCallerClosure.rowImage; owner PhysicalCallerClosure.CallerTarget.
noncomputable abbrev PartACanonical.PrivateABI.a0028 :
(Nat → Option.{0} Bool) →
  (S : Nat) → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → (Fin S → Bool) → Nat → Option.{0} Bool :=
  @(partA_private% "_private.PhysicalCallerClosure.CallerTarget.0.PhysicalCallerClosure.rowImage" owner% "PhysicalCallerClosure.CallerTarget")

-- Exact private ABI: _private.RuntimeBitLength.Rows.0.RuntimeBitLength.decode_row.match_1; owner RuntimeBitLength.Rows.
noncomputable abbrev PartACanonical.PrivateABI.a0029.{u_1} :
(motive : Option.{0} Bool → Sort u_1) →
  (b : Option.{0} Bool) →
    (Unit → motive Option.none.{0}) →
      (Unit → motive (Option.some.{0} Bool.false)) → (Unit → motive (Option.some.{0} Bool.true)) → motive b :=
  @(partA_private% "_private.RuntimeBitLength.Rows.0.RuntimeBitLength.decode_row.match_1" owner% "RuntimeBitLength.Rows")

-- Exact private ABI: _private.SerializedBodyCompletion.Case.0.SerializedBodyCompletion.zero_semantics.match_1; owner SerializedBodyCompletion.Case.
noncomputable abbrev PartACanonical.PrivateABI.a0030.{u_1} :
(n : Nat) →
  (motive : Prod.{0, 0} (Pnp3.Models.Circuit n) (List.{0} Bool) → Sort u_1) →
    (__discr : Prod.{0, 0} (Pnp3.Models.Circuit n) (List.{0} Bool)) →
      ((c : Pnp3.Models.Circuit n) → (tail : List.{0} Bool) → motive (Prod.mk.{0, 0} c tail)) → motive __discr :=
  @(partA_private% "_private.SerializedBodyCompletion.Case.0.SerializedBodyCompletion.zero_semantics.match_1" owner% "SerializedBodyCompletion.Case")

-- Exact private ABI: _private.SmallIngress.Runtime.0.SmallIngress.Node; owner SmallIngress.Runtime.
noncomputable abbrev PartACanonical.PrivateABI.a0032 :
Pnp3.Complexity.Uniform.V1.UniformTM → Type :=
  @(partA_private% "_private.SmallIngress.Runtime.0.SmallIngress.Node" owner% "SmallIngress.Runtime")

-- Exact private ABI: _private.SmallIngress.Runtime.0.SmallIngress.Edge; owner SmallIngress.Runtime.
noncomputable abbrev PartACanonical.PrivateABI.a0031 :
{M : Pnp3.Complexity.Uniform.V1.UniformTM} →
  Nat → PartACanonical.PrivateABI.a0032 M → PartACanonical.PrivateABI.a0032 M → Prop :=
  @(partA_private% "_private.SmallIngress.Runtime.0.SmallIngress.Edge" owner% "SmallIngress.Runtime")

-- Exact private ABI: _private.SmallIngress.Runtime.0.SmallIngress.Node.head; owner SmallIngress.Runtime.
noncomputable abbrev PartACanonical.PrivateABI.a0033 :
{M : Pnp3.Complexity.Uniform.V1.UniformTM} → PartACanonical.PrivateABI.a0032 M → Nat :=
  @(partA_private% "_private.SmallIngress.Runtime.0.SmallIngress.Node.head" owner% "SmallIngress.Runtime")

-- Exact private ABI: _private.SmallIngress.Runtime.0.SmallIngress.Old; owner SmallIngress.Runtime.
noncomputable abbrev PartACanonical.PrivateABI.a0034 :
Pnp3.Complexity.Uniform.V1.UniformTM :=
  @(partA_private% "_private.SmallIngress.Runtime.0.SmallIngress.Old" owner% "SmallIngress.Runtime")

-- Exact private ABI: _private.SmallIngress.Runtime.0.SmallIngress.Path; owner SmallIngress.Runtime.
noncomputable abbrev PartACanonical.PrivateABI.a0035 :
{M : Pnp3.Complexity.Uniform.V1.UniformTM} →
  Nat →
    Nat →
      PartACanonical.PrivateABI.a0032 M → PartACanonical.PrivateABI.a0032 M → Prop :=
  @(partA_private% "_private.SmallIngress.Runtime.0.SmallIngress.Path" owner% "SmallIngress.Runtime")

-- Exact private ABI: _private.SmallIngress.Runtime.0.SmallIngress.Path.append; owner SmallIngress.Runtime.
noncomputable abbrev PartACanonical.PrivateABI.a0036 :
∀ {M : Pnp3.Complexity.Uniform.V1.UniformTM} {P t u : Nat}
  {c d e : PartACanonical.PrivateABI.a0032 M},
  PartACanonical.PrivateABI.a0035 P t c d →
    PartACanonical.PrivateABI.a0035 P u d e →
      PartACanonical.PrivateABI.a0035 P (HAdd.hAdd.{0, 0, 0} t u) c e :=
  @(partA_private% "_private.SmallIngress.Runtime.0.SmallIngress.Path.append" owner% "SmallIngress.Runtime")

-- Exact private ABI: _private.SmallIngress.Runtime.0.SmallIngress.Path.bounds; owner SmallIngress.Runtime.
noncomputable abbrev PartACanonical.PrivateABI.a0037 :
∀ {M : Pnp3.Complexity.Uniform.V1.UniformTM} {P t : Nat} {c d : PartACanonical.PrivateABI.a0032 M},
  PartACanonical.PrivateABI.a0035 P t c d →
    And (LE.le.{0} (PartACanonical.PrivateABI.a0033 c) P)
      (LE.le.{0} (PartACanonical.PrivateABI.a0033 d) P) :=
  @(partA_private% "_private.SmallIngress.Runtime.0.SmallIngress.Path.bounds" owner% "SmallIngress.Runtime")

-- Exact private ABI: _private.SmallIngress.Runtime.0.SmallIngress.embed; owner SmallIngress.Runtime.
noncomputable abbrev PartACanonical.PrivateABI.a0039 :
{M : Pnp3.Complexity.Uniform.V1.UniformTM} →
  {N B : Nat} →
    (c : PartACanonical.PrivateABI.a0032 M) →
      LT.lt.{0} (PartACanonical.PrivateABI.a0033 c) (Pnp3.Complexity.Uniform.V1.tapeLength N B) →
        Pnp3.Complexity.Uniform.V1.Config (Pnp3.Complexity.Uniform.V1.UniformTM.stateCount M) N B :=
  @(partA_private% "_private.SmallIngress.Runtime.0.SmallIngress.embed" owner% "SmallIngress.Runtime")

-- Exact private ABI: _private.SmallIngress.Runtime.0.SmallIngress.Path.execute; owner SmallIngress.Runtime.
noncomputable abbrev PartACanonical.PrivateABI.a0038 :
∀ {M : Pnp3.Complexity.Uniform.V1.UniformTM} {N B P t : Nat} {c d : PartACanonical.PrivateABI.a0032 M}
  (h : PartACanonical.PrivateABI.a0035 P t c d)
  (hp : LT.lt.{0} P (Pnp3.Complexity.Uniform.V1.tapeLength N B)),
  Eq.{1}
    (Pnp3.Complexity.Uniform.V1.UniformTM.run M t
      (PartACanonical.PrivateABI.a0039 c
        (lt_of_le_of_lt.{0} (And.left (PartACanonical.PrivateABI.a0037 h)) hp)))
    (PartACanonical.PrivateABI.a0039 d
      (lt_of_le_of_lt.{0} (And.right (PartACanonical.PrivateABI.a0037 h)) hp)) :=
  @(partA_private% "_private.SmallIngress.Runtime.0.SmallIngress.Path.execute" owner% "SmallIngress.Runtime")

-- Exact private ABI: _private.SmallIngress.Runtime.0.SmallIngress.raw_tag_old._proof_1; owner SmallIngress.Runtime.
noncomputable abbrev PartACanonical.PrivateABI.a0040 :
∀ {a m : Nat},
  LE.le.{0}
      (HAdd.hAdd.{0, 0, 0}
        (HMul.hMul.{0, 0, 0} (OfNat.ofNat.{0} (nat_lit 2))
          (HAdd.hAdd.{0, 0, 0}
            (HAdd.hAdd.{0, 0, 0} (HMul.hMul.{0, 0, 0} (OfNat.ofNat.{0} (nat_lit 2)) a) (OfNat.ofNat.{0} (nat_lit 1)))
            m))
        (OfNat.ofNat.{0} (nat_lit 2)))
      (Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation
        (HAdd.hAdd.{0, 0, 0}
          (HAdd.hAdd.{0, 0, 0} (HMul.hMul.{0, 0, 0} (OfNat.ofNat.{0} (nat_lit 2)) a) (OfNat.ofNat.{0} (nat_lit 1)))
          m)) →
    LE.le.{0} (OfNat.ofNat.{0} (nat_lit 8)) (HAdd.hAdd.{0, 0, 0} a m) →
      Not
          (LT.lt.{0} (OfNat.ofNat.{0} (nat_lit 8))
            (HAdd.hAdd.{0, 0, 0}
              (HAdd.hAdd.{0, 0, 0}
                (HAdd.hAdd.{0, 0, 0}
                  (HAdd.hAdd.{0, 0, 0} (HMul.hMul.{0, 0, 0} (OfNat.ofNat.{0} (nat_lit 2)) a)
                    (OfNat.ofNat.{0} (nat_lit 1)))
                  m)
                (Pnp3.Complexity.Uniform.V1.FixedRawLengthFence.allocation
                  (HAdd.hAdd.{0, 0, 0}
                    (HAdd.hAdd.{0, 0, 0} (HMul.hMul.{0, 0, 0} (OfNat.ofNat.{0} (nat_lit 2)) a)
                      (OfNat.ofNat.{0} (nat_lit 1)))
                    m)))
              (OfNat.ofNat.{0} (nat_lit 1)))) →
        False :=
  @(partA_private% "_private.SmallIngress.Runtime.0.SmallIngress.raw_tag_old._proof_1" owner% "SmallIngress.Runtime")

-- Exact private ABI: _private.SmallOrbit.Runtime.0.SmallOrbit.Node; owner SmallOrbit.Runtime.
noncomputable abbrev PartACanonical.PrivateABI.a0042 :
Pnp3.Complexity.Uniform.V1.UniformTM → Type :=
  @(partA_private% "_private.SmallOrbit.Runtime.0.SmallOrbit.Node" owner% "SmallOrbit.Runtime")

-- Exact private ABI: _private.SmallOrbit.Runtime.0.SmallOrbit.Edge; owner SmallOrbit.Runtime.
noncomputable abbrev PartACanonical.PrivateABI.a0041 :
{M : Pnp3.Complexity.Uniform.V1.UniformTM} →
  Nat → PartACanonical.PrivateABI.a0042 M → PartACanonical.PrivateABI.a0042 M → Prop :=
  @(partA_private% "_private.SmallOrbit.Runtime.0.SmallOrbit.Edge" owner% "SmallOrbit.Runtime")

-- Exact private ABI: _private.SmallOrbit.Runtime.0.SmallOrbit.Node.head; owner SmallOrbit.Runtime.
noncomputable abbrev PartACanonical.PrivateABI.a0043 :
{M : Pnp3.Complexity.Uniform.V1.UniformTM} → PartACanonical.PrivateABI.a0042 M → Nat :=
  @(partA_private% "_private.SmallOrbit.Runtime.0.SmallOrbit.Node.head" owner% "SmallOrbit.Runtime")

-- Exact private ABI: _private.SmallOrbit.Runtime.0.SmallOrbit.Path; owner SmallOrbit.Runtime.
noncomputable abbrev PartACanonical.PrivateABI.a0044 :
{M : Pnp3.Complexity.Uniform.V1.UniformTM} →
  Nat → Nat → PartACanonical.PrivateABI.a0042 M → PartACanonical.PrivateABI.a0042 M → Prop :=
  @(partA_private% "_private.SmallOrbit.Runtime.0.SmallOrbit.Path" owner% "SmallOrbit.Runtime")

-- Exact private ABI: _private.SmallOrbit.Runtime.0.SmallOrbit.Path.append; owner SmallOrbit.Runtime.
noncomputable abbrev PartACanonical.PrivateABI.a0045 :
∀ {M : Pnp3.Complexity.Uniform.V1.UniformTM} {P t u : Nat} {c d e : PartACanonical.PrivateABI.a0042 M},
  PartACanonical.PrivateABI.a0044 P t c d →
    PartACanonical.PrivateABI.a0044 P u d e →
      PartACanonical.PrivateABI.a0044 P (HAdd.hAdd.{0, 0, 0} t u) c e :=
  @(partA_private% "_private.SmallOrbit.Runtime.0.SmallOrbit.Path.append" owner% "SmallOrbit.Runtime")

-- Exact private ABI: _private.SmallOrbit.Runtime.0.SmallOrbit.Path.bounds; owner SmallOrbit.Runtime.
noncomputable abbrev PartACanonical.PrivateABI.a0046 :
∀ {M : Pnp3.Complexity.Uniform.V1.UniformTM} {P t : Nat} {c d : PartACanonical.PrivateABI.a0042 M},
  PartACanonical.PrivateABI.a0044 P t c d →
    And (LE.le.{0} (PartACanonical.PrivateABI.a0043 c) P)
      (LE.le.{0} (PartACanonical.PrivateABI.a0043 d) P) :=
  @(partA_private% "_private.SmallOrbit.Runtime.0.SmallOrbit.Path.bounds" owner% "SmallOrbit.Runtime")

-- Exact private ABI: _private.SmallOrbit.Runtime.0.SmallOrbit.embed; owner SmallOrbit.Runtime.
noncomputable abbrev PartACanonical.PrivateABI.a0048 :
{M : Pnp3.Complexity.Uniform.V1.UniformTM} →
  {N B : Nat} →
    (c : PartACanonical.PrivateABI.a0042 M) →
      LT.lt.{0} (PartACanonical.PrivateABI.a0043 c) (Pnp3.Complexity.Uniform.V1.tapeLength N B) →
        Pnp3.Complexity.Uniform.V1.Config (Pnp3.Complexity.Uniform.V1.UniformTM.stateCount M) N B :=
  @(partA_private% "_private.SmallOrbit.Runtime.0.SmallOrbit.embed" owner% "SmallOrbit.Runtime")

-- Exact private ABI: _private.SmallOrbit.Runtime.0.SmallOrbit.Path.execute; owner SmallOrbit.Runtime.
noncomputable abbrev PartACanonical.PrivateABI.a0047 :
∀ {M : Pnp3.Complexity.Uniform.V1.UniformTM} {N B P t : Nat} {c d : PartACanonical.PrivateABI.a0042 M}
  (h : PartACanonical.PrivateABI.a0044 P t c d)
  (hp : LT.lt.{0} P (Pnp3.Complexity.Uniform.V1.tapeLength N B)),
  Eq.{1}
    (Pnp3.Complexity.Uniform.V1.UniformTM.run M t
      (PartACanonical.PrivateABI.a0048 c
        (lt_of_le_of_lt.{0} (And.left (PartACanonical.PrivateABI.a0046 h)) hp)))
    (PartACanonical.PrivateABI.a0048 d
      (lt_of_le_of_lt.{0} (And.right (PartACanonical.PrivateABI.a0046 h)) hp)) :=
  @(partA_private% "_private.SmallOrbit.Runtime.0.SmallOrbit.Path.execute" owner% "SmallOrbit.Runtime")

-- Exact private ABI: _private.StandardTMBridgeClosure.Machine.0.StandardTMBridgeClosure.phase; owner StandardTMBridgeClosure.Machine.
noncomputable abbrev PartACanonical.PrivateABI.a0049 :
Pnp3.Complexity.Uniform.V1.Move → Fin (OfNat.ofNat.{0} (nat_lit 4)) :=
  @(partA_private% "_private.StandardTMBridgeClosure.Machine.0.StandardTMBridgeClosure.phase" owner% "StandardTMBridgeClosure.Machine")

-- Exact private ABI: _private.StandardTMBridgeClosure.Machine.0.StandardTMBridgeClosure.phase._proof_1; owner StandardTMBridgeClosure.Machine.
noncomputable abbrev PartACanonical.PrivateABI.a0050 :
NeZero.{0} (HAdd.hAdd.{0, 0, 0} (OfNat.ofNat.{0} (nat_lit 3)) (OfNat.ofNat.{0} (nat_lit 1))) :=
  @(partA_private% "_private.StandardTMBridgeClosure.Machine.0.StandardTMBridgeClosure.phase._proof_1" owner% "StandardTMBridgeClosure.Machine")

-- Exact private ABI: _private.Stream.Kernel.0.Stream.Arena; owner Stream.Kernel.
noncomputable abbrev PartACanonical.PrivateABI.a0051 :
(Nat → Option.{0} Bool) → Nat → Nat → Nat → Nat → Nat → Prop :=
  @(partA_private% "_private.Stream.Kernel.0.Stream.Arena" owner% "Stream.Kernel")

-- Exact private ABI: _private.Stream.Kernel.0.Stream.Node; owner Stream.Kernel.
noncomputable abbrev PartACanonical.PrivateABI.a0053 :
Type :=
  @(partA_private% "_private.Stream.Kernel.0.Stream.Node" owner% "Stream.Kernel")

-- Exact private ABI: _private.Stream.Kernel.0.Stream.Edge; owner Stream.Kernel.
noncomputable abbrev PartACanonical.PrivateABI.a0052 :
Nat → PartACanonical.PrivateABI.a0053 → PartACanonical.PrivateABI.a0053 → Prop :=
  @(partA_private% "_private.Stream.Kernel.0.Stream.Edge" owner% "Stream.Kernel")

-- Exact private ABI: _private.Stream.Kernel.0.Stream.Node.head; owner Stream.Kernel.
noncomputable abbrev PartACanonical.PrivateABI.a0054 :
PartACanonical.PrivateABI.a0053 → Nat :=
  @(partA_private% "_private.Stream.Kernel.0.Stream.Node.head" owner% "Stream.Kernel")

-- Exact private ABI: _private.Stream.Kernel.0.Stream.Path; owner Stream.Kernel.
noncomputable abbrev PartACanonical.PrivateABI.a0055 :
Nat → Nat → PartACanonical.PrivateABI.a0053 → PartACanonical.PrivateABI.a0053 → Prop :=
  @(partA_private% "_private.Stream.Kernel.0.Stream.Path" owner% "Stream.Kernel")

-- Exact private ABI: _private.Stream.Kernel.0.Stream.Path.append; owner Stream.Kernel.
noncomputable abbrev PartACanonical.PrivateABI.a0056 :
∀ {P t u : Nat} {c d e : PartACanonical.PrivateABI.a0053},
  PartACanonical.PrivateABI.a0055 P t c d →
    PartACanonical.PrivateABI.a0055 P u d e → PartACanonical.PrivateABI.a0055 P (HAdd.hAdd.{0, 0, 0} t u) c e :=
  @(partA_private% "_private.Stream.Kernel.0.Stream.Path.append" owner% "Stream.Kernel")

-- Exact private ABI: _private.Stream.Kernel.0.Stream.Path.bounds; owner Stream.Kernel.
noncomputable abbrev PartACanonical.PrivateABI.a0057 :
∀ {P t : Nat} {c d : PartACanonical.PrivateABI.a0053},
  PartACanonical.PrivateABI.a0055 P t c d →
    And (LE.le.{0} (PartACanonical.PrivateABI.a0054 c) P)
      (LE.le.{0} (PartACanonical.PrivateABI.a0054 d) P) :=
  @(partA_private% "_private.Stream.Kernel.0.Stream.Path.bounds" owner% "Stream.Kernel")

-- Exact private ABI: _private.Stream.Kernel.0.Stream.embed; owner Stream.Kernel.
noncomputable abbrev PartACanonical.PrivateABI.a0059 :
{N B : Nat} →
  (c : PartACanonical.PrivateABI.a0053) →
    LT.lt.{0} (PartACanonical.PrivateABI.a0054 c) (Pnp3.Complexity.Uniform.V1.tapeLength N B) →
      Pnp3.Complexity.Uniform.V1.Config (OfNat.ofNat.{0} (nat_lit 64)) N B :=
  @(partA_private% "_private.Stream.Kernel.0.Stream.embed" owner% "Stream.Kernel")

-- Exact private ABI: _private.Stream.Kernel.0.Stream.Path.execute; owner Stream.Kernel.
noncomputable abbrev PartACanonical.PrivateABI.a0058 :
∀ {N B P t : Nat} {c d : PartACanonical.PrivateABI.a0053} (h : PartACanonical.PrivateABI.a0055 P t c d)
  (hp : LT.lt.{0} P (Pnp3.Complexity.Uniform.V1.tapeLength N B)),
  Eq.{1}
    (Pnp3.Complexity.Uniform.V1.UniformTM.run Stream.machine t
      (PartACanonical.PrivateABI.a0059 c
        (lt_of_le_of_lt.{0} (And.left (PartACanonical.PrivateABI.a0057 h)) hp)))
    (PartACanonical.PrivateABI.a0059 d
      (lt_of_le_of_lt.{0} (And.right (PartACanonical.PrivateABI.a0057 h)) hp)) :=
  @(partA_private% "_private.Stream.Kernel.0.Stream.Path.execute" owner% "Stream.Kernel")

-- Exact private ABI: _private.Stream.Kernel.0.Stream.ended; owner Stream.Kernel.
noncomputable abbrev PartACanonical.PrivateABI.a0060 :
(Nat → Option.{0} Bool) → Nat → Nat → Nat → Nat → Nat → PartACanonical.PrivateABI.a0053 :=
  @(partA_private% "_private.Stream.Kernel.0.Stream.ended" owner% "Stream.Kernel")

-- Exact private ABI: _private.Stream.Kernel.0.Stream.entry; owner Stream.Kernel.
noncomputable abbrev PartACanonical.PrivateABI.a0061 :
(Nat → Option.{0} Bool) → Nat → Nat → Nat → Nat → Nat → PartACanonical.PrivateABI.a0053 :=
  @(partA_private% "_private.Stream.Kernel.0.Stream.entry" owner% "Stream.Kernel")

-- Exact private ABI: _private.Stream.Kernel.0.Stream.step_row; owner Stream.Kernel.
noncomputable abbrev PartACanonical.PrivateABI.a0062 :
∀ (U : Nat → Option.{0} Bool) (S z n A F r : Nat),
  PartACanonical.PrivateABI.a0051 U S z n A F →
    LT.lt.{0} r
        (HSub.hSub.{0, 0, 0}
          (HSub.hSub.{0, 0, 0} F
            (HAdd.hAdd.{0, 0, 0} (HAdd.hAdd.{0, 0, 0} (HAdd.hAdd.{0, 0, 0} S z) n) (OfNat.ofNat.{0} (nat_lit 3))))
          (OfNat.ofNat.{0} (nat_lit 1))) →
      ∃ (t : Nat),
        And
          (LE.le.{0} t
            (HAdd.hAdd.{0, 0, 0} (HMul.hMul.{0, 0, 0} (OfNat.ofNat.{0} (nat_lit 8)) F) (OfNat.ofNat.{0} (nat_lit 16))))
          (PartACanonical.PrivateABI.a0055 F t (PartACanonical.PrivateABI.a0061 U S z n A r)
            (ite.{1} (Eq.{1} (Prod.snd.{0, 0} (Body.inc (Body.iterBits (List.replicate.{0} n Bool.false) r))) Bool.true)
              (PartACanonical.PrivateABI.a0060 U S z n A (HAdd.hAdd.{0, 0, 0} r (OfNat.ofNat.{0} (nat_lit 1))))
              (PartACanonical.PrivateABI.a0061 U S z n A (HAdd.hAdd.{0, 0, 0} r (OfNat.ofNat.{0} (nat_lit 1)))))) :=
  @(partA_private% "_private.Stream.Kernel.0.Stream.step_row" owner% "Stream.Kernel")

-- Exact private ABI: _private.SuffixCap.Kernel.0.SuffixCap.Node; owner SuffixCap.Kernel.
noncomputable abbrev PartACanonical.PrivateABI.a0064 :
Nat → Type :=
  @(partA_private% "_private.SuffixCap.Kernel.0.SuffixCap.Node" owner% "SuffixCap.Kernel")

-- Exact private ABI: _private.SuffixCap.Kernel.0.SuffixCap.Edge; owner SuffixCap.Kernel.
noncomputable abbrev PartACanonical.PrivateABI.a0063 :
(k : Nat) → Nat → PartACanonical.PrivateABI.a0064 k → PartACanonical.PrivateABI.a0064 k → Prop :=
  @(partA_private% "_private.SuffixCap.Kernel.0.SuffixCap.Edge" owner% "SuffixCap.Kernel")

-- Exact private ABI: _private.SuffixCap.Kernel.0.SuffixCap.Node.head; owner SuffixCap.Kernel.
noncomputable abbrev PartACanonical.PrivateABI.a0065 :
{k : Nat} → PartACanonical.PrivateABI.a0064 k → Nat :=
  @(partA_private% "_private.SuffixCap.Kernel.0.SuffixCap.Node.head" owner% "SuffixCap.Kernel")

-- Exact private ABI: _private.SuffixCap.Kernel.0.SuffixCap.Path; owner SuffixCap.Kernel.
noncomputable abbrev PartACanonical.PrivateABI.a0066 :
(k : Nat) →
  Nat → Nat → PartACanonical.PrivateABI.a0064 k → PartACanonical.PrivateABI.a0064 k → Prop :=
  @(partA_private% "_private.SuffixCap.Kernel.0.SuffixCap.Path" owner% "SuffixCap.Kernel")

-- Exact private ABI: _private.SuffixCap.Kernel.0.SuffixCap.Path.append; owner SuffixCap.Kernel.
noncomputable abbrev PartACanonical.PrivateABI.a0067 :
∀ {k P t u : Nat} {c d e : PartACanonical.PrivateABI.a0064 k},
  PartACanonical.PrivateABI.a0066 k P t c d →
    PartACanonical.PrivateABI.a0066 k P u d e →
      PartACanonical.PrivateABI.a0066 k P (HAdd.hAdd.{0, 0, 0} t u) c e :=
  @(partA_private% "_private.SuffixCap.Kernel.0.SuffixCap.Path.append" owner% "SuffixCap.Kernel")

-- Exact private ABI: _private.SuffixCap.Kernel.0.SuffixCap.Path.bounds; owner SuffixCap.Kernel.
noncomputable abbrev PartACanonical.PrivateABI.a0068 :
∀ {k P t : Nat} {c d : PartACanonical.PrivateABI.a0064 k},
  PartACanonical.PrivateABI.a0066 k P t c d →
    And (LE.le.{0} (PartACanonical.PrivateABI.a0065 c) P)
      (LE.le.{0} (PartACanonical.PrivateABI.a0065 d) P) :=
  @(partA_private% "_private.SuffixCap.Kernel.0.SuffixCap.Path.bounds" owner% "SuffixCap.Kernel")

-- Exact private ABI: _private.SuffixCap.Kernel.0.SuffixCap.embed; owner SuffixCap.Kernel.
noncomputable abbrev PartACanonical.PrivateABI.a0070 :
{k N B : Nat} →
  (c : PartACanonical.PrivateABI.a0064 k) →
    LT.lt.{0} (PartACanonical.PrivateABI.a0065 c) (Pnp3.Complexity.Uniform.V1.tapeLength N B) →
      Pnp3.Complexity.Uniform.V1.Config (Cursor.stateCount k) N B :=
  @(partA_private% "_private.SuffixCap.Kernel.0.SuffixCap.embed" owner% "SuffixCap.Kernel")

-- Exact private ABI: _private.SuffixCap.Kernel.0.SuffixCap.Path.execute; owner SuffixCap.Kernel.
noncomputable abbrev PartACanonical.PrivateABI.a0069 :
∀ {k N B P t : Nat} {c d : PartACanonical.PrivateABI.a0064 k}
  (h : PartACanonical.PrivateABI.a0066 k P t c d)
  (hp : LT.lt.{0} P (Pnp3.Complexity.Uniform.V1.tapeLength N B)),
  Eq.{1}
    (Pnp3.Complexity.Uniform.V1.UniformTM.run (Cursor.machine k) t
      (PartACanonical.PrivateABI.a0070 c
        (lt_of_le_of_lt.{0} (And.left (PartACanonical.PrivateABI.a0068 h)) hp)))
    (PartACanonical.PrivateABI.a0070 d
      (lt_of_le_of_lt.{0} (And.right (PartACanonical.PrivateABI.a0068 h)) hp)) :=
  @(partA_private% "_private.SuffixCap.Kernel.0.SuffixCap.Path.execute" owner% "SuffixCap.Kernel")

-- Exact private ABI: _private.SuffixCap.Raw.0.SuffixCap.raw_prefix; owner SuffixCap.Raw.
noncomputable abbrev PartACanonical.PrivateABI.a0071 :
∀ (k : Nat) {N B : Nat} (y : Pnp3.Complexity.Uniform.V1.Bitstring N) (T t : Nat),
  Eq.{1}
      (Fin.val
        (Pnp3.Complexity.Uniform.V1.Config.state
          (Pnp3.Complexity.Uniform.V1.UniformTM.run Stream.rawMachine T
            (Pnp3.Complexity.Uniform.V1.initialConfig Stream.rawMachine B y))))
      (OfNat.ofNat.{0} (nat_lit 314)) →
    Eq.{1}
        (Fin.val
          (Pnp3.Complexity.Uniform.V1.Config.state
            (Pnp3.Complexity.Uniform.V1.UniformTM.run (Cursor.rawMachine k) t
              (Pnp3.Complexity.Uniform.V1.initialConfig (Cursor.rawMachine k) B y))))
        (OfNat.ofNat.{0} (nat_lit 314)) →
      (∀ (u : Nat),
          LT.lt.{0} u t →
            And
              (Ne.{1}
                (Fin.val
                  (Pnp3.Complexity.Uniform.V1.Config.state
                    (Pnp3.Complexity.Uniform.V1.UniformTM.run (Cursor.rawMachine k) u
                      (Pnp3.Complexity.Uniform.V1.initialConfig (Cursor.rawMachine k) B y))))
                (OfNat.ofNat.{0} (nat_lit 313)))
              (Ne.{1}
                (Fin.val
                  (Pnp3.Complexity.Uniform.V1.Config.state
                    (Pnp3.Complexity.Uniform.V1.UniformTM.run (Cursor.rawMachine k) u
                      (Pnp3.Complexity.Uniform.V1.initialConfig (Cursor.rawMachine k) B y))))
                (OfNat.ofNat.{0} (nat_lit 314)))) →
        ∀ (v : Nat),
          LT.lt.{0} v t →
            LT.lt.{0}
              (Fin.val
                (Pnp3.Complexity.Uniform.V1.Config.state
                  (Pnp3.Complexity.Uniform.V1.UniformTM.run (Cursor.rawMachine k) v
                    (Pnp3.Complexity.Uniform.V1.initialConfig (Cursor.rawMachine k) B y))))
              (OfNat.ofNat.{0} (nat_lit 320)) :=
  @(partA_private% "_private.SuffixCap.Raw.0.SuffixCap.raw_prefix" owner% "SuffixCap.Raw")
