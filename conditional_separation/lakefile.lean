import Lake
open Lake DSL

package conditional_separation

require mathlib from git "https://github.com/leanprover-community/mathlib4" @ "1a5c8fe51b870f5c4ffd6fe44936e09a776d8f3e"

lean_lib ProofCore where
  srcDir := "core"
  globs := #[
    .submodules `AcceptedBody,
    .submodules `AllArityBitLength,
    .submodules `AllArityCounted,
    .submodules `AllArityCursor,
    .submodules `AllArityWorkspace,
    .submodules `BitLengthDriver,
    .submodules `Body,
    .submodules `BodyIngress,
    .submodules `CanonicalLeaf,
    .submodules `CappedWeight,
    .submodules `CappedWorkspace,
    .submodules `CarryReadyCompletion,
    .submodules `CarryWindow,
    .submodules `CertificateGuardClosure,
    .submodules `Complexity,
    .submodules `ConnectedRead,
    .submodules `Core,
    .submodules `Cursor,
    .submodules `FullBodyClosure,
    .submodules `FullFinalClosure,
    .submodules `FullIngressClosure,
    .submodules `FullWeight,
    .submodules `GammaSupport,
    .submodules `IngressAllocation,
    .submodules `IngressRepair,
    .submodules `InputRead,
    .submodules `Models,
    .submodules `NormalClockClosure,
    .submodules `NormalFinalClosure,
    .submodules `PhysicalCallerClosure,
    .submodules `Pnp4,
    .submodules `PostWeight,
    .submodules `PowerDriver,
    .submodules `RawCallerClosure,
    .submodules `RawFrontier,
    .submodules `RawPrelude,
    .submodules `RepairedFrontier,
    .submodules `RuntimeBitLength,
    .submodules `SerializedBody,
    .submodules `SerializedBodyCompletion,
    .submodules `SerializedBodyRefinement,
    .submodules `SerializedPositiveBody,
    .submodules `SmallIngress,
    .submodules `SmallOrbit,
    .submodules `StandardTMBridgeClosure,
    .submodules `Stream,
    .submodules `SuffixCap,
    .submodules `TotalIngressClosure,
    .submodules `UniformClassBridgeClosure,
    .submodules `VirtualFinalClosure,
    .submodules `VirtualLeaf,
    .submodules `VirtualReady,
    .submodules `VirtualReadyPins]

@[default_target]
lean_lib ConditionalSeparation where
  globs := #[.andSubmodules `ConditionalSeparation]
  moreLeanArgs := #["-DwarningAsError=true"]
