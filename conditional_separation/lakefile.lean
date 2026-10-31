import Lake
open Lake DSL

package conditional_separation

require mathlib from git "https://github.com/leanprover-community/mathlib4" @ "1a5c8fe51b870f5c4ffd6fe44936e09a776d8f3e"

lean_lib ProofCore where
  srcDir := "core"
  globs := #[
    .andSubmodules `AcceptedBody,
    .andSubmodules `AllArityBitLength,
    .andSubmodules `AllArityCounted,
    .andSubmodules `AllArityCursor,
    .andSubmodules `AllArityWorkspace,
    .andSubmodules `BitLengthDriver,
    .andSubmodules `Body,
    .andSubmodules `BodyIngress,
    .andSubmodules `CanonicalLeaf,
    .andSubmodules `CappedWeight,
    .andSubmodules `CappedWorkspace,
    .andSubmodules `CarryReadyCompletion,
    .andSubmodules `CarryWindow,
    .andSubmodules `CertificateGuardClosure,
    .andSubmodules `Complexity,
    .andSubmodules `ConnectedRead,
    .andSubmodules `Core,
    .andSubmodules `Cursor,
    .andSubmodules `FullBodyClosure,
    .andSubmodules `FullFinalClosure,
    .andSubmodules `FullIngressClosure,
    .andSubmodules `FullWeight,
    .andSubmodules `GammaSupport,
    .andSubmodules `IngressAllocation,
    .andSubmodules `IngressRepair,
    .andSubmodules `InputRead,
    .andSubmodules `Models,
    .andSubmodules `NormalClockClosure,
    .andSubmodules `NormalFinalClosure,
    .andSubmodules `PhysicalCallerClosure,
    .andSubmodules `Pnp4,
    .andSubmodules `PostWeight,
    .andSubmodules `PowerDriver,
    .andSubmodules `RawCallerClosure,
    .andSubmodules `RawFrontier,
    .andSubmodules `RawPrelude,
    .andSubmodules `RepairedFrontier,
    .andSubmodules `RuntimeBitLength,
    .andSubmodules `SerializedBody,
    .andSubmodules `SerializedBodyCompletion,
    .andSubmodules `SerializedBodyRefinement,
    .andSubmodules `SerializedPositiveBody,
    .andSubmodules `SmallIngress,
    .andSubmodules `SmallOrbit,
    .andSubmodules `StandardTMBridgeClosure,
    .andSubmodules `Stream,
    .andSubmodules `SuffixCap,
    .andSubmodules `TotalIngressClosure,
    .andSubmodules `UniformClassBridgeClosure,
    .andSubmodules `VirtualFinalClosure,
    .andSubmodules `VirtualLeaf,
    .andSubmodules `VirtualReady,
    .andSubmodules `VirtualReadyPins]

@[default_target]
lean_lib ConditionalSeparation where
  globs := #[.andSubmodules `ConditionalSeparation]
  moreLeanArgs := #["-DwarningAsError=true"]
