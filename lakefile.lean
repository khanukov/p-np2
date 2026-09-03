import Lake
open Lake DSL

package pnp3

require mathlib from git "https://github.com/leanprover-community/mathlib4" @ "v4.22.0-rc2"
require fact_locality_lift from "./Facts/LocalityLift"
require fact_sunflower from "./Facts/Sunflower"

@[default_target]
lean_lib PnP3 where
  srcDir := "pnp3"
  globs := #[
    Glob.one `Core.BooleanBasics,
    Glob.one `Core.PDTPartial,
    Glob.one `Core.PDT,
    Glob.one `Core.Atlas,
    Glob.one `Core.SAL_Core,
    Glob.one `Core.ShrinkageWitness,
    Glob.one `Counting.BinomialBounds,
    Glob.one `Counting.CapacityGap,
    Glob.one `Counting.Count_EasyFuncs,
    Glob.one `Counting.CircuitCounting,
    Glob.one `Counting.ShannonCounting,
    Glob.one `Counting.Atlas_to_LB_Core,
    Glob.one `AC0.Formulas,
    -- Multi-switching core: include the shared restriction model plus
    -- the canonical trace helper so downstream modules can import it
    -- without missing `.olean` artifacts.
    Glob.one `AC0.MultiSwitching.Restrictions,
    Glob.one `AC0.MultiSwitching.Duality,
    Glob.one `AC0.MultiSwitching.Definitions,
    Glob.one `AC0.MultiSwitching.BadEvents,
    Glob.one `AC0.MultiSwitching.CanonicalTrace,
    Glob.one `AC0.MultiSwitching.CanonicalDT,
    -- Parameter block for Step 3.2 numerics/encodings.
    Glob.one `AC0.MultiSwitching.Params,
    Glob.one `AC0.MultiSwitching.Numerics,
    Glob.one `AC0.MultiSwitching.Trace,
    Glob.one `AC0.MultiSwitching.TraceBridge,
    Glob.one `AC0.MultiSwitching.CommonBad,
    Glob.one `AC0.MultiSwitching.EncodingCommon,
    Glob.one `AC0.MultiSwitching.CommonBad_Func,
    Glob.one `AC0.MultiSwitching.EncodingCommon_Func,
    Glob.one `AC0.MultiSwitching.Decides,
    Glob.one `AC0.MultiSwitching.Atoms,
    Glob.one `AC0.MultiSwitching.FuncCNF,
    Glob.one `AC0.MultiSwitching.DecidesAtoms,
    Glob.one `AC0.MultiSwitching.CommonCCDT_Func,
    Glob.one `AC0.MultiSwitching.CommonCCDT,
    Glob.one `AC0.MultiSwitching.Counting,
    Glob.one `AC0.MultiSwitching.Encoding,
    Glob.one `AC0.MultiSwitching.ShrinkageFromGood,
    Glob.one `AC0.MultiSwitching.Main,
    Glob.one `Complexity.Promise,
    Glob.one `Complexity.Interfaces,
    Glob.one `Complexity.DagCompose,
    -- P1b-0 (2026-09-03), infrastructure only: generic fixed-width bundle
    -- composition with exact shared-gate recurrence and direct Boolean DAG
    -- gadgets.  No uniform-machine or Ppoly bridge is introduced here.
    Glob.one `Complexity.DagBundleCompose,
    Glob.one `Complexity.DagGadgets,
    -- P1a (2026-09-03), versioned uniform-P infrastructure: finite machine
    -- data, same-budget execution/decision semantics, polynomial clocks, and
    -- literal machines.  This is intentionally independent of the frozen
    -- TMVerifier and legacy encoding/simulation stacks.
    Glob.one `Complexity.Uniform.V1.Machine,
    -- P1b-1 (2026-09-03), direct fixed-width layout and initial bundle only.
    -- No transition/run compiler, polynomial simulation, or Ppoly bridge.
    Glob.one `Complexity.Uniform.V1.CircuitEncoding,
    -- P1b-2/P1b-3 (2026-09-03), encoded semantics, direct shared step bundle,
    -- and linear per-step gate cap.
    Glob.one `Complexity.Uniform.V1.StepKernel,
    Glob.one `Complexity.Uniform.V1.StepBundle,
    -- Final P1b bridge (2026-09-03): fixed clocked run circuits and the
    -- versioned UniformP subset of canonical PpolyDAG theorem only.
    Glob.one `Complexity.Uniform.V1.PpolyDAG,
    Glob.one `Complexity.Uniform.V1.PolynomialTime,
    Glob.one `Complexity.Uniform.V1.Examples,
    -- P1c (2026-09-03), versioned countability/no-length-advice boundary:
    -- explicit finite-machine coding and a direct length-only diagonal.
    Glob.one `Complexity.Uniform.V1.Countability,
    Glob.one `Complexity.Uniform.V1.PpolyDAGExamples,
    Glob.one `Complexity.Uniform.V1.StepKernelExamples,
    Glob.one `Complexity.Uniform.V1.StepBundleExamples,
    Glob.one `Complexity.PsubsetPpolyInternal.Bitstring,
    Glob.one `Complexity.TMVerifier.GapMCSPVerifier,
    Glob.one `Complexity.PsubsetPpolyInternal.TuringEncoding,
    Glob.one `Complexity.TMVerifier.TuringToolkit.Foundation,
    Glob.one `Complexity.TMVerifier.TuringToolkit.BinaryCounter,
    Glob.one `Complexity.TMVerifier.TuringToolkit.Encoding,
    Glob.one `Complexity.TMVerifier.TuringToolkit.AtomicPrograms,
    Glob.one `Complexity.TMVerifier.TuringToolkit.UnaryAtOffset,
    Glob.one `Complexity.TMVerifier.TuringToolkit.CopyAtOffset,
    Glob.one `Complexity.TMVerifier.TuringToolkit.CombineAtOffset,
    Glob.one `Complexity.TMVerifier.TuringToolkit.GateWrappers,
    Glob.one `Complexity.TMVerifier.TuringToolkit.ConstStatePhasedProgram,
    Glob.one `Complexity.TMVerifier.TuringToolkit.ConstStatePhasedProgramInitialConfig,
    Glob.one `Complexity.TMVerifier.TuringToolkit.ConstStatePhasedProgramSeqRun,
    Glob.one `Complexity.TMVerifier.TuringToolkit.ConstStatePhasedProgramAccepts,
    Glob.one `Complexity.TMVerifier.TuringToolkit.ConstStatePhasedProgramConditionalAccept,
    Glob.one `Complexity.TMVerifier.TuringToolkit.ConstStatePhasedProgramConditionalAcceptExamples,
    Glob.one `Complexity.TMVerifier.TuringToolkit.ConstStatePhasedProgramSeqListRun,
    Glob.one `Complexity.TMVerifier.TuringToolkit.ConstStatePhasedProgramSeqRunExamples,
    Glob.one `Complexity.TMVerifier.TuringToolkit.ConstStatePhasedProgramSeqListRunExamples,
    Glob.one `Complexity.TMVerifier.TuringToolkit.ConstStatePhasedStepBridge,
    Glob.one `Complexity.TMVerifier.TuringToolkit.ConstStatePhasedStepBridgeExamples,
    -- Blocker-1 infrastructure: the dependency-closed generic fixed-width
    -- frame-scanner kernel.  `Codec` is the 4-bit alphabet layer, `Kernel`
    -- proves the macrostep and the exact list-scan induction generically in
    -- the program/alphabet/mode/context, and `Probe` is a non-T1 instance
    -- that witnesses the genericity.  None of the three imports any T1
    -- module; `FrameScannerT1` (below `TrueUniformSeek`) is the T1 instance.
    Glob.one `Complexity.TMVerifier.TuringToolkit.FrameScannerCodec,
    Glob.one `Complexity.TMVerifier.TuringToolkit.FrameScannerKernel,
    Glob.one `Complexity.TMVerifier.TuringToolkit.FrameScannerProbe,
    -- Reverse/write half of the same kernel: right-to-left frame scanning,
    -- four-cell frame replacement, and the S3a non-T1 mixed-boundary probe.
    Glob.one `Complexity.TMVerifier.TuringToolkit.FrameScannerReverse,
    Glob.one `Complexity.TMVerifier.TuringToolkit.FrameScannerWrite,
    Glob.one `Complexity.TMVerifier.TuringToolkit.FrameScannerWriteCtx,
    Glob.one `Complexity.TMVerifier.TuringToolkit.FrameScannerReverseProbe,
    -- Mutation half of the same kernel: leftward writer, seek-until-marker
    -- and S3a mixed-boundary drivers, the exact thirteen-step rewrite cycle,
    -- and a non-T1 probe.
    Glob.one `Complexity.TMVerifier.TuringToolkit.FrameScannerWriteLeft,
    Glob.one `Complexity.TMVerifier.TuringToolkit.FrameScannerSeek,
    -- GN-E2-1a (2026-09-02), infrastructure only: a context-derived
    -- rightward writer and one-program source-restoring frame shuttle.
    Glob.one `Complexity.TMVerifier.TuringToolkit.FrameShuttle,
    Glob.one `Complexity.TMVerifier.TuringToolkit.FrameShuttleProbe,
    Glob.one `Complexity.TMVerifier.TuringToolkit.FrameRewriteCycle,
    Glob.one `Complexity.TMVerifier.TuringToolkit.FrameRewriteCycleProbe,
    Glob.one `Complexity.TMVerifier.TuringToolkit.RowConsistencyCheck,
    Glob.one `Complexity.TMVerifier.TuringToolkit.TrueUniformSeekEncoding,
    Glob.one `Complexity.TMVerifier.TuringToolkit.TrueUniformSeek,
    Glob.one `Complexity.TMVerifier.TuringToolkit.FrameScannerT1,
    Glob.one `Complexity.TMVerifier.TuringToolkit.TrueUniformSeekValidation,
    Glob.one `Complexity.TMVerifier.TuringToolkit.TrueUniformSeekTerminalControl,
    Glob.one `Complexity.TMVerifier.TuringToolkit.TrueUniformSeekMutation,
    Glob.one `Complexity.TMVerifier.TuringToolkit.TrueUniformSeekMutationLoop,
    Glob.one `Complexity.TMVerifier.TuringToolkit.TrueUniformSeekMutationLoopExamples,
    -- T1b-C: the seek-loop driver (induction, success tail, terminal split).
    Glob.one `Complexity.TMVerifier.TuringToolkit.TrueUniformSeekMutationDriver,
    Glob.one `Complexity.TMVerifier.TuringToolkit.TrueUniformSeekMutationDriverExamples,
    -- T1c-2: terminal execution (repair pass, output write, the three
    -- exact terminal theorems).
    Glob.one `Complexity.TMVerifier.TuringToolkit.TrueUniformSeekTerminal,
    Glob.one `Complexity.TMVerifier.TuringToolkit.TrueUniformSeekTerminalExamples,
    Glob.one `Complexity.TMVerifier.TuringToolkit.TrueUniformSeekSemantics,
    Glob.one `Complexity.TMVerifier.TuringToolkit.TrueUniformSeekSemanticsExamples,
    Glob.one `Complexity.TMVerifier.TuringToolkit.TrueUniformSeekExamples,
    -- T2a, pure layer: the fresh unary one-gate ABI (`GateOneEncoding`), the
    -- four pass-A residual operations of operand 1 (`GateOneResidual`) and the
    -- pure gate semantics on top of both (`GateOneSemantics`).  These are
    -- parser/spec modules only; the fixed control and execution layers are
    -- registered immediately below.
    Glob.one `Complexity.TMVerifier.TuringToolkit.GateOneEncoding,
    Glob.one `Complexity.TMVerifier.TuringToolkit.GateOneResidual,
    Glob.one `Complexity.TMVerifier.TuringToolkit.GateOneSemantics,
    -- GN-1 (2026-08-30), pure infrastructure only: the fixed multi-gate
    -- record/program ABI, exact-image parsers, symbolic region extents, and
    -- sequential `G1Request.spec`/`SLProgram.eval` correspondence.  No
    -- machine, execution, clock, or acceptance layer.
    Glob.one `Complexity.TMVerifier.TuringToolkit.GateNEncoding,
    -- GN-E1a (2026-09-01), infrastructure only: finite lexical discovery
    -- grammar for the self-delimiting GN word.  It stores no counts/indices
    -- and is deliberately weaker than the exact-list parser.
    Glob.one `Complexity.TMVerifier.TuringToolkit.GateNRuntimeGrammar,
    -- GN-E2-1c (2026-09-02): finite strict stage-zero reverse locator grammar.
    Glob.one `Complexity.TMVerifier.TuringToolkit.GateNLocateGrammar,
    Glob.one `Complexity.TMVerifier.TuringToolkit.GateNEncodingExamples,
    -- GN-2 (2026-08-30), pure infrastructure only: canonical partially
    -- committed tape words, exact GN-1-offset views, pure commit, blank
    -- suffix, and tight work-word capacity.  No machine or execution layer.
    Glob.one `Complexity.TMVerifier.TuringToolkit.GateNTapeState,
    Glob.one `Complexity.TMVerifier.TuringToolkit.GateNTapeStateExamples,
    -- GN-3A (2026-08-30), generic local relocation infrastructure: copy
    -- exactly `[0,W+5)`, preserve the ambient tape outside it, and conjugate
    -- tuple-delegated safe G1 steps/runs into an arbitrary target TM.  No GN
    -- machine, controller, clock, copier, trace, or acceptance theorem.
    Glob.one `Complexity.TMVerifier.TuringToolkit.GateNRelocation,
    Glob.one `Complexity.TMVerifier.TuringToolkit.GateNRelocationExamples,
    -- T2a, control layer: one zero-parameter finite control whose forward
    -- table decides the canonical grammar (`GateOneControl`), and that
    -- control as a genuine instance of the generic frame-scanner kernel
    -- (`GateOneScanner`).  Exact validation/rewind is registered next.
    Glob.one `Complexity.TMVerifier.TuringToolkit.GateOneControl,
    Glob.one `Complexity.TMVerifier.TuringToolkit.GateOneScanner,
    -- T2a, execution layer: the exact validation/rewind capstone from the
    -- real initial configuration (`GateOneValidation`) and the per-tag named
    -- examples (`GateOneExamples`).
    Glob.one `Complexity.TMVerifier.TuringToolkit.GateOneValidation,
    -- T1/G1 instances of the generic reverse frame-scanner kernel.
    Glob.one `Complexity.TMVerifier.TuringToolkit.FrameScannerReverseInstances,
    -- T1 instances of the mutation kernel and the exact G1 obligation.
    Glob.one `Complexity.TMVerifier.TuringToolkit.FrameRewriteCycleInstances,
    Glob.one `Complexity.TMVerifier.TuringToolkit.GateOneExamples,
    Glob.one `Complexity.TMVerifier.TuringToolkit.GateOneRouting,
    -- T2b, pass-B execution layer: the exact `TM.runConfig` route capstones
    -- from the real initial configuration (`GateOneReadB`) and the named
    -- per-route examples (`GateOneReadBExamples`).
    Glob.one `Complexity.TMVerifier.TuringToolkit.GateOneReadB,
    Glob.one `Complexity.TMVerifier.TuringToolkit.GateOneReadBExamples,
    -- T2b-3a, the cursor-walk installation scan: the re-pointed
    -- positive-index route from the real initial configuration
    -- (`GateOneInstallScan`) and its concrete literal probe
    -- (`GateOneInstallScanExamples`).
    Glob.one `Complexity.TMVerifier.TuringToolkit.GateOneInstallScan,
    Glob.one `Complexity.TMVerifier.TuringToolkit.GateOneInstallScanExamples,
    -- T2b-3a-2, the successor of the installation-scan endpoint: the exact
    -- probe / latch / cursor-install atoms on arbitrary frame-list contexts
    -- (`GateOneProbeInstall`) and their literal encoded-frame probes
    -- (`GateOneProbeInstallExamples`).  Every run there starts from a
    -- caller-supplied configuration; `bSeek` is the reverse-seek entry shape
    -- executed in `GateOneWalkKernel`.
    Glob.one `Complexity.TMVerifier.TuringToolkit.GateOneProbeInstall,
    Glob.one `Complexity.TMVerifier.TuringToolkit.GateOneProbeInstallExamples,
    -- PR2b1, one normal round of the cursor walk behind `bSeek`: the reverse
    -- seek, the `index ↦ spent` writer, the forward scan, the turn and the
    -- cursor restore as exact atoms on arbitrary frame-list contexts
    -- (`GateOneWalkKernel`) and their literal encoded-frame probes
    -- (`GateOneWalkExamples`).  Every run there is caller-supplied too, and the
    -- exhaustion outcome stops at `bExh`.
    -- PR2b2 adds, to the same two modules, the terminal exhaustion path behind
    -- that handoff: the exhaustion scan, the terminal turn and the terminal
    -- restore into `readAResetStart` with no cursor left on the tape.  Those
    -- runs are caller-supplied too; nothing composes a round with them.
    Glob.one `Complexity.TMVerifier.TuringToolkit.GateOneWalkKernel,
    Glob.one `Complexity.TMVerifier.TuringToolkit.GateOneWalkExamples,
    -- PR3a, the cursor-walk tape invariant `Σ(j)`: the exact layout with its
    -- length, counts and structural facts (`GateOneWalkInvariant`), the
    -- installation into `Σ(0)` from the real initial configuration, the
    -- empty-data out-of-range branch, and their literal probes
    -- (`GateOneWalkInvariantExamples`).
    -- PR3b adds, to the same two modules, **exactly one round** on `Σ(j)` from
    -- a caller-supplied configuration: the normal step `Σ(j) → Σ(j+1)` in
    -- `16j + 37` steps and the out-of-range abort in `16j + 32` steps onto an
    -- intermediate, unrepaired tape.  No induction over `j`, no driver, no loop
    -- clock and no verdict are claimed there.
    Glob.one `Complexity.TMVerifier.TuringToolkit.GateOneWalkInvariant,
    Glob.one `Complexity.TMVerifier.TuringToolkit.GateOneWalkInvariantExamples,
    -- PR3c, the cursor-walk driver: the `8k² + 29k` loop clock, the induction
    -- into `Σ(k)` from the real initial configuration, the successful terminal
    -- at `j = arg2`, the public positive-index operand-2 read and the
    -- aggregated out-of-range branch — both inside the unchanged `g1Clock` and
    -- both on a repair-pending tape — with their literal probes.
    Glob.one `Complexity.TMVerifier.TuringToolkit.GateOneWalkDriver,
    Glob.one `Complexity.TMVerifier.TuringToolkit.GateOneWalkDriverExamples,
    -- Repair-1, the operand-2 repair control and its generic kernel: the
    -- reverse repair scanner, the `spent ↦ index` rewrite cycle, the
    -- four-step rejection of a frame the scan may not cross and the
    -- arbitrary-frame-list repair pass `g1CS_repair_pass_exact`, which is the
    -- capstone of the slice.  The scan crosses only `G1RepairSkip` frames: a
    -- `blank`, a leftover `cursor` and the three reserved codes send it to the
    -- `reject` sink, so a repair run can never rewrite `spent` units behind
    -- malformed tape.
    -- No `g1Advance` frame-table row enters the sweep; the generic runs are
    -- caller-supplied.  Repair-2a adds the sole live `readAResetStart` bridge.
    -- Repair-1b adds `GateOneRepairKernelExamples`, the all-literal probes of
    -- that kernel: the sixteen-frame word for `⟨and, 0, 2, [false, true,
    -- true]⟩` with both operand-2 units consumed, and four exact `G1M` runs on
    -- it — the `13`-step cycle, the `37`-step seek+repair, the `26`-step
    -- two-unit run and the `79`-step whole pass onto the canonical word plus
    -- the trailing blank.  Both scanned lists are pinned against the narrowed
    -- `G1RepairSkip`, and the trailing `blank` is proved to lie outside the
    -- scan.  Those probes are caller-supplied too.
    Glob.one `Complexity.TMVerifier.TuringToolkit.GateOneRepairKernel,
    Glob.one `Complexity.TMVerifier.TuringToolkit.GateOneRepairKernelExamples,
    -- Repair-2a, the request-specific repair driver: the `readAResetStart`
    -- bridge is now a live row, the layout split
    -- `g1RepairLeft`/`g1RepairMid`/`g1RepairTail` instantiates the Repair-1
    -- pass at the real operand-2 word, and `g1CS_repair_sweep_exact` runs it in
    -- `4u + 4a1 + 8a + 9s + 22` steps from the post-read handoff to head `0` in
    -- `readAStart` on a tape that is **bit-for-bit the initial tape**.  Both
    -- successful reads — positive index and `arg2 = 0` — compose with it from
    -- the real `G1M.initialConfig` and meet in the one canonical handoff
    -- `g1ReadAConfig r b`, with `g1BPassASteps`/`g1ZPassASteps` inside the
    -- **unchanged** `g1Clock`.  Both scanned runs are pinned against the
    -- narrowed `G1RepairSkip`; the trailing `blank` lives in the unread tail.
    -- S1b2a also uses the same bridge/kernel as a zero-rewrite rewind for the
    -- re-pointed `input`/`not`/`const` routes.  Its real-initial capstones end
    -- at head-zero `readAStart`; unary preserves `g1Ctx0`, while `const`
    -- carries `g1ResultCtx b`.  S1b2b activates the next `readAStart` step;
    -- S1c instantiates that live entry at ten real-initial literals.  These
    -- repaired endpoints and `bOOB` remain otherwise unchanged.
    -- Repair-2b adds `GateOneRepairExamples`, the all-literal repaired runs
    -- from `G1M.initialConfig` that Repair-2a deferred.
    Glob.one `Complexity.TMVerifier.TuringToolkit.GateOneRepairDriver,
    -- Repair-2b, the literal repaired reads: three exact `G1M` runs from the
    -- **real** `G1M.initialConfig` onto the one canonical handoff
    -- `g1ReadAConfig r true` — `172 = 134 + 38`, `294 = 239 + 55` and
    -- `400 = 328 + 72` steps at `arg2 = 0, 1, 2` — with head, state, `vB`,
    -- endpoint word, initial-tape identity and clock-bound projections,
    -- and both arms of the common capstone.  The zero branch has no net tape
    -- change and an empty rewrite block;
    -- the positive branches consume and restore, witnessed at cells `28`/`32`.
    -- Encoded input length, explicit validation-word extent and
    -- `G1M.tapeLength` are pinned separately (`probe_extents`); the `arg2 = 2`
    -- endpoint words are Repair-1b's, reused verbatim.
    Glob.one `Complexity.TMVerifier.TuringToolkit.GateOneRepairExamples,
    -- The thirteen-step rewrite cycle at the G1 control, kept as an
    -- arbitrary-configuration regression: the bridge, the fourteen-step
    -- composed round and one literal frame-list probe.  Unreachable from
    -- `G1M.initialConfig`.
    Glob.one `Complexity.TMVerifier.TuringToolkit.GateOneIndexRound,
    -- S1b1/S1b2b, the pass-A control ABI and live entry: the twelve pass-A modes, the
    -- residual view of the two spare context bits and the frame rows that join
    -- them are declared in `GateOneControl`/`GateOneRouting`, and
    -- `GateOnePassAControl` executes both caller-supplied atoms and the
    -- real-initial activation.
    -- S1b2b makes `readAStart` the exact two-way dispatch, closes its
    -- predecessors/exits, and composes real unary/constant/binary repaired
    -- routes to `aBof`/`aInstallStart` or `combineStart`, within unchanged
    -- `g1Clock`.  Operand 1 remains unread.
    Glob.one `Complexity.TMVerifier.TuringToolkit.GateOnePassAControl,
    -- S1c, the ten real-initial pass-A entry probes: input/not selection
    -- contexts false/true, both operand-B outcomes for and/or, and both const
    -- literals.  Exact literal steps, heads, states, initial tapes and clock
    -- bounds are pinned, along with separate input/frame-word/capacity extents
    -- and the and-false context-alias/no-wrong-mode regression.
    Glob.one `Complexity.TMVerifier.TuringToolkit.GateOnePassAEntryExamples,
    -- S4 (2026-08-29), live operand-A cursor installation: the former S3b1
    -- scan/probe/writer atoms are composed through the single stationary
    -- `aInstallStart → aInsSeek` entry.  Real unary/binary routes stop at the
    -- completed writer's `aSeekOut .p3` boundary; unary empty-data reaches
    -- `bOOB`.  No seek, mark, iteration or repair step executes.
    Glob.one `Complexity.TMVerifier.TuringToolkit.GateOneAWalkInstallAtoms,
    -- S3b2a/S3b2b (2026-08-29): dormant normal seek/mark/turn/restore plus
    -- the caller-supplied terminal return and cursor cleanup at the exact
    -- `aRepairStart` boundary.  S8b supplies its activation and repair.
    Glob.one `Complexity.TMVerifier.TuringToolkit.GateOneAWalkKernel,
    -- S5 (2026-08-29), the pure operand-A walk invariant foundation:
    -- canonical `Σᴬ(j)` layout, exact post-S4 inhabitance and honest OOB
    -- separation.  No round, driver, repair, result or output theorem.
    Glob.one `Complexity.TMVerifier.TuringToolkit.GateOneAWalkInvariant,
    -- S6 (2026-08-30), exactly one operand-A machine round.  The normal
    -- branch moves `Σᴬ(j)` to `Σᴬ(j+1)`; successor-data OOB stops at `bOOB`,
    -- while operand-index exhaustion stops at the local `aExh` boundary.
    -- No terminal continuation, A-repair, driver or result row is composed.
    Glob.one `Complexity.TMVerifier.TuringToolkit.GateOneAWalkRound,
    -- S7 (2026-08-30), the exact operand-A induction/driver.  The first `m`
    -- normal rounds use the finite sum of S6's own costs, then the exhaustion
    -- and dormant terminal capstones stop at `aExh` or the cursor-free
    -- `aRepairStart` boundary later consumed by S8b; OOB remains separate.
    Glob.one `Complexity.TMVerifier.TuringToolkit.GateOneAWalkDriver,
    -- S8b (2026-08-30), live reject-aware operand-A repair.  The unique
    -- `aRepairStart` door composes S7 terminal cleanup with S8a's canonical
    -- sweep from real unary/successful-binary initial configurations and stops
    -- at the exact canonical `aRepairDone` handoff.
    Glob.one `Complexity.TMVerifier.TuringToolkit.GateOneARepair,
    -- S9 (2026-08-30), dependency-closed five-tag gate-result boundary.
    -- Non-constant
    -- routes execute `aRepairDone → aResultStart → readAStart →
    -- combineStart`; `const` keeps its pass-B bypass.  Exact pure-spec,
    -- OOB-semantic, boundary, literal and unchanged-clock surfaces reach the
    -- exact combine boundary consumed by S10b.
    Glob.one `Complexity.TMVerifier.TuringToolkit.GateOneAResult,
    -- S10a (2026-08-30), reusable G1 output kernel.  A strict
    -- canonical-prefix scan consumes the unique `output false`, turns, and a
    -- four-cell false/true writer installs `output res` before stopping at a
    -- local output-done boundary.  S10b supplies its live entry and exit.
    Glob.one `Complexity.TMVerifier.TuringToolkit.GateOneOutputKernel,
    -- S10b (2026-08-30), live one-gate output and literal acceptance.  The S9
    -- result enters S10a, writes the exact Boolean output, and accepts both
    -- defined false and true results under the unchanged clock.
    Glob.one `Complexity.TMVerifier.TuringToolkit.GateOneOutputAccept,
    -- GN-3B1 + GN-3B2a + GN-3B2b (2026-08-31), infrastructure only: expose
    -- output-done and prove structural arbitrary-canonical validation/rewind
    -- safety through the existing read-B handoff.  No pass-B walk, full-gate
    -- `ShiftRunSafe`, GN controller, copier, clock, or acceptance.
    Glob.one `Complexity.TMVerifier.TuringToolkit.GateOneTraceSafety,
    -- GN-3B2c1 (2026-08-31), infrastructure only: from the merged read-B
    -- handoff, prove structural positive-operand-B route/install safety and one
    -- successful B cursor-walk round.  No arg2 induction, terminal cleanup,
    -- repair, full gate, `ShiftRunSafe`, GN controller, clock, or acceptance.
    Glob.one `Complexity.TMVerifier.TuringToolkit.GateOnePassBTraceSafety,
    -- GN-3B2c2 (2026-08-31), infrastructure only: exact successful terminal-B
    -- cleanup plus one complete reject-aware spent-to-index repair sweep,
    -- ending at the canonical read-A handoff.  No arbitrary-round induction,
    -- pass A, full gate, `ShiftRunSafe`, GN controller, clock, or acceptance.
    Glob.one `Complexity.TMVerifier.TuringToolkit.GateOnePassBTerminalRepairTraceSafety,
    -- GN-3B2d (2026-08-31), infrastructure only: actual arbitrary-arg2
    -- pass-B safety induction plus the separately safe zero-index route,
    -- composed through terminal cleanup/repair to the canonical read-A
    -- handoff.  No pass-A step, full gate, `ShiftRunSafe`, controller, output,
    -- verdict, or acceptance theorem.
    Glob.one `Complexity.TMVerifier.TuringToolkit.GateOnePassBDriverTraceSafety,
    -- GN-3B2e1a (2026-08-31), infrastructure only: dependency-closed binary
    -- pass-A dispatch/rescan/install safety from the merged read-A handoff,
    -- plus the real-initial exact Σᴬ(0) capstone.  Reverse seek and one-round
    -- safety are deferred to e1b; no terminal A repair or full-gate claim.
    Glob.one `Complexity.TMVerifier.TuringToolkit.GateOnePassATraceSafety,
    -- GN-3B2e1b (2026-09-01), infrastructure only: structural two-mode A
    -- reverse-seek safety and exactly one successful A round, composed from
    -- the merged e1a `Σᴬ(0)` endpoint.  No driver, terminal repair or gate.
    Glob.one `Complexity.TMVerifier.TuringToolkit.GateOnePassARoundTraceSafety,
    -- GN-3B2e2 (2026-09-01), infrastructure only: genuine arbitrary-round A
    -- driver safety, successful exhaustion seek, and terminal cursor cleanup
    -- through the exact cursor-free `aRepairStart` endpoint.  The binary
    -- capstone uses the actual existing schedule expression.  No A-repair,
    -- OOB conflation, unary/constant route, full gate, clock, or acceptance.
    Glob.one `Complexity.TMVerifier.TuringToolkit.GateOnePassADriverTraceSafety,
    -- GN-3B2e3 (2026-09-01), infrastructure only: actual live operand-A
    -- repair trace safety through canonical head-zero `aRepairDone`, composed
    -- with e2 on the existing binary schedule.  No result or full-gate step.
    Glob.one `Complexity.TMVerifier.TuringToolkit.GateOneARepairTraceSafety,
    -- GN-3B2e4 (2026-09-01), infrastructure only: binary result/combine and
    -- complete output-kernel safety from merged e3 through exact result-indexed
    -- `outputDone`, stopping before accept.  No unary/const or five-tag safety.
    Glob.one `Complexity.TMVerifier.TuringToolkit.GateOneOutputDoneTraceSafety,
    -- GN-3B2fA (2026-09-01), infrastructure only: tag-independent forward
    -- route safety and a zero-rewrite rewind, instantiated for unary/constant
    -- real-initial routes through their one-step live activations.  Empty
    -- unary values/OOB and later unary work stay separate; const stops at
    -- combine, before the output kernel.
    Glob.one `Complexity.TMVerifier.TuringToolkit.GateOneRouteRewindTraceSafety,
    -- GN-3B2fB (2026-09-01), infrastructure only: successful unary pass-A
    -- installation, generic driver/terminal cleanup, and live repair safety
    -- through exact canonical `aRepairDone`.  Empty values remain OOB; no
    -- result, combine, output, five-tag, shifted-run, controller or clock.
    Glob.one `Complexity.TMVerifier.TuringToolkit.GateOneUnaryARepairTraceSafety,
    -- GN-3B2fC (2026-09-01), infrastructure only: successful canonical
    -- input/const/not/and/or real-initial safety through exact result-indexed
    -- `outputDone`.  The merged binary theorem is unchanged; no accept step,
    -- shifted run, controller, multigate, clock or verdict is added.
    Glob.one `Complexity.TMVerifier.TuringToolkit.GateOneFiveTagTraceSafety,
    -- GN-E1b (2026-09-01), infrastructure only: the same fixed finite outer
    -- delegate shell and shifted capstones now confirm one physical `0000`
    -- frame after logical word end and return to fixed scratch entry.  No
    -- trailing-zero rejection, installer, loop, verdict or acceptance.
    Glob.one `Complexity.TMVerifier.TuringToolkit.GateNFixedDelegateRelocation,
    -- GN-E2-1b/E2-2 (2026-09-02), infrastructure only: boundary-image
    -- specialization of FrameShuttle in the same finite GNM control.
    Glob.one `Complexity.TMVerifier.TuringToolkit.GateNFrameShuttle,
    -- GN-E2-0 (2026-09-01), infrastructure only: exact pure-stage physical
    -- tapes, canonical first-request geometry, and complete equality between
    -- the base-N shifted target and an explicit concatenated-list endpoint.
    -- No state/transition mutation, installer execution, or marker strategy.
    Glob.one `Complexity.TMVerifier.TuringToolkit.GateNFirstInstallBridge,
    -- GN-E2-1c (2026-09-02): live read-only scratch bootstrap and first-record
    -- discovery; noGate remains dormant.
    Glob.one `Complexity.TMVerifier.TuringToolkit.GateNScratchBootstrap,
    -- GN-E2-2 (2026-09-02): the live firstRecord door and exactly one
    -- cursor-to-bof source-restoring shuttle, stopping at the exact exit
    -- boundary carrying cursor; GN-E2-3a owns its later activation.
    Glob.one `Complexity.TMVerifier.TuringToolkit.GateNBoundaryShuttle,
    -- GN-E2-3a (2026-09-02): payload-preserving one-body-round execution and
    -- fixed recordDone switch only; no arbitrary driver or real-input capstone.
    Glob.one `Complexity.TMVerifier.TuringToolkit.GateNBodyRound,
    Glob.one `Complexity.PsubsetPpolyInternal.CircuitTree,
    Glob.one `Complexity.PsubsetPpolyInternal.StraightLine,
    Glob.one `Complexity.PsubsetPpolyInternal.TreeToStraight,
    Glob.one `Complexity.PsubsetPpolyInternal.StraightLineBuilder,
    Glob.one `Complexity.PsubsetPpolyInternal.StraightLineSemantics,
    Glob.one `Complexity.PsubsetPpolyInternal.Simulation,
    Glob.one `Complexity.PsubsetPpolyInternal.ComplexityInterfaces,
    Glob.one `Complexity.PpolyDAG_StraightLineCore,
    Glob.one `Complexity.PpolyDAG_from_StraightLine,
    Glob.one `Complexity.PpolyFormula_from_PpolyDAG_FixedSlice,
    Glob.one `Complexity.PsubsetPpolyDAG_Internal,
    Glob.one `Complexity.Simulation.TM_Encoding,
    Glob.one `Complexity.Simulation.Circuit_Compiler,
    Glob.one `Barrier.Relativization,
    Glob.one `Barrier.NaturalProofs,
    Glob.one `Barrier.Algebrization,
    Glob.one `Barrier.Bypass,
    Glob.one `Models.PartialTruthTable,
    Glob.one `Models.Model_PartialMCSP,
    Glob.one `LowerBounds.LB_Formulas,
    Glob.one `LowerBounds.ApproxClassContradiction,
    Glob.one `LowerBounds.ApproxClassNoGo,
    Glob.one `LowerBounds.SingletonProvenanceEndpoint,
    Glob.one `LowerBounds.SingletonDensityEndpoint,
    Glob.one `LowerBounds.SingletonDensityContradiction,
    Glob.one `LowerBounds.AcceptedFamilyBarrier,
    Glob.one `LowerBounds.DAGStableRestrictionProducer,
    Glob.one `LowerBounds.RouteBSourceClosure,
    Glob.one `LowerBounds.FailedRoute_FixedSliceSupportHalfCore,
    Glob.one `LowerBounds.FailedRoute_FixedSliceSupportHalfImpossible,
    Glob.one `LowerBounds.FailedRoute_GapSliceFamilyVacuous,
    Glob.one `LowerBounds.FailedRoute_EventualTableForceSlackObstruction,
    Glob.one `LowerBounds.FailedRoutes,
    Glob.one `LowerBounds.DAGUnconditionalBlocker,
    Glob.one `LowerBounds.AsymptoticDAGBarrierInterfaces,
    Glob.one `LowerBounds.AsymptoticDAGBarrierTheorems,
    Glob.one `LowerBounds.AsymptoticDAGBarrier,
    Glob.one `LowerBounds.MCSPGapLocality,
    Glob.one `LowerBounds.AntiChecker_Partial,
    Glob.one `LowerBounds.LB_Formulas_Core_Partial,
    Glob.one `LowerBounds.AC0_GapMCSP_Final,
    Glob.one `LowerBounds.AC0_GapMCSP,
    Glob.one `Magnification.LocalityInterfaces_Partial,
    Glob.one `Magnification.Facts_Magnification_Partial,
    Glob.one `Magnification.PipelineStatements_Partial,
    Glob.one `Magnification.AC0LocalityBridge,
    Glob.one `Magnification.AC0AtlasBridge,
    Glob.one `Magnification.AC0ApproxFamilyBridge,
    Glob.one `Magnification.LocalityProvider_Partial,
    Glob.one `Magnification.LocalityLift_Partial,
    Glob.one `Magnification.Bridge_to_Magnification_Partial,
    Glob.one `Magnification.AsymptoticFormulaCollapse,
    Glob.one `Magnification.FinalResultMainline,
    Glob.one `Magnification.FinalResultAuditRoutes,
    Glob.one `Magnification.FinalResultWeakRoutes,
    Glob.one `Magnification.FinalResultLegacyTM,
    Glob.one `Magnification.FinalResultCore,
    Glob.one `Magnification.UnconditionalResearchGap,
    Glob.one `Magnification.CanonicalAsymptoticTrackData,
    Glob.one `Magnification.CanonicalAsymptoticDecider,
    Glob.one `Magnification.AuditRoutes.DistinguisherMatrixProvenance.V_gpt55.MatrixPrimitives,
    Glob.one `Magnification.AuditRoutes.DistinguisherMatrixProvenance.V_gpt55.ToySeparation,
    Glob.one `Magnification.FinalResult,
    -- Research Governance v0.1, PR 4a: refuted-predicate registry.
    Glob.one `RefutedPredicates.Registry,
    -- Research Governance v0.1, PR 10: FrozenSpec stage 1.
    Glob.one `Spec.FrozenSpec,
    -- Research Governance v0.1, FP-1: FixedParams Probe audit surface.
    Glob.one `Magnification.AuditRoutes.FixedParamsProbe,
    -- v0.4.2 Track A-CL0: CrossLength coherence audit target surface
    -- (research objectives only; no theorems, no NoGoLog entry).
    Glob.one `Magnification.AuditRoutes.CrossLengthCoherence_NoGo,
    -- v0.4.3-followup: 10-engineer parallel attack on FP-3b.2.
    -- Triage wiring; final selection happens at S11 integration.
    Glob.one `Magnification.AuditRoutes.LogWidthAdversary.Width_NatLog2,
    Glob.one `Magnification.AuditRoutes.LogWidthAdversary.Width_PowOfTwoSlice,
    Glob.one `Magnification.AuditRoutes.LogWidthAdversary.RenameSize,
    Glob.one `Magnification.AuditRoutes.LogWidthAdversary.RenameSupport,
    Glob.one `Magnification.AuditRoutes.LogWidthAdversary.TTFormulaSizeBound,
    Glob.one `Magnification.AuditRoutes.LogWidthAdversary.Family_NatLog2,
    Glob.one `Magnification.AuditRoutes.LogWidthAdversary.Family_PowOfTwoSlice,
    Glob.one `Magnification.AuditRoutes.LogWidthAdversary.Diversity_BelowN,
    Glob.one `Magnification.AuditRoutes.LogWidthAdversary.Diversity_Unbounded,
    -- v0.4.3-followup S11 integration: composition of the parallel
    -- engineer outputs into logWidthAdversary_satisfies_diversity.
    Glob.one `Magnification.AuditRoutes.LogWidthAdversary.Composition,
    -- fp3b4 support-cardinality barrier (post-NOGO-000006 follow-up).
    -- T1..T6 of the 6-slot decomposition, ending in the T6 application.
    Glob.one `Magnification.AuditRoutes.SupportCardinalityBarrier.CanonicalHardwiringFamily,
    Glob.one `Magnification.AuditRoutes.SupportCardinalityBarrier.CanonicalHardwiringSupport,
    Glob.one `Magnification.AuditRoutes.SupportCardinalityBarrier.CanonicalHardwiringWitness,
    Glob.one `Magnification.AuditRoutes.SupportCardinalityBarrier.SupportCardinalityOnly,
    Glob.one `Magnification.AuditRoutes.SupportCardinalityBarrier.Barrier,
    Glob.one `Magnification.AuditRoutes.SupportCardinalityBarrier.InSupportFunctionalDiversityApplication,
    -- fp3b3 ProvenanceFilter v2 design — Phase 1 paper sketches
    -- (4 directions, single engineer handle gpt55).
    Glob.one `Magnification.AuditRoutes.ProvenanceFilterV2.V2_A_gpt55.Sketch,
    Glob.one `Magnification.AuditRoutes.ProvenanceFilterV2.V2_A_gpt55.Filter,
    Glob.one `Magnification.AuditRoutes.ProvenanceFilterV2.V2_A_gpt55.ExcludesOverbroad,
    Glob.one `Magnification.AuditRoutes.ProvenanceFilterV2.V2_A_gpt55.ExcludesPrefixAnd,
    Glob.one `Magnification.AuditRoutes.ProvenanceFilterV2.V2_A_gpt55.ExcludesArbitraryPayload,
    Glob.one `Magnification.AuditRoutes.ProvenanceFilterV2.V2_A_gpt55.NonVacuity,
    Glob.one `Magnification.AuditRoutes.ProvenanceFilterV2.V2_A_gpt55.NotSupportCardinalityOnly,
    Glob.one `Magnification.AuditRoutes.ProvenanceFilterV2.V2_A_gpt55.Survivor,
    Glob.one `Magnification.AuditRoutes.ProvenanceFilterV2.V2_A_gpt55.AdversarialRobustness.RewriteAttack,
    Glob.one `Magnification.AuditRoutes.ProvenanceFilterV2.V2_A_gpt55.NaturalProofsSelfTest.RepresentationSensitivity,
    Glob.one `Magnification.AuditRoutes.ProvenanceFilterV2.V2_A_NormaliseMetaBarrier.Barrier,
    Glob.one `Magnification.AuditRoutes.ProvenanceFilterV2.V2_B_gpt55.Sketch,
    Glob.one `Magnification.AuditRoutes.ProvenanceFilterV2.V2_C_GPT55.Sketch,
    Glob.one `Magnification.AuditRoutes.ProvenanceFilterV2.V2_D_GPT55.Sketch,
    -- fp3b2 arbitrary-payload strengthening (post-NOGO-000005 follow-up).
    -- T1..T6 of the 6-slot decomposition, ending in the composition theorem.
    Glob.one `Magnification.AuditRoutes.ArbitraryLogWidthTT.AllEssential,
    Glob.one `Magnification.AuditRoutes.ArbitraryLogWidthTT.TTFormulaSupport,
    Glob.one `Magnification.AuditRoutes.ArbitraryLogWidthTT.RenamePayload,
    Glob.one `Magnification.AuditRoutes.ArbitraryLogWidthTT.Family,
    Glob.one `Magnification.AuditRoutes.ArbitraryLogWidthTT.Witness,
    Glob.one `Magnification.AuditRoutes.ArbitraryLogWidthTT.Composition,
    -- fp3b6 distinguisher-matrix provenance audit route (D1/D3 gpt55 + D2 codex,
    -- D4 read-set locality).
    -- (`V_gpt55.MatrixPrimitives` is already declared above, near `FinalResult`.)
    Glob.one `Magnification.AuditRoutes.DistinguisherMatrixProvenance.V_gpt55.AntiCollapse,
    Glob.one `Magnification.AuditRoutes.DistinguisherMatrixProvenance.V_codex.ToySeparation,
    Glob.one `Magnification.AuditRoutes.DistinguisherMatrixProvenance.V_codexd3a.AntiCollapsePrime,
    Glob.one `Magnification.AuditRoutes.DistinguisherMatrixProvenance.V_codexd3c.Sharpness,
    Glob.one `Magnification.AuditRoutes.DistinguisherMatrixProvenance.V_locality_d4.ReadSetLocality,
    Glob.one `Magnification.AuditRoutes.DistinguisherMatrixProvenance.V_locality_d5.LocalGateInvariance,
    Glob.one `Magnification.AuditRoutes.DistinguisherMatrixProvenance.V_locality_d6.PayloadBudgetThreshold,
    Glob.one `Magnification.AuditRoutes.DistinguisherMatrixProvenance.V_locality_d7.DelocalizationCriterion,
    Glob.one `ThirdPartyFacts.Facts_Switching,
    -- Partial-track bibliography/lemmas used by final magnification result.
    Glob.one `ThirdPartyFacts.PartialTransport,
    Glob.one `ThirdPartyFacts.PartialLocalityLift,
    Glob.one `ThirdPartyFacts.PpolyFormula,
    Glob.one `ThirdPartyFacts.LeafBudget,
    Glob.one `Tests.BarrierAudit,
    Glob.one `Tests.BarrierBypassAudit,
    Glob.one `Tests.AxiomsAudit,
    Glob.one `Tests.AC0PublishableSurface,
    Glob.one `Tests.BridgeLocalityRegression,
    Glob.one `Tests.CanonicalIntegrationTests,
    Glob.one `Tests.RouteSurfaceAudit,
    Glob.one `Tests.CircuitCountTraceBoundProbe,
    Glob.one `Tests.HInDagTrivialityProbe,
    Glob.one `Tests.GlobalHInDagContractProbe,
    Glob.one `Tests.GeneralIsoStrongNoGoProbe,
    Glob.one `Tests.GeneralIsoStrongRouteClosure,
    Glob.one `Tests.PromiseRouteConclusionProbe,
    Glob.one `Tests.WeakRouteSurfaceTests,
    Glob.one `Tests.UniformV1SurfaceTests,
    Glob.one `Tests.UniformV1CountabilitySurfaceTests,
    Glob.one `Tests.UniformV1CircuitEncodingSurfaceTests,
    Glob.one `Tests.UniformV1StepKernelSurfaceTests,
    Glob.one `Tests.UniformV1StepBundleSurfaceTests,
    Glob.one `Tests.UniformV1PpolyDAGSurfaceTests,
    Glob.one `Tests.DagBundleComposeSurfaceTests,
    Glob.one `Tests.TMSeqRunSurfaceTests,
    Glob.one `Tests.TMTrueUniformSeekSurfaceTests,
    Glob.one `Tests.TMTrueUniformSeekMutationSurfaceTests,
    Glob.one `Tests.TMTrueUniformSeekMutationLoopSurfaceTests,
    Glob.one `Tests.TMTrueUniformSeekMutationDriverSurfaceTests,
    Glob.one `Tests.TMTrueUniformSeekTerminalSurfaceTests,
    Glob.one `Tests.TMTrueUniformSeekSemanticsSurfaceTests,
    Glob.one `Tests.TMStepBridgeSurfaceTests,
    Glob.one `Tests.TMFrameScannerSurfaceTests,
    -- Reverse/write and S3a mixed-boundary exact contract surface.
    Glob.one `Tests.TMFrameScannerReverseSurfaceTests,
    Glob.one `Tests.TMFrameRewriteCycleSurfaceTests,
    -- GN-E2-1a (2026-09-02): explicit generic context-writer/shuttle surface,
    -- exact 8d+29 capstone, next blank, and fresh 45-step probes.
    Glob.one `Tests.TMFrameShuttleSurfaceTests,
    Glob.one `Tests.TMGateOnePureSurfaceTests,
    -- GN-1 (2026-08-30): 59 exact wrappers and definition `#check` pins for
    -- the pure multi-gate encoding surface.
    Glob.one `Tests.TMGateNEncodingSurfaceTests,
    -- GN-2 (2026-08-30): exact theorem wrappers and definition-only pins for
    -- the pure multi-gate tape-state surface.
    Glob.one `Tests.TMGateNTapeStateSurfaceTests,
    -- GN-3A (2026-08-30): exact wrappers for the generic local relocation,
    -- literal shifted one-/two-step capstones, and left-clamp counterexample.
    Glob.one `Tests.TMGateNRelocationSurfaceTests,
    Glob.one `Tests.TMGateOneResidualSurfaceTests,
    Glob.one `Tests.TMGateOneControlSurfaceTests,
    Glob.one `Tests.TMGateOneRoutingSurfaceTests,
    Glob.one `Tests.TMGateOnePassAControlSurfaceTests,
    Glob.one `Tests.TMGateOnePassAEntrySurfaceTests,
    Glob.one `Tests.TMGateOneAWalkInstallAtomsSurfaceTests,
    Glob.one `Tests.TMGateOneAWalkSurfaceTests,
    Glob.one `Tests.TMGateOneAWalkInvariantSurfaceTests,
    Glob.one `Tests.TMGateOneAWalkRoundSurfaceTests,
    Glob.one `Tests.TMGateOneAWalkDriverSurfaceTests,
    Glob.one `Tests.TMGateOneARepairSurfaceTests,
    Glob.one `Tests.TMGateOneAResultSurfaceTests,
    Glob.one `Tests.TMGateOneOutputKernelSurfaceTests,
    Glob.one `Tests.TMGateOneOutputAcceptSurfaceTests,
    -- GN-3B1 + GN-3B2a + GN-3B2b (2026-08-31): exact output-done plus
    -- structural parametric canonical validation/rewind safety through the
    -- real read-B handoff.  No pass-B, full-gate, or `ShiftRunSafe` claim.
    Glob.one `Tests.TMGateOneTraceSafetySurfaceTests,
    -- GN-3B2c1 (2026-08-31): exact named structural safety surfaces for the
    -- pass-B route/install and one successful cursor-walk round only.
    Glob.one `Tests.TMGateOnePassBTraceSafetySurfaceTests,
    -- GN-3B2c2 (2026-08-31): exact named structural safety surfaces for
    -- terminal pass-B cleanup and one repair sweep to the read-A handoff.
    Glob.one `Tests.TMGateOnePassBTerminalRepairTraceSafetySurfaceTests,
    -- GN-3B2d (2026-08-31): exact named wrappers for the arbitrary-arg2
    -- pass-B safety induction, the zero route, both repaired branches, their
    -- common read-A endpoint and the `400`/`172` real-initial capstones.
    Glob.one `Tests.TMGateOnePassBDriverTraceSafetySurfaceTests,
    -- GN-3B2e1a (2026-08-31): direct wrappers for nonconstant pass-A
    -- installation safety, retaining exact binary Σᴬ(0) capstones.
    Glob.one `Tests.TMGateOnePassATraceSafetySurfaceTests,
    -- GN-3B2e1b (2026-09-01): direct wrappers for A reverse-frame/run safety,
    -- the mixed boundary, one arbitrary-j successful round, and 53/423 pins.
    Glob.one `Tests.TMGateOnePassARoundTraceSafetySurfaceTests,
    -- GN-3B2e2 (2026-09-01): explicit direct wrappers for arbitrary driver,
    -- exhaustion, terminal cleanup, binary capstone, structure, and literals.
    Glob.one `Tests.TMGateOnePassADriverTraceSafetySurfaceTests,
    -- GN-3B2e3 (2026-09-01): direct proposition wrappers for the complete
    -- live A-repair safety surface, local 58/58/24 and binary 541 literals.
    Glob.one `Tests.TMGateOneARepairTraceSafetySurfaceTests,
    -- GN-3B2e4 (2026-09-01): explicit proposition wrappers for binary
    -- result/combine/output-kernel safety through exact output-done, with
    -- 606/484/512 literal totals and no outputDone-to-accept step.
    Glob.one `Tests.TMGateOneOutputDoneTraceSafetySurfaceTests,
    -- GN-3B2fA (2026-09-01): explicit proposition wrappers for the generic
    -- forward route/zero-rewrite rewind, unary/constant repaired routes and
    -- safe activations, including the actual 99/100, 131/132, 116/117 and
    -- 132/133 literal schedules.  Const stops at combine.
    Glob.one `Tests.TMGateOneRouteRewindTraceSafetySurfaceTests,
    -- GN-3B2fB (2026-09-01): direct explicit-proposition wrappers for unary
    -- install/driver/repair safety and the exact 131/192 and 171/240 literals.
    Glob.one `Tests.TMGateOneUnaryARepairTraceSafetySurfaceTests,
    -- GN-3B2fC (2026-09-01): definition pins and direct explicit-proposition
    -- wrappers for five-tag output-done safety, structure, schedules, and the
    -- complete 229/151/171/285/484/512/606 literal matrix.
    Glob.one `Tests.TMGateOneFiveTagTraceSafetySurfaceTests,
    -- GN-E1b (2026-09-01): constructor/definition pins and direct explicit
    -- proposition wrappers for blank confirmation, exact scratch entry,
    -- rejection probes, schedules, room arithmetic, and preserved capstones.
    Glob.one `Tests.TMGateNFixedDelegateRelocationSurfaceTests,
    -- GN-E2-1b/E2-2 (2026-09-02): GNM boundary-image shuttle owner,
    -- exact 8d+29 image capstones, body identity, rejection, and 45/37 probes.
    Glob.one `Tests.TMGateNFrameShuttleSurfaceTests,
    -- GN-E2-1c (2026-09-02): explicit locator grammar, endpoint, schedule,
    -- handoff, rejection, and literal surface pins.
    Glob.one `Tests.TMGateNScratchBootstrapSurfaceTests,
    -- GN-E2-2 (2026-09-02): exact door/seed/live-capstone, rejection, handoff,
    -- schedule and 188/16 literal wrappers.
    Glob.one `Tests.TMGateNBoundaryShuttleSurfaceTests,
    -- GN-E2-3a (2026-09-02): direct payload-exit, one-round, terminal-switch,
    -- rejection, clock and 94/20 literal proposition wrappers.
    Glob.one `Tests.TMGateNBodyRoundSurfaceTests,
    -- GN-E2-0 (2026-09-01): definition/configuration pins and direct explicit
    -- wrappers for pure physical stages, first-request geometry, and the
    -- complete installed physical endpoint equality.
    Glob.one `Tests.TMGateNFirstInstallBridgeSurfaceTests,
    Glob.one `Tests.TMGateOneExecutionSurfaceTests,
    Glob.one `Tests.TMGateOneReadBSurfaceTests,
    Glob.one `Tests.TMGateOneProbeInstallSurfaceTests,
    Glob.one `Tests.TMGateOneWalkSurfaceTests,
    Glob.one `Tests.TMGateOneWalkInvariantSurfaceTests,
    Glob.one `Tests.TMGateOneWalkDriverSurfaceTests,
    Glob.one `Tests.TMGateOneRepairKernelSurfaceTests,
    Glob.one `Tests.TMGateOneRepairKernelExamplesSurfaceTests,
    Glob.one `Tests.TMGateOneRepairDriverSurfaceTests,
    Glob.one `Tests.TMGateOneRepairExamplesSurfaceTests,
    Glob.one `Tests.FormulaSupportBoundsFalsifiabilityProbe,
    Glob.one `Tests.SmokeTests,
    Glob.one `Tests.UnitTests,
    -- Research Governance v0.1, PR 11: target-lock compile-time probe.
    Glob.one `Tests.TargetLockProbe,
    -- Research Governance v0.1, FP-1: FixedParams Probe NoGo smoke skeleton.
    Glob.one `Tests.FixedParams_Probe_NoGo,
    -- v0.4.2 Track A-CL0: regression smoke for the CL-0 target surface.
    Glob.one `Tests.AuditRoutes_CL0_NoGo_Regression,
    -- v0.4.3-followup S11: regression smoke for the log-width adversary
    -- composition + the parallel-engineer outputs it consumes.
    Glob.one `Tests.AuditRoutes_LogWidthAdversary_Smoke,
    Glob.one `Tests.AuditRoutes_ArbitraryLogWidthTT_Smoke,
    Glob.one `Tests.AuditRoutes_SupportCardinalityBarrier_Smoke,
    -- fp3b3.1 + fp3b3.2: smoke for V2-A landing artifacts
    -- (representation-sensitivity self-test + rewrite attack).
    Glob.one `Tests.AuditRoutes_V2A_LandingArtifacts_Smoke
  ]

lean_lib Pnp4 where
  srcDir := "pnp4"
  globs := #[
    Glob.one `Pnp4.AlgorithmsToLowerBounds.BasicCircuitClasses,
    Glob.one `Pnp4.AlgorithmsToLowerBounds.Growth,
    Glob.one `Pnp4.AlgorithmsToLowerBounds.SuperPolynomialBridge,
    Glob.one `Pnp4.AlgorithmsToLowerBounds.AC0pSuperPolynomialBridge,
    Glob.one `Pnp4.AlgorithmsToLowerBounds.AsymptoticSizeLowerBound,
    Glob.one `Pnp4.AlgorithmsToLowerBounds.AC0pAsymptoticBridge,
    Glob.one `Pnp4.AlgorithmsToLowerBounds.TruthTableMCSP,
    Glob.one `Pnp4.AlgorithmsToLowerBounds.LocalPRG,
    Glob.one `Pnp4.AlgorithmsToLowerBounds.CoinProblem,
    Glob.one `Pnp4.AlgorithmsToLowerBounds.CoinMaskingTranslation,
    Glob.one `Pnp4.AlgorithmsToLowerBounds.MCSPCoinReduction,
    Glob.one `Pnp4.AlgorithmsToLowerBounds.AC0pCoinLowerBound,
    Glob.one `Pnp4.AlgorithmsToLowerBounds.MCSPCoinReductionContract,
    Glob.one `Pnp4.AlgorithmsToLowerBounds.MCSP_AC0p_Final,
    Glob.one `Pnp4.AlgorithmsToLowerBounds.MCSP_AC0p_Quantitative,
    Glob.one `Pnp4.AlgorithmsToLowerBounds.AC0pCoinAsymptotic,
    Glob.one `Pnp4.AlgorithmsToLowerBounds.MCSP_LocalPRG_Transfer,
    Glob.one `Pnp4.AlgorithmsToLowerBounds.LocalPRGHardnessSpec,
    Glob.one `Pnp4.AlgorithmsToLowerBounds.FormulaCircuitTargetModel,
    Glob.one `Pnp4.AlgorithmsToLowerBounds.FormulaCircuitPublishedLowerBound,
    Glob.one `Pnp4.AlgorithmsToLowerBounds.MCSP_Formula_Final,
    Glob.one `Pnp4.AlgorithmsToLowerBounds.MCSP_Formula_Theorem2Quantitative,
    Glob.one `Pnp4.AlgorithmsToLowerBounds.FormulaCircuitAsymptotic,
    Glob.one `Pnp4.AlgorithmsToLowerBounds.BridgeToPpolyDAG,
    Glob.one `Pnp4.Frontier.PvsNPBridgeRequirements,
    Glob.one `Pnp4.Frontier.CompressionMagnification,
    Glob.one `Pnp4.Frontier.SearchMCSPMagnification,
    Glob.one `Pnp4.Frontier.SearchMCSPConcreteTargets,
    Glob.one `Pnp4.Frontier.DagSupportCardinality,
    -- Generic signed-support/no-go infrastructure.  These modules use only
    -- the current `DagCompose` / `DagCircuit` layer and carry no one-tape or
    -- streaming-magnification dependency.
    Glob.one `Pnp4.Frontier.SignedSupportNoGo.FiniteSignedSupport,
    Glob.one `Pnp4.Frontier.SignedSupportNoGo.FiniteSetDAG,
    Glob.one `Pnp4.Frontier.SignedSupportNoGo.DenseEasyBarrier,
    Glob.one `Pnp4.Frontier.ContractExpansion.C_DAG_Adapter,
    Glob.one `Pnp4.Frontier.ContractExpansion.QueryComposition,
    Glob.one `Pnp4.Frontier.ContractExpansion.QueryBuilder,
    Glob.one `Pnp4.Frontier.ContractExpansion.PrefixExtensionLanguage,
    Glob.one `Pnp4.Frontier.ContractExpansion.PrefixQueryBuilder,
    Glob.one `Pnp4.Frontier.ContractExpansion.PrefixExtensionLanguageNP,
    Glob.one `Pnp4.Frontier.ContractExpansion.PrefixExtensionLanguageRuntime,
    Glob.one `Pnp4.Frontier.ContractExpansion.PrefixParserConvention,
    Glob.one `Pnp4.Frontier.ContractExpansion.TreeMCSPPrefixSerializer,
    Glob.one `Pnp4.Frontier.ContractExpansion.TreeMCSPPrefixQueryCircuits,
    Glob.one `Pnp4.Frontier.ContractExpansion.TreeMCSPZeroPrefixBuilder,
    Glob.one `Pnp4.Frontier.ContractExpansion.NaiveGreedySizeSpike,
    Glob.one `Pnp4.Frontier.ContractExpansion.TreeMCSPPrefixStateQueryCircuits,
    Glob.one `Pnp4.Frontier.ContractExpansion.TreeMCSPGreedyBundleStep,
    Glob.one `Pnp4.Frontier.ContractExpansion.TreeMCSPGreedyBundleFold,
    Glob.one `Pnp4.Frontier.ContractExpansion.TreeMCSPGreedyOutputCircuits,
    Glob.one `Pnp4.Frontier.ContractExpansion.PrefixExtendableSplit,
    Glob.one `Pnp4.Frontier.ContractExpansion.TreeMCSPTrueExtensionQuery,
    Glob.one `Pnp4.Frontier.ContractExpansion.TreeMCSPGreedyExtendable,
    Glob.one `Pnp4.Frontier.ContractExpansion.TreeMCSPGreedyTrueOutputCircuits,
    Glob.one `Pnp4.Frontier.ContractExpansion.TreeMCSPDeciderCorrect,
    Glob.one `Pnp4.Frontier.ContractExpansion.TreeMCSPGreedySolves,
    Glob.one `Pnp4.Frontier.ContractExpansion.TreeMCSPBoundedSolver,
    Glob.one `Pnp4.Frontier.ContractExpansion.BoundedSolverFromPpoly,
    Glob.one `Pnp4.Frontier.ContractExpansion.NoSolverContrapositive,
    Glob.one `Pnp4.Frontier.ContractExpansion.ExtractedScheduleGrowth,
    Glob.one `Pnp4.Frontier.ContractExpansion.ConditionalVerifiedSource,
    Glob.one `Pnp4.Frontier.ContractExpansion.WitnessGrowthReduction,
    Glob.one `Pnp4.Frontier.ContractExpansion.PrefixExtensionNPWitness,
    Glob.one `Pnp4.Frontier.ContractExpansion.ExplicitConditionalSource,
    Glob.one `Pnp4.Frontier.ContractExpansion.ConcreteCodecGap,
    Glob.one `Pnp4.Frontier.ContractExpansion.CircuitTreeBridge,
    Glob.one `Pnp4.Frontier.ContractExpansion.CircuitEncodingLength,
    Glob.one `Pnp4.Frontier.ContractExpansion.CircuitDecodeDepthFree,
    Glob.one `Pnp4.Frontier.ContractExpansion.ConcreteTreeCodec,
    Glob.one `Pnp4.Frontier.ContractExpansion.ConcreteTreeDirectEvaluator,
    Glob.one `Pnp4.Frontier.ContractExpansion.ConcreteTreeDirectTagProgram,
    Glob.one `Pnp4.Frontier.ContractExpansion.ConcreteTreeCodecSource,
    Glob.one `Pnp4.Frontier.ContractExpansion.ThresholdGrowth,
    Glob.one `Pnp4.Frontier.ContractExpansion.ConsolidatedTreeSeparation,
    -- NP-verifier prerequisites for the prefix-extension language: the semantic
    -- verifier and its input-tape layout, listed in dependency order (the layout
    -- module imports the semantic verifier).
    Glob.one `Pnp4.Frontier.ContractExpansion.TreeMCSPPrefixSemanticVerifier,
    Glob.one `Pnp4.Frontier.ContractExpansion.TreeMCSPPrefixVerifierLayout,
    -- The content-truthful prefix-extension language `L'`, its padding-stability
    -- lemmas, and the conditional chain re-routed through it, listed in dependency
    -- order (each module imports only modules listed above it; Coincidence pulls in
    -- the two verifier modules above, Padding stays specification-only, and the
    -- explicitly classical transport module imports both Coincidence and Padding).
    Glob.one `Pnp4.Frontier.ContractExpansion.ContentPrefixExtension,
    -- FEAS-0 slice, part 1: parser field recovery.  It imports only
    -- `ContentPrefixExtension`, so it is listed immediately after it.
    Glob.one `Pnp4.Frontier.ContractExpansion.ContentParseFieldRecovery,
    Glob.one `Pnp4.Frontier.ContractExpansion.ContentPrefixExtensionCoincidence,
    Glob.one `Pnp4.Frontier.ContractExpansion.ContentPrefixExtensionPadding,
    -- P0: computable content-side semantic verifier and its specification correctness.
    Glob.one `Pnp4.Frontier.ContractExpansion.ContentSemanticVerifier,
    -- D1a: machine-facing tape lemmas and the predicate-parameterized exact-step bridge.
    Glob.one `Pnp4.Frontier.ContractExpansion.ContentVerifierTapeInterface,
    -- D1b: the codec-specific bridge alias and the conditional witness repackaging.  It imports
    -- both P0's semantic verifier and D1a's bridge structure, so it is listed after both.
    Glob.one `Pnp4.Frontier.ContractExpansion.ContentVerifierBridgeWitness,
    -- FEAS-0 slice, part 2: the concrete accepted-target polynomial bound.
    Glob.one `Pnp4.Frontier.ContractExpansion.ContentTargetSizeBound,
    -- GATE-0 slice: non-vacuity of `ContentAccepts` at the concrete codec.
    Glob.one `Pnp4.Frontier.ContractExpansion.ContentPrefixExtensionNonVacuity,
    -- I1: honest convention-length injectivity, gamma canonicity/narrowing,
    -- unconditional length-gate vacuity, and the exact three-value-test residue.
    -- It imports `ContentPrefixExtensionCoincidence`, `ContentPrefixExtensionPadding`,
    -- `ConcreteTreeCodec` and `ThresholdGrowth`, all listed above.
    Glob.one `Pnp4.Frontier.ContractExpansion.ContentPrefixExtensionGateClosure,
    Glob.one `Pnp4.Frontier.ContractExpansion.ContentPrefixExtensionPaddingTransport,
    Glob.one `Pnp4.Frontier.ContractExpansion.ContentPrefixExtensionTransfer,
    Glob.one `Pnp4.Frontier.ContractExpansion.ContentConsolidatedSource,
    -- Model-audit module: it depends only on the shared complexity interfaces,
    -- so it is listed after the whole contract-expansion chain and before the
    -- test modules that import it.
    Glob.one `Pnp4.Frontier.ModelAudit.RuntimeAdviceBarrier,
    Glob.one `Pnp4.Tests.AlgorithmsToLowerBoundsSurfaceTests,
    Glob.one `Pnp4.Tests.AxiomsAudit
  ]

@[test_driver]
lean_exe test where
  root := `Tests.TestDriver
  srcDir := "pnp3"
