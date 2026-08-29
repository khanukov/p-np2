import Complexity.TMVerifier.TuringToolkit.GateOnePassAControl

/-!
# G1 pass A: real-initial literal entry probes

**Progress classification: Infrastructure.**  S1c instantiates the merged
S1b2b activation/install capstones at ten canonical requests:

| tag | selected value / literal | input cells | frame-word cells | steps | endpoint |
|-----|--------------------------|-------------|------------------|-------|----------|
| `input` | `false`, `true` | `32` | `36` | `113` | `aInstallStart`, head `12`, `idA` |
| `not` | `false`, `true` | `40` | `44` | `153` | `aInstallStart`, head `20`, `notA` |
| `and` | operand B `false`, `true` | `44` | `48` | `198` | `aInstallStart`, head `24`, `constFalse` / `idA` |
| `or` | operand B `false`, `true` | `48` | `52` | `218` | `aInstallStart`, head `28`, `idA` / `constTrue` |
| `const` | `false`, `true` | `32`, `36` | `36`, `40` | `117`, `133` | `combineStart`, head `0` |

Every principal theorem starts at the real `G1M.initialConfig`.  The eight
unary/binary runs stop at the exact `aInstallStart` boundary on the first
cell of operand 1.  Their tape is exactly the initial canonical tape, their
residual is exact, and the operand-B latch `vB` is retained.  Thus pass A has
read only its tag/residual entry prefix at these stated step counts: the next
S4 step is the live `aInsSeek` entry.  The two `const` runs bypass that prefix
and stop at `combineStart`
with exactly `g1ResultCtx false` or `g1ResultCtx true`; the `const` filler row
of `g1Residual` is not used.

`and` with operand B `false` exposes the context-bit alias explicitly: its
latched context is literally `g1ResultCtx false`, but its control mode is
`aInstallStart`, not `combineStart`.

The input length, explicit encoded frame word plus trailing `blank`, and
physical tape capacity are three different quantities.  `probe_extents` pins
all three for every request.  These historical prefix capstones execute no
cursor-installation step; the S4 capstones live in `GateOneAWalkInstallAtoms`.
Nothing here executes combine, writes output, proves acceptance or changes
advice.
-/

namespace Pnp3.Internal.PsubsetPpoly.TM

namespace G1PassAEntryExamples

/-! ## Ten canonical literal requests -/

def reqInputFalse : G1Request := ⟨.input, 0, 0, [false]⟩
def reqInputTrue : G1Request := ⟨.input, 0, 0, [true]⟩
def reqNotFalse : G1Request := ⟨.not, 0, 0, [false]⟩
def reqNotTrue : G1Request := ⟨.not, 0, 0, [true]⟩
def reqAndFalse : G1Request := ⟨.and, 0, 0, [false]⟩
def reqAndTrue : G1Request := ⟨.and, 0, 0, [true]⟩
def reqOrFalse : G1Request := ⟨.or, 0, 0, [false]⟩
def reqOrTrue : G1Request := ⟨.or, 0, 0, [true]⟩
def reqConstFalse : G1Request := ⟨.const, 0, 0, []⟩
def reqConstTrue : G1Request := ⟨.const, 1, 0, []⟩

theorem requests_canonical :
    reqInputFalse.Canonical ∧ reqInputTrue.Canonical ∧
      reqNotFalse.Canonical ∧ reqNotTrue.Canonical ∧
      reqAndFalse.Canonical ∧ reqAndTrue.Canonical ∧
      reqOrFalse.Canonical ∧ reqOrTrue.Canonical ∧
      reqConstFalse.Canonical ∧ reqConstTrue.Canonical := by
  decide

/-- The four operand-1 selections, four operand-B selections and two constant
literals are physically present in the ten requests.  The operand-1 facts are
request facts only: the runs below stop before pass A reads those cells. -/
theorem selected_literals :
    reqInputFalse.vals[reqInputFalse.arg1]? = some false ∧
      reqInputTrue.vals[reqInputTrue.arg1]? = some true ∧
      reqNotFalse.vals[reqNotFalse.arg1]? = some false ∧
      reqNotTrue.vals[reqNotTrue.arg1]? = some true ∧
      reqAndFalse.vals[reqAndFalse.arg2]? = some false ∧
      reqAndTrue.vals[reqAndTrue.arg2]? = some true ∧
      reqOrFalse.vals[reqOrFalse.arg2]? = some false ∧
      reqOrTrue.vals[reqOrTrue.arg2]? = some true ∧
      reqConstFalse.spec = some false ∧ reqConstTrue.spec = some true := by
  decide

/-- For each probe: encoded input cells, explicit validation-frame word cells
(the encoding plus one four-cell `blank`), and physical tape capacity.  These
are intentionally separate equalities. -/
theorem probe_extents :
    ((encodeG1 reqInputFalse).length = 32 ∧
        ((encodeG1Frames reqInputFalse ++ [G1Frame.blank]).flatMap G1Frame.bits).length = 36 ∧
        G1M.tapeLength (encodeG1 reqInputFalse).length = 558113) ∧
      ((encodeG1 reqInputTrue).length = 32 ∧
        ((encodeG1Frames reqInputTrue ++ [G1Frame.blank]).flatMap G1Frame.bits).length = 36 ∧
        G1M.tapeLength (encodeG1 reqInputTrue).length = 558113) ∧
      ((encodeG1 reqNotFalse).length = 40 ∧
        ((encodeG1Frames reqNotFalse ++ [G1Frame.blank]).flatMap G1Frame.bits).length = 44 ∧
        G1M.tapeLength (encodeG1 reqNotFalse).length = 861225) ∧
      ((encodeG1 reqNotTrue).length = 40 ∧
        ((encodeG1Frames reqNotTrue ++ [G1Frame.blank]).flatMap G1Frame.bits).length = 44 ∧
        G1M.tapeLength (encodeG1 reqNotTrue).length = 861225) ∧
      ((encodeG1 reqAndFalse).length = 44 ∧
        ((encodeG1Frames reqAndFalse ++ [G1Frame.blank]).flatMap G1Frame.bits).length = 48 ∧
        G1M.tapeLength (encodeG1 reqAndFalse).length = 1037357) ∧
      ((encodeG1 reqAndTrue).length = 44 ∧
        ((encodeG1Frames reqAndTrue ++ [G1Frame.blank]).flatMap G1Frame.bits).length = 48 ∧
        G1M.tapeLength (encodeG1 reqAndTrue).length = 1037357) ∧
      ((encodeG1 reqOrFalse).length = 48 ∧
        ((encodeG1Frames reqOrFalse ++ [G1Frame.blank]).flatMap G1Frame.bits).length = 52 ∧
        G1M.tapeLength (encodeG1 reqOrFalse).length = 1229873) ∧
      ((encodeG1 reqOrTrue).length = 48 ∧
        ((encodeG1Frames reqOrTrue ++ [G1Frame.blank]).flatMap G1Frame.bits).length = 52 ∧
        G1M.tapeLength (encodeG1 reqOrTrue).length = 1229873) ∧
      ((encodeG1 reqConstFalse).length = 32 ∧
        ((encodeG1Frames reqConstFalse ++ [G1Frame.blank]).flatMap G1Frame.bits).length = 36 ∧
        G1M.tapeLength (encodeG1 reqConstFalse).length = 558113) ∧
      ((encodeG1 reqConstTrue).length = 36 ∧
        ((encodeG1Frames reqConstTrue ++ [G1Frame.blank]).flatMap G1Frame.bits).length = 40 ∧
        G1M.tapeLength (encodeG1 reqConstTrue).length = 701477) := by
  decide

private theorem inputFalse_steps :
    g1UActivatedSteps reqInputFalse +
        (4 * (reqInputFalse.tag.units + 2) + 1) = 113 := by decide
private theorem inputTrue_steps :
    g1UActivatedSteps reqInputTrue +
        (4 * (reqInputTrue.tag.units + 2) + 1) = 113 := by decide
private theorem notFalse_steps :
    g1UActivatedSteps reqNotFalse +
        (4 * (reqNotFalse.tag.units + 2) + 1) = 153 := by decide
private theorem notTrue_steps :
    g1UActivatedSteps reqNotTrue +
        (4 * (reqNotTrue.tag.units + 2) + 1) = 153 := by decide
private theorem andFalse_steps :
    g1BActivatedSteps reqAndFalse +
        (4 * (reqAndFalse.tag.units + 2) + 1) = 198 := by decide
private theorem andTrue_steps :
    g1BActivatedSteps reqAndTrue +
        (4 * (reqAndTrue.tag.units + 2) + 1) = 198 := by decide
private theorem orFalse_steps :
    g1BActivatedSteps reqOrFalse +
        (4 * (reqOrFalse.tag.units + 2) + 1) = 218 := by decide
private theorem orTrue_steps :
    g1BActivatedSteps reqOrTrue +
        (4 * (reqOrTrue.tag.units + 2) + 1) = 218 := by decide
private theorem constFalse_steps : g1ConstActivatedSteps reqConstFalse = 117 := by decide
private theorem constTrue_steps : g1ConstActivatedSteps reqConstTrue = 133 := by decide

/-! ## Exact real-initial runs -/

theorem input_false_install :
    TM.runConfig (M := G1M)
        (G1M.initialConfig (g1Point (encodeG1 reqInputFalse))) 113 =
      g1AInstallConfig reqInputFalse false := by
  have h := g1CS_install_unary_exact reqInputFalse requests_canonical.1 (Or.inl rfl)
  rwa [inputFalse_steps] at h

theorem input_true_install :
    TM.runConfig (M := G1M)
        (G1M.initialConfig (g1Point (encodeG1 reqInputTrue))) 113 =
      g1AInstallConfig reqInputTrue false := by
  have h := g1CS_install_unary_exact reqInputTrue requests_canonical.2.1 (Or.inl rfl)
  rwa [inputTrue_steps] at h

theorem not_false_install :
    TM.runConfig (M := G1M)
        (G1M.initialConfig (g1Point (encodeG1 reqNotFalse))) 153 =
      g1AInstallConfig reqNotFalse false := by
  have h := g1CS_install_unary_exact reqNotFalse requests_canonical.2.2.1
    (Or.inr rfl)
  rwa [notFalse_steps] at h

theorem not_true_install :
    TM.runConfig (M := G1M)
        (G1M.initialConfig (g1Point (encodeG1 reqNotTrue))) 153 =
      g1AInstallConfig reqNotTrue false := by
  have h := g1CS_install_unary_exact reqNotTrue requests_canonical.2.2.2.1
    (Or.inr rfl)
  rwa [notTrue_steps] at h

theorem and_false_install :
    TM.runConfig (M := G1M)
        (G1M.initialConfig (g1Point (encodeG1 reqAndFalse))) 198 =
      g1AInstallConfig reqAndFalse false := by
  have h := g1CS_install_binary_exact reqAndFalse requests_canonical.2.2.2.2.1
    (Or.inl rfl) false selected_literals.2.2.2.2.1
  rwa [andFalse_steps] at h

theorem and_true_install :
    TM.runConfig (M := G1M)
        (G1M.initialConfig (g1Point (encodeG1 reqAndTrue))) 198 =
      g1AInstallConfig reqAndTrue true := by
  have h := g1CS_install_binary_exact reqAndTrue requests_canonical.2.2.2.2.2.1
    (Or.inl rfl) true selected_literals.2.2.2.2.2.1
  rwa [andTrue_steps] at h

theorem or_false_install :
    TM.runConfig (M := G1M)
        (G1M.initialConfig (g1Point (encodeG1 reqOrFalse))) 218 =
      g1AInstallConfig reqOrFalse false := by
  have h := g1CS_install_binary_exact reqOrFalse requests_canonical.2.2.2.2.2.2.1
    (Or.inr rfl) false selected_literals.2.2.2.2.2.2.1
  rwa [orFalse_steps] at h

theorem or_true_install :
    TM.runConfig (M := G1M)
        (G1M.initialConfig (g1Point (encodeG1 reqOrTrue))) 218 =
      g1AInstallConfig reqOrTrue true := by
  have h := g1CS_install_binary_exact reqOrTrue requests_canonical.2.2.2.2.2.2.2.1
    (Or.inr rfl) true selected_literals.2.2.2.2.2.2.2.1
  rwa [orTrue_steps] at h

theorem const_false_result :
    TM.runConfig (M := G1M)
        (G1M.initialConfig (g1Point (encodeG1 reqConstFalse))) 117 =
      g1CombineConfig reqConstFalse false := by
  have h := g1CS_activate_const_exact reqConstFalse requests_canonical.2.2.2.2.2.2.2.2.1
    rfl false selected_literals.2.2.2.2.2.2.2.2.1
  rwa [constFalse_steps] at h

theorem const_true_result :
    TM.runConfig (M := G1M)
        (G1M.initialConfig (g1Point (encodeG1 reqConstTrue))) 133 =
      g1CombineConfig reqConstTrue true := by
  have h := g1CS_activate_const_exact reqConstTrue requests_canonical.2.2.2.2.2.2.2.2.2
    rfl true selected_literals.2.2.2.2.2.2.2.2.2
  rwa [constTrue_steps] at h

/-! ## Exact endpoint projections and clock bounds -/

/-- Exact heads: the eight install probes stop immediately after the tag's
closing `argSep`; the two constant bypasses are stationary at head zero. -/
theorem endpoint_heads :
    ((TM.runConfig (M := G1M)
        (G1M.initialConfig (g1Point (encodeG1 reqInputFalse))) 113).head : Nat) = 12 ∧
      ((TM.runConfig (M := G1M)
        (G1M.initialConfig (g1Point (encodeG1 reqInputTrue))) 113).head : Nat) = 12 ∧
      ((TM.runConfig (M := G1M)
        (G1M.initialConfig (g1Point (encodeG1 reqNotFalse))) 153).head : Nat) = 20 ∧
      ((TM.runConfig (M := G1M)
        (G1M.initialConfig (g1Point (encodeG1 reqNotTrue))) 153).head : Nat) = 20 ∧
      ((TM.runConfig (M := G1M)
        (G1M.initialConfig (g1Point (encodeG1 reqAndFalse))) 198).head : Nat) = 24 ∧
      ((TM.runConfig (M := G1M)
        (G1M.initialConfig (g1Point (encodeG1 reqAndTrue))) 198).head : Nat) = 24 ∧
      ((TM.runConfig (M := G1M)
        (G1M.initialConfig (g1Point (encodeG1 reqOrFalse))) 218).head : Nat) = 28 ∧
      ((TM.runConfig (M := G1M)
        (G1M.initialConfig (g1Point (encodeG1 reqOrTrue))) 218).head : Nat) = 28 ∧
      ((TM.runConfig (M := G1M)
        (G1M.initialConfig (g1Point (encodeG1 reqConstFalse))) 117).head : Nat) = 0 ∧
      ((TM.runConfig (M := G1M)
        (G1M.initialConfig (g1Point (encodeG1 reqConstTrue))) 133).head : Nat) = 0 := by
  rw [input_false_install, input_true_install, not_false_install, not_true_install,
    and_false_install, and_true_install, or_false_install, or_true_install,
    const_false_result, const_true_result]
  decide

/-- Exact control and context states.  In particular these equalities pin every
residual and retained `vB`, while `const` carries only `g1ResultCtx`. -/
theorem endpoint_states :
    (TM.runConfig (M := G1M)
        (G1M.initialConfig (g1Point (encodeG1 reqInputFalse))) 113).state.snd =
          g1AInstallState ((g1Ctx0.withVB false).withRes .idA) ∧
      (TM.runConfig (M := G1M)
        (G1M.initialConfig (g1Point (encodeG1 reqInputTrue))) 113).state.snd =
          g1AInstallState ((g1Ctx0.withVB false).withRes .idA) ∧
      (TM.runConfig (M := G1M)
        (G1M.initialConfig (g1Point (encodeG1 reqNotFalse))) 153).state.snd =
          g1AInstallState ((g1Ctx0.withVB false).withRes .notA) ∧
      (TM.runConfig (M := G1M)
        (G1M.initialConfig (g1Point (encodeG1 reqNotTrue))) 153).state.snd =
          g1AInstallState ((g1Ctx0.withVB false).withRes .notA) ∧
      (TM.runConfig (M := G1M)
        (G1M.initialConfig (g1Point (encodeG1 reqAndFalse))) 198).state.snd =
          g1AInstallState (g1ResultCtx false) ∧
      (TM.runConfig (M := G1M)
        (G1M.initialConfig (g1Point (encodeG1 reqAndTrue))) 198).state.snd =
          g1AInstallState ((g1Ctx0.withVB true).withRes .idA) ∧
      (TM.runConfig (M := G1M)
        (G1M.initialConfig (g1Point (encodeG1 reqOrFalse))) 218).state.snd =
          g1AInstallState ((g1Ctx0.withVB false).withRes .idA) ∧
      (TM.runConfig (M := G1M)
        (G1M.initialConfig (g1Point (encodeG1 reqOrTrue))) 218).state.snd =
          g1AInstallState ((g1Ctx0.withVB true).withRes .constTrue) ∧
      (TM.runConfig (M := G1M)
        (G1M.initialConfig (g1Point (encodeG1 reqConstFalse))) 117).state.snd =
          g1CombineState (g1ResultCtx false) ∧
      (TM.runConfig (M := G1M)
        (G1M.initialConfig (g1Point (encodeG1 reqConstTrue))) 133).state.snd =
          g1CombineState (g1ResultCtx true) := by
  rw [input_false_install, input_true_install, not_false_install, not_true_install,
    and_false_install, and_true_install, or_false_install, or_true_install,
    const_false_result, const_true_result]
  decide

/-- Every endpoint tape is bit-for-bit its own real initial tape. -/
theorem endpoint_tapes :
    (TM.runConfig (M := G1M)
        (G1M.initialConfig (g1Point (encodeG1 reqInputFalse))) 113).tape =
          (G1M.initialConfig (g1Point (encodeG1 reqInputFalse))).tape ∧
      (TM.runConfig (M := G1M)
        (G1M.initialConfig (g1Point (encodeG1 reqInputTrue))) 113).tape =
          (G1M.initialConfig (g1Point (encodeG1 reqInputTrue))).tape ∧
      (TM.runConfig (M := G1M)
        (G1M.initialConfig (g1Point (encodeG1 reqNotFalse))) 153).tape =
          (G1M.initialConfig (g1Point (encodeG1 reqNotFalse))).tape ∧
      (TM.runConfig (M := G1M)
        (G1M.initialConfig (g1Point (encodeG1 reqNotTrue))) 153).tape =
          (G1M.initialConfig (g1Point (encodeG1 reqNotTrue))).tape ∧
      (TM.runConfig (M := G1M)
        (G1M.initialConfig (g1Point (encodeG1 reqAndFalse))) 198).tape =
          (G1M.initialConfig (g1Point (encodeG1 reqAndFalse))).tape ∧
      (TM.runConfig (M := G1M)
        (G1M.initialConfig (g1Point (encodeG1 reqAndTrue))) 198).tape =
          (G1M.initialConfig (g1Point (encodeG1 reqAndTrue))).tape ∧
      (TM.runConfig (M := G1M)
        (G1M.initialConfig (g1Point (encodeG1 reqOrFalse))) 218).tape =
          (G1M.initialConfig (g1Point (encodeG1 reqOrFalse))).tape ∧
      (TM.runConfig (M := G1M)
        (G1M.initialConfig (g1Point (encodeG1 reqOrTrue))) 218).tape =
          (G1M.initialConfig (g1Point (encodeG1 reqOrTrue))).tape ∧
      (TM.runConfig (M := G1M)
        (G1M.initialConfig (g1Point (encodeG1 reqConstFalse))) 117).tape =
          (G1M.initialConfig (g1Point (encodeG1 reqConstFalse))).tape ∧
      (TM.runConfig (M := G1M)
        (G1M.initialConfig (g1Point (encodeG1 reqConstTrue))) 133).tape =
          (G1M.initialConfig (g1Point (encodeG1 reqConstTrue))).tape := by
  rw [input_false_install, input_true_install, not_false_install, not_true_install,
    and_false_install, and_true_install, or_false_install, or_true_install,
    const_false_result, const_true_result]
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The no-wrong-result pin: the `and false` context aliases the false result
bit pattern, but control remains at the exact pre-entry install boundary at
this step count. -/
theorem and_false_no_wrong_result :
    (TM.runConfig (M := G1M)
        (G1M.initialConfig (g1Point (encodeG1 reqAndFalse))) 198).state.snd.ctx =
          g1ResultCtx false ∧
      (TM.runConfig (M := G1M)
        (G1M.initialConfig (g1Point (encodeG1 reqAndFalse))) 198).state.snd.mode =
          .aInstallStart ∧
      (TM.runConfig (M := G1M)
        (G1M.initialConfig (g1Point (encodeG1 reqAndFalse))) 198).state.snd.mode ≠
          .combineStart := by
  rw [and_false_install]
  exact ⟨rfl, rfl, by decide⟩

/-- Every literal total fits the unchanged public `g1Clock`. -/
theorem probe_clocks :
    113 ≤ g1Clock (encodeG1 reqInputFalse).length ∧
      113 ≤ g1Clock (encodeG1 reqInputTrue).length ∧
      153 ≤ g1Clock (encodeG1 reqNotFalse).length ∧
      153 ≤ g1Clock (encodeG1 reqNotTrue).length ∧
      198 ≤ g1Clock (encodeG1 reqAndFalse).length ∧
      198 ≤ g1Clock (encodeG1 reqAndTrue).length ∧
      218 ≤ g1Clock (encodeG1 reqOrFalse).length ∧
      218 ≤ g1Clock (encodeG1 reqOrTrue).length ∧
      117 ≤ g1Clock (encodeG1 reqConstFalse).length ∧
      133 ≤ g1Clock (encodeG1 reqConstTrue).length := by
  decide

end G1PassAEntryExamples

end Pnp3.Internal.PsubsetPpoly.TM
