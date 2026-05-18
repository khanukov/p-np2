# Plan: Закрытие TM-верификатора Canonical Asymptotic GapPartialMCSP

**Репозиторий:** `/home/user/p-np2/pnp3`
**Baseline branch:** `claude/audit-hnpbridge-interface-FnO1v` (уже содержит decoder + components-bridge)

## 1. Context

Reduction-слой на `pnp3/Magnification/CanonicalAsymptoticDecider.lean` уже сводит канонический асимптотический NP-трек к одной типизированной цели: построить `CanonicalAsymptoticVerifierComponents`. Downstream `canonicalAsymptoticData_of_components → AsymptoticFormulaTrackData` полностью доказан без `sorry`/аксиом.

Закрытие TM-верификатора — это **многотысячная LOC инженерия**. Один Lean-сессионный диапазон ≈ один leaf-блокер. Поэтому декомпозируем на **7 последовательных сессий**, каждая со standalone-теоремой и обязательством "0 sorry / только классические аксиомы".

Toolkit уже содержит готовые heavyweight-теоремы:
- `BinaryCounter.incrementProgram_correct` — `BinaryCounter.lean:1315`
- `CombineAtOffset.combineAtOffsetCS_run_full` — `CombineAtOffset.lean:1037`
- `GateWrappers.circuitEvaluatorCS_run_correct_wf` — `GateWrappers.lean:5034`
- `GateWrappers.seqList_timeBound_le_uniform` — `GateWrappers.lean:577`

## 2. Архитектурное решение: Variant B (NP-style)

Заменить `CanonicalAsymptoticVerifierComponents.accepts_eq` на стандартную NP-формулировку:

```lean
accepts_eq : ∀ n (x : Bitstring n),
  decideAsymptotic n x = true ↔
    ∃ w : Bitstring (certificateLength n k),
      Internal.PsubsetPpoly.TM.accepts (M := M) (n := n + certificateLength n k)
        (concatBitstring x w) = true
```

**Обоснование:**
- Устраняет внутренний "Phase A scan + Phase B identify" (~600 LOC) для enumerate-all-candidates.
- TM просто **верифицирует** угадываемый кандидат, закодированный в `w` — стандартный паттерн OPS19/CJW20.
- Не-канонические длины обрабатываются тривиально: верификатор отвергает любой `(x ++ w)` если `n ≠ 2·2^m`, без специального поиска.
- Экономит ~30% LOC во всех сессиях 3-6.

Текущий `witness` (lines 296-312) после правки структуры будет напрямую использовать existential rewrite вместо `trivialCert`.

## 3. План по сессиям

### Session 1 — `seqList_run_full`
**Файл:** `pnp3/Complexity/PsubsetPpolyInternal/TuringToolkit/ConstStatePhasedProgram.lean`
**LOC:** ~350
**Building blocks:** `runConfig_seq_succ_*` (lines 414-544), `seqList` (line 573)
**Deliverable:** generic `seqList_run_full` с motive-параметром `Configuration → S → Prop`, моделируемый по `runConfig_seq_succ_P2_*` (lines 488-544).
**Acceptance:** теорема typechecks, axiom audit ∈ `{propext, Classical.choice, Quot.sound}`.

### Session 2 — `writeVecOfNatProgram`
**Файл:** новый `pnp3/Complexity/PsubsetPpolyInternal/TuringToolkit/RowInputWriter.lean`
**LOC:** ~300
**Building blocks:** `incrementProgram_correct`, `CopyAtOffset.copyAtOffsetProgram_run_full`
**Deliverable:** `writeVecOfNatProgram` + `_run_full` теорема: после `timeBound N` шагов tape-регион `[Δrow .. Δrow+m)` равен `vecOfNat n i`.
**Acceptance:** теорема закрыта, регистрация в `lakefile.lean`.

### Session 3 — `mcspCheckAllRows_correct`
**Файл:** `pnp3/Complexity/PsubsetPpolyInternal/TuringToolkit/RowConsistencyCheck.lean` (расширение)
**LOC:** ~450
**Building blocks:** Session 1 (`seqList_run_full`), `circuitEvaluatorCS_run_correct_wf`, Session 2 (writeVecOfNat), `rowConsistencyCheckCSAt_row` (line 69)
**Deliverable:** `tape[Δflag]` после запуска = `List.any (List.ofFn …) inconsistent_at_row_i`.
**Acceptance:** теорема + axiom audit.

### Session 4 — Witness decoder
**Файл:** новый `pnp3/Complexity/PsubsetPpolyInternal/TuringToolkit/WitnessDecoder.lean`
**LOC:** ~250
**Building blocks:** `Encoding.lean` table layout, `CopyAtOffset.copyAtOffsetProgram_run_full`
**Deliverable:** `decodeCandidateSpec : Bitstring (certLen) → Option (CandidateSpec n)` + `decodeCandidateSpec_writeToTape_run_full` (записывает gate table в tape-регион) + `decodeCandidateSpec_surjective_on_valid_candidates`.
**Acceptance:** оба theorems closed.

### Session 5 — Length probe
**Файл:** новый `pnp3/Complexity/PsubsetPpolyInternal/TuringToolkit/LengthProbe.lean`
**LOC:** ~250
**Building blocks:** `incrementProgram_correct` (doubling), `UnaryAtOffset` для compare
**Deliverable:** `canonicalLengthCheckProgram` читает `m` из стандартного слота `w` и проверяет `n = 2·2^m` через walk + compare; возвращает `(m, true)` или `false`.
**Acceptance:** `canonicalLengthCheckProgram_run_full` closed.

### Session 6 — Top-level composition
**Файл:** новый `pnp3/Complexity/PsubsetPpolyInternal/TuringToolkit/CanonicalVerifierTM.lean`
**LOC:** ~500
**Building blocks:** Sessions 1-5, `decideAsymptotic_at_inputLen`, `decideAsymptotic_of_not_canonical`
**Deliverable:** `verifierProgram` + `verifierProgram_accepts_iff`:
```
TM.accepts (concatBitstring x w) = true ↔ candidateValid w ∧ decideAsymptotic n x = true
```
Non-canonical branch rejects через `decideAsymptotic_of_not_canonical`.
**Acceptance:** теорема + полный build.

### Session 7 — Runtime bound + Components term
**Файлы:**
- новый `pnp3/Magnification/CanonicalAsymptoticVerifierInstance.lean`
- edit `pnp3/Magnification/CanonicalAsymptoticDecider.lean` (struct + witness body, Variant B switch)
- edit `pnp3/Complexity/PsubsetPpolyInternal/GapMCSPVerifier.lean` (документация)
- edit `pnp3/Tests/CanonicalIntegrationTests.lean` (адаптировать examples к новой структуре)

**LOC:** ~450
**Building blocks:** `seqList_timeBound_le_uniform`, `mcspCheckAllRows_timeBound_le` (line 213), Session 6
**Deliverable:**
1. `verifierProgram_runTime_poly` с явными `c, k`.
2. `canonicalAsymptoticVerifierComponents : CanonicalAsymptoticVerifierComponents` (Variant B).
3. `witness` body переписан через existential rewrite.

**Acceptance:** `def canonicalAsymptoticVerifierComponents` typechecks; `#print axioms` ∈ `{propext, Classical.choice, Quot.sound}`; все `canonical_*` теоремы в `CanonicalIntegrationTests.lean` теперь безусловны (после применения `witness` к новому term'у).

## 4. Критические файлы (reusable pieces)

- `pnp3/Complexity/PsubsetPpolyInternal/TuringToolkit/BinaryCounter.lean:1315` — `incrementProgram_correct`
- `pnp3/Complexity/PsubsetPpolyInternal/TuringToolkit/CombineAtOffset.lean:1037` — `combineAtOffsetCS_run_full`
- `pnp3/Complexity/PsubsetPpolyInternal/TuringToolkit/GateWrappers.lean:5034` — `circuitEvaluatorCS_run_correct_wf`
- `pnp3/Complexity/PsubsetPpolyInternal/TuringToolkit/GateWrappers.lean:577` — `seqList_timeBound_le_uniform`
- `pnp3/Complexity/PsubsetPpolyInternal/TuringToolkit/ConstStatePhasedProgram.lean:414-544` — `runConfig_seq_succ_*` (для Session 1)
- `pnp3/Complexity/PsubsetPpolyInternal/TuringToolkit/RowConsistencyCheck.lean:69,175,213` — row primitives
- `pnp3/Magnification/CanonicalAsymptoticDecider.lean:192,206,223,244,271,296` — decider + bridge
- `pnp3/Models/Model_PartialMCSP.lean:883` — `GapPartialMCSP_Asymptotic_TMWitness`

## 5. Per-Session Verification Checklist

В конце каждой сессии:

1. **Build PnP3:**
   ```
   export PATH="$HOME/.elan/bin:$PATH" && cd /home/user/p-np2 && lake build PnP3
   ```
   Должен пройти без errors и без `sorry` warning'ов.

2. **Axiom audit** для новых top-level теорем: добавить `#print axioms T` в `scripts/audit_canonical_axioms.lean` и убедиться что output ⊆ `{propext, Classical.choice, Quot.sound}`.

3. **scripts/check.sh:**
   ```
   bash /home/user/p-np2/scripts/check.sh
   ```
   Exit 0.

4. **Регрессия по интеграции:** `pnp3/Tests/CanonicalIntegrationTests.lean` должен компилироваться. В Session 7 потребуется адаптация examples.

5. **0 sorry / 0 axiom политика:** `grep -c "sorry\|admit" pnp3/**/*.lean` остаётся 0; новых `axiom` деклараций нет.

6. **Commit + push:** одна сессия = один commit с явным сообщением `Session N: <leaf theorem name>`, push в `claude/audit-hnpbridge-interface-FnO1v`.

## 6. Cross-Session Risk Register

- **Session 1:** `seqList_run_full` требует гибкого motive-параметра `Configuration → S → Prop`. Иначе придётся переdoказывать на каждом call-site. Mitigation: моделировать по `runConfig_seq_succ_P2_*` (lines 488-544) с явным state predicate.
- **Session 3:** `OR_{i<2^m}` может вызвать `Decidable.decide`-vs-`Bool` mismatch с `circuitEvaluatorCS_run_correct_wf`. Mitigation: формулировать OR через `List.any` от старта.
- **Session 7:** Изменение `accepts_eq` — breaking API. Grep показывает только `Tests/CanonicalIntegrationTests.lean` (lines 124-152) и `GapMCSPVerifier.lean` (lines 91-101). Оба должны обновляться атомарно в той же сессии.

## 7. Финальное состояние после Session 7

- `Pnp3.Magnification.canonicalAsymptoticVerifierComponents` — concrete term.
- `Pnp3.Magnification.CanonicalAsymptoticVerifierComponents.witness canonicalAsymptoticVerifierComponents` — concrete `GapPartialMCSP_Asymptotic_TMWitness canonicalAsymptoticSpec`.
- Все `canonical_*_of_TM` теоремы в `CanonicalIntegrationTests.lean` инстанцируются на этот witness и становятся unconditional.
- Канонический асимптотический трек закрыт безусловно. Остаётся только research-level `ResearchGapWitness.dagSeparation` (отдельная проблема, не часть TM-верификатора).

**Total estimated work:** 7 сессий × средне ~350 LOC ≈ 2500 LOC новой инженерии плюс ~50 LOC правок к bridge-структуре.
