# L1 iso-strong conclusion report (codex)

## 1. Executive verdict

YELLOW_ONE_OF_THREE_LANDED

## 2. What landed

Landed (kernel-checked) sub-lemma family for the corrected combinatorial core:

- `card_Size1Candidate`:
  `Fintype.card (Size1Candidate n) = n + 2`.
- `exists_trace_not_size1_of_card_lt`:
  for any finite free-coordinate type `α` and embedding `α → Fin n`, if
  `n + 2 < 2 ^ Fintype.card α`, then there exists a Boolean labeling
  `label : α → Bool` that is different from every size-1 candidate trace.
- `exists_trace_not_size1`:
  instantiated to `α = (Finset.univ \ D).attach` with slack
  `p.n + 2 < 2 ^ ((Finset.univ \ D).card`.

Not landed in this session:

- construction of a valid encoding `z` from the non-candidate trace,
- the full bridge `exists_valid_agreeing_not_yes_under_slack`,
- the main theorem `isoStrong_conclusion_negative_for_canonical`.

## 3. Corrected pigeonhole argument

I explicitly did **not** use the false shortcut “YES cardinality ≤ m+2”.
That statement is not correct globally over partial tables, since one size-1
circuit may be consistent with many partial truth tables.

Instead, this session formalizes the correct diagonalization nucleus:

- size-1 candidate family has cardinality exactly `m+2`;
- each candidate induces one trace on the chosen free-coordinate domain;
- if `m+2 < 2^r`, then not all `2^r` labelings can be covered by those traces;
- therefore there exists a free-coordinate labeling not equal to any size-1 trace.

This is the precise trace-level pigeonhole step needed before constructing `z`.

## 4. Remaining blockers

1. Define the concrete free-coordinate trace map directly from consistency of
   `decodePartial z` with size-1 circuits, so the abstract diagonal label can be
   turned into an explicit `z` contradiction.
2. Build `z` by patching `decodePartial yYes` on `D` and setting free coordinates
   from the diagonal label, then prove:
   - `ValidEncoding p z`,
   - `AgreeOnValues D yYes z`,
   - `z ∉ (gapSliceOfParams p).Yes`.
3. Compose with the forcing clause from iso-strong and then finish the canonical
   contradiction theorem.

## 5. Next action

open_isoStrong_conclusion_L1_session_2
