/-!
# Candidate proof file template

**This is a template, not a real candidate.**  The `SourceTheorem_template`
and `gap_from_template` declarations below are placeholders that
intentionally do not prove their stated targets.  Real candidates copy
this directory to `pnp3/Candidates/<method-family>/<candidate-id>/`,
replace the placeholders with concrete claims, and run
`scripts/verify_candidate.sh --candidate <dir>`.

This file is **excluded from `lake build`** by virtue of not being
listed in `lakefile.lean::[lean_lib PnP3].globs`.  It is loaded by
`scripts/verify_candidate.sh` only.

Per `RESEARCH_CONSTITUTION.md`:

* Rule 4 — `SourceTheorem_<id>` ≤ 40 lines; dependency closure ≤ 200
  lines (see `spec/source_theorem_size_policy.md`).
* Rule 5 — no arbitrary `PpolyFormula` quantification without an
  exclusion lemma.
* Rule 16 — no hidden payload providers (`class`, `instance`,
  `Fact ...`, `opaque`, `noncomputable def Provider/Default/Payload/
  Witness/Source/Gap`).
-/

namespace Pnp3
namespace Candidates
namespace Template

/--
Placeholder source theorem.  A real candidate replaces this with its
actual mathematical claim, written in a single self-contained `Prop`.
-/
def SourceTheorem_template : Prop := True

/--
Placeholder bridge.  A real candidate proves a non-trivial implication
from `SourceTheorem_template` to a `ResearchGapWitness`.  The signature
must be:

    gap_from_<id> :
      SourceTheorem_<id> →
      Pnp3.Magnification.ResearchGapWitness

For the template we just record `True → True`; this is **not** a
candidate, only a shape skeleton.
-/
example (h : SourceTheorem_template) : True := h

end Template
end Candidates
end Pnp3
