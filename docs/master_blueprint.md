# Master Blueprint 2025 → 20XX

This note summarizes a long-term plan towards a formal proof that `P ≠ NP`.
The outline below condenses ongoing discussions and research snippets.  It is
not a proof, but a roadmap for the remaining steps.

## 0. Foundation

* Consolidate all published arguments into a single machine-checked corpus.
* Formalise the lower bound for `MCSPpoly` against $AC^0_d$ and the
  magnification theorem.  From these, derive
  `$NP \nsubseteq P/\mathsf{poly}$` under a weak assumption.

## 1. From restricted to general models

Strengthen the current linear lower bound for `MCSP` in restricted circuits to
an $(1+\varepsilon)$ exponent for all depth $o(\log N)$ circuits.  The goal is
to avoid the Natural Proofs barrier by working with sparse languages.

## 2. Trigger magnification

Apply the magnification theorem to the improved bound from step 1, obtaining the
non-uniform separation `$NP \nsubseteq P/\mathsf{poly}`.

## 3. Break algebrisation / relativisation

Develop a meet-in-the-middle SAT algorithm for compositions `ACC⁰ ∘ MCSP` or, if
that fails, argue that the previous steps already go beyond algebrising
techniques.  Key pieces are a structural compression lemma ("Lemma B") and its
consequences for sub-exponential SAT.

## 4. Uniformisation

Convert the non-uniform separation into `$P ≠ NP` using weak-uniform
translations (e.g. Rossman–Williams) and the Karp–Lipton argument.  Verify that
a potential collapse of `PH` cannot bypass the conclusion.

## 5. Proof-complexity lock-in

As an alternative route, show strong lower bounds for Extended Frege proofs.
Combined with the previous steps, this would also yield `$P ≠ NP`.

## 6. Cryptographic connection

Relate the hardness of `MCSP` to pseudorandom generator constructions and
one-way functions.  Establishing such a generator would reinforce the failure of
Natural Proofs and provide an independent path to `$P ≠ NP`.

## 7. Verification and publication

Machine-check every component, provide demo code for the SAT algorithms, and
maintain a public repository with Lean scripts and accompanying notes.

---

### Current status

Much of the foundational material (Step 0) is available in print but only partly
formalised.  Steps 1–3 are active research; the key missing piece is proving a
rectangular cover of `ACC⁰ ∘ MCSP` tables of size at most `2^{N - N^{\delta}}`.
The `coreAgreement` lemma, which underpins the combinatorial part of
the cover construction, has recently been formalised in Lean.  Later
steps depend on this breakthrough.

This document records the plan for future reference and serves as a pointer for
contributors interested in the overarching project.
