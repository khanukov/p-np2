# CircuitPHP search lower bound D0 audit (2026-05-22)

## Scope and progress classification

- **Classification:** Infrastructure + side-track audit.
- This note audits a candidate total-search source theorem and whether it gives a realistic bridge to
  `NP_not_subset_PpolyDAG`.
- Per repository mainline policy, this is **not** counted as mainline P-vs-NP progress unless a concrete
  bridge to `VerifiedNPDAGLowerBoundSource`/`SearchMCSPWeakLowerBound` is produced.

---

## 1) Exact search problem

Define the total search problem `CircuitPHP_m`:

- **Input:** Boolean circuit
  \[
  C : \{0,1\}^{m+1} \to \{0,1\}^{m}
  \]
  encoded as a binary string `⟨C⟩` of length `n` (typically `m <= poly(n)`).
- **Output:** a pair `(x,y)` with
  - `x,y ∈ {0,1}^{m+1}`,
  - `x ≠ y`,
  - `C(x)=C(y)`.

Totality is immediate by pigeonhole principle: `2^(m+1)` inputs map into `2^m` outputs.

Equivalent single-witness version:

- Output `x` plus a short certificate that there exists `y != x` with `C(y)=C(x)`.
- Or output an ordered pair `(x,y)` directly.

---

## 2) Prefix-extension language

Use the canonical NP prefix language attached to the search relation.

Let `R(C, w)` be: `w` decodes as `(x,y)` and `x != y` and `C(x)=C(y)`.

Define
\[
L_{pref} = \{ (\langle C\rangle, p) : \exists w \in \{0,1\}^{t(n)}\ \text{s.t.}\ p \preceq w\ \wedge\ R(C,w) \},
\]
where:
- `p` is a bit-prefix,
- `p \preceq w` means `p` is a prefix of `w`,
- `t(n)=2(m+1)` for direct pair encoding (or another polynomial bound with padding).

Interpretation: `(C,p)` is YES iff the prefix `p` can be extended to a valid collision witness.

---

## 3) Why `L_pref ∈ NP` (sketch)

NP verifier for `(⟨C⟩, p)`:

1. Guess suffix `s` so that `w = p || s` has exact target length `t(n)`.
2. Decode `w` as `(x,y)`.
3. Check `x != y`.
4. Evaluate circuit `C` on `x` and `y` and check equality.

All checks are polynomial in `|⟨C⟩|` (circuit evaluation is polynomial in circuit size), so `L_pref ∈ NP`.

---

## 4) `PpolyDAG` decider for `L_pref` ⇒ search solver (sketch)

Assume `L_pref ∈ PpolyDAG`:

- There is a polynomial-size DAG circuit family deciding if a prefix can be extended to a valid witness.

Then recover a witness by bit-by-bit self-reduction:

1. Start with empty prefix `p = ε`.
2. For `i = 1..t(n)`:
   - Query decider on `(C, p0)`.
   - If YES, set next bit `0`; else set `1`.
3. Final `p` has length `t(n)` and, by construction, is extendable at each step; at full length this means it is itself a valid witness.

Hence a polynomial-time (with nonuniform help inherited from decider family) search solver follows.

This is the standard NP-search-from-prefix-decision reduction used in source-theorem templates.

---

## 5) Attempt to build polynomial-size nonuniform search solver

### 5.1 Direct constructive attempts

- **Brute force over pairs**: requires exponential time/size.
- **Meet-in-the-middle hashing over all `x`**: still exponential in `m`.
- **Algebraic tricks**: no generic structure; circuit is arbitrary.
- **Randomized pair sampling**: finds collision with noticeable probability only after about `2^{m/2}` samples (birthday-type), not polynomial worst-case.

### 5.2 Nonuniform advice idea

Could advice hardwire, for each input circuit `C`, one collision pair?

- Not feasible with polynomial advice length because number of possible circuits of length `n` is exponential in `n`.
- A polynomial-size output circuit family cannot just table-lookup all `C`.

### 5.3 Structural shortcut attempts

- Pairing inputs `0z` and `1z` does **not** force `C(0z)=C(1z)`.
- Restricting to local neighborhoods of inputs gives no universal guarantee.

**Result of attack:** no trivial generic poly-size nonuniform solver was found.

---

## 6) Diagonal attack against arbitrary solver `S`

Target statement: for every polynomial-size circuit family `S` that outputs `(x,y)` from `⟨C⟩`, build a circuit `C_S` such that `S(⟨C_S⟩)` is not a valid collision.

### 6.1 Naive diagonal plan

1. Simulate `S` on description `⟨C⟩`.
2. Let `S` propose `(a,b)`.
3. Define `C` so that `C(a) != C(b)` while preserving totality constraints.

### 6.2 Barrier

- `C` appears in its own encoding supplied to `S`; this becomes a recursion/self-reference problem.
- Enforcing `C(a) != C(b)` while globally remaining a valid map from `m+1` bits to `m` bits is easy locally, but making this consistent with the fixed-point `⟨C⟩` dependence is hard.
- Standard fixed-point/diagonal gadgets here are essentially the same kind of hardness machinery needed in major circuit lower-bound programs.

### 6.3 Assessment

A full diagonal lower bound against arbitrary nonuniform `S` does **not** look elementary; it appears to require techniques comparable to core unresolved barriers.

---

## 7) Literature / proof-complexity audit map

This section is a route map (not a completeness claim):

1. **PHP search**
   - Circuit-collision search is the computational PHP principle.
   - Closely related to the canonical PPP-complete problem often called *PIGEONHOLE CIRCUIT*.

2. **Feasible interpolation**
   - If one can formalize short proofs of associated propositional encodings, interpolation may extract algorithms/circuits.
   - For lower bounds, one seeks proof-system lower bounds that imply algorithmic hardness of extracted objects.

3. **Bounded arithmetic**
   - Totality principles for PHP-type search are tied to provably total search classes of bounded arithmetic fragments.
   - Separation strength typically tracks difficult open problems in proof complexity.

4. **TFNP / PPP**
   - The problem is in TFNP and naturally in PPP.
   - Showing unconditional super-polynomial nonuniform lower bounds for such total search is currently far beyond routine methods.

5. **Circuit complexity of total search**
   - Known frameworks suggest this is meaningful, but direct `P/poly`-style lower bounds for explicit TFNP/PPP search tasks are notoriously difficult.

**Audit implication:** this candidate is conceptually natural but may be entangled with deep proof-complexity and TFNP barriers.

---

## 8) Verdict

- `GREEN_open_L0`: **No** (not clearly an easy-open L0 source).
- `RED_trivial_solver_exists`: **No evidence** of a trivial universal poly-size solver.
- `YELLOW_needs_proof_complexity_audit`: **Yes** (strongly).
- `RED_as_hard_as_main_gap`: **Leaning yes** for unconditional nonuniform lower bound ambitions.

### Final tag

## **YELLOW_needs_proof_complexity_audit**

with a secondary risk flag: **RED_as_hard_as_main_gap** if the goal is a full unconditional lower bound against arbitrary `PpolyDAG` search solvers.

Practical interpretation for pnp4 routing:

- Keep this as a **side-track candidate** until a concrete bridge to
  `SearchMCSPWeakLowerBound` / `VerifiedNPDAGLowerBoundSource` is explicitly exhibited.
- Do not report it as mainline `P != NP` progress yet.
