import Pnp4.Frontier.ContractExpansion.TreeMCSPEncodePreorder

/-!
# `ValidCertTokens` — D2t-5b: certificate-token validity (closes the `encodePreToken` lossiness gap)

`encodePreToken` maps the non-certificate leaves `notGate`/`andGate`/`orGate` to `[]` (they never occur in
a `preorder` stream — they are produced by `settle`, not read from the certificate).  Because `PreToken.leaf`
accepts *any* `SLGate`, a *malformed* token list like `[PreToken.leaf (SLGate.notGate i)]` encodes to `[]`,
which would let the certificate clause of `driverTapeInv` (`windowSpells … (encodePreorder st.toks)`) hold
**vacuously** for a state that still has an unread token — so `driverTapeInv` on its own is not yet a
faithful "the unread certificate is on the tape" statement for *arbitrary* `DriveState`s.

This module supplies the predicate and the key facts that **neutralise** that gap (the first ingredient of
the eventual strong driver invariant):

* `ValidCertToken` / `ValidCertTokens` — a token is valid iff it is a leaf `input`/`const` or an internal
  `node` (exactly what `preorder` produces); the lossy `notGate`/`andGate`/`orGate` leaves are excluded.
* `validCertToken_one_le_length` — every valid token encodes to **≥ 1** tape cell (so it is never lossy).
* `validCertTokens_preorder` — `preorder c` is valid (every reachable `toks` is a suffix of it, hence also
  valid — `step` only ever consumes tokens).
* `validCertTokens_length_le` — for valid `toks`, `toks.length ≤ (encodePreorder … toks).length`.
* **`validCertTokens_encodePreorder_eq_nil_iff`** — for valid `toks`, the certificate encoding is empty
  **iff** there are no unread tokens.  This is the non-vacuity fact: under `ValidCertTokens`, the
  certificate clause of `driverTapeInv` is empty exactly when `toks = []`, so it cannot be satisfied
  vacuously while an unread token remains.

**Progress classification (AGENTS.md): Infrastructure** — a pure validity predicate + non-vacuity facts for
the certificate codec; builds no machine and proves no separation.  Standard `[propext, Classical.choice,
Quot.sound]` triple only.  **No `P ≠ NP` claim.**
-/

namespace Pnp4
namespace Frontier
namespace ContractExpansion

open Pnp3.Internal.PsubsetPpoly.TM.Encoding

/-- A `PreToken` is a valid **certificate** token iff it is a leaf `input`/`const` or an internal `node` —
exactly the tokens `preorder` produces.  The `notGate`/`andGate`/`orGate` leaves (which `encodePreToken`
maps lossily to `[]`) are excluded. -/
def ValidCertToken {n : Nat} : PreToken n → Prop
  | .leaf (SLGate.input _) => True
  | .leaf (SLGate.const _) => True
  | .leaf (SLGate.notGate _) => False
  | .leaf (SLGate.andGate _ _) => False
  | .leaf (SLGate.orGate _ _) => False
  | .node _ => True

/-- A token list is a valid certificate stream iff every token is valid. -/
def ValidCertTokens {n : Nat} (toks : List (PreToken n)) : Prop :=
  ∀ t ∈ toks, ValidCertToken t

/-- Every **valid** certificate token encodes to at least one tape cell — so it is never lossy.  (The
excluded `notGate`/`andGate`/`orGate` leaves are the only ones `encodePreToken` sends to `[]`.) -/
theorem validCertToken_one_le_length {n : Nat} (width : Nat) (h_width : n ≤ 2 ^ width)
    {t : PreToken n} (ht : ValidCertToken t) : 1 ≤ (encodePreToken width h_width t).length := by
  cases t with
  | node tag => cases tag <;> simp only [encodePreToken, List.length_cons, List.length_nil] <;> omega
  | leaf g =>
      cases g with
      | input i =>
          simp only [encodePreToken, List.length_append, List.length_cons, List.length_nil]; omega
      | const b => simp only [encodePreToken, List.length_cons, List.length_nil]; omega
      | notGate i => simp only [ValidCertToken] at ht
      | andGate i j => simp only [ValidCertToken] at ht
      | orGate i j => simp only [ValidCertToken] at ht

/-- `preorder c` is a valid certificate stream — every token it produces is a leaf `input`/`const` or a
`node`.  (Since `DriveState.step` only ever *consumes* tokens, every reachable `toks` is a suffix of
`preorder c`, hence also valid.) -/
theorem validCertTokens_preorder {n : Nat} (c : CircuitTree n) : ValidCertTokens (preorder c) := by
  induction c with
  | input i => intro t ht; simp only [preorder, List.mem_singleton] at ht; subst ht; trivial
  | const b => intro t ht; simp only [preorder, List.mem_singleton] at ht; subst ht; trivial
  | not c ih =>
      intro t ht
      simp only [preorder, List.mem_cons] at ht
      rcases ht with rfl | ht
      · trivial
      · exact ih t ht
  | and a b iha ihb =>
      intro t ht
      simp only [preorder, List.mem_cons, List.mem_append] at ht
      rcases ht with rfl | ht | ht
      · trivial
      · exact iha t ht
      · exact ihb t ht
  | or a b iha ihb =>
      intro t ht
      simp only [preorder, List.mem_cons, List.mem_append] at ht
      rcases ht with rfl | ht | ht
      · trivial
      · exact iha t ht
      · exact ihb t ht

/-- For a valid token stream, the encoded certificate is at least as long as the token count (each token
contributes ≥ 1 cell). -/
theorem validCertTokens_length_le {n : Nat} (width : Nat) (h_width : n ≤ 2 ^ width) :
    ∀ {toks : List (PreToken n)}, ValidCertTokens toks →
      toks.length ≤ (encodePreorder width h_width toks).length := by
  intro toks
  induction toks with
  | nil => intro _; simp
  | cons t ts ih =>
      intro hv
      have ht : ValidCertToken t := hv t List.mem_cons_self
      have hts : ValidCertTokens ts := fun x hx => hv x (List.mem_cons_of_mem t hx)
      have h1 := validCertToken_one_le_length width h_width ht
      have h2 := ih hts
      simp only [encodePreorder_cons, List.length_cons, List.length_append]
      omega

/-- **Non-vacuity.**  For a valid token stream, the encoded certificate is empty **iff** the stream is
empty — so the certificate clause of `driverTapeInv` cannot hold vacuously while an unread token remains.
This closes the `encodePreToken` lossiness gap once `ValidCertTokens` is required of the driver state. -/
theorem validCertTokens_encodePreorder_eq_nil_iff {n : Nat} (width : Nat) (h_width : n ≤ 2 ^ width)
    {toks : List (PreToken n)} (hv : ValidCertTokens toks) :
    encodePreorder width h_width toks = [] ↔ toks = [] := by
  constructor
  · intro he
    have hlen := validCertTokens_length_le width h_width hv
    rw [he, List.length_nil] at hlen
    exact List.length_eq_zero_iff.mp (Nat.le_zero.mp hlen)
  · intro he; subst he; simp

end ContractExpansion
end Frontier
end Pnp4
