import Complexity.DagGadgets

/-!
# Fixed-width DAG-bundle composition surface tests

Definition pins and explicit full-proposition wrappers for the generic P1b-0
composition and gadget API.  Axiom roots live in `Tests/AxiomsAudit.lean`.
-/

namespace Pnp3.Tests.DagBundleCompose

open Pnp3.ComplexityInterfaces
open Pnp3.ComplexityInterfaces.DagCircuit

#check substBundle
#check identityBundle
#check DagBundle.evalFun
#check iterateBundle
#check reindexOutputs
#check projectionBundle
#check constantBundle
#check notCircuit
#check andCircuit
#check orCircuit
#check bigOrCircuit
#check size_bigOrCircuit
#check muxCircuit
#check notBundle
#check andBundle
#check orBundle
#check muxBundle

theorem check_substBundle_gates {m mid out : Nat}
    (S : DagBundle mid out) (B : DagBundle m mid) :
    (substBundle S B).gates = B.gates + S.gates :=
  substBundle_gates S B

theorem check_substBundle_output_no_growth {m mid out : Nat}
    (S : DagBundle mid out) (B : DagBundle m mid) :
    (substBundle S B).output = fun o : Fin out =>
      substWireWithBundle B (S.output o) :=
  substBundle_output_no_growth S B

theorem check_asCircuit_substBundle {m mid out : Nat}
    (S : DagBundle mid out) (B : DagBundle m mid) (o : Fin out) :
    (substBundle S B).asCircuit o = substInputsWithBundle (S.asCircuit o) B :=
  asCircuit_substBundle S B o

theorem check_evalOutput_substBundle {m mid out : Nat}
    (S : DagBundle mid out) (B : DagBundle m mid) (o : Fin out)
    (x : Bitstring m) :
    (substBundle S B).evalOutput o x =
      S.evalOutput o (fun j => B.evalOutput j x) :=
  evalOutput_substBundle S B o x

theorem check_identityBundle_gates (W : Nat) :
    (identityBundle W).gates = 0 :=
  identityBundle_gates W

theorem check_identityBundle_output (W : Nat) (o : Fin W) :
    (identityBundle W).output o = DagWire.input o :=
  identityBundle_output W o

theorem check_evalOutput_identityBundle (W : Nat) (o : Fin W)
    (v : Bitstring W) :
    (identityBundle W).evalOutput o v = v o :=
  evalOutput_identityBundle W o v

theorem check_evalFun_apply {n out : Nat} (B : DagBundle n out)
    (v : Bitstring n) (o : Fin out) :
    B.evalFun v o = B.evalOutput o v :=
  DagBundle.evalFun_apply B v o

theorem check_evalFun_identityBundle (W : Nat) (v : Bitstring W) :
    (identityBundle W).evalFun v = v :=
  evalFun_identityBundle W v

theorem check_reindexOutputs_gates {n out out' : Nat}
    (B : DagBundle n out) (f : Fin out' → Fin out) :
    (reindexOutputs B f).gates = B.gates :=
  reindexOutputs_gates B f

theorem check_evalOutput_reindexOutputs {n out out' : Nat}
    (B : DagBundle n out) (f : Fin out' → Fin out) (o : Fin out')
    (v : Bitstring n) :
    (reindexOutputs B f).evalOutput o v = B.evalOutput (f o) v :=
  evalOutput_reindexOutputs B f o v

theorem check_iterateBundle_zero {W : Nat} (S : DagBundle W W) :
    iterateBundle S 0 = identityBundle W :=
  iterateBundle_zero S

theorem check_iterateBundle_succ {W : Nat} (S : DagBundle W W) (t : Nat) :
    iterateBundle S (t + 1) = substBundle S (iterateBundle S t) :=
  iterateBundle_succ S t

theorem check_iterateBundle_gates {W : Nat} (S : DagBundle W W) (t : Nat) :
    (iterateBundle S t).gates = t * S.gates :=
  iterateBundle_gates S t

theorem check_evalOutput_iterateBundle {W : Nat} (S : DagBundle W W)
    (t : Nat) (v : Bitstring W) (o : Fin W) :
    (iterateBundle S t).evalOutput o v = (S.evalFun^[t]) v o :=
  evalOutput_iterateBundle S t v o

theorem check_iterateBundle_zero_gates {W : Nat} (S : DagBundle W W) :
    (iterateBundle S 0).gates = 0 :=
  iterateBundle_zero_gates S

theorem check_iterateBundle_one_gates {W : Nat} (S : DagBundle W W) :
    (iterateBundle S 1).gates = S.gates :=
  iterateBundle_one_gates S

theorem check_iterateBundle_two_gates {W : Nat} (S : DagBundle W W) :
    (iterateBundle S 2).gates = 2 * S.gates :=
  iterateBundle_two_gates S

theorem check_evalOutput_iterateBundle_zero {W : Nat} (S : DagBundle W W)
    (v : Bitstring W) (o : Fin W) :
    (iterateBundle S 0).evalOutput o v = v o :=
  evalOutput_iterateBundle_zero S v o

theorem check_evalOutput_iterateBundle_one {W : Nat} (S : DagBundle W W)
    (v : Bitstring W) (o : Fin W) :
    (iterateBundle S 1).evalOutput o v = S.evalOutput o v :=
  evalOutput_iterateBundle_one S v o

theorem check_evalOutput_iterateBundle_two {W : Nat} (S : DagBundle W W)
    (v : Bitstring W) (o : Fin W) :
    (iterateBundle S 2).evalOutput o v = S.evalFun (S.evalFun v) o :=
  evalOutput_iterateBundle_two S v o

theorem check_projectionBundle_gates {n : Nat} (j : Fin n) :
    (projectionBundle j).gates = 0 :=
  projectionBundle_gates j

theorem check_evalOutput_projectionBundle {n : Nat} (j : Fin n)
    (x : Bitstring n) :
    (projectionBundle j).evalOutput 0 x = x j :=
  evalOutput_projectionBundle j x

theorem check_constantBundle_gates (n : Nat) (b : Bool) :
    (constantBundle n b).gates = 1 :=
  constantBundle_gates n b

theorem check_evalOutput_constantBundle (n : Nat) (b : Bool)
    (x : Bitstring n) :
    (constantBundle n b).evalOutput 0 x = b :=
  evalOutput_constantBundle n b x

theorem check_notCircuit_gates : notCircuit.gates = 1 :=
  notCircuit_gates

theorem check_size_notCircuit : size notCircuit = 2 :=
  size_notCircuit

theorem check_eval_notCircuit (x : Bitstring 1) :
    eval notCircuit x = !x 0 :=
  eval_notCircuit x

theorem check_andCircuit_gates : andCircuit.gates = 1 :=
  andCircuit_gates

theorem check_size_andCircuit : size andCircuit = 2 :=
  size_andCircuit

theorem check_eval_andCircuit (x : Bitstring 2) :
    eval andCircuit x = (x 0 && x 1) :=
  eval_andCircuit x

theorem check_orCircuit_gates : orCircuit.gates = 1 :=
  orCircuit_gates

theorem check_size_orCircuit : size orCircuit = 2 :=
  size_orCircuit

theorem check_eval_orCircuit (x : Bitstring 2) :
    eval orCircuit x = (x 0 || x 1) :=
  eval_orCircuit x

theorem check_eval_bigOrCircuit {n : Nat} (Cs : List (DagCircuit n))
    (x : Bitstring n) :
    eval (bigOrCircuit Cs) x = Cs.any (fun C => eval C x) :=
  eval_bigOrCircuit Cs x

theorem check_eval_bigOrCircuit_map {n : Nat} {A : Type} (xs : List A)
    (C : A → DagCircuit n) (x : Bitstring n) :
    eval (bigOrCircuit (xs.map C)) x = xs.any (fun a => eval (C a) x) :=
  eval_bigOrCircuit_map xs C x

theorem check_eval_bigOrCircuit_finRange {n k : Nat}
    (C : Fin k → DagCircuit n) (x : Bitstring n) :
    eval (bigOrCircuit ((List.finRange k).map C)) x =
      (List.finRange k).any (fun i => eval (C i) x) :=
  eval_bigOrCircuit_finRange C x

theorem check_bigOrCircuit_gates {n : Nat} (Cs : List (DagCircuit n)) :
    (bigOrCircuit Cs).gates =
      1 + (Cs.map (fun C => C.gates + 1)).sum :=
  bigOrCircuit_gates Cs

theorem check_size_bigOrCircuit {n : Nat} (Cs : List (DagCircuit n)) :
    size (bigOrCircuit Cs) = 2 + (Cs.map size).sum :=
  size_bigOrCircuit Cs

theorem check_muxCircuit_gates : muxCircuit.gates = 4 :=
  muxCircuit_gates

theorem check_size_muxCircuit : size muxCircuit = 5 :=
  size_muxCircuit

theorem check_eval_muxCircuit (x : Bitstring 3) :
    eval muxCircuit x = if x 0 then x 1 else x 2 :=
  eval_muxCircuit x

theorem check_notBundle_gates : notBundle.gates = 1 :=
  notBundle_gates

theorem check_evalOutput_notBundle (x : Bitstring 1) :
    notBundle.evalOutput 0 x = !x 0 :=
  evalOutput_notBundle x

theorem check_andBundle_gates : andBundle.gates = 1 :=
  andBundle_gates

theorem check_evalOutput_andBundle (x : Bitstring 2) :
    andBundle.evalOutput 0 x = (x 0 && x 1) :=
  evalOutput_andBundle x

theorem check_orBundle_gates : orBundle.gates = 1 :=
  orBundle_gates

theorem check_evalOutput_orBundle (x : Bitstring 2) :
    orBundle.evalOutput 0 x = (x 0 || x 1) :=
  evalOutput_orBundle x

theorem check_muxBundle_gates : muxBundle.gates = 4 :=
  muxBundle_gates

theorem check_evalOutput_muxBundle (x : Bitstring 3) :
    muxBundle.evalOutput 0 x = if x 0 then x 1 else x 2 :=
  evalOutput_muxBundle x

theorem check_muxBundle_truthTable :
    (muxBundle.evalOutput 0 ![false, false, false] = false) ∧
    (muxBundle.evalOutput 0 ![false, false, true] = true) ∧
    (muxBundle.evalOutput 0 ![false, true, false] = false) ∧
    (muxBundle.evalOutput 0 ![false, true, true] = true) ∧
    (muxBundle.evalOutput 0 ![true, false, false] = false) ∧
    (muxBundle.evalOutput 0 ![true, false, true] = false) ∧
    (muxBundle.evalOutput 0 ![true, true, false] = true) ∧
    (muxBundle.evalOutput 0 ![true, true, true] = true) :=
  muxBundle_truthTable

theorem check_doubleNot_iteration (v : Bitstring 1) :
    (iterateBundle notBundle 2).evalOutput 0 v = v 0 :=
  doubleNot_iteration v

theorem check_doubleNot_false_literal :
    (iterateBundle notBundle 2).evalOutput 0 ![false] = false :=
  doubleNot_false_literal

end Pnp3.Tests.DagBundleCompose
