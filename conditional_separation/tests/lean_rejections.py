"""Real Lean rejection tests; generic True checks NEVER prove R.

Use a separate freshly created PARTIAL attempt with the pinned dependencies
installed through Lake (or an independently verified external cache). Every
source variant and real compiler receipt is retained under its .lake directory.
This deliberately compiles rejected axiom/sorry fixtures only in that isolated
attempt; none is an active library assumption or a positive R test.
"""
import argparse,importlib.util,json,hashlib,sys,uuid
from pathlib import Path
if sys.flags.optimize:raise SystemExit("optimized tests rejected")
parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument("--attempt",required=True,type=Path)
args=parser.parse_args();A=args.attempt.resolve()
metadata=json.loads((A/"attempt.json").read_text());P=Path(metadata["core"]).resolve()
if (A/"Attempt.lean").read_bytes() != (P/"template/Attempt.lean").read_bytes():
 raise SystemExit("use a separate fresh PARTIAL template; existing research source is never overwritten")
C=A/".lake/rejection-suite"/str(uuid.uuid4());C.mkdir(parents=True);(C/"variants").mkdir()
spec=importlib.util.spec_from_file_location("workbench",P/"tools/workbench.py");m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)
records=[]
def body(text):
 p=A/"Attempt.lean";old=p.read_bytes();count=len(list((C/"variants").glob("attempt-*")))
 (C/"variants"/("attempt-"+str(count).zfill(3)+".lean.txt")).write_bytes(old)
 p.write_text(text,encoding="utf-8")
def actual(label,source,expected="ConditionalSeparation.OpenProblem.R",want=None,proof="Attempt.unit"):
 body(source);record=dict(case=label,source_sha256=hashlib.sha256((A/"Attempt.lean").read_bytes()).hexdigest(),qualification="generic validator only, NOT proof of R")
 try:
  value=m.check(A,proof,expected=expected,assemble=False)
  record.update(accepted=True,result=value,PASS=want is None)
 except (RuntimeError,ValueError,OSError) as error:
  record.update(accepted=False,error=str(error),PASS=want is not None)
  # Compilation rejection must hit its intended boundary, not import/resource failure.
  if want is not None and want not in ["prohibited active source token","installed module shadow rejected"]:
   runs=sorted((A/".lake/conditional-check/runs").iterdir(),key=lambda p:p.stat().st_mtime_ns)
   logs="\n".join(p.read_text() for p in runs[-1].rglob("stdout.txt"))
   record["PASS"]=want in logs
  elif want is not None:record["PASS"]=want in str(error)
 records.append(record);print(json.dumps({k:v for k,v in record.items() if k in ["case","accepted","PASS","error"]}),flush=True)
 if not record["PASS"]:raise RuntimeError("unexpected native DATA result: "+label)
header="import ConditionalSeparation.OpenProblem\nnamespace Attempt\n"
actual("closed_True_positive",header+"theorem unit : True := True.intro\ntheorem check_unit : True := unit\n#print axioms check_unit\nend Attempt\n",expected="True")
actual("closed_True_warm_positive",header+"theorem unit : True := True.intro\ntheorem check_unit : True := unit\n#print axioms check_unit\nend Attempt\n",expected="True")
actual("R_arrow_R_rejected",header+"theorem unit (h : ConditionalSeparation.OpenProblem.R) : ConditionalSeparation.OpenProblem.R := h\nend Attempt\n",want="CLOSED exact expected type")
actual("hidden_False_premise_rejected",header+"theorem unit {_h : False} : ConditionalSeparation.OpenProblem.R := False.elim _h\nend Attempt\n",want="CLOSED exact expected type")
wrong="""open Pnp4.Frontier Pnp4.Frontier.ContractExpansion
def unit : Prop := ∀ d : Nat, ∃ k : Nat, ¬ Nonempty
  (BoundedSearchSolver
    (treeMCSPSearchProblem (thresholdPoly k)
      (TreeMCSPSearchWitnessEncoding.ofCodec (treeCircuitWitnessCodec (thresholdPoly k))))
    C_DAG (fun n => (Pnp3.Models.Partial.tableLen n)^d+d))
"""
actual("wrong_fixed_k_order_definition_rejected",header+wrong+"end Attempt\n",want="CLOSED exact expected type")
actual("weaker_True_is_not_R",header+"theorem unit : True := True.intro\nend Attempt\n",want="CLOSED exact expected type")
decoy="""namespace ConditionalSeparation.OpenProblem
def R : Prop := True
#check (R : Prop)
end ConditionalSeparation.OpenProblem
namespace Attempt
theorem unit : ConditionalSeparation.OpenProblem.R := True.intro
theorem check_unit : ConditionalSeparation.OpenProblem.R := unit
#print axioms unit
#print axioms check_unit
end Attempt
""".replace("\n+","\n")
actual("decoy_R_namespace_rejected",decoy,want="environment already contains 'ConditionalSeparation.OpenProblem.R'")
shadow=A/"ConditionalSeparation/OpenProblem.lean";shadow.parent.mkdir()
shadow.write_text("def untrusted : Nat := 0\n")
actual("installed_module_shadow_policy",header+"theorem unit : True := True.intro\nend Attempt\n",want="installed module shadow rejected")
(C/"rejected-shadow-source.lean.txt").write_bytes(shadow.read_bytes());shadow.unlink();shadow.parent.rmdir()
for label,statement in [
 ("sorry","theorem unit : ConditionalSeparation.OpenProblem.R := by sorry"),
 ("admit","theorem unit : ConditionalSeparation.OpenProblem.R := by admit"),
 ("custom_R_axiom","axiom unit : ConditionalSeparation.OpenProblem.R"),
 ("assumed_False","axiom bad : False\ntheorem unit : ConditionalSeparation.OpenProblem.R := False.elim bad"),
 ("native_decide","theorem unit : True := by native_decide"),
 ("unsafe","unsafe def unit : Nat := 0")]:
 actual(label+"_policy_rejected",header+statement+"\nend Attempt\n",want="prohibited active source token")
# Bypass ONLY the lexical convenience policy for finite generic True kernel DATA.
# This exercises actual transitive-axiom rejection, never production/core acceptance.
for label,statement in [
 ("custom_True_axiom","axiom unit : True"),
 ("False_transitive_axiom","axiom bad : False\ntheorem unit : True := False.elim bad"),
 ("sorryAx","set_option warningAsError false in\ntheorem unit : True := by sorry"),
 ("native_decide_axiom","theorem unit : True := by native_decide")]:
 body(header+statement+"\nend Attempt\n")
 root=A/".lake/conditional-check/kernel-DATA"/str(uuid.uuid4());root.mkdir(parents=True)
 parts=m.compile_source(A,root,"fixture",A/"Attempt.lean","Attempt",{})
 consumer=A/".lake/conditional-check/Consumer.lean";consumer.write_text(m.guard_source("Attempt.unit","True"))
 try:m.compile_source(A,root,"axiom-guard",consumer,"Consumer",{"Attempt":parts})
 except RuntimeError as error:
  log=(root/"axiom-guard-compile/stdout.txt").read_text();ok="nonallowed axiom" in log
  records.append(dict(case=label+"_actual_kernel_guard",PASS=ok,accepted=False,error=str(error),receipts=str(root),lexical_policy_bypassed_only_in_internal_True_test=True))
  print(json.dumps({"case":label+"_actual_kernel_guard","PASS":ok}),flush=True)
  if not ok:raise RuntimeError("wrong kernel rejection boundary")
 else:raise RuntimeError("nonallowed axiom accepted")
# Exercise the kernel's exact type boundary on literal changed search quantifiers.
for label,statement in [
 ("literal_wrong_fixed_k_order", "∀ d : Nat, ∃ k : Nat, ¬ Nonempty (BoundedSearchSolver (treeMCSPSearchProblem (thresholdPoly k) (TreeMCSPSearchWitnessEncoding.ofCodec (treeCircuitWitnessCodec (thresholdPoly k)))) C_DAG (fun n => (Pnp3.Models.Partial.tableLen n)^d+d))"),
 ("only_degree_zero_is_weaker", "∃ k : Nat, ¬ Nonempty (BoundedSearchSolver (treeMCSPSearchProblem (thresholdPoly k) (TreeMCSPSearchWitnessEncoding.ofCodec (treeCircuitWitnessCodec (thresholdPoly k)))) C_DAG (fun n => (Pnp3.Models.Partial.tableLen n)^0+0))")]:
 body(header+"open Pnp4.Frontier Pnp4.Frontier.ContractExpansion\naxiom unit : "+statement+"\nend Attempt\n")
 root=A/".lake/conditional-check/type-DATA"/str(uuid.uuid4());root.mkdir(parents=True)
 parts=m.compile_source(A,root,"fixture",A/"Attempt.lean","Attempt",{})
 consumer=A/".lake/conditional-check/Consumer.lean";consumer.write_text(m.guard_source("Attempt.unit","ConditionalSeparation.OpenProblem.R"))
 try:m.compile_source(A,root,"type-guard",consumer,"Consumer",{"Attempt":parts})
 except RuntimeError as error:
  log=(root/"type-guard-compile/stdout.txt").read_text();ok="CLOSED exact expected type" in log
  records.append(dict(case=label,PASS=ok,accepted=False,error=str(error),receipts=str(root),isolated_axiom_fixture_NOT_a_proof=True))
  if not ok:raise RuntimeError("wrong literal type rejection boundary")
 else:raise RuntimeError("changed search quantifiers accepted")
# Valid commented import, complete fresh helper output and ignored attempt Lake code.
helper=A/"Attempt/Helper.lean";helper.parent.mkdir()
helper.write_text("namespace Attempt.Helper\ndef value : Nat := 2\n#check (value : Nat)\n#print axioms value\nend Attempt.Helper\n")
saved_lake=(A/"lakefile.lean").read_bytes()
(C/"original-attempt-lakefile.lean.txt").write_bytes(saved_lake)
(A/"lakefile.lean").write_text("-- INVALID AS LAKE CONFIG; checker must use the installed core workspace\n")
fresh="""import/- actual token gap -/ Attempt.Helper
namespace Attempt
theorem value_is_two : Attempt.Helper.value = 2 := by decide
theorem check_value_is_two : Attempt.Helper.value = 2 := value_is_two
theorem unit : True := True.intro
theorem check_unit : True := unit
#print axioms value_is_two
#print axioms check_value_is_two
#print axioms check_unit
end Attempt
"""
actual("fresh_commented_import_and_core_workspace",fresh,expected="True")
(C/"commented-import-helper.lean.txt").write_bytes(helper.read_bytes())
(C/"ignored-attempt-lakefile.lean.txt").write_bytes((A/"lakefile.lean").read_bytes())
helper.unlink();helper.parent.rmdir();(A/"lakefile.lean").write_bytes(saved_lake)
# Restore actual partial template and genuinely reject its missing named proof.
actual("partial_template_missing_proof",(P/"template/Attempt.lean").read_text(),proof="Attempt.research_lower_bound",want="missing closed proof")
result=dict(records=records,positive_generic_True=sum(v.get("accepted",False) for v in records),rejections=sum(not v.get("accepted",False) for v in records),failures=sum(not v["PASS"] for v in records),R_proved=False)
(C/"NATIVE_CHECKER_RESULTS.json").write_text(json.dumps(result,indent=2)+"\n")
print(json.dumps({k:v for k,v in result.items() if k!="records"}),flush=True)
