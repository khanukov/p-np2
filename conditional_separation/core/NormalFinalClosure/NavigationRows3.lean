import NormalFinalClosure.CounterSupport2
import NormalFinalClosure.Navigation2
namespace NormalFinalClosure
open Pnp3.Complexity.Uniform.V1 Lean Elab Command Tactic
run_cmd do
  let e←getEnv
  for (owner,ns,leaves) in [
    (`NormalFinalClosure.Rows2Code,`NormalFinalClosure,["ns2","Safe2","ns2_safe"]),
    (`NormalFinalClosure.CounterSupport2,`NormalFinalClosure,["nativeRow"]),
    (`PhysicalCallerClosure.Engine,`PhysicalCallerClosure,["FromHRows"]),
    (`NormalFinalClosure.Navigation2,`NormalFinalClosure,["HToSRows","SToHRows","DToHRows"])] do
    for leaf in leaves do
      let name:=Name.str (Name.append (Name.num (Name.append `_private owner) 0) ns) leaf
      let some ci:=e.find? name | throwError "Missing exact navigation certificate API"
      let some i:=e.getModuleIdxFor? name | throwError "Missing navigation certificate owner"
      unless i.toNat<e.header.moduleNames.size && e.header.moduleNames[i]! == owner do throwError "Wrong navigation certificate owner"
      let kind:=match ci with|.defnInfo _=>"definition"|.thmInfo _=>"theorem"|_=>"other"
      unless kind != "other" do throwError "Wrong navigation certificate kind"
      logInfo m!"literal-navigation-certificate-interface|{name}|{kind}|{ci.type}"
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous leaf) name::st.openDecls}
private theorem h_to_d_1985 (k : Nat) : FromHRows (Safe:=Safe2 k) (ns2 k 1985) (ns2 k 850) := by
  refine ⟨ns2 k 1986,ns2 k 1987,ns2_safe k 1985,ns2_safe k 1986,ns2_safe k 1987,?_,?_,?_,?_,?_,?_⟩
  · run_tac nativeRow
  · run_tac nativeRow
  · run_tac nativeRow
  · run_tac nativeRow
  · run_tac nativeRow
  · run_tac nativeRow

private theorem s_to_h_1989 (k : Nat) : SToHRows (Safe:=Safe2 k) (ns2 k 1989) (ns2 k 1992) := by
  refine ⟨ns2 k 1990,ns2 k 1991,ns2_safe k 1989,ns2_safe k 1990,ns2_safe k 1991,?_,?_,?_,?_,?_⟩
  · run_tac nativeRow
  · intro b;cases b <;> (run_tac nativeRow)
  · run_tac nativeRow
  · intro b;cases b <;> (run_tac nativeRow)
  · run_tac nativeRow

private theorem h_to_d_1992 (k : Nat) : FromHRows (Safe:=Safe2 k) (ns2 k 1992) (ns2 k 1628) := by
  refine ⟨ns2 k 1993,ns2 k 1994,ns2_safe k 1992,ns2_safe k 1993,ns2_safe k 1994,?_,?_,?_,?_,?_,?_⟩
  · run_tac nativeRow
  · run_tac nativeRow
  · run_tac nativeRow
  · run_tac nativeRow
  · run_tac nativeRow
  · run_tac nativeRow

private theorem s_to_h_1995 (k : Nat) : SToHRows (Safe:=Safe2 k) (ns2 k 1995) (ns2 k 1998) := by
  refine ⟨ns2 k 1996,ns2 k 1997,ns2_safe k 1995,ns2_safe k 1996,ns2_safe k 1997,?_,?_,?_,?_,?_⟩
  · run_tac nativeRow
  · intro b;cases b <;> (run_tac nativeRow)
  · run_tac nativeRow
  · intro b;cases b <;> (run_tac nativeRow)
  · run_tac nativeRow

private theorem h_to_d_1998 (k : Nat) : FromHRows (Safe:=Safe2 k) (ns2 k 1998) (ns2 k 2434) := by
  refine ⟨ns2 k 1999,ns2 k 2000,ns2_safe k 1998,ns2_safe k 1999,ns2_safe k 2000,?_,?_,?_,?_,?_,?_⟩
  · run_tac nativeRow
  · run_tac nativeRow
  · run_tac nativeRow
  · run_tac nativeRow
  · run_tac nativeRow
  · run_tac nativeRow

private theorem d_to_h_2281 (k : Nat) : DToHRows (Safe:=Safe2 k) (ns2 k 2281) (ns2 k 2285) := by
  refine ⟨ns2 k 2282,ns2 k 2283,ns2 k 2284,ns2_safe k 2281,ns2_safe k 2282,ns2_safe k 2283,ns2_safe k 2284,?_,?_,?_,?_,?_,?_⟩
  · run_tac nativeRow
  · run_tac nativeRow
  · run_tac nativeRow
  · run_tac nativeRow
  · run_tac nativeRow
  · run_tac nativeRow

private theorem h_to_s_2285 (k : Nat) : HToSRows (Safe:=Safe2 k) (ns2 k 2285) (ns2 k 2288) := by
  refine ⟨ns2 k 2286,ns2 k 2287,ns2_safe k 2285,ns2_safe k 2286,ns2_safe k 2287,?_,?_,?_,?_,?_⟩
  · run_tac nativeRow
  · intro b;cases b <;> (run_tac nativeRow)
  · run_tac nativeRow
  · intro b;cases b <;> (run_tac nativeRow)
  · run_tac nativeRow

private theorem s_to_h_2293 (k : Nat) : SToHRows (Safe:=Safe2 k) (ns2 k 2293) (ns2 k 2296) := by
  refine ⟨ns2 k 2294,ns2 k 2295,ns2_safe k 2293,ns2_safe k 2294,ns2_safe k 2295,?_,?_,?_,?_,?_⟩
  · run_tac nativeRow
  · intro b;cases b <;> (run_tac nativeRow)
  · run_tac nativeRow
  · intro b;cases b <;> (run_tac nativeRow)
  · run_tac nativeRow

private theorem h_to_d_2296 (k : Nat) : FromHRows (Safe:=Safe2 k) (ns2 k 2296) (ns2 k 1277) := by
  refine ⟨ns2 k 2297,ns2 k 2298,ns2_safe k 2296,ns2_safe k 2297,ns2_safe k 2298,?_,?_,?_,?_,?_,?_⟩
  · run_tac nativeRow
  · run_tac nativeRow
  · run_tac nativeRow
  · run_tac nativeRow
  · run_tac nativeRow
  · run_tac nativeRow

private theorem s_to_h_2300 (k : Nat) : SToHRows (Safe:=Safe2 k) (ns2 k 2300) (ns2 k 2303) := by
  refine ⟨ns2 k 2301,ns2 k 2302,ns2_safe k 2300,ns2_safe k 2301,ns2_safe k 2302,?_,?_,?_,?_,?_⟩
  · run_tac nativeRow
  · intro b;cases b <;> (run_tac nativeRow)
  · run_tac nativeRow
  · intro b;cases b <;> (run_tac nativeRow)
  · run_tac nativeRow

private theorem h_to_d_2303 (k : Nat) : FromHRows (Safe:=Safe2 k) (ns2 k 2303) (ns2 k 2129) := by
  refine ⟨ns2 k 2304,ns2 k 2305,ns2_safe k 2303,ns2_safe k 2304,ns2_safe k 2305,?_,?_,?_,?_,?_,?_⟩
  · run_tac nativeRow
  · run_tac nativeRow
  · run_tac nativeRow
  · run_tac nativeRow
  · run_tac nativeRow
  · run_tac nativeRow

private theorem s_to_h_2306 (k : Nat) : SToHRows (Safe:=Safe2 k) (ns2 k 2306) (ns2 k 2309) := by
  refine ⟨ns2 k 2307,ns2 k 2308,ns2_safe k 2306,ns2_safe k 2307,ns2_safe k 2308,?_,?_,?_,?_,?_⟩
  · run_tac nativeRow
  · intro b;cases b <;> (run_tac nativeRow)
  · run_tac nativeRow
  · intro b;cases b <;> (run_tac nativeRow)
  · run_tac nativeRow

private theorem h_to_d_2309 (k : Nat) : FromHRows (Safe:=Safe2 k) (ns2 k 2309) (ns2 k 2831) := by
  refine ⟨ns2 k 2310,ns2 k 2311,ns2_safe k 2309,ns2_safe k 2310,ns2_safe k 2311,?_,?_,?_,?_,?_,?_⟩
  · run_tac nativeRow
  · run_tac nativeRow
  · run_tac nativeRow
  · run_tac nativeRow
  · run_tac nativeRow
  · run_tac nativeRow

private theorem d_to_h_2403 (k : Nat) : DToHRows (Safe:=Safe2 k) (ns2 k 2403) (ns2 k 2407) := by
  refine ⟨ns2 k 2404,ns2 k 2405,ns2 k 2406,ns2_safe k 2403,ns2_safe k 2404,ns2_safe k 2405,ns2_safe k 2406,?_,?_,?_,?_,?_,?_⟩
  · run_tac nativeRow
  · run_tac nativeRow
  · run_tac nativeRow
  · run_tac nativeRow
  · run_tac nativeRow
  · run_tac nativeRow

private theorem h_to_s_2407 (k : Nat) : HToSRows (Safe:=Safe2 k) (ns2 k 2407) (ns2 k 2410) := by
  refine ⟨ns2 k 2408,ns2 k 2409,ns2_safe k 2407,ns2_safe k 2408,ns2_safe k 2409,?_,?_,?_,?_,?_⟩
  · run_tac nativeRow
  · intro b;cases b <;> (run_tac nativeRow)
  · run_tac nativeRow
  · intro b;cases b <;> (run_tac nativeRow)
  · run_tac nativeRow

private theorem s_to_h_2415 (k : Nat) : SToHRows (Safe:=Safe2 k) (ns2 k 2415) (ns2 k 2418) := by
  refine ⟨ns2 k 2416,ns2 k 2417,ns2_safe k 2415,ns2_safe k 2416,ns2_safe k 2417,?_,?_,?_,?_,?_⟩
  · run_tac nativeRow
  · intro b;cases b <;> (run_tac nativeRow)
  · run_tac nativeRow
  · intro b;cases b <;> (run_tac nativeRow)
  · run_tac nativeRow

private theorem h_to_d_2418 (k : Nat) : FromHRows (Safe:=Safe2 k) (ns2 k 2418) (ns2 k 1506) := by
  refine ⟨ns2 k 2419,ns2 k 2420,ns2_safe k 2418,ns2_safe k 2419,ns2_safe k 2420,?_,?_,?_,?_,?_,?_⟩
  · run_tac nativeRow
  · run_tac nativeRow
  · run_tac nativeRow
  · run_tac nativeRow
  · run_tac nativeRow
  · run_tac nativeRow

private theorem s_to_h_2422 (k : Nat) : SToHRows (Safe:=Safe2 k) (ns2 k 2422) (ns2 k 2425) := by
  refine ⟨ns2 k 2423,ns2 k 2424,ns2_safe k 2422,ns2_safe k 2423,ns2_safe k 2424,?_,?_,?_,?_,?_⟩
  · run_tac nativeRow
  · intro b;cases b <;> (run_tac nativeRow)
  · run_tac nativeRow
  · intro b;cases b <;> (run_tac nativeRow)
  · run_tac nativeRow

private theorem h_to_d_2425 (k : Nat) : FromHRows (Safe:=Safe2 k) (ns2 k 2425) (ns2 k 2312) := by
  refine ⟨ns2 k 2426,ns2 k 2427,ns2_safe k 2425,ns2_safe k 2426,ns2_safe k 2427,?_,?_,?_,?_,?_,?_⟩
  · run_tac nativeRow
  · run_tac nativeRow
  · run_tac nativeRow
  · run_tac nativeRow
  · run_tac nativeRow
  · run_tac nativeRow

private theorem s_to_h_2428 (k : Nat) : SToHRows (Safe:=Safe2 k) (ns2 k 2428) (ns2 k 2431) := by
  refine ⟨ns2 k 2429,ns2 k 2430,ns2_safe k 2428,ns2_safe k 2429,ns2_safe k 2430,?_,?_,?_,?_,?_⟩
  · run_tac nativeRow
  · intro b;cases b <;> (run_tac nativeRow)
  · run_tac nativeRow
  · intro b;cases b <;> (run_tac nativeRow)
  · run_tac nativeRow

private theorem h_to_d_2431 (k : Nat) : FromHRows (Safe:=Safe2 k) (ns2 k 2431) (ns2 k 3030) := by
  refine ⟨ns2 k 2432,ns2 k 2433,ns2_safe k 2431,ns2_safe k 2432,ns2_safe k 2433,?_,?_,?_,?_,?_,?_⟩
  · run_tac nativeRow
  · run_tac nativeRow
  · run_tac nativeRow
  · run_tac nativeRow
  · run_tac nativeRow
  · run_tac nativeRow

private theorem d_to_h_3122 (k : Nat) : DToHRows (Safe:=Safe2 k) (ns2 k 3122) (ns2 k 3126) := by
  refine ⟨ns2 k 3123,ns2 k 3124,ns2 k 3125,ns2_safe k 3122,ns2_safe k 3123,ns2_safe k 3124,ns2_safe k 3125,?_,?_,?_,?_,?_,?_⟩
  · run_tac nativeRow
  · run_tac nativeRow
  · run_tac nativeRow
  · run_tac nativeRow
  · run_tac nativeRow
  · run_tac nativeRow

private theorem h_to_s_3126 (k : Nat) : HToSRows (Safe:=Safe2 k) (ns2 k 3126) (ns2 k 3129) := by
  refine ⟨ns2 k 3127,ns2 k 3128,ns2_safe k 3126,ns2_safe k 3127,ns2_safe k 3128,?_,?_,?_,?_,?_⟩
  · run_tac nativeRow
  · intro b;cases b <;> (run_tac nativeRow)
  · run_tac nativeRow
  · intro b;cases b <;> (run_tac nativeRow)
  · run_tac nativeRow
end NormalFinalClosure
