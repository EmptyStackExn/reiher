theory Reiher
imports
  "Engine"
  "$ISABELLE_HOME/src/HOL/Eisbach/Eisbach_Tools" 

begin

method solve_run_witness =
  rule witness_consistency,
  auto,
  (match conclusion in "False" \<Rightarrow> \<open>fail\<close> \<bar> _ \<Rightarrow> \<open>succeed\<close>)

method solve_run_witness_end =
  rule witness_consistency,
  auto

named_theorems init
declare instant_i [init]

named_theorems elims
declare sporadic_e2 [elims]
declare sporadic_e1 [elims]
declare implies_e2 [elims]
declare implies_e1 [elims]

method heron_next_step =
  rule init, auto, solve_run_witness, (rule elims, solve_run_witness)+

method heron_end =
  rule simulation_end, simp, solve_run_witness_end

end