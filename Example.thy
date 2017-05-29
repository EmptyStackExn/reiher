theory Example
imports
    Main
    "Engine"

begin
(* Running on a small example:
  H1 sporadic 1, 2
  H1 implies H2
*)
lemma small_example:
  shows "[], 0 \<Turnstile> [] \<triangleright> [
    \<lceil>''H1''\<rceil> sporadic \<tau>\<^sub>i\<^sub>n\<^sub>t 1,
    \<lceil>''H1''\<rceil> sporadic \<tau>\<^sub>i\<^sub>n\<^sub>t 2,
    \<lceil>''H1''\<rceil> implies \<lceil>''H2''\<rceil>
  ]"
apply (heron_next_step)
(*
apply (rule instant_i, auto, solve_run_witness)
  apply (rule sporadic_e2, solve_run_witness)
  apply (rule sporadic_e1, solve_run_witness)
  apply (rule implies_e2, solve_run_witness)
*)
apply (heron_next_step) print_facts
(*
apply (rule instant_i, auto, solve_run_witness)
  apply (rule sporadic_e2, solve_run_witness)
  apply (rule implies_e2, solve_run_witness)
*)
by (heron_end)
(* by (rule simulation_end, simp, solve_run_witness') *)


end