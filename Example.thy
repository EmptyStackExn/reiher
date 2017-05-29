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
    \<odot>(\<lceil>''H1''\<rceil>, \<tau>\<^sub>i\<^sub>n\<^sub>t 1),
    \<odot>(\<lceil>''H1''\<rceil>, \<tau>\<^sub>i\<^sub>n\<^sub>t 2),
    \<lceil>''H1''\<rceil> \<rightarrow>\<^sub>i\<^sub>m\<^sub>p\<^sub>l\<^sub>i\<^sub>e\<^sub>s \<lceil>''H2''\<rceil>
  ]"
apply (heron_step_continue)
(*
apply (rule instant_i, auto, solve_run_witness)
  apply (rule sporadic_e2, solve_run_witness)
  apply (rule sporadic_e1, solve_run_witness)
  apply (rule implies_e2, solve_run_witness)
*)
apply (heron_step_continue) print_facts
(*
apply (rule instant_i, auto, solve_run_witness)
  apply (rule sporadic_e2, solve_run_witness)
  apply (rule implies_e2, solve_run_witness)
*)
by (heron_step_end)
(* by (rule simulation_end, simp, solve_run_witness') *)

end