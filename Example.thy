theory Example
imports
  "Reiher"

begin
(* Running on a small example:
  H1 sporadic 1, 2
  H1 implies H2
*)
abbreviation \<H>\<^sub>1 where "\<H>\<^sub>1 \<equiv> \<lceil>''H1''\<rceil>"
abbreviation \<H>\<^sub>2 where "\<H>\<^sub>2 \<equiv> \<lceil>''H2''\<rceil>"
abbreviation \<Phi>\<^sub>0 where "\<Phi>\<^sub>0 \<equiv> [
    \<H>\<^sub>1 sporadic \<tau>\<^sub>i\<^sub>n\<^sub>t 1,
    \<H>\<^sub>1 sporadic \<tau>\<^sub>i\<^sub>n\<^sub>t 2,
    \<H>\<^sub>1 implies \<H>\<^sub>2
]"

lemma "[], 0 \<Turnstile> [] \<triangleright> \<Phi>\<^sub>0"
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