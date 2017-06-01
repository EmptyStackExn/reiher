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
  ML_val\<open>print_run @{Isar.goal}\<close>
apply (heron_next_step)
  ML_val\<open>print_run @{Isar.goal}\<close>
apply (heron_next_step)
  ML_val\<open>print_run @{Isar.goal}\<close>
by (heron_end)

end