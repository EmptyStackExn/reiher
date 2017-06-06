theory Reiher_Example
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

lemma my_abs_inv: "\<forall>c. mono (\<lambda>n. time (\<rho> n c)) \<Longrightarrow> Rep_run (Abs_run \<rho>) = \<rho>"
  by (simp add: Abs_run_inverse)
lemma my_abs_inv'[simp]: "Rep_run (Abs_run \<rho>) = \<rho>"
  (* TEMPORARY SOLUTION OF THE PROBLEM *)
  sorry


lemma "[], 0 \<Turnstile> [] \<triangleright> \<Phi>\<^sub>0"
apply (heron_next_step)
(*
apply (rule instant_i, auto, solve_run_witness)
  apply (rule sporadic_e2)

  apply (rule witness_consistency)
  apply (auto)


  apply (rule sporadic_e1, solve_run_witness)
  apply (rule implies_e2, solve_run_witness)
*)
apply (heron_next_step) print_run
(*
apply (rule instant_i, auto, solve_run_witness)
  apply (rule sporadic_e2, solve_run_witness)
  apply (rule implies_e2, solve_run_witness)
*)
by (heron_end)
(* by (rule simulation_end, simp, solve_run_witness') *)

(* Some draft proofs to handle [undefined] constant with monotonicity properties *)
lemma hamlet_is_fst: "hamlet (x, y) = x" by simp
lemma time_is_snd: "time (x, y) = y" by simp
lemma hamlet_ite: "hamlet (if P then (x1, x2) else (y1, y2)) = (if P then x1 else y1)" by simp
lemma time_ite: "time (if P then (x1, x2) else (y1, y2)) = (if P then x2 else y2)" by simp

lemma "hamlet
     (Rep_run
       (Abs_run
         (\<lambda>n' K'.
             if \<H>\<^sub>1 = K' \<and> Suc 0 = n'
             then (True,
                   time
                    (Rep_run
                      (Abs_run
                        (\<lambda>n' K'.
                            if \<H>\<^sub>1 = K' \<and> Suc 0 = n'
                            then (hamlet (Rep_run \<rho>\<^sub>\<odot> (Suc 0) \<H>\<^sub>1),
                                  \<tau>\<^sub>i\<^sub>n\<^sub>t 1)
                            else Rep_run \<rho>\<^sub>\<odot> n' K'))
                      (Suc 0) \<H>\<^sub>1))
             else Rep_run
                   (Abs_run
                     (\<lambda>n' K'.
                         if \<H>\<^sub>1 = K' \<and> Suc 0 = n'
                         then (hamlet (Rep_run \<rho>\<^sub>\<odot> (Suc 0) \<H>\<^sub>1), \<tau>\<^sub>i\<^sub>n\<^sub>t 1)
                         else Rep_run \<rho>\<^sub>\<odot> n' K'))
                   n' K'))
       (Suc 0) \<H>\<^sub>1)"
apply ((subst my_abs_inv)[])+ apply auto+
apply (simp add: mono_def)
apply ((subst my_abs_inv)[])+ apply auto+
apply (simp add: mono_def)
apply (subst hamlet_is_fst)+
apply (subst time_ite)
apply (simp add: mono_def) apply auto+

prefer 3
apply ((subst my_abs_inv)[])+ apply auto+
apply (simp add: mono_def)
apply (subst hamlet_is_fst)+
apply ((subst my_abs_inv)[])+ apply auto+
apply (simp add: mono_def)
apply (subst hamlet_is_fst)+ 

prefer 2
apply ((subst my_abs_inv)[])+ apply auto+
apply (simp add: mono_def)
apply (subst hamlet_is_fst time_is_snd)+
sorry

end