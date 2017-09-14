theory Run
imports
    "TESL"
      
begin

section \<open> Defining runs \<close>

abbreviation hamlet where "hamlet \<equiv> fst"
abbreviation time where "time \<equiv> snd"

(*
type_synonym instant = "clock \<Rightarrow> (bool \<times> tag_const)"
type_synonym run = "nat \<Rightarrow> instant"
*)
typedef (overloaded) run =
  "{ \<rho>::nat \<Rightarrow> clock \<Rightarrow> (bool \<times> tag_const). \<forall>c. mono (\<lambda>n. time (\<rho> n c)) }"
proof
  show "(\<lambda>_ _. (undefined, \<tau>\<^sub>l\<^sub>e\<^sub>a\<^sub>s\<^sub>t)) \<in> {\<rho>::nat \<Rightarrow> clock \<Rightarrow> bool \<times> tag_const. \<forall>c::clock. mono (\<lambda>n::nat. time (\<rho> n c))}"
  using mono_def by auto
qed
(*
abbreviation Abs_run_not ("_\<^sup>\<up>" 1000) where "f\<^sup>\<up> \<equiv> Abs_run f"
abbreviation Rep_run_not ("_\<^sup>\<down>" 1000) where "f\<^sup>\<down> \<equiv> Rep_run f"
*)
lemma Abs_run_inverse_rewrite:
  "\<forall>c. mono (\<lambda>n. time (\<rho> n c)) \<Longrightarrow> Rep_run (Abs_run \<rho>) = \<rho>"
  by (simp add: Abs_run_inverse)

(* WARNING: Admitting monotonicity to compute faster. Use for testing purposes only. *)
lemma Abs_run_inverse_rewrite_unsafe:
  "Rep_run (Abs_run \<rho>) = \<rho>"
  sorry


fun symbolic_run_interpretation_primitive :: "constr \<Rightarrow> run set" ("\<lbrakk> _ \<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n") where
    "\<lbrakk> K \<Up> n  \<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n = { \<rho>. hamlet ((Rep_run \<rho>) n K) = True }"
  | "\<lbrakk> K \<not>\<Up> n \<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n = { \<rho>. hamlet ((Rep_run \<rho>) n K) = False }"
  | "\<lbrakk> K \<Down> n @ \<lfloor> \<tau> \<rfloor> \<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n = { \<rho>. time ((Rep_run \<rho>) n K) = \<tau> }"
  | "\<lbrakk> K \<Down> n @ \<lfloor> \<tau>\<^sub>v\<^sub>a\<^sub>r(K', n') \<oplus> \<tau> \<rfloor> \<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n = { \<rho>. time ((Rep_run \<rho>) n K) = time ((Rep_run \<rho>) n' K') + \<tau> }"
  | "\<lbrakk> \<tau>\<^sub>v\<^sub>a\<^sub>r(K\<^sub>1, n\<^sub>1) \<doteq> \<alpha> * \<tau>\<^sub>v\<^sub>a\<^sub>r(K\<^sub>2, n\<^sub>2) + \<beta> \<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n = { \<rho>. time ((Rep_run \<rho>) n\<^sub>1 K\<^sub>1) = \<alpha> * time ((Rep_run \<rho>) n\<^sub>2 K\<^sub>2) + \<beta> }"

fun symbolic_run_interpretation :: "constr list \<Rightarrow> run set" ("\<lbrakk>\<lbrakk> _ \<rbrakk>\<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n") where
    "\<lbrakk>\<lbrakk> [] \<rbrakk>\<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n = { _. True }"
  | "\<lbrakk>\<lbrakk> \<gamma> # \<Gamma> \<rbrakk>\<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n = \<lbrakk> \<gamma> \<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n \<inter> \<lbrakk>\<lbrakk> \<Gamma> \<rbrakk>\<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n"

definition consistent_run :: "constr list \<Rightarrow> bool" where 
  "consistent_run \<Gamma> \<equiv> \<exists>\<rho>. \<rho> \<in> \<lbrakk>\<lbrakk> \<Gamma> \<rbrakk>\<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n"

(**) section \<open>Defining a method for witness construction\<close> (**)

(* Initial states *)
abbreviation initial_run :: "run" ("\<rho>\<^sub>\<odot>") where
  "\<rho>\<^sub>\<odot> \<equiv> Abs_run ((\<lambda>_ _. (undefined, \<tau>\<^sub>l\<^sub>e\<^sub>a\<^sub>s\<^sub>t)) ::nat \<Rightarrow> clock \<Rightarrow> (bool \<times> tag_const))"

(* To ensure monotonicity, time tag is set at a specific instant and forever after (stuttering) *)
fun time_update
  :: "nat \<Rightarrow> clock \<Rightarrow> tag_const \<Rightarrow> (nat \<Rightarrow> clock \<Rightarrow> (bool \<times> tag_const)) \<Rightarrow> (nat \<Rightarrow> clock \<Rightarrow> (bool \<times> tag_const))" where
    "time_update n K \<tau> \<rho> = (\<lambda>n' K'. if K = K' \<and> n \<le> n' then (hamlet (\<rho> n K), \<tau>) else \<rho> n' K')"

(* Update functionals *)
fun run_update :: "run \<Rightarrow> constr \<Rightarrow> run" ("_ \<langle> _ \<rangle>") where
    "\<rho> \<langle> K \<Up> n \<rangle>  = Abs_run (\<lambda>n' K'. if K = K' \<and> n = n' then (True, time ((Rep_run \<rho>) n K)) else (Rep_run \<rho>) n' K')"
  | "\<rho> \<langle> K \<not>\<Up> n \<rangle> = Abs_run (\<lambda>n' K'. if K = K' \<and> n = n' then (False, time ((Rep_run \<rho>) n K)) else (Rep_run \<rho>) n' K')"
  | "\<rho> \<langle> K \<Down> n @ \<lfloor> \<tau> \<rfloor> \<rangle> = Abs_run (time_update n K \<tau> (Rep_run \<rho>))"
  | "\<rho> \<langle> K \<Down> n @ \<lfloor> \<tau>\<^sub>v\<^sub>a\<^sub>r(K', n') \<oplus> \<tau> \<rfloor> \<rangle> =
     Abs_run (time_update n K (time ((Rep_run \<rho>) n' K') + \<tau>) (Rep_run \<rho>))"
  | "\<rho> \<langle> \<tau>\<^sub>v\<^sub>a\<^sub>r(K\<^sub>1, n\<^sub>1) \<doteq> \<alpha> * \<tau>\<^sub>v\<^sub>a\<^sub>r(K\<^sub>2, n\<^sub>2) + \<beta> \<rangle> =
     Abs_run (if time ((Rep_run \<rho>) n\<^sub>1 K\<^sub>1) = \<tau>\<^sub>l\<^sub>e\<^sub>a\<^sub>s\<^sub>t \<and> time ((Rep_run \<rho>) n\<^sub>2 K\<^sub>2) \<noteq> \<tau>\<^sub>l\<^sub>e\<^sub>a\<^sub>s\<^sub>t
      then (time_update n\<^sub>1 K\<^sub>1 (\<alpha> * time ((Rep_run \<rho>) n\<^sub>2 K\<^sub>2) + \<beta>) (Rep_run \<rho>))
      else if time ((Rep_run \<rho>) n\<^sub>2 K\<^sub>2) = \<tau>\<^sub>l\<^sub>e\<^sub>a\<^sub>s\<^sub>t \<and> time ((Rep_run \<rho>) n\<^sub>1 K\<^sub>1) \<noteq> \<tau>\<^sub>l\<^sub>e\<^sub>a\<^sub>s\<^sub>t
           then time_update n\<^sub>2 K\<^sub>2 (time ((Rep_run \<rho>) n\<^sub>2 K\<^sub>2) (* (time (\<rho> n\<^sub>1 K\<^sub>1) - \<beta>) / \<alpha> *)) (Rep_run \<rho>) (* MAYBE NOT A GOOD CHOICE *)
           else (Rep_run \<rho>) 
     )"

fun run_update' :: "constr list \<Rightarrow> run" ("\<langle>\<langle> _ \<rangle>\<rangle>") where
    "\<langle>\<langle> [] \<rangle>\<rangle>    = \<rho>\<^sub>\<odot>"
  | "\<langle>\<langle> \<gamma> # \<Gamma> \<rangle>\<rangle> = \<langle>\<langle> \<Gamma> \<rangle>\<rangle> \<langle> \<gamma> \<rangle>"

lemma witness_consistency:
  "\<langle>\<langle> \<Gamma> \<rangle>\<rangle> \<in> \<lbrakk>\<lbrakk> \<Gamma> \<rbrakk>\<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n \<Longrightarrow> consistent_run \<Gamma>"
  unfolding consistent_run_def by (rule exI, auto)

lemma witness_consistency':
  "consistent_run \<Gamma> \<Longrightarrow> \<langle>\<langle> \<Gamma> \<rangle>\<rangle> \<in> \<lbrakk>\<lbrakk> \<Gamma> \<rbrakk>\<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n"
  oops (* Not sure the idea is true *)

(**) section \<open>Rules and properties of consistence\<close> (**)

lemma context_consistency_preservationI:
  "consistent_run (\<gamma> # \<Gamma>) \<Longrightarrow> consistent_run \<Gamma>"
using consistent_run_def by auto

(* This is very restrictive *)
inductive context_independency :: "constr \<Rightarrow> constr list \<Rightarrow> bool" ("_ \<bowtie> _") where
  NotTicks_independency:
  "K \<Up> n \<notin> set \<Gamma> \<Longrightarrow> K \<not>\<Up> n \<bowtie> \<Gamma>"
| Ticks_independency:
  "K \<not>\<Up> n \<notin> set \<Gamma> \<Longrightarrow> K \<Up> n \<bowtie> \<Gamma>"
| Timestamp_independency:
  "(\<nexists>\<tau>'. \<tau>' = \<tau> \<and> K \<Down> n @ \<tau> \<in> set \<Gamma>) \<Longrightarrow> K \<Down> n @ \<tau> \<bowtie> \<Gamma>"

thm context_independency.induct

lemma context_consistency_preservationE:
  assumes consist: "consistent_run \<Gamma>"
  and     indepen: "\<gamma> \<bowtie> \<Gamma>"
  shows "consistent_run (\<gamma> # \<Gamma>)"
apply (insert consist indepen)
apply (erule context_independency.cases)
apply auto
proof -
  show "\<And>K n. consistent_run \<Gamma> \<Longrightarrow>
           \<gamma> = K \<not>\<Up> n \<Longrightarrow> K \<Up> n \<notin> set \<Gamma> \<Longrightarrow>
           consistent_run (K \<not>\<Up> n # \<Gamma>)"
    sorry
  show "\<And>K n. consistent_run \<Gamma> \<Longrightarrow>
           \<gamma> = K \<Up> n \<Longrightarrow> K \<not>\<Up> n \<notin> set \<Gamma> \<Longrightarrow>
           consistent_run (K \<Up> n # \<Gamma>)"
    sorry
  show "\<And>\<tau> K n.
       consistent_run \<Gamma> \<Longrightarrow>
       \<gamma> = K \<Down> n @ \<tau> \<Longrightarrow>
       K \<Down> n @ \<tau> \<notin> set \<Gamma> \<Longrightarrow> consistent_run (K \<Down> n @ \<tau> # \<Gamma>)"
    sorry
qed

(**) section \<open>Expansion law\<close> (**)
text \<open>Similar to the expansion laws of lattices\<close>

theorem symrun_interp_expansion:
  shows "\<lbrakk>\<lbrakk> \<Gamma>\<^sub>1 @ \<Gamma>\<^sub>2 \<rbrakk>\<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n = \<lbrakk>\<lbrakk> \<Gamma>\<^sub>1 \<rbrakk>\<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n \<inter> \<lbrakk>\<lbrakk> \<Gamma>\<^sub>2 \<rbrakk>\<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n"
sorry

(**) section \<open>A few equational laws\<close> (**)

lemma symrun_interp_assoc:
  shows "\<lbrakk>\<lbrakk> (\<Gamma>\<^sub>1 @ \<Gamma>\<^sub>2) @ \<Gamma>\<^sub>3 \<rbrakk>\<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n = \<lbrakk>\<lbrakk> \<Gamma>\<^sub>1 @ (\<Gamma>\<^sub>2 @ \<Gamma>\<^sub>3) \<rbrakk>\<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n"
  by auto

lemma symrun_interp_commute:
  shows "\<lbrakk>\<lbrakk> \<Gamma>\<^sub>1 @ \<Gamma>\<^sub>2 \<rbrakk>\<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n = \<lbrakk>\<lbrakk> \<Gamma>\<^sub>2 @ \<Gamma>\<^sub>1 \<rbrakk>\<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n"
  by (simp add: symrun_interp_expansion inf_sup_aci(1))

lemma symrun_interp_left_commute:
  shows "\<lbrakk>\<lbrakk> \<Gamma>\<^sub>1 @ (\<Gamma>\<^sub>2 @ \<Gamma>\<^sub>3) \<rbrakk>\<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n = \<lbrakk>\<lbrakk> \<Gamma>\<^sub>2 @ (\<Gamma>\<^sub>1 @ \<Gamma>\<^sub>3) \<rbrakk>\<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n"
  using symrun_interp_expansion by auto

lemma symrun_interp_idem:
  shows "\<lbrakk>\<lbrakk> \<Gamma> @ \<Gamma> \<rbrakk>\<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n = \<lbrakk>\<lbrakk> \<Gamma> \<rbrakk>\<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n"
  using symrun_interp_expansion by auto

lemma symrun_interp_left_idem:
  shows "\<lbrakk>\<lbrakk> \<Gamma>\<^sub>1 @ (\<Gamma>\<^sub>1 @ \<Gamma>\<^sub>2) \<rbrakk>\<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n = \<lbrakk>\<lbrakk> \<Gamma>\<^sub>1 @ \<Gamma>\<^sub>2 \<rbrakk>\<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n"
  using symrun_interp_expansion by auto

lemma symrun_interp_right_idem:
  shows "\<lbrakk>\<lbrakk> (\<Gamma>\<^sub>1 @ \<Gamma>\<^sub>2) @ \<Gamma>\<^sub>2 \<rbrakk>\<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n = \<lbrakk>\<lbrakk> \<Gamma>\<^sub>1 @ \<Gamma>\<^sub>2 \<rbrakk>\<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n"
  using symrun_interp_expansion by auto

lemmas symrun_interp_aci = symrun_interp_commute symrun_interp_assoc symrun_interp_left_commute symrun_interp_left_idem

lemma tesl_intersect_id_left [simp]: "\<lbrakk>\<lbrakk> [] @ \<Gamma> \<rbrakk>\<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n = \<lbrakk>\<lbrakk> \<Gamma> \<rbrakk>\<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n"
by simp

lemma tesl_intersect_id_right [simp]: "\<lbrakk>\<lbrakk> \<Gamma> @ [] \<rbrakk>\<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n = \<lbrakk>\<lbrakk> \<Gamma> \<rbrakk>\<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n"
by simp

find_theorems "_ \<inter> _ = _"
section \<open>Decreasing interpretation of TESL formulae\<close>

lemma symrun_sem_decreases_head:
  "\<lbrakk>\<lbrakk> \<Gamma> \<rbrakk>\<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n \<supseteq> \<lbrakk>\<lbrakk> \<phi> # \<Gamma> \<rbrakk>\<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n"
by simp

lemma symrun_sem_decreases_tail:
  "\<lbrakk>\<lbrakk> \<Gamma> \<rbrakk>\<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n \<supseteq> \<lbrakk>\<lbrakk> \<Gamma> @ [\<phi>] \<rbrakk>\<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n"
  by (simp add: symrun_interp_expansion)

theorem symrun_interp_decreases_setinc:
  assumes incl: "set \<Gamma> \<subseteq> set \<Gamma>'"
  shows "\<lbrakk>\<lbrakk> \<Gamma> \<rbrakk>\<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n \<supseteq> \<lbrakk>\<lbrakk> \<Gamma>' \<rbrakk>\<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n"
sorry

lemma symrun_interp_decreases_add_head:
  assumes incl: "set \<Gamma> \<subseteq> set \<Gamma>'"
  shows "\<lbrakk>\<lbrakk> \<phi> # \<Gamma> \<rbrakk>\<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n \<supseteq> \<lbrakk>\<lbrakk> \<phi> # \<Gamma>' \<rbrakk>\<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n"
  using symrun_interp_decreases_setinc incl by auto

lemma symrun_interp_decreases_add_tail:
  assumes incl: "set \<Gamma> \<subseteq> set \<Gamma>'"
  shows "\<lbrakk>\<lbrakk> \<Gamma> @ [\<phi>] \<rbrakk>\<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n \<supseteq> \<lbrakk>\<lbrakk> \<Gamma>' @ [\<phi>] \<rbrakk>\<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n"
  by (metis symrun_interp_commute symrun_interp_decreases_add_head append_Cons append_Nil incl)

lemma symrun_interp_absorb1:
  assumes incl: "set \<Gamma>\<^sub>1 \<subseteq> set \<Gamma>\<^sub>2"
  shows "\<lbrakk>\<lbrakk> \<Gamma>\<^sub>1 @ \<Gamma>\<^sub>2 \<rbrakk>\<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n = \<lbrakk>\<lbrakk> \<Gamma>\<^sub>2 \<rbrakk>\<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n"
  by (simp add: Int_absorb1 symrun_interp_decreases_setinc symrun_interp_expansion incl)

lemma symrun_interp_absorb2:
  assumes incl: "set \<Gamma>\<^sub>2 \<subseteq> set \<Gamma>\<^sub>1"
  shows "\<lbrakk>\<lbrakk> \<Gamma>\<^sub>1 @ \<Gamma>\<^sub>2 \<rbrakk>\<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n = \<lbrakk>\<lbrakk> \<Gamma>\<^sub>1 \<rbrakk>\<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n"
  using symrun_interp_absorb1 symrun_interp_commute incl by blast


end
