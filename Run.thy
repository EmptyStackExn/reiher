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

lemma symrun_refinement:
  "\<lbrakk>\<lbrakk> \<Gamma> \<rbrakk>\<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n \<supseteq> \<lbrakk>\<lbrakk> \<gamma> # \<Gamma> \<rbrakk>\<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n"
by simp

lemma symrun_refinement':
  assumes inc: "set \<Gamma> \<subseteq> set \<Gamma>'"
  shows "\<lbrakk>\<lbrakk> \<Gamma> \<rbrakk>\<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n \<supseteq> \<lbrakk>\<lbrakk> \<Gamma>' \<rbrakk>\<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n"
sorry

definition consistent_run :: "constr list \<Rightarrow> bool" where 
  "consistent_run \<Gamma> \<equiv> \<exists>\<rho>. \<rho> \<in> \<lbrakk>\<lbrakk> \<Gamma> \<rbrakk>\<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n"

text \<open> Defining a method for witness construction \<close>

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

end
