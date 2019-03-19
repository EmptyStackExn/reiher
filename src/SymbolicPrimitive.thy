theory SymbolicPrimitive
  imports Run

begin

datatype cnt_expr =
    TickCountLess \<open>clock\<close> \<open>instant_index\<close>  ("#\<^sup><")
  | TickCountLeq \<open>clock\<close> \<open>instant_index\<close> ("#\<^sup>\<le>")

subsection\<open> Symbolic Primitives for Runs \<close>
datatype '\<tau> constr =
    Timestamp     \<open>clock\<close>   \<open>instant_index\<close> \<open>'\<tau> tag_const\<close>         ("_ \<Down> _ @ _")
  | TimeDelay     \<open>clock\<close>   \<open>instant_index\<close> \<open>'\<tau> tag_const\<close> \<open>clock\<close> ("_ @ _ \<oplus> _ \<Rightarrow> _")
  | Ticks         \<open>clock\<close>   \<open>instant_index\<close>                        ("_ \<Up> _")
  | NotTicks      \<open>clock\<close>   \<open>instant_index\<close>                        ("_ \<not>\<Up> _")
  | NotTicksUntil \<open>clock\<close>   \<open>instant_index\<close>                        ("_ \<not>\<Up> < _")
  | NotTicksFrom  \<open>clock\<close>   \<open>instant_index\<close>                        ("_ \<not>\<Up> \<ge> _")
  | TagArith      \<open>tag_var\<close> \<open>tag_var\<close> \<open>('\<tau> tag_const \<times> '\<tau> tag_const) \<Rightarrow> bool\<close> ("\<lfloor>_, _\<rfloor> \<in> _")
  | TickCntArith  \<open>cnt_expr\<close> \<open>cnt_expr\<close> \<open>(nat \<times> nat) \<Rightarrow> bool\<close>               ("\<lceil>_, _\<rceil> \<in> _")
  | TickCntLeq    \<open>cnt_expr\<close> \<open>cnt_expr\<close>                           ("_ \<preceq> _")

type_synonym '\<tau> system = \<open>'\<tau> constr list\<close>

(* The abstract machine
   Follows the intuition: past [\<Gamma>], current index [n], present [\<Psi>], future [\<Phi>]
   Beware: This type is slightly different from which originally implemented in Heron
*)
type_synonym '\<tau> config = \<open>'\<tau> system * instant_index * '\<tau> TESL_formula * '\<tau> TESL_formula\<close>


section \<open>Semantics of Primitive Constraints \<close>

fun counter_expr_eval :: \<open>('\<tau>::linordered_field) run \<Rightarrow> cnt_expr \<Rightarrow> nat\<close> ("\<lbrakk> _ \<turnstile> _ \<rbrakk>\<^sub>c\<^sub>n\<^sub>t\<^sub>e\<^sub>x\<^sub>p\<^sub>r")
where
    \<open>\<lbrakk> \<rho> \<turnstile> #\<^sup>< clk indx \<rbrakk>\<^sub>c\<^sub>n\<^sub>t\<^sub>e\<^sub>x\<^sub>p\<^sub>r = run_tick_count_strictly \<rho> clk indx\<close>
  | \<open>\<lbrakk> \<rho> \<turnstile> #\<^sup>\<le> clk indx \<rbrakk>\<^sub>c\<^sub>n\<^sub>t\<^sub>e\<^sub>x\<^sub>p\<^sub>r = run_tick_count \<rho> clk indx\<close>


fun symbolic_run_interpretation_primitive :: \<open>('\<tau>::linordered_field) constr \<Rightarrow> '\<tau> run set\<close> ("\<lbrakk> _ \<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m")
where
    \<open>\<lbrakk> K \<Up> n  \<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m     = { \<rho>. hamlet ((Rep_run \<rho>) n K) }\<close>
  | \<open>\<lbrakk> K @ n\<^sub>0 \<oplus> \<delta>t \<Rightarrow> K' \<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m = { \<rho>. \<forall>n \<ge> n\<^sub>0. first_time \<rho> K n (time ((Rep_run \<rho>) n\<^sub>0 K) + \<delta>t) \<longrightarrow> hamlet ((Rep_run \<rho>) n K')}\<close>
  | \<open>\<lbrakk> K \<not>\<Up> n \<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m     = { \<rho>. \<not>hamlet ((Rep_run \<rho>) n K) }\<close>
  | \<open>\<lbrakk> K \<not>\<Up> < n \<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m   = { \<rho>. \<forall>i < n. \<not> hamlet ((Rep_run \<rho>) i K)}\<close>
  | \<open>\<lbrakk> K \<not>\<Up> \<ge> n \<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m   = { \<rho>. \<forall>i \<ge> n. \<not> hamlet ((Rep_run \<rho>) i K) }\<close>
  | \<open>\<lbrakk> K \<Down> n @ \<tau> \<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m = { \<rho>. time ((Rep_run \<rho>) n K) = \<tau> }\<close>
  | \<open>\<lbrakk> \<lfloor>\<tau>\<^sub>v\<^sub>a\<^sub>r(K\<^sub>1, n\<^sub>1), \<tau>\<^sub>v\<^sub>a\<^sub>r(K\<^sub>2, n\<^sub>2)\<rfloor> \<in> R \<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m = { \<rho>. R (time ((Rep_run \<rho>) n\<^sub>1 K\<^sub>1), time ((Rep_run \<rho>) n\<^sub>2 K\<^sub>2)) }\<close>
  | \<open>\<lbrakk> \<lceil>e\<^sub>1, e\<^sub>2\<rceil> \<in> R \<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m = { \<rho>. R (\<lbrakk> \<rho> \<turnstile> e\<^sub>1 \<rbrakk>\<^sub>c\<^sub>n\<^sub>t\<^sub>e\<^sub>x\<^sub>p\<^sub>r, \<lbrakk> \<rho> \<turnstile> e\<^sub>2 \<rbrakk>\<^sub>c\<^sub>n\<^sub>t\<^sub>e\<^sub>x\<^sub>p\<^sub>r) }\<close>
  | \<open>\<lbrakk> cnt_e\<^sub>1 \<preceq> cnt_e\<^sub>2 \<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m = { \<rho>. \<lbrakk> \<rho> \<turnstile> cnt_e\<^sub>1 \<rbrakk>\<^sub>c\<^sub>n\<^sub>t\<^sub>e\<^sub>x\<^sub>p\<^sub>r \<le> \<lbrakk> \<rho> \<turnstile> cnt_e\<^sub>2 \<rbrakk>\<^sub>c\<^sub>n\<^sub>t\<^sub>e\<^sub>x\<^sub>p\<^sub>r }\<close>

fun symbolic_run_interpretation :: \<open>('\<tau>::linordered_field) constr list \<Rightarrow> ('\<tau>::linordered_field) run set\<close> ("\<lbrakk>\<lbrakk> _ \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m") where
    \<open>\<lbrakk>\<lbrakk> [] \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m = { _. True }\<close>
  | \<open>\<lbrakk>\<lbrakk> \<gamma> # \<Gamma> \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m = \<lbrakk> \<gamma> \<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m \<inter> \<lbrakk>\<lbrakk> \<Gamma> \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m\<close>

lemma symbolic_run_interp_cons_morph:
  \<open>\<lbrakk> \<gamma> \<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m \<inter> \<lbrakk>\<lbrakk> \<Gamma> \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m = \<lbrakk>\<lbrakk> \<gamma> # \<Gamma> \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m\<close>
  by auto

definition consistent_context :: \<open>('\<tau>::linordered_field) constr list \<Rightarrow> bool\<close> where 
  \<open>consistent_context \<Gamma> \<equiv> \<exists>\<rho>. \<rho> \<in> \<lbrakk>\<lbrakk> \<Gamma> \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m\<close>

subsection \<open>Defining a method for witness construction\<close> (**)

(* Initial states *)
abbreviation initial_run :: \<open>('\<tau>::linordered_field) run\<close> ("\<rho>\<^sub>\<odot>") where
  \<open>\<rho>\<^sub>\<odot> \<equiv> Abs_run ((\<lambda>_ _. (False, \<tau>\<^sub>c\<^sub>s\<^sub>t 0)) ::nat \<Rightarrow> clock \<Rightarrow> (bool \<times> '\<tau> tag_const))\<close>

(* To ensure monotonicity, time tag is set at a specific instant and forever after (stuttering) *)
fun time_update
  :: \<open>nat \<Rightarrow> clock \<Rightarrow> ('\<tau>::linordered_field) tag_const \<Rightarrow> (nat \<Rightarrow> clock \<Rightarrow> (bool \<times> '\<tau> tag_const)) \<Rightarrow> (nat \<Rightarrow> clock \<Rightarrow> (bool \<times> '\<tau> tag_const))\<close> where
    \<open>time_update n K \<tau> \<rho> = (\<lambda>n' K'. if K = K' \<and> n \<le> n' then (hamlet (\<rho> n K), \<tau>) else \<rho> n' K')\<close>


section \<open>Rules and properties of consistence\<close> (**)

(* declare [[show_sorts]] *)

lemma context_consistency_preservationI:
  \<open>consistent_context ((\<gamma> :: ('\<tau>::linordered_field) constr) # \<Gamma>) \<Longrightarrow> consistent_context \<Gamma>\<close>
unfolding consistent_context_def
by auto

(* This is very restrictive *)
inductive context_independency :: \<open>('\<tau>::linordered_field) constr \<Rightarrow> '\<tau> constr list \<Rightarrow> bool\<close> ("_ \<bowtie> _") where
  NotTicks_independency:
  \<open>(K \<Up> n) \<notin> set \<Gamma> \<Longrightarrow> (K \<not>\<Up> n) \<bowtie> \<Gamma>\<close>
| Ticks_independency:
  \<open>(K \<not>\<Up> n) \<notin> set \<Gamma> \<Longrightarrow> (K \<Up> n) \<bowtie> \<Gamma>\<close>
| Timestamp_independency:
  \<open>(\<nexists>\<tau>'. \<tau>' = \<tau> \<and> (K \<Down> n @ \<tau>) \<in> set \<Gamma>) \<Longrightarrow> (K \<Down> n @ \<tau>) \<bowtie> \<Gamma>\<close>


lemma context_consistency_preservationE:
  assumes consist: \<open>consistent_context \<Gamma>\<close>
  and     indepen: \<open>\<gamma> \<bowtie> \<Gamma>\<close>
  shows   \<open>consistent_context (\<gamma> # \<Gamma>)\<close>
  oops


section\<open>Major Theorems\<close>
subsection \<open>Fixpoint lemma\<close> (**)

theorem symrun_interp_fixpoint:
  \<open>\<Inter> ((\<lambda>\<gamma>. \<lbrakk> \<gamma> \<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m) ` set \<Gamma>) = \<lbrakk>\<lbrakk> \<Gamma> \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m\<close>
  proof (induct \<Gamma>)
    case Nil
    then show ?case by simp
  next
    case (Cons a \<Gamma>)
    then show ?case by auto
  qed

subsection \<open>Expansion law\<close> (**)
text \<open>Similar to the expansion laws of lattices\<close>

theorem symrun_interp_expansion:
  shows \<open>\<lbrakk>\<lbrakk> \<Gamma>\<^sub>1 @ \<Gamma>\<^sub>2 \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m = \<lbrakk>\<lbrakk> \<Gamma>\<^sub>1 \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m \<inter> \<lbrakk>\<lbrakk> \<Gamma>\<^sub>2 \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m\<close>
by (induction \<Gamma>\<^sub>1, auto)

section \<open>Equational laws for TESL formulae denotationally interpreted\<close> 
subsection \<open>General laws\<close>

lemma symrun_interp_assoc:
  shows \<open>\<lbrakk>\<lbrakk> (\<Gamma>\<^sub>1 @ \<Gamma>\<^sub>2) @ \<Gamma>\<^sub>3 \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m = \<lbrakk>\<lbrakk> \<Gamma>\<^sub>1 @ (\<Gamma>\<^sub>2 @ \<Gamma>\<^sub>3) \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m\<close>
  by auto

lemma symrun_interp_commute:
  shows \<open>\<lbrakk>\<lbrakk> \<Gamma>\<^sub>1 @ \<Gamma>\<^sub>2 \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m = \<lbrakk>\<lbrakk> \<Gamma>\<^sub>2 @ \<Gamma>\<^sub>1 \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m\<close>
  by (simp add: symrun_interp_expansion inf_sup_aci(1))

lemma symrun_interp_left_commute:
  shows \<open>\<lbrakk>\<lbrakk> \<Gamma>\<^sub>1 @ (\<Gamma>\<^sub>2 @ \<Gamma>\<^sub>3) \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m = \<lbrakk>\<lbrakk> \<Gamma>\<^sub>2 @ (\<Gamma>\<^sub>1 @ \<Gamma>\<^sub>3) \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m\<close>
  unfolding symrun_interp_expansion by auto

lemma symrun_interp_idem:
  shows \<open>\<lbrakk>\<lbrakk> \<Gamma> @ \<Gamma> \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m = \<lbrakk>\<lbrakk> \<Gamma> \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m\<close>
  using symrun_interp_expansion by auto

lemma symrun_interp_left_idem:
  shows \<open>\<lbrakk>\<lbrakk> \<Gamma>\<^sub>1 @ (\<Gamma>\<^sub>1 @ \<Gamma>\<^sub>2) \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m = \<lbrakk>\<lbrakk> \<Gamma>\<^sub>1 @ \<Gamma>\<^sub>2 \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m\<close>
  using symrun_interp_expansion by auto

lemma symrun_interp_right_idem:
  shows \<open>\<lbrakk>\<lbrakk> (\<Gamma>\<^sub>1 @ \<Gamma>\<^sub>2) @ \<Gamma>\<^sub>2 \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m = \<lbrakk>\<lbrakk> \<Gamma>\<^sub>1 @ \<Gamma>\<^sub>2 \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m\<close>
  unfolding symrun_interp_expansion by auto

lemmas symrun_interp_aci = symrun_interp_commute symrun_interp_assoc symrun_interp_left_commute symrun_interp_left_idem

(* Identity element *)
lemma symrun_interp_neutral1:
  shows \<open>\<lbrakk>\<lbrakk> [] @ \<Gamma> \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m = \<lbrakk>\<lbrakk> \<Gamma> \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m\<close>
  by simp

lemma symrun_interp_neutral2:
  shows \<open>\<lbrakk>\<lbrakk> \<Gamma> @ [] \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m = \<lbrakk>\<lbrakk> \<Gamma> \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m\<close>
  by simp

subsection \<open>Decreasing interpretation of TESL formulae\<close>

lemma TESL_sem_decreases_head:
  \<open>\<lbrakk>\<lbrakk> \<Gamma> \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m \<supseteq> \<lbrakk>\<lbrakk> \<gamma> # \<Gamma> \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m\<close>
  by simp

lemma TESL_sem_decreases_tail:
  \<open>\<lbrakk>\<lbrakk> \<Gamma> \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m \<supseteq> \<lbrakk>\<lbrakk> \<Gamma> @ [\<gamma>] \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m\<close>
  by (simp add: symrun_interp_expansion)

lemma symrun_interp_formula_stuttering:
  assumes bel: \<open>\<gamma> \<in> set \<Gamma>\<close>
  shows \<open>\<lbrakk>\<lbrakk> \<gamma> # \<Gamma> \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m = \<lbrakk>\<lbrakk> \<Gamma> \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m\<close>
  by (metis Int_absorb1 Int_left_commute bel inf_le1 split_list symbolic_run_interpretation.simps(2) symrun_interp_expansion)

lemma symrun_interp_decreases:
  shows \<open>\<lbrakk>\<lbrakk> \<Gamma> \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m \<supseteq> \<lbrakk>\<lbrakk> \<gamma> # \<Gamma> \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m\<close>
  by (rule TESL_sem_decreases_head)

lemma symrun_interp_remdups_absorb:
  shows \<open>\<lbrakk>\<lbrakk> \<Gamma> \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m = \<lbrakk>\<lbrakk> remdups \<Gamma> \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m\<close>
  proof (induct \<Gamma>)
    case Nil
    then show ?case by simp
  next
    case (Cons a \<Gamma>)
    then show ?case
      using symrun_interp_formula_stuttering by auto
  qed

lemma symrun_interp_set_lifting:
  assumes \<open>set \<Gamma> = set \<Gamma>'\<close>
  shows \<open>\<lbrakk>\<lbrakk> \<Gamma> \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m = \<lbrakk>\<lbrakk> \<Gamma>' \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m\<close>
  proof -     
    have \<open>set (remdups \<Gamma>) = set (remdups \<Gamma>')\<close>
      by (simp add: assms)
    moreover have fxpnt\<Gamma>: \<open>\<Inter> ((\<lambda>\<gamma>. \<lbrakk> \<gamma> \<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m) ` set \<Gamma>) = \<lbrakk>\<lbrakk> \<Gamma> \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m\<close>
      by (simp add: symrun_interp_fixpoint)
    moreover have fxpnt\<Gamma>': \<open>\<Inter> ((\<lambda>\<gamma>. \<lbrakk> \<gamma> \<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m) ` set \<Gamma>') = \<lbrakk>\<lbrakk> \<Gamma>' \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m\<close>
      by (simp add: symrun_interp_fixpoint)
    moreover have \<open>\<Inter> ((\<lambda>\<gamma>. \<lbrakk> \<gamma> \<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m) ` set \<Gamma>) = \<Inter> ((\<lambda>\<gamma>. \<lbrakk> \<gamma> \<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m) ` set \<Gamma>')\<close>
      by (simp add: assms)
    ultimately show ?thesis using symrun_interp_remdups_absorb by auto
  qed

theorem symrun_interp_decreases_setinc:
  assumes incl: \<open>set \<Gamma> \<subseteq> set \<Gamma>'\<close>
  shows \<open>\<lbrakk>\<lbrakk> \<Gamma> \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m \<supseteq> \<lbrakk>\<lbrakk> \<Gamma>' \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m\<close>
  proof -
    obtain \<Gamma>\<^sub>r where decompose: \<open>set (\<Gamma> @ \<Gamma>\<^sub>r) = set \<Gamma>'\<close> using incl by auto
    have \<open>set (\<Gamma> @ \<Gamma>\<^sub>r) = set \<Gamma>'\<close> using incl decompose by blast
    moreover have \<open>(set \<Gamma>) \<union> (set \<Gamma>\<^sub>r) = set \<Gamma>'\<close> using incl decompose by auto
    moreover have \<open>\<lbrakk>\<lbrakk> \<Gamma>' \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m = \<lbrakk>\<lbrakk> \<Gamma> @ \<Gamma>\<^sub>r \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m\<close> using symrun_interp_set_lifting decompose by blast
    moreover have \<open>\<lbrakk>\<lbrakk> \<Gamma> @ \<Gamma>\<^sub>r \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m = \<lbrakk>\<lbrakk> \<Gamma> \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m \<inter> \<lbrakk>\<lbrakk> \<Gamma>\<^sub>r \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m\<close> by (simp add: symrun_interp_expansion)
    moreover have \<open>\<lbrakk>\<lbrakk> \<Gamma> \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m \<supseteq> \<lbrakk>\<lbrakk> \<Gamma> \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m \<inter> \<lbrakk>\<lbrakk> \<Gamma>\<^sub>r \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m\<close> by simp
    ultimately show ?thesis by simp
  qed

lemma symrun_interp_decreases_add_head:
  assumes incl: \<open>set \<Gamma> \<subseteq> set \<Gamma>'\<close>
  shows \<open>\<lbrakk>\<lbrakk> \<gamma> # \<Gamma> \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m \<supseteq> \<lbrakk>\<lbrakk> \<gamma> # \<Gamma>' \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m\<close>
  using symrun_interp_decreases_setinc incl by auto

lemma symrun_interp_decreases_add_tail:
  assumes incl: \<open>set \<Gamma> \<subseteq> set \<Gamma>'\<close>
  shows \<open>\<lbrakk>\<lbrakk> \<Gamma> @ [\<gamma>] \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m \<supseteq> \<lbrakk>\<lbrakk> \<Gamma>' @ [\<gamma>] \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m\<close>
  by (metis symrun_interp_commute symrun_interp_decreases_add_head append_Cons append_Nil incl)

lemma symrun_interp_absorb1:
  assumes incl: \<open>set \<Gamma>\<^sub>1 \<subseteq> set \<Gamma>\<^sub>2\<close>
  shows \<open>\<lbrakk>\<lbrakk> \<Gamma>\<^sub>1 @ \<Gamma>\<^sub>2 \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m = \<lbrakk>\<lbrakk> \<Gamma>\<^sub>2 \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m\<close>
  by (simp add: Int_absorb1 symrun_interp_decreases_setinc symrun_interp_expansion incl)

lemma symrun_interp_absorb2:
  assumes incl: \<open>set \<Gamma>\<^sub>2 \<subseteq> set \<Gamma>\<^sub>1\<close>
  shows \<open>\<lbrakk>\<lbrakk> \<Gamma>\<^sub>1 @ \<Gamma>\<^sub>2 \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m = \<lbrakk>\<lbrakk> \<Gamma>\<^sub>1 \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m\<close>
  using symrun_interp_absorb1 symrun_interp_commute incl by blast



end
