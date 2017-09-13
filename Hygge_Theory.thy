theory Hygge_Theory
imports
  "Hygge"
  "Denotational"

begin

lemma context_consistency_preservationI:
  "consistent_run (\<gamma> # \<Gamma>) \<Longrightarrow> consistent_run \<Gamma>"
using consistent_run_def by auto

(* Very restrictive *)
inductive context_independency :: "constr \<Rightarrow> constr list \<Rightarrow> bool" ("_ \<bowtie> _") where
  NotTicks_independency:
  "K \<Up> n \<notin> set \<Gamma> \<Longrightarrow> K \<not>\<Up> n \<bowtie> \<Gamma>"
| Ticks_independency:
  "K \<not>\<Up> n \<notin> set \<Gamma> \<Longrightarrow> K \<Up> n \<bowtie> \<Gamma>"
| Timestamp_independency:
  "(\<nexists>\<tau>'. \<tau>' = \<tau> \<and> K \<Down> n @ \<tau> \<in> set \<Gamma>) \<Longrightarrow> K \<Down> n @ \<tau> \<bowtie> \<Gamma>"

thm context_independency.induct

(* by (insert assms, erule operational_semantics_step.cases, auto)
*)

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

lemma simple_derv_implies:
  assumes clk_d: "K\<^sub>1 \<noteq> K\<^sub>2"
  and     consist: "consistent_run \<Gamma>"
  shows   "\<TTurnstile> \<Gamma>, 0::nat \<turnstile> [] \<triangleright> [K\<^sub>1 implies K\<^sub>2]"

apply (rule finite_SAT_i)
apply (rule instant_i)
  using consist apply (assumption)
apply (rule finite_SAT_i)
apply (rule implies_e2, auto)
oops

text \<open>Every [n]-step derived symbolic run has a prefix of length [n] in the set of all denoted runs\<close>

(* Trying for one step *)
lemma
(*assumes derivability: "[(K\<^sub>1 \<Up> Suc 0), (K\<^sub>2 \<Up> Suc 0)], Suc 0 \<Turnstile> [] \<triangleright> [K\<^sub>1 implies K\<^sub>2]"
  assumes existence: "\<rho> \<in> \<lbrakk>\<lbrakk> \<Gamma> \<rbrakk>\<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n" *)
  shows "\<lbrakk>\<lbrakk> [(K\<^sub>1 \<Up> Suc 0), (K\<^sub>2 \<Up> Suc 0)] \<rbrakk>\<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n \<subseteq> \<lbrakk> K\<^sub>1 implies K\<^sub>2 @\<le> Suc 0 \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L"
proof
  fix \<rho>
  assume *: "\<rho> \<in> \<lbrakk>\<lbrakk> [K\<^sub>1 \<Up> Suc 0, K\<^sub>2 \<Up> Suc 0] \<rbrakk>\<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n"
  have "hamlet ((Rep_run \<rho>) (Suc 0) K\<^sub>1) = True \<and> hamlet ((Rep_run \<rho>) (Suc 0) K\<^sub>2) = True"
    using * by simp
  moreover have "hamlet ((Rep_run \<rho>) (Suc 0) K\<^sub>1) \<longrightarrow> hamlet ((Rep_run \<rho>) (Suc 0) K\<^sub>2)"
    by (simp add: calculation)
  moreover have "\<forall>n<Suc 0. hamlet ((Rep_run \<rho>) (Suc 0) K\<^sub>1) \<longrightarrow> hamlet ((Rep_run \<rho>) (Suc 0) K\<^sub>2)"
    using calculation(2) by blast
  then show "\<rho> \<in> \<lbrakk> K\<^sub>1 implies K\<^sub>2 @\<le> Suc 0 \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L" by auto
qed

lemma
  shows "\<lbrakk>\<lbrakk> [(K\<^sub>1 \<Up> Suc 0), (K\<^sub>2 \<Up> Suc 0), (K\<^sub>1 \<Up> Suc (Suc 0)), (K\<^sub>2 \<Up> Suc (Suc 0))] \<rbrakk>\<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n
          \<subseteq> \<lbrakk> K\<^sub>1 implies K\<^sub>2 @\<le> Suc (Suc 0) \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L"
proof
  fix \<rho>
  assume *: "\<rho> \<in> \<lbrakk>\<lbrakk> [(K\<^sub>1 \<Up> Suc 0), (K\<^sub>2 \<Up> Suc 0), (K\<^sub>1 \<Up> Suc (Suc 0)), (K\<^sub>2 \<Up> Suc (Suc 0))] \<rbrakk>\<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n"
  have "hamlet ((Rep_run \<rho>) (Suc 0) K\<^sub>1) = True \<and> hamlet ((Rep_run \<rho>) (Suc 0) K\<^sub>2) = True"
    using * by simp
  moreover have "hamlet ((Rep_run \<rho>) (Suc (Suc 0)) K\<^sub>1) = True \<and> hamlet ((Rep_run \<rho>) (Suc (Suc 0)) K\<^sub>2) = True"
    using * by simp
  ultimately have "\<forall>n<Suc (Suc 0). hamlet ((Rep_run \<rho>) (Suc 0) K\<^sub>1) \<longrightarrow> hamlet ((Rep_run \<rho>) (Suc 0) K\<^sub>2)"
    by simp
  then show "\<rho> \<in> \<lbrakk> K\<^sub>1 implies K\<^sub>2 @\<le> Suc (Suc 0) \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L"
    using less_2_cases numerals(2) by auto
qed

term "({}::(nat rel)) ^^ (n::nat)"

(* sledgehammer[provers="remote_e spass remote_vampire cvc4 z3"] *)

lemma refinement_at_each_step:
  assumes "\<Gamma>\<^sub>1, n\<^sub>1 \<turnstile> \<Psi>\<^sub>1 \<triangleright> \<Phi>\<^sub>1 \<hookrightarrow> \<Gamma>\<^sub>2, n\<^sub>2 \<turnstile> \<Psi>\<^sub>2 \<triangleright> \<Phi>\<^sub>2"
  shows "\<lbrakk>\<lbrakk> \<Gamma>\<^sub>1 \<rbrakk>\<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n \<supseteq> \<lbrakk>\<lbrakk> \<Gamma>\<^sub>2 \<rbrakk>\<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n"
by (insert assms, erule operational_semantics_step.cases, auto)

lemma composition:
  assumes "K\<^sub>1 time-delayed by \<delta>\<tau> on K\<^sub>2 implies K\<^sub>3 \<notin> set \<Phi> \<union> set \<Phi>'"
  assumes "\<TTurnstile> \<Gamma>\<^sub>1, n \<turnstile> [] \<triangleright> \<Phi>\<^sub>1"
  assumes "\<TTurnstile> \<Gamma>\<^sub>2, n \<turnstile> [] \<triangleright> \<Phi>\<^sub>2"
  assumes "consistency_run (\<Gamma>\<^sub>1 @ \<Gamma>\<^sub>2)"
  shows   "\<TTurnstile> \<Gamma>\<^sub>1 @ \<Gamma>\<^sub>2, n \<turnstile> [] \<triangleright> \<Phi>\<^sub>1 @ \<Phi>\<^sub>2"
oops

lemma "set (NoSporadic \<Phi>) \<subseteq> set \<Phi>"
by auto

lemma mono_TESL_interpr:
  assumes "set \<Phi>\<^sub>1 \<subseteq> set \<Phi>\<^sub>2"
  shows "\<lbrakk>\<lbrakk> \<Phi>\<^sub>2 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L \<subseteq> \<lbrakk>\<lbrakk> \<Phi>\<^sub>1 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L"
proof (induction \<Phi>\<^sub>1)
  case Nil
  then show ?case by simp
next
  case (Cons a \<Phi>\<^sub>1)
  then show ?case sorry
qed

lemma idempot_TESL_interpr:
  shows "\<lbrakk>\<lbrakk> \<Phi> @ \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L = \<lbrakk>\<lbrakk> \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L"
proof (induction \<Phi>)
  case Nil
  then show ?case by simp
next
  case (Cons \<phi> \<Phi>')
  then show ?case sorry
qed

(*
fun symbolic_run_interpretation :: "constr list \<Rightarrow> run set" ("\<lbrakk>\<lbrakk> _ \<rbrakk>\<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n") where
    "\<lbrakk>\<lbrakk> [] \<rbrakk>\<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n = { _. True }"
  | "\<lbrakk>\<lbrakk> \<gamma> # \<Gamma> \<rbrakk>\<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n = \<lbrakk> \<gamma> \<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n \<inter> \<lbrakk>\<lbrakk> \<Gamma> \<rbrakk>\<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n"
*)
lemma mono_symrun_interpr:
  assumes "set \<Gamma>\<^sub>1 \<subseteq> set \<Gamma>\<^sub>2"
  shows "\<lbrakk>\<lbrakk> \<Gamma>\<^sub>2 \<rbrakk>\<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n \<subseteq> \<lbrakk>\<lbrakk> \<Gamma>\<^sub>1 \<rbrakk>\<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n"
sorry

lemma minus_sporadic_stable [simp]: "\<lbrakk>\<lbrakk> \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L \<subseteq> \<lbrakk>\<lbrakk> NoSporadic \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L"
by (meson filter_is_subset mono_TESL_interpr)

lemma minus_sporadic_idempt [simp]: "\<lbrakk>\<lbrakk> \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L \<inter> \<lbrakk>\<lbrakk> NoSporadic \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L = \<lbrakk>\<lbrakk> \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L"
by (meson Int_absorb2 filter_is_subset mono_TESL_interpr)

lemma tesl_intersect_id [simp]: "\<lbrakk>\<lbrakk> \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L \<inter> \<lbrakk>\<lbrakk> [] \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L = \<lbrakk>\<lbrakk> \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L"
by simp

(* Prefix notation with fixed prefix length *)
abbreviation run_prefix :: "run \<Rightarrow> nat \<Rightarrow> run \<Rightarrow> bool" ("_ \<sqsubseteq>\<^sup>p\<^sup>r\<^sup>e\<^sup>f\<^sup>i\<^sup>x\<^bsub>_\<^esub> _") where
  "\<rho>\<^sub>1 \<sqsubseteq>\<^sup>p\<^sup>r\<^sup>e\<^sup>f\<^sup>i\<^sup>x\<^bsub>k\<^esub> \<rho>\<^sub>2 \<equiv> \<forall>n > 0. n \<le> k \<longrightarrow> (Rep_run \<rho>\<^sub>1) k = (Rep_run \<rho>\<^sub>2) k"

lemma run_prefix_commut[simp]:
  shows "\<rho>\<^sub>1 \<sqsubseteq>\<^sup>p\<^sup>r\<^sup>e\<^sup>f\<^sup>i\<^sup>x\<^bsub>k\<^esub> \<rho>\<^sub>2 = \<rho>\<^sub>2 \<sqsubseteq>\<^sup>p\<^sup>r\<^sup>e\<^sup>f\<^sup>i\<^sup>x\<^bsub>k\<^esub> \<rho>\<^sub>1"
by auto

abbreviation inclusion_prefix :: "run set \<Rightarrow> nat \<Rightarrow> run set \<Rightarrow> bool" ("_ \<subseteq>\<^sup>p\<^sup>r\<^sup>e\<^sup>f\<^sup>i\<^sup>x\<^bsub>_\<^esub> _") where
  "R\<^sub>1 \<subseteq>\<^sup>p\<^sup>r\<^sup>e\<^sup>f\<^sup>i\<^sup>x\<^bsub>k\<^esub> R\<^sub>2 \<equiv> \<forall>\<rho>\<^sub>1 \<in> R\<^sub>1. \<exists>\<rho>\<^sub>2 \<in> R\<^sub>2. \<forall>n > 0. n \<le> k \<longrightarrow> (Rep_run \<rho>\<^sub>1) k = (Rep_run \<rho>\<^sub>2) k"

lemma
  assumes "R\<^sub>1 \<subseteq>\<^sup>p\<^sup>r\<^sup>e\<^sup>f\<^sup>i\<^sup>x\<^bsub>k\<^esub> R\<^sub>2"
  shows "R\<^sub>1 \<inter> R \<subseteq>\<^sup>p\<^sup>r\<^sup>e\<^sup>f\<^sup>i\<^sup>x\<^bsub>k\<^esub> R\<^sub>2 \<inter> R"
sorry

lemma run_progress:
  assumes "\<Gamma>\<^sub>1, n\<^sub>1 \<turnstile> \<Psi>\<^sub>1 \<triangleright> \<Phi>\<^sub>1  \<hookrightarrow>  \<Gamma>\<^sub>2, n\<^sub>2 \<turnstile> \<Psi>\<^sub>2 \<triangleright> \<Phi>\<^sub>2"
  shows "n\<^sub>2 = Suc n\<^sub>1 \<or> n\<^sub>2 = n\<^sub>1"
by (insert assms, erule operational_semantics_step.cases, auto)

lemma run_preservation:
  assumes "\<Gamma>\<^sub>1, n\<^sub>1 \<turnstile> \<Psi>\<^sub>1 \<triangleright> \<Phi>\<^sub>1  \<hookrightarrow>  \<Gamma>\<^sub>2, n\<^sub>2 \<turnstile> \<Psi>\<^sub>2 \<triangleright> \<Phi>\<^sub>2"
  and "\<lbrakk>\<lbrakk> \<Gamma>\<^sub>1 \<rbrakk>\<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n \<subseteq>\<^sup>p\<^sup>r\<^sup>e\<^sup>f\<^sup>i\<^sup>x\<^bsub>k-1\<^esub> \<lbrakk>\<lbrakk> \<Psi>\<^sub>1 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L \<inter> \<lbrakk>\<lbrakk> \<Phi>\<^sub>1 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L"
  shows "\<lbrakk>\<lbrakk> \<Gamma>\<^sub>2 \<rbrakk>\<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n \<inter> \<lbrakk>\<lbrakk> \<Psi>\<^sub>2 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L \<inter> \<lbrakk>\<lbrakk> \<Phi>\<^sub>2 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L \<subseteq>\<^sup>p\<^sup>r\<^sup>e\<^sup>f\<^sup>i\<^sup>x\<^bsub>n\<^sub>2\<^esub> \<lbrakk>\<lbrakk> \<Gamma>\<^sub>1 \<rbrakk>\<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n \<inter> \<lbrakk>\<lbrakk> \<Psi>\<^sub>1 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L \<inter> \<lbrakk>\<lbrakk> \<Phi>\<^sub>1 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L"
proof (insert assms, erule operational_semantics_step.cases)
  show "\<And>\<Gamma> n \<phi>.
       \<forall>\<rho>\<^sub>1\<in>\<lbrakk>\<lbrakk> \<Gamma>\<^sub>1 \<rbrakk>\<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n.
          \<exists>\<rho>\<^sub>2\<in>\<lbrakk>\<lbrakk> \<Psi>\<^sub>1 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L \<inter> \<lbrakk>\<lbrakk> \<Phi>\<^sub>1 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L.
             \<forall>n>0. n \<le> k - 1 \<longrightarrow> Rep_run \<rho>\<^sub>1 (k - 1) = Rep_run \<rho>\<^sub>2 (k - 1) \<Longrightarrow>
       (\<Gamma>\<^sub>1, n\<^sub>1 \<turnstile> \<Psi>\<^sub>1 \<triangleright> \<Phi>\<^sub>1) = (\<Gamma>, n \<turnstile> [] \<triangleright> \<phi>) \<Longrightarrow>
       (\<Gamma>\<^sub>2, n\<^sub>2 \<turnstile> \<Psi>\<^sub>2 \<triangleright> \<Phi>\<^sub>2) = (\<Gamma>, Suc n \<turnstile> \<phi> \<triangleright> NoSporadic \<phi>) \<Longrightarrow>
       consistent_run \<Gamma> \<Longrightarrow>
       \<forall>\<rho>\<^sub>1\<in>\<lbrakk>\<lbrakk> \<Gamma>\<^sub>2 \<rbrakk>\<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n \<inter> \<lbrakk>\<lbrakk> \<Psi>\<^sub>2 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L \<inter> \<lbrakk>\<lbrakk> \<Phi>\<^sub>2 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L.
          \<exists>\<rho>\<^sub>2\<in>\<lbrakk>\<lbrakk> \<Gamma>\<^sub>1 \<rbrakk>\<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n \<inter> \<lbrakk>\<lbrakk> \<Psi>\<^sub>1 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L \<inter> \<lbrakk>\<lbrakk> \<Phi>\<^sub>1 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L.
             \<forall>n>0. n \<le> n\<^sub>2 \<longrightarrow> Rep_run \<rho>\<^sub>1 n\<^sub>2 = Rep_run \<rho>\<^sub>2 n\<^sub>2"
  by auto
  show "\<And>\<Gamma> n K \<tau> \<psi> \<phi>.
       \<forall>\<rho>\<^sub>1\<in>\<lbrakk>\<lbrakk> \<Gamma>\<^sub>1 \<rbrakk>\<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n.
          \<exists>\<rho>\<^sub>2\<in>\<lbrakk>\<lbrakk> \<Psi>\<^sub>1 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L \<inter> \<lbrakk>\<lbrakk> \<Phi>\<^sub>1 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L.
             \<forall>n>0. n \<le> k - 1 \<longrightarrow> Rep_run \<rho>\<^sub>1 (k - 1) = Rep_run \<rho>\<^sub>2 (k - 1) \<Longrightarrow>
       (\<Gamma>\<^sub>1, n\<^sub>1 \<turnstile> \<Psi>\<^sub>1 \<triangleright> \<Phi>\<^sub>1) = (\<Gamma>, n \<turnstile> (K sporadic \<tau>) # \<psi> \<triangleright> \<phi>) \<Longrightarrow>
       (\<Gamma>\<^sub>2, n\<^sub>2 \<turnstile> \<Psi>\<^sub>2 \<triangleright> \<Phi>\<^sub>2) = (\<Gamma>, n \<turnstile> \<psi> \<triangleright> (K sporadic \<tau>) # \<phi>) \<Longrightarrow>
       consistent_run \<Gamma> \<Longrightarrow>
       \<forall>\<rho>\<^sub>1\<in>\<lbrakk>\<lbrakk> \<Gamma>\<^sub>2 \<rbrakk>\<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n \<inter> \<lbrakk>\<lbrakk> \<Psi>\<^sub>2 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L \<inter> \<lbrakk>\<lbrakk> \<Phi>\<^sub>2 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L.
          \<exists>\<rho>\<^sub>2\<in>\<lbrakk>\<lbrakk> \<Gamma>\<^sub>1 \<rbrakk>\<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n \<inter> \<lbrakk>\<lbrakk> \<Psi>\<^sub>1 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L \<inter> \<lbrakk>\<lbrakk> \<Phi>\<^sub>1 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L.
             \<forall>n>0. n \<le> n\<^sub>2 \<longrightarrow> Rep_run \<rho>\<^sub>1 n\<^sub>2 = Rep_run \<rho>\<^sub>2 n\<^sub>2"
  by auto
  show "\<And>\<Gamma>' K n \<tau> \<Gamma> \<psi> \<phi>.
       \<forall>\<rho>\<^sub>1\<in>\<lbrakk>\<lbrakk> \<Gamma>\<^sub>1 \<rbrakk>\<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n.
          \<exists>\<rho>\<^sub>2\<in>\<lbrakk>\<lbrakk> \<Psi>\<^sub>1 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L \<inter> \<lbrakk>\<lbrakk> \<Phi>\<^sub>1 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L.
             \<forall>n>0. n \<le> k - 1 \<longrightarrow> Rep_run \<rho>\<^sub>1 (k - 1) = Rep_run \<rho>\<^sub>2 (k - 1) \<Longrightarrow>
       (\<Gamma>\<^sub>1, n\<^sub>1 \<turnstile> \<Psi>\<^sub>1 \<triangleright> \<Phi>\<^sub>1) = (\<Gamma>, n \<turnstile> (K sporadic \<tau>) # \<psi> \<triangleright> \<phi>) \<Longrightarrow>
       (\<Gamma>\<^sub>2, n\<^sub>2 \<turnstile> \<Psi>\<^sub>2 \<triangleright> \<Phi>\<^sub>2) = (\<Gamma>', n \<turnstile> \<psi> \<triangleright> \<phi>) \<Longrightarrow>
       consistent_run \<Gamma>' \<Longrightarrow>
       \<Gamma>' = K \<Up> n # K \<Down> n @ \<lfloor> \<tau> \<rfloor> # \<Gamma> \<Longrightarrow>
       \<forall>\<rho>\<^sub>1\<in>\<lbrakk>\<lbrakk> \<Gamma>\<^sub>2 \<rbrakk>\<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n \<inter> \<lbrakk>\<lbrakk> \<Psi>\<^sub>2 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L \<inter> \<lbrakk>\<lbrakk> \<Phi>\<^sub>2 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L.
          \<exists>\<rho>\<^sub>2\<in>\<lbrakk>\<lbrakk> \<Gamma>\<^sub>1 \<rbrakk>\<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n \<inter> \<lbrakk>\<lbrakk> \<Psi>\<^sub>1 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L \<inter> \<lbrakk>\<lbrakk> \<Phi>\<^sub>1 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L.
             \<forall>n>0. n \<le> n\<^sub>2 \<longrightarrow> Rep_run \<rho>\<^sub>1 n\<^sub>2 = Rep_run \<rho>\<^sub>2 n\<^sub>2"
  by auto
  show "\<And>\<Gamma> n K\<^sub>1 \<tau> K\<^sub>2 \<psi> \<phi>.
       \<forall>\<rho>\<^sub>1\<in>\<lbrakk>\<lbrakk> \<Gamma>\<^sub>1 \<rbrakk>\<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n.
          \<exists>\<rho>\<^sub>2\<in>\<lbrakk>\<lbrakk> \<Psi>\<^sub>1 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L \<inter> \<lbrakk>\<lbrakk> \<Phi>\<^sub>1 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L.
             \<forall>n>0. n \<le> k - 1 \<longrightarrow> Rep_run \<rho>\<^sub>1 (k - 1) = Rep_run \<rho>\<^sub>2 (k - 1) \<Longrightarrow>
       (\<Gamma>\<^sub>1, n\<^sub>1 \<turnstile> \<Psi>\<^sub>1 \<triangleright> \<Phi>\<^sub>1) = (\<Gamma>, n \<turnstile> (K\<^sub>1 sporadic \<tau> on K\<^sub>2) # \<psi> \<triangleright> \<phi>) \<Longrightarrow>
       (\<Gamma>\<^sub>2, n\<^sub>2 \<turnstile> \<Psi>\<^sub>2 \<triangleright> \<Phi>\<^sub>2) = (\<Gamma>, n \<turnstile> \<psi> \<triangleright> (K\<^sub>1 sporadic \<tau> on K\<^sub>2) # \<phi>) \<Longrightarrow>
       consistent_run \<Gamma> \<Longrightarrow>
       \<forall>\<rho>\<^sub>1\<in>\<lbrakk>\<lbrakk> \<Gamma>\<^sub>2 \<rbrakk>\<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n \<inter> \<lbrakk>\<lbrakk> \<Psi>\<^sub>2 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L \<inter> \<lbrakk>\<lbrakk> \<Phi>\<^sub>2 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L.
          \<exists>\<rho>\<^sub>2\<in>\<lbrakk>\<lbrakk> \<Gamma>\<^sub>1 \<rbrakk>\<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n \<inter> \<lbrakk>\<lbrakk> \<Psi>\<^sub>1 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L \<inter> \<lbrakk>\<lbrakk> \<Phi>\<^sub>1 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L.
             \<forall>n>0. n \<le> n\<^sub>2 \<longrightarrow> Rep_run \<rho>\<^sub>1 n\<^sub>2 = Rep_run \<rho>\<^sub>2 n\<^sub>2"
  by auto
  show "\<And>\<Gamma>' K\<^sub>1 n K\<^sub>2 \<tau> \<Gamma> \<psi> \<phi>.
       \<forall>\<rho>\<^sub>1\<in>\<lbrakk>\<lbrakk> \<Gamma>\<^sub>1 \<rbrakk>\<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n.
          \<exists>\<rho>\<^sub>2\<in>\<lbrakk>\<lbrakk> \<Psi>\<^sub>1 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L \<inter> \<lbrakk>\<lbrakk> \<Phi>\<^sub>1 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L.
             \<forall>n>0. n \<le> k - 1 \<longrightarrow> Rep_run \<rho>\<^sub>1 (k - 1) = Rep_run \<rho>\<^sub>2 (k - 1) \<Longrightarrow>
       (\<Gamma>\<^sub>1, n\<^sub>1 \<turnstile> \<Psi>\<^sub>1 \<triangleright> \<Phi>\<^sub>1) = (\<Gamma>, n \<turnstile> (K\<^sub>1 sporadic \<tau> on K\<^sub>2) # \<psi> \<triangleright> \<phi>) \<Longrightarrow>
       (\<Gamma>\<^sub>2, n\<^sub>2 \<turnstile> \<Psi>\<^sub>2 \<triangleright> \<Phi>\<^sub>2) = (\<Gamma>', n \<turnstile> \<psi> \<triangleright> \<phi>) \<Longrightarrow>
       consistent_run \<Gamma>' \<Longrightarrow>
       \<Gamma>' = K\<^sub>1 \<Up> n # K\<^sub>2 \<Down> n @ \<tau> # \<Gamma> \<Longrightarrow>
       \<forall>\<rho>\<^sub>1\<in>\<lbrakk>\<lbrakk> \<Gamma>\<^sub>2 \<rbrakk>\<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n \<inter> \<lbrakk>\<lbrakk> \<Psi>\<^sub>2 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L \<inter> \<lbrakk>\<lbrakk> \<Phi>\<^sub>2 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L.
          \<exists>\<rho>\<^sub>2\<in>\<lbrakk>\<lbrakk> \<Gamma>\<^sub>1 \<rbrakk>\<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n \<inter> \<lbrakk>\<lbrakk> \<Psi>\<^sub>1 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L \<inter> \<lbrakk>\<lbrakk> \<Phi>\<^sub>1 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L.
             \<forall>n>0. n \<le> n\<^sub>2 \<longrightarrow> Rep_run \<rho>\<^sub>1 n\<^sub>2 = Rep_run \<rho>\<^sub>2 n\<^sub>2"
  proof -
    have "\<lbrakk>\<lbrakk> [K\<^sub>1 \<Up> n, K\<^sub>2 \<Down> n @ \<tau>] \<rbrakk>\<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n \<subseteq>\<^sup>p\<^sup>r\<^sup>e\<^sup>f\<^sup>i\<^sup>x\<^bsub>Suc n\<^esub> \<lbrakk>\<lbrakk> [K\<^sub>1 sporadic \<tau> on K\<^sub>2] \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L"
      sorry
    have "\<lbrakk>\<lbrakk> [K\<^sub>1 \<Up> n, K\<^sub>2 \<Down> n @ \<tau>] \<rbrakk>\<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n \<subseteq> \<lbrakk> K\<^sub>1 sporadic \<tau> on K\<^sub>2 \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L"
      proof
        fix \<rho>
        assume R: "\<rho> \<in> \<lbrakk>\<lbrakk> [K\<^sub>1 \<Up> n, K\<^sub>2 \<Down> n @ \<tau>] \<rbrakk>\<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n"
        have "hamlet ((Rep_run \<rho>) n K\<^sub>1) = True" using R by auto
        moreover have "\<tau> = \<lfloor>\<tau>'\<rfloor> \<Longrightarrow> time ((Rep_run \<rho>) n K\<^sub>2) = \<tau>'" using R by auto
        moreover have "\<exists>n::nat. hamlet ((Rep_run \<rho>) n K\<^sub>1) = True \<and> time ((Rep_run \<rho>) n K\<^sub>2) = \<tau>'" sorry
        ultimately show "\<rho> \<in> \<lbrakk> K\<^sub>1 sporadic \<tau> on K\<^sub>2 \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L"  sorry
      qed
    show "\<forall>\<rho>\<^sub>1\<in>\<lbrakk>\<lbrakk> \<Gamma>\<^sub>2 \<rbrakk>\<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n \<inter> \<lbrakk>\<lbrakk> \<Psi>\<^sub>2 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L \<inter> \<lbrakk>\<lbrakk> \<Phi>\<^sub>2 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L.
          \<exists>\<rho>\<^sub>2\<in>\<lbrakk>\<lbrakk> \<Gamma>\<^sub>1 \<rbrakk>\<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n \<inter> \<lbrakk>\<lbrakk> \<Psi>\<^sub>1 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L \<inter> \<lbrakk>\<lbrakk> \<Phi>\<^sub>1 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L.
             \<forall>n>0. n \<le> n\<^sub>2 \<longrightarrow> Rep_run \<rho>\<^sub>1 n\<^sub>2 = Rep_run \<rho>\<^sub>2 n\<^sub>2" sorry
qed

lemma run_composition:
  assumes "\<Gamma>, n \<turnstile> \<Psi>\<^sub>1 \<triangleright> (\<Phi>\<^sub>1 @ \<Phi>\<^sub>2)  \<hookrightarrow>  \<Gamma>', n' \<turnstile> \<Psi>\<^sub>2 \<triangleright> (\<Phi>\<^sub>1' @ \<Phi>\<^sub>2')"
  shows "\<lbrakk>\<lbrakk> \<Phi>\<^sub>1 @ \<Phi>\<^sub>2 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L = \<lbrakk>\<lbrakk> \<Phi>\<^sub>1' @ \<Phi>\<^sub>2' \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L"
by (insert assms, erule operational_semantics_step.cases, auto)

(* OPERATIONAL \<longrightarrow> DENOTATIONAL *)
(* A chaque pas de simulation, les runs dérivés préfixent les runs dénotationels *)
lemma soundness:
  assumes "\<Gamma>\<^sub>1, n\<^sub>1 \<turnstile> [] \<triangleright> \<Phi>\<^sub>1  \<hookrightarrow>  \<Gamma>\<^sub>2, n\<^sub>2 \<turnstile> [] \<triangleright> \<Phi>\<^sub>2"
  shows "\<forall>\<rho>\<^sub>o\<^sub>p \<in> \<lbrakk>\<lbrakk> \<Gamma>\<^sub>2 \<rbrakk>\<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n. \<exists>\<rho>\<^sub>d\<^sub>e\<^sub>n \<in> \<lbrakk>\<lbrakk> \<Phi>\<^sub>1 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L.
          \<rho>\<^sub>o\<^sub>p \<sqsubseteq>\<^sup>p\<^sup>r\<^sup>e\<^sup>f\<^sup>i\<^sup>x\<^bsub>n\<^sub>2\<^esub> \<rho>\<^sub>d\<^sub>e\<^sub>n"
by (insert assms, erule operational_semantics_step.cases, auto)

(* DENOTATIONAL \<longrightarrow> OPERATIONAL *)
(* A chaque pas de simulation, un run dénoté préfixe un run dérivé opérationallement *)
lemma completeness:
  assumes "\<Gamma>\<^sub>1, n\<^sub>1 \<turnstile> [] \<triangleright> \<Phi>\<^sub>1 \<hookrightarrow> \<Gamma>\<^sub>2, n\<^sub>2 \<turnstile> [] \<triangleright> \<Phi>\<^sub>2"
  shows "\<forall>\<rho>\<^sub>d\<^sub>e\<^sub>n \<in> \<lbrakk>\<lbrakk> \<Phi>\<^sub>1 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L \<inter> \<lbrakk>\<lbrakk> \<Gamma>\<^sub>1 \<rbrakk>\<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n. \<exists>\<rho>\<^sub>o\<^sub>p \<in> \<lbrakk>\<lbrakk> \<Gamma>\<^sub>2 \<rbrakk>\<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n.
          \<rho>\<^sub>d\<^sub>e\<^sub>n \<sqsubseteq>\<^sup>p\<^sup>r\<^sup>e\<^sup>f\<^sup>i\<^sup>x\<^bsub>n\<^sub>2\<^esub> \<rho>\<^sub>o\<^sub>p"
by (insert assms, erule operational_semantics_step.cases, auto)

end