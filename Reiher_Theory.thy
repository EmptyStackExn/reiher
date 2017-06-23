theory Reiher_Theory
imports
  "Reiher"
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
oops

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

lemma prolongation_2:
  assumes "\<Gamma>\<^sub>1, n\<^sub>1 \<turnstile> [] \<triangleright> \<Phi>\<^sub>1 \<hookrightarrow> \<Gamma>\<^sub>2, n\<^sub>2 \<turnstile> [] \<triangleright> \<Phi>\<^sub>2"
  shows "\<lbrakk>\<lbrakk> \<Phi>\<^sub>1 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L \<inter> \<lbrakk>\<lbrakk> \<Gamma>\<^sub>1 \<rbrakk>\<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n \<supseteq> \<lbrakk>\<lbrakk> \<Phi>\<^sub>2 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L \<inter> \<lbrakk>\<lbrakk> \<Gamma>\<^sub>2 \<rbrakk>\<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n"
by (insert assms, erule operational_semantics_step.cases, auto)

lemma prolongation_and_composition:
  assumes "\<Gamma>, n \<turnstile> [] \<triangleright> (\<Phi>\<^sub>1 @ \<Phi>\<^sub>2) \<hookrightarrow> \<Gamma>', n' \<turnstile> [] \<triangleright> (\<Phi>\<^sub>1' @ \<Phi>\<^sub>2')"
  shows "\<lbrakk>\<lbrakk> \<Phi>\<^sub>1 @ \<Phi>\<^sub>2 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L \<supseteq> \<lbrakk>\<lbrakk> \<Phi>\<^sub>1' @ \<Phi>\<^sub>2' \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L"
by (insert assms, erule operational_semantics_step.cases, auto)



end