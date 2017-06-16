theory Reiher_Theory
imports
  "Reiher"
  "Denotational"

begin

lemma context_consistency_preservationI:
  "consistent_run (\<gamma> # \<Gamma>) \<Longrightarrow> consistent_run \<Gamma>"
using consistent_run_def by auto

inductive context_independency :: "constr \<Rightarrow> constr list \<Rightarrow> bool" ("_ \<bowtie> _") where
  "\<gamma> \<notin> set \<Gamma> \<Longrightarrow> \<gamma> \<bowtie> \<Gamma>"

lemma context_consistency_preservationE:
  assumes "consistent_run \<Gamma>"
  and     "\<gamma> \<bowtie> \<Gamma>"
  shows "consistent_run (\<gamma> # \<Gamma>)"
using consistent_run_def sorry

lemma simple_derv_implies:
  assumes clk_d: "K\<^sub>1 \<noteq> K\<^sub>2"
  and     consist: "consistent_run \<Gamma>"
  shows   "\<TTurnstile> \<Gamma>, 0::nat \<turnstile> [] \<triangleright> [K\<^sub>1 implies K\<^sub>2]"

apply (rule finite_SAT_i)
apply (rule instant_i)
  using consist apply (assumption)
apply (rule finite_SAT_i)
apply (rule implies_e2, auto)
sorry

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
  assumes cons: "consistent_run \<Gamma>\<^sub>1"
  assumes red: "\<Gamma>\<^sub>1, n\<^sub>1 \<turnstile> \<Psi>\<^sub>1 \<triangleright> \<Phi>\<^sub>1 \<hookrightarrow> \<Gamma>\<^sub>2, n\<^sub>2 \<turnstile> \<Psi>\<^sub>2 \<triangleright> \<Phi>\<^sub>2"
  shows "\<lbrakk>\<lbrakk> \<Gamma>\<^sub>1 \<rbrakk>\<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n \<supseteq> \<lbrakk>\<lbrakk> \<Gamma>\<^sub>2 \<rbrakk>\<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n"
proof (induction \<Psi>\<^sub>1)
  case Nil
  have *: "\<Gamma>\<^sub>1, n\<^sub>1 \<turnstile> [] \<triangleright> \<Phi>\<^sub>1 \<hookrightarrow> \<Gamma>\<^sub>1, Suc n\<^sub>1 \<turnstile> \<Phi>\<^sub>1 \<triangleright> NoSporadic \<Phi>\<^sub>1"
    apply (rule instant_i)
    using cons by assumption
  moreover have "\<Gamma>\<^sub>1 = \<Gamma>\<^sub>2" using Nil cons red * nitpick (* Où est l'hypothèse que \<Phi>\<^sub>1 = [] ? *) sorry
  then show ?case by auto
next
  case (Cons \<phi>\<^sub>1 \<Psi>\<^sub>1)
  then show ?case by simp
qed

lemma composition:
  assumes "K\<^sub>1 time-delayed by \<delta>\<tau> on K\<^sub>2 implies K\<^sub>3 \<notin> set \<Phi> \<union> set \<Phi>'"
  assumes "\<TTurnstile> \<Gamma>\<^sub>1, n \<turnstile> [] \<triangleright> \<Phi>\<^sub>1"
  assumes "\<TTurnstile> \<Gamma>\<^sub>2, n \<turnstile> [] \<triangleright> \<Phi>\<^sub>2"
  assumes "consistency_run (\<Gamma>\<^sub>1 @ \<Gamma>\<^sub>2)"
  shows   "\<TTurnstile> \<Gamma>\<^sub>1 @ \<Gamma>\<^sub>2, n \<turnstile> [] \<triangleright> \<Phi>\<^sub>1 @ \<Phi>\<^sub>2"
  sorry

lemma prolongation_2:
  assumes "n' > n"
  and "set \<Gamma>' \<supseteq> set \<Gamma>"
  and "set \<Phi>' \<subseteq> set \<Phi>"
  assumes "\<Gamma>, n \<turnstile> [] \<triangleright> \<Phi> \<hookrightarrow> \<Gamma>', n' \<turnstile> [] \<triangleright> \<Phi>'"
  shows "\<lbrakk>\<lbrakk> \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L \<inter> \<lbrakk>\<lbrakk> \<Gamma> \<rbrakk>\<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n \<supseteq> \<lbrakk>\<lbrakk> \<Phi>' \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L \<inter> \<lbrakk>\<lbrakk> \<Gamma>' \<rbrakk>\<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n"
  sorry

lemma prolongation_and_composition:
  assumes "\<Gamma>, n \<turnstile> [] \<triangleright> (\<Phi>' @ \<Psi>') \<hookrightarrow> \<Gamma>', n' \<turnstile> [] \<triangleright> (\<Phi> @ \<Psi>)"
  shows "\<lbrakk>\<lbrakk> \<Phi> @ \<Psi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L \<subseteq> \<lbrakk>\<lbrakk> \<Phi>' @ \<Psi>' \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L"
  sorry



end