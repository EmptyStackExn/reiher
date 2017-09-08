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

lemma run_preservation:
  assumes "\<Gamma>\<^sub>1, n\<^sub>1 \<turnstile> \<Psi>\<^sub>1 \<triangleright> \<Phi>\<^sub>1  \<hookrightarrow>  \<Gamma>\<^sub>2, n\<^sub>2 \<turnstile> \<Psi>\<^sub>2 \<triangleright> \<Phi>\<^sub>2"
  shows "\<lbrakk>\<lbrakk> \<Phi>\<^sub>1 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L \<inter> \<lbrakk>\<lbrakk> \<Gamma>\<^sub>1 \<rbrakk>\<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n = \<lbrakk>\<lbrakk> \<Phi>\<^sub>2 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L \<inter> \<lbrakk>\<lbrakk> \<Gamma>\<^sub>2 \<rbrakk>\<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n"
apply (insert assms, erule operational_semantics_step.cases, auto)
sorry

lemma run_composition:
  assumes "\<Gamma>, n \<turnstile> \<Psi> \<triangleright> (\<Phi>\<^sub>1 @ \<Phi>\<^sub>2)  \<hookrightarrow>  \<Gamma>', n' \<turnstile> \<Psi>' \<triangleright> (\<Phi>\<^sub>1' @ \<Phi>\<^sub>2')"
  shows "\<lbrakk>\<lbrakk> \<Phi>\<^sub>1 @ \<Phi>\<^sub>2 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L = \<lbrakk>\<lbrakk> \<Phi>\<^sub>1' @ \<Phi>\<^sub>2' \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L"
apply (insert assms, erule operational_semantics_step.cases, auto)
sorry

lemma run_progress:
  assumes "(\<Gamma>\<^sub>1, n\<^sub>1 \<turnstile> [] \<triangleright> \<Phi>\<^sub>1, \<Gamma>\<^sub>2, n\<^sub>2 \<turnstile> [] \<triangleright> \<Phi>\<^sub>2) \<in> \<hookrightarrow>\<^sub>\<nabla>"
  shows "n\<^sub>2 = Suc n\<^sub>1"
sorry


(* OPERATIONAL \<longrightarrow> DENOTATIONAL *)
(* A chaque pas de simulation, les runs dérivés préfixent des runs dénotationels *)
lemma soundness:
  assumes "(\<Gamma>\<^sub>1, n\<^sub>1 \<turnstile> [] \<triangleright> \<Phi>\<^sub>1, \<Gamma>\<^sub>2, n\<^sub>2 \<turnstile> [] \<triangleright> \<Phi>\<^sub>2) \<in> \<hookrightarrow>\<^sub>\<nabla>"
  shows "\<forall>\<rho>\<^sub>o\<^sub>p \<in> \<lbrakk>\<lbrakk> \<Gamma>\<^sub>2 \<rbrakk>\<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n.
          \<exists>\<rho>\<^sub>d\<^sub>e\<^sub>n \<in> \<lbrakk>\<lbrakk> \<Phi>\<^sub>1 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L.
          \<forall>n > 0. n \<le> n\<^sub>2
            \<longrightarrow> (Rep_run \<rho>\<^sub>o\<^sub>p) n = (Rep_run \<rho>\<^sub>d\<^sub>e\<^sub>n) n"
sorry

(* DENOTATIONAL \<longrightarrow> OPERATIONAL *)
(* A chaque pas de simulation, un run dénoté préfixe un run dérivé opérationallement *)
lemma completeness:
  assumes "(\<Gamma>\<^sub>1, n\<^sub>1 \<turnstile> [] \<triangleright> \<Phi>\<^sub>1, \<Gamma>\<^sub>2, n\<^sub>2 \<turnstile> [] \<triangleright> \<Phi>\<^sub>2) \<in> \<hookrightarrow>\<^sub>\<nabla>"
  shows "\<forall>\<rho>\<^sub>d\<^sub>e\<^sub>n \<in> \<lbrakk>\<lbrakk> \<Phi>\<^sub>1 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L \<inter> \<lbrakk>\<lbrakk> \<Gamma>\<^sub>1 \<rbrakk>\<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n.
          \<exists>\<rho>\<^sub>o\<^sub>p \<in> \<lbrakk>\<lbrakk> \<Gamma>\<^sub>2 \<rbrakk>\<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n.
          \<forall>n > 0. n \<le> n\<^sub>2
            \<longrightarrow> (Rep_run \<rho>\<^sub>o\<^sub>p) n = (Rep_run \<rho>\<^sub>d\<^sub>e\<^sub>n) n"
sorry

end