theory Reiher_Theory
imports
  "Reiher"
  "DeepDenotational"

begin

lemma context_consistency_preservation:
  "consistent_run (\<gamma> # \<Gamma>) \<Longrightarrow> consistent_run \<Gamma>"
using consistent_run_def by auto

lemma simple_derv_implies:
  assumes ih:  "\<Gamma>', Suc 0  \<Turnstile> [] \<triangleright> [K\<^sub>1 implies K\<^sub>2]"
  and     ih2: "\<Gamma>' = (K\<^sub>1 \<Up> Suc 0)  # (K\<^sub>2 \<Up> Suc 0) # \<Gamma>"
  and     consist: "consistent_run ((K\<^sub>1 \<Up> Suc 0)  # (K\<^sub>2 \<Up> Suc 0) # \<Gamma>)"
  shows   "\<Gamma>, 0::nat \<Turnstile> [] \<triangleright> [K\<^sub>1 implies K\<^sub>2]"
proof -
show ?thesis
apply (rule init, auto)
apply (rule context_consistency_preservation)
using consist
apply (rule context_consistency_preservation)
apply (rule implies_e2)
using consist
apply (assumption)
using assms
by (auto)
qed

(* Every [n]-step derived symbolic run has a prefix of length [n] in the set of all denoted runs *)
(* Trying for one step *)
lemma operational_soundness:
  assumes derivability: "[(K\<^sub>1 \<Up> Suc 0), (K\<^sub>2 \<Up> Suc 0)], Suc 0 \<Turnstile> [] \<triangleright> [K\<^sub>1 implies K\<^sub>2]"
  assumes existence: "\<rho> \<in> \<lbrakk>\<lbrakk> \<Gamma> \<rbrakk>\<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n"
  shows "\<lbrakk>\<lbrakk> [(K\<^sub>1 \<Up> Suc 0), (K\<^sub>2 \<Up> Suc 0)] \<rbrakk>\<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n \<subseteq> \<lbrakk> K\<^sub>1 implies K\<^sub>2 @\<le> Suc 0 \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L"
proof
  fix \<rho>
  assume *: "\<rho> \<in> \<lbrakk>\<lbrakk> [K\<^sub>1 \<Up> Suc 0, K\<^sub>2 \<Up> Suc 0] \<rbrakk>\<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n"
  have "hamlet ((Rep_run \<rho>) (Suc 0) K\<^sub>1) = True \<and> hamlet ((Rep_run \<rho>) (Suc 0) K\<^sub>2) = True"
    using * by simp
  moreover have "hamlet ((Rep_run \<rho>) (Suc 0) K\<^sub>1) \<longrightarrow> hamlet ((Rep_run \<rho>) (Suc 0) K\<^sub>2)"
    by (simp add: calculation)
  then show "\<rho> \<in> \<lbrakk> K\<^sub>1 implies K\<^sub>2 @\<le> Suc 0 \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L" sorry
qed

(* Every TESL formula has a satisfying run *)
lemma existence:
  shows "\<exists>\<rho>. \<rho> \<in> \<lbrakk>\<lbrakk> \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L"
  proof (induction \<Phi>)
  case Nil
  then show ?case by simp
next
  case (Cons \<phi> \<Phi>')
  then show ?case
    proof (induction \<phi>)
      case (Sporadic x1 x2)
      then show ?case sorry
    next
      case (SporadicOn x1 x2 x3)
      then show ?case sorry
    next
      case (TagRelation x1 x2 x3 x4)
      then show ?case sorry
    next
      case (Implies x1 x2)
      then show ?case sorry
    next
      case (TimeDelayedBy x1 x2 x3 x4)
      then show ?case sorry
    qed
qed

lemma composition:
  assumes "K\<^sub>1 time-delayed by \<delta>\<tau> on K\<^sub>2 implies K\<^sub>3 \<notin> set \<Phi> \<union> set \<Phi>'"
  assumes "[], n \<Turnstile> [] \<triangleright> \<Phi>"
  assumes "[], n \<Turnstile> [] \<triangleright> \<Phi>'"
  shows "[], n \<Turnstile> [] \<triangleright> \<Phi> @ \<Phi>'"
  sorry

lemma prolongation:
  assumes "n' > n"
  and "set \<Gamma>' \<supseteq> set \<Gamma>"
  and "set \<Phi>' \<subseteq> set \<Phi>"
  assumes "\<Gamma>', n' \<Turnstile> [] \<triangleright> \<Phi>' \<Longrightarrow> \<Gamma>, n \<Turnstile> [] \<triangleright> \<Phi>"
  shows "\<lbrakk>\<lbrakk> \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L \<inter> \<lbrakk>\<lbrakk> \<Gamma> \<rbrakk>\<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n \<supseteq> \<lbrakk>\<lbrakk> \<Phi>' \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L \<inter> \<lbrakk>\<lbrakk> \<Gamma>' \<rbrakk>\<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n"
  sorry

lemma prolongation_and_composition:
  assumes "n' > n"
  assumes "\<Gamma>', n' \<Turnstile> [] \<triangleright> (\<Phi> @ \<Psi>) \<Longrightarrow> \<Gamma>, n \<Turnstile> [] \<triangleright> (\<Phi>' @ \<Psi>')"
  shows "\<lbrakk>\<lbrakk> \<Phi> @ \<Psi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L \<subseteq> \<lbrakk>\<lbrakk> \<Phi>' @ \<Psi>' \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L"
  sorry

end