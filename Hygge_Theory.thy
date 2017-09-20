theory Hygge_Theory
imports
  "Hygge"
  "Denotational"

begin

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

text \<open>Each reduction step produces a more refined run\<close>
lemma refinement_at_each_step:
  assumes "\<Gamma>\<^sub>1, n\<^sub>1 \<turnstile> \<Psi>\<^sub>1 \<triangleright> \<Phi>\<^sub>1 \<hookrightarrow> \<Gamma>\<^sub>2, n\<^sub>2 \<turnstile> \<Psi>\<^sub>2 \<triangleright> \<Phi>\<^sub>2"
  shows "\<lbrakk>\<lbrakk> \<Gamma>\<^sub>1 \<rbrakk>\<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n \<supseteq> \<lbrakk>\<lbrakk> \<Gamma>\<^sub>2 \<rbrakk>\<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n"
  by (insert assms, erule operational_semantics_step.cases, auto)

lemma refinement_at_each_step':
  assumes "\<Gamma>\<^sub>1, n\<^sub>1 \<turnstile> \<Psi>\<^sub>1 \<triangleright> \<Phi>\<^sub>1 \<hookrightarrow> \<Gamma>\<^sub>2, n\<^sub>2 \<turnstile> \<Psi>\<^sub>2 \<triangleright> \<Phi>\<^sub>2"
  shows "\<lbrakk>\<lbrakk> \<Gamma>\<^sub>1 \<rbrakk>\<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n \<inter> \<lbrakk>\<lbrakk> \<Phi>\<^sub>2 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L \<inter> \<lbrakk>\<lbrakk> \<Psi>\<^sub>2 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L \<supseteq> \<lbrakk>\<lbrakk> \<Gamma>\<^sub>2 \<rbrakk>\<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n \<inter> \<lbrakk>\<lbrakk> \<Phi>\<^sub>1 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L \<inter> \<lbrakk>\<lbrakk> \<Psi>\<^sub>1 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L"
  apply (insert assms, erule operational_semantics_step.cases, auto)
  using NoSporadic_idem apply fastforce
  (* nitpick *)
  sorry

lemma composition:
  assumes "K\<^sub>1 time-delayed by \<delta>\<tau> on K\<^sub>2 implies K\<^sub>3 \<notin> set \<Phi> \<union> set \<Phi>'"
  assumes "\<TTurnstile> \<Gamma>\<^sub>1, n \<turnstile> [] \<triangleright> \<Phi>\<^sub>1"
  assumes "\<TTurnstile> \<Gamma>\<^sub>2, n \<turnstile> [] \<triangleright> \<Phi>\<^sub>2"
  assumes "consistency_run (\<Gamma>\<^sub>1 @ \<Gamma>\<^sub>2)"
  shows   "\<TTurnstile> \<Gamma>\<^sub>1 @ \<Gamma>\<^sub>2, n \<turnstile> [] \<triangleright> \<Phi>\<^sub>1 @ \<Phi>\<^sub>2"
  oops

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

lemma run_index_progress:
  assumes "\<Gamma>\<^sub>1, n\<^sub>1 \<turnstile> \<Psi>\<^sub>1 \<triangleright> \<Phi>\<^sub>1  \<hookrightarrow>  \<Gamma>\<^sub>2, n\<^sub>2 \<turnstile> \<Psi>\<^sub>2 \<triangleright> \<Phi>\<^sub>2"
  shows "n\<^sub>2 = Suc n\<^sub>1 \<or> n\<^sub>2 = n\<^sub>1"
  by (insert assms, erule operational_semantics_step.cases, auto)

lemma run_index_progress_simlstep:
  assumes siml_step: "(\<Gamma>\<^sub>1, n\<^sub>1 \<turnstile> \<Psi>\<^sub>1 \<triangleright> \<Phi>\<^sub>1, \<Gamma>\<^sub>2, n\<^sub>2 \<turnstile> \<Psi>\<^sub>2 \<triangleright> \<Phi>\<^sub>2) \<in> \<hookrightarrow>\<^sup>\<nabla>"
  shows "n\<^sub>2 = Suc n\<^sub>1"
  sorry

lemma run_preservation_bounded:
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
oops

lemma run_composition:
  assumes "\<Gamma>, n \<turnstile> \<Psi>\<^sub>1 \<triangleright> (\<Phi>\<^sub>1 @ \<Phi>\<^sub>2)  \<hookrightarrow>  \<Gamma>', n' \<turnstile> \<Psi>\<^sub>2 \<triangleright> (\<Phi>\<^sub>1' @ \<Phi>\<^sub>2')"
  shows "\<lbrakk>\<lbrakk> \<Phi>\<^sub>1 @ \<Phi>\<^sub>2 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L = \<lbrakk>\<lbrakk> \<Phi>\<^sub>1' @ \<Phi>\<^sub>2' \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L"
  apply (insert assms, erule operational_semantics_step.cases, auto)
  apply (metis (no_types, lifting) NoSporadic_stable filter_append set_mp)
  (* nitpick *)
  sorry

(**) section \<open>Run existence for TESL arithmetic-consistent formulae\<close> (**)
fun tagrel_consistent :: "TESL_formula \<Rightarrow> bool" where
  "tagrel_consistent \<Phi> = undefined"

lemma existence:
  (* Assumption that the linear system made of tag relations is consistent *)
  assumes "tagrel_consistent \<Phi>"
  shows "\<exists>\<rho>. \<rho> \<in> \<lbrakk>\<lbrakk> \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L"
oops
(* proof (induction \<Phi>) *)

(* OPERATIONAL \<longrightarrow> DENOTATIONAL *)
(* A chaque pas de simulation, les runs dérivés préfixent les runs dénotationels *)
theorem soundness:
  assumes "\<Gamma>\<^sub>1, n\<^sub>1 \<turnstile> \<Psi>\<^sub>1 \<triangleright> \<Phi>\<^sub>1  \<hookrightarrow>  \<Gamma>\<^sub>2, n\<^sub>2 \<turnstile> \<Psi>\<^sub>2 \<triangleright> \<Phi>\<^sub>2"
  shows "\<forall>\<rho>\<^sub>o\<^sub>p \<in> \<lbrakk>\<lbrakk> \<Gamma>\<^sub>2 \<rbrakk>\<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n. \<exists>\<rho>\<^sub>d\<^sub>e\<^sub>n \<in> \<lbrakk>\<lbrakk> \<Phi>\<^sub>1 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L.
          \<rho>\<^sub>o\<^sub>p \<sqsubseteq>\<^sup>p\<^sup>r\<^sup>e\<^sup>f\<^sup>i\<^sup>x\<^bsub>n\<^sub>2\<^esub> \<rho>\<^sub>d\<^sub>e\<^sub>n"
  oops
  (* by (insert assms, erule operational_semantics_step.cases, auto) *)

(* DENOTATIONAL \<longrightarrow> OPERATIONAL *)
(* A chaque pas de simulation, un run dénoté préfixe un run dérivé opérationallement *)
theorem completeness:
  assumes "\<Gamma>\<^sub>1, n\<^sub>1 \<turnstile> \<Psi>\<^sub>1 \<triangleright> \<Phi>\<^sub>1 \<hookrightarrow> \<Gamma>\<^sub>2, n\<^sub>2 \<turnstile> \<Psi>\<^sub>2 \<triangleright> \<Phi>\<^sub>2"
  shows "\<forall>\<rho>\<^sub>d\<^sub>e\<^sub>n \<in> \<lbrakk>\<lbrakk> \<Phi>\<^sub>1 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L \<inter> \<lbrakk>\<lbrakk> \<Gamma>\<^sub>1 \<rbrakk>\<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n. \<exists>\<rho>\<^sub>o\<^sub>p \<in> \<lbrakk>\<lbrakk> \<Gamma>\<^sub>2 \<rbrakk>\<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n.
          \<rho>\<^sub>d\<^sub>e\<^sub>n \<sqsubseteq>\<^sup>p\<^sup>r\<^sup>e\<^sup>f\<^sup>i\<^sup>x\<^bsub>n\<^sub>2\<^esub> \<rho>\<^sub>o\<^sub>p"
  oops
  (* by (insert assms, erule operational_semantics_step.cases, auto) *)

end