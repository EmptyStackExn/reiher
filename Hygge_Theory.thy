theory Hygge_Theory
imports
  "Hygge"
  "Denotational"

begin

fun HeronConf_interpretation :: "config \<Rightarrow> run set" ("\<lbrakk> _ \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f" 71) where
  "\<lbrakk> \<Gamma>, n \<turnstile> \<Psi> \<triangleright> \<Phi> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f = \<lbrakk>\<lbrakk> \<Gamma> \<rbrakk>\<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n \<inter> \<lbrakk>\<lbrakk> \<Psi> \<nabla> n \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L \<inter> \<lbrakk>\<lbrakk> \<Phi> \<nabla> Suc n \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L"

(* To start solving specification [\<Psi>], we start at configuration [], 0 \<turnstile> \<Psi> \<triangleright> [] *)
lemma solve_start:
  shows "\<lbrakk>\<lbrakk> \<Psi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L = \<lbrakk> [], 0 \<turnstile> \<Psi> \<triangleright> [] \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f"
  proof -
    have "\<lbrakk>\<lbrakk> \<Psi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L = \<lbrakk>\<lbrakk> \<Psi> \<nabla> 0 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L"
    by (simp add: TESL_interpretation_at_index_zero')
    moreover have "\<lbrakk> [], 0 \<turnstile> \<Psi> \<triangleright> [] \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f = \<lbrakk>\<lbrakk> [] \<rbrakk>\<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n \<inter> \<lbrakk>\<lbrakk> \<Psi> \<nabla> 0 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L \<inter> \<lbrakk>\<lbrakk> [] \<nabla> Suc 0 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L"
    by simp
    ultimately show ?thesis by auto
  qed

(**) section \<open>Soundness\<close> (**)

theorem soundness:
  assumes "\<Gamma>\<^sub>1, n\<^sub>1 \<turnstile> \<Psi>\<^sub>1 \<triangleright> \<Phi>\<^sub>1  \<hookrightarrow>  \<Gamma>\<^sub>2, n\<^sub>2 \<turnstile> \<Psi>\<^sub>2 \<triangleright> \<Phi>\<^sub>2"
  shows "\<lbrakk>\<lbrakk> \<Gamma>\<^sub>1 \<rbrakk>\<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n \<inter> \<lbrakk>\<lbrakk> \<Psi>\<^sub>1 \<nabla> n\<^sub>1 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L \<inter> \<lbrakk>\<lbrakk> \<Phi>\<^sub>1 \<nabla> Suc n\<^sub>1 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L
          \<supseteq>  \<lbrakk>\<lbrakk> \<Gamma>\<^sub>2 \<rbrakk>\<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n \<inter> \<lbrakk>\<lbrakk> \<Psi>\<^sub>2 \<nabla> n\<^sub>2 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L \<inter> \<lbrakk>\<lbrakk> \<Phi>\<^sub>2 \<nabla> Suc n\<^sub>2 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L"
  proof (insert assms, erule operational_semantics_step.cases)
  show "\<And>\<Gamma> n \<Phi>.
       (\<Gamma>\<^sub>1, n\<^sub>1 \<turnstile> \<Psi>\<^sub>1 \<triangleright> \<Phi>\<^sub>1) = (\<Gamma>, n \<turnstile> [] \<triangleright> \<Phi>) \<Longrightarrow>
       (\<Gamma>\<^sub>2, n\<^sub>2 \<turnstile> \<Psi>\<^sub>2 \<triangleright> \<Phi>\<^sub>2) = (\<Gamma>, Suc n \<turnstile> \<Phi> \<triangleright> []) \<Longrightarrow>
       consistent_run \<Gamma> \<Longrightarrow>
       \<lbrakk>\<lbrakk> \<Gamma>\<^sub>2 \<rbrakk>\<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n \<inter> \<lbrakk>\<lbrakk> \<Psi>\<^sub>2 \<nabla> n\<^sub>2 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L \<inter> \<lbrakk>\<lbrakk> \<Phi>\<^sub>2 \<nabla> Suc n\<^sub>2 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L \<subseteq> \<lbrakk>\<lbrakk> \<Gamma>\<^sub>1 \<rbrakk>\<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n \<inter> \<lbrakk>\<lbrakk> \<Psi>\<^sub>1 \<nabla> n\<^sub>1 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L \<inter> \<lbrakk>\<lbrakk> \<Phi>\<^sub>1 \<nabla> Suc n\<^sub>1 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L"
    by auto
  show "\<And>\<Gamma> n K \<tau> \<Psi> \<Phi>.
       (\<Gamma>\<^sub>1, n\<^sub>1 \<turnstile> \<Psi>\<^sub>1 \<triangleright> \<Phi>\<^sub>1) = (\<Gamma>, n \<turnstile> (K sporadic \<tau>) # \<Psi> \<triangleright> \<Phi>) \<Longrightarrow>
       (\<Gamma>\<^sub>2, n\<^sub>2 \<turnstile> \<Psi>\<^sub>2 \<triangleright> \<Phi>\<^sub>2) = (\<Gamma>, n \<turnstile> \<Psi> \<triangleright> (K sporadic \<tau>) # \<Phi>) \<Longrightarrow>
       consistent_run \<Gamma> \<Longrightarrow>
       \<lbrakk>\<lbrakk> \<Gamma>\<^sub>2 \<rbrakk>\<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n \<inter> \<lbrakk>\<lbrakk> \<Psi>\<^sub>2 \<nabla> n\<^sub>2 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L \<inter> \<lbrakk>\<lbrakk> \<Phi>\<^sub>2 \<nabla> Suc n\<^sub>2 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L \<subseteq> \<lbrakk>\<lbrakk> \<Gamma>\<^sub>1 \<rbrakk>\<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n \<inter> \<lbrakk>\<lbrakk> \<Psi>\<^sub>1 \<nabla> n\<^sub>1 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L \<inter> \<lbrakk>\<lbrakk> \<Phi>\<^sub>1 \<nabla> Suc n\<^sub>1 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L"
    using TESL_interp_at_index_sporadic_cases
    by (smt Int_subset_iff Pair_inject TESL_interpretation_at_index_cons_morph inf.cobounded1 inf.cobounded2 subset_trans sup.cobounded2)
  show "\<And>K n \<tau> \<Gamma> \<Psi> \<Phi>.
       (\<Gamma>\<^sub>1, n\<^sub>1 \<turnstile> \<Psi>\<^sub>1 \<triangleright> \<Phi>\<^sub>1) = (\<Gamma>, n \<turnstile> (K sporadic \<tau>) # \<Psi> \<triangleright> \<Phi>) \<Longrightarrow>
       (\<Gamma>\<^sub>2, n\<^sub>2 \<turnstile> \<Psi>\<^sub>2 \<triangleright> \<Phi>\<^sub>2) = (K \<Up> n # K \<Down> n @ \<lfloor> \<tau> \<rfloor> # \<Gamma>, n \<turnstile> \<Psi> \<triangleright> \<Phi>) \<Longrightarrow>
       consistent_run (K \<Up> n # K \<Down> n @ \<lfloor> \<tau> \<rfloor> # \<Gamma>) \<Longrightarrow>
       \<lbrakk>\<lbrakk> \<Gamma>\<^sub>2 \<rbrakk>\<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n \<inter> \<lbrakk>\<lbrakk> \<Psi>\<^sub>2 \<nabla> n\<^sub>2 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L \<inter> \<lbrakk>\<lbrakk> \<Phi>\<^sub>2 \<nabla> Suc n\<^sub>2 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L \<subseteq> \<lbrakk>\<lbrakk> \<Gamma>\<^sub>1 \<rbrakk>\<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n \<inter> \<lbrakk>\<lbrakk> \<Psi>\<^sub>1 \<nabla> n\<^sub>1 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L \<inter> \<lbrakk>\<lbrakk> \<Phi>\<^sub>1 \<nabla> Suc n\<^sub>1 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L"
    using TESL_interp_at_index_sporadic_cases
  proof -
    fix K :: clock and n :: nat and \<tau> :: tag_const and \<Gamma> :: "constr list" and \<Psi> :: "TESL_atomic list" and \<Phi> :: "TESL_atomic list"
    assume a1: "(\<Gamma>\<^sub>2, n\<^sub>2 \<turnstile> \<Psi>\<^sub>2 \<triangleright> \<Phi>\<^sub>2) = (K \<Up> n # K \<Down> n @ \<lfloor> \<tau> \<rfloor> # \<Gamma>, n \<turnstile> \<Psi> \<triangleright> \<Phi>)"
    assume a2: "(\<Gamma>\<^sub>1, n\<^sub>1 \<turnstile> \<Psi>\<^sub>1 \<triangleright> \<Phi>\<^sub>1) = (\<Gamma>, n \<turnstile> (K sporadic \<tau>) # \<Psi> \<triangleright> \<Phi>)"
    have f3: "\<lbrakk> K \<Up> n \<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n \<inter> (\<lbrakk> K \<Down> n @ \<lfloor> \<tau> \<rfloor> \<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n \<inter> \<lbrakk>\<lbrakk> \<Gamma> \<rbrakk>\<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n) = \<lbrakk>\<lbrakk> \<Gamma>\<^sub>2 \<rbrakk>\<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n"
      using a1 by force
    have "(\<lbrakk> K \<Up> n \<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n \<inter> \<lbrakk> K \<Down> n @ \<lfloor> \<tau> \<rfloor> \<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n \<union> \<lbrakk> K sporadic \<tau> \<nabla> Suc n \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L) \<inter> \<lbrakk>\<lbrakk> \<Psi>\<^sub>2 \<nabla> n\<^sub>2 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L = \<lbrakk>\<lbrakk> \<Psi>\<^sub>1 \<nabla> n\<^sub>1 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L"
      using a2 a1 by (metis (no_types) Pair_inject TESL_interp_at_index_sporadic_cases TESL_interpretation_at_index_cons_morph)
    then show "\<lbrakk>\<lbrakk> \<Gamma>\<^sub>2 \<rbrakk>\<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n \<inter> \<lbrakk>\<lbrakk> \<Psi>\<^sub>2 \<nabla> n\<^sub>2 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L \<inter> \<lbrakk>\<lbrakk> \<Phi>\<^sub>2 \<nabla> Suc n\<^sub>2 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L \<subseteq> \<lbrakk>\<lbrakk> \<Gamma>\<^sub>1 \<rbrakk>\<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n \<inter> \<lbrakk>\<lbrakk> \<Psi>\<^sub>1 \<nabla> n\<^sub>1 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L \<inter> \<lbrakk>\<lbrakk> \<Phi>\<^sub>1 \<nabla> Suc n\<^sub>1 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L"
      using f3 a2 a1 by blast
  qed
  show "\<And>\<Gamma> n K\<^sub>1 \<tau> K\<^sub>2 \<Psi> \<Phi>.
       (\<Gamma>\<^sub>1, n\<^sub>1 \<turnstile> \<Psi>\<^sub>1 \<triangleright> \<Phi>\<^sub>1) = (\<Gamma>, n \<turnstile> (K\<^sub>1 sporadic \<tau> on K\<^sub>2) # \<Psi> \<triangleright> \<Phi>) \<Longrightarrow>
       (\<Gamma>\<^sub>2, n\<^sub>2 \<turnstile> \<Psi>\<^sub>2 \<triangleright> \<Phi>\<^sub>2) = (\<Gamma>, n \<turnstile> \<Psi> \<triangleright> (K\<^sub>1 sporadic \<tau> on K\<^sub>2) # \<Phi>) \<Longrightarrow>
       consistent_run \<Gamma> \<Longrightarrow>
       \<lbrakk>\<lbrakk> \<Gamma>\<^sub>2 \<rbrakk>\<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n \<inter> \<lbrakk>\<lbrakk> \<Psi>\<^sub>2 \<nabla> n\<^sub>2 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L \<inter> \<lbrakk>\<lbrakk> \<Phi>\<^sub>2 \<nabla> Suc n\<^sub>2 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L \<subseteq> \<lbrakk>\<lbrakk> \<Gamma>\<^sub>1 \<rbrakk>\<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n \<inter> \<lbrakk>\<lbrakk> \<Psi>\<^sub>1 \<nabla> n\<^sub>1 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L \<inter> \<lbrakk>\<lbrakk> \<Phi>\<^sub>1 \<nabla> Suc n\<^sub>1 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L"
    using TESL_interp_at_index_sporadicon_cases
    proof -
    fix \<Gamma> :: "constr list" and n :: nat and K\<^sub>1 :: clock and \<tau> :: tag_expr and K\<^sub>2 :: clock and \<Psi> :: "TESL_atomic list" and \<Phi> :: "TESL_atomic list"
    assume a1: "(\<Gamma>\<^sub>1, n\<^sub>1 \<turnstile> \<Psi>\<^sub>1 \<triangleright> \<Phi>\<^sub>1) = (\<Gamma>, n \<turnstile> (K\<^sub>1 sporadic \<tau> on K\<^sub>2) # \<Psi> \<triangleright> \<Phi>)"
    assume a2: "(\<Gamma>\<^sub>2, n\<^sub>2 \<turnstile> \<Psi>\<^sub>2 \<triangleright> \<Phi>\<^sub>2) = (\<Gamma>, n \<turnstile> \<Psi> \<triangleright> (K\<^sub>1 sporadic \<tau> on K\<^sub>2) # \<Phi>)"
    have "n\<^sub>1 = n \<and> (\<Psi>\<^sub>1, \<Phi>\<^sub>1) = ((K\<^sub>1 sporadic \<tau> on K\<^sub>2) # \<Psi>, \<Phi>)"
      using a1 by fastforce
    then have f3: "\<lbrakk> K\<^sub>1 sporadic \<tau> on K\<^sub>2 \<nabla> Suc n\<^sub>1 \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L \<subseteq> \<lbrakk> K\<^sub>1 sporadic \<tau> on K\<^sub>2 \<nabla> n \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L"
      using TESL_interp_at_index_sporadicon_cases by blast
    have f4: "\<lbrakk> K\<^sub>1 sporadic \<tau> on K\<^sub>2 \<nabla> Suc n\<^sub>1 \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L \<inter> \<lbrakk>\<lbrakk> \<Phi>\<^sub>1 \<nabla> Suc n\<^sub>1 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L = \<lbrakk>\<lbrakk> \<Phi>\<^sub>2 \<nabla> Suc n\<^sub>2 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L"
      using a2 a1 by force
    have "\<lbrakk> K\<^sub>1 sporadic \<tau> on K\<^sub>2 \<nabla> n \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L \<inter> \<lbrakk>\<lbrakk> \<Psi>\<^sub>2 \<nabla> n\<^sub>2 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L = \<lbrakk>\<lbrakk> \<Psi>\<^sub>1 \<nabla> n\<^sub>1 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L"
      using a2 a1 by force
    then show "\<lbrakk>\<lbrakk> \<Gamma>\<^sub>2 \<rbrakk>\<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n \<inter> \<lbrakk>\<lbrakk> \<Psi>\<^sub>2 \<nabla> n\<^sub>2 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L \<inter> \<lbrakk>\<lbrakk> \<Phi>\<^sub>2 \<nabla> Suc n\<^sub>2 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L \<subseteq> \<lbrakk>\<lbrakk> \<Gamma>\<^sub>1 \<rbrakk>\<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n \<inter> \<lbrakk>\<lbrakk> \<Psi>\<^sub>1 \<nabla> n\<^sub>1 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L \<inter> \<lbrakk>\<lbrakk> \<Phi>\<^sub>1 \<nabla> Suc n\<^sub>1 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L"
      using f4 f3 a2 a1 by blast
  qed
  show "\<And>K\<^sub>1 n K\<^sub>2 \<tau> \<Gamma> \<Psi> \<Phi>.
       (\<Gamma>\<^sub>1, n\<^sub>1 \<turnstile> \<Psi>\<^sub>1 \<triangleright> \<Phi>\<^sub>1) = (\<Gamma>, n \<turnstile> (K\<^sub>1 sporadic \<tau> on K\<^sub>2) # \<Psi> \<triangleright> \<Phi>) \<Longrightarrow>
       (\<Gamma>\<^sub>2, n\<^sub>2 \<turnstile> \<Psi>\<^sub>2 \<triangleright> \<Phi>\<^sub>2) = (K\<^sub>1 \<Up> n # K\<^sub>2 \<Down> n @ \<tau> # \<Gamma>, n \<turnstile> \<Psi> \<triangleright> \<Phi>) \<Longrightarrow>
       consistent_run (K\<^sub>1 \<Up> n # K\<^sub>2 \<Down> n @ \<tau> # \<Gamma>) \<Longrightarrow>
       \<lbrakk>\<lbrakk> \<Gamma>\<^sub>2 \<rbrakk>\<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n \<inter> \<lbrakk>\<lbrakk> \<Psi>\<^sub>2 \<nabla> n\<^sub>2 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L \<inter> \<lbrakk>\<lbrakk> \<Phi>\<^sub>2 \<nabla> Suc n\<^sub>2 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L \<subseteq> \<lbrakk>\<lbrakk> \<Gamma>\<^sub>1 \<rbrakk>\<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n \<inter> \<lbrakk>\<lbrakk> \<Psi>\<^sub>1 \<nabla> n\<^sub>1 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L \<inter> \<lbrakk>\<lbrakk> \<Phi>\<^sub>1 \<nabla> Suc n\<^sub>1 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L"
    using TESL_interp_at_index_sporadicon_cases
    proof -
    fix K\<^sub>1 :: clock and n :: nat and K\<^sub>2 :: clock and \<tau> :: tag_expr and \<Gamma> :: "constr list" and \<Psi> :: "TESL_atomic list" and \<Phi> :: "TESL_atomic list"
    assume a1: "(\<Gamma>\<^sub>1, n\<^sub>1 \<turnstile> \<Psi>\<^sub>1 \<triangleright> \<Phi>\<^sub>1) = (\<Gamma>, n \<turnstile> (K\<^sub>1 sporadic \<tau> on K\<^sub>2) # \<Psi> \<triangleright> \<Phi>)"
    assume a2: "(\<Gamma>\<^sub>2, n\<^sub>2 \<turnstile> \<Psi>\<^sub>2 \<triangleright> \<Phi>\<^sub>2) = (K\<^sub>1 \<Up> n # K\<^sub>2 \<Down> n @ \<tau> # \<Gamma>, n \<turnstile> \<Psi> \<triangleright> \<Phi>)"
    then have f3: "\<lbrakk>\<lbrakk> \<Gamma>\<^sub>1 \<rbrakk>\<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n \<inter> (\<lbrakk>\<lbrakk> \<Gamma>\<^sub>2 \<rbrakk>\<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n \<inter> (\<lbrakk>\<lbrakk> \<Psi>\<^sub>2 \<nabla> n\<^sub>2 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L \<inter> \<lbrakk>\<lbrakk> \<Phi>\<^sub>2 \<nabla> Suc n\<^sub>2 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L)) \<subseteq> (\<Inter>t\<in>set \<Psi>\<^sub>2. \<lbrakk> t \<nabla> n\<^sub>2 \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L) \<inter> (\<lbrakk>\<lbrakk> \<Gamma>\<^sub>1 \<rbrakk>\<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n \<inter> (\<Inter>t\<in>set \<Phi>\<^sub>1. \<lbrakk> t \<nabla> Suc n\<^sub>1 \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L))"
    using a1 TESL_interpretation_at_index_fixpoint by force
    have f4: "\<lbrakk> K\<^sub>1 \<Up> n \<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n \<inter> (\<lbrakk> K\<^sub>2 \<Down> n @ \<tau> \<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n \<inter> \<lbrakk> K\<^sub>2 \<Down> n @ \<tau> \<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n) \<inter> (\<lbrakk>\<lbrakk> \<Gamma>\<^sub>1 \<rbrakk>\<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n \<inter> (\<lbrakk>\<lbrakk> \<Gamma>\<^sub>2 \<rbrakk>\<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n \<inter> (\<lbrakk>\<lbrakk> \<Psi>\<^sub>2 \<nabla> n\<^sub>2 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L \<inter> \<lbrakk>\<lbrakk> \<Phi>\<^sub>2 \<nabla> Suc n\<^sub>2 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L))) = \<lbrakk>\<lbrakk> \<Gamma>\<^sub>2 \<rbrakk>\<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n \<inter> (\<lbrakk>\<lbrakk> \<Psi>\<^sub>2 \<nabla> n\<^sub>2 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L \<inter> \<lbrakk>\<lbrakk> \<Phi>\<^sub>2 \<nabla> Suc n\<^sub>2 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L)"
      using a2 a1 by force
    have "\<lbrakk> K\<^sub>1 sporadic \<tau> on K\<^sub>2 \<nabla> n \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L \<inter> (\<Inter>t\<in>set \<Psi>\<^sub>2. \<lbrakk> t \<nabla> n\<^sub>2 \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L) \<inter> (\<lbrakk>\<lbrakk> \<Gamma>\<^sub>1 \<rbrakk>\<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n \<inter> (\<Inter>t\<in>set \<Phi>\<^sub>1. \<lbrakk> t \<nabla> Suc n\<^sub>1 \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L)) = (\<Inter>t\<in>set \<Psi>\<^sub>1. \<lbrakk> t \<nabla> n\<^sub>1 \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L) \<inter> (\<lbrakk>\<lbrakk> \<Gamma>\<^sub>1 \<rbrakk>\<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n \<inter> (\<lbrakk>\<lbrakk> \<Gamma>\<^sub>1 \<rbrakk>\<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n \<inter> (\<Inter>t\<in>set \<Phi>\<^sub>1. \<lbrakk> t \<nabla> Suc n\<^sub>1 \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L)))"
      using a2 a1 by simp
    then have "(\<lbrakk> K\<^sub>1 \<Up> n \<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n \<inter> \<lbrakk> K\<^sub>2 \<Down> n @ \<tau> \<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n \<union> \<lbrakk> K\<^sub>1 sporadic \<tau> on K\<^sub>2 \<nabla> Suc n \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L) \<inter> ((\<Inter>t\<in>set \<Psi>\<^sub>2. \<lbrakk> t \<nabla> n\<^sub>2 \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L) \<inter> (\<lbrakk>\<lbrakk> \<Gamma>\<^sub>1 \<rbrakk>\<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n \<inter> (\<Inter>t\<in>set \<Phi>\<^sub>1. \<lbrakk> t \<nabla> Suc n\<^sub>1 \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L))) = \<lbrakk>\<lbrakk> \<Gamma>\<^sub>1 \<rbrakk>\<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n \<inter> (\<lbrakk>\<lbrakk> \<Psi>\<^sub>1 \<nabla> n\<^sub>1 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L \<inter> \<lbrakk>\<lbrakk> \<Phi>\<^sub>1 \<nabla> Suc n\<^sub>1 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L)"
      by (metis Int_absorb TESL_interp_at_index_sporadicon_cases TESL_interpretation_at_index_fixpoint inf_aci(2) inf_left_commute)
    then show "\<lbrakk>\<lbrakk> \<Gamma>\<^sub>2 \<rbrakk>\<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n \<inter> \<lbrakk>\<lbrakk> \<Psi>\<^sub>2 \<nabla> n\<^sub>2 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L \<inter> \<lbrakk>\<lbrakk> \<Phi>\<^sub>2 \<nabla> Suc n\<^sub>2 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L \<subseteq> \<lbrakk>\<lbrakk> \<Gamma>\<^sub>1 \<rbrakk>\<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n \<inter> \<lbrakk>\<lbrakk> \<Psi>\<^sub>1 \<nabla> n\<^sub>1 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L \<inter> \<lbrakk>\<lbrakk> \<Phi>\<^sub>1 \<nabla> Suc n\<^sub>1 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L"
      using f4 f3 by blast
  qed
  show "\<And>K\<^sub>1 n \<alpha> K\<^sub>2 \<beta> \<Gamma> \<Psi> \<Phi>.
       (\<Gamma>\<^sub>1, n\<^sub>1 \<turnstile> \<Psi>\<^sub>1 \<triangleright> \<Phi>\<^sub>1) = (\<Gamma>, n \<turnstile> (tag-relation K\<^sub>1 = \<alpha> * K\<^sub>2 + \<beta>) # \<Psi> \<triangleright> \<Phi>) \<Longrightarrow>
       (\<Gamma>\<^sub>2, n\<^sub>2 \<turnstile> \<Psi>\<^sub>2 \<triangleright> \<Phi>\<^sub>2) = (\<tau>\<^sub>v\<^sub>a\<^sub>r (K\<^sub>1, n) \<doteq> \<alpha> * \<tau>\<^sub>v\<^sub>a\<^sub>r (K\<^sub>2, n) + \<beta> # \<Gamma>, n \<turnstile> \<Psi> \<triangleright> (tag-relation K\<^sub>1 = \<alpha> * K\<^sub>2 + \<beta>) # \<Phi>) \<Longrightarrow>
       consistent_run (\<tau>\<^sub>v\<^sub>a\<^sub>r (K\<^sub>1, n) \<doteq> \<alpha> * \<tau>\<^sub>v\<^sub>a\<^sub>r (K\<^sub>2, n) + \<beta> # \<Gamma>) \<Longrightarrow>
       \<lbrakk>\<lbrakk> \<Gamma>\<^sub>2 \<rbrakk>\<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n \<inter> \<lbrakk>\<lbrakk> \<Psi>\<^sub>2 \<nabla> n\<^sub>2 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L \<inter> \<lbrakk>\<lbrakk> \<Phi>\<^sub>2 \<nabla> Suc n\<^sub>2 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L \<subseteq> \<lbrakk>\<lbrakk> \<Gamma>\<^sub>1 \<rbrakk>\<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n \<inter> \<lbrakk>\<lbrakk> \<Psi>\<^sub>1 \<nabla> n\<^sub>1 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L \<inter> \<lbrakk>\<lbrakk> \<Phi>\<^sub>1 \<nabla> Suc n\<^sub>1 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L"
    using TESL_interp_at_index_tagrel_cases
    proof -
      fix K\<^sub>1 :: clock and n :: nat and \<alpha> :: tag_const and K\<^sub>2 :: clock and \<beta> :: tag_const and \<Gamma> :: "constr list" and \<Psi> :: "TESL_atomic list" and \<Phi> :: "TESL_atomic list"
    assume a1: "(\<Gamma>\<^sub>2, n\<^sub>2 \<turnstile> \<Psi>\<^sub>2 \<triangleright> \<Phi>\<^sub>2) = (\<tau>\<^sub>v\<^sub>a\<^sub>r (K\<^sub>1, n) \<doteq> \<alpha> * \<tau>\<^sub>v\<^sub>a\<^sub>r (K\<^sub>2, n) + \<beta> # \<Gamma>, n \<turnstile> \<Psi> \<triangleright> (tag-relation K\<^sub>1 = \<alpha> * K\<^sub>2 + \<beta>) # \<Phi>)"
    assume a2: "(\<Gamma>\<^sub>1, n\<^sub>1 \<turnstile> \<Psi>\<^sub>1 \<triangleright> \<Phi>\<^sub>1) = (\<Gamma>, n \<turnstile> (tag-relation K\<^sub>1 = \<alpha> * K\<^sub>2 + \<beta>) # \<Psi> \<triangleright> \<Phi>)"
    have f3: "\<forall>ts tsa tsb tsc. (ts::TESL_atomic list, tsa::TESL_atomic list) \<noteq> (tsb, tsc) \<or> ts = tsb \<and> tsa = tsc"
      by fastforce
    have f4: "n\<^sub>2 = n \<and> (\<Psi>\<^sub>2, \<Phi>\<^sub>2) = (\<Psi>, (tag-relation K\<^sub>1 = \<alpha> * K\<^sub>2 + \<beta>) # \<Phi>)"
      using a1 by fastforce
    have f5: "\<lbrakk>\<lbrakk> (tag-relation K\<^sub>1 = \<alpha> * K\<^sub>2 + \<beta>) # \<Phi> \<nabla> Suc n \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L = \<lbrakk>\<lbrakk> \<Phi>\<^sub>2 \<nabla> Suc n\<^sub>2 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L"
      using a1 by force
    have f6: "n\<^sub>1 = n \<and> (\<Psi>\<^sub>1, \<Phi>\<^sub>1) = ((tag-relation K\<^sub>1 = \<alpha> * K\<^sub>2 + \<beta>) # \<Psi>, \<Phi>)"
      using a2 by fastforce
    have f7: "\<lbrakk>\<lbrakk> \<Phi> \<nabla> Suc n \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L = \<lbrakk>\<lbrakk> \<Phi>\<^sub>1 \<nabla> Suc n\<^sub>1 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L"
      using a2 by force
    have f8: "\<lbrakk>\<lbrakk> \<tau>\<^sub>v\<^sub>a\<^sub>r (K\<^sub>1, n) \<doteq> \<alpha> * \<tau>\<^sub>v\<^sub>a\<^sub>r (K\<^sub>2, n) + \<beta> # \<Gamma> \<rbrakk>\<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n = \<lbrakk> \<tau>\<^sub>v\<^sub>a\<^sub>r (K\<^sub>1, n) \<doteq> \<alpha> * \<tau>\<^sub>v\<^sub>a\<^sub>r (K\<^sub>2, n) + \<beta> \<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n \<inter> \<lbrakk>\<lbrakk> \<Gamma>\<^sub>1 \<rbrakk>\<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n"
      using a2 by force
    have f9: "\<lbrakk> tag-relation K\<^sub>1 = \<alpha> * K\<^sub>2 + \<beta> \<nabla> Suc n \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L \<inter> (\<lbrakk>\<lbrakk> \<Psi>\<^sub>2 \<nabla> n\<^sub>2 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L \<inter> \<lbrakk> \<tau>\<^sub>v\<^sub>a\<^sub>r (K\<^sub>1, n) \<doteq> \<alpha> * \<tau>\<^sub>v\<^sub>a\<^sub>r (K\<^sub>2, n) + \<beta> \<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n) = \<lbrakk>\<lbrakk> \<Psi>\<^sub>1 \<nabla> n\<^sub>1 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L"
      using f6 f4 f3 by (metis Int_commute TESL_interp_at_index_tagrel_cases TESL_interpretation_at_index_cons_morph inf_sup_aci(3))
    have "\<lbrakk> tag-relation K\<^sub>1 = \<alpha> * K\<^sub>2 + \<beta> \<nabla> Suc n \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L \<inter> \<lbrakk>\<lbrakk> \<Phi>\<^sub>1 \<nabla> Suc n\<^sub>1 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L = \<lbrakk>\<lbrakk> \<Phi>\<^sub>2 \<nabla> Suc n\<^sub>2 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L"
      using f7 f5 by simp
    then show "\<lbrakk>\<lbrakk> \<Gamma>\<^sub>2 \<rbrakk>\<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n \<inter> \<lbrakk>\<lbrakk> \<Psi>\<^sub>2 \<nabla> n\<^sub>2 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L \<inter> \<lbrakk>\<lbrakk> \<Phi>\<^sub>2 \<nabla> Suc n\<^sub>2 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L \<subseteq> \<lbrakk>\<lbrakk> \<Gamma>\<^sub>1 \<rbrakk>\<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n \<inter> \<lbrakk>\<lbrakk> \<Psi>\<^sub>1 \<nabla> n\<^sub>1 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L \<inter> \<lbrakk>\<lbrakk> \<Phi>\<^sub>1 \<nabla> Suc n\<^sub>1 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L"
      using f9 f8 a1 by blast
  qed
  show "\<And>K\<^sub>1 n \<Gamma> K\<^sub>2 \<Psi> \<Phi>.
       (\<Gamma>\<^sub>1, n\<^sub>1 \<turnstile> \<Psi>\<^sub>1 \<triangleright> \<Phi>\<^sub>1) = (\<Gamma>, n \<turnstile> (K\<^sub>1 implies K\<^sub>2) # \<Psi> \<triangleright> \<Phi>) \<Longrightarrow>
       (\<Gamma>\<^sub>2, n\<^sub>2 \<turnstile> \<Psi>\<^sub>2 \<triangleright> \<Phi>\<^sub>2) = (K\<^sub>1 \<not>\<Up> n # \<Gamma>, n \<turnstile> \<Psi> \<triangleright> (K\<^sub>1 implies K\<^sub>2) # \<Phi>) \<Longrightarrow>
       consistent_run (K\<^sub>1 \<not>\<Up> n # \<Gamma>) \<Longrightarrow>
       \<lbrakk>\<lbrakk> \<Gamma>\<^sub>2 \<rbrakk>\<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n \<inter> \<lbrakk>\<lbrakk> \<Psi>\<^sub>2 \<nabla> n\<^sub>2 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L \<inter> \<lbrakk>\<lbrakk> \<Phi>\<^sub>2 \<nabla> Suc n\<^sub>2 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L \<subseteq> \<lbrakk>\<lbrakk> \<Gamma>\<^sub>1 \<rbrakk>\<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n \<inter> \<lbrakk>\<lbrakk> \<Psi>\<^sub>1 \<nabla> n\<^sub>1 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L \<inter> \<lbrakk>\<lbrakk> \<Phi>\<^sub>1 \<nabla> Suc n\<^sub>1 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L"
    using TESL_interp_at_index_implies_cases
    using [[smt_solver = cvc4]]
    by (smt Int_subset_iff Pair_inject TESL_interpretation_at_index.elims inf.cobounded2 inf.mono inf_sup_aci(2) list.simps(1) list.simps(3) sup.cobounded1 symbolic_run_interpretation.simps(2))
  show "\<And>K\<^sub>1 n K\<^sub>2 \<Gamma> \<Psi> \<Phi>.
       (\<Gamma>\<^sub>1, n\<^sub>1 \<turnstile> \<Psi>\<^sub>1 \<triangleright> \<Phi>\<^sub>1) = (\<Gamma>, n \<turnstile> (K\<^sub>1 implies K\<^sub>2) # \<Psi> \<triangleright> \<Phi>) \<Longrightarrow>
       (\<Gamma>\<^sub>2, n\<^sub>2 \<turnstile> \<Psi>\<^sub>2 \<triangleright> \<Phi>\<^sub>2) = (K\<^sub>1 \<Up> n # K\<^sub>2 \<Up> n # \<Gamma>, n \<turnstile> \<Psi> \<triangleright> (K\<^sub>1 implies K\<^sub>2) # \<Phi>) \<Longrightarrow>
       consistent_run (K\<^sub>1 \<Up> n # K\<^sub>2 \<Up> n # \<Gamma>) \<Longrightarrow>
       \<lbrakk>\<lbrakk> \<Gamma>\<^sub>2 \<rbrakk>\<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n \<inter> \<lbrakk>\<lbrakk> \<Psi>\<^sub>2 \<nabla> n\<^sub>2 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L \<inter> \<lbrakk>\<lbrakk> \<Phi>\<^sub>2 \<nabla> Suc n\<^sub>2 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L \<subseteq> \<lbrakk>\<lbrakk> \<Gamma>\<^sub>1 \<rbrakk>\<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n \<inter> \<lbrakk>\<lbrakk> \<Psi>\<^sub>1 \<nabla> n\<^sub>1 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L \<inter> \<lbrakk>\<lbrakk> \<Phi>\<^sub>1 \<nabla> Suc n\<^sub>1 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L"
    using TESL_interp_at_index_implies_cases
    using [[smt_solver = cvc4]]
    by (smt Int_subset_iff Pair_inject TESL_interpretation_at_index_cons_morph inf_le1 inf_sup_aci(2) le_iff_inf sup.cobounded2 symbolic_run_interpretation.simps(2))
  show "\<And>K\<^sub>1 n \<Gamma> \<delta>\<tau> K\<^sub>2 K\<^sub>3 \<Psi> \<Phi>.
       (\<Gamma>\<^sub>1, n\<^sub>1 \<turnstile> \<Psi>\<^sub>1 \<triangleright> \<Phi>\<^sub>1) = (\<Gamma>, n \<turnstile> (K\<^sub>1 time-delayed by \<delta>\<tau> on K\<^sub>2 implies K\<^sub>3) # \<Psi> \<triangleright> \<Phi>) \<Longrightarrow>
       (\<Gamma>\<^sub>2, n\<^sub>2 \<turnstile> \<Psi>\<^sub>2 \<triangleright> \<Phi>\<^sub>2) = (K\<^sub>1 \<not>\<Up> n # \<Gamma>, n \<turnstile> \<Psi> \<triangleright> (K\<^sub>1 time-delayed by \<delta>\<tau> on K\<^sub>2 implies K\<^sub>3) # \<Phi>) \<Longrightarrow>
       consistent_run (K\<^sub>1 \<not>\<Up> n # \<Gamma>) \<Longrightarrow>
       \<lbrakk>\<lbrakk> \<Gamma>\<^sub>2 \<rbrakk>\<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n \<inter> \<lbrakk>\<lbrakk> \<Psi>\<^sub>2 \<nabla> n\<^sub>2 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L \<inter> \<lbrakk>\<lbrakk> \<Phi>\<^sub>2 \<nabla> Suc n\<^sub>2 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L \<subseteq> \<lbrakk>\<lbrakk> \<Gamma>\<^sub>1 \<rbrakk>\<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n \<inter> \<lbrakk>\<lbrakk> \<Psi>\<^sub>1 \<nabla> n\<^sub>1 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L \<inter> \<lbrakk>\<lbrakk> \<Phi>\<^sub>1 \<nabla> Suc n\<^sub>1 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L"
    using TESL_interp_at_index_timedelayed_cases
    using [[smt_solver = cvc4]]
    by (smt Int_subset_iff Pair_inject TESL_interpretation_at_index_cons_morph inf.cobounded2 inf_le1 subset_trans sup.cobounded1 symbolic_run_interpretation.simps(2))
  show "\<And>K\<^sub>1 n \<Gamma> \<delta>\<tau> K\<^sub>2 K\<^sub>3 \<Psi> \<Phi>.
       (\<Gamma>\<^sub>1, n\<^sub>1 \<turnstile> \<Psi>\<^sub>1 \<triangleright> \<Phi>\<^sub>1) = (\<Gamma>, n \<turnstile> (K\<^sub>1 time-delayed by \<delta>\<tau> on K\<^sub>2 implies K\<^sub>3) # \<Psi> \<triangleright> \<Phi>) \<Longrightarrow>
       (\<Gamma>\<^sub>2, n\<^sub>2 \<turnstile> \<Psi>\<^sub>2 \<triangleright> \<Phi>\<^sub>2) = (K\<^sub>1 \<Up> n # \<Gamma>, n \<turnstile> (K\<^sub>3 sporadic \<lfloor> \<tau>\<^sub>v\<^sub>a\<^sub>r (K\<^sub>2, n) \<oplus> \<delta>\<tau> \<rfloor> on K\<^sub>2) # \<Psi> \<triangleright> (K\<^sub>1 time-delayed by \<delta>\<tau> on K\<^sub>2 implies K\<^sub>3) # \<Phi>) \<Longrightarrow>
       consistent_run (K\<^sub>1 \<Up> n # \<Gamma>) \<Longrightarrow>
       \<lbrakk>\<lbrakk> \<Gamma>\<^sub>2 \<rbrakk>\<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n \<inter> \<lbrakk>\<lbrakk> \<Psi>\<^sub>2 \<nabla> n\<^sub>2 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L \<inter> \<lbrakk>\<lbrakk> \<Phi>\<^sub>2 \<nabla> Suc n\<^sub>2 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L \<subseteq> \<lbrakk>\<lbrakk> \<Gamma>\<^sub>1 \<rbrakk>\<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n \<inter> \<lbrakk>\<lbrakk> \<Psi>\<^sub>1 \<nabla> n\<^sub>1 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L \<inter> \<lbrakk>\<lbrakk> \<Phi>\<^sub>1 \<nabla> Suc n\<^sub>1 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L"
    proof -
    fix K\<^sub>1 :: clock and n :: nat and \<Gamma> :: "constr list" and \<delta>\<tau> :: tag_const and K\<^sub>2 :: clock and K\<^sub>3 :: clock and \<Psi> :: TESL_formula and \<Phi> :: TESL_formula
    assume a1: "(\<Gamma>\<^sub>1, n\<^sub>1 \<turnstile> \<Psi>\<^sub>1 \<triangleright> \<Phi>\<^sub>1) = (\<Gamma>, n \<turnstile> (K\<^sub>1 time-delayed by \<delta>\<tau> on K\<^sub>2 implies K\<^sub>3) # \<Psi> \<triangleright> \<Phi>)"
    assume a2: "(\<Gamma>\<^sub>2, n\<^sub>2 \<turnstile> \<Psi>\<^sub>2 \<triangleright> \<Phi>\<^sub>2) = (K\<^sub>1 \<Up> n # \<Gamma>, n \<turnstile> (K\<^sub>3 sporadic \<lfloor> \<tau>\<^sub>v\<^sub>a\<^sub>r (K\<^sub>2, n) \<oplus> \<delta>\<tau> \<rfloor> on K\<^sub>2) # \<Psi> \<triangleright> (K\<^sub>1 time-delayed by \<delta>\<tau> on K\<^sub>2 implies K\<^sub>3) # \<Phi>)"
    have tdby_cases_corrollary: "\<lbrakk> K\<^sub>1 time-delayed by \<delta>\<tau> on K\<^sub>2 implies K\<^sub>3 \<nabla> n \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L \<supseteq>
        \<lbrakk> K\<^sub>1 \<Up> n \<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n \<inter> \<lbrakk> K\<^sub>3 sporadic \<lfloor>\<tau>\<^sub>v\<^sub>a\<^sub>r(K\<^sub>2, n) \<oplus> \<delta>\<tau>\<rfloor> on K\<^sub>2 \<nabla> n \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L \<inter> \<lbrakk> K\<^sub>1 time-delayed by \<delta>\<tau> on K\<^sub>2 implies K\<^sub>3 \<nabla> Suc n \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L"
      using TESL_interp_at_index_timedelayed_cases by blast
    then show "\<lbrakk>\<lbrakk> \<Gamma>\<^sub>2 \<rbrakk>\<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n \<inter> \<lbrakk>\<lbrakk> \<Psi>\<^sub>2 \<nabla> n\<^sub>2 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L \<inter> \<lbrakk>\<lbrakk> \<Phi>\<^sub>2 \<nabla> Suc n\<^sub>2 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L \<subseteq> \<lbrakk>\<lbrakk> \<Gamma>\<^sub>1 \<rbrakk>\<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n \<inter> \<lbrakk>\<lbrakk> \<Psi>\<^sub>1 \<nabla> n\<^sub>1 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L \<inter> \<lbrakk>\<lbrakk> \<Phi>\<^sub>1 \<nabla> Suc n\<^sub>1 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L"
      using a1 a2 by auto
    qed
  qed

theorem soundness':
  assumes "\<S>\<^sub>1 \<hookrightarrow> \<S>\<^sub>2"
  shows "\<lbrakk> \<S>\<^sub>1 \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f \<supseteq> \<lbrakk> \<S>\<^sub>2 \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f"
  by (metis soundness HeronConf_interpretation.elims assms)

theorem soundness_generalized:
  assumes "\<S>\<^sub>1 \<hookrightarrow>\<^bsup>n\<^esup> \<S>\<^sub>2"
  shows "\<lbrakk> \<S>\<^sub>1 \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f \<supseteq> \<lbrakk> \<S>\<^sub>2 \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f"
  proof (insert assms, induct n arbitrary: \<S>\<^sub>2)
    case 0
    then have *: "\<S>\<^sub>1 \<hookrightarrow>\<^bsup>0\<^esup> \<S>\<^sub>2 \<Longrightarrow> \<S>\<^sub>1 = \<S>\<^sub>2"
      by auto
    moreover have "\<S>\<^sub>1 = \<S>\<^sub>2" using *
      using "0.prems" by linarith
    ultimately show ?case by auto
  next
    case (Suc n)
    then show ?case
      proof -
      fix n :: nat
      assume ff: "\<S>\<^sub>1 \<hookrightarrow>\<^bsup>Suc n\<^esup> \<S>\<^sub>2"
      assume hi: "\<And>\<S>\<^sub>2. \<S>\<^sub>1 \<hookrightarrow>\<^bsup>n\<^esup> \<S>\<^sub>2 \<Longrightarrow> \<lbrakk> \<S>\<^sub>2 \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f \<subseteq> \<lbrakk> \<S>\<^sub>1 \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f"
      obtain \<S>\<^sub>n where red_decomp: "\<S>\<^sub>1 \<hookrightarrow>\<^bsup>n\<^esup> \<S>\<^sub>n \<and> \<S>\<^sub>n \<hookrightarrow> \<S>\<^sub>2"
        using ff by auto
      then have "\<lbrakk> \<S>\<^sub>1 \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f \<supseteq> \<lbrakk> \<S>\<^sub>n \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f"
        using hi by (metis (no_types, lifting) ff relpowp_Suc_E someI_ex)
      also have "\<lbrakk> \<S>\<^sub>n \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f \<supseteq> \<lbrakk> \<S>\<^sub>2 \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f"
        by (simp add: red_decomp soundness')
      ultimately show "\<lbrakk> \<S>\<^sub>1 \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f \<supseteq> \<lbrakk> \<S>\<^sub>2 \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f"
        by auto
      qed
  qed

(**) section \<open>Completeness\<close> (**)

abbreviation Fnext_solve :: "config \<Rightarrow> config set" ("\<F>\<^sub>n\<^sub>e\<^sub>x\<^sub>t _") where
  "\<F>\<^sub>n\<^sub>e\<^sub>x\<^sub>t \<S> \<equiv> { \<S>'. \<S> \<hookrightarrow> \<S>' }"

lemma Fnext_solve_instant:
  shows "\<F>\<^sub>n\<^sub>e\<^sub>x\<^sub>t (\<Gamma>, n \<turnstile> [] \<triangleright> \<Phi>)
          = { \<Gamma>, Suc n \<turnstile> \<Phi> \<triangleright> [] }"
  sorry

lemma Fnext_solve_sporadic:
  shows "\<F>\<^sub>n\<^sub>e\<^sub>x\<^sub>t (\<Gamma>, n \<turnstile> (K sporadic \<tau>) # \<Psi> \<triangleright> \<Phi>)
          = { \<Gamma>, n \<turnstile> \<Psi> \<triangleright> (K sporadic \<tau>) # \<Phi>,
              K \<Up> n # K \<Down> n @ \<lfloor>\<tau>\<rfloor> # \<Gamma>, n \<turnstile> \<Psi> \<triangleright> \<Phi> }"
  sorry

lemma Fnext_solve_sporadicon:
  shows "\<F>\<^sub>n\<^sub>e\<^sub>x\<^sub>t (\<Gamma>, n \<turnstile> (K\<^sub>1 sporadic \<tau> on K\<^sub>2) # \<Psi> \<triangleright> \<Phi>)
          = { \<Gamma>, n \<turnstile> \<Psi> \<triangleright> (K\<^sub>1 sporadic \<tau> on K\<^sub>2) # \<Phi>,
              K\<^sub>1 \<Up> n # K\<^sub>2 \<Down> n @ \<tau> # \<Gamma>, n \<turnstile> \<Psi> \<triangleright> \<Phi> }"
  sorry

lemma Fnext_solve_tagrel:
  shows "\<F>\<^sub>n\<^sub>e\<^sub>x\<^sub>t (\<Gamma>, n \<turnstile> (tag-relation K\<^sub>1 = \<alpha> * K\<^sub>2 + \<beta>) # \<Psi> \<triangleright> \<Phi>)
          = { (\<tau>\<^sub>v\<^sub>a\<^sub>r(K\<^sub>1, n) \<doteq> \<alpha> * \<tau>\<^sub>v\<^sub>a\<^sub>r(K\<^sub>2, n) + \<beta>) # \<Gamma>, n \<turnstile> \<Psi> \<triangleright> (tag-relation K\<^sub>1 = \<alpha> * K\<^sub>2 + \<beta>) # \<Phi> }"
  sorry

lemma Fnext_solve_implies:
  shows "\<F>\<^sub>n\<^sub>e\<^sub>x\<^sub>t (\<Gamma>, n \<turnstile> (K\<^sub>1 implies K\<^sub>2) # \<Psi> \<triangleright> \<Phi>)
          = { K\<^sub>1 \<not>\<Up> n # \<Gamma>, n \<turnstile> \<Psi> \<triangleright> (K\<^sub>1 implies K\<^sub>2) # \<Phi>,
              K\<^sub>1 \<Up> n # K\<^sub>2 \<Up> n # \<Gamma>, n \<turnstile> \<Psi> \<triangleright> (K\<^sub>1 implies K\<^sub>2) # \<Phi>}"
  sorry

lemma Fnext_solve_timedelayed:
  shows "\<F>\<^sub>n\<^sub>e\<^sub>x\<^sub>t (\<Gamma>, n \<turnstile> (K\<^sub>1 time-delayed by \<delta>\<tau> on K\<^sub>2 implies K\<^sub>3) # \<Psi> \<triangleright> \<Phi>)
          = { K\<^sub>1 \<not>\<Up> n # \<Gamma>, n \<turnstile> \<Psi> \<triangleright> (K\<^sub>1 time-delayed by \<delta>\<tau> on K\<^sub>2 implies K\<^sub>3) # \<Phi>,
              K\<^sub>1 \<Up> n # \<Gamma>, n \<turnstile> (K\<^sub>3 sporadic \<lfloor>\<tau>\<^sub>v\<^sub>a\<^sub>r(K\<^sub>2, n) \<oplus> \<delta>\<tau>\<rfloor> on K\<^sub>2) # \<Psi> \<triangleright> (K\<^sub>1 time-delayed by \<delta>\<tau> on K\<^sub>2 implies K\<^sub>3) # \<Phi> }"
  sorry

lemma HeronConf_interp_at_index_sporadic_cases:
  shows "\<lbrakk> \<Gamma>, n \<turnstile> (K sporadic \<tau>) # \<Psi> \<triangleright> \<Phi> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f
          = \<lbrakk> \<Gamma>, n \<turnstile> \<Psi> \<triangleright> (K sporadic \<tau>) # \<Phi> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f
          \<union> \<lbrakk> K \<Up> n # K \<Down> n @ \<lfloor>\<tau>\<rfloor> # \<Gamma>, n \<turnstile> \<Psi> \<triangleright> \<Phi> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f"
  proof -
    have "\<lbrakk> \<Gamma>, n \<turnstile> (K sporadic \<tau>) # \<Psi> \<triangleright> \<Phi> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f = \<lbrakk>\<lbrakk> \<Gamma> \<rbrakk>\<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n \<inter> \<lbrakk>\<lbrakk> (K sporadic \<tau>) # \<Psi> \<nabla> n \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L \<inter> \<lbrakk>\<lbrakk> \<Phi> \<nabla> Suc n \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L"
      by simp
    moreover have "\<lbrakk> \<Gamma>, n \<turnstile> \<Psi> \<triangleright> (K sporadic \<tau>) # \<Phi> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f = \<lbrakk>\<lbrakk> \<Gamma> \<rbrakk>\<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n \<inter> \<lbrakk>\<lbrakk> \<Psi> \<nabla> n \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L \<inter> \<lbrakk>\<lbrakk> (K sporadic \<tau>) # \<Phi> \<nabla> Suc n \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L"
      by simp
    moreover have "\<lbrakk> K \<Up> n # K \<Down> n @ \<lfloor>\<tau>\<rfloor> # \<Gamma>, n \<turnstile> \<Psi> \<triangleright> \<Phi> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f = \<lbrakk>\<lbrakk> K \<Up> n # K \<Down> n @ \<lfloor>\<tau>\<rfloor> # \<Gamma> \<rbrakk>\<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n \<inter> \<lbrakk>\<lbrakk> \<Psi> \<nabla> n \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L \<inter> \<lbrakk>\<lbrakk> \<Phi> \<nabla> Suc n \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L"
      by simp
    ultimately show ?thesis
    proof -
      have "(\<lbrakk> K \<Up> n \<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n \<inter> \<lbrakk> K \<Down> n @ \<lfloor> \<tau> \<rfloor> \<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n \<union> \<lbrakk> K sporadic \<tau> \<nabla> Suc n \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L) \<inter> \<lbrakk>\<lbrakk> \<Psi> \<nabla> n \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L = \<lbrakk>\<lbrakk> (K sporadic \<tau>) # \<Psi> \<nabla> n \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L"
        using TESL_interp_at_index_sporadic_cases TESL_interpretation_at_index_cons_morph by blast
  then have "\<lbrakk> \<Gamma>, n \<turnstile> (K sporadic \<tau>) # \<Psi> \<triangleright> \<Phi> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f = (\<lbrakk>\<lbrakk> K \<Up> n # K \<Down> n @ \<lfloor> \<tau> \<rfloor> # \<Gamma> \<rbrakk>\<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n \<inter> \<lbrakk>\<lbrakk> \<Psi> \<nabla> n \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L \<union> \<lbrakk>\<lbrakk> \<Gamma> \<rbrakk>\<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n \<inter> \<lbrakk>\<lbrakk> \<Psi> \<nabla> n \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L \<inter> \<lbrakk> K sporadic \<tau> \<nabla> Suc n \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L) \<inter> \<lbrakk>\<lbrakk> \<Phi> \<nabla> Suc n \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L"
    by auto
      then show ?thesis
        by (simp add: Int_Un_distrib2 Int_assoc Un_commute)
    qed
  qed

lemma HeronConf_interp_at_index_sporadicon_cases:
  shows "\<lbrakk> \<Gamma>, n \<turnstile> (K\<^sub>1 sporadic \<tau> on K\<^sub>2) # \<Psi> \<triangleright> \<Phi> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f
          = \<lbrakk> \<Gamma>, n \<turnstile> \<Psi> \<triangleright> (K\<^sub>1 sporadic \<tau> on K\<^sub>2) # \<Phi> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f
          \<union> \<lbrakk> K\<^sub>1 \<Up> n # K\<^sub>2 \<Down> n @ \<tau> # \<Gamma>, n \<turnstile> \<Psi> \<triangleright> \<Phi> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f"
  proof -
    have "\<lbrakk> \<Gamma>, n \<turnstile> (K\<^sub>1 sporadic \<tau> on K\<^sub>2) # \<Psi> \<triangleright> \<Phi> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f = \<lbrakk>\<lbrakk> \<Gamma> \<rbrakk>\<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n \<inter> \<lbrakk>\<lbrakk> (K\<^sub>1 sporadic \<tau> on K\<^sub>2) # \<Psi> \<nabla> n \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L \<inter> \<lbrakk>\<lbrakk> \<Phi> \<nabla> Suc n \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L"
      by simp
    moreover have "\<lbrakk> \<Gamma>, n \<turnstile> \<Psi> \<triangleright> (K\<^sub>1 sporadic \<tau> on K\<^sub>2) # \<Phi> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f = \<lbrakk>\<lbrakk> \<Gamma> \<rbrakk>\<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n \<inter> \<lbrakk>\<lbrakk> \<Psi> \<nabla> n \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L \<inter> \<lbrakk>\<lbrakk> (K\<^sub>1 sporadic \<tau> on K\<^sub>2) # \<Phi> \<nabla> Suc n \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L"
      by simp
    moreover have "\<lbrakk> K\<^sub>1 \<Up> n # K\<^sub>2 \<Down> n @ \<tau> # \<Gamma>, n \<turnstile> \<Psi> \<triangleright> \<Phi> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f = \<lbrakk>\<lbrakk> K\<^sub>1 \<Up> n # K\<^sub>2 \<Down> n @ \<tau> # \<Gamma> \<rbrakk>\<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n \<inter> \<lbrakk>\<lbrakk> \<Psi> \<nabla> n \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L \<inter> \<lbrakk>\<lbrakk> \<Phi> \<nabla> Suc n \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L"
      by simp
    ultimately show ?thesis
    proof -
      have "(\<lbrakk> K\<^sub>1 \<Up> n \<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n \<inter> \<lbrakk> K\<^sub>2 \<Down> n @ \<tau> \<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n \<union> \<lbrakk> K\<^sub>1 sporadic \<tau> on K\<^sub>2 \<nabla> Suc n \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L) \<inter> (\<lbrakk>\<lbrakk> \<Gamma> \<rbrakk>\<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n \<inter> \<lbrakk>\<lbrakk> \<Psi> \<nabla> n \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L) = \<lbrakk> K\<^sub>1 sporadic \<tau> on K\<^sub>2 \<nabla> n \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L \<inter> (\<lbrakk>\<lbrakk> \<Psi> \<nabla> n \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L \<inter> \<lbrakk>\<lbrakk> \<Gamma> \<rbrakk>\<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n)"
        using TESL_interp_at_index_sporadicon_cases by blast
      then have "\<lbrakk>\<lbrakk> K\<^sub>1 \<Up> n # K\<^sub>2 \<Down> n @ \<tau> # \<Gamma> \<rbrakk>\<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n \<inter> \<lbrakk>\<lbrakk> \<Psi> \<nabla> n \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L \<union> \<lbrakk>\<lbrakk> \<Gamma> \<rbrakk>\<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n \<inter> \<lbrakk>\<lbrakk> \<Psi> \<nabla> n \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L \<inter> \<lbrakk> K\<^sub>1 sporadic \<tau> on K\<^sub>2 \<nabla> Suc n \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L = \<lbrakk>\<lbrakk> (K\<^sub>1 sporadic \<tau> on K\<^sub>2) # \<Psi> \<nabla> n \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L \<inter> \<lbrakk>\<lbrakk> \<Gamma> \<rbrakk>\<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n"
        by auto
      then show ?thesis
        by auto
    qed
  qed

lemma HeronConf_interp_at_index_tagrel_cases:
  shows "\<lbrakk> \<Gamma>, n \<turnstile> (tag-relation K\<^sub>1 = \<alpha> * K\<^sub>2 + \<beta>) # \<Psi> \<triangleright> \<Phi> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f
          = \<lbrakk> (\<tau>\<^sub>v\<^sub>a\<^sub>r(K\<^sub>1, n) \<doteq> \<alpha> * \<tau>\<^sub>v\<^sub>a\<^sub>r(K\<^sub>2, n) + \<beta>) # \<Gamma>, n \<turnstile> \<Psi> \<triangleright> (tag-relation K\<^sub>1 = \<alpha> * K\<^sub>2 + \<beta>) # \<Phi> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f"
  proof -
    have "\<lbrakk> \<Gamma>, n \<turnstile> (tag-relation K\<^sub>1 = \<alpha> * K\<^sub>2 + \<beta>) # \<Psi> \<triangleright> \<Phi> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f = \<lbrakk>\<lbrakk> \<Gamma> \<rbrakk>\<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n \<inter> \<lbrakk>\<lbrakk> (tag-relation K\<^sub>1 = \<alpha> * K\<^sub>2 + \<beta>) # \<Psi> \<nabla> n \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L \<inter> \<lbrakk>\<lbrakk> \<Phi> \<nabla> Suc n \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L"
      by simp
    moreover have "\<lbrakk> (\<tau>\<^sub>v\<^sub>a\<^sub>r(K\<^sub>1, n) \<doteq> \<alpha> * \<tau>\<^sub>v\<^sub>a\<^sub>r(K\<^sub>2, n) + \<beta>) # \<Gamma>, n \<turnstile> \<Psi> \<triangleright> (tag-relation K\<^sub>1 = \<alpha> * K\<^sub>2 + \<beta>) # \<Phi> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f
                      = \<lbrakk>\<lbrakk> (\<tau>\<^sub>v\<^sub>a\<^sub>r(K\<^sub>1, n) \<doteq> \<alpha> * \<tau>\<^sub>v\<^sub>a\<^sub>r(K\<^sub>2, n) + \<beta>) # \<Gamma> \<rbrakk>\<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n \<inter> \<lbrakk>\<lbrakk> \<Psi> \<nabla> n \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L \<inter> \<lbrakk>\<lbrakk> (tag-relation K\<^sub>1 = \<alpha> * K\<^sub>2 + \<beta>) # \<Phi> \<nabla> Suc n \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L"
      by simp
    ultimately show ?thesis
    proof -
      have "\<lbrakk> \<tau>\<^sub>v\<^sub>a\<^sub>r (K\<^sub>1, n) \<doteq> \<alpha> * \<tau>\<^sub>v\<^sub>a\<^sub>r (K\<^sub>2, n) + \<beta> \<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n \<inter> \<lbrakk> tag-relation K\<^sub>1 = \<alpha> * K\<^sub>2 + \<beta> \<nabla> Suc n \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L \<inter> \<lbrakk>\<lbrakk> \<Psi> \<nabla> n \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L = \<lbrakk>\<lbrakk> (tag-relation K\<^sub>1 = \<alpha> * K\<^sub>2 + \<beta>) # \<Psi> \<nabla> n \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L"
        using TESL_interp_at_index_tagrel_cases TESL_interpretation_at_index_cons_morph by blast
      then show ?thesis
        by auto
    qed
  qed

lemma HeronConf_interp_at_index_implies_cases:
  shows "\<lbrakk> \<Gamma>, n \<turnstile> (K\<^sub>1 implies K\<^sub>2) # \<Psi> \<triangleright> \<Phi> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f
          = \<lbrakk> K\<^sub>1 \<not>\<Up> n # \<Gamma>, n \<turnstile> \<Psi> \<triangleright> (K\<^sub>1 implies K\<^sub>2) # \<Phi> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f
          \<union> \<lbrakk> K\<^sub>1 \<Up> n # K\<^sub>2 \<Up> n # \<Gamma>, n \<turnstile> \<Psi> \<triangleright> (K\<^sub>1 implies K\<^sub>2) # \<Phi> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f"
  proof -
    have "\<lbrakk> \<Gamma>, n \<turnstile> (K\<^sub>1 implies K\<^sub>2) # \<Psi> \<triangleright> \<Phi> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f = \<lbrakk>\<lbrakk> \<Gamma> \<rbrakk>\<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n \<inter> \<lbrakk>\<lbrakk> (K\<^sub>1 implies K\<^sub>2) # \<Psi> \<nabla> n \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L \<inter> \<lbrakk>\<lbrakk> \<Phi> \<nabla> Suc n \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L"
      by simp
    moreover have "\<lbrakk> K\<^sub>1 \<not>\<Up> n # \<Gamma>, n \<turnstile> \<Psi> \<triangleright> (K\<^sub>1 implies K\<^sub>2) # \<Phi> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f = \<lbrakk>\<lbrakk> K\<^sub>1 \<not>\<Up> n # \<Gamma> \<rbrakk>\<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n \<inter> \<lbrakk>\<lbrakk> \<Psi> \<nabla> n \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L \<inter> \<lbrakk>\<lbrakk> (K\<^sub>1 implies K\<^sub>2) # \<Phi> \<nabla> Suc n \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L"
      by simp
    moreover have "\<lbrakk> K\<^sub>1 \<Up> n # K\<^sub>2 \<Up> n # \<Gamma>, n \<turnstile> \<Psi> \<triangleright> (K\<^sub>1 implies K\<^sub>2) # \<Phi> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f = \<lbrakk>\<lbrakk> K\<^sub>1 \<Up> n # K\<^sub>2 \<Up> n # \<Gamma> \<rbrakk>\<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n \<inter> \<lbrakk>\<lbrakk> \<Psi> \<nabla> n \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L \<inter> \<lbrakk>\<lbrakk> (K\<^sub>1 implies K\<^sub>2) # \<Phi> \<nabla> Suc n \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L"
      by simp
    ultimately show ?thesis
    proof -
      have f1: "(\<lbrakk> K\<^sub>1 \<not>\<Up> n \<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n \<union> \<lbrakk> K\<^sub>1 \<Up> n \<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n \<inter> \<lbrakk> K\<^sub>2 \<Up> n \<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n) \<inter> \<lbrakk> K\<^sub>1 implies K\<^sub>2 \<nabla> Suc n \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L \<inter> (\<lbrakk>\<lbrakk> \<Psi> \<nabla> n \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L \<inter> \<lbrakk>\<lbrakk> \<Phi> \<nabla> Suc n \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L) = \<lbrakk>\<lbrakk> (K\<^sub>1 implies K\<^sub>2) # \<Psi> \<nabla> n \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L \<inter> \<lbrakk>\<lbrakk> \<Phi> \<nabla> Suc n \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L"
        using TESL_interp_at_index_implies_cases TESL_interpretation_at_index_cons_morph by blast
      have "\<lbrakk> K\<^sub>1 \<not>\<Up> n \<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n \<inter> \<lbrakk>\<lbrakk> \<Gamma> \<rbrakk>\<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n \<union> \<lbrakk> K\<^sub>1 \<Up> n \<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n \<inter> \<lbrakk>\<lbrakk> K\<^sub>2 \<Up> n # \<Gamma> \<rbrakk>\<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n = (\<lbrakk> K\<^sub>1 \<not>\<Up> n \<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n \<union> \<lbrakk> K\<^sub>1 \<Up> n \<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n \<inter> \<lbrakk> K\<^sub>2 \<Up> n \<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n) \<inter> \<lbrakk>\<lbrakk> \<Gamma> \<rbrakk>\<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n"
        by force
      then have "\<lbrakk> \<Gamma>, n \<turnstile> (K\<^sub>1 implies K\<^sub>2) # \<Psi> \<triangleright> \<Phi> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f = (\<lbrakk> K\<^sub>1 \<not>\<Up> n \<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n \<inter> \<lbrakk>\<lbrakk> \<Gamma> \<rbrakk>\<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n \<union> \<lbrakk> K\<^sub>1 \<Up> n \<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n \<inter> \<lbrakk>\<lbrakk> K\<^sub>2 \<Up> n # \<Gamma> \<rbrakk>\<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n) \<inter> (\<lbrakk>\<lbrakk> \<Psi> \<nabla> n \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L \<inter> \<lbrakk>\<lbrakk> (K\<^sub>1 implies K\<^sub>2) # \<Phi> \<nabla> Suc n \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L)"
        using f1 by (simp add: inf_left_commute inf_sup_aci(2))
      then show ?thesis
        by (simp add: Int_Un_distrib2 inf_sup_aci(2))
    qed
  qed

lemma HeronConf_interp_at_index_timedelayed_cases:
  shows "\<lbrakk> \<Gamma>, n \<turnstile> (K\<^sub>1 time-delayed by \<delta>\<tau> on K\<^sub>2 implies K\<^sub>3) # \<Psi> \<triangleright> \<Phi> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f
          = \<lbrakk> K\<^sub>1 \<not>\<Up> n # \<Gamma>, n \<turnstile> \<Psi> \<triangleright> (K\<^sub>1 time-delayed by \<delta>\<tau> on K\<^sub>2 implies K\<^sub>3) # \<Phi> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f
          \<union> \<lbrakk> K\<^sub>1 \<Up> n # \<Gamma>, n \<turnstile> (K\<^sub>3 sporadic \<lfloor>\<tau>\<^sub>v\<^sub>a\<^sub>r(K\<^sub>2, n) \<oplus> \<delta>\<tau>\<rfloor> on K\<^sub>2) # \<Psi> \<triangleright> (K\<^sub>1 time-delayed by \<delta>\<tau> on K\<^sub>2 implies K\<^sub>3) # \<Phi> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f"
  proof -
    have "\<lbrakk> \<Gamma>, n \<turnstile> (K\<^sub>1 time-delayed by \<delta>\<tau> on K\<^sub>2 implies K\<^sub>3) # \<Psi> \<triangleright> \<Phi> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f
           = \<lbrakk>\<lbrakk> \<Gamma> \<rbrakk>\<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n \<inter> \<lbrakk>\<lbrakk> (K\<^sub>1 time-delayed by \<delta>\<tau> on K\<^sub>2 implies K\<^sub>3) # \<Psi> \<nabla> n \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L \<inter> \<lbrakk>\<lbrakk> \<Phi> \<nabla> Suc n \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L"
      by simp
    moreover have "\<lbrakk> K\<^sub>1 \<not>\<Up> n # \<Gamma>, n \<turnstile> \<Psi> \<triangleright> (K\<^sub>1 time-delayed by \<delta>\<tau> on K\<^sub>2 implies K\<^sub>3) # \<Phi> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f
                     = \<lbrakk>\<lbrakk> K\<^sub>1 \<not>\<Up> n # \<Gamma> \<rbrakk>\<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n \<inter> \<lbrakk>\<lbrakk> \<Psi> \<nabla> n \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L \<inter> \<lbrakk>\<lbrakk> (K\<^sub>1 time-delayed by \<delta>\<tau> on K\<^sub>2 implies K\<^sub>3) # \<Phi> \<nabla> Suc n \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L"
      by simp
    moreover have "\<lbrakk> K\<^sub>1 \<Up> n # \<Gamma>, n \<turnstile> (K\<^sub>3 sporadic \<lfloor>\<tau>\<^sub>v\<^sub>a\<^sub>r(K\<^sub>2, n) \<oplus> \<delta>\<tau>\<rfloor> on K\<^sub>2) # \<Psi> \<triangleright> (K\<^sub>1 time-delayed by \<delta>\<tau> on K\<^sub>2 implies K\<^sub>3) # \<Phi> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f
                     = \<lbrakk>\<lbrakk> K\<^sub>1 \<Up> n # \<Gamma> \<rbrakk>\<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n \<inter> \<lbrakk>\<lbrakk> (K\<^sub>3 sporadic \<lfloor>\<tau>\<^sub>v\<^sub>a\<^sub>r(K\<^sub>2, n) \<oplus> \<delta>\<tau>\<rfloor> on K\<^sub>2) # \<Psi> \<nabla> n \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L
                     \<inter> \<lbrakk>\<lbrakk> (K\<^sub>1 time-delayed by \<delta>\<tau> on K\<^sub>2 implies K\<^sub>3) # \<Phi> \<nabla> Suc n \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L"
      by simp
    ultimately show ?thesis
    proof -
      have "\<lbrakk> \<Gamma>, n \<turnstile> (K\<^sub>1 time-delayed by \<delta>\<tau> on K\<^sub>2 implies K\<^sub>3) # \<Psi> \<triangleright> \<Phi> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f = \<lbrakk>\<lbrakk> \<Gamma> \<rbrakk>\<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n \<inter> (\<lbrakk>\<lbrakk> (K\<^sub>1 time-delayed by \<delta>\<tau> on K\<^sub>2 implies K\<^sub>3) # \<Psi> \<nabla> n \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L \<inter> \<lbrakk>\<lbrakk> \<Phi> \<nabla> Suc n \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L)"
        using \<open>\<lbrakk> \<Gamma>, n \<turnstile> (K\<^sub>1 time-delayed by \<delta>\<tau> on K\<^sub>2 implies K\<^sub>3) # \<Psi> \<triangleright> \<Phi> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f = \<lbrakk>\<lbrakk> \<Gamma> \<rbrakk>\<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n \<inter> \<lbrakk>\<lbrakk> (K\<^sub>1 time-delayed by \<delta>\<tau> on K\<^sub>2 implies K\<^sub>3) # \<Psi> \<nabla> n \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L \<inter> \<lbrakk>\<lbrakk> \<Phi> \<nabla> Suc n \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<close> by blast
      then have "\<lbrakk> \<Gamma>, n \<turnstile> (K\<^sub>1 time-delayed by \<delta>\<tau> on K\<^sub>2 implies K\<^sub>3) # \<Psi> \<triangleright> \<Phi> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f = (\<lbrakk> K\<^sub>1 \<not>\<Up> n \<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n \<union> \<lbrakk> K\<^sub>1 \<Up> n \<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n \<inter> \<lbrakk> K\<^sub>3 sporadic \<lfloor> \<tau>\<^sub>v\<^sub>a\<^sub>r (K\<^sub>2, n) \<oplus> \<delta>\<tau> \<rfloor> on K\<^sub>2 \<nabla> n \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L) \<inter> (\<lbrakk>\<lbrakk> \<Gamma> \<rbrakk>\<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n \<inter> (\<lbrakk>\<lbrakk> \<Psi> \<nabla> n \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L \<inter> \<lbrakk>\<lbrakk> (K\<^sub>1 time-delayed by \<delta>\<tau> on K\<^sub>2 implies K\<^sub>3) # \<Phi> \<nabla> Suc n \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L))"
        using TESL_interp_at_index_timedelayed_cases TESL_interpretation_at_index_cons_morph by blast
      then show ?thesis
        by auto
    qed
  qed


find_theorems name: "operational_semantics_step"
theorem completeness:
  shows "\<lbrakk> \<Gamma>, n \<turnstile> \<Psi> \<triangleright> \<Phi> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f = (\<Union>X\<in>\<F>\<^sub>n\<^sub>e\<^sub>x\<^sub>t (\<Gamma>, n \<turnstile> \<Psi> \<triangleright> \<Phi>). \<lbrakk> X \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f)"
  proof (induct \<Psi>)
    case Nil
    then show ?case using Fnext_solve_instant by simp
  next
    case (Cons \<psi> \<Psi>)
    then show ?case
      proof (induct \<psi>)
        case (Sporadic K \<tau>)
        then show ?case
          using HeronConf_interp_at_index_sporadic_cases Fnext_solve_sporadic by simp
      next
        case (SporadicOn K1 \<tau> K2)
        then show ?case 
          using HeronConf_interp_at_index_sporadicon_cases Fnext_solve_sporadicon by simp
      next
        case (TagRelation K1 \<alpha> K2 \<beta>)
        then show ?case
          using HeronConf_interp_at_index_tagrel_cases Fnext_solve_tagrel by simp
      next
        case (Implies K1 K2)
        then show ?case
          using HeronConf_interp_at_index_implies_cases Fnext_solve_implies by simp
      next
        case (TimeDelayedBy Kmast \<tau> Kmeas Kslave)
        then show ?case
          using HeronConf_interp_at_index_timedelayed_cases Fnext_solve_timedelayed by simp
      qed
  qed

(**) section \<open>Termination of instantaneous formulae elimination\<close> (**)
(* Idea: A bounded monotonic sequence is convergent *)
primrec measure_interpretation :: "TESL_formula \<Rightarrow> nat" ("\<lbrakk>\<lbrakk> _ \<rbrakk>\<rbrakk>\<^sub>m\<^sub>e\<^sub>a\<^sub>s") where
    "\<lbrakk>\<lbrakk> [] \<rbrakk>\<rbrakk>\<^sub>m\<^sub>e\<^sub>a\<^sub>s = (0::nat)"
  | "\<lbrakk>\<lbrakk> \<phi> # \<Phi> \<rbrakk>\<rbrakk>\<^sub>m\<^sub>e\<^sub>a\<^sub>s = (case \<phi> of
                        _ sporadic _ on _ \<Rightarrow> 1 + \<lbrakk>\<lbrakk> \<Phi> \<rbrakk>\<rbrakk>\<^sub>m\<^sub>e\<^sub>a\<^sub>s
                      | _                 \<Rightarrow> 2 + \<lbrakk>\<lbrakk> \<Phi> \<rbrakk>\<rbrakk>\<^sub>m\<^sub>e\<^sub>a\<^sub>s)"

fun measure_interpretation_config :: "config \<Rightarrow> nat" ("\<lbrakk>\<lbrakk> _ \<rbrakk>\<rbrakk>\<^sub>m\<^sub>e\<^sub>a\<^sub>s\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g") where
    "\<lbrakk>\<lbrakk> \<Gamma>, n \<turnstile> \<Psi> \<triangleright> \<Phi> \<rbrakk>\<rbrakk>\<^sub>m\<^sub>e\<^sub>a\<^sub>s\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g = \<lbrakk>\<lbrakk> \<Psi> \<rbrakk>\<rbrakk>\<^sub>m\<^sub>e\<^sub>a\<^sub>s"

lemma elimation_rules_strictly_decreasing:
  assumes "\<Gamma>\<^sub>1, n\<^sub>1 \<turnstile> \<Psi>\<^sub>1 \<triangleright> \<Phi>\<^sub>1  \<hookrightarrow>\<^sub>e  \<Gamma>\<^sub>2, n\<^sub>2 \<turnstile> \<Psi>\<^sub>2 \<triangleright> \<Phi>\<^sub>2"
  shows "\<lbrakk>\<lbrakk> \<Psi>\<^sub>1 \<rbrakk>\<rbrakk>\<^sub>m\<^sub>e\<^sub>a\<^sub>s > \<lbrakk>\<lbrakk> \<Psi>\<^sub>2 \<rbrakk>\<rbrakk>\<^sub>m\<^sub>e\<^sub>a\<^sub>s"
  by (insert assms, erule operational_semantics_elim.cases, auto)

lemma elimation_rules_strictly_decreasing_meas:
  assumes "\<Gamma>\<^sub>1, n\<^sub>1 \<turnstile> \<Psi>\<^sub>1 \<triangleright> \<Phi>\<^sub>1  \<hookrightarrow>\<^sub>e  \<Gamma>\<^sub>2, n\<^sub>2 \<turnstile> \<Psi>\<^sub>2 \<triangleright> \<Phi>\<^sub>2"
  shows "(\<Psi>\<^sub>2, \<Psi>\<^sub>1) \<in> measure measure_interpretation"
  by (insert assms, erule operational_semantics_elim.cases, auto)

lemma elimation_rules_strictly_decreasing_meas':
  assumes "\<S>\<^sub>1  \<hookrightarrow>\<^sub>e  \<S>\<^sub>2"
  shows "(\<S>\<^sub>2, \<S>\<^sub>1) \<in> measure measure_interpretation_config"
  sorry

lemma instant_computation_termination:
  shows "wf {(\<S>\<^sub>1, \<S>\<^sub>2). \<S>\<^sub>1 \<hookrightarrow>\<^sub>e \<S>\<^sub>2}"
  apply (rule wf_subset)
  proof -
    have "measure (\<lambda>\<S>. \<lbrakk>\<lbrakk> \<S> \<rbrakk>\<rbrakk>\<^sub>m\<^sub>e\<^sub>a\<^sub>s\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g) = { (\<S>\<^sub>1, \<S>\<^sub>2). \<lbrakk>\<lbrakk> \<S>\<^sub>1 \<rbrakk>\<rbrakk>\<^sub>m\<^sub>e\<^sub>a\<^sub>s\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g < \<lbrakk>\<lbrakk> \<S>\<^sub>2 \<rbrakk>\<rbrakk>\<^sub>m\<^sub>e\<^sub>a\<^sub>s\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g }"
      by (simp add: inv_image_def less_eq measure_def)
    show "{(\<S>\<^sub>1, \<S>\<^sub>2). \<S>\<^sub>1 \<hookrightarrow>\<^sub>e \<S>\<^sub>2} \<subseteq> (measure (\<lambda>\<S>. \<lbrakk>\<lbrakk> \<S> \<rbrakk>\<rbrakk>\<^sub>m\<^sub>e\<^sub>a\<^sub>s\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g))"
      sorry  (* Pas dans le bon sens !?! *)
    show "wf (measure measure_interpretation_config)"
      by simp
  qed

theorem instant_computation_termination':
  shows "wfP (\<lambda>\<S>\<^sub>1 \<S>\<^sub>2. \<S>\<^sub>1 \<hookrightarrow>\<^sub>e \<S>\<^sub>2)"
  using instant_computation_termination
  by (simp add: wfP_def)

lemma run_index_progress:
  assumes "\<Gamma>\<^sub>1, n\<^sub>1 \<turnstile> \<Psi>\<^sub>1 \<triangleright> \<Phi>\<^sub>1  \<hookrightarrow>  \<Gamma>\<^sub>2, n\<^sub>2 \<turnstile> \<Psi>\<^sub>2 \<triangleright> \<Phi>\<^sub>2"
  shows "n\<^sub>2 = Suc n\<^sub>1 \<or> n\<^sub>2 = n\<^sub>1"
  by (insert assms, erule operational_semantics_step.cases, auto)

lemma run_index_progress_simlstep:
  assumes "\<Gamma>\<^sub>1, n\<^sub>1 \<turnstile> \<Psi>\<^sub>1 \<triangleright> \<Phi>\<^sub>1  \<hookrightarrow>\<^sub>\<nabla>  \<Gamma>\<^sub>2, n\<^sub>2 \<turnstile> \<Psi>\<^sub>2 \<triangleright> \<Phi>\<^sub>2"
  shows "n\<^sub>2 = Suc n\<^sub>1"
  apply (insert assms)
  sorry

(**) section \<open>Composition\<close> (**)

lemma composition:
  shows "\<lbrakk> \<Gamma>\<^sub>1, n \<turnstile> \<Psi>\<^sub>1 \<triangleright> \<Phi>\<^sub>1 \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f \<inter> \<lbrakk> \<Gamma>\<^sub>2, n \<turnstile> \<Psi>\<^sub>2 \<triangleright> \<Phi>\<^sub>2 \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f
         = \<lbrakk> \<Gamma>\<^sub>1 @ \<Gamma>\<^sub>2, n \<turnstile> \<Psi>\<^sub>1 @ \<Psi>\<^sub>2 \<triangleright> \<Phi>\<^sub>1 @ \<Phi>\<^sub>2 \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f"
  using TESL_interp_at_index_composition symrun_interp_expansion by auto

(**) section \<open>Semidecidability\<close> (**)
(* The set of runs hence becomes recursively countable due to the previous observations. *)

(**) section \<open>Existence\<close> (**)
fun tagrel_consistent :: "TESL_formula \<Rightarrow> bool" where
  "tagrel_consistent \<Phi> = undefined"

lemma existence:
  (* Assumption that the linear system made of tag relations is consistent *)
  assumes "tagrel_consistent \<Phi>"
  shows "\<exists>\<rho>. \<rho> \<in> \<lbrakk>\<lbrakk> \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L"
oops
(* proof (induction \<Phi>) *)

end