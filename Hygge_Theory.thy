theory Hygge_Theory
imports
  "Coinductive_Prop"

begin

section \<open>Initial configuration\<close>

lemma solve_start:
  shows "\<lbrakk>\<lbrakk> \<Psi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L = \<lbrakk> [], 0 \<turnstile> \<Psi> \<triangleright> [] \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g"
  proof -
    have "\<lbrakk>\<lbrakk> \<Psi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L = \<lbrakk>\<lbrakk> \<Psi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> 0\<^esup>"
    by (simp add: TESL_interpretation_at_index_zero')
    moreover have "\<lbrakk> [], 0 \<turnstile> \<Psi> \<triangleright> [] \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g = \<lbrakk>\<lbrakk> [] \<rbrakk>\<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n \<inter> \<lbrakk>\<lbrakk> \<Psi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> 0\<^esup> \<inter> \<lbrakk>\<lbrakk> [] \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc 0\<^esup>"
    by simp
    ultimately show ?thesis by auto
  qed

section \<open>Soundness\<close>

theorem soundness:
  assumes "\<Gamma>\<^sub>1, n\<^sub>1 \<turnstile> \<Psi>\<^sub>1 \<triangleright> \<Phi>\<^sub>1  \<hookrightarrow>  \<Gamma>\<^sub>2, n\<^sub>2 \<turnstile> \<Psi>\<^sub>2 \<triangleright> \<Phi>\<^sub>2"
  shows "\<lbrakk>\<lbrakk> \<Gamma>\<^sub>1 \<rbrakk>\<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n \<inter> \<lbrakk>\<lbrakk> \<Psi>\<^sub>1 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^sub>1\<^esup> \<inter> \<lbrakk>\<lbrakk> \<Phi>\<^sub>1 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^sub>1\<^esup>
          \<supseteq>  \<lbrakk>\<lbrakk> \<Gamma>\<^sub>2 \<rbrakk>\<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n \<inter> \<lbrakk>\<lbrakk> \<Psi>\<^sub>2 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^sub>2\<^esup> \<inter> \<lbrakk>\<lbrakk> \<Phi>\<^sub>2 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^sub>2\<^esup>"
  proof (insert assms, erule operational_semantics_step.cases)
  show "\<And>\<Gamma>\<^sub>1' n\<^sub>1' \<Psi>\<^sub>1' \<Phi>\<^sub>1' \<Gamma>\<^sub>2' n\<^sub>2' \<Psi>\<^sub>2' \<Phi>\<^sub>2'.
       \<Gamma>\<^sub>1, n\<^sub>1 \<turnstile> \<Psi>\<^sub>1 \<triangleright> \<Phi>\<^sub>1 = \<Gamma>\<^sub>1', n\<^sub>1' \<turnstile> \<Psi>\<^sub>1' \<triangleright> \<Phi>\<^sub>1' \<Longrightarrow>
       \<Gamma>\<^sub>2, n\<^sub>2 \<turnstile> \<Psi>\<^sub>2 \<triangleright> \<Phi>\<^sub>2 = \<Gamma>\<^sub>2', n\<^sub>2' \<turnstile> \<Psi>\<^sub>2' \<triangleright> \<Phi>\<^sub>2' \<Longrightarrow>
       \<Gamma>\<^sub>1', n\<^sub>1' \<turnstile> \<Psi>\<^sub>1' \<triangleright> \<Phi>\<^sub>1' \<hookrightarrow>\<^sub>i \<Gamma>\<^sub>2', n\<^sub>2' \<turnstile> \<Psi>\<^sub>2' \<triangleright> \<Phi>\<^sub>2' \<Longrightarrow>
       \<lbrakk>\<lbrakk> \<Gamma>\<^sub>2 \<rbrakk>\<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n \<inter> \<lbrakk>\<lbrakk> \<Psi>\<^sub>2 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^sub>2\<^esup> \<inter> \<lbrakk>\<lbrakk> \<Phi>\<^sub>2 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^sub>2\<^esup>
       \<subseteq> \<lbrakk>\<lbrakk> \<Gamma>\<^sub>1 \<rbrakk>\<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n \<inter> \<lbrakk>\<lbrakk> \<Psi>\<^sub>1 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^sub>1\<^esup> \<inter> \<lbrakk>\<lbrakk> \<Phi>\<^sub>1 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^sub>1\<^esup>"
    by (erule operational_semantics_intro.cases, auto)
  show "\<And>\<Gamma>\<^sub>1' n\<^sub>1' \<Psi>\<^sub>1' \<Phi>\<^sub>1' \<Gamma>\<^sub>2' n\<^sub>2' \<Psi>\<^sub>2' \<Phi>\<^sub>2'.
       \<Gamma>\<^sub>1, n\<^sub>1 \<turnstile> \<Psi>\<^sub>1 \<triangleright> \<Phi>\<^sub>1 = \<Gamma>\<^sub>1', n\<^sub>1' \<turnstile> \<Psi>\<^sub>1' \<triangleright> \<Phi>\<^sub>1' \<Longrightarrow>
       \<Gamma>\<^sub>2, n\<^sub>2 \<turnstile> \<Psi>\<^sub>2 \<triangleright> \<Phi>\<^sub>2 = \<Gamma>\<^sub>2', n\<^sub>2' \<turnstile> \<Psi>\<^sub>2' \<triangleright> \<Phi>\<^sub>2' \<Longrightarrow>
       \<Gamma>\<^sub>1', n\<^sub>1' \<turnstile> \<Psi>\<^sub>1' \<triangleright> \<Phi>\<^sub>1' \<hookrightarrow>\<^sub>e \<Gamma>\<^sub>2', n\<^sub>2' \<turnstile> \<Psi>\<^sub>2' \<triangleright> \<Phi>\<^sub>2' \<Longrightarrow>
       \<lbrakk>\<lbrakk> \<Gamma>\<^sub>2 \<rbrakk>\<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n \<inter> \<lbrakk>\<lbrakk> \<Psi>\<^sub>2 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^sub>2\<^esup> \<inter> \<lbrakk>\<lbrakk> \<Phi>\<^sub>2 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^sub>2\<^esup>
       \<subseteq> \<lbrakk>\<lbrakk> \<Gamma>\<^sub>1 \<rbrakk>\<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n \<inter> \<lbrakk>\<lbrakk> \<Psi>\<^sub>1 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^sub>1\<^esup> \<inter> \<lbrakk>\<lbrakk> \<Phi>\<^sub>1 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^sub>1\<^esup>"
    proof (erule operational_semantics_elim.cases)
    show "\<And>\<Gamma>\<^sub>1' n\<^sub>1' \<Psi>\<^sub>1' \<Phi>\<^sub>1' \<Gamma>\<^sub>2' n\<^sub>2' \<Psi>\<^sub>2' \<Phi>\<^sub>2' \<Gamma> n K \<tau> \<Psi> \<Phi>.
       (\<Gamma>\<^sub>1, n\<^sub>1 \<turnstile> \<Psi>\<^sub>1 \<triangleright> \<Phi>\<^sub>1) = (\<Gamma>\<^sub>1', n\<^sub>1' \<turnstile> \<Psi>\<^sub>1' \<triangleright> \<Phi>\<^sub>1') \<Longrightarrow>
       (\<Gamma>\<^sub>2, n\<^sub>2 \<turnstile> \<Psi>\<^sub>2 \<triangleright> \<Phi>\<^sub>2) = (\<Gamma>\<^sub>2', n\<^sub>2' \<turnstile> \<Psi>\<^sub>2' \<triangleright> \<Phi>\<^sub>2') \<Longrightarrow>
       (\<Gamma>\<^sub>1', n\<^sub>1' \<turnstile> \<Psi>\<^sub>1' \<triangleright> \<Phi>\<^sub>1') = (\<Gamma>, n \<turnstile> (K sporadic \<tau>) # \<Psi> \<triangleright> \<Phi>) \<Longrightarrow>
       (\<Gamma>\<^sub>2', n\<^sub>2' \<turnstile> \<Psi>\<^sub>2' \<triangleright> \<Phi>\<^sub>2') = (\<Gamma>, n \<turnstile> \<Psi> \<triangleright> (K sporadic \<tau>) # \<Phi>) \<Longrightarrow>
       \<lbrakk>\<lbrakk> \<Gamma>\<^sub>2 \<rbrakk>\<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n \<inter> \<lbrakk>\<lbrakk> \<Psi>\<^sub>2 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^sub>2\<^esup> \<inter> \<lbrakk>\<lbrakk> \<Phi>\<^sub>2 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^sub>2\<^esup>
       \<subseteq> \<lbrakk>\<lbrakk> \<Gamma>\<^sub>1 \<rbrakk>\<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n \<inter> \<lbrakk>\<lbrakk> \<Psi>\<^sub>1 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^sub>1\<^esup> \<inter> \<lbrakk>\<lbrakk> \<Phi>\<^sub>1 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^sub>1\<^esup>"
      using HeronConf_interp_at_index_sporadic_cases by auto
    show "\<And>\<Gamma>\<^sub>1' n\<^sub>1' \<Psi>\<^sub>1' \<Phi>\<^sub>1' \<Gamma>\<^sub>2' n\<^sub>2' \<Psi>\<^sub>2' \<Phi>\<^sub>2' \<Gamma> n K \<tau> \<Psi> \<Phi>.
       (\<Gamma>\<^sub>1, n\<^sub>1 \<turnstile> \<Psi>\<^sub>1 \<triangleright> \<Phi>\<^sub>1) = (\<Gamma>\<^sub>1', n\<^sub>1' \<turnstile> \<Psi>\<^sub>1' \<triangleright> \<Phi>\<^sub>1') \<Longrightarrow>
       (\<Gamma>\<^sub>2, n\<^sub>2 \<turnstile> \<Psi>\<^sub>2 \<triangleright> \<Phi>\<^sub>2) = (\<Gamma>\<^sub>2', n\<^sub>2' \<turnstile> \<Psi>\<^sub>2' \<triangleright> \<Phi>\<^sub>2') \<Longrightarrow>
       (\<Gamma>\<^sub>1', n\<^sub>1' \<turnstile> \<Psi>\<^sub>1' \<triangleright> \<Phi>\<^sub>1') = (\<Gamma>, n \<turnstile> (K sporadic \<tau>) # \<Psi> \<triangleright> \<Phi>) \<Longrightarrow>
       (\<Gamma>\<^sub>2', n\<^sub>2' \<turnstile> \<Psi>\<^sub>2' \<triangleright> \<Phi>\<^sub>2') = (K \<Up> n # K \<Down> n @ \<lfloor> \<tau> \<rfloor> # \<Gamma>, n \<turnstile> \<Psi> \<triangleright> \<Phi>) \<Longrightarrow>
       \<lbrakk>\<lbrakk> \<Gamma>\<^sub>2 \<rbrakk>\<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n \<inter> \<lbrakk>\<lbrakk> \<Psi>\<^sub>2 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^sub>2\<^esup> \<inter> \<lbrakk>\<lbrakk> \<Phi>\<^sub>2 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^sub>2\<^esup>
       \<subseteq> \<lbrakk>\<lbrakk> \<Gamma>\<^sub>1 \<rbrakk>\<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n \<inter> \<lbrakk>\<lbrakk> \<Psi>\<^sub>1 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^sub>1\<^esup> \<inter> \<lbrakk>\<lbrakk> \<Phi>\<^sub>1 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^sub>1\<^esup>"
      using HeronConf_interp_at_index_sporadic_cases by auto
    show "\<And>\<Gamma>\<^sub>1' n\<^sub>1' \<Psi>\<^sub>1' \<Phi>\<^sub>1' \<Gamma>\<^sub>2' n\<^sub>2' \<Psi>\<^sub>2' \<Phi>\<^sub>2' \<Gamma> n K\<^sub>1 \<tau> K\<^sub>2 \<Psi> \<Phi>.
       (\<Gamma>\<^sub>1, n\<^sub>1 \<turnstile> \<Psi>\<^sub>1 \<triangleright> \<Phi>\<^sub>1) = (\<Gamma>\<^sub>1', n\<^sub>1' \<turnstile> \<Psi>\<^sub>1' \<triangleright> \<Phi>\<^sub>1') \<Longrightarrow>
       (\<Gamma>\<^sub>2, n\<^sub>2 \<turnstile> \<Psi>\<^sub>2 \<triangleright> \<Phi>\<^sub>2) = (\<Gamma>\<^sub>2', n\<^sub>2' \<turnstile> \<Psi>\<^sub>2' \<triangleright> \<Phi>\<^sub>2') \<Longrightarrow>
       (\<Gamma>\<^sub>1', n\<^sub>1' \<turnstile> \<Psi>\<^sub>1' \<triangleright> \<Phi>\<^sub>1') = (\<Gamma>, n \<turnstile> (K\<^sub>1 sporadic \<tau> on K\<^sub>2) # \<Psi> \<triangleright> \<Phi>) \<Longrightarrow>
       (\<Gamma>\<^sub>2', n\<^sub>2' \<turnstile> \<Psi>\<^sub>2' \<triangleright> \<Phi>\<^sub>2') = (\<Gamma>, n \<turnstile> \<Psi> \<triangleright> (K\<^sub>1 sporadic \<tau> on K\<^sub>2) # \<Phi>) \<Longrightarrow>
       \<lbrakk>\<lbrakk> \<Gamma>\<^sub>2 \<rbrakk>\<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n \<inter> \<lbrakk>\<lbrakk> \<Psi>\<^sub>2 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^sub>2\<^esup> \<inter> \<lbrakk>\<lbrakk> \<Phi>\<^sub>2 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^sub>2\<^esup>
       \<subseteq> \<lbrakk>\<lbrakk> \<Gamma>\<^sub>1 \<rbrakk>\<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n \<inter> \<lbrakk>\<lbrakk> \<Psi>\<^sub>1 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^sub>1\<^esup> \<inter> \<lbrakk>\<lbrakk> \<Phi>\<^sub>1 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^sub>1\<^esup>"
      using HeronConf_interp_at_index_sporadicon_cases by auto
    show "\<And>\<Gamma>\<^sub>1' n\<^sub>1' \<Psi>\<^sub>1' \<Phi>\<^sub>1' \<Gamma>\<^sub>2' n\<^sub>2' \<Psi>\<^sub>2' \<Phi>\<^sub>2' \<Gamma> n K\<^sub>1 \<tau> K\<^sub>2 \<Psi> \<Phi>.
       (\<Gamma>\<^sub>1, n\<^sub>1 \<turnstile> \<Psi>\<^sub>1 \<triangleright> \<Phi>\<^sub>1) = (\<Gamma>\<^sub>1', n\<^sub>1' \<turnstile> \<Psi>\<^sub>1' \<triangleright> \<Phi>\<^sub>1') \<Longrightarrow>
       (\<Gamma>\<^sub>2, n\<^sub>2 \<turnstile> \<Psi>\<^sub>2 \<triangleright> \<Phi>\<^sub>2) = (\<Gamma>\<^sub>2', n\<^sub>2' \<turnstile> \<Psi>\<^sub>2' \<triangleright> \<Phi>\<^sub>2') \<Longrightarrow>
       (\<Gamma>\<^sub>1', n\<^sub>1' \<turnstile> \<Psi>\<^sub>1' \<triangleright> \<Phi>\<^sub>1') = (\<Gamma>, n \<turnstile> (K\<^sub>1 sporadic \<tau> on K\<^sub>2) # \<Psi> \<triangleright> \<Phi>) \<Longrightarrow>
       (\<Gamma>\<^sub>2', n\<^sub>2' \<turnstile> \<Psi>\<^sub>2' \<triangleright> \<Phi>\<^sub>2') = (K\<^sub>1 \<Up> n # K\<^sub>2 \<Down> n @ \<tau> # \<Gamma>, n \<turnstile> \<Psi> \<triangleright> \<Phi>) \<Longrightarrow>
       \<lbrakk>\<lbrakk> \<Gamma>\<^sub>2 \<rbrakk>\<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n \<inter> \<lbrakk>\<lbrakk> \<Psi>\<^sub>2 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^sub>2\<^esup> \<inter> \<lbrakk>\<lbrakk> \<Phi>\<^sub>2 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^sub>2\<^esup>
       \<subseteq> \<lbrakk>\<lbrakk> \<Gamma>\<^sub>1 \<rbrakk>\<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n \<inter> \<lbrakk>\<lbrakk> \<Psi>\<^sub>1 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^sub>1\<^esup> \<inter> \<lbrakk>\<lbrakk> \<Phi>\<^sub>1 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^sub>1\<^esup>"
      using HeronConf_interp_at_index_sporadicon_cases by auto
    show "\<And>\<Gamma>\<^sub>1' n\<^sub>1' \<Psi>\<^sub>1' \<Phi>\<^sub>1' \<Gamma>\<^sub>2' n\<^sub>2' \<Psi>\<^sub>2' \<Phi>\<^sub>2' \<Gamma> n K\<^sub>1 \<alpha> K\<^sub>2 \<beta> \<Psi> \<Phi>.
       (\<Gamma>\<^sub>1, n\<^sub>1 \<turnstile> \<Psi>\<^sub>1 \<triangleright> \<Phi>\<^sub>1) = \<Gamma>\<^sub>1', n\<^sub>1' \<turnstile> \<Psi>\<^sub>1' \<triangleright> \<Phi>\<^sub>1' \<Longrightarrow>
       (\<Gamma>\<^sub>2, n\<^sub>2 \<turnstile> \<Psi>\<^sub>2 \<triangleright> \<Phi>\<^sub>2) = \<Gamma>\<^sub>2', n\<^sub>2' \<turnstile> \<Psi>\<^sub>2' \<triangleright> \<Phi>\<^sub>2' \<Longrightarrow>
       (\<Gamma>\<^sub>1', n\<^sub>1' \<turnstile> \<Psi>\<^sub>1' \<triangleright> \<Phi>\<^sub>1') = \<Gamma>, n \<turnstile> (tag-relation K\<^sub>1 = \<alpha> * K\<^sub>2 + \<beta>) # \<Psi> \<triangleright> \<Phi> \<Longrightarrow>
       (\<Gamma>\<^sub>2', n\<^sub>2' \<turnstile> \<Psi>\<^sub>2' \<triangleright> \<Phi>\<^sub>2') =
       \<tau>\<^sub>v\<^sub>a\<^sub>r (K\<^sub>1, n) \<doteq> \<alpha> * \<tau>\<^sub>v\<^sub>a\<^sub>r (K\<^sub>2, n) + \<beta> #
       \<Gamma>, n \<turnstile> \<Psi> \<triangleright> (tag-relation K\<^sub>1 = \<alpha> * K\<^sub>2 + \<beta>) # \<Phi> \<Longrightarrow>
       \<lbrakk>\<lbrakk> \<Gamma>\<^sub>2 \<rbrakk>\<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n \<inter> \<lbrakk>\<lbrakk> \<Psi>\<^sub>2 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^sub>2\<^esup> \<inter> \<lbrakk>\<lbrakk> \<Phi>\<^sub>2 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^sub>2\<^esup>
       \<subseteq> \<lbrakk>\<lbrakk> \<Gamma>\<^sub>1 \<rbrakk>\<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n \<inter> \<lbrakk>\<lbrakk> \<Psi>\<^sub>1 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^sub>1\<^esup> \<inter> \<lbrakk>\<lbrakk> \<Phi>\<^sub>1 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^sub>1\<^esup>"
      using HeronConf_interp_at_index_tagrel_cases by auto
    show "\<And>\<Gamma>\<^sub>1' n\<^sub>1' \<Psi>\<^sub>1' \<Phi>\<^sub>1' \<Gamma>\<^sub>2' n\<^sub>2' \<Psi>\<^sub>2' \<Phi>\<^sub>2' \<Gamma> n K\<^sub>1 K\<^sub>2 \<Psi> \<Phi>.
       (\<Gamma>\<^sub>1, n\<^sub>1 \<turnstile> \<Psi>\<^sub>1 \<triangleright> \<Phi>\<^sub>1) = \<Gamma>\<^sub>1', n\<^sub>1' \<turnstile> \<Psi>\<^sub>1' \<triangleright> \<Phi>\<^sub>1' \<Longrightarrow>
       (\<Gamma>\<^sub>2, n\<^sub>2 \<turnstile> \<Psi>\<^sub>2 \<triangleright> \<Phi>\<^sub>2) = \<Gamma>\<^sub>2', n\<^sub>2' \<turnstile> \<Psi>\<^sub>2' \<triangleright> \<Phi>\<^sub>2' \<Longrightarrow>
       (\<Gamma>\<^sub>1', n\<^sub>1' \<turnstile> \<Psi>\<^sub>1' \<triangleright> \<Phi>\<^sub>1') = \<Gamma>, n \<turnstile> (K\<^sub>1 implies K\<^sub>2) # \<Psi> \<triangleright> \<Phi> \<Longrightarrow>
       (\<Gamma>\<^sub>2', n\<^sub>2' \<turnstile> \<Psi>\<^sub>2' \<triangleright> \<Phi>\<^sub>2') = K\<^sub>1 \<not>\<Up> n # \<Gamma>, n \<turnstile> \<Psi> \<triangleright> (K\<^sub>1 implies K\<^sub>2) # \<Phi> \<Longrightarrow>
       \<lbrakk>\<lbrakk> \<Gamma>\<^sub>2 \<rbrakk>\<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n \<inter> \<lbrakk>\<lbrakk> \<Psi>\<^sub>2 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^sub>2\<^esup> \<inter> \<lbrakk>\<lbrakk> \<Phi>\<^sub>2 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^sub>2\<^esup>
       \<subseteq> \<lbrakk>\<lbrakk> \<Gamma>\<^sub>1 \<rbrakk>\<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n \<inter> \<lbrakk>\<lbrakk> \<Psi>\<^sub>1 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^sub>1\<^esup> \<inter> \<lbrakk>\<lbrakk> \<Phi>\<^sub>1 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^sub>1\<^esup>"
      using HeronConf_interp_at_index_implies_cases by auto
    show "\<And>\<Gamma>\<^sub>1' n\<^sub>1' \<Psi>\<^sub>1' \<Phi>\<^sub>1' \<Gamma>\<^sub>2' n\<^sub>2' \<Psi>\<^sub>2' \<Phi>\<^sub>2' \<Gamma> n K\<^sub>1 K\<^sub>2 \<Psi> \<Phi>.
       (\<Gamma>\<^sub>1, n\<^sub>1 \<turnstile> \<Psi>\<^sub>1 \<triangleright> \<Phi>\<^sub>1) = (\<Gamma>\<^sub>1', n\<^sub>1' \<turnstile> \<Psi>\<^sub>1' \<triangleright> \<Phi>\<^sub>1') \<Longrightarrow>
       (\<Gamma>\<^sub>2, n\<^sub>2 \<turnstile> \<Psi>\<^sub>2 \<triangleright> \<Phi>\<^sub>2) = (\<Gamma>\<^sub>2', n\<^sub>2' \<turnstile> \<Psi>\<^sub>2' \<triangleright> \<Phi>\<^sub>2') \<Longrightarrow>
       (\<Gamma>\<^sub>1', n\<^sub>1' \<turnstile> \<Psi>\<^sub>1' \<triangleright> \<Phi>\<^sub>1') = (\<Gamma>, n \<turnstile> (K\<^sub>1 implies K\<^sub>2) # \<Psi> \<triangleright> \<Phi>) \<Longrightarrow>
       (\<Gamma>\<^sub>2', n\<^sub>2' \<turnstile> \<Psi>\<^sub>2' \<triangleright> \<Phi>\<^sub>2') = (K\<^sub>1 \<Up> n # K\<^sub>2 \<Up> n # \<Gamma>, n \<turnstile> \<Psi> \<triangleright> (K\<^sub>1 implies K\<^sub>2) # \<Phi>) \<Longrightarrow>
       \<lbrakk>\<lbrakk> \<Gamma>\<^sub>2 \<rbrakk>\<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n \<inter> \<lbrakk>\<lbrakk> \<Psi>\<^sub>2 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^sub>2\<^esup> \<inter> \<lbrakk>\<lbrakk> \<Phi>\<^sub>2 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^sub>2\<^esup>
       \<subseteq> \<lbrakk>\<lbrakk> \<Gamma>\<^sub>1 \<rbrakk>\<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n \<inter> \<lbrakk>\<lbrakk> \<Psi>\<^sub>1 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^sub>1\<^esup> \<inter> \<lbrakk>\<lbrakk> \<Phi>\<^sub>1 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^sub>1\<^esup>"
      using HeronConf_interp_at_index_implies_cases by auto
    show "\<And>\<Gamma>\<^sub>1' n\<^sub>1' \<Psi>\<^sub>1' \<Phi>\<^sub>1' \<Gamma>\<^sub>2' n\<^sub>2' \<Psi>\<^sub>2' \<Phi>\<^sub>2' \<Gamma> n K\<^sub>1 \<delta>\<tau> K\<^sub>2 K\<^sub>3 \<Psi> \<Phi>.
       (\<Gamma>\<^sub>1, n\<^sub>1 \<turnstile> \<Psi>\<^sub>1 \<triangleright> \<Phi>\<^sub>1) = (\<Gamma>\<^sub>1', n\<^sub>1' \<turnstile> \<Psi>\<^sub>1' \<triangleright> \<Phi>\<^sub>1') \<Longrightarrow>
       (\<Gamma>\<^sub>2, n\<^sub>2 \<turnstile> \<Psi>\<^sub>2 \<triangleright> \<Phi>\<^sub>2) = (\<Gamma>\<^sub>2', n\<^sub>2' \<turnstile> \<Psi>\<^sub>2' \<triangleright> \<Phi>\<^sub>2') \<Longrightarrow>
       (\<Gamma>\<^sub>1', n\<^sub>1' \<turnstile> \<Psi>\<^sub>1' \<triangleright> \<Phi>\<^sub>1') = \<Gamma>, n \<turnstile> (K\<^sub>1 time-delayed by \<delta>\<tau> on K\<^sub>2 implies K\<^sub>3) # \<Psi> \<triangleright> \<Phi> \<Longrightarrow>
       (\<Gamma>\<^sub>2', n\<^sub>2' \<turnstile> \<Psi>\<^sub>2' \<triangleright> \<Phi>\<^sub>2') =
       K\<^sub>1 \<not>\<Up> n # \<Gamma>, n \<turnstile> \<Psi> \<triangleright> (K\<^sub>1 time-delayed by \<delta>\<tau> on K\<^sub>2 implies K\<^sub>3) # \<Phi> \<Longrightarrow>
       \<lbrakk>\<lbrakk> \<Gamma>\<^sub>2 \<rbrakk>\<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n \<inter> \<lbrakk>\<lbrakk> \<Psi>\<^sub>2 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^sub>2\<^esup> \<inter> \<lbrakk>\<lbrakk> \<Phi>\<^sub>2 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^sub>2\<^esup>
       \<subseteq> \<lbrakk>\<lbrakk> \<Gamma>\<^sub>1 \<rbrakk>\<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n \<inter> \<lbrakk>\<lbrakk> \<Psi>\<^sub>1 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^sub>1\<^esup> \<inter> \<lbrakk>\<lbrakk> \<Phi>\<^sub>1 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^sub>1\<^esup>"
      using HeronConf_interp_at_index_timedelayed_cases by auto
    show "\<And>\<Gamma>\<^sub>1' n\<^sub>1' \<Psi>\<^sub>1' \<Phi>\<^sub>1' \<Gamma>\<^sub>2' n\<^sub>2' \<Psi>\<^sub>2' \<Phi>\<^sub>2' \<Gamma> n K\<^sub>1 \<delta>\<tau> K\<^sub>2 K\<^sub>3 \<Psi> \<Phi>.
       (\<Gamma>\<^sub>1, n\<^sub>1 \<turnstile> \<Psi>\<^sub>1 \<triangleright> \<Phi>\<^sub>1) = (\<Gamma>\<^sub>1', n\<^sub>1' \<turnstile> \<Psi>\<^sub>1' \<triangleright> \<Phi>\<^sub>1') \<Longrightarrow>
       (\<Gamma>\<^sub>2, n\<^sub>2 \<turnstile> \<Psi>\<^sub>2 \<triangleright> \<Phi>\<^sub>2) = (\<Gamma>\<^sub>2', n\<^sub>2' \<turnstile> \<Psi>\<^sub>2' \<triangleright> \<Phi>\<^sub>2') \<Longrightarrow>
       (\<Gamma>\<^sub>1', n\<^sub>1' \<turnstile> \<Psi>\<^sub>1' \<triangleright> \<Phi>\<^sub>1') = \<Gamma>, n \<turnstile> (K\<^sub>1 time-delayed by \<delta>\<tau> on K\<^sub>2 implies K\<^sub>3) # \<Psi> \<triangleright> \<Phi> \<Longrightarrow>
       (\<Gamma>\<^sub>2', n\<^sub>2' \<turnstile> \<Psi>\<^sub>2' \<triangleright> \<Phi>\<^sub>2') =
       K\<^sub>1 \<Up> n #
       \<Gamma>, n \<turnstile> (K\<^sub>3 sporadic \<lfloor> \<tau>\<^sub>v\<^sub>a\<^sub>r (K\<^sub>2, n) \<oplus> \<delta>\<tau> \<rfloor> on K\<^sub>2) #
               \<Psi> \<triangleright> (K\<^sub>1 time-delayed by \<delta>\<tau> on K\<^sub>2 implies K\<^sub>3) # \<Phi> \<Longrightarrow>
       \<lbrakk>\<lbrakk> \<Gamma>\<^sub>2 \<rbrakk>\<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n \<inter> \<lbrakk>\<lbrakk> \<Psi>\<^sub>2 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^sub>2\<^esup> \<inter> \<lbrakk>\<lbrakk> \<Phi>\<^sub>2 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^sub>2\<^esup>
       \<subseteq> \<lbrakk>\<lbrakk> \<Gamma>\<^sub>1 \<rbrakk>\<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n \<inter> \<lbrakk>\<lbrakk> \<Psi>\<^sub>1 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^sub>1\<^esup> \<inter> \<lbrakk>\<lbrakk> \<Phi>\<^sub>1 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^sub>1\<^esup>"
      using HeronConf_interp_at_index_timedelayed_cases by auto
    qed
  qed

theorem soundness':
  assumes "\<S>\<^sub>1 \<hookrightarrow> \<S>\<^sub>2"
  shows "\<lbrakk> \<S>\<^sub>1 \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g \<supseteq> \<lbrakk> \<S>\<^sub>2 \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g"
  by (metis soundness HeronConf_interpretation.elims assms)

theorem soundness_generalized:
  assumes "\<S>\<^sub>1 \<hookrightarrow>\<^bsup>n\<^esup> \<S>\<^sub>2"
  shows "\<lbrakk> \<S>\<^sub>1 \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g \<supseteq> \<lbrakk> \<S>\<^sub>2 \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g"
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
      assume hi: "\<And>\<S>\<^sub>2. \<S>\<^sub>1 \<hookrightarrow>\<^bsup>n\<^esup> \<S>\<^sub>2 \<Longrightarrow> \<lbrakk> \<S>\<^sub>2 \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g \<subseteq> \<lbrakk> \<S>\<^sub>1 \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g"
      obtain \<S>\<^sub>n where red_decomp: "\<S>\<^sub>1 \<hookrightarrow>\<^bsup>n\<^esup> \<S>\<^sub>n \<and> \<S>\<^sub>n \<hookrightarrow> \<S>\<^sub>2"
        using ff by auto
      then have "\<lbrakk> \<S>\<^sub>1 \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g \<supseteq> \<lbrakk> \<S>\<^sub>n \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g"
        using hi by (metis (no_types, lifting) ff relpowp_Suc_E someI_ex)
      also have "\<lbrakk> \<S>\<^sub>n \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g \<supseteq> \<lbrakk> \<S>\<^sub>2 \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g"
        by (simp add: red_decomp soundness')
      ultimately show "\<lbrakk> \<S>\<^sub>1 \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g \<supseteq> \<lbrakk> \<S>\<^sub>2 \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g"
        by auto
      qed
  qed

section \<open>Completeness\<close>

theorem completeness:
  shows "\<lbrakk> \<Gamma>, n \<turnstile> \<Psi> \<triangleright> \<Phi> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g \<subseteq> (\<Union>X\<in>\<F>\<^sub>n\<^sub>e\<^sub>x\<^sub>t (\<Gamma>, n \<turnstile> \<Psi> \<triangleright> \<Phi>). \<lbrakk> X \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g)"
  proof (induct \<Psi>)
    case Nil
    show ?case
      using HeronConf_interp_at_index_instant_cases operational_semantics_step.simps operational_semantics_intro.instant_i
      by fastforce
  next
    case (Cons \<psi> \<Psi>)
    then show ?case
      proof (induct \<psi>)
        case (Sporadic K \<tau>)
        then show ?case
          using HeronConf_interp_at_index_sporadic_cases Fnext_solve_sporadic
          by (smt UN_iff UnE insert_subset subsetI)
      next
        case (SporadicOn K1 \<tau> K2)
        then show ?case 
          using HeronConf_interp_at_index_sporadicon_cases Fnext_solve_sporadicon
          by (smt UN_iff UnE insert_subset subsetI)
      next
        case (TagRelation K1 \<alpha> K2 \<beta>)
        then show ?case
          using HeronConf_interp_at_index_tagrel_cases Fnext_solve_tagrel
          by (smt UN_iff UnE insert_subset subsetI)
      next
        case (Implies K1 K2)
        then show ?case
          using HeronConf_interp_at_index_implies_cases Fnext_solve_implies
          by (smt UN_iff UnE insert_subset subsetI)
      next
        case (TimeDelayedBy Kmast \<tau> Kmeas Kslave)
        then show ?case
          using HeronConf_interp_at_index_timedelayed_cases Fnext_solve_timedelayed
          by (smt UN_iff UnE insert_subset subsetI)
      qed
  qed

theorem completeness':
  shows "\<lbrakk> \<S> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g \<subseteq> (\<Union>X\<in>\<F>\<^sub>n\<^sub>e\<^sub>x\<^sub>t \<S>. \<lbrakk> X \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g)"
  by (metis HeronConf_interpretation.cases completeness)

(*
theorem completeness'':
  assumes "\<rho> \<in> \<lbrakk> \<Gamma>\<^sub>1, n\<^sub>1 \<turnstile> \<Psi>\<^sub>1 \<triangleright> \<Phi>\<^sub>1 \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g"
  shows "\<exists>\<Gamma>\<^sub>2 n\<^sub>2 \<Psi>\<^sub>2 \<Phi>\<^sub>2. \<Gamma>\<^sub>1, n\<^sub>1 \<turnstile> \<Psi>\<^sub>1 \<triangleright> \<Phi>\<^sub>1 \<hookrightarrow> \<Gamma>\<^sub>2, n\<^sub>2 \<turnstile> \<Psi>\<^sub>2 \<triangleright> \<Phi>\<^sub>2
           \<and> \<rho> \<in> \<lbrakk> \<Gamma>\<^sub>2, n\<^sub>2 \<turnstile> \<Psi>\<^sub>2 \<triangleright> \<Phi>\<^sub>2 \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g"
  proof (insert assms, induct \<Psi>\<^sub>1)
    case Nil
    have "\<rho> \<in> \<lbrakk> \<Gamma>\<^sub>1, Suc n\<^sub>1 \<turnstile> \<Phi>\<^sub>1 \<triangleright> [] \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g"
      using assms HeronConf_interp_at_index_instant_cases by auto
    moreover have "\<Gamma>\<^sub>1, n\<^sub>1 \<turnstile> [] \<triangleright> \<Phi>\<^sub>1 \<hookrightarrow> \<Gamma>\<^sub>1, Suc n\<^sub>1 \<turnstile> \<Phi>\<^sub>1 \<triangleright> []"
      using intro_part operational_semantics_intro.instant_i by auto
    ultimately show ?case by blast
  next
    case (Cons \<psi>\<^sub>1 \<Psi>\<^sub>1)
    then show ?case
      proof (induct \<psi>\<^sub>1)
        case (Sporadic x1 x2)
        then show ?case
          using HeronConf_interp_at_index_sporadic_cases
          by (metis UnE elims_part sporadic_e1 sporadic_e2)
      next
        case (SporadicOn x1 x2 x3)
        then show ?case
          using HeronConf_interp_at_index_sporadicon_cases
          by (metis UnE elims_part sporadic_on_e1 sporadic_on_e2)
      next
        case (TagRelation x1 x2 x3 x4)
        then show ?case
          using HeronConf_interp_at_index_tagrel_cases
          by (metis elims_part tagrel_e)
      next
        case (Implies x1 x2)
        then show ?case
          using HeronConf_interp_at_index_implies_cases
          by (metis UnE elims_part implies_e1 implies_e2)
      next
        case (TimeDelayedBy x1 x2 x3 x4)
        then show ?case
          using HeronConf_interp_at_index_timedelayed_cases
          by (metis UnE elims_part timedelayed_e1 timedelayed_e2)
      qed
  qed
*)

theorem completeness''':
  assumes "\<rho> \<in> \<lbrakk> \<S>\<^sub>1 \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g"
  shows "\<exists>\<S>\<^sub>2. \<S>\<^sub>1 \<hookrightarrow> \<S>\<^sub>2 \<and> \<rho> \<in> \<lbrakk> \<S>\<^sub>2 \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g"
  by (metis (mono_tags, lifting) UN_iff assms completeness' mem_Collect_eq set_rev_mp)

theorem completeness'''':
  assumes "\<rho> \<in> \<lbrakk> [], 0 \<turnstile> \<Psi> \<triangleright> [] \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g"
  shows "\<exists>\<S>. [], 0 \<turnstile> \<Psi> \<triangleright> [] \<hookrightarrow>\<^bsup>n\<^esup> \<S> \<and> \<rho> \<in> \<lbrakk> \<S> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g"
  sorry

section \<open>Termination of instant computation\<close>

(* Idea: A bounded monotonic sequence is convergent *)
primrec measure_interpretation :: "TESL_formula \<Rightarrow> nat" ("\<mu>") where
    "\<mu> [] = (0::nat)"
  | "\<mu> (\<phi> # \<Phi>) = (case \<phi> of
                        _ sporadic _ on _ \<Rightarrow> 1 + \<mu> \<Phi>
                      | _                 \<Rightarrow> 2 + \<mu> \<Phi>)"

fun measure_interpretation_config :: "config \<Rightarrow> nat" ("\<mu>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g") where
    "\<mu>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g (\<Gamma>, n \<turnstile> \<Psi> \<triangleright> \<Phi>) = \<mu> \<Psi>"

lemma elimation_rules_strictly_decreasing:
  assumes "\<Gamma>\<^sub>1, n\<^sub>1 \<turnstile> \<Psi>\<^sub>1 \<triangleright> \<Phi>\<^sub>1  \<hookrightarrow>\<^sub>e  \<Gamma>\<^sub>2, n\<^sub>2 \<turnstile> \<Psi>\<^sub>2 \<triangleright> \<Phi>\<^sub>2"
  shows "\<mu> \<Psi>\<^sub>1 > \<mu> \<Psi>\<^sub>2"
  by (insert assms, erule operational_semantics_elim.cases, auto)

lemma elimation_rules_strictly_decreasing_meas:
  assumes "\<Gamma>\<^sub>1, n\<^sub>1 \<turnstile> \<Psi>\<^sub>1 \<triangleright> \<Phi>\<^sub>1  \<hookrightarrow>\<^sub>e  \<Gamma>\<^sub>2, n\<^sub>2 \<turnstile> \<Psi>\<^sub>2 \<triangleright> \<Phi>\<^sub>2"
  shows "(\<Psi>\<^sub>2, \<Psi>\<^sub>1) \<in> measure \<mu>"
  by (insert assms, erule operational_semantics_elim.cases, auto)

lemma elimation_rules_strictly_decreasing_meas':
  assumes "\<S>\<^sub>1  \<hookrightarrow>\<^sub>e  \<S>\<^sub>2"
  shows "(\<S>\<^sub>2, \<S>\<^sub>1) \<in> measure \<mu>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g"
  using elimation_rules_strictly_decreasing_meas
  by (metis assms in_measure measure_interpretation_config.elims)

theorem instant_computation_termination:
  shows "wfP (\<lambda>\<S>\<^sub>1 \<S>\<^sub>2. \<S>\<^sub>1 \<hookrightarrow>\<^sub>e\<^sup>\<leftarrow> \<S>\<^sub>2)"
  proof (simp add: wfP_def)
    show "wf {(\<S>\<^sub>1, \<S>\<^sub>2). \<S>\<^sub>1 \<hookrightarrow>\<^sub>e\<^sup>\<leftarrow> \<S>\<^sub>2}"
    apply (rule wf_subset)
    proof -
      have "measure \<mu>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g = { (\<S>\<^sub>2, \<S>\<^sub>1). \<mu>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g \<S>\<^sub>2 < \<mu>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g \<S>\<^sub>1 }"
        by (simp add: inv_image_def less_eq measure_def)
      then show "{(\<S>\<^sub>1, \<S>\<^sub>2). \<S>\<^sub>1 \<hookrightarrow>\<^sub>e\<^sup>\<leftarrow> \<S>\<^sub>2} \<subseteq> (measure \<mu>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g)"
        using elimation_rules_strictly_decreasing_meas' operational_semantics_elim_inv_def by auto
      show "wf (measure measure_interpretation_config)"
        by simp
    qed
  qed

section \<open>Progress\<close>

lemma run_index_increase:
  assumes "\<Gamma>\<^sub>1, n\<^sub>1 \<turnstile> \<Psi>\<^sub>1 \<triangleright> \<Phi>\<^sub>1  \<hookrightarrow>  \<Gamma>\<^sub>2, n\<^sub>2 \<turnstile> \<Psi>\<^sub>2 \<triangleright> \<Phi>\<^sub>2"
  shows "n\<^sub>2 = Suc n\<^sub>1 \<or> n\<^sub>2 = n\<^sub>1"
  apply (insert assms, erule operational_semantics_step.cases)
  proof -
  show "\<And>\<Gamma>\<^sub>1' n\<^sub>1' \<Psi>\<^sub>1' \<Phi>\<^sub>1' \<Gamma>\<^sub>2' n\<^sub>2' \<Psi>\<^sub>2' \<Phi>\<^sub>2'.
       \<Gamma>\<^sub>1, n\<^sub>1 \<turnstile> \<Psi>\<^sub>1 \<triangleright> \<Phi>\<^sub>1 = \<Gamma>\<^sub>1', n\<^sub>1' \<turnstile> \<Psi>\<^sub>1' \<triangleright> \<Phi>\<^sub>1' \<Longrightarrow>
       \<Gamma>\<^sub>2, n\<^sub>2 \<turnstile> \<Psi>\<^sub>2 \<triangleright> \<Phi>\<^sub>2 = \<Gamma>\<^sub>2', n\<^sub>2' \<turnstile> \<Psi>\<^sub>2' \<triangleright> \<Phi>\<^sub>2' \<Longrightarrow>
       \<Gamma>\<^sub>1', n\<^sub>1' \<turnstile> \<Psi>\<^sub>1' \<triangleright> \<Phi>\<^sub>1' \<hookrightarrow>\<^sub>i \<Gamma>\<^sub>2', n\<^sub>2' \<turnstile> \<Psi>\<^sub>2' \<triangleright> \<Phi>\<^sub>2' \<Longrightarrow> n\<^sub>2 = Suc n\<^sub>1 \<or> n\<^sub>2 = n\<^sub>1"
    by (simp add: operational_semantics_intro.simps)
  show "\<And>\<Gamma>\<^sub>1' n\<^sub>1' \<Psi>\<^sub>1' \<Phi>\<^sub>1' \<Gamma>\<^sub>2' n\<^sub>2' \<Psi>\<^sub>2' \<Phi>\<^sub>2'.
       \<Gamma>\<^sub>1, n\<^sub>1 \<turnstile> \<Psi>\<^sub>1 \<triangleright> \<Phi>\<^sub>1 = \<Gamma>\<^sub>1', n\<^sub>1' \<turnstile> \<Psi>\<^sub>1' \<triangleright> \<Phi>\<^sub>1' \<Longrightarrow>
       \<Gamma>\<^sub>2, n\<^sub>2 \<turnstile> \<Psi>\<^sub>2 \<triangleright> \<Phi>\<^sub>2 = \<Gamma>\<^sub>2', n\<^sub>2' \<turnstile> \<Psi>\<^sub>2' \<triangleright> \<Phi>\<^sub>2' \<Longrightarrow>
       \<Gamma>\<^sub>1', n\<^sub>1' \<turnstile> \<Psi>\<^sub>1' \<triangleright> \<Phi>\<^sub>1' \<hookrightarrow>\<^sub>e \<Gamma>\<^sub>2', n\<^sub>2' \<turnstile> \<Psi>\<^sub>2' \<triangleright> \<Phi>\<^sub>2' \<Longrightarrow> n\<^sub>2 = Suc n\<^sub>1 \<or> n\<^sub>2 = n\<^sub>1"
    using operational_semantics_elim.simps by auto
  qed

lemma progress:
  shows "\<exists>\<Gamma>\<^sub>2 n\<^sub>2 \<Psi>\<^sub>2 \<Phi>\<^sub>2. \<Gamma>\<^sub>1, n\<^sub>1 \<turnstile> \<Psi>\<^sub>1 \<triangleright> \<Phi>\<^sub>1  \<hookrightarrow>  \<Gamma>\<^sub>2, n\<^sub>2 \<turnstile> \<Psi>\<^sub>2 \<triangleright> \<Phi>\<^sub>2"
  proof (induct \<Psi>\<^sub>1)
    case Nil
    then show ?case
      using intro_part operational_semantics_intro.instant_i by blast
  next
    case (Cons \<psi>\<^sub>1 \<Psi>\<^sub>1)
    then show ?case
      proof (induct \<psi>\<^sub>1)
        case (Sporadic x1 x2)
        then show ?case
          using elims_part operational_semantics_elim.sporadic_e1 by blast
      next
        case (SporadicOn x1 x2 x3)
        then show ?case
          using elims_part operational_semantics_elim.sporadic_on_e1 by blast
      next
        case (TagRelation x1 x2 x3 x4)
        then show ?case
          using elims_part operational_semantics_elim.tagrel_e by blast
      next
        case (Implies x1 x2)
        then show ?case
          using elims_part operational_semantics_elim.implies_e1 by blast
      next
        case (TimeDelayedBy x1 x2 x3 x4)
  then show ?case
    using elims_part operational_semantics_elim.timedelayed_e1 by blast
      qed
  qed

(* Elementaire, simple par définition de \<rightarrow>\<^sub>\<nabla> *)
lemma run_index_progress_simlstep:
  assumes "\<Gamma>\<^sub>1, n\<^sub>1 \<turnstile> \<Psi>\<^sub>1 \<triangleright> \<Phi>\<^sub>1  \<hookrightarrow>\<^sub>\<nabla>  \<Gamma>\<^sub>2, n\<^sub>2 \<turnstile> \<Psi>\<^sub>2 \<triangleright> \<Phi>\<^sub>2"
  shows "n\<^sub>2 = Suc n\<^sub>1"
  using assms
  by (simp add: operational_semantics_simlstep.simps)

(**) section \<open>Composition\<close> (**)

lemma composition:
  shows "\<lbrakk> \<Gamma>\<^sub>1, n \<turnstile> \<Psi>\<^sub>1 \<triangleright> \<Phi>\<^sub>1 \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g \<inter> \<lbrakk> \<Gamma>\<^sub>2, n \<turnstile> \<Psi>\<^sub>2 \<triangleright> \<Phi>\<^sub>2 \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g
         = \<lbrakk> \<Gamma>\<^sub>1 @ \<Gamma>\<^sub>2, n \<turnstile> \<Psi>\<^sub>1 @ \<Psi>\<^sub>2 \<triangleright> \<Phi>\<^sub>1 @ \<Phi>\<^sub>2 \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g"
  using TESL_interp_at_index_composition symrun_interp_expansion by auto

(**) section \<open>Semidecidability\<close> (**)
(* The set of runs hence becomes recursively countable due to the previous observations. *)

(**) section \<open>Existence\<close> (**)
lemma existence:
  (* Assumption that the linear system made of tag relations is consistent *)
  assumes "tagrel_consistent \<Phi>"
  shows "\<exists>\<rho>. \<rho> \<in> \<lbrakk>\<lbrakk> \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L"
  oops
  (* proof (induction \<Phi>) *)

end