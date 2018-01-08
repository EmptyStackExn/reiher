theory Hygge_Theory
imports
  "Coinductive_Prop"

begin

section \<open>Initial configuration\<close>

text \<open>Solving a specification [\<Psi>] means to start operational semantics at initial configuration [], 0 \<turnstile> \<Psi> \<triangleright> []\<close>
theorem solve_start:
  shows "\<lbrakk>\<lbrakk> \<Psi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L = \<lbrakk> [], 0 \<turnstile> \<Psi> \<triangleright> [] \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g"
  proof -
    have "\<lbrakk>\<lbrakk> \<Psi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L = \<lbrakk>\<lbrakk> \<Psi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> 0\<^esup>"
    by (simp add: TESL_interpretation_stepwise_zero')
    moreover have "\<lbrakk> [], 0 \<turnstile> \<Psi> \<triangleright> [] \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g = \<lbrakk>\<lbrakk> [] \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m \<inter> \<lbrakk>\<lbrakk> \<Psi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> 0\<^esup> \<inter> \<lbrakk>\<lbrakk> [] \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc 0\<^esup>"
    by simp
    ultimately show ?thesis by auto
  qed

section \<open>Soundness\<close>

lemma sound_reduction:
  assumes "\<Gamma>\<^sub>1, n\<^sub>1 \<turnstile> \<Psi>\<^sub>1 \<triangleright> \<Phi>\<^sub>1  \<hookrightarrow>  \<Gamma>\<^sub>2, n\<^sub>2 \<turnstile> \<Psi>\<^sub>2 \<triangleright> \<Phi>\<^sub>2"
  shows "\<lbrakk>\<lbrakk> \<Gamma>\<^sub>1 \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m \<inter> \<lbrakk>\<lbrakk> \<Psi>\<^sub>1 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^sub>1\<^esup> \<inter> \<lbrakk>\<lbrakk> \<Phi>\<^sub>1 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^sub>1\<^esup>
          \<supseteq>  \<lbrakk>\<lbrakk> \<Gamma>\<^sub>2 \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m \<inter> \<lbrakk>\<lbrakk> \<Psi>\<^sub>2 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^sub>2\<^esup> \<inter> \<lbrakk>\<lbrakk> \<Phi>\<^sub>2 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^sub>2\<^esup>"
  proof (insert assms, erule operational_semantics_step.cases)
  show "\<And>\<Gamma>\<^sub>1' n\<^sub>1' \<Psi>\<^sub>1' \<Phi>\<^sub>1' \<Gamma>\<^sub>2' n\<^sub>2' \<Psi>\<^sub>2' \<Phi>\<^sub>2'.
       \<Gamma>\<^sub>1, n\<^sub>1 \<turnstile> \<Psi>\<^sub>1 \<triangleright> \<Phi>\<^sub>1 = \<Gamma>\<^sub>1', n\<^sub>1' \<turnstile> \<Psi>\<^sub>1' \<triangleright> \<Phi>\<^sub>1' \<Longrightarrow>
       \<Gamma>\<^sub>2, n\<^sub>2 \<turnstile> \<Psi>\<^sub>2 \<triangleright> \<Phi>\<^sub>2 = \<Gamma>\<^sub>2', n\<^sub>2' \<turnstile> \<Psi>\<^sub>2' \<triangleright> \<Phi>\<^sub>2' \<Longrightarrow>
       \<Gamma>\<^sub>1', n\<^sub>1' \<turnstile> \<Psi>\<^sub>1' \<triangleright> \<Phi>\<^sub>1' \<hookrightarrow>\<^sub>i \<Gamma>\<^sub>2', n\<^sub>2' \<turnstile> \<Psi>\<^sub>2' \<triangleright> \<Phi>\<^sub>2' \<Longrightarrow>
       \<lbrakk>\<lbrakk> \<Gamma>\<^sub>2 \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m \<inter> \<lbrakk>\<lbrakk> \<Psi>\<^sub>2 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^sub>2\<^esup> \<inter> \<lbrakk>\<lbrakk> \<Phi>\<^sub>2 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^sub>2\<^esup>
       \<subseteq> \<lbrakk>\<lbrakk> \<Gamma>\<^sub>1 \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m \<inter> \<lbrakk>\<lbrakk> \<Psi>\<^sub>1 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^sub>1\<^esup> \<inter> \<lbrakk>\<lbrakk> \<Phi>\<^sub>1 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^sub>1\<^esup>"
    by (erule operational_semantics_intro.cases, auto)
  show "\<And>\<Gamma>\<^sub>1' n\<^sub>1' \<Psi>\<^sub>1' \<Phi>\<^sub>1' \<Gamma>\<^sub>2' n\<^sub>2' \<Psi>\<^sub>2' \<Phi>\<^sub>2'.
       \<Gamma>\<^sub>1, n\<^sub>1 \<turnstile> \<Psi>\<^sub>1 \<triangleright> \<Phi>\<^sub>1 = \<Gamma>\<^sub>1', n\<^sub>1' \<turnstile> \<Psi>\<^sub>1' \<triangleright> \<Phi>\<^sub>1' \<Longrightarrow>
       \<Gamma>\<^sub>2, n\<^sub>2 \<turnstile> \<Psi>\<^sub>2 \<triangleright> \<Phi>\<^sub>2 = \<Gamma>\<^sub>2', n\<^sub>2' \<turnstile> \<Psi>\<^sub>2' \<triangleright> \<Phi>\<^sub>2' \<Longrightarrow>
       \<Gamma>\<^sub>1', n\<^sub>1' \<turnstile> \<Psi>\<^sub>1' \<triangleright> \<Phi>\<^sub>1' \<hookrightarrow>\<^sub>e \<Gamma>\<^sub>2', n\<^sub>2' \<turnstile> \<Psi>\<^sub>2' \<triangleright> \<Phi>\<^sub>2' \<Longrightarrow>
       \<lbrakk>\<lbrakk> \<Gamma>\<^sub>2 \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m \<inter> \<lbrakk>\<lbrakk> \<Psi>\<^sub>2 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^sub>2\<^esup> \<inter> \<lbrakk>\<lbrakk> \<Phi>\<^sub>2 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^sub>2\<^esup>
       \<subseteq> \<lbrakk>\<lbrakk> \<Gamma>\<^sub>1 \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m \<inter> \<lbrakk>\<lbrakk> \<Psi>\<^sub>1 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^sub>1\<^esup> \<inter> \<lbrakk>\<lbrakk> \<Phi>\<^sub>1 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^sub>1\<^esup>"
    proof (erule operational_semantics_elim.cases)
    show "\<And>\<Gamma>\<^sub>1' n\<^sub>1' \<Psi>\<^sub>1' \<Phi>\<^sub>1' \<Gamma>\<^sub>2' n\<^sub>2' \<Psi>\<^sub>2' \<Phi>\<^sub>2' \<Gamma> n K \<tau> \<Psi> \<Phi>.
       (\<Gamma>\<^sub>1, n\<^sub>1 \<turnstile> \<Psi>\<^sub>1 \<triangleright> \<Phi>\<^sub>1) = (\<Gamma>\<^sub>1', n\<^sub>1' \<turnstile> \<Psi>\<^sub>1' \<triangleright> \<Phi>\<^sub>1') \<Longrightarrow>
       (\<Gamma>\<^sub>2, n\<^sub>2 \<turnstile> \<Psi>\<^sub>2 \<triangleright> \<Phi>\<^sub>2) = (\<Gamma>\<^sub>2', n\<^sub>2' \<turnstile> \<Psi>\<^sub>2' \<triangleright> \<Phi>\<^sub>2') \<Longrightarrow>
       (\<Gamma>\<^sub>1', n\<^sub>1' \<turnstile> \<Psi>\<^sub>1' \<triangleright> \<Phi>\<^sub>1') = (\<Gamma>, n \<turnstile> (K sporadic \<tau>) # \<Psi> \<triangleright> \<Phi>) \<Longrightarrow>
       (\<Gamma>\<^sub>2', n\<^sub>2' \<turnstile> \<Psi>\<^sub>2' \<triangleright> \<Phi>\<^sub>2') = (\<Gamma>, n \<turnstile> \<Psi> \<triangleright> (K sporadic \<tau>) # \<Phi>) \<Longrightarrow>
       \<lbrakk>\<lbrakk> \<Gamma>\<^sub>2 \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m \<inter> \<lbrakk>\<lbrakk> \<Psi>\<^sub>2 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^sub>2\<^esup> \<inter> \<lbrakk>\<lbrakk> \<Phi>\<^sub>2 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^sub>2\<^esup>
       \<subseteq> \<lbrakk>\<lbrakk> \<Gamma>\<^sub>1 \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m \<inter> \<lbrakk>\<lbrakk> \<Psi>\<^sub>1 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^sub>1\<^esup> \<inter> \<lbrakk>\<lbrakk> \<Phi>\<^sub>1 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^sub>1\<^esup>"
      using HeronConf_interp_stepwise_sporadic_cases
      by (metis HeronConf_interpretation.simps Un_upper1)
    show "\<And>\<Gamma>\<^sub>1' n\<^sub>1' \<Psi>\<^sub>1' \<Phi>\<^sub>1' \<Gamma>\<^sub>2' n\<^sub>2' \<Psi>\<^sub>2' \<Phi>\<^sub>2' \<Gamma> n K \<tau> \<Psi> \<Phi>.
       (\<Gamma>\<^sub>1, n\<^sub>1 \<turnstile> \<Psi>\<^sub>1 \<triangleright> \<Phi>\<^sub>1) = (\<Gamma>\<^sub>1', n\<^sub>1' \<turnstile> \<Psi>\<^sub>1' \<triangleright> \<Phi>\<^sub>1') \<Longrightarrow>
       (\<Gamma>\<^sub>2, n\<^sub>2 \<turnstile> \<Psi>\<^sub>2 \<triangleright> \<Phi>\<^sub>2) = (\<Gamma>\<^sub>2', n\<^sub>2' \<turnstile> \<Psi>\<^sub>2' \<triangleright> \<Phi>\<^sub>2') \<Longrightarrow>
       (\<Gamma>\<^sub>1', n\<^sub>1' \<turnstile> \<Psi>\<^sub>1' \<triangleright> \<Phi>\<^sub>1') = (\<Gamma>, n \<turnstile> (K sporadic \<tau>) # \<Psi> \<triangleright> \<Phi>) \<Longrightarrow>
       (\<Gamma>\<^sub>2', n\<^sub>2' \<turnstile> \<Psi>\<^sub>2' \<triangleright> \<Phi>\<^sub>2') = (K \<Up> n # K \<Down> n @ \<lfloor> \<tau> \<rfloor> # \<Gamma>, n \<turnstile> \<Psi> \<triangleright> \<Phi>) \<Longrightarrow>
       \<lbrakk>\<lbrakk> \<Gamma>\<^sub>2 \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m \<inter> \<lbrakk>\<lbrakk> \<Psi>\<^sub>2 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^sub>2\<^esup> \<inter> \<lbrakk>\<lbrakk> \<Phi>\<^sub>2 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^sub>2\<^esup>
       \<subseteq> \<lbrakk>\<lbrakk> \<Gamma>\<^sub>1 \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m \<inter> \<lbrakk>\<lbrakk> \<Psi>\<^sub>1 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^sub>1\<^esup> \<inter> \<lbrakk>\<lbrakk> \<Phi>\<^sub>1 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^sub>1\<^esup>"
      using HeronConf_interp_stepwise_sporadic_cases by auto
    show "\<And>\<Gamma>\<^sub>1' n\<^sub>1' \<Psi>\<^sub>1' \<Phi>\<^sub>1' \<Gamma>\<^sub>2' n\<^sub>2' \<Psi>\<^sub>2' \<Phi>\<^sub>2' \<Gamma> n K\<^sub>1 \<tau> K\<^sub>2 \<Psi> \<Phi>.
       (\<Gamma>\<^sub>1, n\<^sub>1 \<turnstile> \<Psi>\<^sub>1 \<triangleright> \<Phi>\<^sub>1) = (\<Gamma>\<^sub>1', n\<^sub>1' \<turnstile> \<Psi>\<^sub>1' \<triangleright> \<Phi>\<^sub>1') \<Longrightarrow>
       (\<Gamma>\<^sub>2, n\<^sub>2 \<turnstile> \<Psi>\<^sub>2 \<triangleright> \<Phi>\<^sub>2) = (\<Gamma>\<^sub>2', n\<^sub>2' \<turnstile> \<Psi>\<^sub>2' \<triangleright> \<Phi>\<^sub>2') \<Longrightarrow>
       (\<Gamma>\<^sub>1', n\<^sub>1' \<turnstile> \<Psi>\<^sub>1' \<triangleright> \<Phi>\<^sub>1') = (\<Gamma>, n \<turnstile> (K\<^sub>1 sporadic \<tau> on K\<^sub>2) # \<Psi> \<triangleright> \<Phi>) \<Longrightarrow>
       (\<Gamma>\<^sub>2', n\<^sub>2' \<turnstile> \<Psi>\<^sub>2' \<triangleright> \<Phi>\<^sub>2') = (\<Gamma>, n \<turnstile> \<Psi> \<triangleright> (K\<^sub>1 sporadic \<tau> on K\<^sub>2) # \<Phi>) \<Longrightarrow>
       \<lbrakk>\<lbrakk> \<Gamma>\<^sub>2 \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m \<inter> \<lbrakk>\<lbrakk> \<Psi>\<^sub>2 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^sub>2\<^esup> \<inter> \<lbrakk>\<lbrakk> \<Phi>\<^sub>2 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^sub>2\<^esup>
       \<subseteq> \<lbrakk>\<lbrakk> \<Gamma>\<^sub>1 \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m \<inter> \<lbrakk>\<lbrakk> \<Psi>\<^sub>1 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^sub>1\<^esup> \<inter> \<lbrakk>\<lbrakk> \<Phi>\<^sub>1 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^sub>1\<^esup>"
      using HeronConf_interp_stepwise_sporadicon_cases by fastforce
    show "\<And>\<Gamma>\<^sub>1' n\<^sub>1' \<Psi>\<^sub>1' \<Phi>\<^sub>1' \<Gamma>\<^sub>2' n\<^sub>2' \<Psi>\<^sub>2' \<Phi>\<^sub>2' \<Gamma> n K\<^sub>1 \<tau> K\<^sub>2 \<Psi> \<Phi>.
       (\<Gamma>\<^sub>1, n\<^sub>1 \<turnstile> \<Psi>\<^sub>1 \<triangleright> \<Phi>\<^sub>1) = (\<Gamma>\<^sub>1', n\<^sub>1' \<turnstile> \<Psi>\<^sub>1' \<triangleright> \<Phi>\<^sub>1') \<Longrightarrow>
       (\<Gamma>\<^sub>2, n\<^sub>2 \<turnstile> \<Psi>\<^sub>2 \<triangleright> \<Phi>\<^sub>2) = (\<Gamma>\<^sub>2', n\<^sub>2' \<turnstile> \<Psi>\<^sub>2' \<triangleright> \<Phi>\<^sub>2') \<Longrightarrow>
       (\<Gamma>\<^sub>1', n\<^sub>1' \<turnstile> \<Psi>\<^sub>1' \<triangleright> \<Phi>\<^sub>1') = (\<Gamma>, n \<turnstile> (K\<^sub>1 sporadic \<tau> on K\<^sub>2) # \<Psi> \<triangleright> \<Phi>) \<Longrightarrow>
       (\<Gamma>\<^sub>2', n\<^sub>2' \<turnstile> \<Psi>\<^sub>2' \<triangleright> \<Phi>\<^sub>2') = (K\<^sub>1 \<Up> n # K\<^sub>2 \<Down> n @ \<tau> # \<Gamma>, n \<turnstile> \<Psi> \<triangleright> \<Phi>) \<Longrightarrow>
       \<lbrakk>\<lbrakk> \<Gamma>\<^sub>2 \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m \<inter> \<lbrakk>\<lbrakk> \<Psi>\<^sub>2 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^sub>2\<^esup> \<inter> \<lbrakk>\<lbrakk> \<Phi>\<^sub>2 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^sub>2\<^esup>
       \<subseteq> \<lbrakk>\<lbrakk> \<Gamma>\<^sub>1 \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m \<inter> \<lbrakk>\<lbrakk> \<Psi>\<^sub>1 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^sub>1\<^esup> \<inter> \<lbrakk>\<lbrakk> \<Phi>\<^sub>1 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^sub>1\<^esup>"
      using HeronConf_interp_stepwise_sporadicon_cases
      by fastforce
    show "\<And>\<Gamma>\<^sub>1' n\<^sub>1' \<Psi>\<^sub>1' \<Phi>\<^sub>1' \<Gamma>\<^sub>2' n\<^sub>2' \<Psi>\<^sub>2' \<Phi>\<^sub>2' \<Gamma> n K\<^sub>1 \<alpha> K\<^sub>2 \<beta> \<Psi> \<Phi>.
       (\<Gamma>\<^sub>1, n\<^sub>1 \<turnstile> \<Psi>\<^sub>1 \<triangleright> \<Phi>\<^sub>1) = \<Gamma>\<^sub>1', n\<^sub>1' \<turnstile> \<Psi>\<^sub>1' \<triangleright> \<Phi>\<^sub>1' \<Longrightarrow>
       (\<Gamma>\<^sub>2, n\<^sub>2 \<turnstile> \<Psi>\<^sub>2 \<triangleright> \<Phi>\<^sub>2) = \<Gamma>\<^sub>2', n\<^sub>2' \<turnstile> \<Psi>\<^sub>2' \<triangleright> \<Phi>\<^sub>2' \<Longrightarrow>
       (\<Gamma>\<^sub>1', n\<^sub>1' \<turnstile> \<Psi>\<^sub>1' \<triangleright> \<Phi>\<^sub>1') = \<Gamma>, n \<turnstile> (tag-relation K\<^sub>1 = \<alpha> * K\<^sub>2 + \<beta>) # \<Psi> \<triangleright> \<Phi> \<Longrightarrow>
       (\<Gamma>\<^sub>2', n\<^sub>2' \<turnstile> \<Psi>\<^sub>2' \<triangleright> \<Phi>\<^sub>2') =
       \<tau>\<^sub>v\<^sub>a\<^sub>r (K\<^sub>1, n) \<doteq> \<alpha> * \<tau>\<^sub>v\<^sub>a\<^sub>r (K\<^sub>2, n) + \<beta> #
       \<Gamma>, n \<turnstile> \<Psi> \<triangleright> (tag-relation K\<^sub>1 = \<alpha> * K\<^sub>2 + \<beta>) # \<Phi> \<Longrightarrow>
       \<lbrakk>\<lbrakk> \<Gamma>\<^sub>2 \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m \<inter> \<lbrakk>\<lbrakk> \<Psi>\<^sub>2 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^sub>2\<^esup> \<inter> \<lbrakk>\<lbrakk> \<Phi>\<^sub>2 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^sub>2\<^esup>
       \<subseteq> \<lbrakk>\<lbrakk> \<Gamma>\<^sub>1 \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m \<inter> \<lbrakk>\<lbrakk> \<Psi>\<^sub>1 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^sub>1\<^esup> \<inter> \<lbrakk>\<lbrakk> \<Phi>\<^sub>1 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^sub>1\<^esup>"
      using HeronConf_interp_stepwise_tagrel_cases
      by (metis HeronConf_interpretation.simps equalityD1)
    show "\<And>\<Gamma>\<^sub>1' n\<^sub>1' \<Psi>\<^sub>1' \<Phi>\<^sub>1' \<Gamma>\<^sub>2' n\<^sub>2' \<Psi>\<^sub>2' \<Phi>\<^sub>2' \<Gamma> n K\<^sub>1 K\<^sub>2 R \<Psi> \<Phi>.
       (\<Gamma>\<^sub>1, n\<^sub>1 \<turnstile> \<Psi>\<^sub>1 \<triangleright> \<Phi>\<^sub>1) = \<Gamma>\<^sub>1', n\<^sub>1' \<turnstile> \<Psi>\<^sub>1' \<triangleright> \<Phi>\<^sub>1' \<Longrightarrow>
       (\<Gamma>\<^sub>2, n\<^sub>2 \<turnstile> \<Psi>\<^sub>2 \<triangleright> \<Phi>\<^sub>2) = \<Gamma>\<^sub>2', n\<^sub>2' \<turnstile> \<Psi>\<^sub>2' \<triangleright> \<Phi>\<^sub>2' \<Longrightarrow>
       (\<Gamma>\<^sub>1', n\<^sub>1' \<turnstile> \<Psi>\<^sub>1' \<triangleright> \<Phi>\<^sub>1') = \<Gamma>, n \<turnstile> (tag-relation \<langle>K\<^sub>1, K\<^sub>2\<rangle> \<in> R) # \<Psi> \<triangleright> \<Phi> \<Longrightarrow>
       (\<Gamma>\<^sub>2', n\<^sub>2' \<turnstile> \<Psi>\<^sub>2' \<triangleright> \<Phi>\<^sub>2') = \<langle>\<tau>\<^sub>v\<^sub>a\<^sub>r(K\<^sub>1, n), \<tau>\<^sub>v\<^sub>a\<^sub>r(K\<^sub>2, n)\<rangle> \<epsilon> R # \<Gamma>, n \<turnstile> \<Psi> \<triangleright> (tag-relation \<langle>K\<^sub>1, K\<^sub>2\<rangle> \<in> R) # \<Phi> \<Longrightarrow>
       \<lbrakk>\<lbrakk> \<Gamma>\<^sub>2 \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m \<inter> \<lbrakk>\<lbrakk> \<Psi>\<^sub>2 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^sub>2\<^esup> \<inter> \<lbrakk>\<lbrakk> \<Phi>\<^sub>2 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^sub>2\<^esup>
       \<subseteq> \<lbrakk>\<lbrakk> \<Gamma>\<^sub>1 \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m \<inter> \<lbrakk>\<lbrakk> \<Psi>\<^sub>1 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^sub>1\<^esup> \<inter> \<lbrakk>\<lbrakk> \<Phi>\<^sub>1 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^sub>1\<^esup>"
      using HeronConf_interp_stepwise_tagrelgen_cases
      by (metis HeronConf_interpretation.simps equalityD1)
    show "\<And>\<Gamma>\<^sub>1' n\<^sub>1' \<Psi>\<^sub>1' \<Phi>\<^sub>1' \<Gamma>\<^sub>2' n\<^sub>2' \<Psi>\<^sub>2' \<Phi>\<^sub>2' \<Gamma> n K\<^sub>1 K\<^sub>2 \<Psi> \<Phi>.
       (\<Gamma>\<^sub>1, n\<^sub>1 \<turnstile> \<Psi>\<^sub>1 \<triangleright> \<Phi>\<^sub>1) = \<Gamma>\<^sub>1', n\<^sub>1' \<turnstile> \<Psi>\<^sub>1' \<triangleright> \<Phi>\<^sub>1' \<Longrightarrow>
       (\<Gamma>\<^sub>2, n\<^sub>2 \<turnstile> \<Psi>\<^sub>2 \<triangleright> \<Phi>\<^sub>2) = \<Gamma>\<^sub>2', n\<^sub>2' \<turnstile> \<Psi>\<^sub>2' \<triangleright> \<Phi>\<^sub>2' \<Longrightarrow>
       (\<Gamma>\<^sub>1', n\<^sub>1' \<turnstile> \<Psi>\<^sub>1' \<triangleright> \<Phi>\<^sub>1') = \<Gamma>, n \<turnstile> (K\<^sub>1 implies K\<^sub>2) # \<Psi> \<triangleright> \<Phi> \<Longrightarrow>
       (\<Gamma>\<^sub>2', n\<^sub>2' \<turnstile> \<Psi>\<^sub>2' \<triangleright> \<Phi>\<^sub>2') = K\<^sub>1 \<not>\<Up> n # \<Gamma>, n \<turnstile> \<Psi> \<triangleright> (K\<^sub>1 implies K\<^sub>2) # \<Phi> \<Longrightarrow>
       \<lbrakk>\<lbrakk> \<Gamma>\<^sub>2 \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m \<inter> \<lbrakk>\<lbrakk> \<Psi>\<^sub>2 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^sub>2\<^esup> \<inter> \<lbrakk>\<lbrakk> \<Phi>\<^sub>2 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^sub>2\<^esup>
       \<subseteq> \<lbrakk>\<lbrakk> \<Gamma>\<^sub>1 \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m \<inter> \<lbrakk>\<lbrakk> \<Psi>\<^sub>1 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^sub>1\<^esup> \<inter> \<lbrakk>\<lbrakk> \<Phi>\<^sub>1 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^sub>1\<^esup>"
      using HeronConf_interp_stepwise_implies_cases
      by (metis HeronConf_interpretation.simps inf_sup_ord(3))
    show "\<And>\<Gamma>\<^sub>1' n\<^sub>1' \<Psi>\<^sub>1' \<Phi>\<^sub>1' \<Gamma>\<^sub>2' n\<^sub>2' \<Psi>\<^sub>2' \<Phi>\<^sub>2' \<Gamma> n K\<^sub>1 K\<^sub>2 \<Psi> \<Phi>.
       (\<Gamma>\<^sub>1, n\<^sub>1 \<turnstile> \<Psi>\<^sub>1 \<triangleright> \<Phi>\<^sub>1) = (\<Gamma>\<^sub>1', n\<^sub>1' \<turnstile> \<Psi>\<^sub>1' \<triangleright> \<Phi>\<^sub>1') \<Longrightarrow>
       (\<Gamma>\<^sub>2, n\<^sub>2 \<turnstile> \<Psi>\<^sub>2 \<triangleright> \<Phi>\<^sub>2) = (\<Gamma>\<^sub>2', n\<^sub>2' \<turnstile> \<Psi>\<^sub>2' \<triangleright> \<Phi>\<^sub>2') \<Longrightarrow>
       (\<Gamma>\<^sub>1', n\<^sub>1' \<turnstile> \<Psi>\<^sub>1' \<triangleright> \<Phi>\<^sub>1') = (\<Gamma>, n \<turnstile> (K\<^sub>1 implies K\<^sub>2) # \<Psi> \<triangleright> \<Phi>) \<Longrightarrow>
       (\<Gamma>\<^sub>2', n\<^sub>2' \<turnstile> \<Psi>\<^sub>2' \<triangleright> \<Phi>\<^sub>2') = (K\<^sub>1 \<Up> n # K\<^sub>2 \<Up> n # \<Gamma>, n \<turnstile> \<Psi> \<triangleright> (K\<^sub>1 implies K\<^sub>2) # \<Phi>) \<Longrightarrow>
       \<lbrakk>\<lbrakk> \<Gamma>\<^sub>2 \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m \<inter> \<lbrakk>\<lbrakk> \<Psi>\<^sub>2 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^sub>2\<^esup> \<inter> \<lbrakk>\<lbrakk> \<Phi>\<^sub>2 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^sub>2\<^esup>
       \<subseteq> \<lbrakk>\<lbrakk> \<Gamma>\<^sub>1 \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m \<inter> \<lbrakk>\<lbrakk> \<Psi>\<^sub>1 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^sub>1\<^esup> \<inter> \<lbrakk>\<lbrakk> \<Phi>\<^sub>1 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^sub>1\<^esup>"
      using HeronConf_interp_stepwise_implies_cases
      by (metis HeronConf_interpretation.simps inf_sup_ord(4))
    show "\<And>\<Gamma>\<^sub>1' n\<^sub>1' \<Psi>\<^sub>1' \<Phi>\<^sub>1' \<Gamma>\<^sub>2' n\<^sub>2' \<Psi>\<^sub>2' \<Phi>\<^sub>2' \<Gamma> n K\<^sub>1 \<delta>\<tau> K\<^sub>2 K\<^sub>3 \<Psi> \<Phi>.
       (\<Gamma>\<^sub>1, n\<^sub>1 \<turnstile> \<Psi>\<^sub>1 \<triangleright> \<Phi>\<^sub>1) = (\<Gamma>\<^sub>1', n\<^sub>1' \<turnstile> \<Psi>\<^sub>1' \<triangleright> \<Phi>\<^sub>1') \<Longrightarrow>
       (\<Gamma>\<^sub>2, n\<^sub>2 \<turnstile> \<Psi>\<^sub>2 \<triangleright> \<Phi>\<^sub>2) = (\<Gamma>\<^sub>2', n\<^sub>2' \<turnstile> \<Psi>\<^sub>2' \<triangleright> \<Phi>\<^sub>2') \<Longrightarrow>
       (\<Gamma>\<^sub>1', n\<^sub>1' \<turnstile> \<Psi>\<^sub>1' \<triangleright> \<Phi>\<^sub>1') = \<Gamma>, n \<turnstile> (K\<^sub>1 time-delayed by \<delta>\<tau> on K\<^sub>2 implies K\<^sub>3) # \<Psi> \<triangleright> \<Phi> \<Longrightarrow>
       (\<Gamma>\<^sub>2', n\<^sub>2' \<turnstile> \<Psi>\<^sub>2' \<triangleright> \<Phi>\<^sub>2') =
       K\<^sub>1 \<not>\<Up> n # \<Gamma>, n \<turnstile> \<Psi> \<triangleright> (K\<^sub>1 time-delayed by \<delta>\<tau> on K\<^sub>2 implies K\<^sub>3) # \<Phi> \<Longrightarrow>
       \<lbrakk>\<lbrakk> \<Gamma>\<^sub>2 \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m \<inter> \<lbrakk>\<lbrakk> \<Psi>\<^sub>2 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^sub>2\<^esup> \<inter> \<lbrakk>\<lbrakk> \<Phi>\<^sub>2 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^sub>2\<^esup>
       \<subseteq> \<lbrakk>\<lbrakk> \<Gamma>\<^sub>1 \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m \<inter> \<lbrakk>\<lbrakk> \<Psi>\<^sub>1 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^sub>1\<^esup> \<inter> \<lbrakk>\<lbrakk> \<Phi>\<^sub>1 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^sub>1\<^esup>"
      using HeronConf_interp_stepwise_timedelayed_cases
      by (metis (no_types, lifting) HeronConf_interpretation.simps inf.order_iff inf_sup_absorb)
    show "\<And>\<Gamma>\<^sub>1' n\<^sub>1' \<Psi>\<^sub>1' \<Phi>\<^sub>1' \<Gamma>\<^sub>2' n\<^sub>2' \<Psi>\<^sub>2' \<Phi>\<^sub>2' \<Gamma> n K\<^sub>1 \<delta>\<tau> K\<^sub>2 K\<^sub>3 \<Psi> \<Phi>.
       (\<Gamma>\<^sub>1, n\<^sub>1 \<turnstile> \<Psi>\<^sub>1 \<triangleright> \<Phi>\<^sub>1) = (\<Gamma>\<^sub>1', n\<^sub>1' \<turnstile> \<Psi>\<^sub>1' \<triangleright> \<Phi>\<^sub>1') \<Longrightarrow>
       (\<Gamma>\<^sub>2, n\<^sub>2 \<turnstile> \<Psi>\<^sub>2 \<triangleright> \<Phi>\<^sub>2) = (\<Gamma>\<^sub>2', n\<^sub>2' \<turnstile> \<Psi>\<^sub>2' \<triangleright> \<Phi>\<^sub>2') \<Longrightarrow>
       (\<Gamma>\<^sub>1', n\<^sub>1' \<turnstile> \<Psi>\<^sub>1' \<triangleright> \<Phi>\<^sub>1') = \<Gamma>, n \<turnstile> (K\<^sub>1 time-delayed by \<delta>\<tau> on K\<^sub>2 implies K\<^sub>3) # \<Psi> \<triangleright> \<Phi> \<Longrightarrow>
       (\<Gamma>\<^sub>2', n\<^sub>2' \<turnstile> \<Psi>\<^sub>2' \<triangleright> \<Phi>\<^sub>2') =
       K\<^sub>1 \<Up> n #
       \<Gamma>, n \<turnstile> (K\<^sub>3 sporadic \<lfloor> \<tau>\<^sub>v\<^sub>a\<^sub>r (K\<^sub>2, n) \<oplus> \<delta>\<tau> \<rfloor> on K\<^sub>2) #
               \<Psi> \<triangleright> (K\<^sub>1 time-delayed by \<delta>\<tau> on K\<^sub>2 implies K\<^sub>3) # \<Phi> \<Longrightarrow>
       \<lbrakk>\<lbrakk> \<Gamma>\<^sub>2 \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m \<inter> \<lbrakk>\<lbrakk> \<Psi>\<^sub>2 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^sub>2\<^esup> \<inter> \<lbrakk>\<lbrakk> \<Phi>\<^sub>2 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^sub>2\<^esup>
       \<subseteq> \<lbrakk>\<lbrakk> \<Gamma>\<^sub>1 \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m \<inter> \<lbrakk>\<lbrakk> \<Psi>\<^sub>1 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^sub>1\<^esup> \<inter> \<lbrakk>\<lbrakk> \<Phi>\<^sub>1 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^sub>1\<^esup>"
      using HeronConf_interp_stepwise_timedelayed_cases
      by (metis HeronConf_interpretation.simps sup_ge2)
    qed
  qed

lemma sound_reduction':
  assumes "\<S>\<^sub>1 \<hookrightarrow> \<S>\<^sub>2"
  shows "\<lbrakk> \<S>\<^sub>1 \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g \<supseteq> \<lbrakk> \<S>\<^sub>2 \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g"
  by (metis sound_reduction HeronConf_interpretation.elims assms)

lemma sound_reduction_generalized:
  assumes "\<S>\<^sub>1 \<hookrightarrow>\<^bsup>k\<^esup> \<S>\<^sub>2"
  shows "\<lbrakk> \<S>\<^sub>1 \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g \<supseteq> \<lbrakk> \<S>\<^sub>2 \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g"
  proof (insert assms, induct k arbitrary: \<S>\<^sub>2)
    case 0
    then have *: "\<S>\<^sub>1 \<hookrightarrow>\<^bsup>0\<^esup> \<S>\<^sub>2 \<Longrightarrow> \<S>\<^sub>1 = \<S>\<^sub>2"
      by auto
    moreover have "\<S>\<^sub>1 = \<S>\<^sub>2" using *
      using "0.prems" by linarith
    ultimately show ?case by auto
  next
    case (Suc k)
    then show ?case
      proof -
      fix k :: nat
      assume ff: "\<S>\<^sub>1 \<hookrightarrow>\<^bsup>Suc k\<^esup> \<S>\<^sub>2"
      assume hi: "\<And>\<S>\<^sub>2. \<S>\<^sub>1 \<hookrightarrow>\<^bsup>k\<^esup> \<S>\<^sub>2 \<Longrightarrow> \<lbrakk> \<S>\<^sub>2 \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g \<subseteq> \<lbrakk> \<S>\<^sub>1 \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g"
      obtain \<S>\<^sub>n where red_decomp: "\<S>\<^sub>1 \<hookrightarrow>\<^bsup>k\<^esup> \<S>\<^sub>n \<and> \<S>\<^sub>n \<hookrightarrow> \<S>\<^sub>2"
        using ff by auto
      then have "\<lbrakk> \<S>\<^sub>1 \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g \<supseteq> \<lbrakk> \<S>\<^sub>n \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g"
        using hi by (metis (no_types, lifting) ff relpowp_Suc_E someI_ex)
      also have "\<lbrakk> \<S>\<^sub>n \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g \<supseteq> \<lbrakk> \<S>\<^sub>2 \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g"
        by (simp add: red_decomp sound_reduction')
      ultimately show "\<lbrakk> \<S>\<^sub>1 \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g \<supseteq> \<lbrakk> \<S>\<^sub>2 \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g"
        by auto
      qed
  qed

text \<open>From initial configuration, any reduction step number [k] providing a
      configuration [\<S>] will denote runs from initial specification [\<Psi>].\<close>
theorem soundness:
  assumes "[], 0 \<turnstile> \<Psi> \<triangleright> [] \<hookrightarrow>\<^bsup>k\<^esup> \<S>"
  shows "\<lbrakk>\<lbrakk> \<Psi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L \<supseteq> \<lbrakk> \<S> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g"
  using assms sound_reduction_generalized solve_start
  by blast

section \<open>Completeness\<close>

lemma complete_direct_successors:
  shows "\<lbrakk> \<Gamma>, n \<turnstile> \<Psi> \<triangleright> \<Phi> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g \<subseteq> (\<Union>X\<in>\<C>\<^sub>n\<^sub>e\<^sub>x\<^sub>t (\<Gamma>, n \<turnstile> \<Psi> \<triangleright> \<Phi>). \<lbrakk> X \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g)"
  proof (induct \<Psi>)
    case Nil
    show ?case
      using HeronConf_interp_stepwise_instant_cases operational_semantics_step.simps operational_semantics_intro.instant_i
      by fastforce
  next
    case (Cons \<psi> \<Psi>)
    then show ?case
      proof (induct \<psi>)
        case (Sporadic K \<tau>)
        then show ?case
          using HeronConf_interp_stepwise_sporadic_cases Cnext_solve_sporadic
          by (smt UN_iff UnE insert_subset subsetI)
      next
        case (SporadicOn K1 \<tau> K2)
        then show ?case 
          using HeronConf_interp_stepwise_sporadicon_cases Cnext_solve_sporadicon
          by (smt UN_iff UnE insert_subset subsetI)
      next
        case (TagRelation K1 \<alpha> K2 \<beta>)
        then show ?case
          using HeronConf_interp_stepwise_tagrel_cases Cnext_solve_tagrel
          by (smt UN_iff UnE insert_subset subsetI)
      next
        case (TagRelationGen K\<^sub>1 K\<^sub>2 R)
        then show ?case
          using HeronConf_interp_stepwise_tagrelgen_cases Cnext_solve_tagrelgen
          by (smt UN_iff UnE insert_subset subsetI)
      next
        case (Implies K1 K2)
        then show ?case
          using HeronConf_interp_stepwise_implies_cases Cnext_solve_implies
          by (smt UN_iff UnE insert_subset subsetI)
      next
        case (TimeDelayedBy Kmast \<tau> Kmeas Kslave)
        then show ?case
          using HeronConf_interp_stepwise_timedelayed_cases Cnext_solve_timedelayed
          by (smt UN_iff UnE insert_subset subsetI)
      qed
  qed

lemma complete_direct_successors':
  shows "\<lbrakk> \<S> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g \<subseteq> (\<Union>X\<in>\<C>\<^sub>n\<^sub>e\<^sub>x\<^sub>t \<S>. \<lbrakk> X \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g)"
  by (metis HeronConf_interpretation.cases complete_direct_successors)

lemma branch_existence:
  assumes "\<rho> \<in> \<lbrakk> \<S>\<^sub>1 \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g"
  shows "\<exists>\<S>\<^sub>2. \<S>\<^sub>1 \<hookrightarrow> \<S>\<^sub>2 \<and> \<rho> \<in> \<lbrakk> \<S>\<^sub>2 \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g"
  by (metis (mono_tags, lifting) UN_iff assms complete_direct_successors' mem_Collect_eq set_rev_mp)

lemma branch_existence':
  assumes "\<rho> \<in> \<lbrakk> \<S>\<^sub>1 \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g"
  shows "\<exists>\<S>\<^sub>2. \<S>\<^sub>1 \<hookrightarrow>\<^bsup>k\<^esup> \<S>\<^sub>2 \<and> \<rho> \<in> \<lbrakk> \<S>\<^sub>2 \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g"
  proof (induct k)
    case 0
    then show ?case
      by (simp add: assms)
  next
    case (Suc k)
    then show ?case
      by (meson branch_existence relpowp_Suc_I)
  qed

text \<open>Any run from initial specification [\<Psi>] has a corresponding configuration
      [\<S>] at any reduction step number [k] starting from initial configuration.\<close>
theorem completeness:
  assumes "\<rho> \<in> \<lbrakk>\<lbrakk> \<Psi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L"
  shows "\<exists>\<S>. [], 0 \<turnstile> \<Psi> \<triangleright> []  \<hookrightarrow>\<^bsup>k\<^esup>  \<S>
         \<and> \<rho> \<in> \<lbrakk> \<S> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g"
  using assms branch_existence' solve_start by blast

section \<open>Progress\<close>

lemma instant_index_increase:
  assumes "\<rho> \<in> \<lbrakk> \<Gamma>, n \<turnstile> \<Psi> \<triangleright> \<Phi> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g"
  shows   "\<exists>\<Gamma>\<^sub>k \<Psi>\<^sub>k \<Phi>\<^sub>k k. \<Gamma>, n \<turnstile> \<Psi> \<triangleright> \<Phi>  \<hookrightarrow>\<^bsup>k\<^esup>  \<Gamma>\<^sub>k, Suc n \<turnstile> \<Psi>\<^sub>k \<triangleright> \<Phi>\<^sub>k
                         \<and> \<rho> \<in> \<lbrakk> \<Gamma>\<^sub>k, Suc n \<turnstile> \<Psi>\<^sub>k \<triangleright> \<Phi>\<^sub>k \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g"
  proof (insert assms, induct \<Psi> arbitrary: \<Gamma> \<Phi>)
    case (Nil \<Gamma> \<Phi>)
    then show ?case
      proof -
        have "\<Gamma>, n \<turnstile> [] \<triangleright> \<Phi> \<hookrightarrow>\<^bsup>1\<^esup> \<Gamma>, Suc n \<turnstile> \<Phi> \<triangleright> []"
          using instant_i intro_part
          by fastforce
        moreover have "\<lbrakk> \<Gamma>, n \<turnstile> [] \<triangleright> \<Phi> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g = \<lbrakk> \<Gamma>, Suc n \<turnstile> \<Phi> \<triangleright> [] \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g"
          by auto
        moreover have "\<rho> \<in> \<lbrakk> \<Gamma>, Suc n \<turnstile> \<Phi> \<triangleright> [] \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g"
          using assms Nil.prems calculation(2) by blast
        ultimately show ?thesis by blast
      qed
  next
    case (Cons \<psi> \<Psi>)
  then show ?case
    proof (induct \<psi>)
      case (Sporadic K \<tau>)
      have branches: "\<lbrakk> \<Gamma>, n \<turnstile> (K sporadic \<tau>) # \<Psi> \<triangleright> \<Phi> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g = \<lbrakk> \<Gamma>, n \<turnstile> \<Psi> \<triangleright> (K sporadic \<tau>) # \<Phi> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g
                                                           \<union> \<lbrakk> K \<Up> n # K \<Down> n @ \<lfloor>\<tau>\<rfloor> # \<Gamma>, n \<turnstile> \<Psi> \<triangleright> \<Phi> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g"
            using HeronConf_interp_stepwise_sporadic_cases by simp
      have br1: "\<rho> \<in> \<lbrakk> \<Gamma>, n \<turnstile> \<Psi> \<triangleright> (K sporadic \<tau>) # \<Phi> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g \<Longrightarrow> \<exists>\<Gamma>\<^sub>k \<Psi>\<^sub>k \<Phi>\<^sub>k k.
       \<Gamma>, n \<turnstile> (K sporadic \<tau>) # \<Psi> \<triangleright> \<Phi> \<hookrightarrow>\<^bsup>k\<^esup> \<Gamma>\<^sub>k, Suc n \<turnstile> \<Psi>\<^sub>k \<triangleright> \<Phi>\<^sub>k \<and>
       \<rho> \<in> \<lbrakk> \<Gamma>\<^sub>k, Suc n \<turnstile> \<Psi>\<^sub>k \<triangleright> \<Phi>\<^sub>k \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g"
        proof -
          assume h1: "\<rho> \<in> \<lbrakk> \<Gamma>, n \<turnstile> \<Psi> \<triangleright> (K sporadic \<tau>) # \<Phi> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g"
          have "\<exists>\<Gamma>\<^sub>k \<Psi>\<^sub>k \<Phi>\<^sub>k k. \<Gamma>, n \<turnstile> \<Psi> \<triangleright> (K sporadic \<tau>) # \<Phi> \<hookrightarrow>\<^bsup>k\<^esup> \<Gamma>\<^sub>k, Suc n \<turnstile> \<Psi>\<^sub>k \<triangleright> \<Phi>\<^sub>k \<and> \<rho> \<in> \<lbrakk> \<Gamma>\<^sub>k, Suc n \<turnstile> \<Psi>\<^sub>k \<triangleright> \<Phi>\<^sub>k \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g"
            using h1 Sporadic.prems by simp
          then show ?thesis
            by (meson elims_part relpowp_Suc_I2 sporadic_e1)
        qed
      moreover have br2: "\<rho> \<in> \<lbrakk> (K \<Up> n) # (K \<Down> n @ \<lfloor>\<tau>\<rfloor>) # \<Gamma>, n \<turnstile> \<Psi> \<triangleright> \<Phi> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g \<Longrightarrow> \<exists>\<Gamma>\<^sub>k \<Psi>\<^sub>k \<Phi>\<^sub>k k.
       \<Gamma>, n \<turnstile> (K sporadic \<tau>) # \<Psi> \<triangleright> \<Phi> \<hookrightarrow>\<^bsup>k\<^esup> \<Gamma>\<^sub>k, Suc n \<turnstile> \<Psi>\<^sub>k \<triangleright> \<Phi>\<^sub>k \<and>
       \<rho> \<in> \<lbrakk> \<Gamma>\<^sub>k, Suc n \<turnstile> \<Psi>\<^sub>k \<triangleright> \<Phi>\<^sub>k \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g"
        proof -
          assume h2: "\<rho> \<in> \<lbrakk> (K \<Up> n) # (K \<Down> n @ \<lfloor>\<tau>\<rfloor>) # \<Gamma>, n \<turnstile> \<Psi> \<triangleright> \<Phi> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g"
          have "\<exists>\<Gamma>\<^sub>k \<Psi>\<^sub>k \<Phi>\<^sub>k k. (K \<Up> n) # (K \<Down> n @ \<lfloor>\<tau>\<rfloor>) # \<Gamma>, n \<turnstile> \<Psi> \<triangleright> \<Phi> \<hookrightarrow>\<^bsup>k\<^esup> \<Gamma>\<^sub>k, Suc n \<turnstile> \<Psi>\<^sub>k \<triangleright> \<Phi>\<^sub>k \<and> \<rho> \<in> \<lbrakk> \<Gamma>\<^sub>k, Suc n \<turnstile> \<Psi>\<^sub>k \<triangleright> \<Phi>\<^sub>k \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g"
            using h2 Sporadic.prems by simp
          then show ?thesis
            by (meson elims_part relpowp_Suc_I2 sporadic_e2)
        qed
      ultimately show ?case
        by (metis Sporadic.prems(2) UnE branches)
    next
      case (SporadicOn K\<^sub>1 \<tau> K\<^sub>2)
      have branches: "\<lbrakk> \<Gamma>, n \<turnstile> (K\<^sub>1 sporadic \<tau> on K\<^sub>2) # \<Psi> \<triangleright> \<Phi> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g = \<lbrakk> \<Gamma>, n \<turnstile> \<Psi> \<triangleright> (K\<^sub>1 sporadic \<tau> on K\<^sub>2) # \<Phi> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g
                                                                         \<union> \<lbrakk> K\<^sub>1 \<Up> n # K\<^sub>2 \<Down> n @ \<tau> # \<Gamma>, n \<turnstile> \<Psi> \<triangleright> \<Phi> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g"
            using HeronConf_interp_stepwise_sporadicon_cases by simp
      have br1: "\<rho> \<in> \<lbrakk> \<Gamma>, n \<turnstile> \<Psi> \<triangleright> (K\<^sub>1 sporadic \<tau> on K\<^sub>2) # \<Phi> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g \<Longrightarrow> \<exists>\<Gamma>\<^sub>k \<Psi>\<^sub>k \<Phi>\<^sub>k k.
       \<Gamma>, n \<turnstile> (K\<^sub>1 sporadic \<tau> on K\<^sub>2) # \<Psi> \<triangleright> \<Phi> \<hookrightarrow>\<^bsup>k\<^esup> \<Gamma>\<^sub>k, Suc n \<turnstile> \<Psi>\<^sub>k \<triangleright> \<Phi>\<^sub>k \<and>
       \<rho> \<in> \<lbrakk> \<Gamma>\<^sub>k, Suc n \<turnstile> \<Psi>\<^sub>k \<triangleright> \<Phi>\<^sub>k \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g"
        proof -
          assume h1: "\<rho> \<in> \<lbrakk> \<Gamma>, n \<turnstile> \<Psi> \<triangleright> (K\<^sub>1 sporadic \<tau> on K\<^sub>2) # \<Phi> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g"
          then have "\<exists>\<Gamma>\<^sub>k \<Psi>\<^sub>k \<Phi>\<^sub>k k. (\<Gamma>, n \<turnstile> \<Psi> \<triangleright> (K\<^sub>1 sporadic \<tau> on K\<^sub>2) # \<Phi>) \<hookrightarrow>\<^bsup>k\<^esup> \<Gamma>\<^sub>k, Suc n \<turnstile> \<Psi>\<^sub>k \<triangleright> \<Phi>\<^sub>k \<and> \<rho> \<in> \<lbrakk> \<Gamma>\<^sub>k, Suc n \<turnstile> \<Psi>\<^sub>k \<triangleright> \<Phi>\<^sub>k \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g"
            using h1 SporadicOn.prems by simp
          then show ?thesis
            by (meson elims_part relpowp_Suc_I2 sporadic_on_e1)
        qed
      moreover have br2: "\<rho> \<in> \<lbrakk> K\<^sub>1 \<Up> n # K\<^sub>2 \<Down> n @ \<tau> # \<Gamma>, n \<turnstile> \<Psi> \<triangleright> \<Phi> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g \<Longrightarrow> \<exists>\<Gamma>\<^sub>k \<Psi>\<^sub>k \<Phi>\<^sub>k k.
       (\<Gamma>, n \<turnstile> (K\<^sub>1 sporadic \<tau> on K\<^sub>2) # \<Psi> \<triangleright> \<Phi>) \<hookrightarrow>\<^bsup>k\<^esup> (\<Gamma>\<^sub>k, Suc n \<turnstile> \<Psi>\<^sub>k \<triangleright> \<Phi>\<^sub>k) \<and>
       \<rho> \<in> \<lbrakk> \<Gamma>\<^sub>k, Suc n \<turnstile> \<Psi>\<^sub>k \<triangleright> \<Phi>\<^sub>k \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g"
        proof -
          assume h2: "\<rho> \<in> \<lbrakk> K\<^sub>1 \<Up> n # K\<^sub>2 \<Down> n @ \<tau> # \<Gamma>, n \<turnstile> \<Psi> \<triangleright> \<Phi> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g"
          then have "\<exists>\<Gamma>\<^sub>k \<Psi>\<^sub>k \<Phi>\<^sub>k k. ((K\<^sub>1 \<Up> n) # (K\<^sub>2 \<Down> n @ \<tau>) # \<Gamma>, n \<turnstile> \<Psi> \<triangleright> \<Phi>) \<hookrightarrow>\<^bsup>k\<^esup> \<Gamma>\<^sub>k, Suc n \<turnstile> \<Psi>\<^sub>k \<triangleright> \<Phi>\<^sub>k \<and> \<rho> \<in> \<lbrakk> \<Gamma>\<^sub>k, Suc n \<turnstile> \<Psi>\<^sub>k \<triangleright> \<Phi>\<^sub>k \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g"
            using h2 SporadicOn.prems by simp
          then show ?thesis
            by (meson elims_part relpowp_Suc_I2 sporadic_on_e2)
        qed
      ultimately show ?case
        by (metis SporadicOn.prems(2) UnE branches)
    next
      case (TagRelation K\<^sub>1 \<alpha> K\<^sub>2 \<beta>)
      have branches: "\<lbrakk> \<Gamma>, n \<turnstile> (tag-relation K\<^sub>1 = \<alpha> * K\<^sub>2 + \<beta>) # \<Psi> \<triangleright> \<Phi> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g
          = \<lbrakk> (\<tau>\<^sub>v\<^sub>a\<^sub>r(K\<^sub>1, n) \<doteq> \<alpha> * \<tau>\<^sub>v\<^sub>a\<^sub>r(K\<^sub>2, n) + \<beta>) # \<Gamma>, n \<turnstile> \<Psi> \<triangleright> (tag-relation K\<^sub>1 = \<alpha> * K\<^sub>2 + \<beta>) # \<Phi> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g"
        using HeronConf_interp_stepwise_tagrel_cases by simp
      then show ?case
        proof -
          have "\<exists>\<Gamma>\<^sub>k \<Psi>\<^sub>k \<Phi>\<^sub>k k. ((\<tau>\<^sub>v\<^sub>a\<^sub>r(K\<^sub>1, n) \<doteq> \<alpha> * \<tau>\<^sub>v\<^sub>a\<^sub>r(K\<^sub>2, n) + \<beta>) # \<Gamma>, n \<turnstile> \<Psi> \<triangleright> (tag-relation K\<^sub>1 = \<alpha> * K\<^sub>2 + \<beta>) # \<Phi>)
              \<hookrightarrow>\<^bsup>k\<^esup> \<Gamma>\<^sub>k, Suc n \<turnstile> \<Psi>\<^sub>k \<triangleright> \<Phi>\<^sub>k \<and> \<rho> \<in> \<lbrakk> \<Gamma>\<^sub>k, Suc n \<turnstile> \<Psi>\<^sub>k \<triangleright> \<Phi>\<^sub>k \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g"
            using TagRelation.prems by simp
          then show ?thesis
            by (meson elims_part relpowp_Suc_I2 tagrel_e)
        qed
    next
      case (TagRelationGen K\<^sub>1 K\<^sub>2 R)
      have branches: "\<lbrakk> \<Gamma>, n \<turnstile> (tag-relation \<langle>K\<^sub>1, K\<^sub>2\<rangle> \<in> R) # \<Psi> \<triangleright> \<Phi> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g
          = \<lbrakk> (\<langle>\<tau>\<^sub>v\<^sub>a\<^sub>r(K\<^sub>1, n), \<tau>\<^sub>v\<^sub>a\<^sub>r(K\<^sub>2, n)\<rangle> \<epsilon> R) # \<Gamma>, n \<turnstile> \<Psi> \<triangleright> (tag-relation \<langle>K\<^sub>1, K\<^sub>2\<rangle> \<in> R) # \<Phi> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g"
        using HeronConf_interp_stepwise_tagrelgen_cases by simp
      then show ?case
        proof -
          have "\<exists>\<Gamma>\<^sub>k \<Psi>\<^sub>k \<Phi>\<^sub>k k. ((\<langle>\<tau>\<^sub>v\<^sub>a\<^sub>r(K\<^sub>1, n), \<tau>\<^sub>v\<^sub>a\<^sub>r(K\<^sub>2, n)\<rangle> \<epsilon> R) # \<Gamma>, n \<turnstile> \<Psi> \<triangleright> (tag-relation \<langle>K\<^sub>1, K\<^sub>2\<rangle> \<in> R) # \<Phi>)
              \<hookrightarrow>\<^bsup>k\<^esup> \<Gamma>\<^sub>k, Suc n \<turnstile> \<Psi>\<^sub>k \<triangleright> \<Phi>\<^sub>k \<and> \<rho> \<in> \<lbrakk> \<Gamma>\<^sub>k, Suc n \<turnstile> \<Psi>\<^sub>k \<triangleright> \<Phi>\<^sub>k \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g"
            using TagRelationGen.prems by simp
          then show ?thesis
            by (meson elims_part relpowp_Suc_I2 tagrelgen_e)
        qed
    next
      case (Implies K\<^sub>1 K\<^sub>2)
      have branches: "\<lbrakk> \<Gamma>, n \<turnstile> (K\<^sub>1 implies K\<^sub>2) # \<Psi> \<triangleright> \<Phi> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g
          = \<lbrakk> K\<^sub>1 \<not>\<Up> n # \<Gamma>, n \<turnstile> \<Psi> \<triangleright> (K\<^sub>1 implies K\<^sub>2) # \<Phi> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g
          \<union> \<lbrakk> K\<^sub>1 \<Up> n # K\<^sub>2 \<Up> n # \<Gamma>, n \<turnstile> \<Psi> \<triangleright> (K\<^sub>1 implies K\<^sub>2) # \<Phi> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g"
        using HeronConf_interp_stepwise_implies_cases by simp
      have br1: "\<rho> \<in> \<lbrakk> K\<^sub>1 \<not>\<Up> n # \<Gamma>, n \<turnstile> \<Psi> \<triangleright> (K\<^sub>1 implies K\<^sub>2) # \<Phi> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g \<Longrightarrow> \<exists>\<Gamma>\<^sub>k \<Psi>\<^sub>k \<Phi>\<^sub>k k.
       \<Gamma>, n \<turnstile> (K\<^sub>1 implies K\<^sub>2) # \<Psi> \<triangleright> \<Phi> \<hookrightarrow>\<^bsup>k\<^esup> \<Gamma>\<^sub>k, Suc n \<turnstile> \<Psi>\<^sub>k \<triangleright> \<Phi>\<^sub>k \<and>
       \<rho> \<in> \<lbrakk> \<Gamma>\<^sub>k, Suc n \<turnstile> \<Psi>\<^sub>k \<triangleright> \<Phi>\<^sub>k \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g"
        proof -
          assume h1: "\<rho> \<in> \<lbrakk> K\<^sub>1 \<not>\<Up> n # \<Gamma>, n \<turnstile> \<Psi> \<triangleright> (K\<^sub>1 implies K\<^sub>2) # \<Phi> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g"
          then have "\<exists>\<Gamma>\<^sub>k \<Psi>\<^sub>k \<Phi>\<^sub>k k. (K\<^sub>1 \<not>\<Up> n # \<Gamma>, n \<turnstile> \<Psi> \<triangleright> (K\<^sub>1 implies K\<^sub>2) # \<Phi>) \<hookrightarrow>\<^bsup>k\<^esup> \<Gamma>\<^sub>k, Suc n \<turnstile> \<Psi>\<^sub>k \<triangleright> \<Phi>\<^sub>k \<and> \<rho> \<in> \<lbrakk> \<Gamma>\<^sub>k, Suc n \<turnstile> \<Psi>\<^sub>k \<triangleright> \<Phi>\<^sub>k \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g"
            using h1 Implies.prems by simp
          then show ?thesis
            by (meson elims_part relpowp_Suc_I2 implies_e1)
        qed
      moreover have br2: "\<rho> \<in> \<lbrakk> (K\<^sub>1 \<Up> n) # (K\<^sub>2 \<Up> n) # \<Gamma>, n \<turnstile> \<Psi> \<triangleright> (K\<^sub>1 implies K\<^sub>2) # \<Phi> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g \<Longrightarrow> \<exists>\<Gamma>\<^sub>k \<Psi>\<^sub>k \<Phi>\<^sub>k k.
       \<Gamma>, n \<turnstile> (K\<^sub>1 implies K\<^sub>2) # \<Psi> \<triangleright> \<Phi> \<hookrightarrow>\<^bsup>k\<^esup> \<Gamma>\<^sub>k, Suc n \<turnstile> \<Psi>\<^sub>k \<triangleright> \<Phi>\<^sub>k \<and>
       \<rho> \<in> \<lbrakk> \<Gamma>\<^sub>k, Suc n \<turnstile> \<Psi>\<^sub>k \<triangleright> \<Phi>\<^sub>k \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g"
        proof -
          assume h2: "\<rho> \<in> \<lbrakk> (K\<^sub>1 \<Up> n) # (K\<^sub>2 \<Up> n) # \<Gamma>, n \<turnstile> \<Psi> \<triangleright> (K\<^sub>1 implies K\<^sub>2) # \<Phi> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g"
          then have "\<exists>\<Gamma>\<^sub>k \<Psi>\<^sub>k \<Phi>\<^sub>k k. ((K\<^sub>1 \<Up> n) # (K\<^sub>2 \<Up> n) # \<Gamma>, n \<turnstile> \<Psi> \<triangleright> (K\<^sub>1 implies K\<^sub>2) # \<Phi>) \<hookrightarrow>\<^bsup>k\<^esup> \<Gamma>\<^sub>k, Suc n \<turnstile> \<Psi>\<^sub>k \<triangleright> \<Phi>\<^sub>k \<and> \<rho> \<in> \<lbrakk> \<Gamma>\<^sub>k, Suc n \<turnstile> \<Psi>\<^sub>k \<triangleright> \<Phi>\<^sub>k \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g"
            using h2 Implies.prems by simp
          then show ?thesis
            by (meson elims_part relpowp_Suc_I2 implies_e2)
        qed
      ultimately show ?case
        using Implies.prems(2) by fastforce
    next
      case (TimeDelayedBy K\<^sub>1 \<delta>\<tau> K\<^sub>2 K\<^sub>3)
      have branches: "\<lbrakk> \<Gamma>, n \<turnstile> (K\<^sub>1 time-delayed by \<delta>\<tau> on K\<^sub>2 implies K\<^sub>3) # \<Psi> \<triangleright> \<Phi> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g
          = \<lbrakk> K\<^sub>1 \<not>\<Up> n # \<Gamma>, n \<turnstile> \<Psi> \<triangleright> (K\<^sub>1 time-delayed by \<delta>\<tau> on K\<^sub>2 implies K\<^sub>3) # \<Phi> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g
          \<union> \<lbrakk> K\<^sub>1 \<Up> n # \<Gamma>, n \<turnstile> (K\<^sub>3 sporadic \<lfloor>\<tau>\<^sub>v\<^sub>a\<^sub>r(K\<^sub>2, n) \<oplus> \<delta>\<tau>\<rfloor> on K\<^sub>2) # \<Psi> \<triangleright> (K\<^sub>1 time-delayed by \<delta>\<tau> on K\<^sub>2 implies K\<^sub>3) # \<Phi> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g"
        using HeronConf_interp_stepwise_timedelayed_cases by simp
      have more_branches: "\<lbrakk> (K\<^sub>1 \<Up> n) # \<Gamma>, n \<turnstile> (K\<^sub>3 sporadic \<lfloor>\<tau>\<^sub>v\<^sub>a\<^sub>r(K\<^sub>2, n) \<oplus> \<delta>\<tau>\<rfloor> on K\<^sub>2) # \<Psi> \<triangleright> (K\<^sub>1 time-delayed by \<delta>\<tau> on K\<^sub>2 implies K\<^sub>3) # \<Phi> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g
                  = \<lbrakk> (K\<^sub>1 \<Up> n) # \<Gamma>, n \<turnstile> \<Psi> \<triangleright> (K\<^sub>3 sporadic \<lfloor>\<tau>\<^sub>v\<^sub>a\<^sub>r(K\<^sub>2, n) \<oplus> \<delta>\<tau>\<rfloor> on K\<^sub>2) # (K\<^sub>1 time-delayed by \<delta>\<tau> on K\<^sub>2 implies K\<^sub>3) # \<Phi> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g
                  \<union> \<lbrakk> (K\<^sub>3 \<Up> n) # (K\<^sub>2 \<Down> n @ \<lfloor>\<tau>\<^sub>v\<^sub>a\<^sub>r(K\<^sub>2, n) \<oplus> \<delta>\<tau>\<rfloor>) # (K\<^sub>1 \<Up> n) # \<Gamma>, n \<turnstile> \<Psi> \<triangleright> (K\<^sub>1 time-delayed by \<delta>\<tau> on K\<^sub>2 implies K\<^sub>3) # \<Phi> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g"
            using HeronConf_interp_stepwise_sporadicon_cases by blast
      have br1: "\<rho> \<in> \<lbrakk> K\<^sub>1 \<not>\<Up> n # \<Gamma>, n \<turnstile> \<Psi> \<triangleright> (K\<^sub>1 time-delayed by \<delta>\<tau> on K\<^sub>2 implies K\<^sub>3) # \<Phi> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g \<Longrightarrow> \<exists>\<Gamma>\<^sub>k \<Psi>\<^sub>k \<Phi>\<^sub>k k.
       \<Gamma>, n \<turnstile> (K\<^sub>1 time-delayed by \<delta>\<tau> on K\<^sub>2 implies K\<^sub>3) # \<Psi> \<triangleright> \<Phi> \<hookrightarrow>\<^bsup>k\<^esup> \<Gamma>\<^sub>k, Suc n \<turnstile> \<Psi>\<^sub>k \<triangleright> \<Phi>\<^sub>k \<and>
       \<rho> \<in> \<lbrakk> \<Gamma>\<^sub>k, Suc n \<turnstile> \<Psi>\<^sub>k \<triangleright> \<Phi>\<^sub>k \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g"
        proof -
          assume h1: "\<rho> \<in> \<lbrakk> K\<^sub>1 \<not>\<Up> n # \<Gamma>, n \<turnstile> \<Psi> \<triangleright> (K\<^sub>1 time-delayed by \<delta>\<tau> on K\<^sub>2 implies K\<^sub>3) # \<Phi> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g"
          then have "\<exists>\<Gamma>\<^sub>k \<Psi>\<^sub>k \<Phi>\<^sub>k k. (K\<^sub>1 \<not>\<Up> n # \<Gamma>, n \<turnstile> \<Psi> \<triangleright> (K\<^sub>1 time-delayed by \<delta>\<tau> on K\<^sub>2 implies K\<^sub>3) # \<Phi>) \<hookrightarrow>\<^bsup>k\<^esup> \<Gamma>\<^sub>k, Suc n \<turnstile> \<Psi>\<^sub>k \<triangleright> \<Phi>\<^sub>k \<and> \<rho> \<in> \<lbrakk> \<Gamma>\<^sub>k, Suc n \<turnstile> \<Psi>\<^sub>k \<triangleright> \<Phi>\<^sub>k \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g"
            using h1 TimeDelayedBy.prems by simp
          then show ?thesis
            by (meson elims_part relpowp_Suc_I2 timedelayed_e1)
        qed
      moreover have br2: "\<rho> \<in> \<lbrakk> K\<^sub>1 \<Up> n # \<Gamma>, n \<turnstile> \<Psi> \<triangleright> (K\<^sub>3 sporadic \<lfloor>\<tau>\<^sub>v\<^sub>a\<^sub>r(K\<^sub>2, n) \<oplus> \<delta>\<tau>\<rfloor> on K\<^sub>2) # (K\<^sub>1 time-delayed by \<delta>\<tau> on K\<^sub>2 implies K\<^sub>3) # \<Phi> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g \<Longrightarrow> \<exists>\<Gamma>\<^sub>k \<Psi>\<^sub>k \<Phi>\<^sub>k k.
       \<Gamma>, n \<turnstile> (K\<^sub>1 time-delayed by \<delta>\<tau> on K\<^sub>2 implies K\<^sub>3) # \<Psi> \<triangleright> \<Phi> \<hookrightarrow>\<^bsup>k\<^esup> \<Gamma>\<^sub>k, Suc n \<turnstile> \<Psi>\<^sub>k \<triangleright> \<Phi>\<^sub>k \<and>
       \<rho> \<in> \<lbrakk> \<Gamma>\<^sub>k, Suc n \<turnstile> \<Psi>\<^sub>k \<triangleright> \<Phi>\<^sub>k \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g"
        proof -
          assume h2: "\<rho> \<in> \<lbrakk> K\<^sub>1 \<Up> n # \<Gamma>, n \<turnstile> \<Psi> \<triangleright> (K\<^sub>3 sporadic \<lfloor>\<tau>\<^sub>v\<^sub>a\<^sub>r(K\<^sub>2, n) \<oplus> \<delta>\<tau>\<rfloor> on K\<^sub>2) # (K\<^sub>1 time-delayed by \<delta>\<tau> on K\<^sub>2 implies K\<^sub>3) # \<Phi> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g"
          then have "\<exists>\<Gamma>\<^sub>k \<Psi>\<^sub>k \<Phi>\<^sub>k k. (K\<^sub>1 \<Up> n # \<Gamma>, n \<turnstile> \<Psi> \<triangleright> (K\<^sub>3 sporadic \<lfloor>\<tau>\<^sub>v\<^sub>a\<^sub>r(K\<^sub>2, n) \<oplus> \<delta>\<tau>\<rfloor> on K\<^sub>2) # (K\<^sub>1 time-delayed by \<delta>\<tau> on K\<^sub>2 implies K\<^sub>3) # \<Phi>) \<hookrightarrow>\<^bsup>k\<^esup> \<Gamma>\<^sub>k, Suc n \<turnstile> \<Psi>\<^sub>k \<triangleright> \<Phi>\<^sub>k \<and> \<rho> \<in> \<lbrakk> \<Gamma>\<^sub>k, Suc n \<turnstile> \<Psi>\<^sub>k \<triangleright> \<Phi>\<^sub>k \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g"
            using h2 TimeDelayedBy.prems by simp
          then show ?thesis
            by (meson elims_part relpowp_Suc_I2 timedelayed_e2 sporadic_on_e1)
        qed
      moreover have br2': "\<rho> \<in> \<lbrakk> (K\<^sub>3 \<Up> n) # (K\<^sub>2 \<Down> n @ \<lfloor>\<tau>\<^sub>v\<^sub>a\<^sub>r(K\<^sub>2, n) \<oplus> \<delta>\<tau>\<rfloor>) # (K\<^sub>1 \<Up> n) # \<Gamma>, n \<turnstile> \<Psi> \<triangleright> (K\<^sub>1 time-delayed by \<delta>\<tau> on K\<^sub>2 implies K\<^sub>3) # \<Phi> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g \<Longrightarrow> \<exists>\<Gamma>\<^sub>k \<Psi>\<^sub>k \<Phi>\<^sub>k k.
       \<Gamma>, n \<turnstile> (K\<^sub>1 time-delayed by \<delta>\<tau> on K\<^sub>2 implies K\<^sub>3) # \<Psi> \<triangleright> \<Phi> \<hookrightarrow>\<^bsup>k\<^esup> \<Gamma>\<^sub>k, Suc n \<turnstile> \<Psi>\<^sub>k \<triangleright> \<Phi>\<^sub>k \<and>
       \<rho> \<in> \<lbrakk> \<Gamma>\<^sub>k, Suc n \<turnstile> \<Psi>\<^sub>k \<triangleright> \<Phi>\<^sub>k \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g"
        proof -
          assume h2: "\<rho> \<in> \<lbrakk> (K\<^sub>3 \<Up> n) # (K\<^sub>2 \<Down> n @ \<lfloor>\<tau>\<^sub>v\<^sub>a\<^sub>r(K\<^sub>2, n) \<oplus> \<delta>\<tau>\<rfloor>) # (K\<^sub>1 \<Up> n) # \<Gamma>, n \<turnstile> \<Psi> \<triangleright> (K\<^sub>1 time-delayed by \<delta>\<tau> on K\<^sub>2 implies K\<^sub>3) # \<Phi> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g"
          then have "\<exists>\<Gamma>\<^sub>k \<Psi>\<^sub>k \<Phi>\<^sub>k k. ((K\<^sub>3 \<Up> n) # (K\<^sub>2 \<Down> n @ \<lfloor>\<tau>\<^sub>v\<^sub>a\<^sub>r(K\<^sub>2, n) \<oplus> \<delta>\<tau>\<rfloor>) # (K\<^sub>1 \<Up> n) # \<Gamma>, n \<turnstile> \<Psi> \<triangleright> (K\<^sub>1 time-delayed by \<delta>\<tau> on K\<^sub>2 implies K\<^sub>3) # \<Phi>) \<hookrightarrow>\<^bsup>k\<^esup> \<Gamma>\<^sub>k, Suc n \<turnstile> \<Psi>\<^sub>k \<triangleright> \<Phi>\<^sub>k \<and> \<rho> \<in> \<lbrakk> \<Gamma>\<^sub>k, Suc n \<turnstile> \<Psi>\<^sub>k \<triangleright> \<Phi>\<^sub>k \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g"
            using h2 TimeDelayedBy.prems by simp
          then show ?thesis
            by (meson elims_part relpowp_Suc_I2 timedelayed_e2 sporadic_on_e2)
        qed
      ultimately show ?case
        using TimeDelayedBy.prems(2) by (metis UnE branches more_branches)
    qed
  qed

lemma instant_index_increase_generalized:
  assumes "n < n\<^sub>k"
  assumes "\<rho> \<in> \<lbrakk> \<Gamma>, n \<turnstile> \<Psi> \<triangleright> \<Phi> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g"
  shows   "\<exists>\<Gamma>\<^sub>k \<Psi>\<^sub>k \<Phi>\<^sub>k k. \<Gamma>, n \<turnstile> \<Psi> \<triangleright> \<Phi>  \<hookrightarrow>\<^bsup>k\<^esup>  \<Gamma>\<^sub>k, n\<^sub>k \<turnstile> \<Psi>\<^sub>k \<triangleright> \<Phi>\<^sub>k
                         \<and> \<rho> \<in> \<lbrakk> \<Gamma>\<^sub>k, n\<^sub>k \<turnstile> \<Psi>\<^sub>k \<triangleright> \<Phi>\<^sub>k \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g"
  proof -
    obtain \<delta>k where diff: "n\<^sub>k = \<delta>k + Suc n"
      using add.commute assms(1) less_iff_Suc_add by auto
    show ?thesis
      proof (subst diff, subst diff, insert assms(2), induct \<delta>k)
        case 0
        then show ?case
          using instant_index_increase assms(2) by simp
      next
        case (Suc \<delta>k)
        have f0: "\<rho> \<in> \<lbrakk> \<Gamma>, n \<turnstile> \<Psi> \<triangleright> \<Phi> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g \<Longrightarrow> \<exists>\<Gamma>\<^sub>k \<Psi>\<^sub>k \<Phi>\<^sub>k k.
             \<Gamma>, n \<turnstile> \<Psi> \<triangleright> \<Phi> \<hookrightarrow>\<^bsup>k\<^esup> \<Gamma>\<^sub>k, \<delta>k + Suc n \<turnstile> \<Psi>\<^sub>k \<triangleright> \<Phi>\<^sub>k \<and>
             \<rho> \<in> \<lbrakk> \<Gamma>\<^sub>k, \<delta>k + Suc n \<turnstile> \<Psi>\<^sub>k \<triangleright> \<Phi>\<^sub>k \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g"
          using Suc.hyps by blast
        obtain \<Gamma>\<^sub>k \<Psi>\<^sub>k \<Phi>\<^sub>k k where cont: "\<Gamma>, n \<turnstile> \<Psi> \<triangleright> \<Phi> \<hookrightarrow>\<^bsup>k\<^esup> \<Gamma>\<^sub>k, \<delta>k + Suc n \<turnstile> \<Psi>\<^sub>k \<triangleright> \<Phi>\<^sub>k \<and> \<rho> \<in> \<lbrakk> \<Gamma>\<^sub>k, \<delta>k + Suc n \<turnstile> \<Psi>\<^sub>k \<triangleright> \<Phi>\<^sub>k \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g" using f0 assms(1)
          using Suc.prems by blast
        then have fcontinue: "\<exists>\<Gamma>\<^sub>k' \<Psi>\<^sub>k' \<Phi>\<^sub>k' k'. \<Gamma>\<^sub>k, \<delta>k + Suc n \<turnstile> \<Psi>\<^sub>k \<triangleright> \<Phi>\<^sub>k \<hookrightarrow>\<^bsup>k'\<^esup> \<Gamma>\<^sub>k', Suc (\<delta>k + Suc n) \<turnstile> \<Psi>\<^sub>k' \<triangleright> \<Phi>\<^sub>k' \<and>
              \<rho> \<in> \<lbrakk> \<Gamma>\<^sub>k', Suc (\<delta>k + Suc n) \<turnstile> \<Psi>\<^sub>k' \<triangleright> \<Phi>\<^sub>k' \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g"
          using f0 cont instant_index_increase by blast
        obtain \<Gamma>\<^sub>k' \<Psi>\<^sub>k' \<Phi>\<^sub>k' k' where cont2: "\<Gamma>\<^sub>k, \<delta>k + Suc n \<turnstile> \<Psi>\<^sub>k \<triangleright> \<Phi>\<^sub>k \<hookrightarrow>\<^bsup>k'\<^esup> \<Gamma>\<^sub>k', Suc (\<delta>k + Suc n) \<turnstile> \<Psi>\<^sub>k' \<triangleright> \<Phi>\<^sub>k' \<and> \<rho> \<in> \<lbrakk> \<Gamma>\<^sub>k', Suc (\<delta>k + Suc n) \<turnstile> \<Psi>\<^sub>k' \<triangleright> \<Phi>\<^sub>k' \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g"
          using Suc.prems using fcontinue cont by blast
        have trans: "\<Gamma>, n \<turnstile> \<Psi> \<triangleright> \<Phi> \<hookrightarrow>\<^bsup>k + k'\<^esup> \<Gamma>\<^sub>k', Suc (\<delta>k + Suc n) \<turnstile> \<Psi>\<^sub>k' \<triangleright> \<Phi>\<^sub>k'"
          using operational_semantics_trans_generalized cont cont2
          by blast
        moreover have suc_assoc: "Suc \<delta>k + Suc n = Suc (\<delta>k + Suc n)"
          by arith
        ultimately show ?case 
          proof (subst suc_assoc)
          show "\<exists>\<Gamma>\<^sub>k \<Psi>\<^sub>k \<Phi>\<^sub>k k.
               \<Gamma>, n \<turnstile> \<Psi> \<triangleright> \<Phi> \<hookrightarrow>\<^bsup>k\<^esup> \<Gamma>\<^sub>k, Suc (\<delta>k + Suc n) \<turnstile> \<Psi>\<^sub>k \<triangleright> \<Phi>\<^sub>k \<and>
               \<rho> \<in> \<lbrakk> \<Gamma>\<^sub>k, Suc \<delta>k + Suc n \<turnstile> \<Psi>\<^sub>k \<triangleright> \<Phi>\<^sub>k \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g"
            using cont2 local.trans by auto
          qed
    qed
  qed

text \<open>Any run from initial specification [\<Psi>] has a corresponding configuration
      indexed at [n]-th instant starting from initial configuration.\<close>
theorem progress:
  assumes "\<rho> \<in> \<lbrakk>\<lbrakk> \<Psi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L"
  shows   "\<exists>k \<Gamma>\<^sub>k \<Psi>\<^sub>k \<Phi>\<^sub>k. [], 0 \<turnstile> \<Psi> \<triangleright> []  \<hookrightarrow>\<^bsup>k\<^esup>  \<Gamma>\<^sub>k, n \<turnstile> \<Psi>\<^sub>k \<triangleright> \<Phi>\<^sub>k
                         \<and> \<rho> \<in> \<lbrakk> \<Gamma>\<^sub>k, n \<turnstile> \<Psi>\<^sub>k \<triangleright> \<Phi>\<^sub>k \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g"
  using instant_index_increase_generalized
  by (metis assms neq0_conv relpowp_0_I solve_start)

section \<open>Local termination\<close>

primrec measure_interpretation :: "'\<tau> :: linordered_field TESL_formula \<Rightarrow> nat" ("\<mu>") where
    "\<mu> [] = (0::nat)"
  | "\<mu> (\<phi> # \<Phi>) = (case \<phi> of
                        _ sporadic _ on _ \<Rightarrow> 1 + \<mu> \<Phi>
                      | _                 \<Rightarrow> 2 + \<mu> \<Phi>)"

fun measure_interpretation_config :: "'\<tau> :: linordered_field config \<Rightarrow> nat" ("\<mu>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g") where
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

text \<open>The relation made up of elimination rules is well-founded.\<close>
theorem instant_computation_termination:
  shows "wfP (\<lambda>(\<S>\<^sub>1:: 'a :: linordered_field config) \<S>\<^sub>2. \<S>\<^sub>1  \<hookrightarrow>\<^sub>e\<^sup>\<leftarrow>  \<S>\<^sub>2)"
  proof (simp add: wfP_def)
    show "wf {((\<S>\<^sub>1:: 'a :: linordered_field config), \<S>\<^sub>2). \<S>\<^sub>1 \<hookrightarrow>\<^sub>e\<^sup>\<leftarrow> \<S>\<^sub>2}"
    apply (rule wf_subset)
    proof -
      have "measure \<mu>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g = { (\<S>\<^sub>2, (\<S>\<^sub>1:: 'a :: linordered_field config)). \<mu>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g \<S>\<^sub>2 < \<mu>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g \<S>\<^sub>1 }"
        by (simp add: inv_image_def less_eq measure_def)
      then show "{((\<S>\<^sub>1:: 'a :: linordered_field config), \<S>\<^sub>2). \<S>\<^sub>1 \<hookrightarrow>\<^sub>e\<^sup>\<leftarrow> \<S>\<^sub>2} \<subseteq> (measure \<mu>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g)"
        using elimation_rules_strictly_decreasing_meas' operational_semantics_elim_inv_def by blast
      show "wf (measure measure_interpretation_config)"
        by simp
    qed
  qed


end