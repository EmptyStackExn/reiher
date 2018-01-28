theory Concrete_Coinductive_Prop
imports
    "ConcreteOperational"
    "Denotational"
    "Coinductive_Prop"

begin

fun HeronConf_interpretation_concrete
  :: "'\<tau>::linordered_field concrete_config \<Rightarrow> bool" ("\<lparr> _ \<rparr>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g" 71) where
  "\<lparr> \<rho>, n \<turnstile> \<Psi> \<triangleright> \<Phi> \<rparr>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g = (\<rho> \<in> \<lbrakk>\<lbrakk> \<Psi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup> \<inter> \<lbrakk>\<lbrakk> \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^esup>)"

lemma sound_reduction_concrete_implies_e1:
  assumes "\<rho> \<turnstile> (K\<^sub>1 \<not>\<Up> n)"
  assumes "\<lparr> \<rho>, n \<turnstile> \<Psi> \<triangleright> ((K\<^sub>1 implies K\<^sub>2) # \<Phi>) \<rparr>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g"
  shows "\<lparr> \<rho>, n \<turnstile> ((K\<^sub>1 implies K\<^sub>2) # \<Psi>) \<triangleright> \<Phi> \<rparr>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g"
  proof -
    have split: "\<rho> \<in> \<lbrakk>\<lbrakk> \<Psi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup> \<inter> \<lbrakk> K\<^sub>1 implies K\<^sub>2 \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^esup> \<inter> \<lbrakk>\<lbrakk> \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^esup>"
      using assms(2) by auto
    then have bh: "hamlet ((Rep_run \<rho>) n K\<^sub>1) \<longrightarrow> hamlet ((Rep_run \<rho>) n K\<^sub>2)"
      using assms(1) symbolic_run_interpretation_primitive_predic.simps(2) by blast
    also have ih: "\<forall>m\<ge>Suc n. hamlet ((Rep_run \<rho>) m K\<^sub>1) \<longrightarrow> hamlet ((Rep_run \<rho>) m K\<^sub>2)"
      proof -
        have "\<rho> \<in> \<lbrakk> K\<^sub>1 implies K\<^sub>2 \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^esup>"
          using split by auto
        then show ?thesis
          by auto
      qed
    then have "\<rho> \<in> \<lbrakk> K\<^sub>1 implies K\<^sub>2 \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup>"
      proof -
        have "\<forall>m\<ge>n. hamlet ((Rep_run \<rho>) m K\<^sub>1) \<longrightarrow> hamlet ((Rep_run \<rho>) m K\<^sub>2)"
          by (metis Suc_leI assms(1) ih linorder_neqE_nat not_less
                    symbolic_run_interpretation_primitive_predic.simps(2))
        then show ?thesis
          by auto
      qed
    then show ?thesis
      using assms(2) by auto
  qed

lemma sound_reduction_concrete_precedes_e:
  assumes "#\<^sup>< \<rho> K\<^sub>1 n \<ge> #\<^sup>\<le> \<rho> K\<^sub>2 n"
  assumes "\<lparr> \<rho>, n \<turnstile> \<Psi> \<triangleright> ((K\<^sub>1 precedes K\<^sub>2) # \<Phi>) \<rparr>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g"
  shows "\<lparr> \<rho>, n \<turnstile> ((K\<^sub>1 precedes K\<^sub>2) # \<Psi>) \<triangleright> \<Phi> \<rparr>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g"
  proof -
    have split: "\<rho> \<in> \<lbrakk>\<lbrakk> \<Psi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup> \<inter> \<lbrakk> K\<^sub>1 precedes K\<^sub>2 \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^esup> \<inter> \<lbrakk>\<lbrakk> \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^esup>"
      using assms(2) by auto
    then have bh: "#\<^sup>< \<rho> K\<^sub>1 n \<ge> #\<^sup>\<le> \<rho> K\<^sub>2 n"
      using assms(1) by blast
    also have ih: "\<forall>m\<ge>Suc n. #\<^sup>< \<rho> K\<^sub>1 m \<ge> #\<^sup>\<le> \<rho> K\<^sub>2 m"
      proof -
        have "\<rho> \<in> \<lbrakk> K\<^sub>1 precedes K\<^sub>2 \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^esup>"
          using split by auto
        then show ?thesis
          using TESL_interpretation_atomic_stepwise.simps(8) by blast
      qed
    then have "\<rho> \<in> \<lbrakk> K\<^sub>1 precedes K\<^sub>2 \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup>"
      proof -
        have "\<forall>m\<ge>n. #\<^sup>< \<rho> K\<^sub>1 m \<ge> #\<^sup>\<le> \<rho> K\<^sub>2 m"
          using bh ih by (metis le_antisym not_less_eq_eq)
        then show ?thesis
          by simp
      qed
    then show ?thesis
      using assms(2) by auto
  qed

lemma complete_direct_successors_concrete_precedes_e:
  assumes "\<lparr> \<rho>, n \<turnstile> ((K\<^sub>1 precedes K\<^sub>2) # \<Psi>) \<triangleright> \<Phi> \<rparr>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g"
  shows "#\<^sup>< \<rho> K\<^sub>1 n \<ge> #\<^sup>\<le> \<rho> K\<^sub>2 n"
  and "\<lparr> \<rho>, n \<turnstile> \<Psi> \<triangleright> ((K\<^sub>1 precedes K\<^sub>2) # \<Phi>) \<rparr>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g"
  using assms by auto

end