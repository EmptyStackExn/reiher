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
    have "\<rho> \<in> \<lbrakk>\<lbrakk> \<Psi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup> \<inter> \<lbrakk>\<lbrakk> [K\<^sub>1 implies K\<^sub>2] \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^esup> \<inter> \<lbrakk>\<lbrakk> \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^esup>"
      using assms(2) by auto
    then have "\<rho> \<in> \<lbrakk>\<lbrakk> [K\<^sub>1 implies K\<^sub>2] \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup>"
      using assms(1)
      sorry
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
    also have ih: "(\<forall>m\<ge>Suc n. #\<^sup>< \<rho> K\<^sub>1 m \<ge> #\<^sup>\<le> \<rho> K\<^sub>2 m)"
      using split
      sorry
    then have "\<rho> \<in> \<lbrakk> K\<^sub>1 precedes K\<^sub>2 \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup>"
      using bh ih
      sorry
    then show ?thesis
      using assms(2) by auto
  qed

end