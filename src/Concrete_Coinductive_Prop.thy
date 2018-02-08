theory Concrete_Coinductive_Prop
imports
    "ConcreteOperational"
    "Denotational"
    "Coinductive_Prop"

begin

fun HeronConf_interpretation_concrete
  :: "'\<tau>::linordered_field concrete_config \<Rightarrow> bool" ("\<lparr> _ \<rparr>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g" 71) where
  "\<lparr> \<rho>, n \<turnstile> \<Psi> \<triangleright> \<Phi> \<rparr>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g = (\<rho> \<in> \<lbrakk>\<lbrakk> \<Psi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup> \<inter> \<lbrakk>\<lbrakk> \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^esup>)"

section {* Soundness *}

lemma sound_reduction_concrete_intro:
  assumes "\<lparr> \<rho>, Suc n \<turnstile> \<Phi> \<triangleright> [] \<rparr>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g"
  shows "\<lparr> \<rho>, n \<turnstile> [] \<triangleright> \<Phi> \<rparr>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g"
  proof -
    have "\<rho> \<in> \<lbrakk>\<lbrakk> \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^esup>"
      using assms by auto
    then show ?thesis
      by auto
  qed

lemma sound_reduction_concrete_sporadic_e1:
  assumes "\<rho> \<turnstile> (K \<not>\<Up> n)"
  assumes "\<lparr> \<rho>, n \<turnstile> \<Psi> \<triangleright> ((K sporadic \<tau>) # \<Phi>) \<rparr>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g"
  shows "\<lparr> \<rho>, n \<turnstile> ((K sporadic \<tau>) # \<Psi>) \<triangleright> \<Phi> \<rparr>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g"
  proof -
    have f1: "\<rho> \<in> \<lbrakk>\<lbrakk> \<Psi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup> \<inter> \<lbrakk> K sporadic \<tau> \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^esup> \<inter> \<lbrakk>\<lbrakk> \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^esup>"
      using assms(2) by auto
    then have "\<exists>m\<ge>Suc n. hamlet ((Rep_run \<rho>) m K) = True \<and> time ((Rep_run \<rho>) m K) = \<tau>"
      by auto
    then have "\<exists>m\<ge>n. hamlet ((Rep_run \<rho>) m K) = True \<and> time ((Rep_run \<rho>) m K) = \<tau>"
      using Suc_leD by blast
    then show ?thesis
      using f1 by auto
  qed

lemma sound_reduction_concrete_sporadic_e2:
  assumes "\<rho> \<turnstile> (K \<Up> n)"
  assumes "\<rho> \<turnstile> (K \<Down> n @ \<lfloor>\<tau>\<rfloor>)"
  assumes "\<lparr> \<rho>, n \<turnstile> \<Psi> \<triangleright> \<Phi> \<rparr>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g"
  shows "\<lparr> \<rho>, n \<turnstile> ((K sporadic \<tau>) # \<Psi>) \<triangleright> \<Phi> \<rparr>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g"
  proof -
    have "\<rho> \<in> \<lbrakk>\<lbrakk> \<Psi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup> \<inter> \<lbrakk>\<lbrakk> \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^esup>"
      using assms(3) by auto
    also have "\<exists>m\<ge>n. hamlet ((Rep_run \<rho>) m K) = True \<and> time ((Rep_run \<rho>) m K) = \<tau>"
      using assms(1) assms(2) by auto
    then have "\<rho> \<in> \<lbrakk> K sporadic \<tau> \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup>"
      by auto
    then show ?thesis
      using calculation by auto
  qed

lemma sound_reduction_concrete_sporadic_on_e1:
  assumes "\<rho> \<turnstile> (K\<^sub>1 \<not>\<Up> n)"
  assumes "\<lparr> \<rho>, n \<turnstile> \<Psi> \<triangleright> ((K\<^sub>1 sporadic \<lfloor>\<tau>\<rfloor> on K\<^sub>2) # \<Phi>) \<rparr>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g"
  shows "\<lparr> \<rho>, n \<turnstile> ((K\<^sub>1 sporadic \<lfloor>\<tau>\<rfloor> on K\<^sub>2) # \<Psi>) \<triangleright> \<Phi> \<rparr>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g"
  proof -
    have f1: "\<rho> \<in> \<lbrakk>\<lbrakk> \<Psi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup> \<inter> \<lbrakk> K\<^sub>1 sporadic \<lfloor>\<tau>\<rfloor> on K\<^sub>2 \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^esup> \<inter> \<lbrakk>\<lbrakk> \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^esup>"
      using assms(2) by auto
    then have "\<exists>m\<ge>Suc n. hamlet ((Rep_run \<rho>) m K\<^sub>1) = True \<and> time ((Rep_run \<rho>) m K\<^sub>2) = \<tau>"
      by auto
    then have "\<exists>m\<ge>n. hamlet ((Rep_run \<rho>) m K\<^sub>1) = True \<and> time ((Rep_run \<rho>) m K\<^sub>2) = \<tau>"
      using Suc_leD by blast
    then show ?thesis
      using f1 by auto
  qed

lemma sound_reduction_concrete_sporadic_on_e2:
  assumes "\<rho> \<turnstile> (K\<^sub>1 \<Up> n)"
  assumes "\<rho> \<turnstile> (K\<^sub>2 \<Down> n @ \<lfloor> \<tau> \<rfloor>)"
  assumes "\<lparr> \<rho>, n \<turnstile> \<Psi> \<triangleright> \<Phi> \<rparr>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g"
  shows "\<lparr> \<rho>, n \<turnstile> ((K\<^sub>1 sporadic \<lfloor>\<tau>\<rfloor> on K\<^sub>2) # \<Psi>) \<triangleright> \<Phi> \<rparr>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g"
  proof -
    have "\<rho> \<in> \<lbrakk>\<lbrakk> \<Psi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup> \<inter> \<lbrakk>\<lbrakk> \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^esup>"
      using assms(3) by auto
    also have "\<exists>m\<ge>n. hamlet ((Rep_run \<rho>) m K\<^sub>1) = True \<and> time ((Rep_run \<rho>) m K\<^sub>2) = \<tau>"
      using assms(1) assms(2) by auto
    then have "\<rho> \<in> \<lbrakk> K\<^sub>1 sporadic \<lfloor>\<tau>\<rfloor> on K\<^sub>2 \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup>"
      by auto
    then show ?thesis
      using calculation by auto
  qed

lemma sound_reduction_concrete_tagrel_e:
  assumes "\<rho> \<turnstile> (\<tau>\<^sub>v\<^sub>a\<^sub>r(K\<^sub>1, n)) \<doteq> \<alpha> * \<tau>\<^sub>v\<^sub>a\<^sub>r(K\<^sub>2, n) + \<beta>"
  assumes "\<lparr> \<rho>, n \<turnstile> \<Psi> \<triangleright> ((tag-relation K\<^sub>1 = \<alpha> * K\<^sub>2 + \<beta>) # \<Phi>) \<rparr>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g"
  shows "\<lparr> \<rho>, n \<turnstile> ((tag-relation K\<^sub>1 = \<alpha> * K\<^sub>2 + \<beta>) # \<Psi>) \<triangleright> \<Phi> \<rparr>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g"
  proof -
    have split: "\<rho> \<in> \<lbrakk>\<lbrakk> \<Psi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup> \<inter> \<lbrakk> tag-relation K\<^sub>1 = \<alpha> * K\<^sub>2 + \<beta> \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^esup>
                                     \<inter> \<lbrakk>\<lbrakk> \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^esup>"
      using assms(2) by auto
    then have "\<forall>m\<ge>Suc n. time ((Rep_run \<rho>) m K\<^sub>1) = \<alpha> * time ((Rep_run \<rho>) m K\<^sub>2) + \<beta>"
      by auto
    also have "\<rho> \<in> \<lbrakk> tag-relation K\<^sub>1 = \<alpha> * K\<^sub>2 + \<beta> \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup>"
      proof -
        have "\<forall>m\<ge>n. time ((Rep_run \<rho>) m K\<^sub>1) = \<alpha> * time ((Rep_run \<rho>) m K\<^sub>2) + \<beta>"
          by (metis assms(1) calculation le_antisym not_less_eq_eq
                    symbolic_run_interpretation_primitive_predic.simps(5))
        then show ?thesis
          by auto
      qed
    then show ?thesis
      using split by auto
  qed

lemma sound_reduction_concrete_tagrelgen_e:
  assumes "\<rho> \<turnstile> \<langle>\<tau>\<^sub>v\<^sub>a\<^sub>r(K\<^sub>1, n), \<tau>\<^sub>v\<^sub>a\<^sub>r(K\<^sub>2, n)\<rangle> \<epsilon> R"
  assumes "\<lparr> \<rho>, n \<turnstile> \<Psi> \<triangleright> ((tag-relation \<langle>K\<^sub>1, K\<^sub>2\<rangle> \<in> R) # \<Phi>) \<rparr>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g"
  shows "\<lparr> \<rho>, n \<turnstile> ((tag-relation \<langle>K\<^sub>1, K\<^sub>2\<rangle> \<in> R) # \<Psi>) \<triangleright> \<Phi> \<rparr>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g"
  proof -
    have split: "\<rho> \<in> \<lbrakk>\<lbrakk> \<Psi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup> \<inter> \<lbrakk> tag-relation \<langle>K\<^sub>1, K\<^sub>2\<rangle> \<in> R \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^esup>
                                     \<inter> \<lbrakk>\<lbrakk> \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^esup>"
      using assms(2) by auto
    then have "\<forall>m\<ge>Suc n. R (time ((Rep_run \<rho>) n K\<^sub>1), time ((Rep_run \<rho>) n K\<^sub>2))"
      using assms(1) symbolic_run_interpretation_primitive_predic.simps(6) by blast
    also have "\<rho> \<in> \<lbrakk> tag-relation \<langle>K\<^sub>1, K\<^sub>2\<rangle> \<in> R \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup>"
      proof -
        have "\<forall>m\<ge>n. R (time ((Rep_run \<rho>) n K\<^sub>1), time ((Rep_run \<rho>) n K\<^sub>2))"
          by (metis assms(1) calculation le_antisym not_less_eq_eq
                    symbolic_run_interpretation_primitive_predic.simps(5))
        then show ?thesis
          by (metis (mono_tags, lifting) HeronConf_interpretation_concrete.simps IntD1 IntD2 IntI
              TESL_interp_stepwise_tagrelgen_coind_unfold TESL_interpretation_stepwise_cons_morph
              assms(1) assms(2) mem_Collect_eq symbolic_run_interpretation_primitive.simps(6)
              symbolic_run_interpretation_primitive_predic.simps(6))
      qed
    then show ?thesis
      using split by auto
  qed

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

lemma sound_reduction_concrete_implies_e2:
  assumes "\<rho> \<turnstile> (K\<^sub>1 \<Up> n)"
  assumes "\<rho> \<turnstile> (K\<^sub>2 \<Up> n)"
  assumes "\<lparr> \<rho>, n \<turnstile> \<Psi> \<triangleright> ((K\<^sub>1 implies K\<^sub>2) # \<Phi>) \<rparr>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g"
  shows "\<lparr> \<rho>, n \<turnstile> ((K\<^sub>1 implies K\<^sub>2) # \<Psi>) \<triangleright> \<Phi> \<rparr>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g"
  proof -
    have split: "\<rho> \<in> \<lbrakk>\<lbrakk> \<Psi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup> \<inter> \<lbrakk> K\<^sub>1 implies K\<^sub>2 \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^esup> \<inter> \<lbrakk>\<lbrakk> \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^esup>"
      using assms(3) by auto
    then have bh: "hamlet ((Rep_run \<rho>) n K\<^sub>1) \<longrightarrow> hamlet ((Rep_run \<rho>) n K\<^sub>2)"
      using assms(2) symbolic_run_interpretation_primitive_predic.simps(1) by blast
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
          using Suc_leI calculation ih less_le by blast
        then show ?thesis
          by auto
      qed
    then show ?thesis
      using assms(3) by auto
  qed

lemma sound_reduction_concrete_timedelayed_e1:
  assumes "\<rho> \<turnstile> (K\<^sub>1 \<not>\<Up> n)"
  assumes "\<lparr> \<rho>, n \<turnstile> \<Psi> \<triangleright> ((K\<^sub>1 time-delayed by \<delta>\<tau> on K\<^sub>2 implies K\<^sub>3) # \<Phi>) \<rparr>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g"
  shows "\<lparr> \<rho>, n \<turnstile> ((K\<^sub>1 time-delayed by \<delta>\<tau> on K\<^sub>2 implies K\<^sub>3) # \<Psi>) \<triangleright> \<Phi> \<rparr>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g"
  proof -
    have split: "\<rho> \<in> \<lbrakk>\<lbrakk> \<Psi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup> \<inter> \<lbrakk> K\<^sub>1 time-delayed by \<delta>\<tau> on K\<^sub>2 implies K\<^sub>3 \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^esup>
                   \<inter> \<lbrakk>\<lbrakk> \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^esup>"
      using assms(2) by auto
    then have "\<forall>p\<ge>Suc n. hamlet ((Rep_run \<rho>) p K\<^sub>1) \<longrightarrow>
                 (let measured_time = time ((Rep_run \<rho>) p K\<^sub>2) in
                  \<exists>m \<ge> p. hamlet ((Rep_run \<rho>) m K\<^sub>3)
                          \<and> time ((Rep_run \<rho>) m K\<^sub>2) = measured_time + \<delta>\<tau>
                 )"
      proof -
        have "\<rho> \<in> \<lbrakk> K\<^sub>1 time-delayed by \<delta>\<tau> on K\<^sub>2 implies K\<^sub>3 \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^esup>"
          using assms(2) by auto
        then show ?thesis
          by auto
      qed
    then have "\<rho> \<in> \<lbrakk> K\<^sub>1 time-delayed by \<delta>\<tau> on K\<^sub>2 implies K\<^sub>3 \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup>"
      by (smt TESL_interpretation_atomic_stepwise.simps(7) assms(1) le_antisym mem_Collect_eq
              not_less_eq_eq symbolic_run_interpretation_primitive_predic.simps(2))
    then show ?thesis
      using assms(2) by auto
  qed

lemma sound_reduction_concrete_timedelayed_e2:
  assumes "\<rho> \<turnstile> (K\<^sub>1 \<Up> n)"
  assumes "\<lparr> \<rho>, n \<turnstile> ((K\<^sub>3 sporadic \<lfloor>\<tau>\<^sub>v\<^sub>a\<^sub>r(K\<^sub>2, n) \<oplus> \<delta>\<tau>\<rfloor> on K\<^sub>2) # \<Psi>)
                  \<triangleright> ((K\<^sub>1 time-delayed by \<delta>\<tau> on K\<^sub>2 implies K\<^sub>3) # \<Phi>) \<rparr>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g"
  shows "\<lparr> \<rho>, n \<turnstile> ((K\<^sub>1 time-delayed by \<delta>\<tau> on K\<^sub>2 implies K\<^sub>3) # \<Psi>) \<triangleright> \<Phi> \<rparr>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g"
  proof -
    have split: "\<rho> \<in> \<lbrakk> K\<^sub>3 sporadic \<lfloor>\<tau>\<^sub>v\<^sub>a\<^sub>r(K\<^sub>2, n) \<oplus> \<delta>\<tau>\<rfloor> on K\<^sub>2 \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup> \<inter> \<lbrakk>\<lbrakk> \<Psi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup>
                   \<inter> \<lbrakk> K\<^sub>1 time-delayed by \<delta>\<tau> on K\<^sub>2 implies K\<^sub>3 \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^esup> \<inter> \<lbrakk>\<lbrakk> \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^esup>"
      using assms(2) by auto
    then have "\<forall>p\<ge>Suc n. hamlet ((Rep_run \<rho>) p K\<^sub>1) \<longrightarrow>
                 (let measured_time = time ((Rep_run \<rho>) p K\<^sub>2) in
                  \<exists>m \<ge> p. hamlet ((Rep_run \<rho>) m K\<^sub>3)
                          \<and> time ((Rep_run \<rho>) m K\<^sub>2) = measured_time + \<delta>\<tau>
                 )"
      proof -
        have "\<rho> \<in> \<lbrakk> K\<^sub>1 time-delayed by \<delta>\<tau> on K\<^sub>2 implies K\<^sub>3 \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^esup>"
          using assms(2) by auto
        then show ?thesis
          by auto
      qed
    moreover have "\<exists>m \<ge> n. hamlet ((Rep_run \<rho>) m K\<^sub>3)
                          \<and> time ((Rep_run \<rho>) m K\<^sub>2) = time ((Rep_run \<rho>) n K\<^sub>2) + \<delta>\<tau>"
      using split by auto
    then have fext: "\<forall>p\<ge>n. hamlet ((Rep_run \<rho>) p K\<^sub>1) \<longrightarrow>
                 (let measured_time = time ((Rep_run \<rho>) p K\<^sub>2) in
                  \<exists>m \<ge> p. hamlet ((Rep_run \<rho>) m K\<^sub>3)
                          \<and> time ((Rep_run \<rho>) m K\<^sub>2) = measured_time + \<delta>\<tau>
                 )"
      by (metis calculation le_antisym not_less_eq_eq)
    ultimately show ?thesis
      proof -
        have "\<rho> \<in> \<lbrakk> K\<^sub>1 time-delayed by \<delta>\<tau> on K\<^sub>2 implies K\<^sub>3 \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup>"
          using TESL_interpretation_atomic_stepwise.simps(7) fext by blast
        then show ?thesis
          using assms(2) by auto
      qed
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

fun local_run_assumption :: "'\<tau>::linordered_field TESL_atomic \<Rightarrow> '\<tau> run \<Rightarrow> nat \<Rightarrow> bool" where
    "local_run_assumption (K sporadic \<tau>) \<rho> n =
      (True
      \<or> (\<rho> \<turnstile> (K \<Up> n) \<and> \<rho> \<turnstile> (K \<Down> n @ \<lfloor>\<tau>\<rfloor>)))"
  | "local_run_assumption (K\<^sub>1 sporadic \<tau> on K\<^sub>2) \<rho> n = 
      (True
      \<or> (\<rho> \<turnstile> (K\<^sub>1 \<Up> n) \<and> \<rho> \<turnstile> (K\<^sub>2 \<Down> n @ \<tau>)))"
  | "local_run_assumption (tag-relation K\<^sub>1 = \<alpha> * K\<^sub>2 + \<beta>) \<rho> n =
      \<rho> \<turnstile> ((\<tau>\<^sub>v\<^sub>a\<^sub>r(K\<^sub>1, n)) \<doteq> \<alpha> * \<tau>\<^sub>v\<^sub>a\<^sub>r(K\<^sub>2, n) + \<beta>)"
  | "local_run_assumption (tag-relation \<langle>K\<^sub>1, K\<^sub>2\<rangle> \<in> R) \<rho> n =
      \<rho> \<turnstile> (\<langle>\<tau>\<^sub>v\<^sub>a\<^sub>r(K\<^sub>1, n), \<tau>\<^sub>v\<^sub>a\<^sub>r(K\<^sub>2, n)\<rangle> \<epsilon> R)"
  | "local_run_assumption (master implies slave) \<rho> n =
      (\<rho> \<turnstile> (master \<not>\<Up> n)
      \<or> (\<rho> \<turnstile> (master \<Up> n) \<and> \<rho> \<turnstile> (slave \<Up> n)))"
  | "local_run_assumption (master time-delayed by \<delta>\<tau> on measuring implies slave) \<rho> n = 
      (\<rho> \<turnstile> (master \<not>\<Up> n)
      \<or> \<rho> \<turnstile> (master \<Up> n))"
  | "local_run_assumption (master precedes slave) \<rho> n =
      (#\<^sup>< \<rho> master n \<ge> #\<^sup>\<le> \<rho> slave n)"

theorem sound_reduction_concrete:
  assumes "(\<Gamma>\<^sub>1, n\<^sub>1 \<turnstile> \<psi> # \<Psi>\<^sub>1 \<triangleright> \<Phi>\<^sub>1)  \<leadsto>\<^sub>e  (\<Gamma>\<^sub>2, n\<^sub>2 \<turnstile> \<Psi>\<^sub>2 \<triangleright> \<Phi>\<^sub>2)"
  assumes "local_run_assumption \<psi> \<rho> n"
  assumes "\<lparr> \<Gamma>\<^sub>2, n\<^sub>2 \<turnstile> \<Psi>\<^sub>2 \<triangleright> \<Phi>\<^sub>2 \<rparr>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g"
  shows "\<lparr> \<Gamma>\<^sub>1, n\<^sub>1 \<turnstile> \<psi> # \<Psi>\<^sub>1 \<triangleright> \<Phi>\<^sub>1 \<rparr>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g"
  proof (insert assms, erule concrete_operational_semantics_elim.cases)
    show "\<And>\<rho> n K \<tau> \<Psi> \<Phi>.
       (\<Gamma>\<^sub>1, n\<^sub>1 \<turnstile> \<psi> # \<Psi>\<^sub>1 \<triangleright> \<Phi>\<^sub>1) =
       (\<rho>, n \<turnstile> (K sporadic \<tau>) # \<Psi> \<triangleright> \<Phi>) \<Longrightarrow>
       (\<Gamma>\<^sub>2, n\<^sub>2 \<turnstile> \<Psi>\<^sub>2 \<triangleright> \<Phi>\<^sub>2 = \<rho>, n \<turnstile> \<Psi> \<triangleright> (K sporadic \<tau>) # \<Phi>) \<Longrightarrow>
       \<lparr> \<Gamma>\<^sub>1, n\<^sub>1 \<turnstile> \<psi> # \<Psi>\<^sub>1 \<triangleright> \<Phi>\<^sub>1 \<rparr>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g"
      using sound_reduction_concrete_sporadic_e1
      sorry  
  sorry  

section {* Completeness *}

lemma complete_direct_successors_concrete_precedes_e:
  assumes "\<lparr> \<rho>, n \<turnstile> ((K\<^sub>1 precedes K\<^sub>2) # \<Psi>) \<triangleright> \<Phi> \<rparr>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g"
  shows "#\<^sup>< \<rho> K\<^sub>1 n \<ge> #\<^sup>\<le> \<rho> K\<^sub>2 n"
  and "\<lparr> \<rho>, n \<turnstile> \<Psi> \<triangleright> ((K\<^sub>1 precedes K\<^sub>2) # \<Phi>) \<rparr>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g"
  using assms by auto

end