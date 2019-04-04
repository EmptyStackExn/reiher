chapter \<open>Operational Semantics\<close>
text\<open>\label{chap:operational_semantics}\<close>

theory Operational
imports
  SymbolicPrimitive

begin

section\<open>Operational steps\<close>

abbreviation uncurry_conf
  ::\<open>('\<tau>::linordered_field) system \<Rightarrow> instant_index \<Rightarrow> '\<tau> TESL_formula \<Rightarrow> '\<tau> TESL_formula
      \<Rightarrow> '\<tau> config\<close>                                                  ("_, _ \<turnstile> _ \<triangleright> _" 80)
where
  \<open>\<Gamma>, n \<turnstile> \<Psi> \<triangleright> \<Phi> \<equiv> (\<Gamma>, n, \<Psi>, \<Phi>)\<close>

inductive operational_semantics_intro
  ::\<open>('\<tau>::linordered_field) config \<Rightarrow> '\<tau> config \<Rightarrow> bool\<close>              ("_ \<hookrightarrow>\<^sub>i _" 70)
where
  instant_i:
  \<open>(\<Gamma>, n \<turnstile> [] \<triangleright> \<Phi>) \<hookrightarrow>\<^sub>i  (\<Gamma>, Suc n \<turnstile> \<Phi> \<triangleright> [])\<close>

inductive operational_semantics_elim
  ::\<open>('\<tau>::linordered_field) config \<Rightarrow> '\<tau> config \<Rightarrow> bool\<close>              ("_ \<hookrightarrow>\<^sub>e _" 70)
where
  sporadic_on_e1:
  \<open>(\<Gamma>, n \<turnstile> ((K\<^sub>1 sporadic \<tau> on K\<^sub>2) # \<Psi>) \<triangleright> \<Phi>)
     \<hookrightarrow>\<^sub>e  (\<Gamma>, n \<turnstile> \<Psi> \<triangleright> ((K\<^sub>1 sporadic \<tau> on K\<^sub>2) # \<Phi>))\<close>
| sporadic_on_e2:
  \<open>(\<Gamma>, n \<turnstile> ((K\<^sub>1 sporadic \<tau> on K\<^sub>2) # \<Psi>) \<triangleright> \<Phi>)
     \<hookrightarrow>\<^sub>e  (((K\<^sub>1 \<Up> n) # (K\<^sub>2 \<Down> n @ \<tau>) # \<Gamma>), n \<turnstile> \<Psi> \<triangleright> \<Phi>)\<close>
| tagrel_e:
  \<open>(\<Gamma>, n \<turnstile> ((time-relation \<lfloor>K\<^sub>1, K\<^sub>2\<rfloor> \<in> R) # \<Psi>) \<triangleright> \<Phi>)
     \<hookrightarrow>\<^sub>e  (((\<lfloor>\<tau>\<^sub>v\<^sub>a\<^sub>r(K\<^sub>1, n), \<tau>\<^sub>v\<^sub>a\<^sub>r(K\<^sub>2, n)\<rfloor> \<in> R) # \<Gamma>), n \<turnstile> \<Psi> \<triangleright> ((time-relation \<lfloor>K\<^sub>1, K\<^sub>2\<rfloor> \<in> R) # \<Phi>))\<close>
| implies_e1:
  \<open>(\<Gamma>, n \<turnstile> ((K\<^sub>1 implies K\<^sub>2) # \<Psi>) \<triangleright> \<Phi>)
     \<hookrightarrow>\<^sub>e  (((K\<^sub>1 \<not>\<Up> n) # \<Gamma>), n \<turnstile> \<Psi> \<triangleright> ((K\<^sub>1 implies K\<^sub>2) # \<Phi>))\<close>
| implies_e2:
  \<open>(\<Gamma>, n \<turnstile> ((K\<^sub>1 implies K\<^sub>2) # \<Psi>) \<triangleright> \<Phi>)
     \<hookrightarrow>\<^sub>e  (((K\<^sub>1 \<Up> n) # (K\<^sub>2 \<Up> n) # \<Gamma>), n \<turnstile> \<Psi> \<triangleright> ((K\<^sub>1 implies K\<^sub>2) # \<Phi>))\<close>
| implies_not_e1:
  \<open>(\<Gamma>, n \<turnstile> ((K\<^sub>1 implies not K\<^sub>2) # \<Psi>) \<triangleright> \<Phi>)
     \<hookrightarrow>\<^sub>e  (((K\<^sub>1 \<not>\<Up> n) # \<Gamma>), n \<turnstile> \<Psi> \<triangleright> ((K\<^sub>1 implies not K\<^sub>2) # \<Phi>))\<close>
| implies_not_e2:
  \<open>(\<Gamma>, n \<turnstile> ((K\<^sub>1 implies not K\<^sub>2) # \<Psi>) \<triangleright> \<Phi>)
     \<hookrightarrow>\<^sub>e  (((K\<^sub>1 \<Up> n) # (K\<^sub>2 \<not>\<Up> n) # \<Gamma>), n \<turnstile> \<Psi> \<triangleright> ((K\<^sub>1 implies not K\<^sub>2) # \<Phi>))\<close>
| timedelayed_e1:
  \<open>(\<Gamma>, n \<turnstile> ((K\<^sub>1 time-delayed by \<delta>\<tau> on K\<^sub>2 implies K\<^sub>3) # \<Psi>) \<triangleright> \<Phi>)
     \<hookrightarrow>\<^sub>e  (((K\<^sub>1 \<not>\<Up> n) # \<Gamma>), n \<turnstile> \<Psi> \<triangleright> ((K\<^sub>1 time-delayed by \<delta>\<tau> on K\<^sub>2 implies K\<^sub>3) # \<Phi>))\<close>
| timedelayed_e2:
  \<open>(\<Gamma>, n \<turnstile> ((K\<^sub>1 time-delayed by \<delta>\<tau> on K\<^sub>2 implies K\<^sub>3) # \<Psi>) \<triangleright> \<Phi>)
     \<hookrightarrow>\<^sub>e  (((K\<^sub>1 \<Up> n) # (K\<^sub>2 @ n \<oplus> \<delta>\<tau> \<Rightarrow> K\<^sub>3) # \<Gamma>), n
            \<turnstile> \<Psi> \<triangleright> ((K\<^sub>1 time-delayed by \<delta>\<tau> on K\<^sub>2 implies K\<^sub>3) # \<Phi>))\<close>
| weakly_precedes_e:
  \<open>(\<Gamma>, n \<turnstile> ((K\<^sub>1 weakly precedes K\<^sub>2) # \<Psi>) \<triangleright> \<Phi>)
     \<hookrightarrow>\<^sub>e  (((\<lceil>#\<^sup>\<le> K\<^sub>2 n, #\<^sup>\<le> K\<^sub>1 n\<rceil> \<in> (\<lambda>(x,y). x\<le>y)) # \<Gamma>), n
            \<turnstile> \<Psi> \<triangleright> ((K\<^sub>1 weakly precedes K\<^sub>2) # \<Phi>))\<close>
| strictly_precedes_e:
  \<open>(\<Gamma>, n \<turnstile> ((K\<^sub>1 strictly precedes K\<^sub>2) # \<Psi>) \<triangleright> \<Phi>)
     \<hookrightarrow>\<^sub>e  (((\<lceil>#\<^sup>\<le> K\<^sub>2 n, #\<^sup>< K\<^sub>1 n\<rceil> \<in> (\<lambda>(x,y). x\<le>y)) # \<Gamma>), n
            \<turnstile> \<Psi> \<triangleright> ((K\<^sub>1 strictly precedes K\<^sub>2) # \<Phi>))\<close>
| kills_e1:
  \<open>(\<Gamma>, n \<turnstile> ((K\<^sub>1 kills K\<^sub>2) # \<Psi>) \<triangleright> \<Phi>)
     \<hookrightarrow>\<^sub>e  (((K\<^sub>1 \<not>\<Up> n) # \<Gamma>), n \<turnstile> \<Psi> \<triangleright> ((K\<^sub>1 kills K\<^sub>2) # \<Phi>))\<close>
| kills_e2:
  \<open>(\<Gamma>, n \<turnstile> ((K\<^sub>1 kills K\<^sub>2) # \<Psi>) \<triangleright> \<Phi>)
     \<hookrightarrow>\<^sub>e  (((K\<^sub>1 \<Up> n) # (K\<^sub>2 \<not>\<Up> \<ge> n) # \<Gamma>), n \<turnstile> \<Psi> \<triangleright> ((K\<^sub>1 kills K\<^sub>2) # \<Phi>))\<close>

inductive operational_semantics_step
  ::\<open>('\<tau>::linordered_field) config \<Rightarrow> '\<tau> config \<Rightarrow> bool\<close>                ("_ \<hookrightarrow> _" 70)
where
  intro_part:
  \<open>(\<Gamma>\<^sub>1, n\<^sub>1 \<turnstile> \<Psi>\<^sub>1 \<triangleright> \<Phi>\<^sub>1)  \<hookrightarrow>\<^sub>i  (\<Gamma>\<^sub>2, n\<^sub>2 \<turnstile> \<Psi>\<^sub>2 \<triangleright> \<Phi>\<^sub>2)
    \<Longrightarrow> (\<Gamma>\<^sub>1, n\<^sub>1 \<turnstile> \<Psi>\<^sub>1 \<triangleright> \<Phi>\<^sub>1)  \<hookrightarrow>  (\<Gamma>\<^sub>2, n\<^sub>2 \<turnstile> \<Psi>\<^sub>2 \<triangleright> \<Phi>\<^sub>2)\<close>
| elims_part:
  \<open>(\<Gamma>\<^sub>1, n\<^sub>1 \<turnstile> \<Psi>\<^sub>1 \<triangleright> \<Phi>\<^sub>1)  \<hookrightarrow>\<^sub>e  (\<Gamma>\<^sub>2, n\<^sub>2 \<turnstile> \<Psi>\<^sub>2 \<triangleright> \<Phi>\<^sub>2)
    \<Longrightarrow> (\<Gamma>\<^sub>1, n\<^sub>1 \<turnstile> \<Psi>\<^sub>1 \<triangleright> \<Phi>\<^sub>1)  \<hookrightarrow>  (\<Gamma>\<^sub>2, n\<^sub>2 \<turnstile> \<Psi>\<^sub>2 \<triangleright> \<Phi>\<^sub>2)\<close>

abbreviation operational_semantics_step_rtranclp
  ::\<open>('\<tau>::linordered_field) config \<Rightarrow> '\<tau> config \<Rightarrow> bool\<close>                ("_ \<hookrightarrow>\<^sup>*\<^sup>* _" 70)
where
  \<open>\<C>\<^sub>1 \<hookrightarrow>\<^sup>*\<^sup>* \<C>\<^sub>2 \<equiv> operational_semantics_step\<^sup>*\<^sup>* \<C>\<^sub>1 \<C>\<^sub>2\<close>

abbreviation operational_semantics_step_tranclp
  ::\<open>('\<tau>::linordered_field) config \<Rightarrow> '\<tau> config \<Rightarrow> bool\<close>                ("_ \<hookrightarrow>\<^sup>+\<^sup>+ _" 70)
where
  \<open>\<C>\<^sub>1 \<hookrightarrow>\<^sup>+\<^sup>+ \<C>\<^sub>2 \<equiv> operational_semantics_step\<^sup>+\<^sup>+ \<C>\<^sub>1 \<C>\<^sub>2\<close>

abbreviation operational_semantics_step_reflclp
  ::\<open>('\<tau>::linordered_field) config \<Rightarrow> '\<tau> config \<Rightarrow> bool\<close>                ("_ \<hookrightarrow>\<^sup>=\<^sup>= _" 70)
where
  \<open>\<C>\<^sub>1 \<hookrightarrow>\<^sup>=\<^sup>= \<C>\<^sub>2 \<equiv> operational_semantics_step\<^sup>=\<^sup>= \<C>\<^sub>1 \<C>\<^sub>2\<close>

abbreviation operational_semantics_step_relpowp
  ::\<open>('\<tau>::linordered_field) config \<Rightarrow> nat \<Rightarrow> '\<tau> config \<Rightarrow> bool\<close>         ("_ \<hookrightarrow>\<^bsup>_\<^esup> _" 70)
where
  \<open>\<C>\<^sub>1 \<hookrightarrow>\<^bsup>n\<^esup> \<C>\<^sub>2 \<equiv> (operational_semantics_step ^^ n) \<C>\<^sub>1 \<C>\<^sub>2\<close>

definition operational_semantics_elim_inv
  ::\<open>('\<tau>::linordered_field) config \<Rightarrow> '\<tau> config \<Rightarrow> bool\<close>                ("_ \<hookrightarrow>\<^sub>e\<^sup>\<leftarrow> _" 70)
where
  \<open>\<C>\<^sub>1 \<hookrightarrow>\<^sub>e\<^sup>\<leftarrow> \<C>\<^sub>2 \<equiv> \<C>\<^sub>2 \<hookrightarrow>\<^sub>e \<C>\<^sub>1\<close>


section\<open>Basic Lemmas\<close>

lemma operational_semantics_trans_generalized:
  assumes \<open>\<C>\<^sub>1 \<hookrightarrow>\<^bsup>n\<^esup> \<C>\<^sub>2\<close>
  assumes \<open>\<C>\<^sub>2 \<hookrightarrow>\<^bsup>m\<^esup> \<C>\<^sub>3\<close>
    shows \<open>\<C>\<^sub>1 \<hookrightarrow>\<^bsup>n + m\<^esup> \<C>\<^sub>3\<close>
using relcompp.relcompI[of  \<open>operational_semantics_step ^^ n\<close> _ _ 
                            \<open>operational_semantics_step ^^ m\<close>, OF assms]
by (simp add: relpowp_add) 

abbreviation Cnext_solve
  ::\<open>('\<tau>::linordered_field) config \<Rightarrow> '\<tau> config set\<close> ("\<C>\<^sub>n\<^sub>e\<^sub>x\<^sub>t _")
where
  \<open>\<C>\<^sub>n\<^sub>e\<^sub>x\<^sub>t \<S> \<equiv> { \<S>'. \<S> \<hookrightarrow> \<S>' }\<close>

lemma Cnext_solve_instant:
  \<open>(\<C>\<^sub>n\<^sub>e\<^sub>x\<^sub>t (\<Gamma>, n \<turnstile> [] \<triangleright> \<Phi>)) \<supseteq> { \<Gamma>, Suc n \<turnstile> \<Phi> \<triangleright> [] }\<close>
by (simp add: operational_semantics_step.simps operational_semantics_intro.instant_i)

lemma Cnext_solve_sporadicon:
  \<open>(\<C>\<^sub>n\<^sub>e\<^sub>x\<^sub>t (\<Gamma>, n \<turnstile> ((K\<^sub>1 sporadic \<tau> on K\<^sub>2) # \<Psi>) \<triangleright> \<Phi>))
    \<supseteq> { \<Gamma>, n \<turnstile> \<Psi> \<triangleright> ((K\<^sub>1 sporadic \<tau> on K\<^sub>2) # \<Phi>), ((K\<^sub>1 \<Up> n) # (K\<^sub>2 \<Down> n @ \<tau>) # \<Gamma>), n \<turnstile> \<Psi> \<triangleright> \<Phi> }\<close>
by (simp add: operational_semantics_step.simps operational_semantics_elim.sporadic_on_e1
              operational_semantics_elim.sporadic_on_e2)

lemma Cnext_solve_tagrel:
  \<open>(\<C>\<^sub>n\<^sub>e\<^sub>x\<^sub>t (\<Gamma>, n \<turnstile> ((time-relation \<lfloor>K\<^sub>1, K\<^sub>2\<rfloor> \<in> R) # \<Psi>) \<triangleright> \<Phi>))
    \<supseteq> { ((\<lfloor>\<tau>\<^sub>v\<^sub>a\<^sub>r(K\<^sub>1, n), \<tau>\<^sub>v\<^sub>a\<^sub>r(K\<^sub>2, n)\<rfloor> \<in> R) # \<Gamma>), n \<turnstile> \<Psi> \<triangleright> ((time-relation \<lfloor>K\<^sub>1, K\<^sub>2\<rfloor> \<in> R) # \<Phi>) }\<close>
by (simp add: operational_semantics_step.simps operational_semantics_elim.tagrel_e)

lemma Cnext_solve_implies:
  \<open>(\<C>\<^sub>n\<^sub>e\<^sub>x\<^sub>t (\<Gamma>, n \<turnstile> ((K\<^sub>1 implies K\<^sub>2) # \<Psi>) \<triangleright> \<Phi>))
    \<supseteq> { ((K\<^sub>1 \<not>\<Up> n) # \<Gamma>), n \<turnstile> \<Psi> \<triangleright> ((K\<^sub>1 implies K\<^sub>2) # \<Phi>),
         ((K\<^sub>1 \<Up> n) # (K\<^sub>2 \<Up> n) # \<Gamma>), n \<turnstile> \<Psi> \<triangleright> ((K\<^sub>1 implies K\<^sub>2) # \<Phi>) }\<close>
by (simp add: operational_semantics_step.simps operational_semantics_elim.implies_e1
              operational_semantics_elim.implies_e2)

lemma Cnext_solve_implies_not:
  \<open>(\<C>\<^sub>n\<^sub>e\<^sub>x\<^sub>t (\<Gamma>, n \<turnstile> ((K\<^sub>1 implies not K\<^sub>2) # \<Psi>) \<triangleright> \<Phi>))
    \<supseteq> { ((K\<^sub>1 \<not>\<Up> n) # \<Gamma>), n \<turnstile> \<Psi> \<triangleright> ((K\<^sub>1 implies not K\<^sub>2) # \<Phi>),
        ((K\<^sub>1 \<Up> n) # (K\<^sub>2 \<not>\<Up> n) # \<Gamma>), n \<turnstile> \<Psi> \<triangleright> ((K\<^sub>1 implies not K\<^sub>2) # \<Phi>) }\<close>
by (simp add: operational_semantics_step.simps operational_semantics_elim.implies_not_e1
              operational_semantics_elim.implies_not_e2)

lemma Cnext_solve_timedelayed:
  \<open>(\<C>\<^sub>n\<^sub>e\<^sub>x\<^sub>t (\<Gamma>, n \<turnstile> ((K\<^sub>1 time-delayed by \<delta>\<tau> on K\<^sub>2 implies K\<^sub>3) # \<Psi>) \<triangleright> \<Phi>))
    \<supseteq> { ((K\<^sub>1 \<not>\<Up> n) # \<Gamma>), n \<turnstile> \<Psi> \<triangleright> ((K\<^sub>1 time-delayed by \<delta>\<tau> on K\<^sub>2 implies K\<^sub>3) # \<Phi>),
        ((K\<^sub>1 \<Up> n) # (K\<^sub>2 @ n \<oplus> \<delta>\<tau> \<Rightarrow> K\<^sub>3) # \<Gamma>), n
          \<turnstile> \<Psi> \<triangleright> ((K\<^sub>1 time-delayed by \<delta>\<tau> on K\<^sub>2 implies K\<^sub>3) # \<Phi>) }\<close>
by (simp add: operational_semantics_step.simps operational_semantics_elim.timedelayed_e1
              operational_semantics_elim.timedelayed_e2)

lemma Cnext_solve_weakly_precedes:
  \<open>(\<C>\<^sub>n\<^sub>e\<^sub>x\<^sub>t (\<Gamma>, n \<turnstile> ((K\<^sub>1 weakly precedes K\<^sub>2) # \<Psi>) \<triangleright> \<Phi>))
    \<supseteq> { ((\<lceil>#\<^sup>\<le> K\<^sub>2 n, #\<^sup>\<le> K\<^sub>1 n\<rceil> \<in> (\<lambda>(x,y). x\<le>y)) # \<Gamma>), n \<turnstile> \<Psi> \<triangleright> ((K\<^sub>1 weakly precedes K\<^sub>2) # \<Phi>) }\<close>
by (simp add: operational_semantics_step.simps operational_semantics_elim.weakly_precedes_e)

lemma Cnext_solve_strictly_precedes:
  \<open>(\<C>\<^sub>n\<^sub>e\<^sub>x\<^sub>t (\<Gamma>, n \<turnstile> ((K\<^sub>1 strictly precedes K\<^sub>2) # \<Psi>) \<triangleright> \<Phi>))
    \<supseteq> { ((\<lceil>#\<^sup>\<le> K\<^sub>2 n, #\<^sup>< K\<^sub>1 n\<rceil> \<in> (\<lambda>(x,y). x\<le>y)) # \<Gamma>), n \<turnstile> \<Psi> \<triangleright> ((K\<^sub>1 strictly precedes K\<^sub>2) # \<Phi>) }\<close>
by (simp add: operational_semantics_step.simps operational_semantics_elim.strictly_precedes_e)

lemma Cnext_solve_kills:
  \<open>(\<C>\<^sub>n\<^sub>e\<^sub>x\<^sub>t (\<Gamma>, n \<turnstile> ((K\<^sub>1 kills K\<^sub>2) # \<Psi>) \<triangleright> \<Phi>))
    \<supseteq> { ((K\<^sub>1 \<not>\<Up> n) # \<Gamma>), n \<turnstile> \<Psi> \<triangleright> ((K\<^sub>1 kills K\<^sub>2) # \<Phi>),
        ((K\<^sub>1 \<Up> n) # (K\<^sub>2 \<not>\<Up> \<ge> n) # \<Gamma>), n \<turnstile> \<Psi> \<triangleright> ((K\<^sub>1 kills K\<^sub>2) # \<Phi>) }\<close>
by (simp add: operational_semantics_step.simps operational_semantics_elim.kills_e1
              operational_semantics_elim.kills_e2)

lemma empty_spec_reductions:
  \<open>([], 0 \<turnstile> [] \<triangleright> []) \<hookrightarrow>\<^bsup>k\<^esup> ([], k \<turnstile> [] \<triangleright> [])\<close>
proof (induct k)
  case 0 thus ?case by simp
next
  case Suc thus ?case
    using instant_i operational_semantics_step.simps by fastforce 
qed

end
