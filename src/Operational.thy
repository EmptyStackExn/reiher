theory Operational
imports
    "TESL"
    "Run"

begin
text{* Operational steps *}

abbreviation uncurry_conf
  :: "('\<tau>::linordered_field) system \<Rightarrow> instant_index \<Rightarrow> '\<tau> TESL_formula \<Rightarrow> '\<tau> TESL_formula \<Rightarrow> '\<tau> config" ("_, _ \<turnstile> _ \<triangleright> _" 80) where
  "\<Gamma>, n \<turnstile> \<Psi> \<triangleright> \<Phi> \<equiv> (\<Gamma>, n, \<Psi>, \<Phi>)"

inductive operational_semantics_intro :: "('\<tau>::linordered_field) config \<Rightarrow> '\<tau> config \<Rightarrow> bool" ("_ \<hookrightarrow>\<^sub>i _" 70) where
  instant_i:
  "(\<Gamma>, n \<turnstile> [] \<triangleright> \<Phi>)
     \<hookrightarrow>\<^sub>i  (\<Gamma>, Suc n \<turnstile> \<Phi> \<triangleright> [])"

inductive operational_semantics_elim :: "('\<tau>::linordered_field) config \<Rightarrow> '\<tau> config \<Rightarrow> bool" ("_ \<hookrightarrow>\<^sub>e _" 70) where
  sporadic_on_e1:
  "(\<Gamma>, n \<turnstile> ((K\<^sub>1 sporadic \<tau> on K\<^sub>2) # \<Psi>) \<triangleright> \<Phi>)
     \<hookrightarrow>\<^sub>e  (\<Gamma>, n \<turnstile> \<Psi> \<triangleright> ((K\<^sub>1 sporadic \<tau> on K\<^sub>2) # \<Phi>))"
| sporadic_on_e2:
  "(\<Gamma>, n \<turnstile> ((K\<^sub>1 sporadic \<tau> on K\<^sub>2) # \<Psi>) \<triangleright> \<Phi>)
     \<hookrightarrow>\<^sub>e  (((K\<^sub>1 \<Up> n) # (K\<^sub>2 \<Down> n @ \<tau>) # \<Gamma>), n \<turnstile> \<Psi> \<triangleright> \<Phi>)"
| tagrel_e:
  "(\<Gamma>, n \<turnstile> ((time-relation \<lfloor>K\<^sub>1, K\<^sub>2\<rfloor> \<in> R) # \<Psi>) \<triangleright> \<Phi>)
     \<hookrightarrow>\<^sub>e  (((\<lfloor>\<tau>\<^sub>v\<^sub>a\<^sub>r(K\<^sub>1, n), \<tau>\<^sub>v\<^sub>a\<^sub>r(K\<^sub>2, n)\<rfloor> \<in> R) # \<Gamma>), n \<turnstile> \<Psi> \<triangleright> ((time-relation \<lfloor>K\<^sub>1, K\<^sub>2\<rfloor> \<in> R) # \<Phi>))"
| implies_e1:
  "(\<Gamma>, n \<turnstile> ((K\<^sub>1 implies K\<^sub>2) # \<Psi>) \<triangleright> \<Phi>)
     \<hookrightarrow>\<^sub>e  (((K\<^sub>1 \<not>\<Up> n) # \<Gamma>), n \<turnstile> \<Psi> \<triangleright> ((K\<^sub>1 implies K\<^sub>2) # \<Phi>))"
| implies_e2:
  "(\<Gamma>, n \<turnstile> ((K\<^sub>1 implies K\<^sub>2) # \<Psi>) \<triangleright> \<Phi>)
     \<hookrightarrow>\<^sub>e  (((K\<^sub>1 \<Up> n) # (K\<^sub>2 \<Up> n) # \<Gamma>), n \<turnstile> \<Psi> \<triangleright> ((K\<^sub>1 implies K\<^sub>2) # \<Phi>))"
| implies_not_e1:
  "(\<Gamma>, n \<turnstile> ((K\<^sub>1 implies not K\<^sub>2) # \<Psi>) \<triangleright> \<Phi>)
     \<hookrightarrow>\<^sub>e  (((K\<^sub>1 \<not>\<Up> n) # \<Gamma>), n \<turnstile> \<Psi> \<triangleright> ((K\<^sub>1 implies not K\<^sub>2) # \<Phi>))"
| implies_not_e2:
  "(\<Gamma>, n \<turnstile> ((K\<^sub>1 implies not K\<^sub>2) # \<Psi>) \<triangleright> \<Phi>)
     \<hookrightarrow>\<^sub>e  (((K\<^sub>1 \<Up> n) # (K\<^sub>2 \<not>\<Up> n) # \<Gamma>), n \<turnstile> \<Psi> \<triangleright> ((K\<^sub>1 implies not K\<^sub>2) # \<Phi>))"
| timedelayed_e1:
  "(\<Gamma>, n \<turnstile> ((K\<^sub>1 time-delayed by \<delta>\<tau> on K\<^sub>2 implies K\<^sub>3) # \<Psi>) \<triangleright> \<Phi>)
     \<hookrightarrow>\<^sub>e  (((K\<^sub>1 \<not>\<Up> n) # \<Gamma>), n \<turnstile> \<Psi> \<triangleright> ((K\<^sub>1 time-delayed by \<delta>\<tau> on K\<^sub>2 implies K\<^sub>3) # \<Phi>))"
| timedelayed_e2:
  "(\<Gamma>, n \<turnstile> ((K\<^sub>1 time-delayed by \<delta>\<tau> on K\<^sub>2 implies K\<^sub>3) # \<Psi>) \<triangleright> \<Phi>)
     \<hookrightarrow>\<^sub>e  (((K\<^sub>1 \<Up> n) # \<Gamma>), n \<turnstile> ((K\<^sub>3 sporadic \<lparr>\<tau>\<^sub>v\<^sub>a\<^sub>r(K\<^sub>2, n) \<oplus> \<delta>\<tau>\<rparr> on K\<^sub>2) # \<Psi>) \<triangleright> ((K\<^sub>1 time-delayed by \<delta>\<tau> on K\<^sub>2 implies K\<^sub>3) # \<Phi>))"
| weakly_precedes_e:
  "(\<Gamma>, n \<turnstile> ((K\<^sub>1 weakly precedes K\<^sub>2) # \<Psi>) \<triangleright> \<Phi>)
     \<hookrightarrow>\<^sub>e  (((\<lceil>#\<^sup>\<le> K\<^sub>2 n, #\<^sup>\<le> K\<^sub>1 n\<rceil> \<in> (\<lambda>(x,y). x\<le>y)) # \<Gamma>), n \<turnstile> \<Psi> \<triangleright> ((K\<^sub>1 weakly precedes K\<^sub>2) # \<Phi>))"
| strictly_precedes_e:
  "(\<Gamma>, n \<turnstile> ((K\<^sub>1 strictly precedes K\<^sub>2) # \<Psi>) \<triangleright> \<Phi>)
     \<hookrightarrow>\<^sub>e  (((\<lceil>#\<^sup>\<le> K\<^sub>2 n, #\<^sup>< K\<^sub>1 n\<rceil> \<in> (\<lambda>(x,y). x\<le>y)) # \<Gamma>), n \<turnstile> \<Psi> \<triangleright> ((K\<^sub>1 strictly precedes K\<^sub>2) # \<Phi>))"
| kills_e1:
  "(\<Gamma>, n \<turnstile> ((K\<^sub>1 kills K\<^sub>2) # \<Psi>) \<triangleright> \<Phi>)
     \<hookrightarrow>\<^sub>e  (((K\<^sub>1 \<not>\<Up> n) # \<Gamma>), n \<turnstile> \<Psi> \<triangleright> ((K\<^sub>1 kills K\<^sub>2) # \<Phi>))"
| kills_e2:
  "(\<Gamma>, n \<turnstile> ((K\<^sub>1 kills K\<^sub>2) # \<Psi>) \<triangleright> \<Phi>)
     \<hookrightarrow>\<^sub>e  (((K\<^sub>1 \<Up> n) # (K\<^sub>2 \<not>\<Up> \<ge> n) # \<Gamma>), n \<turnstile> \<Psi> \<triangleright> ((K\<^sub>1 kills K\<^sub>2) # \<Phi>))"

inductive operational_semantics_step :: "('\<tau>::linordered_field) config \<Rightarrow> '\<tau> config \<Rightarrow> bool" ("_ \<hookrightarrow> _" 70) where
    intro_part: "(\<Gamma>\<^sub>1, n\<^sub>1 \<turnstile> \<Psi>\<^sub>1 \<triangleright> \<Phi>\<^sub>1)  \<hookrightarrow>\<^sub>i  (\<Gamma>\<^sub>2, n\<^sub>2 \<turnstile> \<Psi>\<^sub>2 \<triangleright> \<Phi>\<^sub>2)
   \<Longrightarrow> (\<Gamma>\<^sub>1, n\<^sub>1 \<turnstile> \<Psi>\<^sub>1 \<triangleright> \<Phi>\<^sub>1)  \<hookrightarrow>  (\<Gamma>\<^sub>2, n\<^sub>2 \<turnstile> \<Psi>\<^sub>2 \<triangleright> \<Phi>\<^sub>2)"
  | elims_part: "(\<Gamma>\<^sub>1, n\<^sub>1 \<turnstile> \<Psi>\<^sub>1 \<triangleright> \<Phi>\<^sub>1)  \<hookrightarrow>\<^sub>e  (\<Gamma>\<^sub>2, n\<^sub>2 \<turnstile> \<Psi>\<^sub>2 \<triangleright> \<Phi>\<^sub>2)
   \<Longrightarrow> (\<Gamma>\<^sub>1, n\<^sub>1 \<turnstile> \<Psi>\<^sub>1 \<triangleright> \<Phi>\<^sub>1)  \<hookrightarrow>  (\<Gamma>\<^sub>2, n\<^sub>2 \<turnstile> \<Psi>\<^sub>2 \<triangleright> \<Phi>\<^sub>2)"

abbreviation operational_semantics_step_rtranclp :: "('\<tau>::linordered_field) config \<Rightarrow> '\<tau> config \<Rightarrow> bool" ("_ \<hookrightarrow>\<^sup>*\<^sup>* _" 70) where
  "\<C>\<^sub>1 \<hookrightarrow>\<^sup>*\<^sup>* \<C>\<^sub>2 \<equiv> operational_semantics_step\<^sup>*\<^sup>* \<C>\<^sub>1 \<C>\<^sub>2"

abbreviation operational_semantics_step_tranclp :: "('\<tau>::linordered_field) config \<Rightarrow> '\<tau> config \<Rightarrow> bool" ("_ \<hookrightarrow>\<^sup>+\<^sup>+ _" 70) where
  "\<C>\<^sub>1 \<hookrightarrow>\<^sup>+\<^sup>+ \<C>\<^sub>2 \<equiv> operational_semantics_step\<^sup>+\<^sup>+ \<C>\<^sub>1 \<C>\<^sub>2"

abbreviation operational_semantics_step_reflclp :: "('\<tau>::linordered_field) config \<Rightarrow> '\<tau> config \<Rightarrow> bool" ("_ \<hookrightarrow>\<^sup>=\<^sup>= _" 70) where
  "\<C>\<^sub>1 \<hookrightarrow>\<^sup>=\<^sup>= \<C>\<^sub>2 \<equiv> operational_semantics_step\<^sup>=\<^sup>= \<C>\<^sub>1 \<C>\<^sub>2"

abbreviation operational_semantics_step_relpowp :: "('\<tau>::linordered_field) config \<Rightarrow> nat \<Rightarrow> '\<tau> config \<Rightarrow> bool" ("_ \<hookrightarrow>\<^bsup>_\<^esup> _" 70) where
  "\<C>\<^sub>1 \<hookrightarrow>\<^bsup>n\<^esup> \<C>\<^sub>2 \<equiv> (operational_semantics_step ^^ n) \<C>\<^sub>1 \<C>\<^sub>2"

definition operational_semantics_elim_inv :: "('\<tau>::linordered_field) config \<Rightarrow> '\<tau> config \<Rightarrow> bool" ("_ \<hookrightarrow>\<^sub>e\<^sup>\<leftarrow> _" 70) where
  "\<C>\<^sub>1 \<hookrightarrow>\<^sub>e\<^sup>\<leftarrow> \<C>\<^sub>2 \<equiv> \<C>\<^sub>2 \<hookrightarrow>\<^sub>e \<C>\<^sub>1"

lemma operational_semantics_trans_generalized:
  assumes "\<C>\<^sub>1 \<hookrightarrow>\<^bsup>n\<^esup> \<C>\<^sub>2"
  assumes "\<C>\<^sub>2 \<hookrightarrow>\<^bsup>m\<^esup> \<C>\<^sub>3"
  shows "\<C>\<^sub>1 \<hookrightarrow>\<^bsup>n + m\<^esup> \<C>\<^sub>3"
  by (metis (no_types, hide_lams) assms(1) assms(2) relcompp.relcompI relpowp_add)

abbreviation Cnext_solve :: "('\<tau>::linordered_field) config \<Rightarrow> '\<tau> config set" ("\<C>\<^sub>n\<^sub>e\<^sub>x\<^sub>t _") where
  "\<C>\<^sub>n\<^sub>e\<^sub>x\<^sub>t \<S> \<equiv> { \<S>'. \<S> \<hookrightarrow> \<S>' }"

lemma Cnext_solve_instant:
  shows "(\<C>\<^sub>n\<^sub>e\<^sub>x\<^sub>t (\<Gamma>, n \<turnstile> [] \<triangleright> \<Phi>))
          \<supseteq> { \<Gamma>, Suc n \<turnstile> \<Phi> \<triangleright> [] }"
  by (simp add: operational_semantics_step.simps operational_semantics_intro.instant_i)

lemma Cnext_solve_sporadicon:
  shows "(\<C>\<^sub>n\<^sub>e\<^sub>x\<^sub>t (\<Gamma>, n \<turnstile> ((K\<^sub>1 sporadic \<tau> on K\<^sub>2) # \<Psi>) \<triangleright> \<Phi>))
          \<supseteq> { \<Gamma>, n \<turnstile> \<Psi> \<triangleright> ((K\<^sub>1 sporadic \<tau> on K\<^sub>2) # \<Phi>),
              ((K\<^sub>1 \<Up> n) # (K\<^sub>2 \<Down> n @ \<tau>) # \<Gamma>), n \<turnstile> \<Psi> \<triangleright> \<Phi> }"
  by (simp add: operational_semantics_step.simps operational_semantics_elim.sporadic_on_e1 operational_semantics_elim.sporadic_on_e2)

lemma Cnext_solve_tagrel:
  shows "(\<C>\<^sub>n\<^sub>e\<^sub>x\<^sub>t (\<Gamma>, n \<turnstile> ((time-relation \<lfloor>K\<^sub>1, K\<^sub>2\<rfloor> \<in> R) # \<Psi>) \<triangleright> \<Phi>))
          \<supseteq> { ((\<lfloor>\<tau>\<^sub>v\<^sub>a\<^sub>r(K\<^sub>1, n), \<tau>\<^sub>v\<^sub>a\<^sub>r(K\<^sub>2, n)\<rfloor> \<in> R) # \<Gamma>), n \<turnstile> \<Psi> \<triangleright> ((time-relation \<lfloor>K\<^sub>1, K\<^sub>2\<rfloor> \<in> R) # \<Phi>) }"
  by (simp add: operational_semantics_step.simps operational_semantics_elim.tagrel_e)

lemma Cnext_solve_implies:
  shows "(\<C>\<^sub>n\<^sub>e\<^sub>x\<^sub>t (\<Gamma>, n \<turnstile> ((K\<^sub>1 implies K\<^sub>2) # \<Psi>) \<triangleright> \<Phi>))
          \<supseteq> { ((K\<^sub>1 \<not>\<Up> n) # \<Gamma>), n \<turnstile> \<Psi> \<triangleright> ((K\<^sub>1 implies K\<^sub>2) # \<Phi>),
              ((K\<^sub>1 \<Up> n) # (K\<^sub>2 \<Up> n) # \<Gamma>), n \<turnstile> \<Psi> \<triangleright> ((K\<^sub>1 implies K\<^sub>2) # \<Phi>)}"
  by (simp add: operational_semantics_step.simps operational_semantics_elim.implies_e1 operational_semantics_elim.implies_e2)

lemma Cnext_solve_implies_not:
  shows "(\<C>\<^sub>n\<^sub>e\<^sub>x\<^sub>t (\<Gamma>, n \<turnstile> ((K\<^sub>1 implies not K\<^sub>2) # \<Psi>) \<triangleright> \<Phi>))
          \<supseteq> { ((K\<^sub>1 \<not>\<Up> n) # \<Gamma>), n \<turnstile> \<Psi> \<triangleright> ((K\<^sub>1 implies not K\<^sub>2) # \<Phi>),
              ((K\<^sub>1 \<Up> n) # (K\<^sub>2 \<not>\<Up> n) # \<Gamma>), n \<turnstile> \<Psi> \<triangleright> ((K\<^sub>1 implies not K\<^sub>2) # \<Phi>)}"
  by (simp add: operational_semantics_step.simps operational_semantics_elim.implies_not_e1 operational_semantics_elim.implies_not_e2)

lemma Cnext_solve_timedelayed:
  shows "(\<C>\<^sub>n\<^sub>e\<^sub>x\<^sub>t (\<Gamma>, n \<turnstile> ((K\<^sub>1 time-delayed by \<delta>\<tau> on K\<^sub>2 implies K\<^sub>3) # \<Psi>) \<triangleright> \<Phi>))
          \<supseteq> { ((K\<^sub>1 \<not>\<Up> n) # \<Gamma>), n \<turnstile> \<Psi> \<triangleright> ((K\<^sub>1 time-delayed by \<delta>\<tau> on K\<^sub>2 implies K\<^sub>3) # \<Phi>),
              ((K\<^sub>1 \<Up> n) # \<Gamma>), n \<turnstile> ((K\<^sub>3 sporadic \<lparr>\<tau>\<^sub>v\<^sub>a\<^sub>r(K\<^sub>2, n) \<oplus> \<delta>\<tau>\<rparr> on K\<^sub>2) # \<Psi>) \<triangleright> ((K\<^sub>1 time-delayed by \<delta>\<tau> on K\<^sub>2 implies K\<^sub>3) # \<Phi>) }"
  by (simp add: operational_semantics_step.simps operational_semantics_elim.timedelayed_e1 operational_semantics_elim.timedelayed_e2)

lemma Cnext_solve_weakly_precedes:
  shows "(\<C>\<^sub>n\<^sub>e\<^sub>x\<^sub>t (\<Gamma>, n \<turnstile> ((K\<^sub>1 weakly precedes K\<^sub>2) # \<Psi>) \<triangleright> \<Phi>))
          \<supseteq> { ((\<lceil>#\<^sup>\<le> K\<^sub>2 n, #\<^sup>\<le> K\<^sub>1 n\<rceil> \<in> (\<lambda>(x,y). x\<le>y)) # \<Gamma>), n \<turnstile> \<Psi> \<triangleright> ((K\<^sub>1 weakly precedes K\<^sub>2) # \<Phi>) }"
  by (simp add: operational_semantics_step.simps operational_semantics_elim.weakly_precedes_e)

lemma Cnext_solve_strictly_precedes:
  shows "(\<C>\<^sub>n\<^sub>e\<^sub>x\<^sub>t (\<Gamma>, n \<turnstile> ((K\<^sub>1 strictly precedes K\<^sub>2) # \<Psi>) \<triangleright> \<Phi>))
          \<supseteq> { ((\<lceil>#\<^sup>\<le> K\<^sub>2 n, #\<^sup>< K\<^sub>1 n\<rceil> \<in> (\<lambda>(x,y). x\<le>y)) # \<Gamma>), n \<turnstile> \<Psi> \<triangleright> ((K\<^sub>1 strictly precedes K\<^sub>2) # \<Phi>) }"
  by (simp add: operational_semantics_step.simps operational_semantics_elim.strictly_precedes_e)

lemma Cnext_solve_kills:
  shows "(\<C>\<^sub>n\<^sub>e\<^sub>x\<^sub>t (\<Gamma>, n \<turnstile> ((K\<^sub>1 kills K\<^sub>2) # \<Psi>) \<triangleright> \<Phi>))
          \<supseteq> { ((K\<^sub>1 \<not>\<Up> n) # \<Gamma>), n \<turnstile> \<Psi> \<triangleright> ((K\<^sub>1 kills K\<^sub>2) # \<Phi>),
              ((K\<^sub>1 \<Up> n) # (K\<^sub>2 \<not>\<Up> \<ge> n) # \<Gamma>), n \<turnstile> \<Psi> \<triangleright> ((K\<^sub>1 kills K\<^sub>2) # \<Phi>)}"
  by (simp add: operational_semantics_step.simps operational_semantics_elim.kills_e1 operational_semantics_elim.kills_e2)

lemma empty_spec_reductions:
  shows "([], 0 \<turnstile> [] \<triangleright> []) \<hookrightarrow>\<^bsup>k\<^esup> ([], k \<turnstile> [] \<triangleright> [])"
  proof (induct k)
    case 0
    then show ?case by simp
  next
    case (Suc k)
    then show ?case
      using instant_i operational_semantics_step.simps by fastforce 
  qed

(* To decide finite-satisfiability of TESL specifications *)
inductive finite_SAT :: "('\<tau>::linordered_field) config \<Rightarrow> bool" ("\<TTurnstile> _" 50) where
  finite_SAT_ax: "set (NoSporadic \<Phi>) = set \<Phi> \<Longrightarrow>
                    consistent_run \<Gamma> \<Longrightarrow>
                   \<TTurnstile> (\<Gamma>, n \<turnstile> \<Psi> \<triangleright> \<Phi>)"
| finite_SAT_i: "(\<Gamma>\<^sub>1, n\<^sub>1 \<turnstile> \<Psi>\<^sub>1 \<triangleright> \<Phi>\<^sub>1) \<hookrightarrow> (\<Gamma>\<^sub>2, n\<^sub>2 \<turnstile> \<Psi>\<^sub>2 \<triangleright> \<Phi>\<^sub>2) \<Longrightarrow>
                   \<TTurnstile> (\<Gamma>\<^sub>2, n\<^sub>2 \<turnstile> \<Psi>\<^sub>2 \<triangleright> \<Phi>\<^sub>2) \<Longrightarrow>
                   \<TTurnstile> (\<Gamma>\<^sub>1, n\<^sub>1 \<turnstile> \<Psi>\<^sub>1 \<triangleright> \<Phi>\<^sub>1)"

end
