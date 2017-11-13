theory Operational
imports
    "TESL"
    "Run"

begin
text{* Operational steps *}

abbreviation uncurry_conf
  :: "system \<Rightarrow> instant_index \<Rightarrow> TESL_formula \<Rightarrow> TESL_formula \<Rightarrow> config" ("_, _ \<turnstile> _ \<triangleright> _" 80) where
  "\<Gamma>, n \<turnstile> \<Psi> \<triangleright> \<Phi> \<equiv> (\<Gamma>, n, \<Psi>, \<Phi>)"

inductive operational_semantics_intro :: "config \<Rightarrow> config \<Rightarrow> bool" ("_ \<hookrightarrow>\<^sub>i _" 70) where
  instant_i:
  "(* consistent_run \<Gamma> \<Longrightarrow> *)
   \<Gamma>, n \<turnstile> [] \<triangleright> \<Phi>
     \<hookrightarrow>\<^sub>i  \<Gamma>, Suc n \<turnstile> \<Phi> \<triangleright> []"

inductive operational_semantics_elim :: "config \<Rightarrow> config \<Rightarrow> bool" ("_ \<hookrightarrow>\<^sub>e _" 70) where
  not_e:
  "\<Gamma>, n \<turnstile> (not K) # \<Psi> \<triangleright> \<Phi>
     \<hookrightarrow>\<^sub>e  K \<not>\<Up> n # \<Gamma>, n \<turnstile> \<Psi> \<triangleright> (not K) # \<Phi>"
| sporadic_e1:
  "(* consistent_run \<Gamma> \<Longrightarrow> *)
   \<Gamma>, n \<turnstile> (K sporadic \<tau>) # \<Psi> \<triangleright> \<Phi>
     \<hookrightarrow>\<^sub>e  \<Gamma>, n \<turnstile> \<Psi> \<triangleright> (K sporadic \<tau>) # \<Phi>"
| sporadic_e2:
  "(* consistent_run ((K \<Up> n) # (K \<Down> n @ \<lfloor>\<tau>\<rfloor>) # \<Gamma>) \<Longrightarrow> *)
   \<Gamma>, n \<turnstile> (K sporadic \<tau>) # \<Psi> \<triangleright> \<Phi>
     \<hookrightarrow>\<^sub>e  K \<Up> n # K \<Down> n @ \<lfloor>\<tau>\<rfloor> # \<Gamma>, n \<turnstile> \<Psi> \<triangleright> \<Phi>"
| sporadic_anytime_e1:
  "\<Gamma>, n \<turnstile> (K sporadic anytime) # \<Psi> \<triangleright> \<Phi>
     \<hookrightarrow>\<^sub>e  \<Gamma>, n \<turnstile> \<Psi> \<triangleright> (K sporadic anytime) # \<Phi>"
| sporadic_anytime_e2:
  "\<Gamma>, n \<turnstile> (K sporadic anytime) # \<Psi> \<triangleright> \<Phi>
     \<hookrightarrow>\<^sub>e  K \<Up> n # \<Gamma>, n \<turnstile> \<Psi> \<triangleright> \<Phi>"
| sporadic_on_e1:
  "(* consistent_run \<Gamma> \<Longrightarrow> *)
   \<Gamma>, n \<turnstile> (K\<^sub>1 sporadic \<tau> on K\<^sub>2) # \<Psi> \<triangleright> \<Phi>
     \<hookrightarrow>\<^sub>e  \<Gamma>, n \<turnstile> \<Psi> \<triangleright> (K\<^sub>1 sporadic \<tau> on K\<^sub>2) # \<Phi>"
| sporadic_on_e2:
  "(* consistent_run ((K\<^sub>1 \<Up> n) # (K\<^sub>2 \<Down> n @ \<tau>) # \<Gamma>) \<Longrightarrow> *)
   \<Gamma>, n \<turnstile> (K\<^sub>1 sporadic \<tau> on K\<^sub>2) # \<Psi> \<triangleright> \<Phi>
     \<hookrightarrow>\<^sub>e  K\<^sub>1 \<Up> n # K\<^sub>2 \<Down> n @ \<tau> # \<Gamma>, n \<turnstile> \<Psi> \<triangleright> \<Phi>"
| tagrel_e:
  "(* consistent_run ((\<tau>\<^sub>v\<^sub>a\<^sub>r(K\<^sub>1, n) \<doteq> \<alpha> * \<tau>\<^sub>v\<^sub>a\<^sub>r(K\<^sub>2, n) + \<beta>) # \<Gamma>) \<Longrightarrow> *)
   \<Gamma>, n \<turnstile> (tag-relation K\<^sub>1 = \<alpha> * K\<^sub>2 + \<beta>) # \<Psi> \<triangleright> \<Phi>
     \<hookrightarrow>\<^sub>e  (\<tau>\<^sub>v\<^sub>a\<^sub>r(K\<^sub>1, n) \<doteq> \<alpha> * \<tau>\<^sub>v\<^sub>a\<^sub>r(K\<^sub>2, n) + \<beta>) # \<Gamma>, n \<turnstile> \<Psi> \<triangleright> (tag-relation K\<^sub>1 = \<alpha> * K\<^sub>2 + \<beta>) # \<Phi>"
| tagrelgen_e:
  "\<Gamma>, n \<turnstile> (tag-relation \<langle>K\<^sub>1, K\<^sub>2\<rangle> \<in> R) # \<Psi> \<triangleright> \<Phi>
     \<hookrightarrow>\<^sub>e  (\<langle>\<tau>\<^sub>v\<^sub>a\<^sub>r(K\<^sub>1, n), \<tau>\<^sub>v\<^sub>a\<^sub>r(K\<^sub>2, n)\<rangle> \<epsilon> R) # \<Gamma>, n \<turnstile> \<Psi> \<triangleright> (tag-relation \<langle>K\<^sub>1, K\<^sub>2\<rangle> \<in> R) # \<Phi>"
| implies_e1:
  "(* consistent_run (K\<^sub>1 \<not>\<Up> n # \<Gamma>) \<Longrightarrow> *)
   \<Gamma>, n \<turnstile> (K\<^sub>1 implies K\<^sub>2) # \<Psi> \<triangleright> \<Phi>
     \<hookrightarrow>\<^sub>e  K\<^sub>1 \<not>\<Up> n # \<Gamma>, n \<turnstile> \<Psi> \<triangleright> (K\<^sub>1 implies K\<^sub>2) # \<Phi>"
| implies_e2:
  "(* consistent_run ((K\<^sub>1 \<Up> n) # (K\<^sub>2 \<Up> n) # \<Gamma>) \<Longrightarrow> *)
   \<Gamma>, n \<turnstile> (K\<^sub>1 implies K\<^sub>2) # \<Psi> \<triangleright> \<Phi>
     \<hookrightarrow>\<^sub>e  K\<^sub>1 \<Up> n # K\<^sub>2 \<Up> n # \<Gamma>, n \<turnstile> \<Psi> \<triangleright> (K\<^sub>1 implies K\<^sub>2) # \<Phi>"
| implies_not_e1:
  "(* consistent_run (K\<^sub>1 \<not>\<Up> n # \<Gamma>) \<Longrightarrow> *)
   \<Gamma>, n \<turnstile> (K\<^sub>1 implies not K\<^sub>2) # \<Psi> \<triangleright> \<Phi>
     \<hookrightarrow>\<^sub>e  K\<^sub>1 \<not>\<Up> n # \<Gamma>, n \<turnstile> \<Psi> \<triangleright> (K\<^sub>1 implies not K\<^sub>2) # \<Phi>"
| implies_not_e2:
  "(* consistent_run ((K\<^sub>1 \<Up> n) # (K\<^sub>2 \<Up> n) # \<Gamma>) \<Longrightarrow> *)
   \<Gamma>, n \<turnstile> (K\<^sub>1 implies not K\<^sub>2) # \<Psi> \<triangleright> \<Phi>
     \<hookrightarrow>\<^sub>e  K\<^sub>1 \<Up> n # K\<^sub>2 \<not>\<Up> n # \<Gamma>, n \<turnstile> \<Psi> \<triangleright> (K\<^sub>1 implies not K\<^sub>2) # \<Phi>"
| iff_e1:
  "\<Gamma>, n \<turnstile> (K\<^sub>1 iff K\<^sub>2) # \<Psi> \<triangleright> \<Phi>
     \<hookrightarrow>\<^sub>e  K\<^sub>1 \<not>\<Up> n # K\<^sub>2 \<not>\<Up> n # \<Gamma>, n \<turnstile> \<Psi> \<triangleright> (K\<^sub>1 iff K\<^sub>2) # \<Phi>"
| iff_e2:
  "\<Gamma>, n \<turnstile> (K\<^sub>1 iff K\<^sub>2) # \<Psi> \<triangleright> \<Phi>
     \<hookrightarrow>\<^sub>e  K\<^sub>1 \<Up> n # K\<^sub>2 \<Up> n # \<Gamma>, n \<turnstile> \<Psi> \<triangleright> (K\<^sub>1 iff K\<^sub>2) # \<Phi>"
| implies_anytime_e1:
  "(* consistent_run (K\<^sub>1 \<not>\<Up> n # \<Gamma>) \<Longrightarrow> *)
   \<Gamma>, n \<turnstile> (master anytime implies slave) # \<Psi> \<triangleright> \<Phi>
     \<hookrightarrow>\<^sub>e  master \<not>\<Up> n # \<Gamma>, n \<turnstile> \<Psi> \<triangleright> (master anytime implies slave) # \<Phi>"
| implies_anytime_e2:
  "(* consistent_run (K\<^sub>1 \<Up> n # \<Gamma>) \<Longrightarrow> *)
   \<Gamma>, n \<turnstile> (master anytime implies slave) # \<Psi> \<triangleright> \<Phi>
     \<hookrightarrow>\<^sub>e  master \<Up> n # \<Gamma>, n \<turnstile> (slave sporadic anytime) # \<Psi> \<triangleright> (master anytime implies slave) # \<Phi>"
| timedelayed_e1:
  "(* consistent_run (K\<^sub>1 \<not>\<Up> n # \<Gamma>) \<Longrightarrow> *)
   \<Gamma>, n \<turnstile> (K\<^sub>1 time-delayed by \<delta>\<tau> on K\<^sub>2 implies K\<^sub>3) # \<Psi> \<triangleright> \<Phi>
     \<hookrightarrow>\<^sub>e  K\<^sub>1 \<not>\<Up> n # \<Gamma>, n \<turnstile> \<Psi> \<triangleright> (K\<^sub>1 time-delayed by \<delta>\<tau> on K\<^sub>2 implies K\<^sub>3) # \<Phi>"
| timedelayed_e2:
  "(* consistent_run (K\<^sub>1 \<Up> n # \<Gamma>) \<Longrightarrow> *)
   \<Gamma>, n \<turnstile> (K\<^sub>1 time-delayed by \<delta>\<tau> on K\<^sub>2 implies K\<^sub>3) # \<Psi> \<triangleright> \<Phi>
     \<hookrightarrow>\<^sub>e  K\<^sub>1 \<Up> n # \<Gamma>, n \<turnstile> (K\<^sub>3 sporadic \<lfloor>\<tau>\<^sub>v\<^sub>a\<^sub>r(K\<^sub>2, n) \<oplus> \<delta>\<tau>\<rfloor> on K\<^sub>2) # \<Psi> \<triangleright> (K\<^sub>1 time-delayed by \<delta>\<tau> on K\<^sub>2 implies K\<^sub>3) # \<Phi>"
| sustained_from_e1:
  "\<Gamma>, n \<turnstile> (master sustained from begin to end implies slave) # \<Psi> \<triangleright> \<Phi>
     \<hookrightarrow>\<^sub>e  master \<not>\<Up> n # \<Gamma>, n \<turnstile> \<Psi> \<triangleright> (master sustained from begin to end implies slave) # \<Phi>"
| sustained_from_e2:
  "\<Gamma>, n \<turnstile> (master sustained from begin to end implies slave) # \<Psi> \<triangleright> \<Phi>
     \<hookrightarrow>\<^sub>e  master \<Up> n # \<Gamma>,  n \<turnstile> \<Psi> \<triangleright> (master sustained until begin reset on end implies slave) # \<Phi>"
| sustained_until_e1a:
  "\<Gamma>, n \<turnstile> (master sustained until end reset on begin implies slave) # \<Psi> \<triangleright> \<Phi>
     \<hookrightarrow>\<^sub>e  (end \<not>\<Up> n) # (master \<not>\<Up> n) # \<Gamma>,              n \<turnstile> \<Psi> \<triangleright> (master sustained until begin reset on end implies slave) # \<Phi>"
| sustained_until_e1b:
  "\<Gamma>, n \<turnstile> (master sustained until end reset on begin implies slave) # \<Psi> \<triangleright> \<Phi>
     \<hookrightarrow>\<^sub>e  (end \<not>\<Up> n) # (master \<Up> n) # (slave \<Up> n) # \<Gamma>, n \<turnstile> \<Psi> \<triangleright> (master sustained until begin reset on end implies slave) # \<Phi>"
| sustained_until_e2a:
  "\<Gamma>, n \<turnstile> (master sustained until end reset on begin implies slave) # \<Psi> \<triangleright> \<Phi>
     \<hookrightarrow>\<^sub>e  (end \<Up> n) # (master \<not>\<Up> n) # \<Gamma>,              n \<turnstile> \<Psi> \<triangleright> (master sustained from begin to end implies slave) # \<Phi>"
| sustained_until_e2b:
  "\<Gamma>, n \<turnstile> (master sustained until end reset on begin implies slave) # \<Psi> \<triangleright> \<Phi>
     \<hookrightarrow>\<^sub>e  (end \<Up> n) # (master \<Up> n) # (slave \<Up> n) # \<Gamma>, n \<turnstile> \<Psi> \<triangleright> (master sustained from begin to end implies slave) # \<Phi>"

inductive operational_semantics_step :: "config \<Rightarrow> config \<Rightarrow> bool" ("_ \<hookrightarrow> _" 70) where
    intro_part: "\<Gamma>\<^sub>1, n\<^sub>1 \<turnstile> \<Psi>\<^sub>1 \<triangleright> \<Phi>\<^sub>1  \<hookrightarrow>\<^sub>i  \<Gamma>\<^sub>2, n\<^sub>2 \<turnstile> \<Psi>\<^sub>2 \<triangleright> \<Phi>\<^sub>2
   \<Longrightarrow> \<Gamma>\<^sub>1, n\<^sub>1 \<turnstile> \<Psi>\<^sub>1 \<triangleright> \<Phi>\<^sub>1  \<hookrightarrow>  \<Gamma>\<^sub>2, n\<^sub>2 \<turnstile> \<Psi>\<^sub>2 \<triangleright> \<Phi>\<^sub>2"
  | elims_part: "\<Gamma>\<^sub>1, n\<^sub>1 \<turnstile> \<Psi>\<^sub>1 \<triangleright> \<Phi>\<^sub>1  \<hookrightarrow>\<^sub>e  \<Gamma>\<^sub>2, n\<^sub>2 \<turnstile> \<Psi>\<^sub>2 \<triangleright> \<Phi>\<^sub>2
   \<Longrightarrow> \<Gamma>\<^sub>1, n\<^sub>1 \<turnstile> \<Psi>\<^sub>1 \<triangleright> \<Phi>\<^sub>1  \<hookrightarrow>  \<Gamma>\<^sub>2, n\<^sub>2 \<turnstile> \<Psi>\<^sub>2 \<triangleright> \<Phi>\<^sub>2"

abbreviation operational_semantics_step_rtranclp :: "config \<Rightarrow> config \<Rightarrow> bool" ("_ \<hookrightarrow>\<^sup>*\<^sup>* _" 70) where
  "\<C>\<^sub>1 \<hookrightarrow>\<^sup>*\<^sup>* \<C>\<^sub>2 \<equiv> operational_semantics_step\<^sup>*\<^sup>* \<C>\<^sub>1 \<C>\<^sub>2"

abbreviation operational_semantics_step_tranclp :: "config \<Rightarrow> config \<Rightarrow> bool" ("_ \<hookrightarrow>\<^sup>+\<^sup>+ _" 70) where
  "\<C>\<^sub>1 \<hookrightarrow>\<^sup>+\<^sup>+ \<C>\<^sub>2 \<equiv> operational_semantics_step\<^sup>+\<^sup>+ \<C>\<^sub>1 \<C>\<^sub>2"

abbreviation operational_semantics_step_reflclp :: "config \<Rightarrow> config \<Rightarrow> bool" ("_ \<hookrightarrow>\<^sup>=\<^sup>= _" 70) where
  "\<C>\<^sub>1 \<hookrightarrow>\<^sup>=\<^sup>= \<C>\<^sub>2 \<equiv> operational_semantics_step\<^sup>=\<^sup>= \<C>\<^sub>1 \<C>\<^sub>2"

abbreviation operational_semantics_step_relpowp :: "config \<Rightarrow> nat \<Rightarrow> config \<Rightarrow> bool" ("_ \<hookrightarrow>\<^bsup>_\<^esup> _" 70) where
  "\<C>\<^sub>1 \<hookrightarrow>\<^bsup>n\<^esup> \<C>\<^sub>2 \<equiv> (operational_semantics_step ^^ n) \<C>\<^sub>1 \<C>\<^sub>2"

definition operational_semantics_elim_inv :: "config \<Rightarrow> config \<Rightarrow> bool" ("_ \<hookrightarrow>\<^sub>e\<^sup>\<leftarrow> _" 70) where
  "\<C>\<^sub>1 \<hookrightarrow>\<^sub>e\<^sup>\<leftarrow> \<C>\<^sub>2 \<equiv> \<C>\<^sub>2 \<hookrightarrow>\<^sub>e \<C>\<^sub>1"

lemma operational_semantics_trans_generalized:
  assumes "\<C>\<^sub>1 \<hookrightarrow>\<^bsup>n\<^esup> \<C>\<^sub>2"
  assumes "\<C>\<^sub>2 \<hookrightarrow>\<^bsup>m\<^esup> \<C>\<^sub>3"
  shows "\<C>\<^sub>1 \<hookrightarrow>\<^bsup>n + m\<^esup> \<C>\<^sub>3"
  by (metis (no_types, hide_lams) assms(1) assms(2) relcompp.relcompI relpowp_add)

(*
inductive operational_semantics_simlstep :: "config \<Rightarrow> config \<Rightarrow> bool" ("_ \<hookrightarrow>\<^sub>\<nabla> _" 70) where
  "(\<Gamma>\<^sub>1, n \<turnstile> [] \<triangleright> \<Phi>\<^sub>1) \<hookrightarrow>\<^sup>+\<^sup>+ (\<Gamma>, n + 1 \<turnstile> [] \<triangleright> \<Phi>\<^sub>2) \<Longrightarrow>
   \<Psi>\<^sub>1 = [] \<Longrightarrow>
   \<Psi>\<^sub>2 = [] \<Longrightarrow>
   n' = Suc n \<Longrightarrow>
   (\<Gamma>\<^sub>1, n \<turnstile> \<Psi>\<^sub>1 \<triangleright> \<Phi>\<^sub>1) \<hookrightarrow>\<^sub>\<nabla> (\<Gamma>, n' \<turnstile> \<Psi>\<^sub>2 \<triangleright> \<Phi>\<^sub>2)"
*)

abbreviation Cnext_solve :: "config \<Rightarrow> config set" ("\<C>\<^sub>n\<^sub>e\<^sub>x\<^sub>t _") where
  "\<C>\<^sub>n\<^sub>e\<^sub>x\<^sub>t \<S> \<equiv> { \<S>'. \<S> \<hookrightarrow> \<S>' }"

lemma Cnext_solve_instant:
  shows "\<C>\<^sub>n\<^sub>e\<^sub>x\<^sub>t (\<Gamma>, n \<turnstile> [] \<triangleright> \<Phi>)
          \<supseteq> { \<Gamma>, Suc n \<turnstile> \<Phi> \<triangleright> [] }"
  by (simp add: operational_semantics_step.simps operational_semantics_intro.instant_i)

lemma Cnext_solve_not:
  shows "\<C>\<^sub>n\<^sub>e\<^sub>x\<^sub>t (\<Gamma>, n \<turnstile> (not K) # \<Psi> \<triangleright> \<Phi>)
          \<supseteq> { K \<not>\<Up> n # \<Gamma>, n \<turnstile> \<Psi> \<triangleright> (not K) #\<Phi> }"
  by (simp add: operational_semantics_step.simps operational_semantics_elim.not_e)

lemma Cnext_solve_sporadic:
  shows "\<C>\<^sub>n\<^sub>e\<^sub>x\<^sub>t (\<Gamma>, n \<turnstile> (K sporadic \<tau>) # \<Psi> \<triangleright> \<Phi>)
          \<supseteq> { \<Gamma>, n \<turnstile> \<Psi> \<triangleright> (K sporadic \<tau>) # \<Phi>,
              K \<Up> n # K \<Down> n @ \<lfloor>\<tau>\<rfloor> # \<Gamma>, n \<turnstile> \<Psi> \<triangleright> \<Phi> }"
  by (simp add: operational_semantics_step.simps operational_semantics_elim.sporadic_e1 operational_semantics_elim.sporadic_e2)

lemma Cnext_solve_sporadic_anytime:
  shows "\<C>\<^sub>n\<^sub>e\<^sub>x\<^sub>t (\<Gamma>, n \<turnstile> (K sporadic anytime) # \<Psi> \<triangleright> \<Phi>)
          \<supseteq> { \<Gamma>, n \<turnstile> \<Psi> \<triangleright> (K sporadic anytime) # \<Phi>,
              K \<Up> n # \<Gamma>, n \<turnstile> \<Psi> \<triangleright> \<Phi> }"
  by (simp add: operational_semantics_step.simps operational_semantics_elim.sporadic_anytime_e1 operational_semantics_elim.sporadic_anytime_e2)

lemma Cnext_solve_sporadicon:
  shows "\<C>\<^sub>n\<^sub>e\<^sub>x\<^sub>t (\<Gamma>, n \<turnstile> (K\<^sub>1 sporadic \<tau> on K\<^sub>2) # \<Psi> \<triangleright> \<Phi>)
          \<supseteq> { \<Gamma>, n \<turnstile> \<Psi> \<triangleright> (K\<^sub>1 sporadic \<tau> on K\<^sub>2) # \<Phi>,
              K\<^sub>1 \<Up> n # K\<^sub>2 \<Down> n @ \<tau> # \<Gamma>, n \<turnstile> \<Psi> \<triangleright> \<Phi> }"
  by (simp add: operational_semantics_step.simps operational_semantics_elim.sporadic_on_e1 operational_semantics_elim.sporadic_on_e2)

lemma Cnext_solve_tagrel:
  shows "\<C>\<^sub>n\<^sub>e\<^sub>x\<^sub>t (\<Gamma>, n \<turnstile> (tag-relation K\<^sub>1 = \<alpha> * K\<^sub>2 + \<beta>) # \<Psi> \<triangleright> \<Phi>)
          \<supseteq> { (\<tau>\<^sub>v\<^sub>a\<^sub>r(K\<^sub>1, n) \<doteq> \<alpha> * \<tau>\<^sub>v\<^sub>a\<^sub>r(K\<^sub>2, n) + \<beta>) # \<Gamma>, n \<turnstile> \<Psi> \<triangleright> (tag-relation K\<^sub>1 = \<alpha> * K\<^sub>2 + \<beta>) # \<Phi> }"
  by (simp add: operational_semantics_step.simps operational_semantics_elim.tagrel_e)

lemma Cnext_solve_tagrelgen:
  shows "\<C>\<^sub>n\<^sub>e\<^sub>x\<^sub>t (\<Gamma>, n \<turnstile> (tag-relation \<langle>K\<^sub>1, K\<^sub>2\<rangle> \<in> R) # \<Psi> \<triangleright> \<Phi>)
          \<supseteq> { (\<langle>\<tau>\<^sub>v\<^sub>a\<^sub>r(K\<^sub>1, n), \<tau>\<^sub>v\<^sub>a\<^sub>r(K\<^sub>2, n)\<rangle> \<epsilon> R) # \<Gamma>, n \<turnstile> \<Psi> \<triangleright> (tag-relation \<langle>K\<^sub>1, K\<^sub>2\<rangle> \<in> R) # \<Phi> }"
  by (simp add: operational_semantics_step.simps operational_semantics_elim.tagrelgen_e)

lemma Cnext_solve_implies:
  shows "\<C>\<^sub>n\<^sub>e\<^sub>x\<^sub>t (\<Gamma>, n \<turnstile> (K\<^sub>1 implies K\<^sub>2) # \<Psi> \<triangleright> \<Phi>)
          \<supseteq> { K\<^sub>1 \<not>\<Up> n # \<Gamma>, n \<turnstile> \<Psi> \<triangleright> (K\<^sub>1 implies K\<^sub>2) # \<Phi>,
              K\<^sub>1 \<Up> n # K\<^sub>2 \<Up> n # \<Gamma>, n \<turnstile> \<Psi> \<triangleright> (K\<^sub>1 implies K\<^sub>2) # \<Phi>}"
  by (simp add: operational_semantics_step.simps operational_semantics_elim.implies_e1 operational_semantics_elim.implies_e2)

lemma Cnext_solve_implies_not:
  shows "\<C>\<^sub>n\<^sub>e\<^sub>x\<^sub>t (\<Gamma>, n \<turnstile> (K\<^sub>1 implies not K\<^sub>2) # \<Psi> \<triangleright> \<Phi>)
          \<supseteq> { (K\<^sub>1 \<not>\<Up> n) # \<Gamma>, n \<turnstile> \<Psi> \<triangleright> (K\<^sub>1 implies not K\<^sub>2) # \<Phi>,
              (K\<^sub>1 \<Up> n) # (K\<^sub>2 \<not>\<Up> n) # \<Gamma>, n \<turnstile> \<Psi> \<triangleright> (K\<^sub>1 implies not K\<^sub>2) # \<Phi>}"
  by (simp add: operational_semantics_step.simps operational_semantics_elim.implies_not_e1 operational_semantics_elim.implies_not_e2)

lemma Cnext_solve_iff:
  shows "\<C>\<^sub>n\<^sub>e\<^sub>x\<^sub>t (\<Gamma>, n \<turnstile> (K\<^sub>1 iff K\<^sub>2) # \<Psi> \<triangleright> \<Phi>)
          \<supseteq> { (K\<^sub>1 \<not>\<Up> n) # (K\<^sub>2 \<not>\<Up> n) # \<Gamma>, n \<turnstile> \<Psi> \<triangleright> (K\<^sub>1 iff K\<^sub>2) # \<Phi>,
              (K\<^sub>1 \<Up> n) # (K\<^sub>2 \<Up> n) # \<Gamma>, n \<turnstile> \<Psi> \<triangleright> (K\<^sub>1 iff K\<^sub>2) # \<Phi>}"
  by (simp add: operational_semantics_step.simps operational_semantics_elim.iff_e1 operational_semantics_elim.iff_e2)

lemma Cnext_solve_implies_anytime:
  shows "\<C>\<^sub>n\<^sub>e\<^sub>x\<^sub>t (\<Gamma>, n \<turnstile> (master anytime implies slave) # \<Psi> \<triangleright> \<Phi>)
          \<supseteq> { master \<not>\<Up> n # \<Gamma>, n \<turnstile> \<Psi> \<triangleright> (master anytime implies slave) # \<Phi>,
              master \<Up> n # \<Gamma>, n \<turnstile> (slave sporadic anytime) # \<Psi> \<triangleright> (master anytime implies slave) # \<Phi> }"
  by (simp add: operational_semantics_step.simps operational_semantics_elim.implies_anytime_e1 operational_semantics_elim.implies_anytime_e2)

lemma Cnext_solve_timedelayed:
  shows "\<C>\<^sub>n\<^sub>e\<^sub>x\<^sub>t (\<Gamma>, n \<turnstile> (K\<^sub>1 time-delayed by \<delta>\<tau> on K\<^sub>2 implies K\<^sub>3) # \<Psi> \<triangleright> \<Phi>)
          \<supseteq> { K\<^sub>1 \<not>\<Up> n # \<Gamma>, n \<turnstile> \<Psi> \<triangleright> (K\<^sub>1 time-delayed by \<delta>\<tau> on K\<^sub>2 implies K\<^sub>3) # \<Phi>,
              K\<^sub>1 \<Up> n # \<Gamma>, n \<turnstile> (K\<^sub>3 sporadic \<lfloor>\<tau>\<^sub>v\<^sub>a\<^sub>r(K\<^sub>2, n) \<oplus> \<delta>\<tau>\<rfloor> on K\<^sub>2) # \<Psi> \<triangleright> (K\<^sub>1 time-delayed by \<delta>\<tau> on K\<^sub>2 implies K\<^sub>3) # \<Phi> }"
  by (simp add: operational_semantics_step.simps operational_semantics_elim.timedelayed_e1 operational_semantics_elim.timedelayed_e2)

lemma Cnext_solve_sustained_from:
  shows "\<C>\<^sub>n\<^sub>e\<^sub>x\<^sub>t (\<Gamma>, n \<turnstile> (master sustained from begin to end implies slave) # \<Psi> \<triangleright> \<Phi>)
          \<supseteq> { (end \<not>\<Up> n) # (master \<not>\<Up> n) # \<Gamma>,              n \<turnstile> \<Psi> \<triangleright> (master sustained until begin reset on end implies slave) # \<Phi>,
              (end \<not>\<Up> n) # (master \<Up> n) # (slave \<Up> n) # \<Gamma>, n \<turnstile> \<Psi> \<triangleright> (master sustained until begin reset on end implies slave) # \<Phi>,
              (end \<Up> n) # (master \<not>\<Up> n) # \<Gamma>,              n \<turnstile> \<Psi> \<triangleright> (master sustained from begin to end implies slave) # \<Phi>,
              (end \<Up> n) # (master \<Up> n) # (slave \<Up> n) # \<Gamma>, n \<turnstile> \<Psi> \<triangleright> (master sustained from begin to end implies slave) # \<Phi> }"
  sorry

lemma Cnext_solve_sustained_until:
  shows "\<C>\<^sub>n\<^sub>e\<^sub>x\<^sub>t (\<Gamma>, n \<turnstile> (master sustained until end reset on begin implies slave) # \<Psi> \<triangleright> \<Phi>)
          \<supseteq> { (end \<not>\<Up> n) # (master \<not>\<Up> n) # \<Gamma>, n \<turnstile> \<Psi> \<triangleright> (master sustained until begin reset on end implies slave) # \<Phi>,
              (end \<not>\<Up> n) # (master \<Up> n) # (slave \<Up> n) # \<Gamma>, n \<turnstile> \<Psi> \<triangleright> (master sustained until begin reset on end implies slave) # \<Phi>,
              (end \<Up> n) # (master \<not>\<Up> n) # \<Gamma>, n \<turnstile> \<Psi> \<triangleright> (master sustained from begin to end implies slave) # \<Phi>,
              (end \<Up> n) # (master \<Up> n) # (slave \<Up> n) # \<Gamma>, n \<turnstile> \<Psi> \<triangleright> (master sustained from begin to end implies slave) # \<Phi> }"
  sorry

lemma empty_spec_reductions:
  shows "[], 0 \<turnstile> [] \<triangleright> [] \<hookrightarrow>\<^bsup>k\<^esup> [], k \<turnstile> [] \<triangleright> []"
  proof (induct k)
    case 0
    then show ?case by simp
  next
    case (Suc k)
    then show ?case
      using instant_i intro_part by auto
  qed

(* To decide finite-satisfiability of TESL specifications *)
inductive finite_SAT :: "config \<Rightarrow> bool" ("\<TTurnstile> _" 50) where
  finite_SAT_ax: "set (NoSporadic \<Phi>) = set \<Phi> \<Longrightarrow>
                    consistent_run \<Gamma> \<Longrightarrow>
                   \<TTurnstile> \<Gamma>, n \<turnstile> \<Psi> \<triangleright> \<Phi>"
| finite_SAT_i: "\<Gamma>\<^sub>1, n\<^sub>1 \<turnstile> \<Psi>\<^sub>1 \<triangleright> \<Phi>\<^sub>1 \<hookrightarrow> \<Gamma>\<^sub>2, n\<^sub>2 \<turnstile> \<Psi>\<^sub>2 \<triangleright> \<Phi>\<^sub>2 \<Longrightarrow>
                   \<TTurnstile> \<Gamma>\<^sub>2, n\<^sub>2 \<turnstile> \<Psi>\<^sub>2 \<triangleright> \<Phi>\<^sub>2 \<Longrightarrow>
                   \<TTurnstile> \<Gamma>\<^sub>1, n\<^sub>1 \<turnstile> \<Psi>\<^sub>1 \<triangleright> \<Phi>\<^sub>1"

end