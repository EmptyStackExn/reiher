theory ConcreteOperational
imports
    "TESL"
    "Run"

begin

type_synonym '\<tau> concrete_config = "'\<tau> run * instant_index * '\<tau> TESL_formula * '\<tau> TESL_formula"

abbreviation uncurry_conf
  :: "('\<tau>::linordered_field) run \<Rightarrow> instant_index \<Rightarrow> '\<tau> TESL_formula \<Rightarrow> '\<tau> TESL_formula \<Rightarrow> '\<tau> concrete_config" ("_, _ \<turnstile> _ \<triangleright> _" 80) where
  "\<rho>, n \<turnstile> \<Psi> \<triangleright> \<Phi> \<equiv> (\<rho>, n, \<Psi>, \<Phi>)"

inductive operational_semantics_intro :: "('\<tau>::linordered_field) concrete_config \<Rightarrow> '\<tau> concrete_config \<Rightarrow> bool" ("_ \<leadsto>\<^sub>i _" 70) where
  instant_i:
  "(\<rho>, n \<turnstile> [] \<triangleright> \<Phi>)
     \<leadsto>\<^sub>i  (\<rho>, Suc n \<turnstile> \<Phi> \<triangleright> [])"

inductive operational_semantics_elim :: "('\<tau>::linordered_field) concrete_config \<Rightarrow> '\<tau> concrete_config \<Rightarrow> bool" ("_ \<leadsto>\<^sub>e _" 70) where
  sporadic_e1:
  "(\<rho>, n \<turnstile> ((K sporadic \<tau>) # \<Psi>) \<triangleright> \<Phi>)
     \<leadsto>\<^sub>e  (\<rho>, n \<turnstile> \<Psi> \<triangleright> ((K sporadic \<tau>) # \<Phi>))"
| sporadic_e2:
  "\<rho> \<turnstile> (K \<Up> n) \<Longrightarrow>
   \<rho> \<turnstile> (K \<Down> n @ \<lfloor>\<tau>\<rfloor>) \<Longrightarrow>
   (\<rho>, n \<turnstile> ((K sporadic \<tau>) # \<Psi>) \<triangleright> \<Phi>)
     \<leadsto>\<^sub>e  (\<rho>, n \<turnstile> \<Psi> \<triangleright> \<Phi>)"
| sporadic_on_e1:
  "(\<rho>, n \<turnstile> ((K\<^sub>1 sporadic \<tau> on K\<^sub>2) # \<Psi>) \<triangleright> \<Phi>)
     \<leadsto>\<^sub>e  (\<rho>, n \<turnstile> \<Psi> \<triangleright> ((K\<^sub>1 sporadic \<tau> on K\<^sub>2) # \<Phi>))"
| sporadic_on_e2:
  "\<rho> \<turnstile> (K\<^sub>1 \<Up> n) \<Longrightarrow>
   \<rho> \<turnstile> (K\<^sub>2 \<Down> n @ \<tau>) \<Longrightarrow>
   (\<rho>, n \<turnstile> ((K\<^sub>1 sporadic \<tau> on K\<^sub>2) # \<Psi>) \<triangleright> \<Phi>)
     \<leadsto>\<^sub>e  (\<rho>, n \<turnstile> \<Psi> \<triangleright> \<Phi>)"
| tagrel_e:
  "\<rho> \<turnstile> ((\<tau>\<^sub>v\<^sub>a\<^sub>r(K\<^sub>1, n)) \<doteq> \<alpha> * \<tau>\<^sub>v\<^sub>a\<^sub>r(K\<^sub>2, n) + \<beta>) \<Longrightarrow>
   (\<rho>, n \<turnstile> ((tag-relation K\<^sub>1 = \<alpha> * K\<^sub>2 + \<beta>) # \<Psi>) \<triangleright> \<Phi>)
     \<leadsto>\<^sub>e  (\<rho>, n \<turnstile> \<Psi> \<triangleright> ((tag-relation K\<^sub>1 = \<alpha> * K\<^sub>2 + \<beta>) # \<Phi>))"
| tagrelgen_e:
  "\<rho> \<turnstile> (\<langle>\<tau>\<^sub>v\<^sub>a\<^sub>r(K\<^sub>1, n), \<tau>\<^sub>v\<^sub>a\<^sub>r(K\<^sub>2, n)\<rangle> \<epsilon> R) \<Longrightarrow>
   (\<rho>, n \<turnstile> ((tag-relation \<langle>K\<^sub>1, K\<^sub>2\<rangle> \<in> R) # \<Psi>) \<triangleright> \<Phi>)
     \<leadsto>\<^sub>e  (\<rho>, n \<turnstile> \<Psi> \<triangleright> ((tag-relation \<langle>K\<^sub>1, K\<^sub>2\<rangle> \<in> R) # \<Phi>))"
| implies_e1:
  "\<rho> \<turnstile> (K\<^sub>1 \<not>\<Up> n) \<Longrightarrow>
   (\<rho>, n \<turnstile> ((K\<^sub>1 implies K\<^sub>2) # \<Psi>) \<triangleright> \<Phi>)
     \<leadsto>\<^sub>e  (\<rho>, n \<turnstile> \<Psi> \<triangleright> ((K\<^sub>1 implies K\<^sub>2) # \<Phi>))"
| implies_e2:
  "\<rho> \<turnstile> (K\<^sub>1 \<Up> n) \<Longrightarrow>
   \<rho> \<turnstile> (K\<^sub>2 \<Up> n) \<Longrightarrow>
   (\<rho>, n \<turnstile> ((K\<^sub>1 implies K\<^sub>2) # \<Psi>) \<triangleright> \<Phi>)
     \<leadsto>\<^sub>e  (\<rho>, n \<turnstile> \<Psi> \<triangleright> ((K\<^sub>1 implies K\<^sub>2) # \<Phi>))"
| timedelayed_e1:
  "\<rho> \<turnstile> (K\<^sub>1 \<not>\<Up> n) \<Longrightarrow>
   (\<rho>, n \<turnstile> ((K\<^sub>1 time-delayed by \<delta>\<tau> on K\<^sub>2 implies K\<^sub>3) # \<Psi>) \<triangleright> \<Phi>)
     \<leadsto>\<^sub>e  (\<rho>, n \<turnstile> \<Psi> \<triangleright> ((K\<^sub>1 time-delayed by \<delta>\<tau> on K\<^sub>2 implies K\<^sub>3) # \<Phi>))"
| timedelayed_e2:
  "\<rho> \<turnstile> (K\<^sub>1 \<Up> n) \<Longrightarrow>
   (\<rho>, n \<turnstile> ((K\<^sub>1 time-delayed by \<delta>\<tau> on K\<^sub>2 implies K\<^sub>3) # \<Psi>) \<triangleright> \<Phi>)
     \<leadsto>\<^sub>e  (\<rho>, n \<turnstile> ((K\<^sub>3 sporadic \<lfloor>\<tau>\<^sub>v\<^sub>a\<^sub>r(K\<^sub>2, n) \<oplus> \<delta>\<tau>\<rfloor> on K\<^sub>2) # \<Psi>) \<triangleright> ((K\<^sub>1 time-delayed by \<delta>\<tau> on K\<^sub>2 implies K\<^sub>3) # \<Phi>))"
| precedes_e:
  "#\<^sup>< \<rho> master n \<ge> #\<^sup>\<le> \<rho> slave n \<Longrightarrow>
   (\<rho>, n \<turnstile> ((K\<^sub>1 precedes K\<^sub>2) # \<Psi>) \<triangleright> \<Phi>)
     \<leadsto>\<^sub>e  (\<rho>, n \<turnstile> \<Psi> \<triangleright> ((K\<^sub>1 precedes K\<^sub>2) # \<Phi>))"

inductive operational_semantics_step :: "('\<tau>::linordered_field) concrete_config \<Rightarrow> '\<tau> concrete_config \<Rightarrow> bool" ("_ \<leadsto> _" 70) where
    intro_part: "(\<rho>\<^sub>1, n\<^sub>1 \<turnstile> \<Psi>\<^sub>1 \<triangleright> \<Phi>\<^sub>1)  \<leadsto>\<^sub>i  (\<rho>\<^sub>2, n\<^sub>2 \<turnstile> \<Psi>\<^sub>2 \<triangleright> \<Phi>\<^sub>2)
   \<Longrightarrow> (\<rho>\<^sub>1, n\<^sub>1 \<turnstile> \<Psi>\<^sub>1 \<triangleright> \<Phi>\<^sub>1)  \<leadsto>  (\<rho>\<^sub>2, n\<^sub>2 \<turnstile> \<Psi>\<^sub>2 \<triangleright> \<Phi>\<^sub>2)"
  | elims_part: "(\<rho>\<^sub>1, n\<^sub>1 \<turnstile> \<Psi>\<^sub>1 \<triangleright> \<Phi>\<^sub>1)  \<leadsto>\<^sub>e  (\<rho>\<^sub>2, n\<^sub>2 \<turnstile> \<Psi>\<^sub>2 \<triangleright> \<Phi>\<^sub>2)
   \<Longrightarrow> (\<rho>\<^sub>1, n\<^sub>1 \<turnstile> \<Psi>\<^sub>1 \<triangleright> \<Phi>\<^sub>1)  \<leadsto>  (\<rho>\<^sub>2, n\<^sub>2 \<turnstile> \<Psi>\<^sub>2 \<triangleright> \<Phi>\<^sub>2)"

abbreviation operational_semantics_step_rtranclp :: "('\<tau>::linordered_field) concrete_config \<Rightarrow> '\<tau> concrete_config \<Rightarrow> bool" ("_ \<leadsto>\<^sup>*\<^sup>* _" 70) where
  "\<C>\<^sub>1 \<leadsto>\<^sup>*\<^sup>* \<C>\<^sub>2 \<equiv> operational_semantics_step\<^sup>*\<^sup>* \<C>\<^sub>1 \<C>\<^sub>2"

abbreviation operational_semantics_step_tranclp :: "('\<tau>::linordered_field) concrete_config \<Rightarrow> '\<tau> concrete_config \<Rightarrow> bool" ("_ \<leadsto>\<^sup>+\<^sup>+ _" 70) where
  "\<C>\<^sub>1 \<leadsto>\<^sup>+\<^sup>+ \<C>\<^sub>2 \<equiv> operational_semantics_step\<^sup>+\<^sup>+ \<C>\<^sub>1 \<C>\<^sub>2"

abbreviation operational_semantics_step_reflclp :: "('\<tau>::linordered_field) concrete_config \<Rightarrow> '\<tau> concrete_config \<Rightarrow> bool" ("_ \<leadsto>\<^sup>=\<^sup>= _" 70) where
  "\<C>\<^sub>1 \<leadsto>\<^sup>=\<^sup>= \<C>\<^sub>2 \<equiv> operational_semantics_step\<^sup>=\<^sup>= \<C>\<^sub>1 \<C>\<^sub>2"

abbreviation operational_semantics_step_relpowp :: "('\<tau>::linordered_field) concrete_config \<Rightarrow> nat \<Rightarrow> '\<tau> concrete_config \<Rightarrow> bool" ("_ \<leadsto>\<^bsup>_\<^esup> _" 70) where
  "\<C>\<^sub>1 \<leadsto>\<^bsup>n\<^esup> \<C>\<^sub>2 \<equiv> (operational_semantics_step ^^ n) \<C>\<^sub>1 \<C>\<^sub>2"

definition operational_semantics_elim_inv :: "('\<tau>::linordered_field) concrete_config \<Rightarrow> '\<tau> concrete_config \<Rightarrow> bool" ("_ \<leadsto>\<^sub>e\<^sup>\<leftarrow> _" 70) where
  "\<C>\<^sub>1 \<leadsto>\<^sub>e\<^sup>\<leftarrow> \<C>\<^sub>2 \<equiv> \<C>\<^sub>2 \<leadsto>\<^sub>e \<C>\<^sub>1"

lemma operational_semantics_trans_generalized:
  assumes "\<C>\<^sub>1 \<leadsto>\<^bsup>n\<^esup> \<C>\<^sub>2"
  assumes "\<C>\<^sub>2 \<leadsto>\<^bsup>m\<^esup> \<C>\<^sub>3"
  shows "\<C>\<^sub>1 \<leadsto>\<^bsup>n + m\<^esup> \<C>\<^sub>3"
  by (metis (no_types, hide_lams) assms(1) assms(2) relcompp.relcompI relpowp_add)


end
