theory Operational
imports
    "TESL"
    "Run"

begin
text{* Operational steps *}

abbreviation uncurry_conf
  :: "system \<Rightarrow> instant_index \<Rightarrow> TESL_formula \<Rightarrow> TESL_formula \<Rightarrow> config" ("_, _ \<turnstile> _ \<triangleright> _" 80) where
  "\<Gamma>, n \<turnstile> \<Psi> \<triangleright> \<Phi> \<equiv> (\<Gamma>, n, \<Psi>, \<Phi>)"

inductive operational_semantics_step :: "config \<Rightarrow> config \<Rightarrow> bool" ("_ \<hookrightarrow> _" 70) where
  instant_i:
  "consistent_run \<Gamma> \<Longrightarrow>
   \<Gamma>, n \<turnstile> [] \<triangleright> \<Phi>
     \<hookrightarrow>  \<Gamma>, Suc n \<turnstile> \<Phi> \<triangleright> []"
| sporadic_e1:
  "consistent_run \<Gamma> \<Longrightarrow>
   \<Gamma>, n \<turnstile> (K sporadic \<tau>) # \<Psi> \<triangleright> \<Phi>
     \<hookrightarrow>  \<Gamma>, n \<turnstile> \<Psi> \<triangleright> (K sporadic \<tau>) # \<Phi>"
| sporadic_e2:
  "consistent_run ((K \<Up> n) # (K \<Down> n @ \<lfloor>\<tau>\<rfloor>) # \<Gamma>) \<Longrightarrow>
   \<Gamma>, n \<turnstile> (K sporadic \<tau>) # \<Psi> \<triangleright> \<Phi>
     \<hookrightarrow>  K \<Up> n # K \<Down> n @ \<lfloor>\<tau>\<rfloor> # \<Gamma>, n \<turnstile> \<Psi> \<triangleright> \<Phi>"
| sporadic_on_e1:
  "consistent_run \<Gamma> \<Longrightarrow>
   \<Gamma>, n \<turnstile> (K\<^sub>1 sporadic \<tau> on K\<^sub>2) # \<Psi> \<triangleright> \<Phi>
     \<hookrightarrow>  \<Gamma>, n \<turnstile> \<Psi> \<triangleright> (K\<^sub>1 sporadic \<tau> on K\<^sub>2) # \<Phi>"
| sporadic_on_e2:
  "consistent_run ((K\<^sub>1 \<Up> n) # (K\<^sub>2 \<Down> n @ \<tau>) # \<Gamma>) \<Longrightarrow>
   \<Gamma>, n \<turnstile> (K\<^sub>1 sporadic \<tau> on K\<^sub>2) # \<Psi> \<triangleright> \<Phi>
     \<hookrightarrow>  K\<^sub>1 \<Up> n # K\<^sub>2 \<Down> n @ \<tau> # \<Gamma>, n \<turnstile> \<Psi> \<triangleright> \<Phi>"
| tagrel_e:
  "consistent_run ((\<tau>\<^sub>v\<^sub>a\<^sub>r(K\<^sub>1, n) \<doteq> \<alpha> * \<tau>\<^sub>v\<^sub>a\<^sub>r(K\<^sub>2, n) + \<beta>) # \<Gamma>) \<Longrightarrow>
   \<Gamma>, n \<turnstile> (tag-relation K\<^sub>1 = \<alpha> * K\<^sub>2 + \<beta>) # \<Psi> \<triangleright> \<Phi>
     \<hookrightarrow>  (\<tau>\<^sub>v\<^sub>a\<^sub>r(K\<^sub>1, n) \<doteq> \<alpha> * \<tau>\<^sub>v\<^sub>a\<^sub>r(K\<^sub>2, n) + \<beta>) # \<Gamma>, n \<turnstile> \<Psi> \<triangleright> (tag-relation K\<^sub>1 = \<alpha> * K\<^sub>2 + \<beta>) # \<Phi>"
| implies_e1:
  "consistent_run (K\<^sub>1 \<not>\<Up> n # \<Gamma>) \<Longrightarrow>
   \<Gamma>, n \<turnstile> (K\<^sub>1 implies K\<^sub>2) # \<Psi> \<triangleright> \<Phi>
     \<hookrightarrow>  K\<^sub>1 \<not>\<Up> n # \<Gamma>, n \<turnstile> \<Psi> \<triangleright> (K\<^sub>1 implies K\<^sub>2) # \<Phi>"
| implies_e2:
  "consistent_run ((K\<^sub>1 \<Up> n) # (K\<^sub>2 \<Up> n) # \<Gamma>) \<Longrightarrow>
   \<Gamma>, n \<turnstile> (K\<^sub>1 implies K\<^sub>2) # \<Psi> \<triangleright> \<Phi>
     \<hookrightarrow>  K\<^sub>1 \<Up> n # K\<^sub>2 \<Up> n # \<Gamma>, n \<turnstile> \<Psi> \<triangleright> (K\<^sub>1 implies K\<^sub>2) # \<Phi>"
| timedelayed_e1:
  "consistent_run (K\<^sub>1 \<not>\<Up> n # \<Gamma>) \<Longrightarrow>
   \<Gamma>, n \<turnstile> (K\<^sub>1 time-delayed by \<delta>\<tau> on K\<^sub>2 implies K\<^sub>3) # \<Psi> \<triangleright> \<Phi>
     \<hookrightarrow>  K\<^sub>1 \<not>\<Up> n # \<Gamma>, n \<turnstile> \<Psi> \<triangleright> (K\<^sub>1 time-delayed by \<delta>\<tau> on K\<^sub>2 implies K\<^sub>3) # \<Phi>"
| timedelayed_e2:
  "consistent_run (K\<^sub>1 \<Up> n # \<Gamma>) \<Longrightarrow>
   \<Gamma>, n \<turnstile> (K\<^sub>1 time-delayed by \<delta>\<tau> on K\<^sub>2 implies K\<^sub>3) # \<Psi> \<triangleright> \<Phi>
     \<hookrightarrow>  K\<^sub>1 \<Up> n # \<Gamma>, n \<turnstile> (K\<^sub>3 sporadic \<lfloor>\<tau>\<^sub>v\<^sub>a\<^sub>r(K\<^sub>2, n) \<oplus> \<delta>\<tau>\<rfloor> on K\<^sub>2) # \<Psi> \<triangleright> (K\<^sub>1 time-delayed by \<delta>\<tau> on K\<^sub>2 implies K\<^sub>3) # \<Phi>"

inductive operational_semantics_intro :: "config \<Rightarrow> config \<Rightarrow> bool" ("_ \<hookrightarrow>\<^sub>i _" 70) where
  instant_i:
  "consistent_run \<Gamma> \<Longrightarrow>
   \<Gamma>, n \<turnstile> [] \<triangleright> \<Phi>
     \<hookrightarrow>\<^sub>i  \<Gamma>, Suc n \<turnstile> \<Phi> \<triangleright> []"

inductive operational_semantics_elim :: "config \<Rightarrow> config \<Rightarrow> bool" ("_ \<hookrightarrow>\<^sub>e _" 70) where
  sporadic_e1:
  "consistent_run \<Gamma> \<Longrightarrow>
   \<Gamma>, n \<turnstile> (K sporadic \<tau>) # \<Psi> \<triangleright> \<Phi>
     \<hookrightarrow>\<^sub>e  \<Gamma>, n \<turnstile> \<Psi> \<triangleright> (K sporadic \<tau>) # \<Phi>"
| sporadic_e2:
  "consistent_run ((K \<Up> n) # (K \<Down> n @ \<lfloor>\<tau>\<rfloor>) # \<Gamma>) \<Longrightarrow>
   \<Gamma>, n \<turnstile> (K sporadic \<tau>) # \<Psi> \<triangleright> \<Phi>
     \<hookrightarrow>\<^sub>e  K \<Up> n # K \<Down> n @ \<lfloor>\<tau>\<rfloor> # \<Gamma>, n \<turnstile> \<Psi> \<triangleright> \<Phi>"
| sporadic_on_e1:
  "consistent_run \<Gamma> \<Longrightarrow>
   \<Gamma>, n \<turnstile> (K\<^sub>1 sporadic \<tau> on K\<^sub>2) # \<Psi> \<triangleright> \<Phi>
     \<hookrightarrow>\<^sub>e  \<Gamma>, n \<turnstile> \<Psi> \<triangleright> (K\<^sub>1 sporadic \<tau> on K\<^sub>2) # \<Phi>"
| sporadic_on_e2:
  "consistent_run ((K\<^sub>1 \<Up> n) # (K\<^sub>2 \<Down> n @ \<tau>) # \<Gamma>) \<Longrightarrow>
   \<Gamma>, n \<turnstile> (K\<^sub>1 sporadic \<tau> on K\<^sub>2) # \<Psi> \<triangleright> \<Phi>
     \<hookrightarrow>\<^sub>e  K\<^sub>1 \<Up> n # K\<^sub>2 \<Down> n @ \<tau> # \<Gamma>, n \<turnstile> \<Psi> \<triangleright> \<Phi>"
| tagrel_e:
  "consistent_run ((\<tau>\<^sub>v\<^sub>a\<^sub>r(K\<^sub>1, n) \<doteq> \<alpha> * \<tau>\<^sub>v\<^sub>a\<^sub>r(K\<^sub>2, n) + \<beta>) # \<Gamma>) \<Longrightarrow>
   \<Gamma>, n \<turnstile> (tag-relation K\<^sub>1 = \<alpha> * K\<^sub>2 + \<beta>) # \<Psi> \<triangleright> \<Phi>
     \<hookrightarrow>\<^sub>e  (\<tau>\<^sub>v\<^sub>a\<^sub>r(K\<^sub>1, n) \<doteq> \<alpha> * \<tau>\<^sub>v\<^sub>a\<^sub>r(K\<^sub>2, n) + \<beta>) # \<Gamma>, n \<turnstile> \<Psi> \<triangleright> (tag-relation K\<^sub>1 = \<alpha> * K\<^sub>2 + \<beta>) # \<Phi>"
| implies_e1:
  "consistent_run (K\<^sub>1 \<not>\<Up> n # \<Gamma>) \<Longrightarrow>
   \<Gamma>, n \<turnstile> (K\<^sub>1 implies K\<^sub>2) # \<Psi> \<triangleright> \<Phi>
     \<hookrightarrow>\<^sub>e  K\<^sub>1 \<not>\<Up> n # \<Gamma>, n \<turnstile> \<Psi> \<triangleright> (K\<^sub>1 implies K\<^sub>2) # \<Phi>"
| implies_e2:
  "consistent_run ((K\<^sub>1 \<Up> n) # (K\<^sub>2 \<Up> n) # \<Gamma>) \<Longrightarrow>
   \<Gamma>, n \<turnstile> (K\<^sub>1 implies K\<^sub>2) # \<Psi> \<triangleright> \<Phi>
     \<hookrightarrow>\<^sub>e  K\<^sub>1 \<Up> n # K\<^sub>2 \<Up> n # \<Gamma>, n \<turnstile> \<Psi> \<triangleright> (K\<^sub>1 implies K\<^sub>2) # \<Phi>"
| timedelayed_e1:
  "consistent_run (K\<^sub>1 \<not>\<Up> n # \<Gamma>) \<Longrightarrow>
   \<Gamma>, n \<turnstile> (K\<^sub>1 time-delayed by \<delta>\<tau> on K\<^sub>2 implies K\<^sub>3) # \<Psi> \<triangleright> \<Phi>
     \<hookrightarrow>\<^sub>e  K\<^sub>1 \<not>\<Up> n # \<Gamma>, n \<turnstile> \<Psi> \<triangleright> (K\<^sub>1 time-delayed by \<delta>\<tau> on K\<^sub>2 implies K\<^sub>3) # \<Phi>"
| timedelayed_e2:
  "consistent_run (K\<^sub>1 \<Up> n # \<Gamma>) \<Longrightarrow>
   \<Gamma>, n \<turnstile> (K\<^sub>1 time-delayed by \<delta>\<tau> on K\<^sub>2 implies K\<^sub>3) # \<Psi> \<triangleright> \<Phi>
     \<hookrightarrow>\<^sub>e  K\<^sub>1 \<Up> n # \<Gamma>, n \<turnstile> (K\<^sub>3 sporadic \<lfloor>\<tau>\<^sub>v\<^sub>a\<^sub>r(K\<^sub>2, n) \<oplus> \<delta>\<tau>\<rfloor> on K\<^sub>2) # \<Psi> \<triangleright> (K\<^sub>1 time-delayed by \<delta>\<tau> on K\<^sub>2 implies K\<^sub>3) # \<Phi>"

find_theorems name:"operational_semantics_step"

lemma operational_semantics_split:
  shows "\<S>\<^sub>1 \<hookrightarrow> \<S>\<^sub>2 = \<S>\<^sub>1 \<hookrightarrow>\<^sub>i \<S>\<^sub>2 \<or> \<S>\<^sub>1 \<hookrightarrow>\<^sub>e \<S>\<^sub>2"
  apply (rule operational_semantics_step.induct)
  defer
  apply (simp add: operational_semantics_intro.instant_i operational_semantics_step.instant_i)
  apply (simp add: operational_semantics_elim.sporadic_e1)
  apply (simp add: operational_semantics_elim.sporadic_e2)
  apply (simp add: operational_semantics_elim.sporadic_on_e1)
  apply (simp add: operational_semantics_elim.sporadic_on_e2)
  apply (simp add: operational_semantics_elim.tagrel_e)
  apply (simp add: operational_semantics_elim.implies_e1)
  apply (simp add: operational_semantics_elim.implies_e2)
  apply (simp add: operational_semantics_elim.timedelayed_e1)
  apply (simp add: operational_semantics_elim.timedelayed_e2)
  sorry

abbreviation operational_semantics_step_rtranclp :: "config \<Rightarrow> config \<Rightarrow> bool" ("_ \<hookrightarrow>\<^sup>*\<^sup>* _" 70) where
  "A \<hookrightarrow>\<^sup>*\<^sup>* B \<equiv> operational_semantics_step\<^sup>*\<^sup>* A B"

abbreviation operational_semantics_step_tranclp :: "config \<Rightarrow> config \<Rightarrow> bool" ("_ \<hookrightarrow>\<^sup>+\<^sup>+ _" 70) where
  "A \<hookrightarrow>\<^sup>+\<^sup>+ B \<equiv> operational_semantics_step\<^sup>+\<^sup>+ A B"

abbreviation operational_semantics_step_reflclp :: "config \<Rightarrow> config \<Rightarrow> bool" ("_ \<hookrightarrow>\<^sup>=\<^sup>= _" 70) where
  "A \<hookrightarrow>\<^sup>=\<^sup>= B \<equiv> operational_semantics_step\<^sup>=\<^sup>= A B"

abbreviation operational_semantics_step_relpowp :: "config \<Rightarrow> nat \<Rightarrow> config \<Rightarrow> bool" ("_ \<hookrightarrow>\<^bsup>_\<^esup> _" 70) where
  "A \<hookrightarrow>\<^bsup>n\<^esup> B \<equiv> (operational_semantics_step ^^ n) A B"

inductive operational_semantics_simlstep :: "config \<Rightarrow> config \<Rightarrow> bool" ("_ \<hookrightarrow>\<^sub>\<nabla> _" 70) where
  "(\<Gamma>\<^sub>1, n \<turnstile> [] \<triangleright> \<Phi>\<^sub>1) \<hookrightarrow>\<^sup>+\<^sup>+ (\<Gamma>, n + 1 \<turnstile> [] \<triangleright> \<Phi>\<^sub>2) \<Longrightarrow>
   (\<Gamma>\<^sub>1, n \<turnstile> [] \<triangleright> \<Phi>\<^sub>1) \<hookrightarrow>\<^sub>\<nabla> (\<Gamma>, n + 1 \<turnstile> [] \<triangleright> \<Phi>\<^sub>2)"

inductive finite_SAT :: "config \<Rightarrow> bool" ("\<TTurnstile> _" 50) where
  finite_SAT_ax: "set (NoSporadic \<Phi>) = set \<Phi> \<Longrightarrow>
                    consistent_run \<Gamma> \<Longrightarrow>
                   \<TTurnstile> \<Gamma>, n \<turnstile> \<Psi> \<triangleright> \<Phi>"
| finite_SAT_i: "\<Gamma>\<^sub>1, n\<^sub>1 \<turnstile> \<Psi>\<^sub>1 \<triangleright> \<Phi>\<^sub>1 \<hookrightarrow> \<Gamma>\<^sub>2, n\<^sub>2 \<turnstile> \<Psi>\<^sub>2 \<triangleright> \<Phi>\<^sub>2 \<Longrightarrow>
                   \<TTurnstile> \<Gamma>\<^sub>2, n\<^sub>2 \<turnstile> \<Psi>\<^sub>2 \<triangleright> \<Phi>\<^sub>2 \<Longrightarrow>
                   \<TTurnstile> \<Gamma>\<^sub>1, n\<^sub>1 \<turnstile> \<Psi>\<^sub>1 \<triangleright> \<Phi>\<^sub>1"

end