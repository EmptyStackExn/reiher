theory Operational
imports
    "TESL"
    "Run"

begin
text{* Operational steps *}

abbreviation uncurry_conf
  :: "system \<Rightarrow> instant_index \<Rightarrow> TESL_formula \<Rightarrow> TESL_formula
   \<Rightarrow> (system \<times> instant_index \<times> TESL_formula \<times> TESL_formula)" ("_, _ \<turnstile> _ \<triangleright> _" 50) where
  "\<Gamma>, n \<turnstile> \<Psi> \<triangleright> \<Phi> \<equiv> (\<Gamma>, n, \<Psi>, \<Phi>)"

inductive operational_semantics_step
  :: "(system \<times> instant_index \<times> TESL_formula \<times> TESL_formula)
    \<Rightarrow> (system \<times> instant_index \<times> TESL_formula \<times> TESL_formula) \<Rightarrow> bool" ("_ \<hookrightarrow> _" 50) where
  instant_i:
  "consistent_run \<Gamma> \<Longrightarrow>
   \<Gamma>, n \<turnstile> [] \<triangleright> \<Phi>
     \<hookrightarrow>  \<Gamma>, Suc n \<turnstile> \<Phi> \<triangleright> []"
| sporadic_e1:
  "consistent_run \<Gamma> \<Longrightarrow>
   \<Gamma>, n \<turnstile> (K sporadic \<tau>) # \<Psi> \<triangleright> \<Phi>
     \<hookrightarrow>  \<top>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n # \<top>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n # \<Gamma>, n \<turnstile> \<top>\<^sub>T\<^sub>E\<^sub>S\<^sub>L # \<Psi> \<triangleright> (K sporadic \<tau>) # \<Phi>"
| sporadic_e2:
  "consistent_run ((K \<Up> n) # (K \<Down> n @ \<lfloor>\<tau>\<rfloor>) # \<Gamma>) \<Longrightarrow>
   \<Gamma>, n \<turnstile> (K sporadic \<tau>) # \<Psi> \<triangleright> \<Phi>
     \<hookrightarrow>  K \<Up> n # K \<Down> n @ \<lfloor>\<tau>\<rfloor> # \<Gamma>, n \<turnstile> \<top>\<^sub>T\<^sub>E\<^sub>S\<^sub>L # \<Psi> \<triangleright> \<top>\<^sub>T\<^sub>E\<^sub>S\<^sub>L # \<Phi>"
| sporadic_on_e1:
  "consistent_run \<Gamma> \<Longrightarrow>
   \<Gamma>, n \<turnstile> (K\<^sub>1 sporadic \<tau> on K\<^sub>2) # \<Psi> \<triangleright> \<Phi>
     \<hookrightarrow>  \<top>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n # \<top>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n # \<Gamma>, n \<turnstile> \<top>\<^sub>T\<^sub>E\<^sub>S\<^sub>L # \<Psi> \<triangleright> (K\<^sub>1 sporadic \<tau> on K\<^sub>2) # \<Phi>"
| sporadic_on_e2:
  "consistent_run ((K\<^sub>1 \<Up> n) # (K\<^sub>2 \<Down> n @ \<tau>) # \<Gamma>) \<Longrightarrow>
   \<Gamma>, n \<turnstile> (K\<^sub>1 sporadic \<tau> on K\<^sub>2) # \<Psi> \<triangleright> \<Phi>
     \<hookrightarrow>  K\<^sub>1 \<Up> n # K\<^sub>2 \<Down> n @ \<tau> # \<Gamma>, n \<turnstile> \<top>\<^sub>T\<^sub>E\<^sub>S\<^sub>L # \<Psi> \<triangleright> \<top>\<^sub>T\<^sub>E\<^sub>S\<^sub>L # \<Phi>"
| tagrel_e:
  "consistent_run ((\<tau>\<^sub>v\<^sub>a\<^sub>r(K\<^sub>1, n) \<doteq> \<alpha> * \<tau>\<^sub>v\<^sub>a\<^sub>r(K\<^sub>2, n) + \<beta>) # \<Gamma>) \<Longrightarrow>
   \<Gamma>, n \<turnstile> (tag-relation K\<^sub>1 = \<alpha> * K\<^sub>2 + \<beta>) # \<Psi> \<triangleright> \<Phi>
     \<hookrightarrow>  \<top>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n # (\<tau>\<^sub>v\<^sub>a\<^sub>r(K\<^sub>1, n) \<doteq> \<alpha> * \<tau>\<^sub>v\<^sub>a\<^sub>r(K\<^sub>2, n) + \<beta>) # \<Gamma>, n \<turnstile> \<top>\<^sub>T\<^sub>E\<^sub>S\<^sub>L # \<Psi> \<triangleright> (tag-relation K\<^sub>1 = \<alpha> * K\<^sub>2 + \<beta>) # \<Phi>"
| implies_e1:
  "consistent_run (K\<^sub>1 \<not>\<Up> n # \<Gamma>) \<Longrightarrow>
   \<Gamma>, n \<turnstile> (K\<^sub>1 implies K\<^sub>2) # \<Psi> \<triangleright> \<Phi>
     \<hookrightarrow>  \<top>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n # K\<^sub>1 \<not>\<Up> n # \<Gamma>, n \<turnstile> \<top>\<^sub>T\<^sub>E\<^sub>S\<^sub>L # \<Psi> \<triangleright> (K\<^sub>1 implies K\<^sub>2) # \<Phi>"
| implies_e2:
  "consistent_run ((K\<^sub>1 \<Up> n) # (K\<^sub>2 \<Up> n) # \<Gamma>) \<Longrightarrow>
   \<Gamma>, n \<turnstile> (K\<^sub>1 implies K\<^sub>2) # \<Psi> \<triangleright> \<Phi>
     \<hookrightarrow>  K\<^sub>1 \<Up> n # K\<^sub>2 \<Up> n # \<Gamma>, n \<turnstile> \<top>\<^sub>T\<^sub>E\<^sub>S\<^sub>L # \<Psi> \<triangleright> (K\<^sub>1 implies K\<^sub>2) # \<Phi>"
| timedelayed_e1:
  "consistent_run (K\<^sub>1 \<not>\<Up> n # \<Gamma>) \<Longrightarrow>
   \<Gamma>, n \<turnstile> (K\<^sub>1 time-delayed by \<delta>\<tau> on K\<^sub>2 implies K\<^sub>3) # \<Psi> \<triangleright> \<Phi>
     \<hookrightarrow>  \<top>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n # K\<^sub>1 \<not>\<Up> n # \<Gamma>, n \<turnstile> \<top>\<^sub>T\<^sub>E\<^sub>S\<^sub>L # \<Psi> \<triangleright> (K\<^sub>1 time-delayed by \<delta>\<tau> on K\<^sub>2 implies K\<^sub>3) # \<Phi>"
| timedelayed_e2:
  "consistent_run (K\<^sub>1 \<Up> n # \<Gamma>) \<Longrightarrow>
   \<Gamma>, n \<turnstile> (K\<^sub>1 time-delayed by \<delta>\<tau> on K\<^sub>2 implies K\<^sub>3) # \<Psi> \<triangleright> \<Phi>
     \<hookrightarrow>  \<top>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n # K\<^sub>1 \<Up> n # \<Gamma>, n \<turnstile> (K\<^sub>3 sporadic \<lfloor>\<tau>\<^sub>v\<^sub>a\<^sub>r(K\<^sub>2, n) \<oplus> \<delta>\<tau>\<rfloor> on K\<^sub>2) # \<Psi> \<triangleright> (K\<^sub>1 time-delayed by \<delta>\<tau> on K\<^sub>2 implies K\<^sub>3) # \<Phi>"

abbreviation operational_semantics_step'
  :: "(system \<times> instant_index \<times> TESL_formula \<times> TESL_formula) rel" ("\<hookrightarrow>\<^sup>\<up>") where
  "\<hookrightarrow>\<^sup>\<up> \<equiv> { ((\<Gamma>\<^sub>1, n\<^sub>1, \<Psi>\<^sub>1, \<Phi>\<^sub>1), (\<Gamma>\<^sub>2, n\<^sub>2, \<Psi>\<^sub>2, \<Phi>\<^sub>2)).
              \<Gamma>\<^sub>1, n\<^sub>1 \<turnstile> \<Psi>\<^sub>1 \<triangleright> \<Phi>\<^sub>1 \<hookrightarrow> \<Gamma>\<^sub>2, n\<^sub>2 \<turnstile> \<Psi>\<^sub>2 \<triangleright> \<Phi>\<^sub>2 }"

abbreviation operational_semantics_simulation_step
  :: "(system \<times> instant_index \<times> TESL_formula \<times> TESL_formula) rel" ("\<hookrightarrow>\<^sup>\<nabla>") where
  "\<hookrightarrow>\<^sup>\<nabla> \<equiv> { ((\<Gamma>\<^sub>1, n\<^sub>1, \<Psi>, \<Phi>\<^sub>1), (\<Gamma>\<^sub>2, n\<^sub>2, \<Psi>, \<Phi>\<^sub>2)).
                \<Psi> = []
              \<and> (\<Gamma>\<^sub>1, n\<^sub>1 \<turnstile> \<Psi> \<triangleright> \<Phi>\<^sub>1, \<Gamma>\<^sub>2, n\<^sub>2 \<turnstile> \<Psi> \<triangleright> \<Phi>\<^sub>2) \<in> \<hookrightarrow>\<^sup>\<up>\<^sup>+
              \<and> consistent_run \<Gamma>\<^sub>1
              \<and> consistent_run \<Gamma>\<^sub>2}"

(* Example of one simulation step: introduction rule then one elimination *)
(* Note that \<hookrightarrow>\<^sub>\<nabla> is unfolded as necessary as it is to eliminate \<psi>-formulae *)
lemma "([], 0        \<turnstile> [] \<triangleright> [H\<^sub>1 sporadic \<tau>\<^sub>i\<^sub>n\<^sub>t 0, H\<^sub>1 implies H\<^sub>2],
         \<Gamma>, 1 \<turnstile> [] \<triangleright> \<Phi>)
         \<in> \<hookrightarrow>\<^sup>\<nabla>"
apply auto
apply (rule trancl_into_trancl)
apply (rule trancl_into_trancl)
apply (rule r_into_trancl)
apply simp
apply (rule instant_i)
  apply (rule witness_consistency, auto, ((simp add: Abs_run_inverse_rewrite mono_iff_le_Suc)+)?)
apply (rule sporadic_e2)
  apply (rule witness_consistency, auto, ((simp add: Abs_run_inverse_rewrite mono_iff_le_Suc)+)?)
sorry (* OK *)

inductive finite_SAT
  :: "(system \<times> instant_index \<times> TESL_formula \<times> TESL_formula) \<Rightarrow> bool" ("\<TTurnstile> _" 50) where
  finite_SAT_ax: "set (NoSporadic \<Phi>) = set \<Phi> \<Longrightarrow>
                    consistent_run \<Gamma> \<Longrightarrow>
                   \<TTurnstile> \<Gamma>, n \<turnstile> \<Psi> \<triangleright> \<Phi>"
| finite_SAT_i: "\<Gamma>\<^sub>1, n\<^sub>1 \<turnstile> \<Psi>\<^sub>1 \<triangleright> \<Phi>\<^sub>1 \<hookrightarrow> \<Gamma>\<^sub>2, n\<^sub>2 \<turnstile> \<Psi>\<^sub>2 \<triangleright> \<Phi>\<^sub>2 \<Longrightarrow>
                   \<TTurnstile> \<Gamma>\<^sub>2, n\<^sub>2 \<turnstile> \<Psi>\<^sub>2 \<triangleright> \<Phi>\<^sub>2 \<Longrightarrow>
                   \<TTurnstile> \<Gamma>\<^sub>1, n\<^sub>1 \<turnstile> \<Psi>\<^sub>1 \<triangleright> \<Phi>\<^sub>1"

end