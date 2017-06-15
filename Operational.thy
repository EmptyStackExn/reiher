theory Operational
imports
    "TESL"
    "Run"

begin
text{* Operational steps *}

abbreviation NoSporadic :: "TESL_formula \<Rightarrow> TESL_formula" where 
  "NoSporadic f \<equiv> (List.filter (\<lambda>f\<^sub>a\<^sub>t\<^sub>o\<^sub>m. case f\<^sub>a\<^sub>t\<^sub>o\<^sub>m of
      _ sporadic _  \<Rightarrow> False
    | _ sporadic _ on _ \<Rightarrow> False
    | _ \<Rightarrow> True) f)"

abbreviation uncurry_conf
  :: "system \<Rightarrow> instant_index \<Rightarrow> TESL_formula \<Rightarrow> TESL_formula
   \<Rightarrow> (system \<times> instant_index \<times> TESL_formula \<times> TESL_formula)" ("_, _ \<turnstile> _ \<triangleright> _" 50) where
  "\<Gamma>, n \<turnstile> \<psi> \<triangleright> \<phi> \<equiv> (\<Gamma>, n, \<psi>, \<phi>)"

inductive operational_semantics_step
  :: "(system \<times> instant_index \<times> TESL_formula \<times> TESL_formula)
    \<Rightarrow> (system \<times> instant_index \<times> TESL_formula \<times> TESL_formula) \<Rightarrow> bool" ("_ \<hookrightarrow> _" 50) where
  simulation_end:
  "set (NoSporadic \<phi>) = set \<phi> \<Longrightarrow>
   consistent_run \<Gamma> \<Longrightarrow>
   \<Gamma>, n \<turnstile> \<psi> \<triangleright> \<phi>
   \<hookrightarrow> \<Gamma>, n \<turnstile> \<psi> \<triangleright> \<phi>"
| instant_i:
  "consistent_run \<Gamma> \<Longrightarrow>
   \<Gamma>, n \<turnstile> [] \<triangleright> \<phi>
   \<hookrightarrow> \<Gamma>, Suc n \<turnstile> \<phi> \<triangleright> NoSporadic \<phi>"
| sporadic_e1:
  "consistent_run \<Gamma> \<Longrightarrow>
   \<Gamma>, n \<turnstile> (K sporadic \<tau>) # \<psi> \<triangleright> \<phi>
   \<hookrightarrow> \<Gamma>, n \<turnstile> \<psi> \<triangleright> (K sporadic \<tau>) # \<phi>"
| sporadic_e2:
  "consistent_run \<Gamma>' \<Longrightarrow>
   \<Gamma>' = (K \<Up> n) # (K \<Down> n @ \<lfloor>\<tau>\<rfloor>) # \<Gamma> \<Longrightarrow>
   \<Gamma>, n \<turnstile> (K sporadic \<tau>) # \<psi> \<triangleright> \<phi>
   \<hookrightarrow> \<Gamma>', n \<turnstile> \<psi> \<triangleright> \<phi>"
| sporadic_on_e1:
  "consistent_run \<Gamma> \<Longrightarrow>
   \<Gamma>, n \<turnstile> (K\<^sub>1 sporadic \<tau> on K\<^sub>2) # \<psi> \<triangleright> \<phi>
   \<hookrightarrow> \<Gamma>, n \<turnstile> \<psi> \<triangleright> (K\<^sub>1 sporadic \<tau> on K\<^sub>2) # \<phi>"
| sporadic_on_e2:
  "consistent_run \<Gamma>' \<Longrightarrow>
   \<Gamma>' = (K\<^sub>2 \<Up> n) # (K\<^sub>1 \<Down> n @ \<tau>) # \<Gamma> \<Longrightarrow>
   \<Gamma>, n \<turnstile> (K\<^sub>1 sporadic \<tau> on K\<^sub>2) # \<psi> \<triangleright> \<phi>
   \<hookrightarrow> \<Gamma>, n \<turnstile> \<psi> \<triangleright> \<phi>"
| tagrel_e:
  "consistent_run \<Gamma>' \<Longrightarrow>
   \<Gamma>' = (\<tau>\<^sub>v\<^sub>a\<^sub>r(K\<^sub>1, n) \<doteq> \<alpha> * \<tau>\<^sub>v\<^sub>a\<^sub>r(K\<^sub>2, n) + \<beta>) # \<Gamma> \<Longrightarrow>
   \<Gamma>, n \<turnstile> (tag-relation K\<^sub>1 = \<alpha> * K\<^sub>2 + \<beta>) # \<psi> \<triangleright> \<phi>
   \<hookrightarrow> \<Gamma>', n \<turnstile> \<psi> \<triangleright> \<phi>"
| implies_e1:
  "consistent_run \<Gamma>' \<Longrightarrow>
   \<Gamma>' = K\<^sub>1 \<not>\<Up> n # \<Gamma> \<Longrightarrow>
   \<Gamma>, n \<turnstile> (K\<^sub>1 implies K\<^sub>2) # \<psi> \<triangleright> \<phi>
   \<hookrightarrow> \<Gamma>', n \<turnstile> \<psi> \<triangleright> \<phi>"
| implies_e2:
  "consistent_run \<Gamma>' \<Longrightarrow>
   \<Gamma>' = (K\<^sub>1 \<Up> n) # (K\<^sub>2 \<Up> n) # \<Gamma> \<Longrightarrow>
   \<Gamma>, n \<turnstile> (K\<^sub>1 implies K\<^sub>2) # \<psi> \<triangleright> \<phi>
   \<hookrightarrow> \<Gamma>', n \<turnstile> \<psi> \<triangleright> \<phi>"
| timedelayed_e1:
  "consistent_run \<Gamma>' \<Longrightarrow>
   \<Gamma>' = (K\<^sub>1 \<not>\<Up> n) # \<Gamma> \<Longrightarrow>
   \<Gamma>, n \<turnstile> (K\<^sub>1 time-delayed by \<delta>\<tau> on K\<^sub>2 implies K\<^sub>3) # \<psi> \<triangleright> \<phi>
   \<hookrightarrow> \<Gamma>', n \<turnstile> \<psi> \<triangleright> \<phi>"
| timedelayed_e2:
  "consistent_run \<Gamma>' \<Longrightarrow>
   \<Gamma>' = (K\<^sub>1 \<Up> n) # \<Gamma> \<Longrightarrow>
   \<Gamma>, n \<turnstile> (K\<^sub>1 time-delayed by \<delta>\<tau> on K\<^sub>2 implies K\<^sub>3) # \<psi> \<triangleright> \<phi>
   \<hookrightarrow> \<Gamma>', n \<turnstile> \<psi> \<triangleright> (K\<^sub>3 sporadic \<lfloor>\<tau>\<^sub>v\<^sub>a\<^sub>r(K\<^sub>2, n) \<oplus> \<delta>\<tau>\<rfloor> on K\<^sub>2) # \<phi>"

abbreviation operational_semantics_step'
  :: "(system \<times> instant_index \<times> TESL_formula \<times> TESL_formula) rel" ("\<hookrightarrow>") where
  "\<hookrightarrow> \<equiv> { ((\<Gamma>\<^sub>1, n\<^sub>1, \<psi>\<^sub>1, \<phi>\<^sub>1), (\<Gamma>\<^sub>2, n\<^sub>2, \<psi>\<^sub>2, \<phi>\<^sub>2)).
              \<Gamma>\<^sub>1, n\<^sub>1 \<turnstile> \<psi>\<^sub>1 \<triangleright> \<phi>\<^sub>1 \<hookrightarrow> \<Gamma>\<^sub>2, n\<^sub>2 \<turnstile> \<psi>\<^sub>2 \<triangleright> \<phi>\<^sub>2 }"

abbreviation operational_semantics_simulation_step
  :: "(system \<times> instant_index \<times> TESL_formula \<times> TESL_formula) rel" ("\<hookrightarrow>\<^sub>\<nabla>") where
  "\<hookrightarrow>\<^sub>\<nabla> \<equiv> { ((\<Gamma>\<^sub>1, n\<^sub>1, \<psi>, \<phi>\<^sub>1), (\<Gamma>\<^sub>2, n\<^sub>2, \<psi>, \<phi>\<^sub>2)).
                \<psi> = []
              \<and> (\<Gamma>\<^sub>1, n\<^sub>1 \<turnstile> \<psi> \<triangleright> \<phi>\<^sub>1, \<Gamma>\<^sub>2, n\<^sub>2 \<turnstile> \<psi> \<triangleright> \<phi>\<^sub>2) \<in> \<hookrightarrow>\<^sup>+
              \<and> consistent_run \<Gamma>\<^sub>1
              \<and> consistent_run \<Gamma>\<^sub>2}"

(* Example of one simulation step: introduction rule then one elimination *)
(* Note that \<hookrightarrow>\<^sub>\<nabla> is unfolded as necessary as it is to eliminate \<psi>-formulae *)
lemma "([], 0        \<turnstile> [] \<triangleright> [H\<^sub>1 sporadic \<tau>\<^sub>i\<^sub>n\<^sub>t 0, H\<^sub>1 implies H\<^sub>2],
         \<Gamma>, 1 \<turnstile> [] \<triangleright> \<Phi>)
         \<in> \<hookrightarrow>\<^sub>\<nabla>"
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
  finite_SAT_ax: "\<Gamma>, n \<turnstile> \<psi> \<triangleright> \<phi> \<hookrightarrow> \<Gamma>, n \<turnstile> \<psi> \<triangleright> \<phi> \<Longrightarrow>
                   \<TTurnstile> \<Gamma>, n \<turnstile> \<psi> \<triangleright> \<phi>"
| finite_SAT_i: "\<Gamma>\<^sub>1, n\<^sub>1 \<turnstile> \<psi>\<^sub>1 \<triangleright> \<phi>\<^sub>1 \<hookrightarrow> \<Gamma>\<^sub>2, n\<^sub>2 \<turnstile> \<psi>\<^sub>2 \<triangleright> \<phi>\<^sub>2 \<Longrightarrow>
                   \<TTurnstile> \<Gamma>\<^sub>2, n\<^sub>2 \<turnstile> \<psi>\<^sub>2 \<triangleright> \<phi>\<^sub>2 \<Longrightarrow>
                   \<TTurnstile> \<Gamma>\<^sub>1, n\<^sub>1 \<turnstile> \<psi>\<^sub>1 \<triangleright> \<phi>\<^sub>1"

end