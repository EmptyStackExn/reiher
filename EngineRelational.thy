theory EngineRelational
imports
    "TESL"
    "Run"

begin

abbreviation uncurry_conf
  :: "system \<Rightarrow> instant_index \<Rightarrow> TESL_formula \<Rightarrow> TESL_formula \<Rightarrow> (system \<times> instant_index \<times> TESL_formula \<times> TESL_formula)" ("_, _ \<turnstile> _ \<triangleright> _" 50) where
  "\<Gamma>, n \<turnstile> \<psi> \<triangleright> \<phi> \<equiv> (\<Gamma>, n, \<psi>, \<phi>)"

(* Impossible to reason on operational semantics with current formalism *)
(* Another way to express it? *)
inductive explicit_operational
  :: "(system \<times> instant_index \<times> TESL_formula \<times> TESL_formula) \<Rightarrow> (system \<times> instant_index \<times> TESL_formula \<times> TESL_formula) \<Rightarrow> bool" ("_ \<hookrightarrow> _" 50) where
  simulation_end_expl:
  "set (NoSporadic \<phi>) = set \<phi> \<Longrightarrow>
   consistent_run \<Gamma> \<Longrightarrow>
   \<Gamma>, n \<turnstile> \<psi> \<triangleright> \<phi> \<hookrightarrow> \<Gamma>, n \<turnstile> \<psi> \<triangleright> \<phi>"
| instant_i_expl:
  "consistent_run \<Gamma> \<Longrightarrow>
   \<Gamma>, n \<turnstile> [] \<triangleright> \<phi> \<hookrightarrow> \<Gamma>, Suc n \<turnstile> \<phi> \<triangleright> NoSporadic \<phi>"
| sporadic_e1_expl:
  "consistent_run \<Gamma> \<Longrightarrow>
   \<Gamma>, n \<turnstile> (K sporadic \<tau>) # \<psi> \<triangleright> \<phi> \<hookrightarrow> \<Gamma>, n \<turnstile> \<psi> \<triangleright> (K sporadic \<tau>) # \<phi>"
| sporadic_e2_expl:
  "consistent_run \<Gamma>' \<Longrightarrow>
   \<Gamma>' = (K \<Up> n) # (K \<Down> n @ \<lfloor>\<tau>\<rfloor>) # \<Gamma> \<Longrightarrow>
   \<Gamma>, n \<turnstile> (K sporadic \<tau>) # \<psi> \<triangleright> \<phi> \<hookrightarrow> \<Gamma>', n \<turnstile> \<psi> \<triangleright> \<phi>"
| sporadic_on_e1_expl:
  "consistent_run \<Gamma> \<Longrightarrow>
   \<Gamma>, n \<turnstile> (K\<^sub>1 sporadic \<tau> on K\<^sub>2) # \<psi> \<triangleright> \<phi> \<hookrightarrow> \<Gamma>, n \<turnstile> \<psi> \<triangleright> (K\<^sub>1 sporadic \<tau> on K\<^sub>2) # \<phi>"
| sporadic_on_e2_expl:
  "consistent_run \<Gamma>' \<Longrightarrow>
   \<Gamma>' = (K\<^sub>2 \<Up> n) # (K\<^sub>1 \<Down> n @ \<tau>) # \<Gamma> \<Longrightarrow>
   \<Gamma>, n \<turnstile> (K\<^sub>1 sporadic \<tau> on K\<^sub>2) # \<psi> \<triangleright> \<phi> \<hookrightarrow> \<Gamma>, n \<turnstile> \<psi> \<triangleright> \<phi>"
| tagrel_e_expl:
  "consistent_run \<Gamma>' \<Longrightarrow>
   \<Gamma>' = (\<tau>\<^sub>v\<^sub>a\<^sub>r(K\<^sub>1, n) \<doteq> \<alpha> * \<tau>\<^sub>v\<^sub>a\<^sub>r(K\<^sub>2, n) + \<beta>) # \<Gamma> \<Longrightarrow>
   \<Gamma>, n \<turnstile> (tag-relation K\<^sub>1 = \<alpha> * K\<^sub>2 + \<beta>) # \<psi> \<triangleright> \<phi> \<hookrightarrow> \<Gamma>', n \<turnstile> \<psi> \<triangleright> \<phi>"
| implies_e1_expl:
  "consistent_run (K\<^sub>1 \<not>\<Up> n # \<Gamma>) \<Longrightarrow>
   \<Gamma>' = K\<^sub>1 \<not>\<Up> n # \<Gamma> \<Longrightarrow>
   \<Gamma>, n \<turnstile> (K\<^sub>1 implies K\<^sub>2) # \<psi> \<triangleright> \<phi> \<hookrightarrow> \<Gamma>', n \<turnstile> \<psi> \<triangleright> \<phi>"
| implies_e2_expl:
  "consistent_run (K\<^sub>1 \<not>\<Up> n # \<Gamma>) \<Longrightarrow>
   \<Gamma>' = (K\<^sub>1 \<Up> n) # (K\<^sub>2 \<Up> n) # \<Gamma> \<Longrightarrow>
   \<Gamma>, n \<turnstile> (K\<^sub>1 implies K\<^sub>2) # \<psi> \<triangleright> \<phi> \<hookrightarrow> \<Gamma>', n \<turnstile> \<psi> \<triangleright> \<phi>"
| timedelayed_e1:
  "consistent_run \<Gamma>' \<Longrightarrow>
   \<Gamma>' = (K\<^sub>1 \<not>\<Up> n) # \<Gamma> \<Longrightarrow>
   \<Gamma>, n \<turnstile> (K\<^sub>1 time-delayed by \<delta>\<tau> on K\<^sub>2 implies K\<^sub>3) # \<psi> \<triangleright> \<phi> \<hookrightarrow> \<Gamma>', n \<turnstile> \<psi> \<triangleright> \<phi>"
| timedelayed_e2:
  "consistent_run \<Gamma>' \<Longrightarrow>
   \<Gamma>' = (K\<^sub>1 \<Up> n) # \<Gamma> \<Longrightarrow>
   \<Gamma>, n \<turnstile> (K\<^sub>1 time-delayed by \<delta>\<tau> on K\<^sub>2 implies K\<^sub>3) # \<psi> \<triangleright> \<phi> \<hookrightarrow> \<Gamma>', n \<turnstile> \<psi> \<triangleright> (K\<^sub>3 sporadic \<lfloor>\<tau>\<^sub>v\<^sub>a\<^sub>r(K\<^sub>2, n) \<oplus> \<delta>\<tau>\<rfloor> on K\<^sub>2) # \<phi>"


abbreviation explicit_operational_step
  :: "(system \<times> instant_index \<times> TESL_formula \<times> TESL_formula) rel" ("\<hookrightarrow>\<^sub>x") where
  "\<hookrightarrow>\<^sub>x \<equiv> { ((\<Gamma>\<^sub>1, n\<^sub>1, \<psi>\<^sub>1, \<phi>\<^sub>1), (\<Gamma>\<^sub>2, n\<^sub>2, \<psi>\<^sub>2, \<phi>\<^sub>2)).
              \<Gamma>\<^sub>1, n\<^sub>1 \<turnstile> \<psi>\<^sub>1 \<triangleright> \<phi>\<^sub>1 \<hookrightarrow> \<Gamma>\<^sub>2, n\<^sub>2 \<turnstile> \<psi>\<^sub>2 \<triangleright> \<phi>\<^sub>2 }"

(* Example by eliminating the implies operator ONCE *)
lemma "([], 0        \<turnstile> [H\<^sub>1 implies H\<^sub>2] \<triangleright> [],
         [H\<^sub>1 \<not>\<Up> 0], 0 \<turnstile> []              \<triangleright> [])
         \<in> \<hookrightarrow>\<^sub>x"
apply simp
apply (rule implies_e1_expl) apply (auto+) sorry (* OK *)

(* Now trying with the transitive closure to eliminate TWICE*)
lemma "([], 0                 \<turnstile> [H\<^sub>1 implies H\<^sub>2, H\<^sub>1 implies H\<^sub>2] \<triangleright> [],
         [H\<^sub>1 \<not>\<Up> 0, H\<^sub>1 \<not>\<Up> 0], 0 \<turnstile> []                            \<triangleright> [])
         \<in> \<hookrightarrow>\<^sub>x\<^sup>+"
apply (rule trancl_into_trancl)
apply (rule r_into_trancl)
apply simp
apply (rule implies_e1_expl) apply (auto+) defer 1
apply (rule implies_e1_expl) apply (auto+)
 sorry (* OK *)

end
