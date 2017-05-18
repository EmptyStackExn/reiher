theory Engine
imports
    Main
    "TESL"
    "RunConsistency"
    "$ISABELLE_HOME/src/HOL/Eisbach/Eisbach_Tools" 

begin
text{* Operational steps *}

abbreviation NoSporadic :: "TESL_formula \<Rightarrow> TESL_formula" where 
  "NoSporadic f \<equiv> (List.filter (\<lambda>f\<^sub>a\<^sub>t\<^sub>o\<^sub>m. case f\<^sub>a\<^sub>t\<^sub>o\<^sub>m of
      \<odot> _  \<Rightarrow> False
    | \<Odot> _ \<Rightarrow> False
    | _ \<Rightarrow> True) f)"
  
(* Operational rules *)
inductive kern_step
  :: "system \<Rightarrow> instant_index \<Rightarrow> TESL_formula \<Rightarrow> TESL_formula \<Rightarrow> bool"
  ("_, _ \<Turnstile> _ \<triangleright> _" 50) where
  simulation_end:
  "set (NoSporadic \<phi>) = set \<phi> \<Longrightarrow>
   consistent_run \<Gamma> \<Longrightarrow>
   \<Gamma>, n \<Turnstile> [] \<triangleright> \<phi>"
  (* Instant introduction *)
| instant_i:
  "\<Gamma>, Suc n \<Turnstile> \<phi> \<triangleright> NoSporadic \<phi> \<Longrightarrow>
   \<Gamma>, n \<Turnstile> [] \<triangleright> \<phi>"
  (* Elimination of `sporadic` *)
| sporadic_e1:
  "\<Gamma>, n \<Turnstile> \<psi> \<triangleright> \<odot> (K, \<tau>) # \<phi> \<Longrightarrow>
   \<Gamma>, n \<Turnstile> \<odot> (K, \<tau>) # \<psi> \<triangleright> \<phi>"
| sporadic_e2:
  "\<Up>(K, n) # \<Down>(K, n, \<tau>) # \<Gamma>, n \<Turnstile> \<psi> \<triangleright> \<phi> \<Longrightarrow>
   \<Gamma>, n \<Turnstile> \<odot> (K, \<tau>) # \<psi> \<triangleright> \<phi>"
  (* Elimination of `sporadic on` *)
| sporadic_on_e1:
  "\<Gamma>, n \<Turnstile> \<psi> \<triangleright> \<Odot> (K\<^sub>1, \<tau>, K\<^sub>2) # \<phi> \<Longrightarrow>
   \<Gamma>, n \<Turnstile> \<Odot> (K\<^sub>1, \<tau>, K\<^sub>2) # \<psi> \<triangleright> \<phi>"
| sporadic_on_e2:
  "\<Up>(K\<^sub>2, n) # \<Down>(K\<^sub>1, n, \<tau>) # \<Gamma>, n \<Turnstile> \<psi> \<triangleright> \<phi> \<Longrightarrow>
   \<Gamma>, n \<Turnstile> \<Odot> (K\<^sub>1, \<tau>, K\<^sub>2) # \<psi> \<triangleright> \<phi>"
  (* Elimination of `tag relation` *)
| tagrel_e:
  "\<doteq>(\<tau>\<^sub>v\<^sub>a\<^sub>r(K\<^sub>1, n), \<alpha>, \<tau>\<^sub>v\<^sub>a\<^sub>r(K\<^sub>2, n), \<beta>) # \<Gamma>, n \<Turnstile> \<psi> \<triangleright> \<phi> \<Longrightarrow>
   \<Gamma>, n \<Turnstile> \<rightleftharpoons>\<^sub>t\<^sub>a\<^sub>g\<^sub>r\<^sub>e\<^sub>l (K\<^sub>1, \<alpha>, K\<^sub>2, \<beta>) # \<psi> \<triangleright> \<phi>"
  (* Elimination of `implies` *)
| implies_e1:
  "\<not>\<Up>(K\<^sub>1, n) # \<Gamma>, n \<Turnstile> \<psi> \<triangleright> \<phi> \<Longrightarrow>
   \<Gamma>, n \<Turnstile> (K\<^sub>1 \<rightarrow>\<^sub>i\<^sub>m\<^sub>p\<^sub>l\<^sub>i\<^sub>e\<^sub>s K\<^sub>2) # \<psi> \<triangleright> \<phi>"
| implies_e2:
  "\<Up>(K\<^sub>1, n) # \<Up>(K\<^sub>2, n) # \<Gamma>, n \<Turnstile> \<psi> \<triangleright> \<phi> \<Longrightarrow>
   \<Gamma>, n \<Turnstile> (K\<^sub>1 \<rightarrow>\<^sub>i\<^sub>m\<^sub>p\<^sub>l\<^sub>i\<^sub>e\<^sub>s K\<^sub>2) # \<psi> \<triangleright> \<phi>"
  (* Elimination of `time delayed by` *)
| timedelayed_e1:
  "\<not>\<Up>(K\<^sub>1, n) # \<Gamma>, n \<Turnstile> \<psi> \<triangleright> \<phi> \<Longrightarrow>
   \<Gamma>, n \<Turnstile> \<rightarrow>\<^sub>t\<^sub>i\<^sub>m\<^sub>e\<^sub>d\<^sub>e\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>d (K\<^sub>1, \<delta>\<tau>, K\<^sub>2, K\<^sub>3) # \<psi> \<triangleright> \<phi>"
| timedelayed_e2:
  "\<Up>(K\<^sub>1, n) # \<Down>(K\<^sub>2, n, \<tau>\<^sub>v\<^sub>a\<^sub>r(K\<^sub>2, n)) # \<Gamma>, n \<Turnstile> \<psi> \<triangleright> \<Odot>(K\<^sub>3, \<tau>\<^sub>v\<^sub>a\<^sub>r(K\<^sub>2, n), K\<^sub>2) # \<phi> \<Longrightarrow>
   \<Gamma>, n \<Turnstile> \<rightarrow>\<^sub>t\<^sub>i\<^sub>m\<^sub>e\<^sub>d\<^sub>e\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>d (K\<^sub>1, \<delta>\<tau>, K\<^sub>2, K\<^sub>3) # \<psi> \<triangleright> \<phi>"

(* Running on a small example:
  H1 sporadic 1, 2
  H1 implies H2
*)
lemma small_example:
  shows "[], 0 \<Turnstile> [] \<triangleright> [
    \<odot>(\<lceil>''H1''\<rceil>, \<tau>\<^sub>i\<^sub>n\<^sub>t 1),
    \<odot>(\<lceil>''H1''\<rceil>, \<tau>\<^sub>i\<^sub>n\<^sub>t 2),
    \<lceil>''H1''\<rceil> \<rightarrow>\<^sub>i\<^sub>m\<^sub>p\<^sub>l\<^sub>i\<^sub>e\<^sub>s \<lceil>''H2''\<rceil>
  ]"
apply (rule instant_i, auto)
  apply (rule sporadic_e2)
  apply (rule sporadic_e1)
  apply (rule implies_e2)
apply (rule instant_i, auto)
  apply (rule sporadic_e2)
  apply (rule implies_e2)
apply (rule simulation_end, simp)
unfolding consistent_run_def
by (rule_tac x="\<langle>\<langle> [\<Up> (\<lceil> ''H1'' \<rceil>, Suc (Suc 0)), \<Up> (\<lceil> ''H2'' \<rceil>, Suc (Suc 0)), \<Up> (\<lceil> ''H1'' \<rceil>, Suc (Suc 0)),
              \<Down> (\<lceil> ''H1'' \<rceil>, Suc (Suc 0), \<tau>\<^sub>i\<^sub>n\<^sub>t 2), \<Up> (\<lceil> ''H1'' \<rceil>, Suc 0), \<Up> (\<lceil> ''H2'' \<rceil>, Suc 0),
              \<Up> (\<lceil> ''H1'' \<rceil>, Suc 0), \<Down> (\<lceil> ''H1'' \<rceil>, Suc 0, \<tau>\<^sub>i\<^sub>n\<^sub>t 1)] \<rangle>\<rangle>" in exI,
    simp)

end