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
      _ sporadic _  \<Rightarrow> False
    | _ sporadic _ on _ \<Rightarrow> False
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
  "consistent_run \<Gamma> \<Longrightarrow>
   \<Gamma>, Suc n \<Turnstile> \<phi> \<triangleright> NoSporadic \<phi> \<Longrightarrow>
   \<Gamma>, n \<Turnstile> [] \<triangleright> \<phi>"
  (* Elimination of `sporadic` *)
| sporadic_e1:
  "consistent_run \<Gamma> \<Longrightarrow>
   \<Gamma>, n \<Turnstile> \<psi> \<triangleright> (K sporadic \<tau>) # \<phi> \<Longrightarrow>
   \<Gamma>, n \<Turnstile> (K sporadic \<tau>) # \<psi> \<triangleright> \<phi>"
| sporadic_e2:
  "consistent_run ((K \<Up> n) # (K \<Down> n, \<lfloor>\<tau>\<rfloor>\<^sub>c\<^sub>s\<^sub>t) # \<Gamma>) \<Longrightarrow>
   (K \<Up> n) # (K \<Down> n, \<lfloor>\<tau>\<rfloor>\<^sub>c\<^sub>s\<^sub>t) # \<Gamma>, n \<Turnstile> \<psi> \<triangleright> \<phi> \<Longrightarrow>
   \<Gamma>, n \<Turnstile> (K sporadic \<tau>) # \<psi> \<triangleright> \<phi>"
  (* Elimination of `sporadic on` *)
| sporadic_on_e1:
  "consistent_run \<Gamma> \<Longrightarrow>
   \<Gamma>, n \<Turnstile> \<psi> \<triangleright> (K\<^sub>1 sporadic \<tau> on K\<^sub>2) # \<phi> \<Longrightarrow>
   \<Gamma>, n \<Turnstile> (K\<^sub>1 sporadic \<tau> on K\<^sub>2) # \<psi> \<triangleright> \<phi>"
| sporadic_on_e2:
  "consistent_run ((K\<^sub>2 \<Up> n) # (K\<^sub>1 \<Down> n, \<tau>) # \<Gamma>) \<Longrightarrow>
   (K\<^sub>2 \<Up> n) # (K\<^sub>1 \<Down> n, \<tau>) # \<Gamma>, n \<Turnstile> \<psi> \<triangleright> \<phi> \<Longrightarrow>
   \<Gamma>, n \<Turnstile> (K\<^sub>1 sporadic \<tau> on K\<^sub>2) # \<psi> \<triangleright> \<phi>"
  (* Elimination of `tag relation` *)
| tagrel_e:
  "consistent_run ((\<tau>\<^sub>v\<^sub>a\<^sub>r(K\<^sub>1, n) \<doteq> \<alpha> * \<tau>\<^sub>v\<^sub>a\<^sub>r(K\<^sub>2, n) + \<beta>) # \<Gamma>) \<Longrightarrow>
   (\<tau>\<^sub>v\<^sub>a\<^sub>r(K\<^sub>1, n) \<doteq> \<alpha> * \<tau>\<^sub>v\<^sub>a\<^sub>r(K\<^sub>2, n) + \<beta>) # \<Gamma>, n \<Turnstile> \<psi> \<triangleright> \<phi> \<Longrightarrow>
   \<Gamma>, n \<Turnstile> (tag-relation K\<^sub>1 = \<alpha> * K\<^sub>2 + \<beta>) # \<psi> \<triangleright> \<phi>"
  (* Elimination of `implies` *)
| implies_e1:
  "consistent_run ((K\<^sub>1 \<not>\<Up> n) # \<Gamma>) \<Longrightarrow>
   K\<^sub>1 \<not>\<Up> n # \<Gamma>, n \<Turnstile> \<psi> \<triangleright> \<phi> \<Longrightarrow>
   \<Gamma>, n \<Turnstile> (K\<^sub>1 implies K\<^sub>2) # \<psi> \<triangleright> \<phi>"
| implies_e2:
  "consistent_run ((K\<^sub>1 \<Up> n) # (K\<^sub>2 \<Up> n) # \<Gamma>) \<Longrightarrow>
   (K\<^sub>1 \<Up> n) # (K\<^sub>2 \<Up> n) # \<Gamma>, n \<Turnstile> \<psi> \<triangleright> \<phi> \<Longrightarrow>
   \<Gamma>, n \<Turnstile> (K\<^sub>1 implies K\<^sub>2) # \<psi> \<triangleright> \<phi>"
  (* Elimination of `time delayed by` *)
| timedelayed_e1:
  "consistent_run ((K\<^sub>1 \<not>\<Up> n) # \<Gamma>) \<Longrightarrow>
   (K\<^sub>1 \<not>\<Up> n) # \<Gamma>, n \<Turnstile> \<psi> \<triangleright> \<phi> \<Longrightarrow>
   \<Gamma>, n \<Turnstile> (K\<^sub>1 time-delayed by \<delta>\<tau> on K\<^sub>2 implies K\<^sub>3) # \<psi> \<triangleright> \<phi>"
| timedelayed_e2:
  "consistent_run ((K\<^sub>1 \<Up> n) # (K\<^sub>2 \<Down> n, \<lfloor>\<tau>\<^sub>v\<^sub>a\<^sub>r(K\<^sub>2, n)\<rfloor>\<^sub>v\<^sub>a\<^sub>r) # \<Gamma>) \<Longrightarrow>
   (K\<^sub>1 \<Up> n) # (K\<^sub>2 \<Down> n, \<lfloor>\<tau>\<^sub>v\<^sub>a\<^sub>r(K\<^sub>2, n)\<rfloor>\<^sub>v\<^sub>a\<^sub>r) # \<Gamma>, n \<Turnstile> \<psi> \<triangleright> (K\<^sub>3 sporadic \<lfloor>\<lfloor>\<tau>\<^sub>v\<^sub>a\<^sub>r(K\<^sub>2, n)\<rfloor>\<^sub>v\<^sub>a\<^sub>r + \<lfloor>\<delta>\<tau>\<rfloor>\<^sub>c\<^sub>s\<^sub>t\<rfloor> on K\<^sub>2) # \<phi> \<Longrightarrow>
   \<Gamma>, n \<Turnstile> (K\<^sub>1 time-delayed by \<delta>\<tau> on K\<^sub>2 implies K\<^sub>3) # \<psi> \<triangleright> \<phi>"

named_theorems init
declare instant_i [init]

named_theorems elims
declare sporadic_e2 [elims]
declare sporadic_e1 [elims]
declare implies_e2 [elims]
declare implies_e1 [elims]

method heron_next_step =
  rule init, auto, solve_run_witness, (rule elims, solve_run_witness)+

method heron_end =
  rule simulation_end, simp, solve_run_witness'


end