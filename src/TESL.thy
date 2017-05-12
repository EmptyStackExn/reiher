theory TESL
imports Main

begin

text {* Defining as follows the syntax of primitives to describe symbolic runs *}

datatype clock = Clk "string"        ("\<lceil> _ \<rceil>")
type_synonym instant_index = "nat"

datatype tag =
    Unit                              ("\<tau>\<^sub>u\<^sub>n\<^sub>i\<^sub>t")
  | Integer "int"                     ("\<tau>\<^sub>i\<^sub>n\<^sub>t")
  | Schematic "clock * instant_index" ("\<tau>\<^sub>v\<^sub>a\<^sub>r")
  | Add       "tag * tag"

datatype constr =
    Timestamp "clock * instant_index * tag" ("\<Down>")
  | Ticks     "clock * instant_index"       ("\<Up>")
  | NotTicks  "clock * instant_index"       ("\<not>\<Up>")
  | Affine    "tag * tag * tag * tag"       ("\<propto>")

type_synonym system = "constr list"

text{* Define as follows the syntax of TESL *}

datatype TESL_atomic =
    Sporadic       "clock * tag"                 ("\<odot>")
  | TagRelation    "clock * tag * clock * tag"   ("\<rightleftharpoons>")
  | Implies        "clock * clock"               ("\<rightarrow>\<^sub>i\<^sub>m\<^sub>p\<^sub>l\<^sub>i\<^sub>e\<^sub>s")
  | TimeDelayedBy  "clock * tag * clock * clock" ("\<rightarrow>\<^sub>t\<^sub>i\<^sub>m\<^sub>e\<^sub>d\<^sub>e\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>d")
  | SporadicOn     "clock * tag * clock"         ("\<Odot>")

type_synonym TESL_formula = "TESL_atomic list"

(* This type is slightly different from which originally implemented
   Follows the intuition: past [\<Gamma>], current index [n], present [\<psi>], future [\<phi>]
*)
type_synonym TESL_ARS_conf = "system * instant_index * TESL_formula * TESL_formula"

abbreviation NoSporadic :: "TESL_formula \<Rightarrow> TESL_formula" where 
  "NoSporadic f \<equiv> (List.filter (\<lambda>f\<^sub>a\<^sub>t\<^sub>o\<^sub>m. case f\<^sub>a\<^sub>t\<^sub>o\<^sub>m of
      Sporadic _   \<Rightarrow> False
    | SporadicOn _ \<Rightarrow> False
    | _ \<Rightarrow> True) f)"

text{* Operational steps *}

inductive kern_step
  :: "system \<Rightarrow> instant_index \<Rightarrow> TESL_formula \<Rightarrow> TESL_formula \<Rightarrow> bool"
  ("_, _ \<Turnstile> _, _" 50) where
  simulation_end:
  "set (NoSporadic \<phi>) = set \<phi> \<Longrightarrow>
   \<Gamma>, n \<Turnstile> [], \<phi>"
  (* Instant introduction *)
| instant_i:
  "\<Gamma>, Suc n \<Turnstile> \<phi>, NoSporadic \<phi> \<Longrightarrow>
   \<Gamma>, n \<Turnstile> [], \<phi>"
  (* Elimination of `sporadic` *)
| sporadic_e1:
  "\<Gamma>, n \<Turnstile> \<psi>, \<odot> (K, \<tau>) # \<phi> \<Longrightarrow>
   \<Gamma>, n \<Turnstile> \<odot> (K, \<tau>) # \<psi>, \<phi>"
| sporadic_e2:
  "\<Up>(K, n) # \<Down>(K, n, \<tau>) # \<Gamma>, n \<Turnstile> \<psi>, \<phi> \<Longrightarrow>
   \<Gamma>, n \<Turnstile> \<odot> (K, \<tau>) # \<psi>, \<phi>"
  (* Elimination of `sporadic on` *)
| sporadic_on_e1:
  "\<Gamma>, n \<Turnstile> \<psi>, \<Odot> (K\<^sub>1, \<tau>, K\<^sub>2) # \<phi> \<Longrightarrow>
   \<Gamma>, n \<Turnstile> \<Odot> (K\<^sub>1, \<tau>, K\<^sub>2) # \<psi>, \<phi>"
| sporadic_on_e2:
  "\<Up>(K\<^sub>2, n) # \<Down>(K\<^sub>1, n, \<tau>) # \<Gamma>, n \<Turnstile> \<psi>, \<phi> \<Longrightarrow>
   \<Gamma>, n \<Turnstile> \<Odot> (K\<^sub>1, \<tau>, K\<^sub>2) # \<psi>, \<phi>"
  (* Elimination of `tag relation` *)
| tagrel_e:
  "\<propto>(\<tau>\<^sub>v\<^sub>a\<^sub>r(K\<^sub>1, n), \<alpha>, \<tau>\<^sub>v\<^sub>a\<^sub>r(K\<^sub>2, n), \<beta>) # \<Gamma>, n \<Turnstile> \<psi>, \<phi> \<Longrightarrow>
   \<Gamma>, n \<Turnstile> \<rightleftharpoons> (K\<^sub>1, \<alpha>, K\<^sub>2, \<beta>) # \<psi>, \<phi>"
  (* Elimination of `implies` *)
| implies_e1:
  "\<not>\<Up>(K\<^sub>1, n) # \<Gamma>, n \<Turnstile> \<psi>, \<phi> \<Longrightarrow>
   \<Gamma>, n \<Turnstile> \<rightarrow>\<^sub>i\<^sub>m\<^sub>p\<^sub>l\<^sub>i\<^sub>e\<^sub>s (K\<^sub>1, K\<^sub>2) # \<psi>, \<phi>"
| implies_e2:
  "\<Up>(K\<^sub>1, n) # \<Up>(K\<^sub>2, n) # \<Gamma>, n \<Turnstile> \<psi>, \<phi> \<Longrightarrow>
   \<Gamma>, n \<Turnstile> \<rightarrow>\<^sub>i\<^sub>m\<^sub>p\<^sub>l\<^sub>i\<^sub>e\<^sub>s (K\<^sub>1, K\<^sub>2) # \<psi>, \<phi>"
  (* Elimination of `time delayed by` *)
| timedelayed_e1:
  "\<not>\<Up>(K\<^sub>1, n) # \<Gamma>, n \<Turnstile> \<psi>, \<phi> \<Longrightarrow>
   \<Gamma>, n \<Turnstile> \<rightarrow>\<^sub>t\<^sub>i\<^sub>m\<^sub>e\<^sub>d\<^sub>e\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>d (K\<^sub>1, \<delta>\<tau>, K\<^sub>2, K\<^sub>3) # \<psi>, \<phi>"
| timedelayed_e2:
  "\<Up>(K\<^sub>1, n) # \<Down>(K\<^sub>2, n, \<tau>\<^sub>v\<^sub>a\<^sub>r(K\<^sub>2, n)) # \<Gamma>, n \<Turnstile> \<psi>, \<Odot>(K\<^sub>3, \<tau>\<^sub>v\<^sub>a\<^sub>r(K\<^sub>2, n), K\<^sub>2) # \<phi> \<Longrightarrow>
   \<Gamma>, n \<Turnstile> \<rightarrow>\<^sub>t\<^sub>i\<^sub>m\<^sub>e\<^sub>d\<^sub>e\<^sub>l\<^sub>a\<^sub>y\<^sub>e\<^sub>d (K\<^sub>1, \<delta>\<tau>, K\<^sub>2, K\<^sub>3) # \<psi>, \<phi>"

(* Running on a small example:
  H1 sporadic 1, 2
  H1 implies H2
*)
lemma small_example:
  shows "[], 0 \<Turnstile> [], [
    \<odot>(\<lceil>''H1''\<rceil>, \<tau>\<^sub>i\<^sub>n\<^sub>t 1),
    \<odot>(\<lceil>''H1''\<rceil>, \<tau>\<^sub>i\<^sub>n\<^sub>t 2),
    \<rightarrow>\<^sub>i\<^sub>m\<^sub>p\<^sub>l\<^sub>i\<^sub>e\<^sub>s(\<lceil>''H1''\<rceil>, \<lceil>''H2''\<rceil>)
  ]"
apply (rule instant_i, auto)
  apply (rule sporadic_e2)
  apply (rule sporadic_e1)
  apply (rule implies_e2)
apply (rule instant_i, auto)
  apply (rule sporadic_e2)
  apply (rule implies_e2)
by (rule simulation_end, auto)

end