theory RunConsistency
imports
    Main
    "TESL"
    "$ISABELLE_HOME/src/HOL/Eisbach/Eisbach_Tools" 

begin

abbreviation is_a_valuation :: "(tag \<Rightarrow> tag) \<Rightarrow> bool" where
  "is_a_valuation \<eta> \<equiv>
  (* A constant evaluates in itself *)
  (\<forall>\<tau>::tag. is_concrete \<tau> \<longrightarrow> (\<eta> \<tau> = \<tau>)) \<and>
  (* A valuation only gives concrete tags *)
  (\<forall>\<tau>::tag. is_concrete (\<eta> \<tau>))"

text \<open> A run is a time frame and tag variable valuation \<close>
  
(* type_synonym tag_eval = "tag \<Rightarrow> tag" *)
typedef (overloaded) tag_eval = "{ \<eta> :: tag \<Rightarrow> tag. is_a_valuation \<eta> }"
  proof -
    have "(\<lambda>x. case x of Unit \<Rightarrow> x | Integer _ \<Rightarrow> x | Add _ \<Rightarrow> Unit | Schematic _ \<Rightarrow> Unit) \<in> {\<eta>. is_a_valuation \<eta>}"
      by (simp, metis tag.case(1) tag.case(2) tag.case(3) tag.case(4) tag.exhaust)
    then show ?thesis by auto
  qed
type_synonym instant = "clock \<Rightarrow> (bool * tag)"
type_synonym time_frame = "nat \<Rightarrow> instant"
type_synonym run = "time_frame * tag_eval"

abbreviation hamlet where "hamlet \<equiv> fst"
abbreviation time where "time \<equiv> snd"

fun symbolic_run_interpretation_primitive :: "constr \<Rightarrow> run set" ("\<lbrakk>\<lbrakk> _ \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m\<^sub>i\<^sub>t\<^sub>i\<^sub>v\<^sub>e") where
    "\<lbrakk>\<lbrakk> \<Up>(c, n)    \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m\<^sub>i\<^sub>t\<^sub>i\<^sub>v\<^sub>e = { (\<sigma>, \<eta>). hamlet (\<sigma> n c) = True }"
  | "\<lbrakk>\<lbrakk> \<not>\<Up>(c, n)   \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m\<^sub>i\<^sub>t\<^sub>i\<^sub>v\<^sub>e = { (\<sigma>, \<eta>). hamlet (\<sigma> n c) = False }"
  | "\<lbrakk>\<lbrakk> \<Down>(c, n, \<tau>) \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m\<^sub>i\<^sub>t\<^sub>i\<^sub>v\<^sub>e = { (\<sigma>, \<eta>). time (\<sigma> n c) = \<tau> }"
  | "\<lbrakk>\<lbrakk> \<doteq> (\<tau>\<^sub>1, \<alpha>, \<tau>\<^sub>2, \<beta>) \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m\<^sub>i\<^sub>t\<^sub>i\<^sub>v\<^sub>e =
    (* TODO: \<alpha> and \<beta> to build a semi-ring *)
    { (\<sigma>, \<eta>). (Rep_tag_eval \<eta>) \<tau>\<^sub>1 = ((Rep_tag_eval \<eta>) \<tau>\<^sub>2)}" 

fun symbolic_run_interpretation :: "constr list \<Rightarrow> run set" ("\<lbrakk>\<lbrakk> _ \<rbrakk>\<rbrakk>") where
    "\<lbrakk>\<lbrakk> [] \<rbrakk>\<rbrakk>    = { _. True }"
  | "\<lbrakk>\<lbrakk> \<gamma> # \<Gamma> \<rbrakk>\<rbrakk> = \<lbrakk>\<lbrakk> \<gamma> \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m\<^sub>i\<^sub>t\<^sub>i\<^sub>v\<^sub>e \<inter> \<lbrakk>\<lbrakk> \<Gamma> \<rbrakk>\<rbrakk>"

definition consistent_run :: "constr list \<Rightarrow> bool" where 
  "consistent_run \<Gamma> \<equiv> \<exists>\<rho>. \<rho> \<in> \<lbrakk>\<lbrakk> \<Gamma> \<rbrakk>\<rbrakk>"

text \<open> Defining a method for witness construction \<close>

(* Initial states *)
abbreviation initial_time_frame :: "time_frame" ("\<sigma>\<^sub>\<odot>") where
  "\<sigma>\<^sub>\<odot> \<equiv> \<lambda>n c. ((* False *) undefined, undefined)"
abbreviation initial_tag_eval :: "tag_eval" ("\<eta>\<^sub>\<odot>") where
  "\<eta>\<^sub>\<odot> \<equiv> Abs_tag_eval (\<lambda>x. undefined)"
abbreviation initial_run :: "run" ("\<rho>\<^sub>\<odot>") where
  "\<rho>\<^sub>\<odot> \<equiv> (\<sigma>\<^sub>\<odot>, \<eta>\<^sub>\<odot>)"

(* Update functionals *)
fun time_frame_update :: "time_frame \<Rightarrow> constr \<Rightarrow> time_frame" ("_ \<langle> _ \<rangle>\<^sub>t\<^sub>i\<^sub>m\<^sub>e\<^sub>f\<^sub>r\<^sub>a\<^sub>m\<^sub>e") where
    "\<sigma> \<langle> \<Up>(c, n) \<rangle>\<^sub>t\<^sub>i\<^sub>m\<^sub>e\<^sub>f\<^sub>r\<^sub>a\<^sub>m\<^sub>e = (\<lambda>n' c'. if c = c' \<and> n = n' then (True, time (\<sigma> n c)) else \<sigma> n' c')"
  | "\<sigma> \<langle> \<not>\<Up>(c, n) \<rangle>\<^sub>t\<^sub>i\<^sub>m\<^sub>e\<^sub>f\<^sub>r\<^sub>a\<^sub>m\<^sub>e = (\<lambda>n' c'. if c = c' \<and> n = n' then (False, time (\<sigma> n c)) else \<sigma> n' c')"
  | "\<sigma> \<langle> \<Down>(c, n, \<tau>) \<rangle>\<^sub>t\<^sub>i\<^sub>m\<^sub>e\<^sub>f\<^sub>r\<^sub>a\<^sub>m\<^sub>e = (\<lambda>n' c'. if c = c' \<and> n = n' then (hamlet (\<sigma> n c), \<tau>) else \<sigma> n' c')"
  | "\<sigma> \<langle> \<doteq> (\<tau>\<^sub>1, \<alpha>, \<tau>\<^sub>2, \<beta>) \<rangle>\<^sub>t\<^sub>i\<^sub>m\<^sub>e\<^sub>f\<^sub>r\<^sub>a\<^sub>m\<^sub>e = \<sigma>"

fun tag_eval_update :: "tag_eval \<Rightarrow> constr \<Rightarrow> tag_eval" ("_ \<langle> _ \<rangle>\<^sub>t\<^sub>a\<^sub>g\<^sub>e\<^sub>v\<^sub>a\<^sub>l") where
    "\<eta> \<langle> \<Up>(c, n) \<rangle>\<^sub>t\<^sub>a\<^sub>g\<^sub>e\<^sub>v\<^sub>a\<^sub>l = \<eta>"
  | "\<eta> \<langle> \<not>\<Up>(c, n) \<rangle>\<^sub>t\<^sub>a\<^sub>g\<^sub>e\<^sub>v\<^sub>a\<^sub>l = \<eta>"
  | "\<eta> \<langle> \<Down>(c, n, \<tau>) \<rangle>\<^sub>t\<^sub>a\<^sub>g\<^sub>e\<^sub>v\<^sub>a\<^sub>l = Abs_tag_eval (\<lambda>\<tau>'. if \<tau>' = \<tau>\<^sub>v\<^sub>a\<^sub>r(c, n) then \<tau> else (Rep_tag_eval \<eta>) \<tau>')"
  | "\<eta> \<langle> \<doteq> (\<tau>\<^sub>1, \<alpha>, \<tau>\<^sub>2, \<beta>) \<rangle>\<^sub>t\<^sub>a\<^sub>g\<^sub>e\<^sub>v\<^sub>a\<^sub>l = undefined" (* TODO *)

fun run_update :: "run \<Rightarrow> constr \<Rightarrow> run" ("_ \<langle> _ \<rangle>") where
    "(\<sigma>, \<eta>) \<langle> \<gamma> \<rangle> = (\<sigma> \<langle> \<gamma> \<rangle>\<^sub>t\<^sub>i\<^sub>m\<^sub>e\<^sub>f\<^sub>r\<^sub>a\<^sub>m\<^sub>e, \<eta> \<langle> \<gamma> \<rangle>\<^sub>t\<^sub>a\<^sub>g\<^sub>e\<^sub>v\<^sub>a\<^sub>l)"

fun run_update' :: "constr list \<Rightarrow> run" ("\<langle>\<langle> _ \<rangle>\<rangle>") where
    "\<langle>\<langle> [] \<rangle>\<rangle>    = \<rho>\<^sub>\<odot>"
  | "\<langle>\<langle> \<gamma> # \<Gamma> \<rangle>\<rangle> = \<langle>\<langle> \<Gamma> \<rangle>\<rangle> \<langle> \<gamma> \<rangle>"

lemma witness_consistency:
  "\<langle>\<langle> \<Gamma> \<rangle>\<rangle> \<in> \<lbrakk>\<lbrakk> \<Gamma> \<rbrakk>\<rbrakk> \<Longrightarrow> consistent_run \<Gamma>"
  unfolding consistent_run_def by (rule exI, auto)

method solve_run_witness =
  rule witness_consistency,
  auto,
  (match conclusion in "False" \<Rightarrow> \<open>fail\<close> \<bar> _ \<Rightarrow> \<open>succeed\<close>)

method solve_run_witness' =
  rule witness_consistency,
  auto

end
