theory RunConsistency
imports
    "TESL"
    "$ISABELLE_HOME/src/HOL/Eisbach/Eisbach_Tools" 

begin

text \<open> A run is a time frame and tag variable valuation \<close>
  
definition is_a_valuation :: "(tag_expr \<Rightarrow> tag_const) \<Rightarrow> bool" where
  "is_a_valuation \<eta> \<equiv>
   (* A constant valuates into itself *)
   (\<forall>\<tau>. \<eta> \<lfloor> \<tau> \<rfloor>\<^sub>c\<^sub>s\<^sub>t = \<tau>) \<and>
   (* Addition is distributed *)
   (\<forall>\<tau>\<^sub>1 \<tau>\<^sub>2. \<eta> \<lfloor> \<tau>\<^sub>1 + \<tau>\<^sub>2 \<rfloor> = \<eta> \<tau>\<^sub>1 + \<eta> \<tau>\<^sub>2)"

typedef (overloaded) time_frame = "{ \<eta> :: tag_expr \<Rightarrow> tag_const. is_a_valuation \<eta> }"
  sorry

type_synonym instant = "clock \<Rightarrow> bool"
type_synonym event_frame = "nat \<Rightarrow> instant"
type_synonym run = "event_frame * time_frame"

fun symbolic_run_interpretation_primitive :: "constr \<Rightarrow> run set" ("\<lbrakk> _ \<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n") where
    "\<lbrakk> c \<Up> n    \<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n = { (\<sigma>, \<eta>). \<sigma> n c = True }"
  | "\<lbrakk> c \<not>\<Up> n   \<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n = { (\<sigma>, \<eta>). \<sigma> n c = False }"
  | "\<lbrakk> c \<Down> n, \<tau> \<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n = { (\<sigma>, \<eta>).
                      ((Rep_time_frame \<eta>) (\<lfloor>\<tau>\<^sub>v\<^sub>a\<^sub>r(c, n)\<rfloor>\<^sub>v\<^sub>a\<^sub>r)) = (case \<tau> of
                                           \<lfloor> \<tau> \<rfloor>\<^sub>c\<^sub>s\<^sub>t \<Rightarrow> \<tau>
                                         | \<lfloor> X \<rfloor>\<^sub>v\<^sub>a\<^sub>r \<Rightarrow> (Rep_time_frame \<eta>) \<lfloor> X \<rfloor>\<^sub>v\<^sub>a\<^sub>r
                                         | \<lfloor> \<tau>\<^sub>1 + \<tau>\<^sub>2 \<rfloor> \<Rightarrow> (Rep_time_frame \<eta>) \<tau>\<^sub>1 + (Rep_time_frame \<eta>) \<tau>\<^sub>2)}"
  | "\<lbrakk> \<tau>\<^sub>1 \<doteq> \<alpha> * \<tau>\<^sub>2 + \<beta> \<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n = { (\<sigma>, \<eta>) . (Rep_time_frame \<eta>) \<lfloor>\<tau>\<^sub>1\<rfloor>\<^sub>v\<^sub>a\<^sub>r = \<alpha> * ((Rep_time_frame \<eta>) \<lfloor>\<tau>\<^sub>2\<rfloor>\<^sub>v\<^sub>a\<^sub>r) + \<beta>}"

fun symbolic_run_interpretation :: "constr list \<Rightarrow> run set" ("\<lbrakk>\<lbrakk> _ \<rbrakk>\<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n") where
    "\<lbrakk>\<lbrakk> [] \<rbrakk>\<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n = { _. True }"
  | "\<lbrakk>\<lbrakk> \<gamma> # \<Gamma> \<rbrakk>\<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n = \<lbrakk> \<gamma> \<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n \<inter> \<lbrakk>\<lbrakk> \<Gamma> \<rbrakk>\<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n"

definition consistent_run :: "constr list \<Rightarrow> bool" where 
  "consistent_run \<Gamma> \<equiv> \<exists>\<rho>. \<rho> \<in> \<lbrakk>\<lbrakk> \<Gamma> \<rbrakk>\<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n"

text \<open> Defining a method for witness construction \<close>

(* Initial states *)
abbreviation initial_time_frame :: "event_frame" ("\<sigma>\<^sub>\<odot>") where
  "\<sigma>\<^sub>\<odot> \<equiv> \<lambda>n c. (* False *) undefined"
abbreviation initial_tag_eval :: "time_frame" ("\<eta>\<^sub>\<odot>") where
  "\<eta>\<^sub>\<odot> \<equiv> Abs_time_frame (\<lambda>x. case x of \<lfloor> \<tau> \<rfloor>\<^sub>c\<^sub>s\<^sub>t \<Rightarrow> \<tau> | _ \<Rightarrow> undefined)"
abbreviation initial_run :: "run" ("\<rho>\<^sub>\<odot>") where
  "\<rho>\<^sub>\<odot> \<equiv> (\<sigma>\<^sub>\<odot>, \<eta>\<^sub>\<odot>)"

(* Update functionals *)
fun event_frame_update :: "event_frame \<Rightarrow> constr \<Rightarrow> event_frame" ("_ \<langle> _ \<rangle>\<^sub>e\<^sub>v\<^sub>e\<^sub>n\<^sub>t\<^sub>f\<^sub>r\<^sub>a\<^sub>m\<^sub>e") where
    "\<sigma> \<langle> c \<Up> n \<rangle>\<^sub>e\<^sub>v\<^sub>e\<^sub>n\<^sub>t\<^sub>f\<^sub>r\<^sub>a\<^sub>m\<^sub>e = (\<lambda>n' c'. if c = c' \<and> n = n' then True else \<sigma> n' c')"
  | "\<sigma> \<langle> c \<not>\<Up> n \<rangle>\<^sub>e\<^sub>v\<^sub>e\<^sub>n\<^sub>t\<^sub>f\<^sub>r\<^sub>a\<^sub>m\<^sub>e = (\<lambda>n' c'. if c = c' \<and> n = n' then False else \<sigma> n' c')"
  | "\<sigma> \<langle> c \<Down> n, \<tau> \<rangle>\<^sub>e\<^sub>v\<^sub>e\<^sub>n\<^sub>t\<^sub>f\<^sub>r\<^sub>a\<^sub>m\<^sub>e = (\<lambda>n' c'. if c = c' \<and> n = n' then \<sigma> n c else \<sigma> n' c')"
  | "\<sigma> \<langle> \<tau>\<^sub>1 \<doteq> \<alpha> * \<tau>\<^sub>2 + \<beta> \<rangle>\<^sub>e\<^sub>v\<^sub>e\<^sub>n\<^sub>t\<^sub>f\<^sub>r\<^sub>a\<^sub>m\<^sub>e = \<sigma>"

fun time_frame_update :: "time_frame \<Rightarrow> constr \<Rightarrow> time_frame" ("_ \<langle> _ \<rangle>\<^sub>t\<^sub>i\<^sub>m\<^sub>e\<^sub>f\<^sub>r\<^sub>a\<^sub>m\<^sub>e") where
    "\<eta> \<langle> c \<Up> n \<rangle>\<^sub>t\<^sub>i\<^sub>m\<^sub>e\<^sub>f\<^sub>r\<^sub>a\<^sub>m\<^sub>e = \<eta>"
  | "\<eta> \<langle> c \<not>\<Up> n \<rangle>\<^sub>t\<^sub>i\<^sub>m\<^sub>e\<^sub>f\<^sub>r\<^sub>a\<^sub>m\<^sub>e = \<eta>"
  | "\<eta> \<langle> c \<Down> n, \<tau> \<rangle>\<^sub>t\<^sub>i\<^sub>m\<^sub>e\<^sub>f\<^sub>r\<^sub>a\<^sub>m\<^sub>e = Abs_time_frame (\<lambda>\<tau>'. if \<tau>' = \<lfloor>\<tau>\<^sub>v\<^sub>a\<^sub>r(c, n)\<rfloor>\<^sub>v\<^sub>a\<^sub>r then (case \<tau> of
                                             \<lfloor> \<tau> \<rfloor>\<^sub>c\<^sub>s\<^sub>t \<Rightarrow> \<tau>
                                           | \<lfloor> X \<rfloor>\<^sub>v\<^sub>a\<^sub>r \<Rightarrow> (Rep_time_frame \<eta>) \<lfloor> X \<rfloor>\<^sub>v\<^sub>a\<^sub>r
                                           | \<lfloor> \<tau>\<^sub>1 + \<tau>\<^sub>2 \<rfloor> \<Rightarrow> (Rep_time_frame \<eta>) \<tau>\<^sub>1 + (Rep_time_frame \<eta>) \<tau>\<^sub>2
    ) else (Rep_time_frame \<eta>) \<tau>')"
  | "\<eta> \<langle> \<tau>\<^sub>1 \<doteq> \<alpha> * \<tau>\<^sub>2 + \<beta> \<rangle>\<^sub>t\<^sub>i\<^sub>m\<^sub>e\<^sub>f\<^sub>r\<^sub>a\<^sub>m\<^sub>e = undefined" (* TODO *)

fun run_update :: "run \<Rightarrow> constr \<Rightarrow> run" ("_ \<langle> _ \<rangle>") where
    "(\<sigma>, \<eta>) \<langle> \<gamma> \<rangle> = (\<sigma> \<langle> \<gamma> \<rangle>\<^sub>e\<^sub>v\<^sub>e\<^sub>n\<^sub>t\<^sub>f\<^sub>r\<^sub>a\<^sub>m\<^sub>e, \<eta> \<langle> \<gamma> \<rangle>\<^sub>t\<^sub>i\<^sub>m\<^sub>e\<^sub>f\<^sub>r\<^sub>a\<^sub>m\<^sub>e)"

fun run_update' :: "constr list \<Rightarrow> run" ("\<langle>\<langle> _ \<rangle>\<rangle>") where
    "\<langle>\<langle> [] \<rangle>\<rangle>    = \<rho>\<^sub>\<odot>"
  | "\<langle>\<langle> \<gamma> # \<Gamma> \<rangle>\<rangle> = \<langle>\<langle> \<Gamma> \<rangle>\<rangle> \<langle> \<gamma> \<rangle>"

lemma witness_consistency:
  "\<langle>\<langle> \<Gamma> \<rangle>\<rangle> \<in> \<lbrakk>\<lbrakk> \<Gamma> \<rbrakk>\<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n \<Longrightarrow> consistent_run \<Gamma>"
  unfolding consistent_run_def by (rule exI, auto)

method solve_run_witness =
  rule witness_consistency,
  auto,
  (match conclusion in "False" \<Rightarrow> \<open>fail\<close> \<bar> _ \<Rightarrow> \<open>succeed\<close>)

method solve_run_witness' =
  rule witness_consistency,
  auto

lemma
  "is_a_valuation \<eta> \<Longrightarrow>
   \<eta> X = X' \<Longrightarrow>
   Rep_time_frame (Abs_time_frame \<eta>) X = X'"
  by (simp add: Abs_time_frame_inverse)




end
