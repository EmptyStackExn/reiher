theory Run
imports
    "TESL"

begin

section \<open> Defining runs \<close>

abbreviation hamlet where "hamlet \<equiv> fst"
abbreviation time where "time \<equiv> snd"

(*
type_synonym instant = "clock \<Rightarrow> (bool \<times> tag_const)"
type_synonym run = "nat \<Rightarrow> instant"
*)
typedef (overloaded) run =
  "{ \<rho>::nat \<Rightarrow> clock \<Rightarrow> (bool \<times> tag_const). \<forall>c. mono (\<lambda>n. time (\<rho> n c)) }"
sorry

abbreviation Abs_run_not ("_\<^sup>\<up>" 1000) where "f\<^sup>\<up> \<equiv> Abs_run f"
abbreviation Rep_run_not ("_\<^sup>\<down>" 1000) where "f\<^sup>\<down> \<equiv> Rep_run f"

fun symbolic_run_interpretation_primitive :: "constr \<Rightarrow> run set" ("\<lbrakk> _ \<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n") where
    "\<lbrakk> K \<Up> n  \<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n = { \<rho>. hamlet (\<rho>\<^sup>\<down> n K) = True }"
  | "\<lbrakk> K \<not>\<Up> n \<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n = { \<rho>. hamlet (\<rho>\<^sup>\<down> n K) = False }"
  | "\<lbrakk> K \<Down> n @ \<lfloor> \<tau> \<rfloor> \<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n = { \<rho>. time (\<rho>\<^sup>\<down> n K) = \<tau> }"
  | "\<lbrakk> K \<Down> n @ \<lfloor> \<tau>\<^sub>v\<^sub>a\<^sub>r(K', n') \<oplus> \<tau> \<rfloor> \<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n = { \<rho>. time (\<rho>\<^sup>\<down> n K) = time (\<rho>\<^sup>\<down> n' K') + \<tau> }"
  | "\<lbrakk> \<tau>\<^sub>v\<^sub>a\<^sub>r(K\<^sub>1, n\<^sub>1) \<doteq> \<alpha> * \<tau>\<^sub>v\<^sub>a\<^sub>r(K\<^sub>2, n\<^sub>2) + \<beta> \<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n = { \<rho>. time (\<rho>\<^sup>\<down> n\<^sub>1 K\<^sub>1) = \<alpha> * time (\<rho>\<^sup>\<down> n\<^sub>2 K\<^sub>2) + \<beta> }"

fun symbolic_run_interpretation :: "constr list \<Rightarrow> run set" ("\<lbrakk>\<lbrakk> _ \<rbrakk>\<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n") where
    "\<lbrakk>\<lbrakk> [] \<rbrakk>\<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n = { _. True }"
  | "\<lbrakk>\<lbrakk> \<gamma> # \<Gamma> \<rbrakk>\<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n = \<lbrakk> \<gamma> \<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n \<inter> \<lbrakk>\<lbrakk> \<Gamma> \<rbrakk>\<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n"

definition consistent_run :: "constr list \<Rightarrow> bool" where 
  "consistent_run \<Gamma> \<equiv> \<exists>\<rho>. \<rho> \<in> \<lbrakk>\<lbrakk> \<Gamma> \<rbrakk>\<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n"

text \<open> Defining a method for witness construction \<close>

(* Initial states *)
abbreviation initial_run :: "run" ("\<rho>\<^sub>\<odot>") where
  "\<rho>\<^sub>\<odot> \<equiv> Abs_run (\<lambda>_ _. (undefined, undefined))"

(* Update functionals *)
fun run_update :: "run \<Rightarrow> constr \<Rightarrow> run" ("_ \<langle> _ \<rangle>") where
    "\<rho> \<langle> K \<Up> n \<rangle>  = (\<lambda>n' K'. if K = K' \<and> n = n' then (True, time (\<rho>\<^sup>\<down> n K)) else \<rho>\<^sup>\<down> n' K')\<^sup>\<up>"
  | "\<rho> \<langle> K \<not>\<Up> n \<rangle> = (\<lambda>n' K'. if K = K' \<and> n = n' then (False, time (\<rho>\<^sup>\<down> n K)) else \<rho>\<^sup>\<down> n' K')\<^sup>\<up>"
  | "\<rho> \<langle> K \<Down> n @ \<lfloor> \<tau> \<rfloor> \<rangle> = (\<lambda>n' K'. if K = K' \<and> n = n' then (hamlet (\<rho>\<^sup>\<down> n K), \<tau>) else \<rho>\<^sup>\<down> n' K')\<^sup>\<up>"
  | "\<rho> \<langle> K \<Down> n @ \<lfloor> \<tau>\<^sub>v\<^sub>a\<^sub>r(K', n') \<oplus> \<tau> \<rfloor> \<rangle> =
     (\<lambda>n'' K''. if K = K'' \<and> n = n'' then (hamlet (\<rho>\<^sup>\<down> n K), time (\<rho>\<^sup>\<down> n' K') + \<tau>) else \<rho>\<^sup>\<down> n'' K'')\<^sup>\<up>"
  | "\<rho> \<langle> \<tau>\<^sub>v\<^sub>a\<^sub>r(K\<^sub>1, n\<^sub>1) \<doteq> \<alpha> * \<tau>\<^sub>v\<^sub>a\<^sub>r(K\<^sub>2, n\<^sub>2) + \<beta> \<rangle> =
     (if time (\<rho>\<^sup>\<down> n\<^sub>1 K\<^sub>1) = undefined \<and> time (\<rho>\<^sup>\<down> n\<^sub>2 K\<^sub>2) \<noteq> undefined
      then (\<lambda>n K. if K = K\<^sub>1 \<and> n = n\<^sub>1 then (hamlet (\<rho>\<^sup>\<down> n K), \<alpha> * time (\<rho>\<^sup>\<down> n\<^sub>2 K\<^sub>2) + \<beta>) else \<rho>\<^sup>\<down> n K)
      else if time (\<rho>\<^sup>\<down> n\<^sub>2 K\<^sub>2) = undefined \<and> time (\<rho>\<^sup>\<down> n\<^sub>1 K\<^sub>1) \<noteq> undefined
           then (\<lambda>n K. if K = K\<^sub>2 \<and> n = n\<^sub>2 then (hamlet (\<rho>\<^sup>\<down> n K), undefined (* (time (\<rho> n\<^sub>1 K\<^sub>1) - \<beta>) / \<alpha> *)) else \<rho>\<^sup>\<down> n K)
           else \<rho>\<^sup>\<down> (* MAYBE NOT A GOOD CHOICE *)
     )\<^sup>\<up>"

fun run_update' :: "constr list \<Rightarrow> run" ("\<langle>\<langle> _ \<rangle>\<rangle>") where
    "\<langle>\<langle> [] \<rangle>\<rangle>    = \<rho>\<^sub>\<odot>"
  | "\<langle>\<langle> \<gamma> # \<Gamma> \<rangle>\<rangle> = \<langle>\<langle> \<Gamma> \<rangle>\<rangle> \<langle> \<gamma> \<rangle>"

lemma witness_consistency:
  "\<langle>\<langle> \<Gamma> \<rangle>\<rangle> \<in> \<lbrakk>\<lbrakk> \<Gamma> \<rbrakk>\<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n \<Longrightarrow> consistent_run \<Gamma>"
  unfolding consistent_run_def by (rule exI, auto)

end
