theory RunExtra

imports Run

begin
(*
abbreviation Abs_run_not ("_\<^sup>\<up>" 1000) where "f\<^sup>\<up> \<equiv> Abs_run f"
abbreviation Rep_run_not ("_\<^sup>\<down>" 1000) where "f\<^sup>\<down> \<equiv> Rep_run f"
*)

(* Update functionals *)
fun run_update :: "('\<tau>::linordered_field) run \<Rightarrow> '\<tau> constr \<Rightarrow> '\<tau> run" ("_ \<langle> _ \<rangle>") where
    "\<rho> \<langle> K \<Up> n \<rangle>  = Abs_run (\<lambda>n' K'. if K = K' \<and> n = n' then (True, time ((Rep_run \<rho>) n K)) else (Rep_run \<rho>) n' K')"
  | "\<rho> \<langle> K \<not>\<Up> n \<rangle> = Abs_run (\<lambda>n' K'. if K = K' \<and> n = n' then (False, time ((Rep_run \<rho>) n K)) else (Rep_run \<rho>) n' K')"
  | "\<rho> \<langle> K \<Down> n @ \<lfloor> \<tau> \<rfloor> \<rangle> = Abs_run (time_update n K \<tau> (Rep_run \<rho>))"
  | "\<rho> \<langle> K \<Down> n @ \<lfloor> \<tau>\<^sub>v\<^sub>a\<^sub>r(K', n') \<oplus> \<tau> \<rfloor> \<rangle> =
     Abs_run (time_update n K (time ((Rep_run \<rho>) n' K') + \<tau>) (Rep_run \<rho>))"
  (* | "\<rho> \<langle> \<langle>\<tau>\<^sub>v\<^sub>a\<^sub>r(K, n), \<tau>\<^sub>v\<^sub>a\<^sub>r(K', n')\<rangle> \<epsilon> R \<rangle> = ?" *) (* Missing pattern *)
  | "\<rho> \<langle> (\<tau>\<^sub>v\<^sub>a\<^sub>r(K\<^sub>1, n\<^sub>1)) \<doteq> \<alpha> * \<tau>\<^sub>v\<^sub>a\<^sub>r(K\<^sub>2, n\<^sub>2) + \<beta> \<rangle> =
     Abs_run (if time ((Rep_run \<rho>) n\<^sub>1 K\<^sub>1) = \<tau>\<^sub>c\<^sub>s\<^sub>t 0 \<and> time ((Rep_run \<rho>) n\<^sub>2 K\<^sub>2) \<noteq> \<tau>\<^sub>c\<^sub>s\<^sub>t 0
      then (time_update n\<^sub>1 K\<^sub>1 (\<alpha> * time ((Rep_run \<rho>) n\<^sub>2 K\<^sub>2) + \<beta>) (Rep_run \<rho>))
      else if time ((Rep_run \<rho>) n\<^sub>2 K\<^sub>2) = \<tau>\<^sub>c\<^sub>s\<^sub>t 0 \<and> time ((Rep_run \<rho>) n\<^sub>1 K\<^sub>1) \<noteq> \<tau>\<^sub>c\<^sub>s\<^sub>t 0
           then time_update n\<^sub>2 K\<^sub>2 ((time ((Rep_run \<rho>) n\<^sub>1 K\<^sub>1) - \<beta>) / \<alpha>) (Rep_run \<rho>)
           else (Rep_run \<rho>) 
     )"

fun run_update' :: "('\<tau>::linordered_field) constr list \<Rightarrow> '\<tau> run" ("\<langle>\<langle> _ \<rangle>\<rangle>") where
    "\<langle>\<langle> [] \<rangle>\<rangle>    = \<rho>\<^sub>\<odot>"
  | "\<langle>\<langle> \<gamma> # \<Gamma> \<rangle>\<rangle> = (\<langle>\<langle> \<Gamma> \<rangle>\<rangle> \<langle> \<gamma> \<rangle>)"

lemma witness_consistency:
  "\<langle>\<langle> \<Gamma> \<rangle>\<rangle> \<in> \<lbrakk>\<lbrakk> \<Gamma> \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m \<Longrightarrow> consistent_run \<Gamma>"
  unfolding consistent_run_def by (rule exI, auto)

lemma witness_consistency':
  "consistent_run \<Gamma> \<Longrightarrow> \<langle>\<langle> \<Gamma> \<rangle>\<rangle> \<in> \<lbrakk>\<lbrakk> \<Gamma> \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m"
  oops (* Not sure the idea is true *)


end
