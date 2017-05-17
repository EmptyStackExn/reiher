theory RunConsistency
imports
    Main
    "TESL"

begin

type_synonym instant = "clock \<Rightarrow> (bool * tag)"

abbreviation is_a_valuation :: "(tag \<Rightarrow> tag) \<Rightarrow> bool" where
  "is_a_valuation \<eta> \<equiv>
  (* A constant evaluates in itself *)
  (\<forall>\<tau>::tag. is_concrete \<tau> \<longrightarrow> (\<eta> \<tau> = \<tau>)) \<and>
  (* A valuation only gives concrete tags *)
  (\<forall>\<tau>::tag. is_concrete (\<eta> \<tau>))"

value "f [x := 1]"
(* A run is a time frame and tag variable valuation *)
(* type_synonym tag_eval = "tag \<Rightarrow> tag" *)
typedef (overloaded) tag_eval = "{ \<eta> :: tag \<Rightarrow> tag. is_a_valuation \<eta> }"
  proof -
    have "(\<lambda>x. case x of Unit \<Rightarrow> x | Integer _ \<Rightarrow> x | Add _ \<Rightarrow> Unit | Schematic _ \<Rightarrow> Unit) \<in> {\<eta>. is_a_valuation \<eta>}"
      by (simp, metis tag.case(1) tag.case(2) tag.case(3) tag.case(4) tag.exhaust)
    then show ?thesis by auto
  qed
type_synonym time_frame = "nat \<Rightarrow> instant"
type_synonym run = "time_frame * tag_eval"

abbreviation hamlet where "hamlet \<equiv> fst"
abbreviation time where "time \<equiv> snd"

(* How to shallowly make a deep embedding of arithmetic reasoning? *)
fun symbolic_run_interpretation_primitive :: "constr \<Rightarrow> run set" ("\<lbrakk>\<lbrakk> _ \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m\<^sub>i\<^sub>t\<^sub>i\<^sub>v\<^sub>e") where
    "\<lbrakk>\<lbrakk> \<Up>(c, n)    \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m\<^sub>i\<^sub>t\<^sub>i\<^sub>v\<^sub>e = { (\<rho>, \<eta>). hamlet (\<rho> n c) = True }"
  | "\<lbrakk>\<lbrakk> \<not>\<Up>(c, n)   \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m\<^sub>i\<^sub>t\<^sub>i\<^sub>v\<^sub>e = { (\<rho>, \<eta>). hamlet (\<rho> n c) = False }"
  | "\<lbrakk>\<lbrakk> \<Down>(c, n, \<tau>) \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m\<^sub>i\<^sub>t\<^sub>i\<^sub>v\<^sub>e = { (\<rho>, \<eta>). time (\<rho> n c) = \<tau> }"
  | "\<lbrakk>\<lbrakk> \<doteq> (\<tau>\<^sub>1, \<alpha>, \<tau>\<^sub>2, \<beta>) \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m\<^sub>i\<^sub>t\<^sub>i\<^sub>v\<^sub>e =
    (* TODO: \<alpha> et \<beta> pour former un semi-ring *)
    { (\<rho>, \<eta>). (Rep_tag_eval \<eta>) \<tau>\<^sub>1 = (Rep_tag_eval \<eta>) \<tau>\<^sub>2 }" 

fun symbolic_run_interpretation :: "constr list \<Rightarrow> run set" ("\<lbrakk>\<lbrakk> _ \<rbrakk>\<rbrakk>") where
    "\<lbrakk>\<lbrakk> [] \<rbrakk>\<rbrakk> = { _. True }"
  | "\<lbrakk>\<lbrakk> \<gamma> # \<Gamma> \<rbrakk>\<rbrakk> = \<lbrakk>\<lbrakk> \<gamma> \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m\<^sub>i\<^sub>t\<^sub>i\<^sub>v\<^sub>e \<inter> \<lbrakk>\<lbrakk> \<Gamma> \<rbrakk>\<rbrakk>"

definition consistent_run :: "constr list \<Rightarrow> bool" where 
  *[simp]: "consistent_run \<Gamma> \<equiv> \<exists>\<rho> \<eta>. (\<rho>, \<eta>) \<in> \<lbrakk>\<lbrakk> \<Gamma> \<rbrakk>\<rbrakk>"

term "(\<lambda>_ _. (True, \<lambda>x. x))"
term "(\<lambda>x. x) ((3::nat) := 1)"
term "(\<lambda>n. (\<lambda>c. (True, \<tau>\<^sub>u\<^sub>n\<^sub>i\<^sub>t)), Abs_tag_eval (\<lambda>x. x))::run"
(* DEBUG EXAMPLE *)
lemma "consistent_run [\<Up> (\<lceil> ''H1'' \<rceil>, Suc 0)]"
proof (auto)
  show " \<exists>\<rho>::time_frame. hamlet (\<rho> (Suc 0) \<lceil> ''H1'' \<rceil>)" 
  proof -
    let ?f = "(\<lambda>n::nat. (\<lambda>c::clock. (True, \<tau>\<^sub>u\<^sub>n\<^sub>i\<^sub>t)))"
    show ?thesis
       by (rule_tac x="?f" in  exI, simp)
  qed
qed
    
end
