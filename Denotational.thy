theory Denotational
imports
    "TESL"
    "Run"

begin

fun TESL_interpretation_primitive
    :: "TESL_atomic \<Rightarrow> run set" ("\<lbrakk> _ \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L") where
    "\<lbrakk> K sporadic \<tau> \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L =
        { \<rho>. \<exists>n::nat. hamlet ((Rep_run \<rho>) n K) = True \<and> time ((Rep_run \<rho>) n K) = \<tau> }"
  | "\<lbrakk> K\<^sub>1 sporadic \<lfloor>\<tau>\<rfloor> on K\<^sub>2 \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L =
        { \<rho>. \<exists>n::nat. hamlet ((Rep_run \<rho>) n K\<^sub>1) = True \<and> time ((Rep_run \<rho>) n K\<^sub>2) = \<tau> }"
  | "\<lbrakk> K\<^sub>1 sporadic \<lfloor>\<tau>\<^sub>v\<^sub>a\<^sub>r(K, n) \<oplus> \<tau>\<rfloor> on K\<^sub>2 \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L =
        { \<rho>. \<exists>n'::nat. hamlet ((Rep_run \<rho>) n' K\<^sub>1) = True
                       \<and> time ((Rep_run \<rho>) n' K\<^sub>2) = time ((Rep_run \<rho>) n K) + \<tau> }"
  | "\<lbrakk> tag-relation K\<^sub>1 = \<alpha> * K\<^sub>2 + \<beta> \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L =
        { \<rho>. \<forall>n::nat. time ((Rep_run \<rho>) n K\<^sub>1) = \<alpha> * time ((Rep_run \<rho>) n K\<^sub>2) + \<beta> }"
  | "\<lbrakk> master implies slave \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L =
        { \<rho>. \<forall>n::nat. hamlet ((Rep_run \<rho>) n master) \<longrightarrow> hamlet ((Rep_run \<rho>) n slave) }"
  | "\<lbrakk> master time-delayed by \<delta>\<tau> on measuring implies slave \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L =
        { \<rho>. \<forall>n. hamlet ((Rep_run \<rho>) n master) \<longrightarrow>
                 (let measured_time = time ((Rep_run \<rho>) n measuring) in
                  \<exists>m > n. hamlet ((Rep_run \<rho>) n master)
                          \<and> time ((Rep_run \<rho>) m measuring) = measured_time + \<delta>\<tau>
                 )
        }"

fun TESL_interpretation_primitive_bounded
    :: "TESL_atomic \<Rightarrow> nat \<Rightarrow> run set" ("\<lbrakk> _ @\<le> _ \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L") where
    "\<lbrakk> K sporadic \<tau> @\<le> b \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L =
        { \<rho>. \<exists>n<b::nat. 0 < n \<and> hamlet ((Rep_run \<rho>) n K) = True \<and> time ((Rep_run \<rho>) n K) = \<tau> }"
  | "\<lbrakk> K\<^sub>1 sporadic \<lfloor>\<tau>\<rfloor> on K\<^sub>2 @\<le> b \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L =
        { \<rho>. \<exists>n<b::nat. 0 < n \<and> hamlet ((Rep_run \<rho>) n K\<^sub>1) = True \<and> time ((Rep_run \<rho>) n K\<^sub>2) = \<tau> }"
  | "\<lbrakk> K\<^sub>1 sporadic \<lfloor>\<tau>\<^sub>v\<^sub>a\<^sub>r(K, n) \<oplus> \<tau>\<rfloor> on K\<^sub>2 @\<le> b \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L =
        { \<rho>. \<exists>n'<b::nat. 0 < n' \<and> hamlet ((Rep_run \<rho>) n' K\<^sub>1) = True
                         \<and> time ((Rep_run \<rho>) n' K\<^sub>2) = time ((Rep_run \<rho>) n K) + \<tau> }"
  | "\<lbrakk> tag-relation K\<^sub>1 = \<alpha> * K\<^sub>2 + \<beta> @\<le> b \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L =
        { \<rho>. \<forall>n<b::nat. 0 < n \<longrightarrow> time ((Rep_run \<rho>) n K\<^sub>1) = \<alpha> * time ((Rep_run \<rho>) n K\<^sub>2) + \<beta> }"
  | "\<lbrakk> master implies slave @\<le> b \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L =
        { \<rho>. \<forall>n<b::nat. 0 < n \<longrightarrow> hamlet ((Rep_run \<rho>) n master) \<longrightarrow> hamlet ((Rep_run \<rho>) n slave) }"
  | "\<lbrakk> master time-delayed by \<delta>\<tau> on measuring implies slave @\<le> b \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L =
        { \<rho>. \<forall>n<b. 0 < n \<longrightarrow> hamlet ((Rep_run \<rho>) n master) \<longrightarrow>
                 (let measured_time = time ((Rep_run \<rho>) n measuring) in
                  \<exists>m > n. hamlet ((Rep_run \<rho>) n master)
                          \<and> time ((Rep_run \<rho>) m measuring) = measured_time + \<delta>\<tau>
                 )
        }"

instantiation prod :: (complete_lattice, type) complete_lattice
begin
  definition Inf_prod :: "('a \<times> 'b) set \<Rightarrow> 'a \<times> 'b" where "Inf_prod \<equiv> undefined"
  definition Sup_prod :: "('a \<times> 'b) set \<Rightarrow> 'a \<times> 'b" where "Sup_prod \<equiv> undefined"
  definition bot_prod :: "'a \<times> 'b" where "bot_prod \<equiv> undefined"
  definition sup_prod :: "'a \<times> 'b \<Rightarrow> 'a \<times> 'b \<Rightarrow> 'a \<times> 'b" where "sup_prod \<equiv> undefined"
  definition top_prod :: "'a \<times> 'b" where "top_prod \<equiv> undefined"
  definition inf_prod :: "'a \<times> 'b \<Rightarrow> 'a \<times> 'b \<Rightarrow> 'a \<times> 'b" where "inf_prod \<equiv> undefined"
  definition less_eq_prod :: "'a \<times> 'b \<Rightarrow> 'a \<times> 'b \<Rightarrow> bool" where "less_eq_prod \<equiv> undefined"
  definition less_prod :: "'a \<times> 'b \<Rightarrow> 'a \<times> 'b \<Rightarrow> bool" where "less_prod \<equiv> undefined"
instance sorry
end

lemma "\<lbrakk> \<phi> \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L = fst (gfp (\<lambda>(R, n). (R \<inter> \<lbrakk> \<phi> @\<le> n \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L, n + 1)))"
sorry

(*
fun TESL_interpretation_primitive_bounded_rec
  :: "TESL_atomic \<Rightarrow> nat \<Rightarrow> run set" ("\<lbrakk> _ @\<le> _ \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L") where
    "\<lbrakk> \<phi> @\<le> (0::nat) \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L =
        { _. True }"
  | "\<lbrakk> master implies slave @\<le> Suc n \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L =
        { \<rho> \<in> \<lbrakk> master implies slave @\<le> n \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L.(hamlet ((Rep_run \<rho>) n master) \<longrightarrow> hamlet ((Rep_run \<rho>) n slave)) }"
*)


fun TESL_interpretation :: "TESL_formula \<Rightarrow> run set" ("\<lbrakk>\<lbrakk> _ \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L") where
    "\<lbrakk>\<lbrakk> [] \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L = { _. True }"
  | "\<lbrakk>\<lbrakk> \<phi> # \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L = \<lbrakk> \<phi> \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L \<inter> \<lbrakk>\<lbrakk> \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L"


end
