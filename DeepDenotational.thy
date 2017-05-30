theory DeepDenotational
imports
    "TESL"
    "Run"

begin

fun TESL_interpretation_primitive :: "TESL_atomic \<Rightarrow> run set" ("\<lbrakk> _ \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L") where
    "\<lbrakk> K sporadic \<tau> \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L =
        { \<rho>. \<exists>n::nat. hamlet (\<rho> n K) = True \<and> time (\<rho> n K) = \<tau> }"
  | "\<lbrakk> K\<^sub>1 sporadic \<lfloor>\<tau>\<rfloor> on K\<^sub>2 \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L =
        { \<rho>. \<exists>n::nat. hamlet (\<rho> n K\<^sub>1) = True \<and> time (\<rho> n K\<^sub>2) = \<tau> }"
  | "\<lbrakk> K\<^sub>1 sporadic \<lfloor>\<tau>\<^sub>v\<^sub>a\<^sub>r(K, n) \<oplus> \<tau>\<rfloor> on K\<^sub>2 \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L =
        { \<rho>. \<exists>n'::nat. hamlet (\<rho> n' K\<^sub>1) = True \<and> time (\<rho> n' K\<^sub>2) = time (\<rho> n K) + \<tau> }"
  | "\<lbrakk> tag-relation K\<^sub>1 = \<alpha> * K\<^sub>2 + \<beta> \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L =
        { \<rho>. \<forall>n::nat. time (\<rho> n K\<^sub>1) = \<alpha> * time (\<rho> n K\<^sub>2) + \<beta> }"
  | "\<lbrakk> master implies slave \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L =
        { \<rho>. \<forall>n::nat. hamlet (\<rho> n master) \<longrightarrow> hamlet (\<rho> n slave) }"
  | "\<lbrakk> master time-delayed by \<delta>\<tau> on measuring implies slave \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L =
        { \<rho>. \<forall>n. hamlet (\<rho> n master) \<longrightarrow>
                 (let measured_time = time (\<rho> n measuring) in
                  \<exists>m > n. hamlet (\<rho> n master)
                          \<and> time (\<rho> m measuring) = measured_time + \<delta>\<tau>
                 )
        }"

fun TESL_interpretation :: "TESL_formula \<Rightarrow> run set" ("\<lbrakk>\<lbrakk> _ \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L") where
    "\<lbrakk>\<lbrakk> [] \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L = { _. True }"
  | "\<lbrakk>\<lbrakk> \<phi> # \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L = \<lbrakk> \<phi> \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L \<inter> \<lbrakk>\<lbrakk> \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L"


end
