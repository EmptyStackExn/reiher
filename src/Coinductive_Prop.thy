theory Coinductive_Prop
imports
  "Operational"
  "Denotational"

begin

section \<open>Stepwise denotational interpretation of TESL atoms\<close>

(* Denotational interpretation of TESL bounded by index *)
fun TESL_interpretation_atomic_stepwise
    :: "TESL_atomic \<Rightarrow> nat \<Rightarrow> run set" ("\<lbrakk> _ \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> _\<^esup>") where
    "\<lbrakk> not K \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> i\<^esup> =
        { \<rho>. \<forall>n\<ge>i. \<not> hamlet ((Rep_run \<rho>) n K) }"
  | "\<lbrakk> K sporadic anytime \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> i\<^esup> =
        { \<rho>. \<exists>n\<ge>i. hamlet ((Rep_run \<rho>) n K) = True }"
  | "\<lbrakk> K sporadic \<tau> \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> i\<^esup> =
        { \<rho>. \<exists>n\<ge>i. hamlet ((Rep_run \<rho>) n K) = True \<and> time ((Rep_run \<rho>) n K) = \<tau> }"
  | "\<lbrakk> K\<^sub>1 sporadic \<lfloor>\<tau>\<rfloor> on K\<^sub>2 \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> i\<^esup> =
        { \<rho>. \<exists>n\<ge>i. hamlet ((Rep_run \<rho>) n K\<^sub>1) = True \<and> time ((Rep_run \<rho>) n K\<^sub>2) = \<tau> }"
  | "\<lbrakk> K\<^sub>1 sporadic \<lfloor>\<tau>\<^sub>v\<^sub>a\<^sub>r(K\<^sub>p\<^sub>a\<^sub>s\<^sub>t, n\<^sub>p\<^sub>a\<^sub>s\<^sub>t) \<oplus> \<delta>\<tau>\<rfloor> on K\<^sub>2 \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> i\<^esup> =
        { \<rho>. \<exists>n\<ge>i. hamlet ((Rep_run \<rho>) n K\<^sub>1) = True
                         \<and> time ((Rep_run \<rho>) n K\<^sub>2) = time ((Rep_run \<rho>) n\<^sub>p\<^sub>a\<^sub>s\<^sub>t K\<^sub>p\<^sub>a\<^sub>s\<^sub>t) + \<delta>\<tau> }"
  | "\<lbrakk> tag-relation K\<^sub>1 = \<alpha> * K\<^sub>2 + \<beta> \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> i\<^esup> =
        { \<rho>. \<forall>n\<ge>i. time ((Rep_run \<rho>) n K\<^sub>1) = \<alpha> * time ((Rep_run \<rho>) n K\<^sub>2) + \<beta> }"
  | "\<lbrakk> tag-relation \<langle>K\<^sub>1, K\<^sub>2\<rangle> \<in> R \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> i\<^esup> =
        { \<rho>. \<forall>n\<ge>i. R (time ((Rep_run \<rho>) n K\<^sub>1), time ((Rep_run \<rho>) n K\<^sub>2)) }"
  | "\<lbrakk> master implies slave \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> i\<^esup> =
        { \<rho>. \<forall>n\<ge>i. hamlet ((Rep_run \<rho>) n master) \<longrightarrow> hamlet ((Rep_run \<rho>) n slave) }"
  | "\<lbrakk> master implies not slave \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> i\<^esup> =
        { \<rho>. \<forall>n\<ge>i. hamlet ((Rep_run \<rho>) n master) \<longrightarrow> \<not> hamlet ((Rep_run \<rho>) n slave) }"
  | "\<lbrakk> K\<^sub>1 iff K\<^sub>2 \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> i\<^esup> =
        { \<rho>. \<forall>n\<ge>i. hamlet ((Rep_run \<rho>) n K\<^sub>1) \<longleftrightarrow> hamlet ((Rep_run \<rho>) n K\<^sub>2) }"
  | "\<lbrakk> master anytime implies slave \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> i\<^esup> =
        { \<rho>. \<forall>n\<ge>i. hamlet ((Rep_run \<rho>) n master) \<longrightarrow> (\<exists>m \<ge> n. hamlet ((Rep_run \<rho>) m slave)) }"
  | "\<lbrakk> master time-delayed by \<delta>\<tau> on measuring implies slave \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> i\<^esup> =
        { \<rho>. \<forall>n\<ge>i. hamlet ((Rep_run \<rho>) n master) \<longrightarrow>
                 (let measured_time = time ((Rep_run \<rho>) n measuring) in
                  \<exists>m \<ge> n. hamlet ((Rep_run \<rho>) m slave)
                          \<and> time ((Rep_run \<rho>) m measuring) = measured_time + \<delta>\<tau>
                 )
        }"
  (* TODO *)
  | "\<lbrakk> master sustained from begin to end implies slave \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> i\<^esup> =
        { \<rho>. \<forall>n\<ge>i. hamlet ((Rep_run \<rho>) n begin) \<longrightarrow>
                   (\<exists>p>n. (\<forall>k. (n<k \<and> k\<le>p \<and> (hamlet ((Rep_run \<rho>) k master))) \<longrightarrow> hamlet ((Rep_run \<rho>) k slave))
                                    \<and> hamlet ((Rep_run \<rho>) p end)
                          \<and> \<not> hamlet ((Rep_run \<rho>) p end))
                   
        }"
  | "\<lbrakk> master sustained until end reset on begin implies slave \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> i\<^esup> =
        { \<rho>. (\<exists>p>i. (\<forall>i<k\<le>p. (hamlet ((Rep_run \<rho>) k master) \<longrightarrow> hamlet ((Rep_run \<rho>) k slave))
                                    \<and> hamlet ((Rep_run \<rho>) p end))
                          \<and> \<not> hamlet ((Rep_run \<rho>) p end))
             \<and> (\<forall>n\<ge>Suc i. hamlet ((Rep_run \<rho>) n begin) \<longrightarrow>
                   (\<exists>p>n. (\<forall>k. n<k \<and> k\<le>p \<and> (hamlet ((Rep_run \<rho>) k master) \<longrightarrow> hamlet ((Rep_run \<rho>) k slave))
                                    \<and> hamlet ((Rep_run \<rho>) p end))
                          \<and> \<not> hamlet ((Rep_run \<rho>) p end)
               )
             )
        }"


theorem predicate_Inter_unfold:
  "{ \<rho>. \<forall>n. P \<rho> n} = \<Inter> {Y. \<exists>n. Y = { \<rho>. P \<rho> n }}"
  by (simp add: Collect_all_eq full_SetCompr_eq)

theorem predicate_Union_unfold:
  "{ \<rho>. \<exists>n. P \<rho> n} = \<Union> {Y. \<exists>n. Y = { \<rho>. P \<rho> n }}"
  by auto

lemma TESL_interp_unfold_stepwise_not:
  shows "\<lbrakk> not K \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L = \<Inter> {Y. \<exists>n::nat. Y = \<lbrakk> not K \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup>}"
  by auto

lemma TESL_interp_unfold_stepwise_sporadic_anytime:
  shows "\<lbrakk> K sporadic anytime \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L = \<Union> {Y. \<exists>n::nat. Y = \<lbrakk> K sporadic anytime \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup>}"
  by auto

lemma TESL_interp_unfold_stepwise_sporadic:
  shows "\<lbrakk> K sporadic \<tau> \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L = \<Union> {Y. \<exists>n::nat. Y = \<lbrakk> K sporadic \<tau> \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup>}"
  by auto

lemma TESL_interp_unfold_stepwise_sporadicon:
  shows "\<lbrakk> K\<^sub>1 sporadic \<lfloor>\<tau>\<rfloor> on K\<^sub>2 \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L = \<Union> {Y. \<exists>n::nat. Y = \<lbrakk> K\<^sub>1 sporadic \<lfloor>\<tau>\<rfloor> on K\<^sub>2 \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup>}"
  by auto

lemma TESL_interp_unfold_stepwise_sporadicon_add:
  shows "\<lbrakk> K\<^sub>1 sporadic \<lfloor>\<tau>\<^sub>v\<^sub>a\<^sub>r(K, n') \<oplus> \<tau>\<rfloor> on K\<^sub>2 \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L = \<Union> {Y. \<exists>n::nat. Y = \<lbrakk> K\<^sub>1 sporadic \<lfloor>\<tau>\<^sub>v\<^sub>a\<^sub>r(K, n') \<oplus> \<tau>\<rfloor> on K\<^sub>2 \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup>}"
  by auto

lemma TESL_interp_unfold_stepwise_tagrel:
  shows "\<lbrakk> tag-relation K\<^sub>1 = \<alpha> * K\<^sub>2 + \<beta> \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L = \<Inter> {Y. \<exists>n::nat. Y = \<lbrakk> tag-relation K\<^sub>1 = \<alpha> * K\<^sub>2 + \<beta> \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup>}"
  by auto

lemma TESL_interp_unfold_stepwise_tagrelgen:
  shows "\<lbrakk> tag-relation \<langle>K\<^sub>1, K\<^sub>2\<rangle> \<in> R \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L = \<Inter> {Y. \<exists>n::nat. Y = \<lbrakk> tag-relation \<langle>K\<^sub>1, K\<^sub>2\<rangle> \<in> R \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup>}"
  by auto

lemma TESL_interp_unfold_stepwise_implies:
  shows "\<lbrakk> master implies slave \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L = \<Inter> {Y. \<exists>n::nat. Y = \<lbrakk> master implies slave \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup>}"
  by auto

lemma TESL_interp_unfold_stepwise_implies_not:
  shows "\<lbrakk> master implies not slave \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L = \<Inter> {Y. \<exists>n::nat. Y = \<lbrakk> master implies not slave \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup>}"
  by auto

lemma TESL_interp_unfold_stepwise_iff:
  shows "\<lbrakk> master iff slave \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L = \<Inter> {Y. \<exists>n::nat. Y = \<lbrakk> master iff slave \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup>}"
  by auto

lemma TESL_interp_unfold_stepwise_implies_anytime:
  shows "\<lbrakk> master anytime implies slave \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L
    = \<Inter> {Y. \<exists>n::nat. Y = \<lbrakk> master anytime implies slave \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup>}"
  by auto

lemma TESL_interp_unfold_stepwise_timedelayed:
  shows "\<lbrakk> master time-delayed by \<delta>\<tau> on measuring implies slave \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L
    = \<Inter> {Y. \<exists>n::nat. Y = \<lbrakk> master time-delayed by \<delta>\<tau> on measuring implies slave \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup>}"
  by auto

theorem TESL_interp_unfold_stepwise_positive_atoms:
  assumes "positive_atom \<phi>"
  shows "\<lbrakk> \<phi> \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L = \<Union> {Y. \<exists>n::nat. Y = \<lbrakk> \<phi> \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup>}"
  proof -
    obtain cc :: "TESL_atomic \<Rightarrow> clock" and tt :: "TESL_atomic \<Rightarrow> tag_const" and cca :: "TESL_atomic \<Rightarrow> clock" and tta :: "TESL_atomic \<Rightarrow> tag_expr" and ccb :: "TESL_atomic \<Rightarrow> clock" where
      f1: "\<forall>t. \<not> positive_atom t \<or> t = cc t sporadic anytime \<or> t = cc t sporadic tt t \<or> t = cca t sporadic tta t on ccb t"
      using positive_atom.elims(2) by moura
    obtain ttb :: "tag_expr \<Rightarrow> tag_const" where
      "\<And>c t ca. \<Union>{R. \<exists>n. R = \<lbrakk> c sporadic t on ca \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup>} = \<lbrakk> c sporadic t on ca \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L \<or> \<lfloor> ttb t \<rfloor> = t"
      by (metis TESL_interp_unfold_stepwise_sporadicon_add old.prod.exhaust tag_expr.exhaust tag_var.exhaust)
    then have "\<And>t. \<Union>{R. \<exists>n. R = \<lbrakk> t \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup>} = \<lbrakk> t \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L \<or> \<lfloor> ttb (tta t) \<rfloor> = tta t \<or> \<not> positive_atom t"
      using f1 by (metis TESL_interp_unfold_stepwise_sporadic TESL_interp_unfold_stepwise_sporadic_anytime)
    then show ?thesis
      using f1
      by (metis TESL_interp_unfold_stepwise_sporadic TESL_interp_unfold_stepwise_sporadic_anytime TESL_interp_unfold_stepwise_sporadicon assms)
  qed

theorem TESL_interp_unfold_stepwise_negative_atoms:
  assumes "\<not> positive_atom \<phi>"
  shows "\<lbrakk> \<phi> \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L = \<Inter> {Y. \<exists>n::nat. Y = \<lbrakk> \<phi> \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup>}"
  by (smt Collect_cong TESL_interp_unfold_stepwise_not TESL_interp_unfold_stepwise_implies TESL_interp_unfold_stepwise_implies_not
      TESL_interp_unfold_stepwise_tagrel TESL_interp_unfold_stepwise_tagrelgen TESL_interp_unfold_stepwise_iff
      TESL_interp_unfold_stepwise_implies_anytime TESL_interp_unfold_stepwise_timedelayed assms
      positive_atom.elims(3))

lemma forall_nat_expansion:
  "(\<forall>n\<^sub>1 \<ge> (n\<^sub>0::nat). P n\<^sub>1) \<equiv> P n\<^sub>0 \<and> (\<forall>n\<^sub>1 \<ge> Suc n\<^sub>0. P n\<^sub>1)"
  by (smt Suc_leD dual_order.antisym not_less_eq_eq)

lemma exists_nat_expansion:
  "(\<exists>n\<^sub>1 \<ge> (n\<^sub>0::nat). P n\<^sub>1) \<equiv> P n\<^sub>0 \<or> (\<exists>n\<^sub>1 \<ge> Suc n\<^sub>0. P n\<^sub>1)"
  by (smt Suc_leD dual_order.antisym not_less_eq_eq)

section \<open>Coinduction unfolding properties\<close>

lemma TESL_interp_stepwise_not_coind_unfold:
  shows "\<lbrakk> not K \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup> =
    \<lbrakk> K \<not>\<Up> n \<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m
    \<inter> \<lbrakk> not K \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^esup>"
  by (smt Collect_cong Collect_conj_eq TESL_interpretation_atomic_stepwise.simps(1)
      dual_order.antisym nat_le_linear not_less_eq_eq symbolic_run_interpretation_primitive.simps(2))

lemma TESL_interp_stepwise_sporadic_anytime_coind_unfold:
  shows "\<lbrakk> K sporadic anytime \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup> =
    \<lbrakk> K \<Up> n \<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m
    \<union> \<lbrakk> K sporadic anytime \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^esup>"
  by (smt Collect_cong Collect_disj_eq Suc_leD TESL_interpretation_atomic_stepwise.simps(2)
      forall_nat_expansion le_antisym not_less_eq_eq symbolic_run_interpretation_primitive.simps(1))

lemma TESL_interp_stepwise_sporadic_coind_unfold:
  shows "\<lbrakk> K sporadic \<tau> \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup> =
    \<lbrakk> K \<Up> n \<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m \<inter> \<lbrakk> K \<Down> n @ \<lfloor> \<tau> \<rfloor> \<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m
    \<union> \<lbrakk> K sporadic \<tau> \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^esup>"
  proof -
    have "{ \<rho>. \<exists>m\<ge>n. hamlet ((Rep_run \<rho>) m K) = True \<and> time ((Rep_run \<rho>) m K) = \<tau> }
        = { \<rho>. hamlet ((Rep_run \<rho>) n K) = True \<and> time ((Rep_run \<rho>) n K) = \<tau>
               \<or> (\<exists>m\<ge>Suc n. hamlet ((Rep_run \<rho>) m K) = True \<and> time ((Rep_run \<rho>) m K) = \<tau>) }"
      using Suc_leD not_less_eq_eq by fastforce
    moreover have "{ \<rho>. hamlet ((Rep_run \<rho>) n K) = True \<and> time ((Rep_run \<rho>) n K) = \<tau>
                        \<or> (\<exists>m\<ge>Suc n. hamlet ((Rep_run \<rho>) m K) = True \<and> time ((Rep_run \<rho>) m K) = \<tau>) }
                 = \<lbrakk> K \<Up> n \<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m \<inter> \<lbrakk> K \<Down> n @ \<lfloor> \<tau> \<rfloor> \<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m \<union> \<lbrakk> K sporadic \<tau> \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^esup>"
      by (simp add: Collect_conj_eq Collect_disj_eq)
    ultimately show ?thesis by auto
  qed

lemma TESL_interp_stepwise_sporadicon_cst_coind_unfold:
  shows "\<lbrakk> K\<^sub>1 sporadic \<lfloor>\<tau>\<rfloor> on K\<^sub>2 \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup> =
    \<lbrakk> K\<^sub>1 \<Up> n \<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m \<inter> \<lbrakk> K\<^sub>2 \<Down> n @ \<lfloor> \<tau> \<rfloor> \<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m
    \<union> \<lbrakk> K\<^sub>1 sporadic \<lfloor>\<tau>\<rfloor> on K\<^sub>2 \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^esup>"
  proof -
    have "{ \<rho>. \<exists>m\<ge>n. hamlet ((Rep_run \<rho>) m K\<^sub>1) = True \<and> time ((Rep_run \<rho>) m K\<^sub>2) = \<tau> }
        = { \<rho>. hamlet ((Rep_run \<rho>) n K\<^sub>1) = True \<and> time ((Rep_run \<rho>) n K\<^sub>2) = \<tau>
               \<or> (\<exists>m\<ge>Suc n. hamlet ((Rep_run \<rho>) m K\<^sub>1) = True \<and> time ((Rep_run \<rho>) m K\<^sub>2) = \<tau>) }"
      using Suc_leD not_less_eq_eq by fastforce
    moreover have "{ \<rho>. hamlet ((Rep_run \<rho>) n K\<^sub>1) = True \<and> time ((Rep_run \<rho>) n K\<^sub>2) = \<tau>
                        \<or> (\<exists>m\<ge>Suc n. hamlet ((Rep_run \<rho>) m K\<^sub>1) = True \<and> time ((Rep_run \<rho>) m K\<^sub>2) = \<tau>) }
                 = \<lbrakk> K\<^sub>1 \<Up> n \<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m \<inter> \<lbrakk> K\<^sub>2 \<Down> n @ \<lfloor>\<tau>\<rfloor> \<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m \<union> \<lbrakk> K\<^sub>1 sporadic \<lfloor>\<tau>\<rfloor> on K\<^sub>2 \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^esup>"
      by (simp add: Collect_conj_eq Collect_disj_eq)
    ultimately show ?thesis by auto
  qed

lemma TESL_interp_stepwise_sporadicon_add_coind_unfold:
  shows "\<lbrakk> K\<^sub>1 sporadic \<lfloor>\<tau>\<^sub>v\<^sub>a\<^sub>r(K, n') \<oplus> \<tau>\<rfloor> on K\<^sub>2 \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup> =
    \<lbrakk> K\<^sub>1 \<Up> n \<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m \<inter> \<lbrakk> K\<^sub>2 \<Down> n @ \<lfloor>\<tau>\<^sub>v\<^sub>a\<^sub>r(K, n') \<oplus> \<tau>\<rfloor> \<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m
    \<union> \<lbrakk> K\<^sub>1 sporadic \<lfloor>\<tau>\<^sub>v\<^sub>a\<^sub>r(K, n') \<oplus> \<tau>\<rfloor> on K\<^sub>2 \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^esup>"
  proof -
    have "{ \<rho>. \<exists>m\<ge>n. hamlet ((Rep_run \<rho>) m K\<^sub>1) = True \<and> time ((Rep_run \<rho>) m K\<^sub>2) = time ((Rep_run \<rho>) n' K) + \<tau> }
        = { \<rho>. hamlet ((Rep_run \<rho>) n K\<^sub>1) = True \<and> time ((Rep_run \<rho>) n K\<^sub>2) = time ((Rep_run \<rho>) n' K) + \<tau>
               \<or> (\<exists>m\<ge>Suc n. hamlet ((Rep_run \<rho>) m K\<^sub>1) = True \<and> time ((Rep_run \<rho>) m K\<^sub>2) = time ((Rep_run \<rho>) n' K) + \<tau>) }"
      using Suc_leD not_less_eq_eq by fastforce
    then show ?thesis by auto
  qed

lemma TESL_interp_stepwise_sporadicon_coind_unfold:
  shows "\<lbrakk> K\<^sub>1 sporadic \<tau> on K\<^sub>2 \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup> =
    \<lbrakk> K\<^sub>1 \<Up> n \<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m \<inter> \<lbrakk> K\<^sub>2 \<Down> n @ \<tau> \<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m
    \<union> \<lbrakk> K\<^sub>1 sporadic \<tau> on K\<^sub>2 \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^esup>"
  proof (induct \<tau>)
    case (Const x)
    then show ?case using TESL_interp_stepwise_sporadicon_cst_coind_unfold by blast
  next
    case (AddDelay tagv x2)
    then show ?case
      proof (induct tagv)
        case (Schematic xa)
        then show ?case
          proof (induct xa)
            case (Pair a b)
            then show ?case using TESL_interp_stepwise_sporadicon_add_coind_unfold by blast
          qed
      qed
  qed

lemma TESL_interp_stepwise_tagrel_coind_unfold:
  shows "\<lbrakk> tag-relation K\<^sub>1 = \<alpha> * K\<^sub>2 + \<beta> \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup> =
    \<lbrakk> \<tau>\<^sub>v\<^sub>a\<^sub>r(K\<^sub>1, n) \<doteq> \<alpha> * \<tau>\<^sub>v\<^sub>a\<^sub>r(K\<^sub>2, n) + \<beta> \<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m
    \<inter> \<lbrakk> tag-relation K\<^sub>1 = \<alpha> * K\<^sub>2 + \<beta> \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^esup>"
  proof -
    have "{ \<rho>. \<forall>m\<ge>n. time ((Rep_run \<rho>) m K\<^sub>1) = \<alpha> * time ((Rep_run \<rho>) m K\<^sub>2) + \<beta> }
         = { \<rho>. time ((Rep_run \<rho>) n K\<^sub>1) = \<alpha> * time ((Rep_run \<rho>) n K\<^sub>2) + \<beta> }
         \<inter> { \<rho>. \<forall>m\<ge>Suc n. time ((Rep_run \<rho>) m K\<^sub>1) = \<alpha> * time ((Rep_run \<rho>) m K\<^sub>2) + \<beta> }"
      by (smt Collect_cong Collect_conj_eq Suc_leD eq_refl le_antisym not_less_eq_eq)
  then show ?thesis by auto
  qed

lemma TESL_interp_stepwise_tagrelgen_coind_unfold:
  shows "\<lbrakk> tag-relation \<langle>K\<^sub>1, K\<^sub>2\<rangle> \<in> R \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup> =
    \<lbrakk> \<langle>\<tau>\<^sub>v\<^sub>a\<^sub>r(K\<^sub>1, n), \<tau>\<^sub>v\<^sub>a\<^sub>r(K\<^sub>2, n)\<rangle> \<epsilon> R \<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m
    \<inter> \<lbrakk> tag-relation \<langle>K\<^sub>1, K\<^sub>2\<rangle> \<in> R \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^esup>"
  proof -
    have "{ \<rho>. \<forall>m\<ge>n. R (time ((Rep_run \<rho>) m K\<^sub>1), time ((Rep_run \<rho>) m K\<^sub>2)) }
         = { \<rho>. R (time ((Rep_run \<rho>) n K\<^sub>1), time ((Rep_run \<rho>) n K\<^sub>2)) }
         \<inter> { \<rho>. \<forall>m\<ge>Suc n. R (time ((Rep_run \<rho>) m K\<^sub>1), time ((Rep_run \<rho>) m K\<^sub>2)) }"
      by (smt Collect_cong Collect_conj_eq Suc_leD eq_refl le_antisym not_less_eq_eq)
  then show ?thesis by auto
  qed

lemma TESL_interp_stepwise_implies_coind_unfold:
  shows "\<lbrakk> master implies slave \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup> =
    (\<lbrakk> master \<not>\<Up> n \<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m \<union> \<lbrakk> master \<Up> n \<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m \<inter> \<lbrakk> slave \<Up> n \<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m)
    \<inter> \<lbrakk> master implies slave \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^esup>"
  proof -
    have "{ \<rho>. \<forall>m\<ge>n. hamlet ((Rep_run \<rho>) m master) \<longrightarrow> hamlet ((Rep_run \<rho>) m slave) }
          = { \<rho>. hamlet ((Rep_run \<rho>) n master) \<longrightarrow> hamlet ((Rep_run \<rho>) n slave) }
          \<inter> { \<rho>. \<forall>m\<ge>Suc n. hamlet ((Rep_run \<rho>) m master) \<longrightarrow> hamlet ((Rep_run \<rho>) m slave) }"
      by (smt Collect_cong Collect_conj_eq Suc_leD eq_refl le_antisym not_less_eq_eq)
    then show ?thesis by auto
  qed

lemma TESL_interp_stepwise_implies_not_coind_unfold:
  shows "\<lbrakk> master implies not slave \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup> =
    (\<lbrakk> master \<not>\<Up> n \<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m \<union> \<lbrakk> master \<Up> n \<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m \<inter> \<lbrakk> slave \<not>\<Up> n \<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m)
    \<inter> \<lbrakk> master implies not slave \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^esup>"
  proof -
    have "{ \<rho>. \<forall>m\<ge>n. hamlet ((Rep_run \<rho>) m master) \<longrightarrow> \<not> hamlet ((Rep_run \<rho>) m slave) }
          = { \<rho>. hamlet ((Rep_run \<rho>) n master) \<longrightarrow> \<not> hamlet ((Rep_run \<rho>) n slave) }
          \<inter> { \<rho>. \<forall>m\<ge>Suc n. hamlet ((Rep_run \<rho>) m master) \<longrightarrow> \<not> hamlet ((Rep_run \<rho>) m slave) }"
      by (smt Collect_cong Collect_conj_eq Suc_leD eq_refl le_antisym not_less_eq_eq)
    then show ?thesis by auto
  qed

lemma TESL_interp_stepwise_iff_coind_unfold:
  shows "\<lbrakk> K\<^sub>1 iff K\<^sub>2 \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup> =
    (\<lbrakk> K\<^sub>1 \<not>\<Up> n \<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m \<inter> \<lbrakk> K\<^sub>2 \<not>\<Up> n \<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m \<union> \<lbrakk> K\<^sub>1 \<Up> n \<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m \<inter> \<lbrakk> K\<^sub>2 \<Up> n \<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m)
    \<inter> \<lbrakk> K\<^sub>1 iff K\<^sub>2 \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^esup>"
  proof -
    have "{ \<rho>. \<forall>m\<ge>n. hamlet ((Rep_run \<rho>) m K\<^sub>1) \<longleftrightarrow> hamlet ((Rep_run \<rho>) m K\<^sub>2) }
          = { \<rho>. hamlet ((Rep_run \<rho>) n K\<^sub>1) \<longleftrightarrow> hamlet ((Rep_run \<rho>) n K\<^sub>2) }
          \<inter> { \<rho>. \<forall>m\<ge>Suc n. hamlet ((Rep_run \<rho>) m K\<^sub>1) \<longleftrightarrow> hamlet ((Rep_run \<rho>) m K\<^sub>2) }"
      by (smt Collect_cong Collect_conj_eq Suc_leD eq_refl le_antisym not_less_eq_eq)
    then show ?thesis by auto
  qed

lemma TESL_interp_stepwise_implies_anytime_coind_unfold:
  shows "\<lbrakk> master anytime implies slave \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup> =
    (\<lbrakk> master \<not>\<Up> n \<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m \<union> \<lbrakk> master \<Up> n \<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m \<inter> \<lbrakk> slave sporadic anytime \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup>)
    \<inter> \<lbrakk> master anytime implies slave \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^esup>"
  proof -
    have "{ \<rho>. \<forall>m\<ge>n. hamlet ((Rep_run \<rho>) m master) \<longrightarrow> (\<exists>p \<ge> m. hamlet ((Rep_run \<rho>) p slave)) }
         = { \<rho>. hamlet ((Rep_run \<rho>) n master) \<longrightarrow> (\<exists>p \<ge> n. hamlet ((Rep_run \<rho>) p slave)) }
         \<inter> { \<rho>. \<forall>m\<ge>Suc n. hamlet ((Rep_run \<rho>) m master) \<longrightarrow> (\<exists>p \<ge> m. hamlet ((Rep_run \<rho>) p slave)) }"
      by (smt Collect_cong Collect_conj_eq Suc_leD eq_refl le_antisym not_less_eq_eq)
    then show ?thesis by auto
  qed

lemma TESL_interp_stepwise_timedelayed_coind_unfold:
  shows "\<lbrakk> master time-delayed by \<delta>\<tau> on measuring implies slave \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup> =
    (\<lbrakk> master \<not>\<Up> n \<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m \<union> \<lbrakk> master \<Up> n \<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m \<inter> \<lbrakk> slave sporadic \<lfloor>\<tau>\<^sub>v\<^sub>a\<^sub>r(measuring, n) \<oplus> \<delta>\<tau>\<rfloor> on measuring \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup>)
    \<inter> \<lbrakk> master time-delayed by \<delta>\<tau> on measuring implies slave \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^esup>"
  proof -
    have "{ \<rho>. \<forall>m\<ge>n. hamlet ((Rep_run \<rho>) m master) \<longrightarrow>
                 (let measured_time = time ((Rep_run \<rho>) m measuring) in
                  \<exists>p \<ge> m. hamlet ((Rep_run \<rho>) p slave) \<and> time ((Rep_run \<rho>) p measuring) = measured_time + \<delta>\<tau>)}
         = { \<rho>. hamlet ((Rep_run \<rho>) n master) \<longrightarrow>
                 (let measured_time = time ((Rep_run \<rho>) n measuring) in
                  \<exists>p \<ge> n. hamlet ((Rep_run \<rho>) p slave) \<and> time ((Rep_run \<rho>) p measuring) = measured_time + \<delta>\<tau>)}
           \<inter> { \<rho>. \<forall>m\<ge>Suc n. hamlet ((Rep_run \<rho>) m master) \<longrightarrow>
                 (let measured_time = time ((Rep_run \<rho>) m measuring) in
                  \<exists>p \<ge> m. hamlet ((Rep_run \<rho>) p slave) \<and> time ((Rep_run \<rho>) p measuring) = measured_time + \<delta>\<tau>)}"
      by (smt Collect_cong Collect_conj_eq Suc_leD eq_refl le_antisym not_less_eq_eq)
    then show ?thesis by auto
  qed

fun TESL_interpretation_stepwise :: "TESL_formula \<Rightarrow> nat \<Rightarrow> run set" ("\<lbrakk>\<lbrakk> _ \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> _\<^esup>") where
    "\<lbrakk>\<lbrakk> [] \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup> = { _. True }"
  | "\<lbrakk>\<lbrakk> \<phi> # \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup> = \<lbrakk> \<phi> \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup> \<inter> \<lbrakk>\<lbrakk> \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup>"

lemma TESL_interpretation_stepwise_fixpoint:
  "\<lbrakk>\<lbrakk> \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup> = \<Inter> ((\<lambda>\<phi>. \<lbrakk> \<phi> \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup>) ` set \<Phi>)"
  proof (induct \<Phi>)
    case Nil
    then show ?case by simp
  next
    case (Cons a \<Phi>)
    then show ?case by auto
  qed

lemma TESL_interpretation_stepwise_zero:
  "\<lbrakk> \<phi> \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L = \<lbrakk> \<phi> \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> 0\<^esup>"
  proof (induct \<phi>)
    case (Not K)
    then show ?case by simp
  next
    case (SporadicAnytime K)
    then show ?case by simp
  next
    case (Sporadic x1 x2)
    then show ?case by simp
  next
    case (SporadicOn K\<^sub>1 \<tau> K\<^sub>2)
    then show ?case
      proof (induct \<tau>)
        case (Const x)
        then show ?case by simp
      next
        case (AddDelay tag x2)
        then show ?case
          proof (induct tag)
            case (Schematic xa)
            then show ?case
              proof (induct xa)
                case (Pair a b)
                then show ?case by auto
              qed
          qed
      qed
  next
    case (TagRelation x1 x2 x3 x4)
    then show ?case by simp
  next
    case (TagRelationGen x1 x2 x3)
    then show ?case by simp
  next
    case (Implies x1 x2)
    then show ?case by simp
  next
    case (ImpliesNot x1 x2)
    then show ?case by simp
  next
    case (Iff x1 x2)
    then show ?case by simp
  next
    case (ImpliesAnytime H1 H2)
    then show ?case by simp
  next
    case (TimeDelayedBy x1 x2 x3 x4)
    then show ?case by simp
  qed

lemma TESL_interpretation_stepwise_zero':
  "\<lbrakk>\<lbrakk> \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L = \<lbrakk>\<lbrakk> \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> 0\<^esup>"
  proof (induct \<Phi>)
    case Nil
    then show ?case by simp
  next
    case (Cons a \<Phi>)
    then show ?case
      by (simp add: TESL_interpretation_stepwise_zero)
  qed

lemma TESL_interpretation_stepwise_cons_morph:
  "\<lbrakk> \<phi> \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup> \<inter> \<lbrakk>\<lbrakk> \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup> = \<lbrakk>\<lbrakk> \<phi> # \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup>"
  by auto

theorem TESL_interp_stepwise_composition:
  shows "\<lbrakk>\<lbrakk> \<Phi>\<^sub>1 @ \<Phi>\<^sub>2 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup> = \<lbrakk>\<lbrakk> \<Phi>\<^sub>1 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup> \<inter> \<lbrakk>\<lbrakk> \<Phi>\<^sub>2 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup>"
  proof (induct \<Phi>\<^sub>1)
    case Nil
    then show ?case by simp
  next
    case (Cons a \<Phi>\<^sub>1)
    then show ?case by auto
  qed

section \<open>Interpretation of configurations\<close>

fun HeronConf_interpretation :: "config \<Rightarrow> run set" ("\<lbrakk> _ \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g" 71) where
  "\<lbrakk> \<Gamma>, n \<turnstile> \<Psi> \<triangleright> \<Phi> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g = \<lbrakk>\<lbrakk> \<Gamma> \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m \<inter> \<lbrakk>\<lbrakk> \<Psi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup> \<inter> \<lbrakk>\<lbrakk> \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^esup>"

lemma HeronConf_interp_composition:
  shows "\<lbrakk> \<Gamma>\<^sub>1, n \<turnstile> \<Psi>\<^sub>1 \<triangleright> \<Phi>\<^sub>1 \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g \<inter> \<lbrakk> \<Gamma>\<^sub>2, n \<turnstile> \<Psi>\<^sub>2 \<triangleright> \<Phi>\<^sub>2 \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g
         = \<lbrakk> \<Gamma>\<^sub>1 @ \<Gamma>\<^sub>2, n \<turnstile> \<Psi>\<^sub>1 @ \<Psi>\<^sub>2 \<triangleright> \<Phi>\<^sub>1 @ \<Phi>\<^sub>2 \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g"
  using TESL_interp_stepwise_composition symrun_interp_expansion by auto

lemma HeronConf_interp_stepwise_instant_cases:
  shows "\<lbrakk> \<Gamma>, n \<turnstile> [] \<triangleright> \<Phi> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g
          = \<lbrakk> \<Gamma>, Suc n \<turnstile> \<Phi> \<triangleright> [] \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g"
  proof -
    have "\<lbrakk> \<Gamma>, n \<turnstile> [] \<triangleright> \<Phi> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g = \<lbrakk>\<lbrakk> \<Gamma> \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m \<inter> \<lbrakk>\<lbrakk> [] \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup> \<inter> \<lbrakk>\<lbrakk> \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^esup>"
      by simp
    moreover have "\<lbrakk> \<Gamma>, Suc n \<turnstile> \<Phi> \<triangleright> [] \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g = \<lbrakk>\<lbrakk> \<Gamma> \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m \<inter> \<lbrakk>\<lbrakk> \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^esup> \<inter> \<lbrakk>\<lbrakk> [] \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^esup>"
      by simp
    moreover have "\<lbrakk>\<lbrakk> \<Gamma> \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m \<inter> \<lbrakk>\<lbrakk> [] \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup> \<inter> \<lbrakk>\<lbrakk> \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^esup>
                   = \<lbrakk>\<lbrakk> \<Gamma> \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m \<inter> \<lbrakk>\<lbrakk> \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^esup> \<inter> \<lbrakk>\<lbrakk> [] \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^esup>"
      by simp
    ultimately show ?thesis by blast
  qed

lemma HeronConf_interp_stepwise_not_cases:
  shows "\<lbrakk> \<Gamma>, n \<turnstile> (not K) # \<Psi> \<triangleright> \<Phi> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g
          = \<lbrakk> K \<not>\<Up> n # \<Gamma>, n \<turnstile> \<Psi> \<triangleright> (not K) # \<Phi> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g"
  proof -
    have "\<lbrakk>  \<Gamma>, n \<turnstile> (not K) # \<Psi> \<triangleright> \<Phi> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g = \<lbrakk>\<lbrakk> \<Gamma> \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m \<inter> \<lbrakk>\<lbrakk> (not K) # \<Psi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup> \<inter> \<lbrakk>\<lbrakk> \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^esup>"
      by simp
    moreover have "\<lbrakk> K \<not>\<Up> n # \<Gamma>, n \<turnstile> \<Psi> \<triangleright> (not K) # \<Phi> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g
                      = \<lbrakk>\<lbrakk> K \<not>\<Up> n # \<Gamma> \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m \<inter> \<lbrakk>\<lbrakk> \<Psi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup> \<inter> \<lbrakk>\<lbrakk> (not K) # \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^esup>"
      by simp
    ultimately show ?thesis
      proof -
        have "\<lbrakk> K \<not>\<Up> n \<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m \<inter> \<lbrakk> not K \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^esup> \<inter> \<lbrakk>\<lbrakk> \<Psi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup> = \<lbrakk>\<lbrakk> (not K) # \<Psi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup>"
          using TESL_interp_stepwise_not_coind_unfold TESL_interpretation_stepwise_cons_morph by blast
        then show ?thesis
          by auto
      qed
  qed

lemma HeronConf_interp_stepwise_sporadic_anytime_cases:
  shows "\<lbrakk> \<Gamma>, n \<turnstile> (K sporadic anytime) # \<Psi> \<triangleright> \<Phi> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g
          = \<lbrakk> \<Gamma>, n \<turnstile> \<Psi> \<triangleright> (K sporadic anytime) # \<Phi> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g
          \<union> \<lbrakk> K \<Up> n # \<Gamma>, n \<turnstile> \<Psi> \<triangleright> \<Phi> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g"
  proof -
    have "\<lbrakk> \<Gamma>, n \<turnstile> (K sporadic anytime) # \<Psi> \<triangleright> \<Phi> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g = \<lbrakk>\<lbrakk> \<Gamma> \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m \<inter> \<lbrakk>\<lbrakk> (K sporadic anytime) # \<Psi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup> \<inter> \<lbrakk>\<lbrakk> \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^esup>"
      by simp
    moreover have "\<lbrakk> \<Gamma>, n \<turnstile> \<Psi> \<triangleright> (K sporadic anytime) # \<Phi> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g = \<lbrakk>\<lbrakk> \<Gamma> \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m \<inter> \<lbrakk>\<lbrakk> \<Psi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup> \<inter> \<lbrakk>\<lbrakk> (K sporadic anytime) # \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^esup>"
      by simp
    moreover have "\<lbrakk> K \<Up> n # \<Gamma>, n \<turnstile> \<Psi> \<triangleright> \<Phi> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g = \<lbrakk>\<lbrakk> K \<Up> n # \<Gamma> \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m \<inter> \<lbrakk>\<lbrakk> \<Psi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup> \<inter> \<lbrakk>\<lbrakk> \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^esup>"
      by simp
    ultimately show ?thesis
      by (smt TESL_interp_stepwise_sporadic_anytime_coind_unfold TESL_interpretation_stepwise_cons_morph inf.commute inf_sup_aci(2) inf_sup_distrib2 sup_commute symbolic_run_interpretation.simps(2))
  qed

lemma HeronConf_interp_stepwise_sporadic_cases:
  shows "\<lbrakk> \<Gamma>, n \<turnstile> (K sporadic \<tau>) # \<Psi> \<triangleright> \<Phi> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g
          = \<lbrakk> \<Gamma>, n \<turnstile> \<Psi> \<triangleright> (K sporadic \<tau>) # \<Phi> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g
          \<union> \<lbrakk> K \<Up> n # K \<Down> n @ \<lfloor>\<tau>\<rfloor> # \<Gamma>, n \<turnstile> \<Psi> \<triangleright> \<Phi> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g"
  proof -
    have "\<lbrakk> \<Gamma>, n \<turnstile> (K sporadic \<tau>) # \<Psi> \<triangleright> \<Phi> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g = \<lbrakk>\<lbrakk> \<Gamma> \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m \<inter> \<lbrakk>\<lbrakk> (K sporadic \<tau>) # \<Psi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup> \<inter> \<lbrakk>\<lbrakk> \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^esup>"
      by simp
    moreover have "\<lbrakk> \<Gamma>, n \<turnstile> \<Psi> \<triangleright> (K sporadic \<tau>) # \<Phi> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g = \<lbrakk>\<lbrakk> \<Gamma> \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m \<inter> \<lbrakk>\<lbrakk> \<Psi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup> \<inter> \<lbrakk>\<lbrakk> (K sporadic \<tau>) # \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^esup>"
      by simp
    moreover have "\<lbrakk> K \<Up> n # K \<Down> n @ \<lfloor>\<tau>\<rfloor> # \<Gamma>, n \<turnstile> \<Psi> \<triangleright> \<Phi> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g = \<lbrakk>\<lbrakk> K \<Up> n # K \<Down> n @ \<lfloor>\<tau>\<rfloor> # \<Gamma> \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m \<inter> \<lbrakk>\<lbrakk> \<Psi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup> \<inter> \<lbrakk>\<lbrakk> \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^esup>"
      by simp
    ultimately show ?thesis
    proof -
      have "(\<lbrakk> K \<Up> n \<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m \<inter> \<lbrakk> K \<Down> n @ \<lfloor> \<tau> \<rfloor> \<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m \<union> \<lbrakk> K sporadic \<tau> \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^esup>) \<inter> \<lbrakk>\<lbrakk> \<Psi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup> = \<lbrakk>\<lbrakk> (K sporadic \<tau>) # \<Psi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup>"
        using TESL_interp_stepwise_sporadic_coind_unfold TESL_interpretation_stepwise_cons_morph by blast
  then have "\<lbrakk> \<Gamma>, n \<turnstile> (K sporadic \<tau>) # \<Psi> \<triangleright> \<Phi> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g = (\<lbrakk>\<lbrakk> K \<Up> n # K \<Down> n @ \<lfloor> \<tau> \<rfloor> # \<Gamma> \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m \<inter> \<lbrakk>\<lbrakk> \<Psi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup> \<union> \<lbrakk>\<lbrakk> \<Gamma> \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m \<inter> \<lbrakk>\<lbrakk> \<Psi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup> \<inter> \<lbrakk> K sporadic \<tau> \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^esup>) \<inter> \<lbrakk>\<lbrakk> \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^esup>"
    by auto
      then show ?thesis
        by (simp add: Int_Un_distrib2 Int_assoc Un_commute)
    qed
  qed

lemma HeronConf_interp_stepwise_sporadicon_cases:
  shows "\<lbrakk> \<Gamma>, n \<turnstile> (K\<^sub>1 sporadic \<tau> on K\<^sub>2) # \<Psi> \<triangleright> \<Phi> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g
          = \<lbrakk> \<Gamma>, n \<turnstile> \<Psi> \<triangleright> (K\<^sub>1 sporadic \<tau> on K\<^sub>2) # \<Phi> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g
          \<union> \<lbrakk> K\<^sub>1 \<Up> n # K\<^sub>2 \<Down> n @ \<tau> # \<Gamma>, n \<turnstile> \<Psi> \<triangleright> \<Phi> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g"
  proof -
    have "\<lbrakk> \<Gamma>, n \<turnstile> (K\<^sub>1 sporadic \<tau> on K\<^sub>2) # \<Psi> \<triangleright> \<Phi> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g = \<lbrakk>\<lbrakk> \<Gamma> \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m \<inter> \<lbrakk>\<lbrakk> (K\<^sub>1 sporadic \<tau> on K\<^sub>2) # \<Psi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup> \<inter> \<lbrakk>\<lbrakk> \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^esup>"
      by simp
    moreover have "\<lbrakk> \<Gamma>, n \<turnstile> \<Psi> \<triangleright> (K\<^sub>1 sporadic \<tau> on K\<^sub>2) # \<Phi> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g = \<lbrakk>\<lbrakk> \<Gamma> \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m \<inter> \<lbrakk>\<lbrakk> \<Psi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup> \<inter> \<lbrakk>\<lbrakk> (K\<^sub>1 sporadic \<tau> on K\<^sub>2) # \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^esup>"
      by simp
    moreover have "\<lbrakk> K\<^sub>1 \<Up> n # K\<^sub>2 \<Down> n @ \<tau> # \<Gamma>, n \<turnstile> \<Psi> \<triangleright> \<Phi> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g = \<lbrakk>\<lbrakk> K\<^sub>1 \<Up> n # K\<^sub>2 \<Down> n @ \<tau> # \<Gamma> \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m \<inter> \<lbrakk>\<lbrakk> \<Psi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup> \<inter> \<lbrakk>\<lbrakk> \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^esup>"
      by simp
    ultimately show ?thesis
    proof -
      have "(\<lbrakk> K\<^sub>1 \<Up> n \<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m \<inter> \<lbrakk> K\<^sub>2 \<Down> n @ \<tau> \<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m \<union> \<lbrakk> K\<^sub>1 sporadic \<tau> on K\<^sub>2 \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^esup>) \<inter> (\<lbrakk>\<lbrakk> \<Gamma> \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m \<inter> \<lbrakk>\<lbrakk> \<Psi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup>) = \<lbrakk> K\<^sub>1 sporadic \<tau> on K\<^sub>2 \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup> \<inter> (\<lbrakk>\<lbrakk> \<Psi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup> \<inter> \<lbrakk>\<lbrakk> \<Gamma> \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m)"
        using TESL_interp_stepwise_sporadicon_coind_unfold by blast
      then have "\<lbrakk>\<lbrakk> K\<^sub>1 \<Up> n # K\<^sub>2 \<Down> n @ \<tau> # \<Gamma> \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m \<inter> \<lbrakk>\<lbrakk> \<Psi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup> \<union> \<lbrakk>\<lbrakk> \<Gamma> \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m \<inter> \<lbrakk>\<lbrakk> \<Psi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup> \<inter> \<lbrakk> K\<^sub>1 sporadic \<tau> on K\<^sub>2 \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^esup> = \<lbrakk>\<lbrakk> (K\<^sub>1 sporadic \<tau> on K\<^sub>2) # \<Psi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup> \<inter> \<lbrakk>\<lbrakk> \<Gamma> \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m"
        by auto
      then show ?thesis
        by auto
    qed
  qed

lemma HeronConf_interp_stepwise_tagrel_cases:
  shows "\<lbrakk> \<Gamma>, n \<turnstile> (tag-relation K\<^sub>1 = \<alpha> * K\<^sub>2 + \<beta>) # \<Psi> \<triangleright> \<Phi> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g
          = \<lbrakk> (\<tau>\<^sub>v\<^sub>a\<^sub>r(K\<^sub>1, n) \<doteq> \<alpha> * \<tau>\<^sub>v\<^sub>a\<^sub>r(K\<^sub>2, n) + \<beta>) # \<Gamma>, n \<turnstile> \<Psi> \<triangleright> (tag-relation K\<^sub>1 = \<alpha> * K\<^sub>2 + \<beta>) # \<Phi> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g"
  proof -
    have "\<lbrakk> \<Gamma>, n \<turnstile> (tag-relation K\<^sub>1 = \<alpha> * K\<^sub>2 + \<beta>) # \<Psi> \<triangleright> \<Phi> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g = \<lbrakk>\<lbrakk> \<Gamma> \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m \<inter> \<lbrakk>\<lbrakk> (tag-relation K\<^sub>1 = \<alpha> * K\<^sub>2 + \<beta>) # \<Psi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup> \<inter> \<lbrakk>\<lbrakk> \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^esup>"
      by simp
    moreover have "\<lbrakk> (\<tau>\<^sub>v\<^sub>a\<^sub>r(K\<^sub>1, n) \<doteq> \<alpha> * \<tau>\<^sub>v\<^sub>a\<^sub>r(K\<^sub>2, n) + \<beta>) # \<Gamma>, n \<turnstile> \<Psi> \<triangleright> (tag-relation K\<^sub>1 = \<alpha> * K\<^sub>2 + \<beta>) # \<Phi> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g
                      = \<lbrakk>\<lbrakk> (\<tau>\<^sub>v\<^sub>a\<^sub>r(K\<^sub>1, n) \<doteq> \<alpha> * \<tau>\<^sub>v\<^sub>a\<^sub>r(K\<^sub>2, n) + \<beta>) # \<Gamma> \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m \<inter> \<lbrakk>\<lbrakk> \<Psi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup> \<inter> \<lbrakk>\<lbrakk> (tag-relation K\<^sub>1 = \<alpha> * K\<^sub>2 + \<beta>) # \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^esup>"
      by simp
    ultimately show ?thesis
    proof -
      have "\<lbrakk> \<tau>\<^sub>v\<^sub>a\<^sub>r (K\<^sub>1, n) \<doteq> \<alpha> * \<tau>\<^sub>v\<^sub>a\<^sub>r (K\<^sub>2, n) + \<beta> \<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m \<inter> \<lbrakk> tag-relation K\<^sub>1 = \<alpha> * K\<^sub>2 + \<beta> \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^esup> \<inter> \<lbrakk>\<lbrakk> \<Psi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup> = \<lbrakk>\<lbrakk> (tag-relation K\<^sub>1 = \<alpha> * K\<^sub>2 + \<beta>) # \<Psi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup>"
        using TESL_interp_stepwise_tagrel_coind_unfold TESL_interpretation_stepwise_cons_morph by blast
      then show ?thesis
        by auto
    qed
  qed

lemma HeronConf_interp_stepwise_tagrelgen_cases:
  shows "\<lbrakk> \<Gamma>, n \<turnstile> (tag-relation \<langle>K\<^sub>1, K\<^sub>2\<rangle> \<in> R) # \<Psi> \<triangleright> \<Phi> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g
          = \<lbrakk> (\<langle>\<tau>\<^sub>v\<^sub>a\<^sub>r(K\<^sub>1, n), \<tau>\<^sub>v\<^sub>a\<^sub>r(K\<^sub>2, n)\<rangle> \<epsilon> R) # \<Gamma>, n \<turnstile> \<Psi> \<triangleright> (tag-relation \<langle>K\<^sub>1, K\<^sub>2\<rangle> \<in> R) # \<Phi> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g"
  proof -
    have "\<lbrakk> \<Gamma>, n \<turnstile> (tag-relation \<langle>K\<^sub>1, K\<^sub>2\<rangle> \<in> R) # \<Psi> \<triangleright> \<Phi> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g = \<lbrakk>\<lbrakk> \<Gamma> \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m \<inter> \<lbrakk>\<lbrakk> (tag-relation \<langle>K\<^sub>1, K\<^sub>2\<rangle> \<in> R) # \<Psi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup> \<inter> \<lbrakk>\<lbrakk> \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^esup>"
      by simp
    moreover have "\<lbrakk> (\<langle>\<tau>\<^sub>v\<^sub>a\<^sub>r(K\<^sub>1, n), \<tau>\<^sub>v\<^sub>a\<^sub>r(K\<^sub>2, n)\<rangle> \<epsilon> R) # \<Gamma>, n \<turnstile> \<Psi> \<triangleright> (tag-relation \<langle>K\<^sub>1, K\<^sub>2\<rangle> \<in> R) # \<Phi> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g
                      = \<lbrakk>\<lbrakk> (\<langle>\<tau>\<^sub>v\<^sub>a\<^sub>r(K\<^sub>1, n), \<tau>\<^sub>v\<^sub>a\<^sub>r(K\<^sub>2, n)\<rangle> \<epsilon> R) # \<Gamma> \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m \<inter> \<lbrakk>\<lbrakk> \<Psi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup> \<inter> \<lbrakk>\<lbrakk> (tag-relation \<langle>K\<^sub>1, K\<^sub>2\<rangle> \<in> R) # \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^esup>"
      by simp
    ultimately show ?thesis
    proof -
      have "\<lbrakk> \<langle>\<tau>\<^sub>v\<^sub>a\<^sub>r(K\<^sub>1, n), \<tau>\<^sub>v\<^sub>a\<^sub>r(K\<^sub>2, n)\<rangle> \<epsilon> R \<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m \<inter> \<lbrakk> tag-relation \<langle>K\<^sub>1, K\<^sub>2\<rangle> \<in> R \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^esup> \<inter> \<lbrakk>\<lbrakk> \<Psi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup> = \<lbrakk>\<lbrakk> (tag-relation \<langle>K\<^sub>1, K\<^sub>2\<rangle> \<in> R) # \<Psi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup>"
        using TESL_interp_stepwise_tagrelgen_coind_unfold TESL_interpretation_stepwise_cons_morph by blast
      then show ?thesis
        by auto
    qed
  qed

lemma HeronConf_interp_stepwise_implies_cases:
  shows "\<lbrakk> \<Gamma>, n \<turnstile> (K\<^sub>1 implies K\<^sub>2) # \<Psi> \<triangleright> \<Phi> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g
          = \<lbrakk> K\<^sub>1 \<not>\<Up> n # \<Gamma>, n \<turnstile> \<Psi> \<triangleright> (K\<^sub>1 implies K\<^sub>2) # \<Phi> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g
          \<union> \<lbrakk> K\<^sub>1 \<Up> n # K\<^sub>2 \<Up> n # \<Gamma>, n \<turnstile> \<Psi> \<triangleright> (K\<^sub>1 implies K\<^sub>2) # \<Phi> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g"
  proof -
    have "\<lbrakk> \<Gamma>, n \<turnstile> (K\<^sub>1 implies K\<^sub>2) # \<Psi> \<triangleright> \<Phi> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g = \<lbrakk>\<lbrakk> \<Gamma> \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m \<inter> \<lbrakk>\<lbrakk> (K\<^sub>1 implies K\<^sub>2) # \<Psi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup> \<inter> \<lbrakk>\<lbrakk> \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^esup>"
      by simp
    moreover have "\<lbrakk> K\<^sub>1 \<not>\<Up> n # \<Gamma>, n \<turnstile> \<Psi> \<triangleright> (K\<^sub>1 implies K\<^sub>2) # \<Phi> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g = \<lbrakk>\<lbrakk> K\<^sub>1 \<not>\<Up> n # \<Gamma> \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m \<inter> \<lbrakk>\<lbrakk> \<Psi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup> \<inter> \<lbrakk>\<lbrakk> (K\<^sub>1 implies K\<^sub>2) # \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^esup>"
      by simp
    moreover have "\<lbrakk> K\<^sub>1 \<Up> n # K\<^sub>2 \<Up> n # \<Gamma>, n \<turnstile> \<Psi> \<triangleright> (K\<^sub>1 implies K\<^sub>2) # \<Phi> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g = \<lbrakk>\<lbrakk> K\<^sub>1 \<Up> n # K\<^sub>2 \<Up> n # \<Gamma> \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m \<inter> \<lbrakk>\<lbrakk> \<Psi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup> \<inter> \<lbrakk>\<lbrakk> (K\<^sub>1 implies K\<^sub>2) # \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^esup>"
      by simp
    ultimately show ?thesis
    proof -
      have f1: "(\<lbrakk> K\<^sub>1 \<not>\<Up> n \<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m \<union> \<lbrakk> K\<^sub>1 \<Up> n \<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m \<inter> \<lbrakk> K\<^sub>2 \<Up> n \<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m) \<inter> \<lbrakk> K\<^sub>1 implies K\<^sub>2 \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^esup> \<inter> (\<lbrakk>\<lbrakk> \<Psi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup> \<inter> \<lbrakk>\<lbrakk> \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^esup>) = \<lbrakk>\<lbrakk> (K\<^sub>1 implies K\<^sub>2) # \<Psi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup> \<inter> \<lbrakk>\<lbrakk> \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^esup>"
        using TESL_interp_stepwise_implies_coind_unfold TESL_interpretation_stepwise_cons_morph by blast
      have "\<lbrakk> K\<^sub>1 \<not>\<Up> n \<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m \<inter> \<lbrakk>\<lbrakk> \<Gamma> \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m \<union> \<lbrakk> K\<^sub>1 \<Up> n \<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m \<inter> \<lbrakk>\<lbrakk> K\<^sub>2 \<Up> n # \<Gamma> \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m = (\<lbrakk> K\<^sub>1 \<not>\<Up> n \<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m \<union> \<lbrakk> K\<^sub>1 \<Up> n \<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m \<inter> \<lbrakk> K\<^sub>2 \<Up> n \<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m) \<inter> \<lbrakk>\<lbrakk> \<Gamma> \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m"
        by force
      then have "\<lbrakk> \<Gamma>, n \<turnstile> (K\<^sub>1 implies K\<^sub>2) # \<Psi> \<triangleright> \<Phi> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g = (\<lbrakk> K\<^sub>1 \<not>\<Up> n \<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m \<inter> \<lbrakk>\<lbrakk> \<Gamma> \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m \<union> \<lbrakk> K\<^sub>1 \<Up> n \<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m \<inter> \<lbrakk>\<lbrakk> K\<^sub>2 \<Up> n # \<Gamma> \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m) \<inter> (\<lbrakk>\<lbrakk> \<Psi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup> \<inter> \<lbrakk>\<lbrakk> (K\<^sub>1 implies K\<^sub>2) # \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^esup>)"
        using f1 by (simp add: inf_left_commute inf_sup_aci(2))
      then show ?thesis
        by (simp add: Int_Un_distrib2 inf_sup_aci(2))
    qed
  qed

lemma HeronConf_interp_stepwise_implies_not_cases:
  shows "\<lbrakk> \<Gamma>, n \<turnstile> (K\<^sub>1 implies not K\<^sub>2) # \<Psi> \<triangleright> \<Phi> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g
          = \<lbrakk> (K\<^sub>1 \<not>\<Up> n) # \<Gamma>, n \<turnstile> \<Psi> \<triangleright> (K\<^sub>1 implies not K\<^sub>2) # \<Phi> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g
          \<union> \<lbrakk> (K\<^sub>1 \<Up> n) # (K\<^sub>2 \<not>\<Up> n) # \<Gamma>, n \<turnstile> \<Psi> \<triangleright> (K\<^sub>1 implies not K\<^sub>2) # \<Phi> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g"
  by (smt HeronConf_interpretation.simps Int_commute Int_left_commute TESL_interp_stepwise_implies_not_coind_unfold
      TESL_interpretation_stepwise_cons_morph inf_sup_distrib2 symbolic_run_interp_cons_morph)

lemma HeronConf_interp_stepwise_iff_cases:
  shows "\<lbrakk> \<Gamma>, n \<turnstile> (K\<^sub>1 iff K\<^sub>2) # \<Psi> \<triangleright> \<Phi> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g
          = \<lbrakk> (K\<^sub>1 \<not>\<Up> n) # (K\<^sub>2 \<not>\<Up> n) # \<Gamma>, n \<turnstile> \<Psi> \<triangleright> (K\<^sub>1 iff K\<^sub>2) # \<Phi> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g
          \<union> \<lbrakk> (K\<^sub>1 \<Up> n) # (K\<^sub>2 \<Up> n) # \<Gamma>, n \<turnstile> \<Psi> \<triangleright> (K\<^sub>1 iff K\<^sub>2) # \<Phi> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g"
  by (smt HeronConf_interpretation.simps Int_commute Int_left_commute TESL_interp_stepwise_iff_coind_unfold
      TESL_interpretation_stepwise_cons_morph inf_sup_distrib2 symbolic_run_interpretation.simps(2))

lemma HeronConf_interp_stepwise_implies_anytime_cases:
  shows "\<lbrakk> \<Gamma>, n \<turnstile> (master anytime implies slave) # \<Psi> \<triangleright> \<Phi> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g
          = \<lbrakk> master \<not>\<Up> n # \<Gamma>, n \<turnstile> \<Psi> \<triangleright> (master anytime implies slave) # \<Phi> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g
          \<union> \<lbrakk> master \<Up> n # \<Gamma>, n \<turnstile> (slave sporadic anytime) # \<Psi> \<triangleright> (master anytime implies slave) # \<Phi> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g"
  by (smt HeronConf_interpretation.simps Int_ac(3) Int_ac(4) TESL_interp_stepwise_implies_anytime_coind_unfold
      TESL_interpretation_stepwise_cons_morph distrib(4) symbolic_run_interpretation.simps(2))

lemma HeronConf_interp_stepwise_timedelayed_cases:
  shows "\<lbrakk> \<Gamma>, n \<turnstile> (K\<^sub>1 time-delayed by \<delta>\<tau> on K\<^sub>2 implies K\<^sub>3) # \<Psi> \<triangleright> \<Phi> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g
          = \<lbrakk> K\<^sub>1 \<not>\<Up> n # \<Gamma>, n \<turnstile> \<Psi> \<triangleright> (K\<^sub>1 time-delayed by \<delta>\<tau> on K\<^sub>2 implies K\<^sub>3) # \<Phi> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g
          \<union> \<lbrakk> K\<^sub>1 \<Up> n # \<Gamma>, n \<turnstile> (K\<^sub>3 sporadic \<lfloor>\<tau>\<^sub>v\<^sub>a\<^sub>r(K\<^sub>2, n) \<oplus> \<delta>\<tau>\<rfloor> on K\<^sub>2) # \<Psi> \<triangleright> (K\<^sub>1 time-delayed by \<delta>\<tau> on K\<^sub>2 implies K\<^sub>3) # \<Phi> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g"
  proof -
    have "\<lbrakk> \<Gamma>, n \<turnstile> (K\<^sub>1 time-delayed by \<delta>\<tau> on K\<^sub>2 implies K\<^sub>3) # \<Psi> \<triangleright> \<Phi> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g
           = \<lbrakk>\<lbrakk> \<Gamma> \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m \<inter> \<lbrakk>\<lbrakk> (K\<^sub>1 time-delayed by \<delta>\<tau> on K\<^sub>2 implies K\<^sub>3) # \<Psi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup> \<inter> \<lbrakk>\<lbrakk> \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^esup>"
      by simp
    moreover have "\<lbrakk> K\<^sub>1 \<not>\<Up> n # \<Gamma>, n \<turnstile> \<Psi> \<triangleright> (K\<^sub>1 time-delayed by \<delta>\<tau> on K\<^sub>2 implies K\<^sub>3) # \<Phi> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g
                     = \<lbrakk>\<lbrakk> K\<^sub>1 \<not>\<Up> n # \<Gamma> \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m \<inter> \<lbrakk>\<lbrakk> \<Psi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup> \<inter> \<lbrakk>\<lbrakk> (K\<^sub>1 time-delayed by \<delta>\<tau> on K\<^sub>2 implies K\<^sub>3) # \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^esup>"
      by simp
    moreover have "\<lbrakk> K\<^sub>1 \<Up> n # \<Gamma>, n \<turnstile> (K\<^sub>3 sporadic \<lfloor>\<tau>\<^sub>v\<^sub>a\<^sub>r(K\<^sub>2, n) \<oplus> \<delta>\<tau>\<rfloor> on K\<^sub>2) # \<Psi> \<triangleright> (K\<^sub>1 time-delayed by \<delta>\<tau> on K\<^sub>2 implies K\<^sub>3) # \<Phi> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g
                     = \<lbrakk>\<lbrakk> K\<^sub>1 \<Up> n # \<Gamma> \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m \<inter> \<lbrakk>\<lbrakk> (K\<^sub>3 sporadic \<lfloor>\<tau>\<^sub>v\<^sub>a\<^sub>r(K\<^sub>2, n) \<oplus> \<delta>\<tau>\<rfloor> on K\<^sub>2) # \<Psi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup>
                     \<inter> \<lbrakk>\<lbrakk> (K\<^sub>1 time-delayed by \<delta>\<tau> on K\<^sub>2 implies K\<^sub>3) # \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^esup>"
      by simp
    ultimately show ?thesis
    proof -
      have "\<lbrakk> \<Gamma>, n \<turnstile> (K\<^sub>1 time-delayed by \<delta>\<tau> on K\<^sub>2 implies K\<^sub>3) # \<Psi> \<triangleright> \<Phi> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g = \<lbrakk>\<lbrakk> \<Gamma> \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m \<inter> (\<lbrakk>\<lbrakk> (K\<^sub>1 time-delayed by \<delta>\<tau> on K\<^sub>2 implies K\<^sub>3) # \<Psi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup> \<inter> \<lbrakk>\<lbrakk> \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^esup>)"
        using \<open>\<lbrakk> \<Gamma>, n \<turnstile> (K\<^sub>1 time-delayed by \<delta>\<tau> on K\<^sub>2 implies K\<^sub>3) # \<Psi> \<triangleright> \<Phi> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g = \<lbrakk>\<lbrakk> \<Gamma> \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m \<inter> \<lbrakk>\<lbrakk> (K\<^sub>1 time-delayed by \<delta>\<tau> on K\<^sub>2 implies K\<^sub>3) # \<Psi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup> \<inter> \<lbrakk>\<lbrakk> \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^esup>\<close> by blast
      then have "\<lbrakk> \<Gamma>, n \<turnstile> (K\<^sub>1 time-delayed by \<delta>\<tau> on K\<^sub>2 implies K\<^sub>3) # \<Psi> \<triangleright> \<Phi> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g = (\<lbrakk> K\<^sub>1 \<not>\<Up> n \<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m \<union> \<lbrakk> K\<^sub>1 \<Up> n \<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m \<inter> \<lbrakk> K\<^sub>3 sporadic \<lfloor> \<tau>\<^sub>v\<^sub>a\<^sub>r (K\<^sub>2, n) \<oplus> \<delta>\<tau> \<rfloor> on K\<^sub>2 \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup>) \<inter> (\<lbrakk>\<lbrakk> \<Gamma> \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m \<inter> (\<lbrakk>\<lbrakk> \<Psi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup> \<inter> \<lbrakk>\<lbrakk> (K\<^sub>1 time-delayed by \<delta>\<tau> on K\<^sub>2 implies K\<^sub>3) # \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^esup>))"
        using TESL_interp_stepwise_timedelayed_coind_unfold TESL_interpretation_stepwise_cons_morph by blast
      then show ?thesis
        by auto
    qed
  qed

end
