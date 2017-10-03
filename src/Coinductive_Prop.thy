theory Coinductive_Prop
imports
  "Operational"
  "Denotational"

begin

section \<open>Coinductive version of denotational semantics\<close>

(**) section \<open>Denotational interpretation for atoms bounded by index\<close> (**)

(* Denotational interpretation of TESL bounded by index *)
fun TESL_interpretation_primitive_at_index
    :: "TESL_atomic \<Rightarrow> nat \<Rightarrow> run set" ("\<lbrakk> _ \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> _\<^esup>") where
    "\<lbrakk> K sporadic \<tau> \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> i\<^esup> =
        { \<rho>. \<exists>n\<ge>i. hamlet ((Rep_run \<rho>) n K) = True \<and> time ((Rep_run \<rho>) n K) = \<tau> }"
  | "\<lbrakk> K\<^sub>1 sporadic \<lfloor>\<tau>\<rfloor> on K\<^sub>2 \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> i\<^esup> =
        { \<rho>. \<exists>n\<ge>i. hamlet ((Rep_run \<rho>) n K\<^sub>1) = True \<and> time ((Rep_run \<rho>) n K\<^sub>2) = \<tau> }"
  | "\<lbrakk> K\<^sub>1 sporadic \<lfloor>\<tau>\<^sub>v\<^sub>a\<^sub>r(K\<^sub>p\<^sub>a\<^sub>s\<^sub>t, n\<^sub>p\<^sub>a\<^sub>s\<^sub>t) \<oplus> \<delta>\<tau>\<rfloor> on K\<^sub>2 \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> i\<^esup> =
        { \<rho>. \<exists>n\<ge>i. hamlet ((Rep_run \<rho>) n K\<^sub>1) = True
                         \<and> time ((Rep_run \<rho>) n K\<^sub>2) = time ((Rep_run \<rho>) n\<^sub>p\<^sub>a\<^sub>s\<^sub>t K\<^sub>p\<^sub>a\<^sub>s\<^sub>t) + \<delta>\<tau> }"
  | "\<lbrakk> tag-relation K\<^sub>1 = \<alpha> * K\<^sub>2 + \<beta> \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> i\<^esup> =
        { \<rho>. \<forall>n\<ge>i. time ((Rep_run \<rho>) n K\<^sub>1) = \<alpha> * time ((Rep_run \<rho>) n K\<^sub>2) + \<beta> }"
  | "\<lbrakk> master implies slave \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> i\<^esup> =
        { \<rho>. \<forall>n\<ge>i. hamlet ((Rep_run \<rho>) n master) \<longrightarrow> hamlet ((Rep_run \<rho>) n slave) }"
  | "\<lbrakk> master time-delayed by \<delta>\<tau> on measuring implies slave \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> i\<^esup> =
        { \<rho>. \<forall>n\<ge>i. hamlet ((Rep_run \<rho>) n master) \<longrightarrow>
                 (let measured_time = time ((Rep_run \<rho>) n measuring) in
                  \<exists>m \<ge> n. hamlet ((Rep_run \<rho>) m slave)
                          \<and> time ((Rep_run \<rho>) m measuring) = measured_time + \<delta>\<tau>
                 )
        }"

theorem predicate_Inter_unfold:
  "{ \<rho>. \<forall>n. P \<rho> n} = \<Inter> {Y. \<exists>n. Y = { \<rho>. P \<rho> n }}"
  by (simp add: Collect_all_eq full_SetCompr_eq)

theorem predicate_Union_unfold:
  "{ \<rho>. \<exists>n. P \<rho> n} = \<Union> {Y. \<exists>n. Y = { \<rho>. P \<rho> n }}"
  by auto

lemma TESL_interp_unfold_at_index_sporadic:
  shows "\<lbrakk> K sporadic \<tau> \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L = \<Union> {Y. \<exists>n::nat. Y = \<lbrakk> K sporadic \<tau> \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup>}"
  by auto

lemma TESL_interp_unfold_at_index_sporadicon:
  shows "\<lbrakk> K\<^sub>1 sporadic \<lfloor>\<tau>\<rfloor> on K\<^sub>2 \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L = \<Union> {Y. \<exists>n::nat. Y = \<lbrakk> K\<^sub>1 sporadic \<lfloor>\<tau>\<rfloor> on K\<^sub>2 \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup>}"
  by auto

lemma TESL_interp_unfold_at_index_sporadicon_add:
  shows "\<lbrakk> K\<^sub>1 sporadic \<lfloor>\<tau>\<^sub>v\<^sub>a\<^sub>r(K, n') \<oplus> \<tau>\<rfloor> on K\<^sub>2 \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L = \<Union> {Y. \<exists>n::nat. Y = \<lbrakk> K\<^sub>1 sporadic \<lfloor>\<tau>\<^sub>v\<^sub>a\<^sub>r(K, n') \<oplus> \<tau>\<rfloor> on K\<^sub>2 \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup>}"
  by auto

lemma TESL_interp_unfold_at_index_tagrel:
  shows "\<lbrakk> tag-relation K\<^sub>1 = \<alpha> * K\<^sub>2 + \<beta> \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L = \<Inter> {Y. \<exists>n::nat. Y = \<lbrakk> tag-relation K\<^sub>1 = \<alpha> * K\<^sub>2 + \<beta> \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup>}"
  by auto

lemma TESL_interp_unfold_at_index_implies:
  shows "\<lbrakk> master implies slave \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L = \<Inter> {Y. \<exists>n::nat. Y = \<lbrakk> master implies slave \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup>}"
  by auto

lemma TESL_interp_unfold_at_index_timedelayed:
  shows "\<lbrakk> master time-delayed by \<delta>\<tau> on measuring implies slave \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L
    = \<Inter> {Y. \<exists>n::nat. Y = \<lbrakk> master time-delayed by \<delta>\<tau> on measuring implies slave \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup>}"
  by auto

theorem TESL_interp_unfold_at_index_positive_atoms:
  assumes "positive_atom \<phi>"
  shows "\<lbrakk> \<phi> \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L = \<Union> {Y. \<exists>n::nat. Y = \<lbrakk> \<phi> \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup>}"
  proof -
    obtain cc :: "TESL_atomic \<Rightarrow> clock" and tt :: "TESL_atomic \<Rightarrow> tag_const" and cca :: "TESL_atomic \<Rightarrow> clock" and tta :: "TESL_atomic \<Rightarrow> tag_expr" and ccb :: "TESL_atomic \<Rightarrow> clock" where
      f1: "\<forall>t. \<not> positive_atom t \<or> t = cc t sporadic tt t \<or> t = cca t sporadic tta t on ccb t"
      using positive_atom.elims(2) by moura
    obtain ttb :: "tag_expr \<Rightarrow> tag_const" where
      "\<And>c t ca. \<Union>{R. \<exists>n. R = \<lbrakk> c sporadic t on ca \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup>} = \<lbrakk> c sporadic t on ca \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L \<or> \<lfloor> ttb t \<rfloor> = t"
      by (metis TESL_interp_unfold_at_index_sporadicon_add old.prod.exhaust tag_expr.exhaust tag_var.exhaust)
    then have "\<And>t. \<Union>{R. \<exists>n. R = \<lbrakk> t \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup>} = \<lbrakk> t \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L \<or> \<lfloor> ttb (tta t) \<rfloor> = tta t \<or> \<not> positive_atom t"
      using f1 by (metis TESL_interp_unfold_at_index_sporadic)
    then show ?thesis
      using f1 by (metis TESL_interp_unfold_at_index_sporadic TESL_interp_unfold_at_index_sporadicon assms)
  qed

theorem TESL_interp_unfold_at_index_negative_atoms:
  assumes "\<not> positive_atom \<phi>"
  shows "\<lbrakk> \<phi> \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L = \<Inter> {Y. \<exists>n::nat. Y = \<lbrakk> \<phi> \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup>}"
  by (smt Collect_cong TESL_interp_unfold_at_index_implies TESL_interp_unfold_at_index_tagrel TESL_interp_unfold_at_index_timedelayed assms positive_atom.elims(3))

lemma forall_nat_expansion:
  "(\<forall>n\<^sub>1 \<ge> (n\<^sub>0::nat). P n\<^sub>1) \<equiv> P n\<^sub>0 \<and> (\<forall>n\<^sub>1 \<ge> Suc n\<^sub>0. P n\<^sub>1)"
  by (smt Suc_leD dual_order.antisym not_less_eq_eq)

lemma exists_nat_expansion:
  "(\<exists>n\<^sub>1 \<ge> (n\<^sub>0::nat). P n\<^sub>1) \<equiv> P n\<^sub>0 \<or> (\<exists>n\<^sub>1 \<ge> Suc n\<^sub>0. P n\<^sub>1)"
  by (smt Suc_leD dual_order.antisym not_less_eq_eq)

lemma TESL_interp_at_index_sporadic_cases:
  shows "\<lbrakk> K sporadic \<tau> \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup> =
    \<lbrakk> K \<Up> n \<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n \<inter> \<lbrakk> K \<Down> n @ \<lfloor> \<tau> \<rfloor> \<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n
    \<union> \<lbrakk> K sporadic \<tau> \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^esup>"
  proof -
    have "{ \<rho>. \<exists>m\<ge>n. hamlet ((Rep_run \<rho>) m K) = True \<and> time ((Rep_run \<rho>) m K) = \<tau> }
        = { \<rho>. hamlet ((Rep_run \<rho>) n K) = True \<and> time ((Rep_run \<rho>) n K) = \<tau>
               \<or> (\<exists>m\<ge>Suc n. hamlet ((Rep_run \<rho>) m K) = True \<and> time ((Rep_run \<rho>) m K) = \<tau>) }"
      using Suc_leD not_less_eq_eq by fastforce
    moreover have "{ \<rho>. hamlet ((Rep_run \<rho>) n K) = True \<and> time ((Rep_run \<rho>) n K) = \<tau>
                        \<or> (\<exists>m\<ge>Suc n. hamlet ((Rep_run \<rho>) m K) = True \<and> time ((Rep_run \<rho>) m K) = \<tau>) }
                 = \<lbrakk> K \<Up> n \<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n \<inter> \<lbrakk> K \<Down> n @ \<lfloor> \<tau> \<rfloor> \<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n \<union> \<lbrakk> K sporadic \<tau> \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^esup>"
      by (simp add: Collect_conj_eq Collect_disj_eq)
    ultimately show ?thesis by auto
  qed

lemma TESL_interp_at_index_sporadicon_cst_cases:
  shows "\<lbrakk> K\<^sub>1 sporadic \<lfloor>\<tau>\<rfloor> on K\<^sub>2 \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup> =
    \<lbrakk> K\<^sub>1 \<Up> n \<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n \<inter> \<lbrakk> K\<^sub>2 \<Down> n @ \<lfloor> \<tau> \<rfloor> \<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n
    \<union> \<lbrakk> K\<^sub>1 sporadic \<lfloor>\<tau>\<rfloor> on K\<^sub>2 \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^esup>"
  proof -
    have "{ \<rho>. \<exists>m\<ge>n. hamlet ((Rep_run \<rho>) m K\<^sub>1) = True \<and> time ((Rep_run \<rho>) m K\<^sub>2) = \<tau> }
        = { \<rho>. hamlet ((Rep_run \<rho>) n K\<^sub>1) = True \<and> time ((Rep_run \<rho>) n K\<^sub>2) = \<tau>
               \<or> (\<exists>m\<ge>Suc n. hamlet ((Rep_run \<rho>) m K\<^sub>1) = True \<and> time ((Rep_run \<rho>) m K\<^sub>2) = \<tau>) }"
      using Suc_leD not_less_eq_eq by fastforce
    moreover have "{ \<rho>. hamlet ((Rep_run \<rho>) n K\<^sub>1) = True \<and> time ((Rep_run \<rho>) n K\<^sub>2) = \<tau>
                        \<or> (\<exists>m\<ge>Suc n. hamlet ((Rep_run \<rho>) m K\<^sub>1) = True \<and> time ((Rep_run \<rho>) m K\<^sub>2) = \<tau>) }
                 = \<lbrakk> K\<^sub>1 \<Up> n \<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n \<inter> \<lbrakk> K\<^sub>2 \<Down> n @ \<lfloor>\<tau>\<rfloor> \<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n \<union> \<lbrakk> K\<^sub>1 sporadic \<lfloor>\<tau>\<rfloor> on K\<^sub>2 \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^esup>"
      by (simp add: Collect_conj_eq Collect_disj_eq)
    ultimately show ?thesis by auto
  qed

lemma TESL_interp_at_index_sporadicon_add_cases:
  shows "\<lbrakk> K\<^sub>1 sporadic \<lfloor>\<tau>\<^sub>v\<^sub>a\<^sub>r(K, n') \<oplus> \<tau>\<rfloor> on K\<^sub>2 \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup> =
    \<lbrakk> K\<^sub>1 \<Up> n \<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n \<inter> \<lbrakk> K\<^sub>2 \<Down> n @ \<lfloor>\<tau>\<^sub>v\<^sub>a\<^sub>r(K, n') \<oplus> \<tau>\<rfloor> \<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n
    \<union> \<lbrakk> K\<^sub>1 sporadic \<lfloor>\<tau>\<^sub>v\<^sub>a\<^sub>r(K, n') \<oplus> \<tau>\<rfloor> on K\<^sub>2 \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^esup>"
  proof -
    have "{ \<rho>. \<exists>m\<ge>n. hamlet ((Rep_run \<rho>) m K\<^sub>1) = True \<and> time ((Rep_run \<rho>) m K\<^sub>2) = time ((Rep_run \<rho>) n' K) + \<tau> }
        = { \<rho>. hamlet ((Rep_run \<rho>) n K\<^sub>1) = True \<and> time ((Rep_run \<rho>) n K\<^sub>2) = time ((Rep_run \<rho>) n' K) + \<tau>
               \<or> (\<exists>m\<ge>Suc n. hamlet ((Rep_run \<rho>) m K\<^sub>1) = True \<and> time ((Rep_run \<rho>) m K\<^sub>2) = time ((Rep_run \<rho>) n' K) + \<tau>) }"
      using Suc_leD not_less_eq_eq by fastforce
    then show ?thesis by auto
  qed

lemma TESL_interp_at_index_sporadicon_cases:
  shows "\<lbrakk> K\<^sub>1 sporadic \<tau> on K\<^sub>2 \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup> =
    \<lbrakk> K\<^sub>1 \<Up> n \<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n \<inter> \<lbrakk> K\<^sub>2 \<Down> n @ \<tau> \<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n
    \<union> \<lbrakk> K\<^sub>1 sporadic \<tau> on K\<^sub>2 \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^esup>"
  proof (induct \<tau>)
    case (Const x)
    then show ?case using TESL_interp_at_index_sporadicon_cst_cases by blast
  next
    case (AddDelay tagv x2)
    then show ?case
      proof (induct tagv)
        case (Schematic xa)
        then show ?case
          proof (induct xa)
            case (Pair a b)
            then show ?case using TESL_interp_at_index_sporadicon_add_cases by blast
          qed
      qed
  qed

lemma TESL_interp_at_index_tagrel_cases:
  shows "\<lbrakk> tag-relation K\<^sub>1 = \<alpha> * K\<^sub>2 + \<beta> \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup> =
    \<lbrakk> \<tau>\<^sub>v\<^sub>a\<^sub>r(K\<^sub>1, n) \<doteq> \<alpha> * \<tau>\<^sub>v\<^sub>a\<^sub>r(K\<^sub>2, n) + \<beta> \<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n
    \<inter> \<lbrakk> tag-relation K\<^sub>1 = \<alpha> * K\<^sub>2 + \<beta> \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^esup>"
  proof -
    have "{ \<rho>. \<forall>m\<ge>n. time ((Rep_run \<rho>) m K\<^sub>1) = \<alpha> * time ((Rep_run \<rho>) m K\<^sub>2) + \<beta> }
         = { \<rho>. time ((Rep_run \<rho>) n K\<^sub>1) = \<alpha> * time ((Rep_run \<rho>) n K\<^sub>2) + \<beta> }
         \<inter> { \<rho>. \<forall>m\<ge>Suc n. time ((Rep_run \<rho>) m K\<^sub>1) = \<alpha> * time ((Rep_run \<rho>) m K\<^sub>2) + \<beta> }"
      by (smt Collect_cong Collect_conj_eq Suc_leD eq_refl le_antisym not_less_eq_eq)
  then show ?thesis by auto
  qed

lemma TESL_interp_at_index_implies_cases:
  shows "\<lbrakk> master implies slave \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup> =
    (\<lbrakk> master \<not>\<Up> n \<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n \<union> \<lbrakk> master \<Up> n \<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n \<inter> \<lbrakk> slave \<Up> n \<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n)
    \<inter> \<lbrakk> master implies slave \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^esup>"
  proof -
    have "{ \<rho>. \<forall>m\<ge>n. hamlet ((Rep_run \<rho>) m master) \<longrightarrow> hamlet ((Rep_run \<rho>) m slave) }
          = { \<rho>. hamlet ((Rep_run \<rho>) n master) \<longrightarrow> hamlet ((Rep_run \<rho>) n slave) }
          \<inter> { \<rho>. \<forall>m\<ge>Suc n. hamlet ((Rep_run \<rho>) m master) \<longrightarrow> hamlet ((Rep_run \<rho>) m slave) }"
      by (smt Collect_cong Collect_conj_eq Suc_leD eq_refl le_antisym not_less_eq_eq)
    then show ?thesis by auto
  qed

lemma TESL_interp_at_index_timedelayed_cases:
  shows "\<lbrakk> master time-delayed by \<delta>\<tau> on measuring implies slave \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup> =
    (\<lbrakk> master \<not>\<Up> n \<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n \<union> \<lbrakk> master \<Up> n \<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n \<inter> \<lbrakk> slave sporadic \<lfloor>\<tau>\<^sub>v\<^sub>a\<^sub>r(measuring, n) \<oplus> \<delta>\<tau>\<rfloor> on measuring \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup>)
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

fun TESL_interpretation_at_index :: "TESL_formula \<Rightarrow> nat \<Rightarrow> run set" ("\<lbrakk>\<lbrakk> _ \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> _\<^esup>") where
    "\<lbrakk>\<lbrakk> [] \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup> = { _. True }"
  | "\<lbrakk>\<lbrakk> \<phi> # \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup> = \<lbrakk> \<phi> \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup> \<inter> \<lbrakk>\<lbrakk> \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup>"

lemma TESL_interpretation_at_index_fixpoint:
  "\<lbrakk>\<lbrakk> \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup> = \<Inter> ((\<lambda>\<phi>. \<lbrakk> \<phi> \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup>) ` set \<Phi>)"
  proof (induct \<Phi>)
    case Nil
    then show ?case by simp
  next
    case (Cons a \<Phi>)
    then show ?case by auto
  qed

lemma TESL_interpretation_at_index_zero:
  "\<lbrakk> \<phi> \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L = \<lbrakk> \<phi> \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> 0\<^esup>"
  proof (induct \<phi>)
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
    case (Implies x1 x2)
    then show ?case by simp
  next
    case (TimeDelayedBy x1 x2 x3 x4)
    then show ?case by simp
  qed

lemma TESL_interpretation_at_index_zero':
  "\<lbrakk>\<lbrakk> \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L = \<lbrakk>\<lbrakk> \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> 0\<^esup>"
  proof (induct \<Phi>)
    case Nil
    then show ?case by simp
  next
    case (Cons a \<Phi>)
    then show ?case
      by (simp add: TESL_interpretation_at_index_zero)
  qed

lemma TESL_interpretation_at_index_cons_morph:
  "\<lbrakk> \<phi> \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup> \<inter> \<lbrakk>\<lbrakk> \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup> = \<lbrakk>\<lbrakk> \<phi> # \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup>"
  by auto

theorem TESL_interp_at_index_composition:
  shows "\<lbrakk>\<lbrakk> \<Phi>\<^sub>1 @ \<Phi>\<^sub>2 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup> = \<lbrakk>\<lbrakk> \<Phi>\<^sub>1 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup> \<inter> \<lbrakk>\<lbrakk> \<Phi>\<^sub>2 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup>"
  proof (induct \<Phi>\<^sub>1)
    case Nil
    then show ?case by simp
  next
    case (Cons a \<Phi>\<^sub>1)
    then show ?case by auto
  qed

section \<open>Accurate interpretation of configurations\<close>

fun HeronConf_interpretation :: "config \<Rightarrow> run set" ("\<lbrakk> _ \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g" 71) where
  "\<lbrakk> \<Gamma>, n \<turnstile> \<Psi> \<triangleright> \<Phi> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g = \<lbrakk>\<lbrakk> \<Gamma> \<rbrakk>\<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n \<inter> \<lbrakk>\<lbrakk> \<Psi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup> \<inter> \<lbrakk>\<lbrakk> \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^esup>"

lemma HeronConf_interp_at_index_instant_cases:
  shows "\<lbrakk> \<Gamma>, n \<turnstile> [] \<triangleright> \<Phi> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g
          = \<lbrakk> \<Gamma>, Suc n \<turnstile> \<Phi> \<triangleright> [] \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g"
  proof -
    have "\<lbrakk> \<Gamma>, n \<turnstile> [] \<triangleright> \<Phi> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g = \<lbrakk>\<lbrakk> \<Gamma> \<rbrakk>\<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n \<inter> \<lbrakk>\<lbrakk> [] \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup> \<inter> \<lbrakk>\<lbrakk> \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^esup>"
      by simp
    moreover have "\<lbrakk> \<Gamma>, Suc n \<turnstile> \<Phi> \<triangleright> [] \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g = \<lbrakk>\<lbrakk> \<Gamma> \<rbrakk>\<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n \<inter> \<lbrakk>\<lbrakk> \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^esup> \<inter> \<lbrakk>\<lbrakk> [] \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^esup>"
      by simp
    moreover have "\<lbrakk>\<lbrakk> \<Gamma> \<rbrakk>\<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n \<inter> \<lbrakk>\<lbrakk> [] \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup> \<inter> \<lbrakk>\<lbrakk> \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^esup>
                   = \<lbrakk>\<lbrakk> \<Gamma> \<rbrakk>\<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n \<inter> \<lbrakk>\<lbrakk> \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^esup> \<inter> \<lbrakk>\<lbrakk> [] \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^esup>"
      by simp
    ultimately show ?thesis by blast
  qed

lemma HeronConf_interp_at_index_sporadic_cases:
  shows "\<lbrakk> \<Gamma>, n \<turnstile> (K sporadic \<tau>) # \<Psi> \<triangleright> \<Phi> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g
          = \<lbrakk> \<Gamma>, n \<turnstile> \<Psi> \<triangleright> (K sporadic \<tau>) # \<Phi> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g
          \<union> \<lbrakk> K \<Up> n # K \<Down> n @ \<lfloor>\<tau>\<rfloor> # \<Gamma>, n \<turnstile> \<Psi> \<triangleright> \<Phi> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g"
  proof -
    have "\<lbrakk> \<Gamma>, n \<turnstile> (K sporadic \<tau>) # \<Psi> \<triangleright> \<Phi> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g = \<lbrakk>\<lbrakk> \<Gamma> \<rbrakk>\<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n \<inter> \<lbrakk>\<lbrakk> (K sporadic \<tau>) # \<Psi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup> \<inter> \<lbrakk>\<lbrakk> \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^esup>"
      by simp
    moreover have "\<lbrakk> \<Gamma>, n \<turnstile> \<Psi> \<triangleright> (K sporadic \<tau>) # \<Phi> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g = \<lbrakk>\<lbrakk> \<Gamma> \<rbrakk>\<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n \<inter> \<lbrakk>\<lbrakk> \<Psi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup> \<inter> \<lbrakk>\<lbrakk> (K sporadic \<tau>) # \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^esup>"
      by simp
    moreover have "\<lbrakk> K \<Up> n # K \<Down> n @ \<lfloor>\<tau>\<rfloor> # \<Gamma>, n \<turnstile> \<Psi> \<triangleright> \<Phi> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g = \<lbrakk>\<lbrakk> K \<Up> n # K \<Down> n @ \<lfloor>\<tau>\<rfloor> # \<Gamma> \<rbrakk>\<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n \<inter> \<lbrakk>\<lbrakk> \<Psi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup> \<inter> \<lbrakk>\<lbrakk> \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^esup>"
      by simp
    ultimately show ?thesis
    proof -
      have "(\<lbrakk> K \<Up> n \<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n \<inter> \<lbrakk> K \<Down> n @ \<lfloor> \<tau> \<rfloor> \<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n \<union> \<lbrakk> K sporadic \<tau> \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^esup>) \<inter> \<lbrakk>\<lbrakk> \<Psi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup> = \<lbrakk>\<lbrakk> (K sporadic \<tau>) # \<Psi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup>"
        using TESL_interp_at_index_sporadic_cases TESL_interpretation_at_index_cons_morph by blast
  then have "\<lbrakk> \<Gamma>, n \<turnstile> (K sporadic \<tau>) # \<Psi> \<triangleright> \<Phi> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g = (\<lbrakk>\<lbrakk> K \<Up> n # K \<Down> n @ \<lfloor> \<tau> \<rfloor> # \<Gamma> \<rbrakk>\<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n \<inter> \<lbrakk>\<lbrakk> \<Psi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup> \<union> \<lbrakk>\<lbrakk> \<Gamma> \<rbrakk>\<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n \<inter> \<lbrakk>\<lbrakk> \<Psi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup> \<inter> \<lbrakk> K sporadic \<tau> \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^esup>) \<inter> \<lbrakk>\<lbrakk> \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^esup>"
    by auto
      then show ?thesis
        by (simp add: Int_Un_distrib2 Int_assoc Un_commute)
    qed
  qed

lemma HeronConf_interp_at_index_sporadicon_cases:
  shows "\<lbrakk> \<Gamma>, n \<turnstile> (K\<^sub>1 sporadic \<tau> on K\<^sub>2) # \<Psi> \<triangleright> \<Phi> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g
          = \<lbrakk> \<Gamma>, n \<turnstile> \<Psi> \<triangleright> (K\<^sub>1 sporadic \<tau> on K\<^sub>2) # \<Phi> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g
          \<union> \<lbrakk> K\<^sub>1 \<Up> n # K\<^sub>2 \<Down> n @ \<tau> # \<Gamma>, n \<turnstile> \<Psi> \<triangleright> \<Phi> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g"
  proof -
    have "\<lbrakk> \<Gamma>, n \<turnstile> (K\<^sub>1 sporadic \<tau> on K\<^sub>2) # \<Psi> \<triangleright> \<Phi> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g = \<lbrakk>\<lbrakk> \<Gamma> \<rbrakk>\<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n \<inter> \<lbrakk>\<lbrakk> (K\<^sub>1 sporadic \<tau> on K\<^sub>2) # \<Psi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup> \<inter> \<lbrakk>\<lbrakk> \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^esup>"
      by simp
    moreover have "\<lbrakk> \<Gamma>, n \<turnstile> \<Psi> \<triangleright> (K\<^sub>1 sporadic \<tau> on K\<^sub>2) # \<Phi> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g = \<lbrakk>\<lbrakk> \<Gamma> \<rbrakk>\<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n \<inter> \<lbrakk>\<lbrakk> \<Psi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup> \<inter> \<lbrakk>\<lbrakk> (K\<^sub>1 sporadic \<tau> on K\<^sub>2) # \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^esup>"
      by simp
    moreover have "\<lbrakk> K\<^sub>1 \<Up> n # K\<^sub>2 \<Down> n @ \<tau> # \<Gamma>, n \<turnstile> \<Psi> \<triangleright> \<Phi> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g = \<lbrakk>\<lbrakk> K\<^sub>1 \<Up> n # K\<^sub>2 \<Down> n @ \<tau> # \<Gamma> \<rbrakk>\<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n \<inter> \<lbrakk>\<lbrakk> \<Psi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup> \<inter> \<lbrakk>\<lbrakk> \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^esup>"
      by simp
    ultimately show ?thesis
    proof -
      have "(\<lbrakk> K\<^sub>1 \<Up> n \<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n \<inter> \<lbrakk> K\<^sub>2 \<Down> n @ \<tau> \<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n \<union> \<lbrakk> K\<^sub>1 sporadic \<tau> on K\<^sub>2 \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^esup>) \<inter> (\<lbrakk>\<lbrakk> \<Gamma> \<rbrakk>\<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n \<inter> \<lbrakk>\<lbrakk> \<Psi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup>) = \<lbrakk> K\<^sub>1 sporadic \<tau> on K\<^sub>2 \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup> \<inter> (\<lbrakk>\<lbrakk> \<Psi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup> \<inter> \<lbrakk>\<lbrakk> \<Gamma> \<rbrakk>\<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n)"
        using TESL_interp_at_index_sporadicon_cases by blast
      then have "\<lbrakk>\<lbrakk> K\<^sub>1 \<Up> n # K\<^sub>2 \<Down> n @ \<tau> # \<Gamma> \<rbrakk>\<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n \<inter> \<lbrakk>\<lbrakk> \<Psi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup> \<union> \<lbrakk>\<lbrakk> \<Gamma> \<rbrakk>\<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n \<inter> \<lbrakk>\<lbrakk> \<Psi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup> \<inter> \<lbrakk> K\<^sub>1 sporadic \<tau> on K\<^sub>2 \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^esup> = \<lbrakk>\<lbrakk> (K\<^sub>1 sporadic \<tau> on K\<^sub>2) # \<Psi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup> \<inter> \<lbrakk>\<lbrakk> \<Gamma> \<rbrakk>\<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n"
        by auto
      then show ?thesis
        by auto
    qed
  qed

lemma HeronConf_interp_at_index_tagrel_cases:
  shows "\<lbrakk> \<Gamma>, n \<turnstile> (tag-relation K\<^sub>1 = \<alpha> * K\<^sub>2 + \<beta>) # \<Psi> \<triangleright> \<Phi> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g
          = \<lbrakk> (\<tau>\<^sub>v\<^sub>a\<^sub>r(K\<^sub>1, n) \<doteq> \<alpha> * \<tau>\<^sub>v\<^sub>a\<^sub>r(K\<^sub>2, n) + \<beta>) # \<Gamma>, n \<turnstile> \<Psi> \<triangleright> (tag-relation K\<^sub>1 = \<alpha> * K\<^sub>2 + \<beta>) # \<Phi> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g"
  proof -
    have "\<lbrakk> \<Gamma>, n \<turnstile> (tag-relation K\<^sub>1 = \<alpha> * K\<^sub>2 + \<beta>) # \<Psi> \<triangleright> \<Phi> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g = \<lbrakk>\<lbrakk> \<Gamma> \<rbrakk>\<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n \<inter> \<lbrakk>\<lbrakk> (tag-relation K\<^sub>1 = \<alpha> * K\<^sub>2 + \<beta>) # \<Psi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup> \<inter> \<lbrakk>\<lbrakk> \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^esup>"
      by simp
    moreover have "\<lbrakk> (\<tau>\<^sub>v\<^sub>a\<^sub>r(K\<^sub>1, n) \<doteq> \<alpha> * \<tau>\<^sub>v\<^sub>a\<^sub>r(K\<^sub>2, n) + \<beta>) # \<Gamma>, n \<turnstile> \<Psi> \<triangleright> (tag-relation K\<^sub>1 = \<alpha> * K\<^sub>2 + \<beta>) # \<Phi> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g
                      = \<lbrakk>\<lbrakk> (\<tau>\<^sub>v\<^sub>a\<^sub>r(K\<^sub>1, n) \<doteq> \<alpha> * \<tau>\<^sub>v\<^sub>a\<^sub>r(K\<^sub>2, n) + \<beta>) # \<Gamma> \<rbrakk>\<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n \<inter> \<lbrakk>\<lbrakk> \<Psi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup> \<inter> \<lbrakk>\<lbrakk> (tag-relation K\<^sub>1 = \<alpha> * K\<^sub>2 + \<beta>) # \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^esup>"
      by simp
    ultimately show ?thesis
    proof -
      have "\<lbrakk> \<tau>\<^sub>v\<^sub>a\<^sub>r (K\<^sub>1, n) \<doteq> \<alpha> * \<tau>\<^sub>v\<^sub>a\<^sub>r (K\<^sub>2, n) + \<beta> \<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n \<inter> \<lbrakk> tag-relation K\<^sub>1 = \<alpha> * K\<^sub>2 + \<beta> \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^esup> \<inter> \<lbrakk>\<lbrakk> \<Psi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup> = \<lbrakk>\<lbrakk> (tag-relation K\<^sub>1 = \<alpha> * K\<^sub>2 + \<beta>) # \<Psi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup>"
        using TESL_interp_at_index_tagrel_cases TESL_interpretation_at_index_cons_morph by blast
      then show ?thesis
        by auto
    qed
  qed

lemma HeronConf_interp_at_index_implies_cases:
  shows "\<lbrakk> \<Gamma>, n \<turnstile> (K\<^sub>1 implies K\<^sub>2) # \<Psi> \<triangleright> \<Phi> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g
          = \<lbrakk> K\<^sub>1 \<not>\<Up> n # \<Gamma>, n \<turnstile> \<Psi> \<triangleright> (K\<^sub>1 implies K\<^sub>2) # \<Phi> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g
          \<union> \<lbrakk> K\<^sub>1 \<Up> n # K\<^sub>2 \<Up> n # \<Gamma>, n \<turnstile> \<Psi> \<triangleright> (K\<^sub>1 implies K\<^sub>2) # \<Phi> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g"
  proof -
    have "\<lbrakk> \<Gamma>, n \<turnstile> (K\<^sub>1 implies K\<^sub>2) # \<Psi> \<triangleright> \<Phi> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g = \<lbrakk>\<lbrakk> \<Gamma> \<rbrakk>\<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n \<inter> \<lbrakk>\<lbrakk> (K\<^sub>1 implies K\<^sub>2) # \<Psi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup> \<inter> \<lbrakk>\<lbrakk> \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^esup>"
      by simp
    moreover have "\<lbrakk> K\<^sub>1 \<not>\<Up> n # \<Gamma>, n \<turnstile> \<Psi> \<triangleright> (K\<^sub>1 implies K\<^sub>2) # \<Phi> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g = \<lbrakk>\<lbrakk> K\<^sub>1 \<not>\<Up> n # \<Gamma> \<rbrakk>\<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n \<inter> \<lbrakk>\<lbrakk> \<Psi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup> \<inter> \<lbrakk>\<lbrakk> (K\<^sub>1 implies K\<^sub>2) # \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^esup>"
      by simp
    moreover have "\<lbrakk> K\<^sub>1 \<Up> n # K\<^sub>2 \<Up> n # \<Gamma>, n \<turnstile> \<Psi> \<triangleright> (K\<^sub>1 implies K\<^sub>2) # \<Phi> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g = \<lbrakk>\<lbrakk> K\<^sub>1 \<Up> n # K\<^sub>2 \<Up> n # \<Gamma> \<rbrakk>\<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n \<inter> \<lbrakk>\<lbrakk> \<Psi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup> \<inter> \<lbrakk>\<lbrakk> (K\<^sub>1 implies K\<^sub>2) # \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^esup>"
      by simp
    ultimately show ?thesis
    proof -
      have f1: "(\<lbrakk> K\<^sub>1 \<not>\<Up> n \<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n \<union> \<lbrakk> K\<^sub>1 \<Up> n \<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n \<inter> \<lbrakk> K\<^sub>2 \<Up> n \<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n) \<inter> \<lbrakk> K\<^sub>1 implies K\<^sub>2 \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^esup> \<inter> (\<lbrakk>\<lbrakk> \<Psi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup> \<inter> \<lbrakk>\<lbrakk> \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^esup>) = \<lbrakk>\<lbrakk> (K\<^sub>1 implies K\<^sub>2) # \<Psi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup> \<inter> \<lbrakk>\<lbrakk> \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^esup>"
        using TESL_interp_at_index_implies_cases TESL_interpretation_at_index_cons_morph by blast
      have "\<lbrakk> K\<^sub>1 \<not>\<Up> n \<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n \<inter> \<lbrakk>\<lbrakk> \<Gamma> \<rbrakk>\<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n \<union> \<lbrakk> K\<^sub>1 \<Up> n \<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n \<inter> \<lbrakk>\<lbrakk> K\<^sub>2 \<Up> n # \<Gamma> \<rbrakk>\<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n = (\<lbrakk> K\<^sub>1 \<not>\<Up> n \<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n \<union> \<lbrakk> K\<^sub>1 \<Up> n \<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n \<inter> \<lbrakk> K\<^sub>2 \<Up> n \<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n) \<inter> \<lbrakk>\<lbrakk> \<Gamma> \<rbrakk>\<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n"
        by force
      then have "\<lbrakk> \<Gamma>, n \<turnstile> (K\<^sub>1 implies K\<^sub>2) # \<Psi> \<triangleright> \<Phi> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g = (\<lbrakk> K\<^sub>1 \<not>\<Up> n \<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n \<inter> \<lbrakk>\<lbrakk> \<Gamma> \<rbrakk>\<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n \<union> \<lbrakk> K\<^sub>1 \<Up> n \<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n \<inter> \<lbrakk>\<lbrakk> K\<^sub>2 \<Up> n # \<Gamma> \<rbrakk>\<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n) \<inter> (\<lbrakk>\<lbrakk> \<Psi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup> \<inter> \<lbrakk>\<lbrakk> (K\<^sub>1 implies K\<^sub>2) # \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^esup>)"
        using f1 by (simp add: inf_left_commute inf_sup_aci(2))
      then show ?thesis
        by (simp add: Int_Un_distrib2 inf_sup_aci(2))
    qed
  qed

lemma HeronConf_interp_at_index_timedelayed_cases:
  shows "\<lbrakk> \<Gamma>, n \<turnstile> (K\<^sub>1 time-delayed by \<delta>\<tau> on K\<^sub>2 implies K\<^sub>3) # \<Psi> \<triangleright> \<Phi> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g
          = \<lbrakk> K\<^sub>1 \<not>\<Up> n # \<Gamma>, n \<turnstile> \<Psi> \<triangleright> (K\<^sub>1 time-delayed by \<delta>\<tau> on K\<^sub>2 implies K\<^sub>3) # \<Phi> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g
          \<union> \<lbrakk> K\<^sub>1 \<Up> n # \<Gamma>, n \<turnstile> (K\<^sub>3 sporadic \<lfloor>\<tau>\<^sub>v\<^sub>a\<^sub>r(K\<^sub>2, n) \<oplus> \<delta>\<tau>\<rfloor> on K\<^sub>2) # \<Psi> \<triangleright> (K\<^sub>1 time-delayed by \<delta>\<tau> on K\<^sub>2 implies K\<^sub>3) # \<Phi> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g"
  proof -
    have "\<lbrakk> \<Gamma>, n \<turnstile> (K\<^sub>1 time-delayed by \<delta>\<tau> on K\<^sub>2 implies K\<^sub>3) # \<Psi> \<triangleright> \<Phi> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g
           = \<lbrakk>\<lbrakk> \<Gamma> \<rbrakk>\<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n \<inter> \<lbrakk>\<lbrakk> (K\<^sub>1 time-delayed by \<delta>\<tau> on K\<^sub>2 implies K\<^sub>3) # \<Psi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup> \<inter> \<lbrakk>\<lbrakk> \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^esup>"
      by simp
    moreover have "\<lbrakk> K\<^sub>1 \<not>\<Up> n # \<Gamma>, n \<turnstile> \<Psi> \<triangleright> (K\<^sub>1 time-delayed by \<delta>\<tau> on K\<^sub>2 implies K\<^sub>3) # \<Phi> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g
                     = \<lbrakk>\<lbrakk> K\<^sub>1 \<not>\<Up> n # \<Gamma> \<rbrakk>\<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n \<inter> \<lbrakk>\<lbrakk> \<Psi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup> \<inter> \<lbrakk>\<lbrakk> (K\<^sub>1 time-delayed by \<delta>\<tau> on K\<^sub>2 implies K\<^sub>3) # \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^esup>"
      by simp
    moreover have "\<lbrakk> K\<^sub>1 \<Up> n # \<Gamma>, n \<turnstile> (K\<^sub>3 sporadic \<lfloor>\<tau>\<^sub>v\<^sub>a\<^sub>r(K\<^sub>2, n) \<oplus> \<delta>\<tau>\<rfloor> on K\<^sub>2) # \<Psi> \<triangleright> (K\<^sub>1 time-delayed by \<delta>\<tau> on K\<^sub>2 implies K\<^sub>3) # \<Phi> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g
                     = \<lbrakk>\<lbrakk> K\<^sub>1 \<Up> n # \<Gamma> \<rbrakk>\<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n \<inter> \<lbrakk>\<lbrakk> (K\<^sub>3 sporadic \<lfloor>\<tau>\<^sub>v\<^sub>a\<^sub>r(K\<^sub>2, n) \<oplus> \<delta>\<tau>\<rfloor> on K\<^sub>2) # \<Psi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup>
                     \<inter> \<lbrakk>\<lbrakk> (K\<^sub>1 time-delayed by \<delta>\<tau> on K\<^sub>2 implies K\<^sub>3) # \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^esup>"
      by simp
    ultimately show ?thesis
    proof -
      have "\<lbrakk> \<Gamma>, n \<turnstile> (K\<^sub>1 time-delayed by \<delta>\<tau> on K\<^sub>2 implies K\<^sub>3) # \<Psi> \<triangleright> \<Phi> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g = \<lbrakk>\<lbrakk> \<Gamma> \<rbrakk>\<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n \<inter> (\<lbrakk>\<lbrakk> (K\<^sub>1 time-delayed by \<delta>\<tau> on K\<^sub>2 implies K\<^sub>3) # \<Psi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup> \<inter> \<lbrakk>\<lbrakk> \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^esup>)"
        using \<open>\<lbrakk> \<Gamma>, n \<turnstile> (K\<^sub>1 time-delayed by \<delta>\<tau> on K\<^sub>2 implies K\<^sub>3) # \<Psi> \<triangleright> \<Phi> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g = \<lbrakk>\<lbrakk> \<Gamma> \<rbrakk>\<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n \<inter> \<lbrakk>\<lbrakk> (K\<^sub>1 time-delayed by \<delta>\<tau> on K\<^sub>2 implies K\<^sub>3) # \<Psi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup> \<inter> \<lbrakk>\<lbrakk> \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^esup>\<close> by blast
      then have "\<lbrakk> \<Gamma>, n \<turnstile> (K\<^sub>1 time-delayed by \<delta>\<tau> on K\<^sub>2 implies K\<^sub>3) # \<Psi> \<triangleright> \<Phi> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g = (\<lbrakk> K\<^sub>1 \<not>\<Up> n \<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n \<union> \<lbrakk> K\<^sub>1 \<Up> n \<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n \<inter> \<lbrakk> K\<^sub>3 sporadic \<lfloor> \<tau>\<^sub>v\<^sub>a\<^sub>r (K\<^sub>2, n) \<oplus> \<delta>\<tau> \<rfloor> on K\<^sub>2 \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup>) \<inter> (\<lbrakk>\<lbrakk> \<Gamma> \<rbrakk>\<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n \<inter> (\<lbrakk>\<lbrakk> \<Psi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup> \<inter> \<lbrakk>\<lbrakk> (K\<^sub>1 time-delayed by \<delta>\<tau> on K\<^sub>2 implies K\<^sub>3) # \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^esup>))"
        using TESL_interp_at_index_timedelayed_cases TESL_interpretation_at_index_cons_morph by blast
      then show ?thesis
        by auto
    qed
  qed

lemma HeronConf_interp_at_index_successor_run_presv:
  assumes "\<rho> \<in> \<lbrakk> \<Gamma>, k \<turnstile> \<Psi> \<triangleright> \<Phi> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g"
  shows   "\<exists>\<Gamma>\<^sub>n k\<^sub>n \<Psi>\<^sub>n \<Phi>\<^sub>n. \<Gamma>, k \<turnstile> \<Psi> \<triangleright> \<Phi>  \<hookrightarrow>  \<Gamma>\<^sub>n, k\<^sub>n \<turnstile> \<Psi>\<^sub>n \<triangleright> \<Phi>\<^sub>n
                         \<and> \<rho> \<in> \<lbrakk> \<Gamma>\<^sub>n, k\<^sub>n \<turnstile> \<Psi>\<^sub>n \<triangleright> \<Phi>\<^sub>n \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g"
  proof (insert assms, induct \<Psi>)
    case Nil
    then show ?case
      proof -
        have "\<rho> \<in> \<lbrakk> \<Gamma>, Suc k \<turnstile> \<Phi> \<triangleright> [] \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g"
          using assms HeronConf_interp_at_index_instant_cases by auto
        moreover have "\<Gamma>, k \<turnstile> [] \<triangleright> \<Phi> \<hookrightarrow> \<Gamma>, Suc k \<turnstile> \<Phi> \<triangleright> []"
          using intro_part instant_i by auto
        ultimately show ?thesis by blast
      qed
  next
    case (Cons \<psi> \<Psi>)
  then show ?case
    proof (induct \<psi>)
      case (Sporadic K \<tau>)
      then show ?case
        proof -
          have f0: "\<rho> \<in> \<lbrakk> \<Gamma>, k \<turnstile> (K sporadic \<tau>) # \<Psi> \<triangleright> \<Phi> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g"
            using Sporadic.prems(2) by blast
          then have f1: "\<rho> \<in> \<lbrakk> \<Gamma>, k \<turnstile> \<Psi> \<triangleright> (K sporadic \<tau>) # \<Phi> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g \<union> \<lbrakk> K \<Up> k # K \<Down> k @ \<lfloor>\<tau>\<rfloor> # \<Gamma>, k \<turnstile> \<Psi> \<triangleright> \<Phi> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g"
            using HeronConf_interp_at_index_sporadic_cases by blast
          then have f2: "(\<Gamma>, k \<turnstile> (K sporadic \<tau>) # \<Psi> \<triangleright> \<Phi>) \<hookrightarrow> (\<Gamma>, k \<turnstile> \<Psi> \<triangleright> (K sporadic \<tau>) # \<Phi>)
                         \<or> (\<Gamma>, k \<turnstile> (K sporadic \<tau>) # \<Psi> \<triangleright> \<Phi>) \<hookrightarrow> (K \<Up> k # K \<Down> k @ \<lfloor>\<tau>\<rfloor> # \<Gamma>, k \<turnstile> \<Psi> \<triangleright> \<Phi>)"
            using elims_part sporadic_e1 sporadic_e2 by simp
          then show ?thesis
            by (meson UnE elims_part f1 sporadic_e1 sporadic_e2)
        qed
    next
      case (SporadicOn K\<^sub>1 \<tau> K\<^sub>2)
      then show ?case
        proof -
          have "\<rho> \<in> \<lbrakk> \<Gamma>, k \<turnstile> (K\<^sub>1 sporadic \<tau> on K\<^sub>2) # \<Psi> \<triangleright> \<Phi> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g"
            using SporadicOn.prems(2) by blast
          then have p1: "\<rho> \<in> \<lbrakk> \<Gamma>, k \<turnstile> \<Psi> \<triangleright> (K\<^sub>1 sporadic \<tau> on K\<^sub>2) # \<Phi> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g \<union> \<lbrakk> K\<^sub>1 \<Up> k # K\<^sub>2 \<Down> k @ \<tau> # \<Gamma>, k \<turnstile> \<Psi> \<triangleright> \<Phi> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g"
            using HeronConf_interp_at_index_sporadicon_cases by blast
          then have p2: "(\<Gamma>, k \<turnstile> (K\<^sub>1 sporadic \<tau> on K\<^sub>2) # \<Psi> \<triangleright> \<Phi>) \<hookrightarrow> (\<Gamma>, k \<turnstile> \<Psi> \<triangleright> (K\<^sub>1 sporadic \<tau> on K\<^sub>2) # \<Phi>)
                        \<or> (\<Gamma>, k \<turnstile> (K\<^sub>1 sporadic \<tau> on K\<^sub>2) # \<Psi> \<triangleright> \<Phi>) \<hookrightarrow> (K\<^sub>1 \<Up> k # K\<^sub>2 \<Down> k @ \<tau> # \<Gamma>, k \<turnstile> \<Psi> \<triangleright> \<Phi>)"
            using elims_part sporadic_on_e1 sporadic_on_e2 by simp
          then show ?thesis
            by (meson Un_iff elims_part p1 sporadic_on_e1 sporadic_on_e2)
        qed
    next
      case (TagRelation K\<^sub>1 \<alpha> K\<^sub>2 \<beta>)
      then show ?case
        proof -
          have p0: "\<rho> \<in> \<lbrakk> \<Gamma>, k \<turnstile> (tag-relation K\<^sub>1 = \<alpha> * K\<^sub>2 + \<beta>) # \<Psi> \<triangleright> \<Phi> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g"
            using TagRelation.prems(2) by blast
          then have p1: "\<rho> \<in> \<lbrakk> \<Gamma>, k \<turnstile> \<Psi> \<triangleright> (tag-relation K\<^sub>1 = \<alpha> * K\<^sub>2 + \<beta>) # \<Phi> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g"
            using HeronConf_interp_at_index_tagrel_cases by auto
          then have p2: "\<Gamma>, k \<turnstile> (tag-relation K\<^sub>1 = \<alpha> * K\<^sub>2 + \<beta>) # \<Psi> \<triangleright> \<Phi> \<hookrightarrow> (\<tau>\<^sub>v\<^sub>a\<^sub>r(K\<^sub>1, k) \<doteq> \<alpha> * \<tau>\<^sub>v\<^sub>a\<^sub>r(K\<^sub>2, k) + \<beta>) # \<Gamma>, k \<turnstile> \<Psi> \<triangleright> (tag-relation K\<^sub>1 = \<alpha> * K\<^sub>2 + \<beta>) # \<Phi>"
            using elims_part tagrel_e by simp
          then show ?thesis
            using HeronConf_interp_at_index_tagrel_cases p0 by blast
        qed
    next
      case (Implies K\<^sub>1 K\<^sub>2)
      then show ?case
        proof -
          have p0: "\<rho> \<in> \<lbrakk> \<Gamma>, k \<turnstile> (K\<^sub>1 implies K\<^sub>2) # \<Psi> \<triangleright> \<Phi> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g"
            using Implies.prems(2) by blast
          then have p1: "\<rho> \<in> \<lbrakk> K\<^sub>1 \<not>\<Up> k # \<Gamma>, k \<turnstile> \<Psi> \<triangleright> (K\<^sub>1 implies K\<^sub>2) # \<Phi> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g \<union> \<lbrakk> K\<^sub>1 \<Up> k # K\<^sub>2 \<Up> k # \<Gamma>, k \<turnstile> \<Psi> \<triangleright> (K\<^sub>1 implies K\<^sub>2) # \<Phi> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g"
            using HeronConf_interp_at_index_implies_cases by simp
          then have p2: "(\<Gamma>, k \<turnstile> (K\<^sub>1 implies K\<^sub>2) # \<Psi> \<triangleright> \<Phi>) \<hookrightarrow> ((K\<^sub>1 \<not>\<Up> k) # \<Gamma>, k \<turnstile> \<Psi> \<triangleright> (K\<^sub>1 implies K\<^sub>2) # \<Phi>)
                             \<and> (\<Gamma>, k \<turnstile> (K\<^sub>1 implies K\<^sub>2) # \<Psi> \<triangleright> \<Phi>) \<hookrightarrow> ((K\<^sub>1 \<Up> k) # (K\<^sub>2 \<Up> k) # \<Gamma>, k \<turnstile> \<Psi> \<triangleright> (K\<^sub>1 implies K\<^sub>2) # \<Phi>)"
            using elims_part implies_e1 implies_e2 by simp
          then show ?thesis
            using UnE p1 by blast
        qed
    next
      case (TimeDelayedBy K\<^sub>1 \<delta>\<tau> K\<^sub>2 K\<^sub>3)
      then show ?case
        proof -
          have p0: "\<rho> \<in> \<lbrakk> \<Gamma>, k \<turnstile> (K\<^sub>1 time-delayed by \<delta>\<tau> on K\<^sub>2 implies K\<^sub>3) # \<Psi> \<triangleright> \<Phi> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g"
            using TimeDelayedBy.prems(2) by blast
          then have p1: "\<rho> \<in> \<lbrakk> K\<^sub>1 \<not>\<Up> k # \<Gamma>, k \<turnstile> \<Psi> \<triangleright> (K\<^sub>1 time-delayed by \<delta>\<tau> on K\<^sub>2 implies K\<^sub>3) # \<Phi> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g
                                \<union> \<lbrakk> K\<^sub>1 \<Up> k # \<Gamma>, k \<turnstile> (K\<^sub>3 sporadic \<lfloor>\<tau>\<^sub>v\<^sub>a\<^sub>r(K\<^sub>2, k) \<oplus> \<delta>\<tau>\<rfloor> on K\<^sub>2) # \<Psi> \<triangleright> (K\<^sub>1 time-delayed by \<delta>\<tau> on K\<^sub>2 implies K\<^sub>3) # \<Phi> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g"
            using HeronConf_interp_at_index_implies_cases by simp
          then show ?thesis
            by (meson UnE elims_part timedelayed_e1 timedelayed_e2)
        qed
    qed
  qed

lemma HeronConf_interp_at_index_next_instant_run_presv:
  assumes "\<rho> \<in> \<lbrakk> \<Gamma>, k \<turnstile> \<Psi> \<triangleright> \<Phi> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g"
  shows   "\<exists>\<Gamma>\<^sub>n \<Psi>\<^sub>n \<Phi>\<^sub>n n. \<Gamma>, k \<turnstile> \<Psi> \<triangleright> \<Phi>  \<hookrightarrow>\<^bsup>n\<^esup>  \<Gamma>\<^sub>n, Suc k \<turnstile> \<Psi>\<^sub>n \<triangleright> \<Phi>\<^sub>n
                         \<and> \<rho> \<in> \<lbrakk> \<Gamma>\<^sub>n, Suc k \<turnstile> \<Psi>\<^sub>n \<triangleright> \<Phi>\<^sub>n \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g"
  proof (insert assms, induct \<Psi> arbitrary: \<Gamma> \<Phi>)
    case (Nil \<Gamma> \<Phi>)
    then show ?case
      proof -
        have "\<Gamma>, k \<turnstile> [] \<triangleright> \<Phi> \<hookrightarrow>\<^bsup>1\<^esup> \<Gamma>, Suc k \<turnstile> \<Phi> \<triangleright> []"
          using instant_i intro_part by auto
        moreover have "\<lbrakk> \<Gamma>, k \<turnstile> [] \<triangleright> \<Phi> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g = \<lbrakk> \<Gamma>, Suc k \<turnstile> \<Phi> \<triangleright> [] \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g"
          by auto
        moreover have "\<rho> \<in> \<lbrakk> \<Gamma>, Suc k \<turnstile> \<Phi> \<triangleright> [] \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g"
          using assms Nil.prems calculation(2) by blast
        ultimately show ?thesis by blast
      qed
  next
    case (Cons \<psi> \<Psi>)
  then show ?case
    proof (induct \<psi>)
      case (Sporadic K \<tau>)
      have branches: "\<lbrakk> \<Gamma>, k \<turnstile> (K sporadic \<tau>) # \<Psi> \<triangleright> \<Phi> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g = \<lbrakk> \<Gamma>, k \<turnstile> \<Psi> \<triangleright> (K sporadic \<tau>) # \<Phi> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g
                                                           \<union> \<lbrakk> K \<Up> k # K \<Down> k @ \<lfloor>\<tau>\<rfloor> # \<Gamma>, k \<turnstile> \<Psi> \<triangleright> \<Phi> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g"
            using HeronConf_interp_at_index_sporadic_cases by simp
      have br1: "\<rho> \<in> \<lbrakk> \<Gamma>, k \<turnstile> \<Psi> \<triangleright> (K sporadic \<tau>) # \<Phi> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g \<Longrightarrow> \<exists>\<Gamma>\<^sub>n \<Psi>\<^sub>n \<Phi>\<^sub>n n.
       \<Gamma>, k \<turnstile> (K sporadic \<tau>) # \<Psi> \<triangleright> \<Phi> \<hookrightarrow>\<^bsup>n\<^esup> \<Gamma>\<^sub>n, Suc k \<turnstile> \<Psi>\<^sub>n \<triangleright> \<Phi>\<^sub>n \<and>
       \<rho> \<in> \<lbrakk> \<Gamma>\<^sub>n, Suc k \<turnstile> \<Psi>\<^sub>n \<triangleright> \<Phi>\<^sub>n \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g"
        proof -
          assume h1: "\<rho> \<in> \<lbrakk> \<Gamma>, k \<turnstile> \<Psi> \<triangleright> (K sporadic \<tau>) # \<Phi> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g"
          have "\<exists>\<Gamma>\<^sub>n \<Psi>\<^sub>n \<Phi>\<^sub>n n. \<Gamma>, k \<turnstile> \<Psi> \<triangleright> (K sporadic \<tau>) # \<Phi> \<hookrightarrow>\<^bsup>n\<^esup> \<Gamma>\<^sub>n, Suc k \<turnstile> \<Psi>\<^sub>n \<triangleright> \<Phi>\<^sub>n \<and> \<rho> \<in> \<lbrakk> \<Gamma>\<^sub>n, Suc k \<turnstile> \<Psi>\<^sub>n \<triangleright> \<Phi>\<^sub>n \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g"
            using h1 Sporadic.prems by simp
          then show ?thesis
            by (meson elims_part relpowp_Suc_I2 sporadic_e1)
        qed
      moreover have br2: "\<rho> \<in> \<lbrakk> (K \<Up> k) # (K \<Down> k @ \<lfloor>\<tau>\<rfloor>) # \<Gamma>, k \<turnstile> \<Psi> \<triangleright> \<Phi> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g \<Longrightarrow> \<exists>\<Gamma>\<^sub>n \<Psi>\<^sub>n \<Phi>\<^sub>n n.
       \<Gamma>, k \<turnstile> (K sporadic \<tau>) # \<Psi> \<triangleright> \<Phi> \<hookrightarrow>\<^bsup>n\<^esup> \<Gamma>\<^sub>n, Suc k \<turnstile> \<Psi>\<^sub>n \<triangleright> \<Phi>\<^sub>n \<and>
       \<rho> \<in> \<lbrakk> \<Gamma>\<^sub>n, Suc k \<turnstile> \<Psi>\<^sub>n \<triangleright> \<Phi>\<^sub>n \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g"
        proof -
          assume h2: "\<rho> \<in> \<lbrakk> (K \<Up> k) # (K \<Down> k @ \<lfloor>\<tau>\<rfloor>) # \<Gamma>, k \<turnstile> \<Psi> \<triangleright> \<Phi> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g"
          have "\<exists>\<Gamma>\<^sub>n \<Psi>\<^sub>n \<Phi>\<^sub>n n. (K \<Up> k) # (K \<Down> k @ \<lfloor>\<tau>\<rfloor>) # \<Gamma>, k \<turnstile> \<Psi> \<triangleright> \<Phi> \<hookrightarrow>\<^bsup>n\<^esup> \<Gamma>\<^sub>n, Suc k \<turnstile> \<Psi>\<^sub>n \<triangleright> \<Phi>\<^sub>n \<and> \<rho> \<in> \<lbrakk> \<Gamma>\<^sub>n, Suc k \<turnstile> \<Psi>\<^sub>n \<triangleright> \<Phi>\<^sub>n \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g"
            using h2 Sporadic.prems by simp
          then show ?thesis
            by (meson elims_part relpowp_Suc_I2 sporadic_e2)
        qed
      ultimately show ?case
        by (metis Sporadic.prems(2) UnE branches)
    next
      case (SporadicOn K\<^sub>1 \<tau> K\<^sub>2)
      have branches: "\<lbrakk> \<Gamma>, k \<turnstile> (K\<^sub>1 sporadic \<tau> on K\<^sub>2) # \<Psi> \<triangleright> \<Phi> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g = \<lbrakk> \<Gamma>, k \<turnstile> \<Psi> \<triangleright> (K\<^sub>1 sporadic \<tau> on K\<^sub>2) # \<Phi> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g
                                                                         \<union> \<lbrakk> K\<^sub>1 \<Up> k # K\<^sub>2 \<Down> k @ \<tau> # \<Gamma>, k \<turnstile> \<Psi> \<triangleright> \<Phi> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g"
            using HeronConf_interp_at_index_sporadicon_cases by simp
      have br1: "\<rho> \<in> \<lbrakk> \<Gamma>, k \<turnstile> \<Psi> \<triangleright> (K\<^sub>1 sporadic \<tau> on K\<^sub>2) # \<Phi> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g \<Longrightarrow> \<exists>\<Gamma>\<^sub>n \<Psi>\<^sub>n \<Phi>\<^sub>n n.
       \<Gamma>, k \<turnstile> (K\<^sub>1 sporadic \<tau> on K\<^sub>2) # \<Psi> \<triangleright> \<Phi> \<hookrightarrow>\<^bsup>n\<^esup> \<Gamma>\<^sub>n, Suc k \<turnstile> \<Psi>\<^sub>n \<triangleright> \<Phi>\<^sub>n \<and>
       \<rho> \<in> \<lbrakk> \<Gamma>\<^sub>n, Suc k \<turnstile> \<Psi>\<^sub>n \<triangleright> \<Phi>\<^sub>n \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g"
        proof -
          assume h1: "\<rho> \<in> \<lbrakk> \<Gamma>, k \<turnstile> \<Psi> \<triangleright> (K\<^sub>1 sporadic \<tau> on K\<^sub>2) # \<Phi> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g"
          then have "\<exists>\<Gamma>\<^sub>n \<Psi>\<^sub>n \<Phi>\<^sub>n n. (\<Gamma>, k \<turnstile> \<Psi> \<triangleright> (K\<^sub>1 sporadic \<tau> on K\<^sub>2) # \<Phi>) \<hookrightarrow>\<^bsup>n\<^esup> \<Gamma>\<^sub>n, Suc k \<turnstile> \<Psi>\<^sub>n \<triangleright> \<Phi>\<^sub>n \<and> \<rho> \<in> \<lbrakk> \<Gamma>\<^sub>n, Suc k \<turnstile> \<Psi>\<^sub>n \<triangleright> \<Phi>\<^sub>n \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g"
            using h1 SporadicOn.prems by simp
          then show ?thesis
            by (meson elims_part relpowp_Suc_I2 sporadic_on_e1)
        qed
      moreover have br2: "\<rho> \<in> \<lbrakk> K\<^sub>1 \<Up> k # K\<^sub>2 \<Down> k @ \<tau> # \<Gamma>, k \<turnstile> \<Psi> \<triangleright> \<Phi> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g \<Longrightarrow> \<exists>\<Gamma>\<^sub>n \<Psi>\<^sub>n \<Phi>\<^sub>n n.
       (\<Gamma>, k \<turnstile> (K\<^sub>1 sporadic \<tau> on K\<^sub>2) # \<Psi> \<triangleright> \<Phi>) \<hookrightarrow>\<^bsup>n\<^esup> (\<Gamma>\<^sub>n, Suc k \<turnstile> \<Psi>\<^sub>n \<triangleright> \<Phi>\<^sub>n) \<and>
       \<rho> \<in> \<lbrakk> \<Gamma>\<^sub>n, Suc k \<turnstile> \<Psi>\<^sub>n \<triangleright> \<Phi>\<^sub>n \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g"
        proof -
          assume h2: "\<rho> \<in> \<lbrakk> K\<^sub>1 \<Up> k # K\<^sub>2 \<Down> k @ \<tau> # \<Gamma>, k \<turnstile> \<Psi> \<triangleright> \<Phi> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g"
          then have "\<exists>\<Gamma>\<^sub>n \<Psi>\<^sub>n \<Phi>\<^sub>n n. ((K\<^sub>1 \<Up> k) # (K\<^sub>2 \<Down> k @ \<tau>) # \<Gamma>, k \<turnstile> \<Psi> \<triangleright> \<Phi>) \<hookrightarrow>\<^bsup>n\<^esup> \<Gamma>\<^sub>n, Suc k \<turnstile> \<Psi>\<^sub>n \<triangleright> \<Phi>\<^sub>n \<and> \<rho> \<in> \<lbrakk> \<Gamma>\<^sub>n, Suc k \<turnstile> \<Psi>\<^sub>n \<triangleright> \<Phi>\<^sub>n \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g"
            using h2 SporadicOn.prems by simp
          then show ?thesis
            by (meson elims_part relpowp_Suc_I2 sporadic_on_e2)
        qed
      ultimately show ?case
        by (metis SporadicOn.prems(2) UnE branches)
    next
      case (TagRelation K\<^sub>1 \<alpha> K\<^sub>2 \<beta>)
      have branches: "\<lbrakk> \<Gamma>, k \<turnstile> (tag-relation K\<^sub>1 = \<alpha> * K\<^sub>2 + \<beta>) # \<Psi> \<triangleright> \<Phi> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g
          = \<lbrakk> (\<tau>\<^sub>v\<^sub>a\<^sub>r(K\<^sub>1, k) \<doteq> \<alpha> * \<tau>\<^sub>v\<^sub>a\<^sub>r(K\<^sub>2, k) + \<beta>) # \<Gamma>, k \<turnstile> \<Psi> \<triangleright> (tag-relation K\<^sub>1 = \<alpha> * K\<^sub>2 + \<beta>) # \<Phi> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g"
        using HeronConf_interp_at_index_tagrel_cases by simp
      then show ?case
        proof -
          have "\<exists>\<Gamma>\<^sub>n \<Psi>\<^sub>n \<Phi>\<^sub>n n. ((\<tau>\<^sub>v\<^sub>a\<^sub>r(K\<^sub>1, k) \<doteq> \<alpha> * \<tau>\<^sub>v\<^sub>a\<^sub>r(K\<^sub>2, k) + \<beta>) # \<Gamma>, k \<turnstile> \<Psi> \<triangleright> (tag-relation K\<^sub>1 = \<alpha> * K\<^sub>2 + \<beta>) # \<Phi>)
              \<hookrightarrow>\<^bsup>n\<^esup> \<Gamma>\<^sub>n, Suc k \<turnstile> \<Psi>\<^sub>n \<triangleright> \<Phi>\<^sub>n \<and> \<rho> \<in> \<lbrakk> \<Gamma>\<^sub>n, Suc k \<turnstile> \<Psi>\<^sub>n \<triangleright> \<Phi>\<^sub>n \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g"
            using TagRelation.prems by simp
          then show ?thesis
            by (meson elims_part relpowp_Suc_I2 tagrel_e)
        qed
    next
      case (Implies K\<^sub>1 K\<^sub>2)
      have branches: "\<lbrakk> \<Gamma>, k \<turnstile> (K\<^sub>1 implies K\<^sub>2) # \<Psi> \<triangleright> \<Phi> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g
          = \<lbrakk> K\<^sub>1 \<not>\<Up> k # \<Gamma>, k \<turnstile> \<Psi> \<triangleright> (K\<^sub>1 implies K\<^sub>2) # \<Phi> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g
          \<union> \<lbrakk> K\<^sub>1 \<Up> k # K\<^sub>2 \<Up> k # \<Gamma>, k \<turnstile> \<Psi> \<triangleright> (K\<^sub>1 implies K\<^sub>2) # \<Phi> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g"
        using HeronConf_interp_at_index_implies_cases by simp
      have br1: "\<rho> \<in> \<lbrakk> K\<^sub>1 \<not>\<Up> k # \<Gamma>, k \<turnstile> \<Psi> \<triangleright> (K\<^sub>1 implies K\<^sub>2) # \<Phi> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g \<Longrightarrow> \<exists>\<Gamma>\<^sub>n \<Psi>\<^sub>n \<Phi>\<^sub>n n.
       \<Gamma>, k \<turnstile> (K\<^sub>1 implies K\<^sub>2) # \<Psi> \<triangleright> \<Phi> \<hookrightarrow>\<^bsup>n\<^esup> \<Gamma>\<^sub>n, Suc k \<turnstile> \<Psi>\<^sub>n \<triangleright> \<Phi>\<^sub>n \<and>
       \<rho> \<in> \<lbrakk> \<Gamma>\<^sub>n, Suc k \<turnstile> \<Psi>\<^sub>n \<triangleright> \<Phi>\<^sub>n \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g"
        proof -
          assume h1: "\<rho> \<in> \<lbrakk> K\<^sub>1 \<not>\<Up> k # \<Gamma>, k \<turnstile> \<Psi> \<triangleright> (K\<^sub>1 implies K\<^sub>2) # \<Phi> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g"
          then have "\<exists>\<Gamma>\<^sub>n \<Psi>\<^sub>n \<Phi>\<^sub>n n. (K\<^sub>1 \<not>\<Up> k # \<Gamma>, k \<turnstile> \<Psi> \<triangleright> (K\<^sub>1 implies K\<^sub>2) # \<Phi>) \<hookrightarrow>\<^bsup>n\<^esup> \<Gamma>\<^sub>n, Suc k \<turnstile> \<Psi>\<^sub>n \<triangleright> \<Phi>\<^sub>n \<and> \<rho> \<in> \<lbrakk> \<Gamma>\<^sub>n, Suc k \<turnstile> \<Psi>\<^sub>n \<triangleright> \<Phi>\<^sub>n \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g"
            using h1 Implies.prems by simp
          then show ?thesis
            by (meson elims_part relpowp_Suc_I2 implies_e1)
        qed
      moreover have br2: "\<rho> \<in> \<lbrakk> (K\<^sub>1 \<Up> k) # (K\<^sub>2 \<Up> k) # \<Gamma>, k \<turnstile> \<Psi> \<triangleright> (K\<^sub>1 implies K\<^sub>2) # \<Phi> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g \<Longrightarrow> \<exists>\<Gamma>\<^sub>n \<Psi>\<^sub>n \<Phi>\<^sub>n n.
       \<Gamma>, k \<turnstile> (K\<^sub>1 implies K\<^sub>2) # \<Psi> \<triangleright> \<Phi> \<hookrightarrow>\<^bsup>n\<^esup> \<Gamma>\<^sub>n, Suc k \<turnstile> \<Psi>\<^sub>n \<triangleright> \<Phi>\<^sub>n \<and>
       \<rho> \<in> \<lbrakk> \<Gamma>\<^sub>n, Suc k \<turnstile> \<Psi>\<^sub>n \<triangleright> \<Phi>\<^sub>n \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g"
        proof -
          assume h2: "\<rho> \<in> \<lbrakk> (K\<^sub>1 \<Up> k) # (K\<^sub>2 \<Up> k) # \<Gamma>, k \<turnstile> \<Psi> \<triangleright> (K\<^sub>1 implies K\<^sub>2) # \<Phi> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g"
          then have "\<exists>\<Gamma>\<^sub>n \<Psi>\<^sub>n \<Phi>\<^sub>n n. ((K\<^sub>1 \<Up> k) # (K\<^sub>2 \<Up> k) # \<Gamma>, k \<turnstile> \<Psi> \<triangleright> (K\<^sub>1 implies K\<^sub>2) # \<Phi>) \<hookrightarrow>\<^bsup>n\<^esup> \<Gamma>\<^sub>n, Suc k \<turnstile> \<Psi>\<^sub>n \<triangleright> \<Phi>\<^sub>n \<and> \<rho> \<in> \<lbrakk> \<Gamma>\<^sub>n, Suc k \<turnstile> \<Psi>\<^sub>n \<triangleright> \<Phi>\<^sub>n \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g"
            using h2 Implies.prems by simp
          then show ?thesis
            by (meson elims_part relpowp_Suc_I2 implies_e2)
        qed
      ultimately show ?case
        using Implies.prems(2) by fastforce
    next
      case (TimeDelayedBy K\<^sub>1 \<delta>\<tau> K\<^sub>2 K\<^sub>3)
      have branches: "\<lbrakk> \<Gamma>, k \<turnstile> (K\<^sub>1 time-delayed by \<delta>\<tau> on K\<^sub>2 implies K\<^sub>3) # \<Psi> \<triangleright> \<Phi> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g
          = \<lbrakk> K\<^sub>1 \<not>\<Up> k # \<Gamma>, k \<turnstile> \<Psi> \<triangleright> (K\<^sub>1 time-delayed by \<delta>\<tau> on K\<^sub>2 implies K\<^sub>3) # \<Phi> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g
          \<union> \<lbrakk> K\<^sub>1 \<Up> k # \<Gamma>, k \<turnstile> (K\<^sub>3 sporadic \<lfloor>\<tau>\<^sub>v\<^sub>a\<^sub>r(K\<^sub>2, k) \<oplus> \<delta>\<tau>\<rfloor> on K\<^sub>2) # \<Psi> \<triangleright> (K\<^sub>1 time-delayed by \<delta>\<tau> on K\<^sub>2 implies K\<^sub>3) # \<Phi> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g"
        using HeronConf_interp_at_index_timedelayed_cases by simp
      have more_branches: "\<lbrakk> K\<^sub>1 \<Up> k # \<Gamma>, k \<turnstile> (K\<^sub>3 sporadic \<lfloor>\<tau>\<^sub>v\<^sub>a\<^sub>r(K\<^sub>2, k) \<oplus> \<delta>\<tau>\<rfloor> on K\<^sub>2) # \<Psi> \<triangleright> (K\<^sub>1 time-delayed by \<delta>\<tau> on K\<^sub>2 implies K\<^sub>3) # \<Phi> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g
                  = \<lbrakk> K\<^sub>1 \<Up> k # \<Gamma>, k \<turnstile> \<Psi> \<triangleright> (K\<^sub>3 sporadic \<lfloor>\<tau>\<^sub>v\<^sub>a\<^sub>r(K\<^sub>2, k) \<oplus> \<delta>\<tau>\<rfloor> on K\<^sub>2) # (K\<^sub>1 time-delayed by \<delta>\<tau> on K\<^sub>2 implies K\<^sub>3) # \<Phi> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g
                  \<union> \<lbrakk> (K\<^sub>3 \<Up> k) # (K\<^sub>2 \<Down> k @ \<lfloor>\<tau>\<^sub>v\<^sub>a\<^sub>r(K\<^sub>2, k) \<oplus> \<delta>\<tau>\<rfloor>) # (K\<^sub>1 \<Up> k) # \<Gamma>, k \<turnstile> \<Psi> \<triangleright> (K\<^sub>1 time-delayed by \<delta>\<tau> on K\<^sub>2 implies K\<^sub>3) # \<Phi> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g"
            using HeronConf_interp_at_index_sporadicon_cases by blast
      have br1: "\<rho> \<in> \<lbrakk> K\<^sub>1 \<not>\<Up> k # \<Gamma>, k \<turnstile> \<Psi> \<triangleright> (K\<^sub>1 time-delayed by \<delta>\<tau> on K\<^sub>2 implies K\<^sub>3) # \<Phi> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g \<Longrightarrow> \<exists>\<Gamma>\<^sub>n \<Psi>\<^sub>n \<Phi>\<^sub>n n.
       \<Gamma>, k \<turnstile> (K\<^sub>1 time-delayed by \<delta>\<tau> on K\<^sub>2 implies K\<^sub>3) # \<Psi> \<triangleright> \<Phi> \<hookrightarrow>\<^bsup>n\<^esup> \<Gamma>\<^sub>n, Suc k \<turnstile> \<Psi>\<^sub>n \<triangleright> \<Phi>\<^sub>n \<and>
       \<rho> \<in> \<lbrakk> \<Gamma>\<^sub>n, Suc k \<turnstile> \<Psi>\<^sub>n \<triangleright> \<Phi>\<^sub>n \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g"
        proof -
          assume h1: "\<rho> \<in> \<lbrakk> K\<^sub>1 \<not>\<Up> k # \<Gamma>, k \<turnstile> \<Psi> \<triangleright> (K\<^sub>1 time-delayed by \<delta>\<tau> on K\<^sub>2 implies K\<^sub>3) # \<Phi> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g"
          then have "\<exists>\<Gamma>\<^sub>n \<Psi>\<^sub>n \<Phi>\<^sub>n n. (K\<^sub>1 \<not>\<Up> k # \<Gamma>, k \<turnstile> \<Psi> \<triangleright> (K\<^sub>1 time-delayed by \<delta>\<tau> on K\<^sub>2 implies K\<^sub>3) # \<Phi>) \<hookrightarrow>\<^bsup>n\<^esup> \<Gamma>\<^sub>n, Suc k \<turnstile> \<Psi>\<^sub>n \<triangleright> \<Phi>\<^sub>n \<and> \<rho> \<in> \<lbrakk> \<Gamma>\<^sub>n, Suc k \<turnstile> \<Psi>\<^sub>n \<triangleright> \<Phi>\<^sub>n \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g"
            using h1 TimeDelayedBy.prems by simp
          then show ?thesis
            by (meson elims_part relpowp_Suc_I2 timedelayed_e1)
        qed
      moreover have br2: "\<rho> \<in> \<lbrakk> K\<^sub>1 \<Up> k # \<Gamma>, k \<turnstile> \<Psi> \<triangleright> (K\<^sub>3 sporadic \<lfloor>\<tau>\<^sub>v\<^sub>a\<^sub>r(K\<^sub>2, k) \<oplus> \<delta>\<tau>\<rfloor> on K\<^sub>2) # (K\<^sub>1 time-delayed by \<delta>\<tau> on K\<^sub>2 implies K\<^sub>3) # \<Phi> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g \<Longrightarrow> \<exists>\<Gamma>\<^sub>n \<Psi>\<^sub>n \<Phi>\<^sub>n n.
       \<Gamma>, k \<turnstile> (K\<^sub>1 time-delayed by \<delta>\<tau> on K\<^sub>2 implies K\<^sub>3) # \<Psi> \<triangleright> \<Phi> \<hookrightarrow>\<^bsup>n\<^esup> \<Gamma>\<^sub>n, Suc k \<turnstile> \<Psi>\<^sub>n \<triangleright> \<Phi>\<^sub>n \<and>
       \<rho> \<in> \<lbrakk> \<Gamma>\<^sub>n, Suc k \<turnstile> \<Psi>\<^sub>n \<triangleright> \<Phi>\<^sub>n \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g"
        proof -
          assume h2: "\<rho> \<in> \<lbrakk> K\<^sub>1 \<Up> k # \<Gamma>, k \<turnstile> \<Psi> \<triangleright> (K\<^sub>3 sporadic \<lfloor>\<tau>\<^sub>v\<^sub>a\<^sub>r(K\<^sub>2, k) \<oplus> \<delta>\<tau>\<rfloor> on K\<^sub>2) # (K\<^sub>1 time-delayed by \<delta>\<tau> on K\<^sub>2 implies K\<^sub>3) # \<Phi> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g"
          then have "\<exists>\<Gamma>\<^sub>n \<Psi>\<^sub>n \<Phi>\<^sub>n n. (K\<^sub>1 \<Up> k # \<Gamma>, k \<turnstile> \<Psi> \<triangleright> (K\<^sub>3 sporadic \<lfloor>\<tau>\<^sub>v\<^sub>a\<^sub>r(K\<^sub>2, k) \<oplus> \<delta>\<tau>\<rfloor> on K\<^sub>2) # (K\<^sub>1 time-delayed by \<delta>\<tau> on K\<^sub>2 implies K\<^sub>3) # \<Phi>) \<hookrightarrow>\<^bsup>n\<^esup> \<Gamma>\<^sub>n, Suc k \<turnstile> \<Psi>\<^sub>n \<triangleright> \<Phi>\<^sub>n \<and> \<rho> \<in> \<lbrakk> \<Gamma>\<^sub>n, Suc k \<turnstile> \<Psi>\<^sub>n \<triangleright> \<Phi>\<^sub>n \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g"
            using h2 TimeDelayedBy.prems by simp
          then show ?thesis
            by (meson elims_part relpowp_Suc_I2 timedelayed_e2 sporadic_on_e1)
        qed
      moreover have br2': "\<rho> \<in> \<lbrakk> (K\<^sub>3 \<Up> k) # (K\<^sub>2 \<Down> k @ \<lfloor>\<tau>\<^sub>v\<^sub>a\<^sub>r(K\<^sub>2, k) \<oplus> \<delta>\<tau>\<rfloor>) # (K\<^sub>1 \<Up> k) # \<Gamma>, k \<turnstile> \<Psi> \<triangleright> (K\<^sub>1 time-delayed by \<delta>\<tau> on K\<^sub>2 implies K\<^sub>3) # \<Phi> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g \<Longrightarrow> \<exists>\<Gamma>\<^sub>n \<Psi>\<^sub>n \<Phi>\<^sub>n n.
       \<Gamma>, k \<turnstile> (K\<^sub>1 time-delayed by \<delta>\<tau> on K\<^sub>2 implies K\<^sub>3) # \<Psi> \<triangleright> \<Phi> \<hookrightarrow>\<^bsup>n\<^esup> \<Gamma>\<^sub>n, Suc k \<turnstile> \<Psi>\<^sub>n \<triangleright> \<Phi>\<^sub>n \<and>
       \<rho> \<in> \<lbrakk> \<Gamma>\<^sub>n, Suc k \<turnstile> \<Psi>\<^sub>n \<triangleright> \<Phi>\<^sub>n \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g"
        proof -
          assume h2: "\<rho> \<in> \<lbrakk> (K\<^sub>3 \<Up> k) # (K\<^sub>2 \<Down> k @ \<lfloor>\<tau>\<^sub>v\<^sub>a\<^sub>r(K\<^sub>2, k) \<oplus> \<delta>\<tau>\<rfloor>) # (K\<^sub>1 \<Up> k) # \<Gamma>, k \<turnstile> \<Psi> \<triangleright> (K\<^sub>1 time-delayed by \<delta>\<tau> on K\<^sub>2 implies K\<^sub>3) # \<Phi> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g"
          then have "\<exists>\<Gamma>\<^sub>n \<Psi>\<^sub>n \<Phi>\<^sub>n n. ((K\<^sub>3 \<Up> k) # (K\<^sub>2 \<Down> k @ \<lfloor>\<tau>\<^sub>v\<^sub>a\<^sub>r(K\<^sub>2, k) \<oplus> \<delta>\<tau>\<rfloor>) # (K\<^sub>1 \<Up> k) # \<Gamma>, k \<turnstile> \<Psi> \<triangleright> (K\<^sub>1 time-delayed by \<delta>\<tau> on K\<^sub>2 implies K\<^sub>3) # \<Phi>) \<hookrightarrow>\<^bsup>n\<^esup> \<Gamma>\<^sub>n, Suc k \<turnstile> \<Psi>\<^sub>n \<triangleright> \<Phi>\<^sub>n \<and> \<rho> \<in> \<lbrakk> \<Gamma>\<^sub>n, Suc k \<turnstile> \<Psi>\<^sub>n \<triangleright> \<Phi>\<^sub>n \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g"
            using h2 TimeDelayedBy.prems by simp
          then show ?thesis
            by (meson elims_part relpowp_Suc_I2 timedelayed_e2 sporadic_on_e2)
        qed
      ultimately show ?case
        using TimeDelayedBy.prems(2) by (metis UnE branches more_branches)
    qed
  qed

lemma HeronConf_interp_at_index_next_instant_run_presv_generalized:
  assumes "k < k\<^sub>n"
  assumes "\<rho> \<in> \<lbrakk> \<Gamma>, k \<turnstile> \<Psi> \<triangleright> \<Phi> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g"
  shows   "\<exists>\<Gamma>\<^sub>n \<Psi>\<^sub>n \<Phi>\<^sub>n n. \<Gamma>, k \<turnstile> \<Psi> \<triangleright> \<Phi>  \<hookrightarrow>\<^bsup>n\<^esup>  \<Gamma>\<^sub>n, k\<^sub>n \<turnstile> \<Psi>\<^sub>n \<triangleright> \<Phi>\<^sub>n
                         \<and> \<rho> \<in> \<lbrakk> \<Gamma>\<^sub>n, k\<^sub>n \<turnstile> \<Psi>\<^sub>n \<triangleright> \<Phi>\<^sub>n \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g"
  proof -
    obtain \<delta>n where diff: "k\<^sub>n = \<delta>n + Suc k"
      using add.commute assms(1) less_iff_Suc_add by auto
    show ?thesis
      proof (subst diff, subst diff, insert assms(2), induct \<delta>n)
        case 0
        then show ?case
          using HeronConf_interp_at_index_next_instant_run_presv assms(2) by simp
      next
        case (Suc \<delta>n)
        have f0: "\<rho> \<in> \<lbrakk> \<Gamma>, k \<turnstile> \<Psi> \<triangleright> \<Phi> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g \<Longrightarrow> \<exists>\<Gamma>\<^sub>n \<Psi>\<^sub>n \<Phi>\<^sub>n n.
             \<Gamma>, k \<turnstile> \<Psi> \<triangleright> \<Phi> \<hookrightarrow>\<^bsup>n\<^esup> \<Gamma>\<^sub>n, \<delta>n + Suc k \<turnstile> \<Psi>\<^sub>n \<triangleright> \<Phi>\<^sub>n \<and>
             \<rho> \<in> \<lbrakk> \<Gamma>\<^sub>n, \<delta>n + Suc k \<turnstile> \<Psi>\<^sub>n \<triangleright> \<Phi>\<^sub>n \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g"
          using Suc.hyps by blast
        obtain \<Gamma>\<^sub>n \<Psi>\<^sub>n \<Phi>\<^sub>n n where cont: "\<Gamma>, k \<turnstile> \<Psi> \<triangleright> \<Phi> \<hookrightarrow>\<^bsup>n\<^esup> \<Gamma>\<^sub>n, \<delta>n + Suc k \<turnstile> \<Psi>\<^sub>n \<triangleright> \<Phi>\<^sub>n \<and> \<rho> \<in> \<lbrakk> \<Gamma>\<^sub>n, \<delta>n + Suc k \<turnstile> \<Psi>\<^sub>n \<triangleright> \<Phi>\<^sub>n \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g" using f0 assms(1)
          using Suc.prems by blast
        then have fcontinue: "\<exists>\<Gamma>\<^sub>n' \<Psi>\<^sub>n' \<Phi>\<^sub>n' n'. \<Gamma>\<^sub>n, \<delta>n + Suc k \<turnstile> \<Psi>\<^sub>n \<triangleright> \<Phi>\<^sub>n \<hookrightarrow>\<^bsup>n'\<^esup> \<Gamma>\<^sub>n', Suc (\<delta>n + Suc k) \<turnstile> \<Psi>\<^sub>n' \<triangleright> \<Phi>\<^sub>n' \<and>
              \<rho> \<in> \<lbrakk> \<Gamma>\<^sub>n', Suc (\<delta>n + Suc k) \<turnstile> \<Psi>\<^sub>n' \<triangleright> \<Phi>\<^sub>n' \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g"
          using f0 cont HeronConf_interp_at_index_next_instant_run_presv by blast
        obtain \<Gamma>\<^sub>n' \<Psi>\<^sub>n' \<Phi>\<^sub>n' n' where cont2: "\<Gamma>\<^sub>n, \<delta>n + Suc k \<turnstile> \<Psi>\<^sub>n \<triangleright> \<Phi>\<^sub>n \<hookrightarrow>\<^bsup>n'\<^esup> \<Gamma>\<^sub>n', Suc (\<delta>n + Suc k) \<turnstile> \<Psi>\<^sub>n' \<triangleright> \<Phi>\<^sub>n' \<and> \<rho> \<in> \<lbrakk> \<Gamma>\<^sub>n', Suc (\<delta>n + Suc k) \<turnstile> \<Psi>\<^sub>n' \<triangleright> \<Phi>\<^sub>n' \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g"
          using Suc.prems using fcontinue cont by blast
        have trans: "\<Gamma>, k \<turnstile> \<Psi> \<triangleright> \<Phi> \<hookrightarrow>\<^bsup>n + n'\<^esup> \<Gamma>\<^sub>n', Suc (\<delta>n + Suc k) \<turnstile> \<Psi>\<^sub>n' \<triangleright> \<Phi>\<^sub>n'"
          using operational_semantics_trans_generalized cont cont2
          by blast
        moreover have suc_assoc: "Suc \<delta>n + Suc k = Suc (\<delta>n + Suc k)"
          by arith
        ultimately show ?case 
          proof (subst suc_assoc)
          show "\<exists>\<Gamma>\<^sub>n \<Psi>\<^sub>n \<Phi>\<^sub>n n.
               \<Gamma>, k \<turnstile> \<Psi> \<triangleright> \<Phi> \<hookrightarrow>\<^bsup>n\<^esup> \<Gamma>\<^sub>n, Suc (\<delta>n + Suc k) \<turnstile> \<Psi>\<^sub>n \<triangleright> \<Phi>\<^sub>n \<and>
               \<rho> \<in> \<lbrakk> \<Gamma>\<^sub>n, Suc \<delta>n + Suc k \<turnstile> \<Psi>\<^sub>n \<triangleright> \<Phi>\<^sub>n \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g"
            using cont2 local.trans by auto
          qed
    qed
  qed

end
