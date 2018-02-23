theory Denotational
imports
    "TESL"
    "Run"

begin

section \<open>Denotational interpretation for atomic TESL formulae\<close>

(* Denotational interpretation of TESL atomic formulae *)
fun TESL_interpretation_atomic
    :: "('\<tau>::linordered_field) TESL_atomic \<Rightarrow> '\<tau> run set" ("\<lbrakk> _ \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L") where
    "\<lbrakk> K\<^sub>1 sporadic \<lfloor>\<tau>\<rfloor> on K\<^sub>2 \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L =
        { \<rho>. \<exists>n::nat. hamlet ((Rep_run \<rho>) n K\<^sub>1) = True \<and> time ((Rep_run \<rho>) n K\<^sub>2) = \<tau> }"
  | "\<lbrakk> K\<^sub>1 sporadic \<lfloor>\<tau>\<^sub>v\<^sub>a\<^sub>r(K\<^sub>i, n\<^sub>i) \<oplus> \<delta>\<tau>\<rfloor> on K\<^sub>2 \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L =
        { \<rho>. \<exists>n::nat. hamlet ((Rep_run \<rho>) n K\<^sub>1) = True
                       \<and> time ((Rep_run \<rho>) n K\<^sub>2) = time ((Rep_run \<rho>) n\<^sub>i K\<^sub>i) + \<delta>\<tau> }"
  (* | "\<lbrakk> tag-relation K\<^sub>1 = \<alpha> * K\<^sub>2 + \<beta> \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L =
        { \<rho>. \<forall>n::nat. time ((Rep_run \<rho>) n K\<^sub>1) = \<alpha> * time ((Rep_run \<rho>) n K\<^sub>2) + \<beta> }" *)
  | "\<lbrakk> tag-relation \<langle>K\<^sub>1, K\<^sub>2\<rangle> \<in> R \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L =
        { \<rho>. \<forall>n::nat. R (time ((Rep_run \<rho>) n K\<^sub>1), time ((Rep_run \<rho>) n K\<^sub>2)) }"
  | "\<lbrakk> master implies slave \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L =
        { \<rho>. \<forall>n::nat. hamlet ((Rep_run \<rho>) n master) \<longrightarrow> hamlet ((Rep_run \<rho>) n slave) }"
  | "\<lbrakk> master implies not slave \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L =
        { \<rho>. \<forall>n::nat. hamlet ((Rep_run \<rho>) n master) \<longrightarrow> \<not> hamlet ((Rep_run \<rho>) n slave) }"
  | "\<lbrakk> master time-delayed by \<delta>\<tau> on measuring implies slave \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L =
        { \<rho>. \<forall>n. hamlet ((Rep_run \<rho>) n master) \<longrightarrow>
                 (let measured_time = time ((Rep_run \<rho>) n measuring) in
                  \<exists>m \<ge> n. hamlet ((Rep_run \<rho>) m slave)
                          \<and> time ((Rep_run \<rho>) m measuring) = measured_time + \<delta>\<tau>
                 )
        }"
  | "\<lbrakk> K\<^sub>1 precedes K\<^sub>2 \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L =
        { \<rho>. \<forall>n::nat. (run_tick_count \<rho> K\<^sub>2 n) \<le> (run_tick_count_strictly \<rho> K\<^sub>1 n) }"

section \<open>Denotational interpretation for TESL formulae\<close>

fun TESL_interpretation :: "('\<tau>::linordered_field) TESL_formula \<Rightarrow> '\<tau> run set" ("\<lbrakk>\<lbrakk> _ \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L") where
    "\<lbrakk>\<lbrakk> [] \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L = { _. True }"
  | "\<lbrakk>\<lbrakk> \<phi> # \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L = \<lbrakk> \<phi> \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L \<inter> \<lbrakk>\<lbrakk> \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L"

lemma TESL_interpretation_homo:
  "\<lbrakk> \<phi> \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L \<inter> \<lbrakk>\<lbrakk> \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L = \<lbrakk>\<lbrakk> \<phi> # \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L"
  by auto

subsection \<open>Image interpretation lemma\<close>

theorem TESL_interpretation_image:
  "\<lbrakk>\<lbrakk> \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L = \<Inter> ((\<lambda>\<phi>. \<lbrakk> \<phi> \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L) ` set \<Phi>)"
  proof (induct \<Phi>)
    case Nil
    then show ?case by simp
  next
    case (Cons a \<Phi>)
    then show ?case by auto
  qed

subsection \<open>Expansion law\<close>
text \<open>Similar to the expansion laws of lattices\<close>

theorem TESL_interp_homo_append:
  shows "\<lbrakk>\<lbrakk> \<Phi>\<^sub>1 @ \<Phi>\<^sub>2 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L = \<lbrakk>\<lbrakk> \<Phi>\<^sub>1 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L \<inter> \<lbrakk>\<lbrakk> \<Phi>\<^sub>2 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L"
  proof (induct \<Phi>\<^sub>1)
    case Nil
    then show ?case by simp
  next
    case (Cons a \<Phi>\<^sub>1)
    then show ?case by auto
  qed


subsection \<open>Equational laws for TESL formulae denotationally interpreted\<close>

lemma TESL_interp_assoc:
  shows "\<lbrakk>\<lbrakk> (\<Phi>\<^sub>1 @ \<Phi>\<^sub>2) @ \<Phi>\<^sub>3 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L = \<lbrakk>\<lbrakk> \<Phi>\<^sub>1 @ (\<Phi>\<^sub>2 @ \<Phi>\<^sub>3) \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L"
  by auto

lemma TESL_interp_commute:
  shows "\<lbrakk>\<lbrakk> \<Phi>\<^sub>1 @ \<Phi>\<^sub>2 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L = \<lbrakk>\<lbrakk> \<Phi>\<^sub>2 @ \<Phi>\<^sub>1 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L"
  by (simp add: TESL_interp_homo_append inf_sup_aci(1))

lemma TESL_interp_left_commute:
  shows "\<lbrakk>\<lbrakk> \<Phi>\<^sub>1 @ (\<Phi>\<^sub>2 @ \<Phi>\<^sub>3) \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L = \<lbrakk>\<lbrakk> \<Phi>\<^sub>2 @ (\<Phi>\<^sub>1 @ \<Phi>\<^sub>3) \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L"
  unfolding TESL_interp_homo_append by auto

lemma TESL_interp_idem:
  shows "\<lbrakk>\<lbrakk> \<Phi> @ \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L = \<lbrakk>\<lbrakk> \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L"
  using TESL_interp_homo_append by auto

lemma TESL_interp_left_idem:
  shows "\<lbrakk>\<lbrakk> \<Phi>\<^sub>1 @ (\<Phi>\<^sub>1 @ \<Phi>\<^sub>2) \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L = \<lbrakk>\<lbrakk> \<Phi>\<^sub>1 @ \<Phi>\<^sub>2 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L"
  using TESL_interp_homo_append by auto

lemma TESL_interp_right_idem:
  shows "\<lbrakk>\<lbrakk> (\<Phi>\<^sub>1 @ \<Phi>\<^sub>2) @ \<Phi>\<^sub>2 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L = \<lbrakk>\<lbrakk> \<Phi>\<^sub>1 @ \<Phi>\<^sub>2 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L"
  unfolding TESL_interp_homo_append by auto

lemmas TESL_interp_aci = TESL_interp_commute TESL_interp_assoc TESL_interp_left_commute TESL_interp_left_idem

(* Identity element *)
lemma TESL_interp_neutral1:
  shows "\<lbrakk>\<lbrakk> [] @ \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L = \<lbrakk>\<lbrakk> \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L"
  by simp

lemma TESL_interp_neutral2:
  shows "\<lbrakk>\<lbrakk> \<Phi> @ [] \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L = \<lbrakk>\<lbrakk> \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L"
  by simp

section \<open>Decreasing interpretation of TESL formulae\<close>

lemma TESL_sem_decreases_head:
  "\<lbrakk>\<lbrakk> \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L \<supseteq> \<lbrakk>\<lbrakk> \<phi> # \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L"
  by simp

lemma TESL_sem_decreases_tail:
  "\<lbrakk>\<lbrakk> \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L \<supseteq> \<lbrakk>\<lbrakk> \<Phi> @ [\<phi>] \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L"
  by (simp add: TESL_interp_homo_append)

lemma TESL_interp_formula_stuttering:
  assumes bel: "\<phi> \<in> set \<Phi>"
  shows "\<lbrakk>\<lbrakk> \<phi> # \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L = \<lbrakk>\<lbrakk> \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L"
  by (metis Int_subset_iff TESL_interp_homo_append TESL_interpretation.simps(2) bel in_set_conv_decomp_first subset_antisym subset_refl)

lemma TESL_interp_decreases:
  shows "\<lbrakk>\<lbrakk> \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L \<supseteq> \<lbrakk>\<lbrakk> \<phi> # \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L"
  by (rule TESL_sem_decreases_head)

lemma TESL_interp_remdups_absorb:
  shows "\<lbrakk>\<lbrakk> \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L = \<lbrakk>\<lbrakk> remdups \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L"
  proof (induct \<Phi>)
    case Nil
    then show ?case by simp
  next
    case (Cons a \<Phi>)
    then show ?case
      using TESL_interp_formula_stuttering by auto
  qed

lemma TESL_interp_set_lifting:
  assumes "set \<Phi> = set \<Phi>'"
  shows "\<lbrakk>\<lbrakk> \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L = \<lbrakk>\<lbrakk> \<Phi>' \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L"
  proof -     
    have "set (remdups \<Phi>) = set (remdups \<Phi>')"
      by (simp add: assms)
    moreover have fxpnt\<Phi>: "\<Inter> ((\<lambda>\<phi>. \<lbrakk> \<phi> \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L) ` set \<Phi>) = \<lbrakk>\<lbrakk> \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L"
      by (simp add: TESL_interpretation_image)
    moreover have fxpnt\<Phi>': "\<Inter> ((\<lambda>\<phi>. \<lbrakk> \<phi> \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L) ` set \<Phi>') = \<lbrakk>\<lbrakk> \<Phi>' \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L"
      by (simp add: TESL_interpretation_image)
    moreover have "\<Inter> ((\<lambda>\<phi>. \<lbrakk> \<phi> \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L) ` set \<Phi>) = \<Inter> ((\<lambda>\<phi>. \<lbrakk> \<phi> \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L) ` set \<Phi>')"
      by (simp add: assms)
    ultimately show ?thesis using TESL_interp_remdups_absorb by auto
  qed

theorem TESL_interp_decreases_setinc:
  assumes incl: "set \<Phi> \<subseteq> set \<Phi>'"
  shows "\<lbrakk>\<lbrakk> \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L \<supseteq> \<lbrakk>\<lbrakk> \<Phi>' \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L"
  proof -
    obtain \<Phi>\<^sub>r where decompose: "set (\<Phi> @ \<Phi>\<^sub>r) = set \<Phi>'" using incl by auto
    have "set (\<Phi> @ \<Phi>\<^sub>r) = set \<Phi>'" using incl decompose by blast
    moreover have "(set \<Phi>) \<union> (set \<Phi>\<^sub>r) = set \<Phi>'" using incl decompose by auto
    moreover have "\<lbrakk>\<lbrakk> \<Phi>' \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L = \<lbrakk>\<lbrakk> \<Phi> @ \<Phi>\<^sub>r \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L" using TESL_interp_set_lifting decompose by blast
    moreover have "\<lbrakk>\<lbrakk> \<Phi> @ \<Phi>\<^sub>r \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L = \<lbrakk>\<lbrakk> \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L \<inter> \<lbrakk>\<lbrakk> \<Phi>\<^sub>r \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L" by (simp add: TESL_interp_homo_append)
    moreover have "\<lbrakk>\<lbrakk> \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L \<supseteq> \<lbrakk>\<lbrakk> \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L \<inter> \<lbrakk>\<lbrakk> \<Phi>\<^sub>r \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L" by simp
    ultimately show ?thesis by simp
  qed

lemma TESL_interp_decreases_add_head:
  assumes incl: "set \<Phi> \<subseteq> set \<Phi>'"
  shows "\<lbrakk>\<lbrakk> \<phi> # \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L \<supseteq> \<lbrakk>\<lbrakk> \<phi> # \<Phi>' \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L"
  using TESL_interp_decreases_setinc incl by auto

lemma TESL_interp_decreases_add_tail:
  assumes incl: "set \<Phi> \<subseteq> set \<Phi>'"
  shows "\<lbrakk>\<lbrakk> \<Phi> @ [\<phi>] \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L \<supseteq> \<lbrakk>\<lbrakk> \<Phi>' @ [\<phi>] \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L"
  by (metis TESL_interp_commute TESL_interp_decreases_add_head append_Cons append_Nil incl)

lemma TESL_interp_absorb1:
  assumes incl: "set \<Phi>\<^sub>1 \<subseteq> set \<Phi>\<^sub>2"
  shows "\<lbrakk>\<lbrakk> \<Phi>\<^sub>1 @ \<Phi>\<^sub>2 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L = \<lbrakk>\<lbrakk> \<Phi>\<^sub>2 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L"
  by (simp add: Int_absorb1 TESL_interp_decreases_setinc TESL_interp_homo_append incl)

lemma TESL_interp_absorb2:
  assumes incl: "set \<Phi>\<^sub>2 \<subseteq> set \<Phi>\<^sub>1"
  shows "\<lbrakk>\<lbrakk> \<Phi>\<^sub>1 @ \<Phi>\<^sub>2 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L = \<lbrakk>\<lbrakk> \<Phi>\<^sub>1 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L"
  using TESL_interp_absorb1 TESL_interp_commute incl by blast

subsection \<open>Some special cases\<close>

lemma NoSporadic_stable [simp]:
  shows "\<lbrakk>\<lbrakk> \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L \<subseteq> \<lbrakk>\<lbrakk> NoSporadic \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L"
  by (meson filter_is_subset TESL_interp_decreases_setinc)

lemma NoSporadic_idem [simp]:
  shows "\<lbrakk>\<lbrakk> \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L \<inter> \<lbrakk>\<lbrakk> NoSporadic \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L = \<lbrakk>\<lbrakk> \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L"
  by (meson Int_absorb2 filter_is_subset TESL_interp_decreases_setinc)

lemma NoSporadic_setinc:
  shows "set (NoSporadic \<Phi>) \<subseteq> set \<Phi>"
  by auto

(*
lemma Tagrel_affine_sugar:
  shows "\<lbrakk> tag-relation K\<^sub>1 = \<alpha> * K\<^sub>2 + \<beta> \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L = \<lbrakk> tag-relation \<langle>K\<^sub>1, K\<^sub>2\<rangle> \<in> (\<lambda>(\<tau>\<^sub>1, \<tau>\<^sub>2). \<tau>\<^sub>1 = \<alpha> * \<tau>\<^sub>2 + \<beta>) \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L"
  proof -
    have "\<lbrakk> tag-relation \<langle>K\<^sub>1, K\<^sub>2\<rangle> \<in> (\<lambda>(\<tau>\<^sub>1, \<tau>\<^sub>2). \<tau>\<^sub>1 = \<alpha> * \<tau>\<^sub>2 + \<beta>) \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L
       = { \<rho>. \<forall>n::nat. (\<lambda>(\<tau>\<^sub>1, \<tau>\<^sub>2). \<tau>\<^sub>1 = \<alpha> * \<tau>\<^sub>2 + \<beta>) (time ((Rep_run \<rho>) n K\<^sub>1), time ((Rep_run \<rho>) n K\<^sub>2)) }"
      by auto
    then show ?thesis by auto
  qed
*)

end
