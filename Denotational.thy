theory Denotational
imports
    "TESL"
    "Run"

begin

(**) section \<open>Denotational interpretation for atomic TESL formulae\<close> (**)

(* Denotational interpretation of TESL *)
fun TESL_interpretation_atomic
    :: "TESL_atomic \<Rightarrow> run set" ("\<lbrakk> _ \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L") where
    "\<lbrakk> K sporadic \<tau> \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L =
        { \<rho>. \<exists>n::nat. hamlet ((Rep_run \<rho>) n K) = True \<and> time ((Rep_run \<rho>) n K) = \<tau> }"
  | "\<lbrakk> K\<^sub>1 sporadic \<lfloor>\<tau>\<rfloor> on K\<^sub>2 \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L =
        { \<rho>. \<exists>n::nat. hamlet ((Rep_run \<rho>) n K\<^sub>1) = True \<and> time ((Rep_run \<rho>) n K\<^sub>2) = \<tau> }"
  | "\<lbrakk> K\<^sub>1 sporadic \<lfloor>\<tau>\<^sub>v\<^sub>a\<^sub>r(K\<^sub>i, n\<^sub>i) \<oplus> \<delta>\<tau>\<rfloor> on K\<^sub>2 \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L =
        { \<rho>. \<exists>n::nat. hamlet ((Rep_run \<rho>) n K\<^sub>1) = True
                       \<and> time ((Rep_run \<rho>) n K\<^sub>2) = time ((Rep_run \<rho>) n\<^sub>i K\<^sub>i) + \<delta>\<tau> }"
  | "\<lbrakk> tag-relation K\<^sub>1 = \<alpha> * K\<^sub>2 + \<beta> \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L =
        { \<rho>. \<forall>n::nat. time ((Rep_run \<rho>) n K\<^sub>1) = \<alpha> * time ((Rep_run \<rho>) n K\<^sub>2) + \<beta> }"
  | "\<lbrakk> master implies slave \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L =
        { \<rho>. \<forall>n::nat. hamlet ((Rep_run \<rho>) n master) \<longrightarrow> hamlet ((Rep_run \<rho>) n slave) }"
  | "\<lbrakk> master time-delayed by \<delta>\<tau> on measuring implies slave \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L =
        { \<rho>. \<forall>n. hamlet ((Rep_run \<rho>) n master) \<longrightarrow>
                 (let measured_time = time ((Rep_run \<rho>) n measuring) in
                  \<exists>m \<ge> n. hamlet ((Rep_run \<rho>) m slave)
                          \<and> time ((Rep_run \<rho>) m measuring) = measured_time + \<delta>\<tau>
                 )
        }"

(**) section \<open>Denotational interpretation for TESL formulae\<close> (**)

fun TESL_interpretation :: "TESL_formula \<Rightarrow> run set" ("\<lbrakk>\<lbrakk> _ \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L") where
    "\<lbrakk>\<lbrakk> [] \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L = { _. True }"
  | "\<lbrakk>\<lbrakk> \<phi> # \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L = \<lbrakk> \<phi> \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L \<inter> \<lbrakk>\<lbrakk> \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L"

lemma TESL_interpretation_cons_morph:
  "\<lbrakk> \<phi> \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L \<inter> \<lbrakk>\<lbrakk> \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L = \<lbrakk>\<lbrakk> \<phi> # \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L"
  by auto

(***) subsection \<open>Fixpoint lemma\<close> (***)

theorem TESL_interp_fixpoint:
  "\<lbrakk>\<lbrakk> \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L = \<Inter> ((\<lambda>\<phi>. \<lbrakk> \<phi> \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L) ` set \<Phi>)"
  proof (induct \<Phi>)
    case Nil
    then show ?case by simp
  next
    case (Cons a \<Phi>)
    then show ?case by auto
  qed


(***) subsection \<open>Expansion law\<close> (***)
text \<open>Similar to the expansion laws of lattices\<close>

theorem TESL_interp_expansion:
  shows "\<lbrakk>\<lbrakk> \<Phi>\<^sub>1 @ \<Phi>\<^sub>2 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L = \<lbrakk>\<lbrakk> \<Phi>\<^sub>1 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L \<inter> \<lbrakk>\<lbrakk> \<Phi>\<^sub>2 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L"
  proof (induct \<Phi>\<^sub>1)
    case Nil
    then show ?case by simp
  next
    case (Cons a \<Phi>\<^sub>1)
    then show ?case by auto
  qed


(***) subsection \<open>Equational laws for TESL formulae denotationally interpreted\<close> (***)

lemma TESL_interp_assoc:
  shows "\<lbrakk>\<lbrakk> (\<Phi>\<^sub>1 @ \<Phi>\<^sub>2) @ \<Phi>\<^sub>3 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L = \<lbrakk>\<lbrakk> \<Phi>\<^sub>1 @ (\<Phi>\<^sub>2 @ \<Phi>\<^sub>3) \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L"
  by auto

lemma TESL_interp_commute:
  shows "\<lbrakk>\<lbrakk> \<Phi>\<^sub>1 @ \<Phi>\<^sub>2 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L = \<lbrakk>\<lbrakk> \<Phi>\<^sub>2 @ \<Phi>\<^sub>1 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L"
  by (simp add: TESL_interp_expansion inf_sup_aci(1))

lemma TESL_interp_left_commute:
  shows "\<lbrakk>\<lbrakk> \<Phi>\<^sub>1 @ (\<Phi>\<^sub>2 @ \<Phi>\<^sub>3) \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L = \<lbrakk>\<lbrakk> \<Phi>\<^sub>2 @ (\<Phi>\<^sub>1 @ \<Phi>\<^sub>3) \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L"
  using TESL_interp_expansion by auto

lemma TESL_interp_idem:
  shows "\<lbrakk>\<lbrakk> \<Phi> @ \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L = \<lbrakk>\<lbrakk> \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L"
  using TESL_interp_expansion by auto

lemma TESL_interp_left_idem:
  shows "\<lbrakk>\<lbrakk> \<Phi>\<^sub>1 @ (\<Phi>\<^sub>1 @ \<Phi>\<^sub>2) \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L = \<lbrakk>\<lbrakk> \<Phi>\<^sub>1 @ \<Phi>\<^sub>2 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L"
  using TESL_interp_expansion by auto

lemma TESL_interp_right_idem:
  shows "\<lbrakk>\<lbrakk> (\<Phi>\<^sub>1 @ \<Phi>\<^sub>2) @ \<Phi>\<^sub>2 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L = \<lbrakk>\<lbrakk> \<Phi>\<^sub>1 @ \<Phi>\<^sub>2 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L"
  using TESL_interp_expansion by auto

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
  by (simp add: TESL_interp_expansion)

lemma TESL_interp_formula_stuttering:
  assumes bel: "\<phi> \<in> set \<Phi>"
  shows "\<lbrakk>\<lbrakk> \<phi> # \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L = \<lbrakk>\<lbrakk> \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L"
  by (metis Int_subset_iff TESL_interp_expansion TESL_interpretation.simps(2) bel in_set_conv_decomp_first subset_antisym subset_refl)

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
      by (simp add: TESL_interp_fixpoint)
    moreover have fxpnt\<Phi>': "\<Inter> ((\<lambda>\<phi>. \<lbrakk> \<phi> \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L) ` set \<Phi>') = \<lbrakk>\<lbrakk> \<Phi>' \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L"
      by (simp add: TESL_interp_fixpoint)
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
    moreover have "\<lbrakk>\<lbrakk> \<Phi> @ \<Phi>\<^sub>r \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L = \<lbrakk>\<lbrakk> \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L \<inter> \<lbrakk>\<lbrakk> \<Phi>\<^sub>r \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L" by (simp add: TESL_interp_expansion)
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
  by (simp add: Int_absorb1 TESL_interp_decreases_setinc TESL_interp_expansion incl)

lemma TESL_interp_absorb2:
  assumes incl: "set \<Phi>\<^sub>2 \<subseteq> set \<Phi>\<^sub>1"
  shows "\<lbrakk>\<lbrakk> \<Phi>\<^sub>1 @ \<Phi>\<^sub>2 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L = \<lbrakk>\<lbrakk> \<Phi>\<^sub>1 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L"
  using TESL_interp_absorb1 TESL_interp_commute incl by blast


(***) subsection \<open>Some special cases\<close> (***)

lemma NoSporadic_stable [simp]:
  shows "\<lbrakk>\<lbrakk> \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L \<subseteq> \<lbrakk>\<lbrakk> NoSporadic \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L"
  by (meson filter_is_subset TESL_interp_decreases_setinc)

lemma NoSporadic_idem [simp]:
  shows "\<lbrakk>\<lbrakk> \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L \<inter> \<lbrakk>\<lbrakk> NoSporadic \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L = \<lbrakk>\<lbrakk> \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L"
  by (meson Int_absorb2 filter_is_subset TESL_interp_decreases_setinc)

lemma NoSporadic_setinc:
  shows "set (NoSporadic \<Phi>) \<subseteq> set \<Phi>"
  by auto

lemma SporadicOn_sugar_atom:
  shows "\<lbrakk> K sporadic \<lfloor>\<tau>\<rfloor> on K \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L = \<lbrakk> K sporadic \<tau> \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L"
  by auto

lemma SporadicOn_sugar:
  shows "\<lbrakk>\<lbrakk> (K sporadic \<lfloor>\<tau>\<rfloor> on K) # \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L = \<lbrakk>\<lbrakk> (K sporadic \<tau>) # \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L"
  by auto

(**) section \<open>Denotational interpretation for atoms bounded by index\<close> (**)

(* Denotational interpretation of TESL bounded by index *)
fun TESL_interpretation_primitive_at_index
    :: "TESL_atomic \<Rightarrow> nat \<Rightarrow> run set" ("\<lbrakk> _ \<nabla> _ \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L") where
    "\<lbrakk> K sporadic \<tau> \<nabla> n \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L =
        { \<rho>. \<exists>m\<ge>n. hamlet ((Rep_run \<rho>) m K) = True \<and> time ((Rep_run \<rho>) m K) = \<tau> }"
  | "\<lbrakk> K\<^sub>1 sporadic \<lfloor>\<tau>\<rfloor> on K\<^sub>2 \<nabla> n \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L =
        { \<rho>. \<exists>m\<ge>n. hamlet ((Rep_run \<rho>) m K\<^sub>1) = True \<and> time ((Rep_run \<rho>) m K\<^sub>2) = \<tau> }"
  | "\<lbrakk> K\<^sub>1 sporadic \<lfloor>\<tau>\<^sub>v\<^sub>a\<^sub>r(K\<^sub>i, n\<^sub>i) \<oplus> \<delta>\<tau>\<rfloor> on K\<^sub>2 \<nabla> n \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L =
        { \<rho>. \<exists>m\<ge>n. hamlet ((Rep_run \<rho>) m K\<^sub>1) = True
                         \<and> time ((Rep_run \<rho>) m K\<^sub>2) = time ((Rep_run \<rho>) n\<^sub>i K\<^sub>i) + \<delta>\<tau> }"
  | "\<lbrakk> tag-relation K\<^sub>1 = \<alpha> * K\<^sub>2 + \<beta> \<nabla> n \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L =
        { \<rho>. \<forall>m\<ge>n. time ((Rep_run \<rho>) m K\<^sub>1) = \<alpha> * time ((Rep_run \<rho>) m K\<^sub>2) + \<beta> }"
  | "\<lbrakk> master implies slave \<nabla> n \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L =
        { \<rho>. \<forall>m\<ge>n. hamlet ((Rep_run \<rho>) m master) \<longrightarrow> hamlet ((Rep_run \<rho>) m slave) }"
  | "\<lbrakk> master time-delayed by \<delta>\<tau> on measuring implies slave \<nabla> n \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L =
        { \<rho>. \<forall>m\<ge>n. hamlet ((Rep_run \<rho>) m master) \<longrightarrow>
                 (let measured_time = time ((Rep_run \<rho>) m measuring) in
                  \<exists>p \<ge> m. hamlet ((Rep_run \<rho>) p slave)
                          \<and> time ((Rep_run \<rho>) p measuring) = measured_time + \<delta>\<tau>
                 )
        }"

theorem predicate_Inter_unfold:
  "{ \<rho>. \<forall>n. P \<rho> n} = \<Inter> {Y. \<exists>n. Y = { \<rho>. P \<rho> n }}"
  by (simp add: Collect_all_eq full_SetCompr_eq)

theorem predicate_Union_unfold:
  "{ \<rho>. \<exists>n. P \<rho> n} = \<Union> {Y. \<exists>n. Y = { \<rho>. P \<rho> n }}"
  by auto

lemma TESL_interp_unfold_at_index_sporadic:
  shows "\<lbrakk> K sporadic \<tau> \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L = \<Union> {Y. \<exists>n::nat. Y = \<lbrakk> K sporadic \<tau> \<nabla> n \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L}"
  by auto

lemma TESL_interp_unfold_at_index_sporadicon:
  shows "\<lbrakk> K\<^sub>1 sporadic \<lfloor>\<tau>\<rfloor> on K\<^sub>2 \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L = \<Union> {Y. \<exists>n::nat. Y = \<lbrakk> K\<^sub>1 sporadic \<lfloor>\<tau>\<rfloor> on K\<^sub>2 \<nabla> n \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L}"
  by auto

lemma TESL_interp_unfold_at_index_sporadicon_add:
  shows "\<lbrakk> K\<^sub>1 sporadic \<lfloor>\<tau>\<^sub>v\<^sub>a\<^sub>r(K, n') \<oplus> \<tau>\<rfloor> on K\<^sub>2 \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L = \<Union> {Y. \<exists>n::nat. Y = \<lbrakk> K\<^sub>1 sporadic \<lfloor>\<tau>\<^sub>v\<^sub>a\<^sub>r(K, n') \<oplus> \<tau>\<rfloor> on K\<^sub>2 \<nabla> n \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L}"
  by auto

lemma TESL_interp_unfold_at_index_tagrel:
  shows "\<lbrakk> tag-relation K\<^sub>1 = \<alpha> * K\<^sub>2 + \<beta> \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L = \<Inter> {Y. \<exists>n::nat. Y = \<lbrakk> tag-relation K\<^sub>1 = \<alpha> * K\<^sub>2 + \<beta> \<nabla> n \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L}"
  by auto

lemma TESL_interp_unfold_at_index_implies:
  shows "\<lbrakk> master implies slave \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L = \<Inter> {Y. \<exists>n::nat. Y = \<lbrakk> master implies slave \<nabla> n \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L}"
  by auto

lemma TESL_interp_unfold_at_index_timedelayed:
  shows "\<lbrakk> master time-delayed by \<delta>\<tau> on measuring implies slave \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L
    = \<Inter> {Y. \<exists>n::nat. Y = \<lbrakk> master time-delayed by \<delta>\<tau> on measuring implies slave \<nabla> n \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L}"
  by auto

theorem TESL_interp_unfold_at_index_positive_atoms:
  assumes "positive_atom \<phi>"
  shows "\<lbrakk> \<phi> \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L = \<Union> {Y. \<exists>n::nat. Y = \<lbrakk> \<phi> \<nabla> n \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L}"
  proof -
    obtain cc :: "TESL_atomic \<Rightarrow> clock" and tt :: "TESL_atomic \<Rightarrow> tag_const" and cca :: "TESL_atomic \<Rightarrow> clock" and tta :: "TESL_atomic \<Rightarrow> tag_expr" and ccb :: "TESL_atomic \<Rightarrow> clock" where
      f1: "\<forall>t. \<not> positive_atom t \<or> t = cc t sporadic tt t \<or> t = cca t sporadic tta t on ccb t"
      using positive_atom.elims(2) by moura
    obtain ttb :: "tag_expr \<Rightarrow> tag_const" where
      "\<And>c t ca. \<Union>{R. \<exists>n. R = \<lbrakk> c sporadic t on ca \<nabla> n \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L} = \<lbrakk> c sporadic t on ca \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L \<or> \<lfloor> ttb t \<rfloor> = t"
      by (metis TESL_interp_unfold_at_index_sporadicon_add old.prod.exhaust tag_expr.exhaust tag_var.exhaust)
    then have "\<And>t. \<Union>{R. \<exists>n. R = \<lbrakk> t \<nabla> n \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L} = \<lbrakk> t \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L \<or> \<lfloor> ttb (tta t) \<rfloor> = tta t \<or> \<not> positive_atom t"
      using f1 by (metis TESL_interp_unfold_at_index_sporadic)
    then show ?thesis
      using f1 by (metis TESL_interp_unfold_at_index_sporadic TESL_interp_unfold_at_index_sporadicon assms)
  qed

theorem TESL_interp_unfold_at_index_negative_atoms:
  assumes "\<not> positive_atom \<phi>"
  shows "\<lbrakk> \<phi> \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L = \<Inter> {Y. \<exists>n::nat. Y = \<lbrakk> \<phi> \<nabla> n \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L}"
  by (smt Collect_cong TESL_interp_unfold_at_index_implies TESL_interp_unfold_at_index_tagrel TESL_interp_unfold_at_index_timedelayed assms positive_atom.elims(3))

lemma forall_nat_expansion:
  "(\<forall>n\<^sub>1 \<ge> (n\<^sub>0::nat). P n\<^sub>1) \<equiv> P n\<^sub>0 \<and> (\<forall>n\<^sub>1 \<ge> Suc n\<^sub>0. P n\<^sub>1)"
  by (smt Suc_leD dual_order.antisym not_less_eq_eq)

lemma exists_nat_expansion:
  "(\<exists>n\<^sub>1 \<ge> (n\<^sub>0::nat). P n\<^sub>1) \<equiv> P n\<^sub>0 \<or> (\<exists>n\<^sub>1 \<ge> Suc n\<^sub>0. P n\<^sub>1)"
  by (smt Suc_leD dual_order.antisym not_less_eq_eq)

lemma TESL_interp_at_index_sporadic_cases:
  shows "\<lbrakk> K sporadic \<tau> \<nabla> n \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L =
    \<lbrakk> K \<Up> n \<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n \<inter> \<lbrakk> K \<Down> n @ \<lfloor> \<tau> \<rfloor> \<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n
    \<union> \<lbrakk> K sporadic \<tau> \<nabla> Suc n \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L"
  proof -
    have "{ \<rho>. \<exists>m\<ge>n. hamlet ((Rep_run \<rho>) m K) = True \<and> time ((Rep_run \<rho>) m K) = \<tau> }
        = { \<rho>. hamlet ((Rep_run \<rho>) n K) = True \<and> time ((Rep_run \<rho>) n K) = \<tau>
               \<or> (\<exists>m\<ge>Suc n. hamlet ((Rep_run \<rho>) m K) = True \<and> time ((Rep_run \<rho>) m K) = \<tau>) }"
      using Suc_leD not_less_eq_eq by fastforce
    moreover have "{ \<rho>. hamlet ((Rep_run \<rho>) n K) = True \<and> time ((Rep_run \<rho>) n K) = \<tau>
                        \<or> (\<exists>m\<ge>Suc n. hamlet ((Rep_run \<rho>) m K) = True \<and> time ((Rep_run \<rho>) m K) = \<tau>) }
                 = \<lbrakk> K \<Up> n \<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n \<inter> \<lbrakk> K \<Down> n @ \<lfloor> \<tau> \<rfloor> \<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n \<union> \<lbrakk> K sporadic \<tau> \<nabla> Suc n \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L"
      by (simp add: Collect_conj_eq Collect_disj_eq)
    ultimately show ?thesis by auto
  qed

lemma TESL_interp_at_index_sporadicon_cst_cases:
  shows "\<lbrakk> K\<^sub>1 sporadic \<lfloor>\<tau>\<rfloor> on K\<^sub>2 \<nabla> n \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L =
    \<lbrakk> K\<^sub>1 \<Up> n \<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n \<inter> \<lbrakk> K\<^sub>2 \<Down> n @ \<lfloor> \<tau> \<rfloor> \<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n
    \<union> \<lbrakk> K\<^sub>1 sporadic \<lfloor>\<tau>\<rfloor> on K\<^sub>2 \<nabla> Suc n \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L"
  proof -
    have "{ \<rho>. \<exists>m\<ge>n. hamlet ((Rep_run \<rho>) m K\<^sub>1) = True \<and> time ((Rep_run \<rho>) m K\<^sub>2) = \<tau> }
        = { \<rho>. hamlet ((Rep_run \<rho>) n K\<^sub>1) = True \<and> time ((Rep_run \<rho>) n K\<^sub>2) = \<tau>
               \<or> (\<exists>m\<ge>Suc n. hamlet ((Rep_run \<rho>) m K\<^sub>1) = True \<and> time ((Rep_run \<rho>) m K\<^sub>2) = \<tau>) }"
      using Suc_leD not_less_eq_eq by fastforce
    moreover have "{ \<rho>. hamlet ((Rep_run \<rho>) n K\<^sub>1) = True \<and> time ((Rep_run \<rho>) n K\<^sub>2) = \<tau>
                        \<or> (\<exists>m\<ge>Suc n. hamlet ((Rep_run \<rho>) m K\<^sub>1) = True \<and> time ((Rep_run \<rho>) m K\<^sub>2) = \<tau>) }
                 = \<lbrakk> K\<^sub>1 \<Up> n \<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n \<inter> \<lbrakk> K\<^sub>2 \<Down> n @ \<lfloor>\<tau>\<rfloor> \<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n \<union> \<lbrakk> K\<^sub>1 sporadic \<lfloor>\<tau>\<rfloor> on K\<^sub>2 \<nabla> Suc n \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L"
      by (simp add: Collect_conj_eq Collect_disj_eq)
    ultimately show ?thesis by auto
  qed

lemma TESL_interp_at_index_sporadicon_add_cases:
  shows "\<lbrakk> K\<^sub>1 sporadic \<lfloor>\<tau>\<^sub>v\<^sub>a\<^sub>r(K, n') \<oplus> \<tau>\<rfloor> on K\<^sub>2 \<nabla> n \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L =
    \<lbrakk> K\<^sub>1 \<Up> n \<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n \<inter> \<lbrakk> K\<^sub>2 \<Down> n @ \<lfloor>\<tau>\<^sub>v\<^sub>a\<^sub>r(K, n') \<oplus> \<tau>\<rfloor> \<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n
    \<union> \<lbrakk> K\<^sub>1 sporadic \<lfloor>\<tau>\<^sub>v\<^sub>a\<^sub>r(K, n') \<oplus> \<tau>\<rfloor> on K\<^sub>2 \<nabla> Suc n \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L"
  proof -
    have "{ \<rho>. \<exists>m\<ge>n. hamlet ((Rep_run \<rho>) m K\<^sub>1) = True \<and> time ((Rep_run \<rho>) m K\<^sub>2) = time ((Rep_run \<rho>) n' K) + \<tau> }
        = { \<rho>. hamlet ((Rep_run \<rho>) n K\<^sub>1) = True \<and> time ((Rep_run \<rho>) n K\<^sub>2) = time ((Rep_run \<rho>) n' K) + \<tau>
               \<or> (\<exists>m\<ge>Suc n. hamlet ((Rep_run \<rho>) m K\<^sub>1) = True \<and> time ((Rep_run \<rho>) m K\<^sub>2) = time ((Rep_run \<rho>) n' K) + \<tau>) }"
      using Suc_leD not_less_eq_eq by fastforce
    then show ?thesis by auto
  qed

lemma TESL_interp_at_index_sporadicon_cases:
  shows "\<lbrakk> K\<^sub>1 sporadic \<tau> on K\<^sub>2 \<nabla> n \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L =
    \<lbrakk> K\<^sub>1 \<Up> n \<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n \<inter> \<lbrakk> K\<^sub>2 \<Down> n @ \<tau> \<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n
    \<union> \<lbrakk> K\<^sub>1 sporadic \<tau> on K\<^sub>2 \<nabla> Suc n \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L"
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
  shows "\<lbrakk> tag-relation K\<^sub>1 = \<alpha> * K\<^sub>2 + \<beta> \<nabla> n \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L =
    \<lbrakk> \<tau>\<^sub>v\<^sub>a\<^sub>r(K\<^sub>1, n) \<doteq> \<alpha> * \<tau>\<^sub>v\<^sub>a\<^sub>r(K\<^sub>2, n) + \<beta> \<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n
    \<inter> \<lbrakk> tag-relation K\<^sub>1 = \<alpha> * K\<^sub>2 + \<beta> \<nabla> Suc n \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L"
  proof -
    have "{ \<rho>. \<forall>m\<ge>n. time ((Rep_run \<rho>) m K\<^sub>1) = \<alpha> * time ((Rep_run \<rho>) m K\<^sub>2) + \<beta> }
         = { \<rho>. time ((Rep_run \<rho>) n K\<^sub>1) = \<alpha> * time ((Rep_run \<rho>) n K\<^sub>2) + \<beta> }
         \<inter> { \<rho>. \<forall>m\<ge>Suc n. time ((Rep_run \<rho>) m K\<^sub>1) = \<alpha> * time ((Rep_run \<rho>) m K\<^sub>2) + \<beta> }"
      by (smt Collect_cong Collect_conj_eq Suc_leD eq_refl le_antisym not_less_eq_eq)
  then show ?thesis by auto
  qed

lemma TESL_interp_at_index_implies_cases:
  shows "\<lbrakk> master implies slave \<nabla> n \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L =
    (\<lbrakk> master \<not>\<Up> n \<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n \<union> \<lbrakk> master \<Up> n \<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n \<inter> \<lbrakk> slave \<Up> n \<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n)
    \<inter> \<lbrakk> master implies slave \<nabla> Suc n \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L"
  proof -
    have "{ \<rho>. \<forall>m\<ge>n. hamlet ((Rep_run \<rho>) m master) \<longrightarrow> hamlet ((Rep_run \<rho>) m slave) }
          = { \<rho>. hamlet ((Rep_run \<rho>) n master) \<longrightarrow> hamlet ((Rep_run \<rho>) n slave) }
          \<inter> { \<rho>. \<forall>m\<ge>Suc n. hamlet ((Rep_run \<rho>) m master) \<longrightarrow> hamlet ((Rep_run \<rho>) m slave) }"
      by (smt Collect_cong Collect_conj_eq Suc_leD eq_refl le_antisym not_less_eq_eq)
    then show ?thesis by auto
  qed

lemma TESL_interp_at_index_timedelayed_cases:
  shows "\<lbrakk> master time-delayed by \<delta>\<tau> on measuring implies slave \<nabla> n \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L =
    (\<lbrakk> master \<not>\<Up> n \<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n \<union> \<lbrakk> master \<Up> n \<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n \<inter> \<lbrakk> slave sporadic \<lfloor>\<tau>\<^sub>v\<^sub>a\<^sub>r(measuring, n) \<oplus> \<delta>\<tau>\<rfloor> on measuring \<nabla> n \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L)
    \<inter> \<lbrakk> master time-delayed by \<delta>\<tau> on measuring implies slave \<nabla> Suc n \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L"
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

fun TESL_interpretation_at_index :: "TESL_formula \<Rightarrow> nat \<Rightarrow> run set" ("\<lbrakk>\<lbrakk> _ \<nabla> _ \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L") where
    "\<lbrakk>\<lbrakk> [] \<nabla> n \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L = { _. True }"
  | "\<lbrakk>\<lbrakk> \<phi> # \<Phi> \<nabla> n \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L = \<lbrakk> \<phi> \<nabla> n \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L \<inter> \<lbrakk>\<lbrakk> \<Phi> \<nabla> n \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L"

lemma TESL_interpretation_at_index_fixpoint:
  "\<lbrakk>\<lbrakk> \<Phi> \<nabla> n \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L = \<Inter> ((\<lambda>\<phi>. \<lbrakk> \<phi> \<nabla> n \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L) ` set \<Phi>)"
  proof (induct \<Phi>)
    case Nil
    then show ?case by simp
  next
    case (Cons a \<Phi>)
    then show ?case by auto
  qed

lemma TESL_interpretation_at_index_zero:
  "\<lbrakk> \<phi> \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L = \<lbrakk> \<phi> \<nabla> 0 \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L"
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
  "\<lbrakk>\<lbrakk> \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L = \<lbrakk>\<lbrakk> \<Phi> \<nabla> 0 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L"
  proof (induct \<Phi>)
    case Nil
    then show ?case by simp
  next
    case (Cons a \<Phi>)
    then show ?case
      by (simp add: TESL_interpretation_at_index_zero)
  qed

lemma TESL_interpretation_at_index_cons_morph:
  "\<lbrakk> \<phi> \<nabla> n \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L \<inter> \<lbrakk>\<lbrakk> \<Phi> \<nabla> n \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L = \<lbrakk>\<lbrakk> \<phi> # \<Phi> \<nabla> n \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L"
  by auto

end
