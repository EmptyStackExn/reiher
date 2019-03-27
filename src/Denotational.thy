chapter \<open>Denotational Semantics\<close>

theory Denotational
imports
    TESL
    Run

begin

section \<open>Denotational interpretation for atomic TESL formulae\<close>
(*<*)
consts dummyT0 ::\<open>'\<tau> tag_const\<close>
consts dummyDeltaT ::\<open>'\<tau> tag_const\<close>

notation dummyT0    ("t\<^sub>0")
notation dummyDeltaT ("\<delta>t")
(*>*)

fun TESL_interpretation_atomic
    :: \<open>('\<tau>::linordered_field) TESL_atomic \<Rightarrow> '\<tau> run set\<close> ("\<lbrakk> _ \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L") where
    \<open>\<lbrakk> K\<^sub>1 sporadic \<tau> on K\<^sub>2 \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L =
        { \<rho>. \<exists>n::nat. hamlet ((Rep_run \<rho>) n K\<^sub>1) \<and> time ((Rep_run \<rho>) n K\<^sub>2) = \<tau> }\<close>
  | \<open>\<lbrakk> time-relation \<lfloor>K\<^sub>1, K\<^sub>2\<rfloor> \<in> R \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L =
        { \<rho>. \<forall>n::nat. R (time ((Rep_run \<rho>) n K\<^sub>1), time ((Rep_run \<rho>) n K\<^sub>2)) }\<close>
  | \<open>\<lbrakk> master implies slave \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L =
        { \<rho>. \<forall>n::nat. hamlet ((Rep_run \<rho>) n master) \<longrightarrow> hamlet ((Rep_run \<rho>) n slave) }\<close>
  | \<open>\<lbrakk> master implies not slave \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L =
        { \<rho>. \<forall>n::nat. hamlet ((Rep_run \<rho>) n master) \<longrightarrow> \<not> hamlet ((Rep_run \<rho>) n slave) }\<close>
  | \<open>\<lbrakk> master time-delayed by \<delta>\<tau> on measuring implies slave \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L =
    \<comment> \<open>
      When master ticks, let's call @term\<open>t\<^sub>0\<close> the current date on measuring. Then, at the first
      instant when the date on measuring is @term\<open>t\<^sub>0+\<delta>t\<close>, slave has to tick.
    \<close>
        { \<rho>. \<forall>n. hamlet ((Rep_run \<rho>) n master) \<longrightarrow>
                 (let measured_time = time ((Rep_run \<rho>) n measuring) in
                  \<forall>m \<ge> n.  first_time \<rho> measuring m (measured_time + \<delta>\<tau>)
                            \<longrightarrow> hamlet ((Rep_run \<rho>) m slave)
                 )
        }\<close>
  | \<open>\<lbrakk> K\<^sub>1 weakly precedes K\<^sub>2 \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L =
        { \<rho>. \<forall>n::nat. (run_tick_count \<rho> K\<^sub>2 n) \<le> (run_tick_count \<rho> K\<^sub>1 n) }\<close>
  | \<open>\<lbrakk> K\<^sub>1 strictly precedes K\<^sub>2 \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L =
        { \<rho>. \<forall>n::nat. (run_tick_count \<rho> K\<^sub>2 n) \<le> (run_tick_count_strictly \<rho> K\<^sub>1 n) }\<close>
  | \<open>\<lbrakk> K\<^sub>1 kills K\<^sub>2 \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L =
        { \<rho>. \<forall>n::nat. hamlet ((Rep_run \<rho>) n K\<^sub>1) \<longrightarrow> (\<forall>m\<ge>n. \<not> hamlet ((Rep_run \<rho>) m K\<^sub>2)) }\<close>

section \<open>Denotational interpretation for TESL formulae\<close>

fun TESL_interpretation :: \<open>('\<tau>::linordered_field) TESL_formula \<Rightarrow> '\<tau> run set\<close> ("\<lbrakk>\<lbrakk> _ \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L") where
    \<open>\<lbrakk>\<lbrakk> [] \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L = { _. True }\<close>
  | \<open>\<lbrakk>\<lbrakk> \<phi> # \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L = \<lbrakk> \<phi> \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L \<inter> \<lbrakk>\<lbrakk> \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<close>

lemma TESL_interpretation_homo:
  \<open>\<lbrakk> \<phi> \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L \<inter> \<lbrakk>\<lbrakk> \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L = \<lbrakk>\<lbrakk> \<phi> # \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<close>
  by auto

subsection \<open>Image interpretation lemma\<close>

theorem TESL_interpretation_image:
  \<open>\<lbrakk>\<lbrakk> \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L = \<Inter> ((\<lambda>\<phi>. \<lbrakk> \<phi> \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L) ` set \<Phi>)\<close>
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
  shows \<open>\<lbrakk>\<lbrakk> \<Phi>\<^sub>1 @ \<Phi>\<^sub>2 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L = \<lbrakk>\<lbrakk> \<Phi>\<^sub>1 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L \<inter> \<lbrakk>\<lbrakk> \<Phi>\<^sub>2 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<close>
  proof (induct \<Phi>\<^sub>1)
    case Nil
    then show ?case by simp
  next
    case (Cons a \<Phi>\<^sub>1)
    then show ?case by auto
  qed


section \<open>Equational laws for TESL formulae denotationally interpreted\<close>

lemma TESL_interp_assoc:
  shows \<open>\<lbrakk>\<lbrakk> (\<Phi>\<^sub>1 @ \<Phi>\<^sub>2) @ \<Phi>\<^sub>3 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L = \<lbrakk>\<lbrakk> \<Phi>\<^sub>1 @ (\<Phi>\<^sub>2 @ \<Phi>\<^sub>3) \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<close>
  by auto

lemma TESL_interp_commute:
  shows \<open>\<lbrakk>\<lbrakk> \<Phi>\<^sub>1 @ \<Phi>\<^sub>2 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L = \<lbrakk>\<lbrakk> \<Phi>\<^sub>2 @ \<Phi>\<^sub>1 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<close>
  by (simp add: TESL_interp_homo_append inf_sup_aci(1))

lemma TESL_interp_left_commute:
  shows \<open>\<lbrakk>\<lbrakk> \<Phi>\<^sub>1 @ (\<Phi>\<^sub>2 @ \<Phi>\<^sub>3) \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L = \<lbrakk>\<lbrakk> \<Phi>\<^sub>2 @ (\<Phi>\<^sub>1 @ \<Phi>\<^sub>3) \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<close>
  unfolding TESL_interp_homo_append by auto

lemma TESL_interp_idem:
  shows \<open>\<lbrakk>\<lbrakk> \<Phi> @ \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L = \<lbrakk>\<lbrakk> \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<close>
  using TESL_interp_homo_append by auto

lemma TESL_interp_left_idem:
  shows \<open>\<lbrakk>\<lbrakk> \<Phi>\<^sub>1 @ (\<Phi>\<^sub>1 @ \<Phi>\<^sub>2) \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L = \<lbrakk>\<lbrakk> \<Phi>\<^sub>1 @ \<Phi>\<^sub>2 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<close>
  using TESL_interp_homo_append by auto

lemma TESL_interp_right_idem:
  shows \<open>\<lbrakk>\<lbrakk> (\<Phi>\<^sub>1 @ \<Phi>\<^sub>2) @ \<Phi>\<^sub>2 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L = \<lbrakk>\<lbrakk> \<Phi>\<^sub>1 @ \<Phi>\<^sub>2 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<close>
  unfolding TESL_interp_homo_append by auto

lemmas TESL_interp_aci = TESL_interp_commute TESL_interp_assoc TESL_interp_left_commute TESL_interp_left_idem

(* Identity element *)
lemma TESL_interp_neutral1:
  shows \<open>\<lbrakk>\<lbrakk> [] @ \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L = \<lbrakk>\<lbrakk> \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<close>
  by simp

lemma TESL_interp_neutral2:
  shows \<open>\<lbrakk>\<lbrakk> \<Phi> @ [] \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L = \<lbrakk>\<lbrakk> \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<close>
  by simp

section \<open>Decreasing interpretation of TESL formulae\<close>

lemma TESL_sem_decreases_head:
  \<open>\<lbrakk>\<lbrakk> \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L \<supseteq> \<lbrakk>\<lbrakk> \<phi> # \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<close>
  by simp

lemma TESL_sem_decreases_tail:
  \<open>\<lbrakk>\<lbrakk> \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L \<supseteq> \<lbrakk>\<lbrakk> \<Phi> @ [\<phi>] \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<close>
  by (simp add: TESL_interp_homo_append)

lemma TESL_interp_formula_stuttering:
  assumes bel: \<open>\<phi> \<in> set \<Phi>\<close>
  shows \<open>\<lbrakk>\<lbrakk> \<phi> # \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L = \<lbrakk>\<lbrakk> \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<close>
  by (metis Int_subset_iff TESL_interp_homo_append TESL_interpretation.simps(2) bel in_set_conv_decomp_first subset_antisym subset_refl)

lemma TESL_interp_decreases:
  shows \<open>\<lbrakk>\<lbrakk> \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L \<supseteq> \<lbrakk>\<lbrakk> \<phi> # \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<close>
  by (rule TESL_sem_decreases_head)

lemma TESL_interp_remdups_absorb:
  shows \<open>\<lbrakk>\<lbrakk> \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L = \<lbrakk>\<lbrakk> remdups \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<close>
  proof (induct \<Phi>)
    case Nil
    then show ?case by simp
  next
    case (Cons a \<Phi>)
    then show ?case
      using TESL_interp_formula_stuttering by auto
  qed

lemma TESL_interp_set_lifting:
  assumes \<open>set \<Phi> = set \<Phi>'\<close>
  shows \<open>\<lbrakk>\<lbrakk> \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L = \<lbrakk>\<lbrakk> \<Phi>' \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<close>
  proof -     
    have \<open>set (remdups \<Phi>) = set (remdups \<Phi>')\<close>
      by (simp add: assms)
    moreover have fxpnt\<Phi>: \<open>\<Inter> ((\<lambda>\<phi>. \<lbrakk> \<phi> \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L) ` set \<Phi>) = \<lbrakk>\<lbrakk> \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<close>
      by (simp add: TESL_interpretation_image)
    moreover have fxpnt\<Phi>': \<open>\<Inter> ((\<lambda>\<phi>. \<lbrakk> \<phi> \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L) ` set \<Phi>') = \<lbrakk>\<lbrakk> \<Phi>' \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<close>
      by (simp add: TESL_interpretation_image)
    moreover have \<open>\<Inter> ((\<lambda>\<phi>. \<lbrakk> \<phi> \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L) ` set \<Phi>) = \<Inter> ((\<lambda>\<phi>. \<lbrakk> \<phi> \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L) ` set \<Phi>')\<close>
      by (simp add: assms)
    ultimately show ?thesis using TESL_interp_remdups_absorb by auto
  qed

theorem TESL_interp_decreases_setinc:
  assumes incl: \<open>set \<Phi> \<subseteq> set \<Phi>'\<close>
  shows \<open>\<lbrakk>\<lbrakk> \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L \<supseteq> \<lbrakk>\<lbrakk> \<Phi>' \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<close>
  proof -
    obtain \<Phi>\<^sub>r where decompose: \<open>set (\<Phi> @ \<Phi>\<^sub>r) = set \<Phi>'\<close> using incl by auto
    have \<open>set (\<Phi> @ \<Phi>\<^sub>r) = set \<Phi>'\<close> using incl decompose by blast
    moreover have \<open>(set \<Phi>) \<union> (set \<Phi>\<^sub>r) = set \<Phi>'\<close> using incl decompose by auto
    moreover have \<open>\<lbrakk>\<lbrakk> \<Phi>' \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L = \<lbrakk>\<lbrakk> \<Phi> @ \<Phi>\<^sub>r \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<close> using TESL_interp_set_lifting decompose by blast
    moreover have \<open>\<lbrakk>\<lbrakk> \<Phi> @ \<Phi>\<^sub>r \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L = \<lbrakk>\<lbrakk> \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L \<inter> \<lbrakk>\<lbrakk> \<Phi>\<^sub>r \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<close> by (simp add: TESL_interp_homo_append)
    moreover have \<open>\<lbrakk>\<lbrakk> \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L \<supseteq> \<lbrakk>\<lbrakk> \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L \<inter> \<lbrakk>\<lbrakk> \<Phi>\<^sub>r \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<close> by simp
    ultimately show ?thesis by simp
  qed

lemma TESL_interp_decreases_add_head:
  assumes incl: \<open>set \<Phi> \<subseteq> set \<Phi>'\<close>
  shows \<open>\<lbrakk>\<lbrakk> \<phi> # \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L \<supseteq> \<lbrakk>\<lbrakk> \<phi> # \<Phi>' \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<close>
  using TESL_interp_decreases_setinc incl by auto

lemma TESL_interp_decreases_add_tail:
  assumes incl: \<open>set \<Phi> \<subseteq> set \<Phi>'\<close>
  shows \<open>\<lbrakk>\<lbrakk> \<Phi> @ [\<phi>] \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L \<supseteq> \<lbrakk>\<lbrakk> \<Phi>' @ [\<phi>] \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<close>
  by (metis TESL_interp_commute TESL_interp_decreases_add_head append_Cons append_Nil incl)

lemma TESL_interp_absorb1:
  assumes incl: \<open>set \<Phi>\<^sub>1 \<subseteq> set \<Phi>\<^sub>2\<close>
  shows \<open>\<lbrakk>\<lbrakk> \<Phi>\<^sub>1 @ \<Phi>\<^sub>2 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L = \<lbrakk>\<lbrakk> \<Phi>\<^sub>2 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<close>
  by (simp add: Int_absorb1 TESL_interp_decreases_setinc TESL_interp_homo_append incl)

lemma TESL_interp_absorb2:
  assumes incl: \<open>set \<Phi>\<^sub>2 \<subseteq> set \<Phi>\<^sub>1\<close>
  shows \<open>\<lbrakk>\<lbrakk> \<Phi>\<^sub>1 @ \<Phi>\<^sub>2 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L = \<lbrakk>\<lbrakk> \<Phi>\<^sub>1 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<close>
  using TESL_interp_absorb1 TESL_interp_commute incl by blast

section \<open>Some special cases\<close>

lemma NoSporadic_stable [simp]:
  shows \<open>\<lbrakk>\<lbrakk> \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L \<subseteq> \<lbrakk>\<lbrakk> NoSporadic \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<close>
  by (meson filter_is_subset TESL_interp_decreases_setinc)

lemma NoSporadic_idem [simp]:
  shows \<open>\<lbrakk>\<lbrakk> \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L \<inter> \<lbrakk>\<lbrakk> NoSporadic \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L = \<lbrakk>\<lbrakk> \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<close>
  by (meson Int_absorb2 filter_is_subset TESL_interp_decreases_setinc)

lemma NoSporadic_setinc:
  shows \<open>set (NoSporadic \<Phi>) \<subseteq> set \<Phi>\<close>
  by auto

(*<*)
no_notation dummyT0    ("t\<^sub>0")
no_notation dummyDeltaT ("\<delta>t")
(*>*)

end
