theory Denotational
imports
    "TESL"
    "Run"

begin

(* Denotational interpretation of TESL *)
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
                  \<exists>m \<ge> n. hamlet ((Rep_run \<rho>) n master)
                          \<and> time ((Rep_run \<rho>) m measuring) = measured_time + \<delta>\<tau>
                 )
        }"

(* Denotational interpretation of TESL bounded by index *)
fun TESL_interpretation_primitive_at_index
    :: "TESL_atomic \<Rightarrow> nat \<Rightarrow> run set" ("\<lbrakk> _ @ _ \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L") where
    "\<lbrakk> K sporadic \<tau> @ n \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L =
        { \<rho>. hamlet ((Rep_run \<rho>) n K) = True \<and> time ((Rep_run \<rho>) n K) = \<tau> }"
  | "\<lbrakk> K\<^sub>1 sporadic \<lfloor>\<tau>\<rfloor> on K\<^sub>2 @ n \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L =
        { \<rho>. hamlet ((Rep_run \<rho>) n K\<^sub>1) = True \<and> time ((Rep_run \<rho>) n K\<^sub>2) = \<tau> }"
  | "\<lbrakk> K\<^sub>1 sporadic \<lfloor>\<tau>\<^sub>v\<^sub>a\<^sub>r(K, n') \<oplus> \<tau>\<rfloor> on K\<^sub>2 @ n \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L =
        { \<rho>. hamlet ((Rep_run \<rho>) n K\<^sub>1) = True
                         \<and> time ((Rep_run \<rho>) n K\<^sub>2) = time ((Rep_run \<rho>) n' K) + \<tau> }"
  | "\<lbrakk> tag-relation K\<^sub>1 = \<alpha> * K\<^sub>2 + \<beta> @ n \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L =
        { \<rho>. time ((Rep_run \<rho>) n K\<^sub>1) = \<alpha> * time ((Rep_run \<rho>) n K\<^sub>2) + \<beta> }"
  | "\<lbrakk> master implies slave @ n \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L =
        { \<rho>. hamlet ((Rep_run \<rho>) n master) \<longrightarrow> hamlet ((Rep_run \<rho>) n slave) }"
  | "\<lbrakk> master time-delayed by \<delta>\<tau> on measuring implies slave @ n \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L =
        { \<rho>. hamlet ((Rep_run \<rho>) n master) \<longrightarrow>
                 (let measured_time = time ((Rep_run \<rho>) n measuring) in
                  \<exists>m \<ge> n. hamlet ((Rep_run \<rho>) n master)
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
  shows "\<lbrakk> K sporadic \<tau> \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L = \<Union> {Y. \<exists>n::nat. Y = \<lbrakk> K sporadic \<tau> @ n \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L}"
  by auto

lemma TESL_interp_unfold_at_index_sporadicon:
  shows "\<lbrakk> K\<^sub>1 sporadic \<lfloor>\<tau>\<rfloor> on K\<^sub>2 \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L = \<Union> {Y. \<exists>n::nat. Y = \<lbrakk> K\<^sub>1 sporadic \<lfloor>\<tau>\<rfloor> on K\<^sub>2 @ n \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L}"
  by auto

lemma TESL_interp_unfold_at_index_sporadicon_add:
  shows "\<lbrakk> K\<^sub>1 sporadic \<lfloor>\<tau>\<^sub>v\<^sub>a\<^sub>r(K, n') \<oplus> \<tau>\<rfloor> on K\<^sub>2 \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L = \<Union> {Y. \<exists>n::nat. Y = \<lbrakk> K\<^sub>1 sporadic \<lfloor>\<tau>\<^sub>v\<^sub>a\<^sub>r(K, n') \<oplus> \<tau>\<rfloor> on K\<^sub>2 @ n \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L}"
  by auto

lemma TESL_interp_unfold_at_index_tagrel:
  shows "\<lbrakk> tag-relation K\<^sub>1 = \<alpha> * K\<^sub>2 + \<beta> \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L = \<Inter> {Y. \<exists>n::nat. Y = \<lbrakk> tag-relation K\<^sub>1 = \<alpha> * K\<^sub>2 + \<beta> @ n \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L}"
  by auto

lemma TESL_interp_unfold_at_index_implies:
  shows "\<lbrakk> master implies slave \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L = \<Inter> {Y. \<exists>n::nat. Y = \<lbrakk> master implies slave @ n \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L}"
  by auto

lemma TESL_interp_at_index_implies_cases:
  shows "\<lbrakk> master implies slave @ n \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L =
    \<lbrakk> master \<not>\<Up> n \<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n
    \<union> \<lbrakk> master \<Up> n \<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n \<inter> \<lbrakk> slave \<Up> n \<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n"
  by auto

lemma TESL_interp_unfold_at_index_timedelayed:
  shows "\<lbrakk> master time-delayed by \<delta>\<tau> on measuring implies slave \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L
    = \<Inter> {Y. \<exists>n::nat. Y = \<lbrakk> master time-delayed by \<delta>\<tau> on measuring implies slave @ n \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L}"
  by auto

lemma TESL_interp_at_index_timedelayed_cases:
  shows "\<lbrakk> master time-delayed by \<delta>\<tau> on measuring implies slave @ n \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L =
    \<lbrakk> master \<not>\<Up> n \<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n
    \<union> \<lbrakk> master \<Up> n \<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n \<inter> \<lbrakk> slave sporadic \<lfloor>\<tau>\<^sub>v\<^sub>a\<^sub>r(measuring, n) \<oplus> \<delta>\<tau>\<rfloor> on measuring \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L" nitpick
sorry

(* Denotational interpretation of TESL bounded by index *)
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

(* CONJECTURE: Not sure it is true *)
theorem TESL_interp_bnd_fixpoint:
  shows "\<lbrakk> \<phi> \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L = fst (gfp (\<lambda>(R, n). (R \<inter> \<lbrakk> \<phi> @\<le> n \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L, n + 1)))"
  oops

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

(**) section \<open>Fixpoint lemma\<close> (**)

theorem TESL_interp_fixpoint:
  "\<lbrakk>\<lbrakk> \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L = \<Inter> ((\<lambda>\<phi>. \<lbrakk> \<phi> \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L) ` set \<Phi>)"
  proof (induct \<Phi>)
    case Nil
    then show ?case by simp
  next
    case (Cons a \<Phi>)
    then show ?case by auto
  qed

(**) section \<open>Expansion law\<close> (**)
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

(**) section \<open>Equational laws for TESL formulae denotationally interpreted\<close> (**)
(***) subsection \<open>General laws\<close> (***)

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

(***) subsection \<open>Case of filtering out sporadic atoms\<close> (***)

lemma NoSporadic_stable [simp]:
  shows "\<lbrakk>\<lbrakk> \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L \<subseteq> \<lbrakk>\<lbrakk> NoSporadic \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L"
  by (meson filter_is_subset TESL_interp_decreases_setinc)

lemma NoSporadic_idem [simp]:
  shows "\<lbrakk>\<lbrakk> \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L \<inter> \<lbrakk>\<lbrakk> NoSporadic \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L = \<lbrakk>\<lbrakk> \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L"
  by (meson Int_absorb2 filter_is_subset TESL_interp_decreases_setinc)

lemma NoSporadic_setinc:
  shows "set (NoSporadic \<Phi>) \<subseteq> set \<Phi>"
  by auto

(**) section \<open>Equivalence between sporadic variants\<close> (**)

lemma SporadicOn_sugar:
  shows "\<lbrakk> K\<^sub>1 sporadic \<lfloor>\<tau>\<rfloor> on K\<^sub>1 \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L = \<lbrakk> K\<^sub>1 sporadic \<tau> \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L"
  by auto

lemma SporadicOn_sugar':
  shows "\<lbrakk>\<lbrakk> (K\<^sub>1 sporadic \<lfloor>\<tau>\<rfloor> on K\<^sub>1) # \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L = \<lbrakk>\<lbrakk> (K\<^sub>1 sporadic \<tau>) # \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L"
  by auto


(**) section \<open>Run existence for TESL arithmetic-consistent formulae\<close> (**)
fun tagrel_consistent :: "TESL_formula \<Rightarrow> bool" where
  "tagrel_consistent \<Phi> = undefined"

lemma existence:
  (* Assumption that the linear system made of tag relations is consistent *)
  assumes "tagrel_consistent \<Phi>"
  shows "\<exists>\<rho>. \<rho> \<in> \<lbrakk>\<lbrakk> \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L"
oops
(* proof (induction \<Phi>) *)

end
