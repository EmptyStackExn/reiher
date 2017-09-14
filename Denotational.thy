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
                  \<exists>m > n. hamlet ((Rep_run \<rho>) n master)
                          \<and> time ((Rep_run \<rho>) m measuring) = measured_time + \<delta>\<tau>
                 )
        }"

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

theorem TESL_interp_bnd_fixpoint:
  shows "\<lbrakk> \<phi> \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L = fst (gfp (\<lambda>(R, n). (R \<inter> \<lbrakk> \<phi> @\<le> n \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L, n + 1)))"
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

(**) section \<open>Expansion law\<close> (**)
text \<open>Similar to the expansion laws of lattices\<close>

theorem TESL_interp_expansion:
  shows "\<lbrakk>\<lbrakk> \<Phi>\<^sub>1 @ \<Phi>\<^sub>2 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L = \<lbrakk>\<lbrakk> \<Phi>\<^sub>1 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L \<inter> \<lbrakk>\<lbrakk> \<Phi>\<^sub>2 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L"
sorry

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
lemma tesl_intersect_id_left [simp]: "\<lbrakk>\<lbrakk> [] @ \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L = \<lbrakk>\<lbrakk> \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L"
by simp

lemma tesl_intersect_id_right [simp]: "\<lbrakk>\<lbrakk> \<Phi> @ [] \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L = \<lbrakk>\<lbrakk> \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L"
by simp

find_theorems "_ \<inter> _ = _"
section \<open>Decreasing interpretation of TESL formulae\<close>

lemma TESL_sem_decreases_head:
  "\<lbrakk>\<lbrakk> \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L \<supseteq> \<lbrakk>\<lbrakk> \<phi> # \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L"
by simp

lemma TESL_sem_decreases_tail:
  "\<lbrakk>\<lbrakk> \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L \<supseteq> \<lbrakk>\<lbrakk> \<Phi> @ [\<phi>] \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L"
  by (simp add: TESL_interp_expansion)


(** Draft attempts of Burkhart *)
(*
lemma extension_monotone_generqalized1:
  shows "\<lbrakk>\<lbrakk> \<Phi>' @ \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L \<subseteq> \<lbrakk>\<lbrakk> \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L"
proof(induct "\<Phi>'")
    case Nil
    then show ?case by simp
next
    case (Cons a \<Phi>')
    then show ?case by auto
qed

lemma extension_distr:
  shows "\<lbrakk>\<lbrakk> \<Phi> @ \<Phi>' \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L =  \<lbrakk>\<lbrakk> \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L \<inter> \<lbrakk>\<lbrakk> \<Phi>' \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L"
proof(induct "\<Phi>")
  case Nil
  then show ?case by simp
next
  case (Cons a \<Phi>)
  then show ?case by auto
qed

lemma set_append_mono: "set \<Phi> \<subseteq> set \<Phi>' \<Longrightarrow> \<exists> \<Phi>'' . set \<Phi>' =  set(\<Phi>'' @ \<Phi>)" 
sorry

lemma elim_remove1 : "x \<in> set S \<Longrightarrow> \<exists> T T'. remove1 x S = T @ T' \<and> S = T @ [x] @ T' "
sorry


find_theorems "_ \<in> _" "remove1"
lemma "set \<Phi> =  set \<Phi>' \<Longrightarrow> set (remove1 n \<Phi>) =  set (remove1 n \<Phi>')"
sorry

lemma XXX: "\<lbrakk>\<lbrakk> \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L = \<lbrakk>\<lbrakk> remdups \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L"
sorry

lemma  "length \<Phi> \<le> n \<Longrightarrow> length \<Phi>' \<le> n \<Longrightarrow> set \<Phi> =  set \<Phi>'\<Longrightarrow> \<lbrakk>\<lbrakk> \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L =  \<lbrakk>\<lbrakk> \<Phi>' \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L" 
proof(induct n arbitrary: \<Phi> \<Phi>') print_cases
  case 0
  then show ?case by simp
next
  case (Suc n)
     have * : "\<And>n \<Phi> . length \<Phi> = Suc n \<Longrightarrow> \<exists> n. n \<in> set \<Phi>"
              using length_Suc_conv by fastforce
     have **: "length \<Phi> = 0 \<Longrightarrow> \<Phi> = []"
              by simp
  show ?case 
     apply(insert Suc.hyps Suc.prems)
     proof(cases "length \<Phi> \<le> length \<Phi>'")
       case True
       then show ?thesis
            proof(cases "length \<Phi>' = Suc n")
              case True
              then show ?thesis
                 apply(insert *[OF `length \<Phi>' = Suc n`], elim exE, simp)
                 proof - 
                    fix m
                    assume 1: "m \<in> set \<Phi>'" and 2: " length \<Phi>' = Suc n"
                    have *** : "m \<in> set \<Phi>"  by (simp add: Suc.prems(3) \<open>m \<in> set \<Phi>'\<close>)
                    show "\<lbrakk>\<lbrakk> \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L = \<lbrakk>\<lbrakk> \<Phi>' \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L"                       
                      apply(insert 1, drule elim_remove1, insert ***, drule elim_remove1, clarsimp)
                      apply(simp add: extension_distr)
find_theorems (140)"_ \<inter> _ = _ " name:"Set"
                      apply(subst Set.Int_assoc[symmetric])
                      apply(subst Set.Int_commute)
                      apply(subst Set.Int_assoc[symmetric])
                      apply(subst (3) Set.Int_commute)
                      apply(subst Set.Int_assoc)
                      apply(subst Set.Int_assoc)
                      apply(subst extension_distr[symmetric])
                      apply(subst extension_distr[symmetric])
                      apply(subst Suc.hyps)
                      prefer 4 apply(rule refl)
                      using Suc.prems(1) apply auto[1]
                      using True apply auto[1]
                      apply(insert Suc.prems)
(* sledgehammer *)
 sorry
            next
              case False
              then show ?thesis sorry
            qed
 sorry
     next
       case False
       then show ?thesis sorry
     qed 
sledgehammer
 sorry
qed

lemma  "set \<Phi> =  set \<Phi>' \<Longrightarrow> \<lbrakk>\<lbrakk> \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L =  \<lbrakk>\<lbrakk> \<Phi>' \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L" 
find_theorems (450) "set _ = set _"
sorry

lemma **:
  assumes "set \<Phi> \<subseteq> set \<Phi>'"
  shows "\<lbrakk>\<lbrakk> \<Phi>' \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L \<subseteq> \<lbrakk>\<lbrakk> \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L"
apply(insert assms[THEN set_append_mono], clarsimp)
sorry
*)

theorem TESL_interp_decreases_setinc:
  assumes incl: "set \<Phi> \<subseteq> set \<Phi>'"
  shows "\<lbrakk>\<lbrakk> \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L \<supseteq> \<lbrakk>\<lbrakk> \<Phi>' \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L"
sorry

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
