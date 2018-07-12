theory TESLStuttering
imports TESLStutteringLemmas

begin

text {*
  Sporadic specifications are preserved in a dilated run.
*}
lemma sporadic_sub:
  assumes "sub \<lless> r"
      and "sub \<in> \<lbrakk>c sporadic \<lparr>\<tau>\<rparr> on c'\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L"
    shows "r \<in> \<lbrakk>c sporadic \<lparr>\<tau>\<rparr> on c'\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L"
proof -
  from assms(1) is_subrun_def obtain f
    where "dilating f sub r" by blast
  hence "\<forall>n c. time ((Rep_run sub) n c) = time ((Rep_run r) (f n) c)
           \<and> hamlet ((Rep_run sub) n c) = hamlet ((Rep_run r) (f n) c)" by (simp add: dilating_def)
  moreover from assms(2) have
    "sub \<in> {r. \<exists> n. hamlet ((Rep_run r) n c) \<and> time ((Rep_run r) n c') = \<tau>}" by simp
  from this obtain k where "time ((Rep_run sub) k c') = \<tau> \<and> hamlet ((Rep_run sub) k c)" by auto
  ultimately have "time ((Rep_run r) (f k) c') = \<tau> \<and> hamlet ((Rep_run r) (f k) c)" by simp
  thus ?thesis by auto
qed

text {*
  Implications are preserved in a dilated run.
*}
theorem implies_sub:
  assumes "sub \<lless> r"
      and "sub \<in> \<lbrakk>c\<^sub>1 implies c\<^sub>2\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L"
    shows "r \<in> \<lbrakk>c\<^sub>1 implies c\<^sub>2\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L"
proof -
  from assms(1) is_subrun_def obtain f where "dilating f sub r" by blast
  moreover from assms(2) have
    "sub \<in> {r. \<forall>n. hamlet ((Rep_run r) n c\<^sub>1) \<longrightarrow> hamlet ((Rep_run r) n c\<^sub>2)}" by simp
  hence "\<forall>n. hamlet ((Rep_run sub) n c\<^sub>1) \<longrightarrow> hamlet ((Rep_run sub) n c\<^sub>2)" by simp
  ultimately have "\<forall>n. hamlet ((Rep_run r) n c\<^sub>1) \<longrightarrow> hamlet ((Rep_run r) n c\<^sub>2)"
    using ticks_imp_ticks_subk ticks_sub by blast
  thus ?thesis by simp
qed

theorem implies_not_sub:
  assumes "sub \<lless> r"
      and "sub \<in> \<lbrakk>c\<^sub>1 implies not c\<^sub>2\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L"
    shows "r \<in> \<lbrakk>c\<^sub>1 implies not c\<^sub>2\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L"
proof -
  from assms(1) is_subrun_def obtain f where "dilating f sub r" by blast
  moreover from assms(2) have
    "sub \<in> {r. \<forall>n. hamlet ((Rep_run r) n c\<^sub>1) \<longrightarrow> \<not> hamlet ((Rep_run r) n c\<^sub>2)}" by simp
  hence "\<forall>n. hamlet ((Rep_run sub) n c\<^sub>1) \<longrightarrow> \<not> hamlet ((Rep_run sub) n c\<^sub>2)" by simp
  ultimately have "\<forall>n. hamlet ((Rep_run r) n c\<^sub>1) \<longrightarrow> \<not> hamlet ((Rep_run r) n c\<^sub>2)"
    using ticks_imp_ticks_subk ticks_sub by blast
  thus ?thesis by simp
qed

text {*
  Precedence relations are preserved in a dilated run.
*}
theorem weakly_precedes_sub:
  assumes "sub \<lless> r"
      and "sub \<in> \<lbrakk>c\<^sub>1 weakly precedes c\<^sub>2\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L"
    shows "r \<in> \<lbrakk>c\<^sub>1 weakly precedes c\<^sub>2\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L"
proof -
  from assms(1) is_subrun_def obtain f where *:"dilating f sub r" by blast
  from assms(2) have
    "sub \<in> {r. \<forall>n. (run_tick_count r c\<^sub>2 n) \<le> (run_tick_count r c\<^sub>1 n)}" by simp
  hence "\<forall>n. (run_tick_count sub c\<^sub>2 n) \<le> (run_tick_count sub c\<^sub>1 n)" by simp
  from dil_tick_count[OF assms(1) this] have "\<forall>n. (run_tick_count r c\<^sub>2 n) \<le> (run_tick_count r c\<^sub>1 n)" by simp
  thus ?thesis by simp
qed

theorem strictly_precedes_sub2:
  assumes "sub \<lless> r"
      and "sub \<in> \<lbrakk>c\<^sub>1 strictly precedes c\<^sub>2\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L"
    shows "r \<in> \<lbrakk>c\<^sub>1 strictly precedes c\<^sub>2\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L"
proof -
  from assms(1) is_subrun_def obtain f where *:"dilating f sub r" by blast
  from assms(2) have "sub \<in> { \<rho>. \<forall>n::nat. (run_tick_count \<rho> c\<^sub>2 n) \<le> (run_tick_count_strictly \<rho> c\<^sub>1 n) }" by simp
  with strictly_precedes_alt_def2[of "c\<^sub>2" "c\<^sub>1"]  have
    "sub \<in> { \<rho>. (\<not>hamlet ((Rep_run \<rho>) 0 c\<^sub>2)) \<and> (\<forall>n::nat. (run_tick_count \<rho> c\<^sub>2 (Suc n)) \<le> (run_tick_count \<rho> c\<^sub>1 n)) }"
  by blast
  hence "(\<not>hamlet ((Rep_run sub) 0 c\<^sub>2)) \<and> (\<forall>n::nat. (run_tick_count sub c\<^sub>2 (Suc n)) \<le> (run_tick_count sub c\<^sub>1 n))"
    by simp
  hence
    1:"(\<not>hamlet ((Rep_run sub) 0 c\<^sub>2)) \<and> (\<forall>n::nat. (tick_count sub c\<^sub>2 (Suc n)) \<le> (tick_count sub c\<^sub>1 n))"
  by (simp add: tick_count_is_fun)
  have "\<forall>n::nat. (tick_count r c\<^sub>2 (Suc n)) \<le> (tick_count r c\<^sub>1 n)"
  proof -
    { fix n::nat
      have "tick_count r c\<^sub>2 (Suc n) \<le> tick_count r c\<^sub>1 n"
      proof (cases "\<exists>n\<^sub>0. f n\<^sub>0 = n")
        case True (* n is in the image of f *)
          from this obtain n\<^sub>0 where fn:"f n\<^sub>0 = n" by blast
          show ?thesis
          proof (cases "\<exists>sn\<^sub>0. f sn\<^sub>0 = Suc n")
            case True (* Suc n is in the image of f *)
              from this obtain sn\<^sub>0 where fsn:"f sn\<^sub>0 = Suc n" by blast
              with fn have "sn\<^sub>0 = Suc n\<^sub>0" using strict_mono_suc * dilating_def dilating_fun_def by blast
              with 1 have "tick_count sub c\<^sub>2 sn\<^sub>0 \<le> tick_count sub c\<^sub>1 n\<^sub>0" by simp
              thus ?thesis using fn fsn tick_count_sub[OF *] by simp
          next
            case False (* Suc n is not in the image of f *)
              hence "\<not>hamlet ((Rep_run r) (Suc n) c\<^sub>2)"
                using * by (simp add: dilating_def dilating_fun_def)
              hence "tick_count r c\<^sub>2 (Suc n) = tick_count r c\<^sub>2 n" by (simp add: tick_count_suc)
              also have "... = tick_count sub c\<^sub>2 n\<^sub>0" using fn tick_count_sub[OF *] by simp
              finally have "tick_count r c\<^sub>2 (Suc n) = tick_count sub c\<^sub>2 n\<^sub>0" .
              moreover have "tick_count sub c\<^sub>2 n\<^sub>0 \<le> tick_count sub c\<^sub>2 (Suc n\<^sub>0)"
                by (simp add: tick_count_suc)
              ultimately have "tick_count r c\<^sub>2 (Suc n) \<le> tick_count sub c\<^sub>2 (Suc n\<^sub>0)" by simp
              moreover have "tick_count sub c\<^sub>2 (Suc n\<^sub>0) \<le> tick_count sub c\<^sub>1 n\<^sub>0" using 1 by simp
              ultimately have "tick_count r c\<^sub>2 (Suc n) \<le> tick_count sub c\<^sub>1 n\<^sub>0" by simp
              thus ?thesis using tick_count_sub[OF *] fn by simp
          qed
      next
        case False (* n is not in the image of f *)
          from greatest_prev_image[OF * this] obtain n\<^sub>p
            where np_prop:"f n\<^sub>p < n \<and> (\<forall>k. f n\<^sub>p < k \<and> k \<le> n \<longrightarrow> (\<nexists>k\<^sub>0. f k\<^sub>0 = k))" by blast
          from tick_count_latest[OF * this] have "tick_count r c\<^sub>1 n = tick_count r c\<^sub>1 (f n\<^sub>p)" . 
          hence a:"tick_count r c\<^sub>1 n = tick_count sub c\<^sub>1 n\<^sub>p" using tick_count_sub[OF *] by simp
          have b: "tick_count sub c\<^sub>2 (Suc n\<^sub>p) \<le> tick_count sub c\<^sub>1 n\<^sub>p" using 1 by simp
          show ?thesis
          proof (cases "\<exists>sn\<^sub>0. f sn\<^sub>0 = Suc n")
            case True (* Suc n is in the image of f *)
              from this obtain sn\<^sub>0 where fsn:"f sn\<^sub>0 = Suc n" by blast
              from next_non_stuttering[OF * np_prop this]  have sn_prop:"sn\<^sub>0 = Suc n\<^sub>p" .
              with b have "tick_count sub c\<^sub>2 sn\<^sub>0 \<le> tick_count sub c\<^sub>1 n\<^sub>p" by simp
              thus ?thesis using tick_count_sub[OF *] fsn a by auto
          next
            case False (* Suc n is not in the image of f *)
              hence "\<not>hamlet ((Rep_run r) (Suc n) c\<^sub>2)"
                using * by (simp add: dilating_def dilating_fun_def)
              hence "tick_count r c\<^sub>2 (Suc n) = tick_count r c\<^sub>2 n" by (simp add: tick_count_suc)
              also have "... = tick_count sub c\<^sub>2 n\<^sub>p" using np_prop tick_count_sub[OF *]
                by (simp add: tick_count_latest[OF * np_prop])
              finally have "tick_count r c\<^sub>2 (Suc n) = tick_count sub c\<^sub>2 n\<^sub>p" .
              moreover have "tick_count sub c\<^sub>2 n\<^sub>p \<le> tick_count sub c\<^sub>2 (Suc n\<^sub>p)"
                by (simp add: tick_count_suc)
              ultimately have "tick_count r c\<^sub>2 (Suc n) \<le> tick_count sub c\<^sub>2 (Suc n\<^sub>p)" by simp
              moreover have "tick_count sub c\<^sub>2 (Suc n\<^sub>p) \<le> tick_count sub c\<^sub>1 n\<^sub>p" using 1 by simp
              ultimately have "tick_count r c\<^sub>2 (Suc n) \<le> tick_count sub c\<^sub>1 n\<^sub>p" by simp
              thus ?thesis using np_prop mono_tick_count  using a by linarith
          qed
      qed
    } thus ?thesis ..
  qed
  moreover from 1 have "\<not>hamlet ((Rep_run r) 0 c\<^sub>2)"
    using "*" empty_dilated_prefix ticks_sub by fastforce
  ultimately show ?thesis by (simp add: tick_count_is_fun strictly_precedes_alt_def2) 
qed

text {*
  Time delayed relations are preserved in a dilated run.
*}
theorem time_delayed_sub:
  assumes "sub \<lless> r"
      and "sub \<in> \<lbrakk> a time-delayed by \<delta>\<tau> on ms implies b \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L"
    shows "r \<in> \<lbrakk> a time-delayed by \<delta>\<tau> on ms implies b \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L"
proof -
  from assms(1) is_subrun_def obtain f where *:"dilating f sub r" by blast
  from assms(2) have "\<forall>n. hamlet ((Rep_run sub) n a)
                          \<longrightarrow> (\<exists>m \<ge> n. hamlet ((Rep_run sub) m b)
                                    \<and> time ((Rep_run sub) m ms) =  time ((Rep_run sub) n ms) + \<delta>\<tau>)"
    using TESL_interpretation_atomic.simps(6)[of "a" "\<delta>\<tau>" "ms" "b"] by simp
  hence **:"\<forall>n\<^sub>0. hamlet ((Rep_run r) (f n\<^sub>0) a)
                  \<longrightarrow> (\<exists>m\<^sub>0 \<ge> n\<^sub>0. hamlet ((Rep_run r) (f m\<^sub>0) b)
                             \<and>  time ((Rep_run r) (f m\<^sub>0) ms) = time ((Rep_run r) (f n\<^sub>0) ms) + \<delta>\<tau>)"
    using * by (simp add: dilating_def)
  hence "\<forall>n. hamlet ((Rep_run r) n a)
                  \<longrightarrow> (\<exists>m \<ge> n. hamlet ((Rep_run r) m b)
                             \<and> time ((Rep_run r) m ms) = time ((Rep_run r) n ms) + \<delta>\<tau>)"
  proof -
    { fix n assume assm:"hamlet ((Rep_run r) n a)"
      from ticks_image_sub[OF * assm] obtain n\<^sub>0 where nfn0:"n = f n\<^sub>0" by blast
      with ** assm have
        "(\<exists>m\<^sub>0 \<ge> n\<^sub>0. hamlet ((Rep_run r) (f m\<^sub>0) b)
               \<and>  time ((Rep_run r) (f m\<^sub>0) ms) = time ((Rep_run r) (f n\<^sub>0) ms) + \<delta>\<tau>)" by blast
      hence "(\<exists>m \<ge> n. hamlet ((Rep_run r) m b)
               \<and>  time ((Rep_run r) m ms) = time ((Rep_run r) n ms) + \<delta>\<tau>)"
        using * nfn0 dilating_def dilating_fun_def by (metis strict_mono_less_eq)
    } thus ?thesis by simp
  qed
  thus ?thesis by simp
qed

text {*
  Time relations are preserved by contraction
*}
lemma tagrel_sub_inv:
  assumes "sub \<lless> r"
      and "r \<in> \<lbrakk> time-relation \<lfloor>c\<^sub>1, c\<^sub>2\<rfloor> \<in> R \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L"
    shows "sub \<in> \<lbrakk> time-relation \<lfloor>c\<^sub>1, c\<^sub>2\<rfloor> \<in> R \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L"
proof -
  from assms(1) is_subrun_def obtain f where df:"dilating f sub r" by blast
  moreover from assms(2) TESL_interpretation_atomic.simps(3) have
    "r \<in> {\<rho>. \<forall>n. R (time ((Rep_run \<rho>) n c\<^sub>1), time ((Rep_run \<rho>) n c\<^sub>2))}" by blast
  hence "\<forall>n. R (time ((Rep_run r) n c\<^sub>1), time ((Rep_run r) n c\<^sub>2))" by simp
  hence "\<forall>n. (\<exists>n\<^sub>0. f n\<^sub>0 = n) \<longrightarrow> R (time ((Rep_run r) n c\<^sub>1), time ((Rep_run r) n c\<^sub>2))" by simp
  hence "\<forall>n\<^sub>0. R (time ((Rep_run r) (f n\<^sub>0) c\<^sub>1), time ((Rep_run r) (f n\<^sub>0) c\<^sub>2))" by blast
  moreover from dilating_def df have
    "\<forall>n c. time ((Rep_run sub) n c) = time ((Rep_run r) (f n) c)" by blast
  ultimately have "\<forall>n\<^sub>0. R (time ((Rep_run sub) n\<^sub>0 c\<^sub>1), time ((Rep_run sub) n\<^sub>0 c\<^sub>2))" by auto
  thus ?thesis by simp
qed

text {*
  A time relation is preserved through dilation of a run.
*}
lemma tagrel_sub':
  assumes "sub \<lless> r"
      and "sub \<in> \<lbrakk> time-relation \<lfloor>c\<^sub>1,c\<^sub>2\<rfloor> \<in> R \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L"
    shows "R (time ((Rep_run r) n c\<^sub>1), time ((Rep_run r) n c\<^sub>2))"
proof -
  from assms(1) is_subrun_def obtain f where *:"dilating f sub r" by blast
  moreover from assms(2) TESL_interpretation_atomic.simps(3) have
    "sub \<in> {r. \<forall>n. R (time ((Rep_run r) n c\<^sub>1), time ((Rep_run r) n c\<^sub>2))}" by blast
  hence 1:"\<forall>n. R (time ((Rep_run sub) n c\<^sub>1), time ((Rep_run sub) n c\<^sub>2))" by simp
  show ?thesis
  proof (induction n)
    case 0
    then show ?case
      by (metis (no_types, lifting) "1" calculation dilating_def dilating_fun_def)
  next
    case (Suc n)
    then show ?case
    proof (cases "\<nexists>n\<^sub>0. f n\<^sub>0 = Suc n")
      case True
        thus ?thesis by (metis Suc.IH calculation dilating_def dilating_fun_def)
    next
      case False
      from this obtain n\<^sub>0 where n\<^sub>0prop:"f n\<^sub>0 = Suc n" by blast
      from 1 have "R (time ((Rep_run sub) n\<^sub>0 c\<^sub>1), time ((Rep_run sub) n\<^sub>0 c\<^sub>2))" by simp
      moreover from n\<^sub>0prop * have "time ((Rep_run sub) n\<^sub>0 c\<^sub>1) = time ((Rep_run r) (Suc n) c\<^sub>1)"
        by (simp add: dilating_def)
      moreover from n\<^sub>0prop * have "time ((Rep_run sub) n\<^sub>0 c\<^sub>2) = time ((Rep_run r) (Suc n) c\<^sub>2)"
        by (simp add: dilating_def)
      ultimately show ?thesis by simp
    qed
  qed
qed

corollary tagrel_sub:
  assumes "sub \<lless> r"
      and "sub \<in> \<lbrakk> time-relation \<lfloor>c\<^sub>1,c\<^sub>2\<rfloor> \<in> R \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L"
    shows "r \<in> \<lbrakk> time-relation \<lfloor>c\<^sub>1,c\<^sub>2\<rfloor> \<in> R \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L"
using tagrel_sub'[OF assms] unfolding TESL_interpretation_atomic.simps(3) by simp

theorem kill_sub:
  assumes "sub \<lless> r"
      and "sub \<in> \<lbrakk> c\<^sub>1 kills c\<^sub>2 \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L"
    shows "r \<in> \<lbrakk> c\<^sub>1 kills c\<^sub>2 \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L"
proof -
  from assms(1) is_subrun_def obtain f where *:"dilating f sub r" by blast
  from assms(2) TESL_interpretation_atomic.simps(9) have
    "\<forall>n. hamlet (Rep_run sub n c\<^sub>1) \<longrightarrow> (\<forall>m\<ge>n. \<not> hamlet (Rep_run sub m c\<^sub>2))" by simp
  hence "\<forall>n. hamlet (Rep_run r (f n) c\<^sub>1) \<longrightarrow> (\<forall>m\<ge>n. \<not> hamlet (Rep_run r (f m) c\<^sub>2))"
    using ticks_sub[OF *] by simp
  hence "\<forall>n. hamlet (Rep_run r (f n) c\<^sub>1) \<longrightarrow> (\<forall>m\<ge> (f n). \<not> hamlet (Rep_run r m c\<^sub>2))"
    by (metis "*" dilating_def dilating_fun_def strict_mono_less_eq)
  hence "\<forall>n. hamlet (Rep_run r n c\<^sub>1) \<longrightarrow> (\<forall>m \<ge> n. \<not> hamlet (Rep_run r m c\<^sub>2))"
    using ticks_imp_ticks_subk[OF *] by blast
  thus ?thesis using TESL_interpretation_atomic.simps(9) by blast
qed

end
