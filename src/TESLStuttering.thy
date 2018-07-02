theory TESLStuttering
imports Denotational

begin
text {*
  A dilating function inserts empty instants in a run.
  It is strictly increasing, the image of a nat is greater than it, 
  and if n is not in the image of the function, no clock ticks at instant n.
*}
definition dilating_fun
where
  "dilating_fun (f::nat \<Rightarrow> nat) (r::'a::linordered_field run)
    \<equiv> strict_mono f \<and> (\<forall>n. f n \<ge> n \<and> ((\<nexists>n\<^sub>0. f n\<^sub>0 = n) \<longrightarrow> (\<forall>c. \<not>(hamlet ((Rep_run r) n c)))))"

lemma dilating_fun_injects:
  assumes "dilating_fun f r"
  shows   "inj_on f A"
using assms dilating_fun_def strict_mono_imp_inj_on by blast

text {*
  If a clock ticks at an instant in a dilated run, that instant is the image
  by the dilating function of an instant of the original run.
*}
lemma ticks_image:
  assumes "dilating_fun f r"
  and     "hamlet ((Rep_run r) n c)"
  shows   "\<exists>n\<^sub>0. f n\<^sub>0 = n"
using dilating_fun_def assms by blast

text {*
  The image of the ticks in a interval by a dilating function is the interval 
  bounded by the image of the bound of the original interval.
  This is proven for all 4 kinds of intervals: ]m, n[, [m, n[, ]m, n] and [m, n].
*}
lemma dilating_fun_image_strict:
  assumes "dilating_fun f r"
  shows   "{k. f m < k \<and> k < f n \<and> hamlet ((Rep_run r) k c)}
            = image f {k. m < k \<and> k < n \<and> hamlet ((Rep_run r) (f k) c)}"
  (is "?IMG = image f ?SET")
proof
  { fix k assume h:"k \<in> ?IMG"
    from h obtain k\<^sub>0 where k0prop:"f k\<^sub>0 = k \<and> hamlet ((Rep_run r) (f k\<^sub>0) c)"
      using ticks_image[OF assms] by blast
    with h have "k \<in> image f ?SET" using assms dilating_fun_def strict_mono_less by blast
  } thus "?IMG \<subseteq> image f ?SET" ..
next
  { fix k assume h:"k \<in> image f ?SET"
    from h obtain k\<^sub>0 where k0prop:"k = f k\<^sub>0 \<and> k\<^sub>0 \<in> ?SET" by blast
    hence "k \<in> ?IMG" using assms dilating_fun_def strict_mono_less by blast
  } thus "image f ?SET \<subseteq> ?IMG" ..
qed

lemma dilating_fun_image_left:
  assumes "dilating_fun f r"
  shows   "{k. f m \<le> k \<and> k < f n \<and> hamlet ((Rep_run r) k c)}
          = image f {k. m \<le> k \<and> k < n \<and> hamlet ((Rep_run r) (f k) c)}"
  (is "?IMG = image f ?SET")
proof
  { fix k assume h:"k \<in> ?IMG"
    from h obtain k\<^sub>0 where k0prop:"f k\<^sub>0 = k \<and> hamlet ((Rep_run r) (f k\<^sub>0) c)"
      using ticks_image[OF assms] by blast
    with h have "k \<in> image f ?SET"
      using assms dilating_fun_def strict_mono_less strict_mono_less_eq by fastforce
  } thus "?IMG \<subseteq> image f ?SET" ..
next
  { fix k assume h:"k \<in> image f ?SET"
    from h obtain k\<^sub>0 where k0prop:"k = f k\<^sub>0 \<and> k\<^sub>0 \<in> ?SET" by blast
    hence "k \<in> ?IMG"
      using assms dilating_fun_def strict_mono_less strict_mono_less_eq by fastforce
  } thus "image f ?SET \<subseteq> ?IMG" ..
qed

lemma dilating_fun_image_right:
  assumes "dilating_fun f r"
  shows   "{k. f m < k \<and> k \<le> f n \<and> hamlet ((Rep_run r) k c)}
          = image f {k. m < k \<and> k \<le> n \<and> hamlet ((Rep_run r) (f k) c)}"
  (is "?IMG = image f ?SET")
proof
  { fix k assume h:"k \<in> ?IMG"
    from h obtain k\<^sub>0 where k0prop:"f k\<^sub>0 = k \<and> hamlet ((Rep_run r) (f k\<^sub>0) c)"
      using ticks_image[OF assms] by blast
    with h have "k \<in> image f ?SET"
      using assms dilating_fun_def strict_mono_less strict_mono_less_eq by fastforce
  } thus "?IMG \<subseteq> image f ?SET" ..
next
  { fix k assume h:"k \<in> image f ?SET"
    from h obtain k\<^sub>0 where k0prop:"k = f k\<^sub>0 \<and> k\<^sub>0 \<in> ?SET" by blast
    hence "k \<in> ?IMG"
      using assms dilating_fun_def strict_mono_less strict_mono_less_eq by fastforce
  } thus "image f ?SET \<subseteq> ?IMG" ..
qed

lemma dilating_fun_image:
  assumes "dilating_fun f r"
  shows   "{k. f m \<le> k \<and> k \<le> f n \<and> hamlet ((Rep_run r) k c)}
          = image f {k. m \<le> k \<and> k \<le> n \<and> hamlet ((Rep_run r) (f k) c)}"
  (is "?IMG = image f ?SET")
proof
  { fix k assume h:"k \<in> ?IMG"
    from h obtain k\<^sub>0 where k0prop:"f k\<^sub>0 = k \<and> hamlet ((Rep_run r) (f k\<^sub>0) c)"
      using ticks_image[OF assms] by blast
    with h have "k \<in> image f ?SET"
      using assms dilating_fun_def strict_mono_less_eq by blast
  } thus "?IMG \<subseteq> image f ?SET" ..
next
  { fix k assume h:"k \<in> image f ?SET"
    from h obtain k\<^sub>0 where k0prop:"k = f k\<^sub>0 \<and> k\<^sub>0 \<in> ?SET" by blast
    hence "k \<in> ?IMG" using assms dilating_fun_def strict_mono_less_eq by blast
  } thus "image f ?SET \<subseteq> ?IMG" ..
qed

text {*
  On any clock, the number of ticks in an interval is preserved
  by a dilating function.
*}
lemma ticks_as_often_strict:
  assumes "dilating_fun f r"
  shows   "card {p. n < p \<and> p < m \<and> hamlet ((Rep_run r) (f p) c)}
          = card {p. f n < p \<and> p < f m \<and> hamlet ((Rep_run r) p c)}"
    (is "card ?SET = card ?IMG")
proof -
  from dilating_fun_injects[OF assms] have "inj_on f ?SET" .
  moreover have "finite ?SET" by simp
  from inj_on_iff_eq_card[OF this] calculation have "card (image f ?SET) = card ?SET" by blast
  moreover from dilating_fun_image_strict[OF assms] have "?IMG = image f ?SET" .
  ultimately show ?thesis by auto
qed

lemma ticks_as_often_left:
  assumes "dilating_fun f r"
  shows   "card {p. n \<le> p \<and> p < m \<and> hamlet ((Rep_run r) (f p) c)}
          = card {p. f n \<le> p \<and> p < f m \<and> hamlet ((Rep_run r) p c)}"
    (is "card ?SET = card ?IMG")
proof -
  from dilating_fun_injects[OF assms] have "inj_on f ?SET" .
  moreover have "finite ?SET" by simp
  from inj_on_iff_eq_card[OF this] calculation have "card (image f ?SET) = card ?SET" by blast
  moreover from dilating_fun_image_left[OF assms] have "?IMG = image f ?SET" .
  ultimately show ?thesis by auto
qed

lemma ticks_as_often_right:
  assumes "dilating_fun f r"
  shows   "card {p. n < p \<and> p \<le> m \<and> hamlet ((Rep_run r) (f p) c)}
          = card {p. f n < p \<and> p \<le> f m \<and> hamlet ((Rep_run r) p c)}"
    (is "card ?SET = card ?IMG")
proof -
  from dilating_fun_injects[OF assms] have "inj_on f ?SET" .
  moreover have "finite ?SET" by simp
  from inj_on_iff_eq_card[OF this] calculation have "card (image f ?SET) = card ?SET" by blast
  moreover from dilating_fun_image_right[OF assms] have "?IMG = image f ?SET" .
  ultimately show ?thesis by auto
qed

lemma ticks_as_often:
  assumes "dilating_fun f r"
  shows   "card {p. n \<le> p \<and> p \<le> m \<and> hamlet ((Rep_run r) (f p) c)}
          = card {p. f n \<le> p \<and> p \<le> f m \<and> hamlet ((Rep_run r) p c)}"
    (is "card ?SET = card ?IMG")
proof -
  from dilating_fun_injects[OF assms] have "inj_on f ?SET" .
  moreover have "finite ?SET" by simp
  from inj_on_iff_eq_card[OF this] calculation have "card (image f ?SET) = card ?SET" by blast
  moreover from dilating_fun_image[OF assms] have "?IMG = image f ?SET" .
  ultimately show ?thesis by auto
qed

text {*
  Dilating a run. A run r is a dilation of a run sub by function f if:
    * f is a dilating function on the hamlet of r
    * the time in r is the time in sub dilated by f
    * the hamlet in r is the hamlet in sub dilated by f
*}
definition dilating
  where "dilating f sub r \<equiv>   dilating_fun f r
                            \<and> (\<forall>n c. time ((Rep_run sub) n c) = time ((Rep_run r) (f n) c))
                            \<and> (\<forall>n c. hamlet ((Rep_run sub) n c) = hamlet ((Rep_run r) (f n) c))"

lemma dilating_injects:
  assumes "dilating f sub r"
  shows   "inj_on f A"
using assms by (simp add: dilating_def dilating_fun_def strict_mono_imp_inj_on)

text {*
  If there is a tick at instant n in a dilated run, n is necessarily the image
  of some instant in the subrun.
*}
lemma ticks_image_sub:
  assumes "dilating f sub r"
  and     "hamlet ((Rep_run r) n c)"
  shows   "\<exists>n\<^sub>0. f n\<^sub>0 = n"
using assms dilating_def ticks_image by metis

lemma ticks_image_sub':
  assumes "dilating f sub r"
  and     "\<exists>c. hamlet ((Rep_run r) n c)"
  shows   "\<exists>n\<^sub>0. f n\<^sub>0 = n"
using assms dilating_def dilating_fun_def by metis

text {*
  Time is preserved by dilation when ticks occur.
*}
lemma ticks_tag_image:
  assumes "dilating f sub r"
  and     "\<exists>c. hamlet ((Rep_run r) k c)"
  and     "time ((Rep_run r) k c) = \<tau>"
  shows   "\<exists>k\<^sub>0. f k\<^sub>0 = k \<and> time ((Rep_run sub) k\<^sub>0 c) = \<tau>"
proof -
  from ticks_image_sub'[OF assms(1,2)] have "\<exists>k\<^sub>0. f k\<^sub>0 = k" .
  from this obtain k\<^sub>0 where "f k\<^sub>0 = k" by blast
  moreover with assms(1,3) have "time ((Rep_run sub) k\<^sub>0 c) = \<tau>" by (simp add: dilating_def)
  ultimately show ?thesis by blast
qed

text {*
  A run is a subrun of another run if there exists a dilation between them.
*}
definition is_subrun ::"'a::linordered_field run \<Rightarrow> 'a run \<Rightarrow> bool" (infixl "\<lless>" 60)
where
  "sub \<lless> r \<equiv> (\<exists>f. dilating f sub r)"

text {*
  TESL operators are preserved by dilation.
*}

lemma ticks_sub:
  assumes "dilating f sub r"
  shows   "hamlet ((Rep_run sub) n a) = hamlet ((Rep_run r) (f n) a)"
using assms by (simp add: dilating_def)

lemma no_tick_sub:
  assumes "dilating f sub r"
  shows   "(\<nexists>n\<^sub>0. f n\<^sub>0 = n) \<longrightarrow> \<not>hamlet ((Rep_run r) n a)"
using assms dilating_def dilating_fun_def by blast

text {*
  Lifting a total function to a partial function on an option domain.
*}
definition opt_lift::"('a \<Rightarrow> 'a) \<Rightarrow> ('a option \<Rightarrow> 'a option)"
where
  "opt_lift f \<equiv> \<lambda>x. case x of None \<Rightarrow> None | Some y \<Rightarrow> Some (f y)"

text {*
  The set of instants when a clock ticks in a dilated run is the image by the dilation function
  of the set of instants when it ticks in the subrun.
*}
lemma tick_set_sub:
  assumes "dilating f sub r"
  shows   "{k. hamlet ((Rep_run r) k c)} = image f {k. hamlet ((Rep_run sub) k c)}"
    (is "?R = image f ?S")
proof
  { fix k assume h:"k \<in> ?R"
    with no_tick_sub[OF assms] have "\<exists>k\<^sub>0. f k\<^sub>0 = k" by blast
    from this obtain k\<^sub>0 where k0prop:"f k\<^sub>0 = k" by blast
    with ticks_sub[OF assms] h have "hamlet ((Rep_run sub) k\<^sub>0 c)" by blast
    with k0prop have "k \<in> image f ?S" by blast
  }
  thus "?R \<subseteq> image f ?S" by blast
next
  { fix k assume h:"k \<in> image f ?S"
    from this obtain k\<^sub>0 where "f k\<^sub>0 = k \<and> hamlet ((Rep_run sub) k\<^sub>0 c)" by blast
    with assms have "k \<in> ?R" using ticks_sub by blast 
  }
  thus "image f ?S \<subseteq> ?R" by blast
qed

text {*
  Strictly monotonous functions preserve the least element.
*}
lemma Least_strict_mono:
  assumes "strict_mono f"
  and     "\<exists>x \<in> S. \<forall>y \<in> S. x \<le> y"
  shows   "(LEAST y. y \<in> f ` S) = f (LEAST x. x \<in> S)"
using Least_mono[OF strict_mono_mono, OF assms] .

text {*
  A non empty set of nats has a least element.
*}
lemma Least_nat_ex:
  "(n::nat) \<in> S \<Longrightarrow> \<exists>x \<in> S. (\<forall>y \<in> S. x \<le> y)"
by (induction n rule: nat_less_induct, insert not_le_imp_less, blast)

text {*
  The first instant when a clock ticks in a dilated run is the image by the dilation
  function of the first instant when it ticks in the subrun.
*}
lemma Least_sub:
  assumes "dilating f sub r"
  and     "\<exists>k::nat. hamlet ((Rep_run sub) k c)"
  shows   "(LEAST k. k \<in> {t. hamlet ((Rep_run r) t c)}) = f (LEAST k. k \<in> {t. hamlet ((Rep_run sub) t c)})"
          (is "(LEAST k. k \<in> ?R) = f (LEAST k. k \<in> ?S)")
proof -
  from assms(2) have "\<exists>x. x \<in> ?S" by simp
  hence least:"\<exists>x \<in> ?S. \<forall>y \<in> ?S. x \<le> y"
    using Least_nat_ex ..
  from assms(1) have "strict_mono f" by (simp add: dilating_def dilating_fun_def)
  from Least_strict_mono[OF this least] have
    "(LEAST y. y \<in> f ` ?S)  = f (LEAST x. x \<in> ?S)" .
  with tick_set_sub[OF assms(1), of "c"] show ?thesis by auto
qed

text {*
  If a clock ticks in a run, it ticks in the subrun.
*}
lemma ticks_imp_ticks_sub:
  assumes "dilating f sub r"
  and     "\<exists>k. hamlet ((Rep_run r) k c)"
  shows   "\<exists>k\<^sub>0. hamlet ((Rep_run sub) k\<^sub>0 c)"
proof -
  from assms(2) obtain k where "hamlet ((Rep_run r) k c)" by blast
  with ticks_image_sub[OF assms(1)] ticks_sub[OF assms(1)] show ?thesis by blast
qed

text {*
  Stronger version: it ticks in the subrun and we know when.
*}
lemma ticks_imp_ticks_subk:
  assumes "dilating f sub r"
  and     "hamlet ((Rep_run r) k c)"
  shows   "\<exists>k\<^sub>0. f k\<^sub>0 = k \<and> hamlet ((Rep_run sub) k\<^sub>0 c)"
proof -
  from no_tick_sub[OF assms(1)] assms(2) have "\<exists>k\<^sub>0. f k\<^sub>0 = k" by blast
  from this obtain k\<^sub>0 where "f k\<^sub>0 = k" by blast
  moreover with ticks_sub[OF assms(1)] assms(2) have "hamlet ((Rep_run sub) k\<^sub>0 c)" by blast
  ultimately show ?thesis by blast
qed

(*******************)

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
lemma implies_sub:
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





end
