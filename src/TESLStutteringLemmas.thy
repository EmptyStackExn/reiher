theory TESLStutteringLemmas

imports TESLStutteringDefs

begin

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

text {*
  A dilating function preserves the tick count on an interval for any clock.
*}
lemma dilated_ticks_strict:
  assumes "dilating f sub r"
  shows   "{i. f m < i \<and> i < f n \<and> hamlet ((Rep_run r) i c)}
          = image f {i. m < i \<and> i < n \<and> hamlet ((Rep_run sub) i c)}"
    (is "?RUN = image f ?SUB")
proof
  { fix i assume h:"i \<in> ?SUB"
    hence "m < i \<and> i < n" by simp
    hence "f m < f i \<and> f i < (f n)" using assms
      by (simp add: dilating_def dilating_fun_def strict_monoD strict_mono_less_eq)
    moreover from h have "hamlet ((Rep_run sub) i c)" by simp
    hence "hamlet ((Rep_run r) (f i) c)" using ticks_sub[OF assms] by blast
    ultimately have "f i \<in> ?RUN" by simp
  } thus "image f ?SUB \<subseteq> ?RUN" by blast
next
  { fix i assume h:"i \<in> ?RUN"
    hence "hamlet ((Rep_run r) i c)" by simp
    from ticks_imp_ticks_subk[OF assms this]
      obtain i\<^sub>0 where i0prop:"f i\<^sub>0 = i \<and> hamlet ((Rep_run sub) i\<^sub>0 c)" by blast
    with h have "f m < f i\<^sub>0 \<and> f i\<^sub>0 < f n" by simp
    moreover have "strict_mono f" using assms dilating_def dilating_fun_def by blast
    ultimately have "m < i\<^sub>0 \<and> i\<^sub>0 < n" using strict_mono_less strict_mono_less_eq by blast
    with i0prop have "\<exists>i\<^sub>0. f i\<^sub>0 = i \<and> i\<^sub>0 \<in> ?SUB" by blast
  } thus "?RUN \<subseteq> image f ?SUB" by blast
qed

lemma dilated_ticks_left:
  assumes "dilating f sub r"
  shows   "{i. f m \<le> i \<and> i < f n \<and> hamlet ((Rep_run r) i c)}
          = image f {i. m \<le> i \<and> i < n \<and> hamlet ((Rep_run sub) i c)}"
    (is "?RUN = image f ?SUB")
proof
  { fix i assume h:"i \<in> ?SUB"
    hence "m \<le> i \<and> i < n" by simp
    hence "f m \<le> f i \<and> f i < (f n)" using assms
      by (simp add: dilating_def dilating_fun_def strict_monoD strict_mono_less_eq)
    moreover from h have "hamlet ((Rep_run sub) i c)" by simp
    hence "hamlet ((Rep_run r) (f i) c)" using ticks_sub[OF assms] by blast
    ultimately have "f i \<in> ?RUN" by simp
  } thus "image f ?SUB \<subseteq> ?RUN" by blast
next
  { fix i assume h:"i \<in> ?RUN"
    hence "hamlet ((Rep_run r) i c)" by simp
    from ticks_imp_ticks_subk[OF assms this]
      obtain i\<^sub>0 where i0prop:"f i\<^sub>0 = i \<and> hamlet ((Rep_run sub) i\<^sub>0 c)" by blast
    with h have "f m \<le> f i\<^sub>0 \<and> f i\<^sub>0 < f n" by simp
    moreover have "strict_mono f" using assms dilating_def dilating_fun_def by blast
    ultimately have "m \<le> i\<^sub>0 \<and> i\<^sub>0 < n" using strict_mono_less strict_mono_less_eq by blast
    with i0prop have "\<exists>i\<^sub>0. f i\<^sub>0 = i \<and> i\<^sub>0 \<in> ?SUB" by blast
  } thus "?RUN \<subseteq> image f ?SUB" by blast
qed

lemma dilated_ticks_right:
  assumes "dilating f sub r"
  shows   "{i. f m < i \<and> i \<le> f n \<and> hamlet ((Rep_run r) i c)}
          = image f {i. m < i \<and> i \<le> n \<and> hamlet ((Rep_run sub) i c)}"
    (is "?RUN = image f ?SUB")
proof
  { fix i  assume h:"i \<in> ?SUB"
    hence "m < i \<and> i \<le> n" by simp
    hence "f m < f i \<and> f i \<le> (f n)" using assms
      by (simp add: dilating_def dilating_fun_def strict_monoD strict_mono_less_eq)
    moreover from h have "hamlet ((Rep_run sub) i c)" by simp
    hence "hamlet ((Rep_run r) (f i) c)" using ticks_sub[OF assms] by blast
    ultimately have "f i \<in> ?RUN" by simp
  } thus "image f ?SUB \<subseteq> ?RUN" by blast
next
  { fix i assume h:"i \<in> ?RUN"
    hence "hamlet ((Rep_run r) i c)" by simp
    from ticks_imp_ticks_subk[OF assms this]
      obtain i\<^sub>0 where i0prop:"f i\<^sub>0 = i \<and> hamlet ((Rep_run sub) i\<^sub>0 c)" by blast
    with h have "f m < f i\<^sub>0 \<and> f i\<^sub>0 \<le> f n" by simp
    moreover have "strict_mono f" using assms dilating_def dilating_fun_def by blast
    ultimately have "m < i\<^sub>0 \<and> i\<^sub>0 \<le> n" using strict_mono_less strict_mono_less_eq by blast
    with i0prop have "\<exists>i\<^sub>0. f i\<^sub>0 = i \<and> i\<^sub>0 \<in> ?SUB" by blast
  } thus "?RUN \<subseteq> image f ?SUB" by blast
qed

lemma dilated_ticks:
  assumes "dilating f sub r"
  shows   "{i. f m \<le> i \<and> i \<le> f n \<and> hamlet ((Rep_run r) i c)}
          = image f {i. m \<le> i \<and> i \<le> n \<and> hamlet ((Rep_run sub) i c)}"
    (is "?RUN = image f ?SUB")
proof
  { fix i assume h:"i \<in> ?SUB"
    hence "m \<le> i \<and> i \<le> n" by simp
    hence "f m \<le> f i \<and> f i \<le> (f n)"
      using assms by (simp add: dilating_def dilating_fun_def strict_mono_less_eq)
    moreover from h have "hamlet ((Rep_run sub) i c)" by simp
    hence "hamlet ((Rep_run r) (f i) c)" using ticks_sub[OF assms] by blast
    ultimately have "f i \<in>?RUN" by simp
  } thus "image f ?SUB \<subseteq> ?RUN" by blast
next
  { fix i assume h:"i \<in> ?RUN"
    hence "hamlet ((Rep_run r) i c)" by simp
    from ticks_imp_ticks_subk[OF assms this]
      obtain i\<^sub>0 where i0prop:"f i\<^sub>0 = i \<and> hamlet ((Rep_run sub) i\<^sub>0 c)" by blast
    with h have "f m \<le> f i\<^sub>0 \<and> f i\<^sub>0 \<le> f n" by simp
    moreover have "strict_mono f" using assms dilating_def dilating_fun_def by blast
    ultimately have "m \<le> i\<^sub>0 \<and> i\<^sub>0 \<le> n" using strict_mono_less_eq by blast
    with i0prop have "\<exists>i\<^sub>0. f i\<^sub>0 = i \<and> i\<^sub>0 \<in> ?SUB" by blast
  } thus "?RUN \<subseteq> image f ?SUB" by blast
qed


text {*
  No tick can occur in a dilated run before the image of 0 by the dilation function.
*}
lemma empty_dilated_prefix:
  assumes "dilating f sub r"
  and     "n < f 0"
  shows   "\<not> hamlet ((Rep_run r) n c)"
proof
  { assume "hamlet ((Rep_run r) n c)"
    hence "\<exists>n\<^sub>0. f n\<^sub>0 = n" using no_tick_sub[OF assms(1)] by blast
    from this obtain n\<^sub>0 where "f n\<^sub>0 = n" by blast
    hence "f n\<^sub>0 < f 0" using assms(2) by simp
    moreover have "strict_mono f" using assms(1) dilating_def dilating_fun_def by blast
    ultimately have "n\<^sub>0 < 0" using strict_mono_less by blast
    hence False by simp
  } thus "hamlet ((Rep_run r) n c) \<Longrightarrow> False" .
qed

corollary empty_dilated_prefix':
  assumes "dilating f sub r"
  shows   "{i. f 0 \<le> i \<and> i \<le> f n \<and> hamlet ((Rep_run r) i c)} = {i. i \<le> f n \<and> hamlet ((Rep_run r) i c)}"
proof -
  from assms have "strict_mono f" using dilating_def dilating_fun_def by blast
  hence "f 0 \<le> f n" unfolding strict_mono_def by (simp add: less_mono_imp_le_mono)
  hence "\<forall>i. i \<le> f n = (i < f 0) \<or> (f 0 \<le> i \<and> i \<le> f n)" by auto
  hence "{i. i \<le> f n \<and> hamlet ((Rep_run r) i c)}
        = {i. i < f 0 \<and> hamlet ((Rep_run r) i c)} \<union> {i. f 0 \<le> i \<and> i \<le> f n \<and> hamlet ((Rep_run r) i c)}"
    by auto
  also have "... = {i. f 0 \<le> i \<and> i \<le> f n \<and> hamlet ((Rep_run r) i c)}"
     using empty_dilated_prefix[OF assms] by blast
  finally show ?thesis by simp
qed

corollary dilated_prefix:
  assumes "dilating f sub r"
  shows   "{i. i \<le> f n \<and> hamlet ((Rep_run r) i c)}
          = image f {i. i \<le> n \<and> hamlet ((Rep_run sub) i c)}"
proof -
  have "{i. 0 \<le> i \<and> i \<le> f n \<and> hamlet ((Rep_run r) i c)}
        = image f {i. 0 \<le> i \<and> i \<le> n \<and> hamlet ((Rep_run sub) i c)}"
    using dilated_ticks[OF assms] empty_dilated_prefix'[OF assms] by blast
  thus ?thesis by simp
qed

text {*
  A singleton of nat can be defined with a weaker property.
*}
lemma nat_sing_prop:
  "{i::nat. i = k \<and> P(i)} = {i::nat. i = k \<and> P(k)}"
by auto

text {*
  The set definition and the function definition of tick_count are equivalent.
*}
lemma tick_count_is_fun[code]:"tick_count r c n = run_tick_count r c n"
proof (induction n)
  case 0
    have "tick_count r c 0 = card {i. i \<le> 0 \<and> hamlet ((Rep_run r) i c)}"
      by (simp add: tick_count_def)
    also have "... = card {i::nat. i = 0 \<and> hamlet ((Rep_run r) 0 c)}"
      using le_zero_eq nat_sing_prop[of "0" "\<lambda>i. hamlet ((Rep_run r) i c)"] by simp
    also have "... = (if hamlet ((Rep_run r) 0 c) then 1 else 0)" by simp
    also have "... = run_tick_count r c 0" by simp
    finally show ?case .
next
  case (Suc k)
    show ?case
    proof (cases "hamlet ((Rep_run r) (Suc k) c)")
      case True
        hence "{i. i \<le> Suc k \<and> hamlet ((Rep_run r) i c)} = insert (Suc k) {i. i \<le> k \<and> hamlet ((Rep_run r) i c)}"
          by auto
        hence "tick_count r c (Suc k) = Suc (tick_count r c k)"
          by (simp add: tick_count_def)
        with Suc.IH have "tick_count r c (Suc k) = Suc (run_tick_count r c k)" by simp
        thus ?thesis by (simp add: True)
    next
      case False
        hence "{i. i \<le> Suc k \<and> hamlet ((Rep_run r) i c)} = {i. i \<le> k \<and> hamlet ((Rep_run r) i c)}"
          using le_Suc_eq by auto
        hence "tick_count r c (Suc k) = tick_count r c k" by (simp add: tick_count_def)
        thus ?thesis using Suc.IH by (simp add: False)
    qed
qed

text {*
  The set definition and the function definition of tick_count_strict are equivalent.
*}
lemma tick_count_strict_suc:"tick_count_strict r c (Suc n) = tick_count r c n"
  unfolding tick_count_def tick_count_strict_def using less_Suc_eq_le by auto

lemma tick_count_strict_is_fun[code]:"tick_count_strict r c n = run_tick_count_strictly r c n"
proof (cases "n = 0")
  case True
    hence "tick_count_strict r c n = 0" unfolding tick_count_strict_def by simp
    also have "... = run_tick_count_strictly r c 0" using run_tick_count_strictly.simps(1)[symmetric] .
    finally show ?thesis using True by simp
next
  case False
  from not0_implies_Suc[OF this] obtain m where *:"n = Suc m" by blast
  hence "tick_count_strict r c n = tick_count r c m" using tick_count_strict_suc by simp
  also have "... = run_tick_count r c m" using tick_count_is_fun[of "r" "c" "m"] .
  also have "... = run_tick_count_strictly r c (Suc m)" using run_tick_count_strictly.simps(2)[symmetric] .
  finally show ?thesis using * by simp
qed

lemma run_tick_count_suc:
  "run_tick_count r c (Suc n) = (if hamlet ((Rep_run r) (Suc n) c)
                                 then Suc (run_tick_count r c n)
                                 else run_tick_count r c n)"
by simp

corollary tick_count_suc:
  "tick_count r c (Suc n) = (if hamlet ((Rep_run r) (Suc n) c)
                             then Suc (tick_count r c n)
                             else tick_count r c n)"
by (simp add: tick_count_is_fun)

lemma card_suc:"card {i. i \<le> (Suc n) \<and> P i} = card {i. i \<le> n \<and> P i} + card {i. i = (Suc n) \<and> P i}"
proof -
  have "{i. i \<le> n \<and> P i} \<inter> {i. i = (Suc n) \<and> P i} = {}" by auto
  moreover have "{i. i \<le> n \<and> P i} \<union> {i. i = (Suc n) \<and> P i} = {i. i \<le> (Suc n) \<and> P i}" by auto
  moreover have "finite {i. i \<le> n \<and> P i}" by simp
  moreover have "finite {i. i = (Suc n) \<and> P i}" by simp
  ultimately show ?thesis using card_Un_disjoint[of "{i. i \<le> n \<and> P i}" "{i. i = Suc n \<and> P i}"] by simp
qed

lemma card_le_leq:
  assumes "m < n"
    shows "card {i::nat. m < i \<and> i \<le> n \<and> P i} = card {i. m < i \<and> i < n \<and> P i} + card {i. i = n \<and> P i}"
proof -
  have "{i::nat. m < i \<and> i < n \<and> P i} \<inter> {i. i = n \<and> P i} = {}" by auto
  moreover with assms have "{i::nat. m < i \<and> i < n \<and> P i} \<union> {i. i = n \<and> P i} = {i. m < i \<and> i \<le> n \<and> P i}" by auto
  moreover have "finite {i. m < i \<and> i < n \<and> P i}" by simp
  moreover have "finite {i. i = n \<and> P i}" by simp
  ultimately show ?thesis using card_Un_disjoint[of "{i. m < i \<and> i < n \<and> P i}" "{i. i = n \<and> P i}"] by simp
qed

lemma card_le_leq_0:"card {i::nat. i \<le> n \<and> P i} = card {i. i < n \<and> P i} + card {i. i = n \<and> P i}"
proof -
  have "{i::nat. i < n \<and> P i} \<inter> {i. i = n \<and> P i} = {}" by auto
  moreover have "{i. i < n \<and> P i} \<union> {i. i = n \<and> P i} = {i. i \<le> n \<and> P i}" by auto
  moreover have "finite {i. i < n \<and> P i}" by simp
  moreover have "finite {i. i = n \<and> P i}" by simp
  ultimately show ?thesis using card_Un_disjoint[of "{i. i < n \<and> P i}" "{i. i = n \<and> P i}"] by simp
qed

lemma nat_interval_union:
  assumes "m \<le> n"
    shows "{i::nat. i \<le> n \<and> P i} = {i::nat. i \<le> m \<and> P i} \<union> {i::nat. m < i \<and> i \<le> n \<and> P i}"
using assms le_cases nat_less_le by auto

lemma tick_count_fsuc:
  assumes "dilating f sub r"
  shows "tick_count r c (f (Suc n)) = tick_count r c (f n) + card {k. k = f (Suc n) \<and> hamlet ((Rep_run r) k c)}"
proof -
  from assms have *:"\<forall>k. n < k \<and> k < (Suc n) \<longrightarrow> \<not>hamlet ((Rep_run r) k c)"
    using dilating_def dilating_fun_def by linarith
  have 1:"finite {k. k \<le> f n \<and> hamlet ((Rep_run r) k c)}" by simp
  have 2:"finite {k. f n < k \<and> k \<le> f (Suc n) \<and> hamlet ((Rep_run r) k c)}" by simp
  have 3:"{k. k \<le> f n \<and> hamlet ((Rep_run r) k c)} \<inter> {k. f n < k \<and> k \<le> f (Suc n) \<and> hamlet ((Rep_run r) k c)} = {}"
    using assms dilating_def dilating_fun_def by auto
  have "strict_mono f" using assms dilating_def dilating_fun_def by blast
  hence m:"f n < f (Suc n)" by (simp add: strict_monoD)
  hence m':"f n \<le> f (Suc n)" by simp
  have 4:"{k. k \<le> f (Suc n) \<and> hamlet ((Rep_run r) k c)}
          = {k. k \<le> f n \<and> hamlet ((Rep_run r) k c)} \<union> {k. f n < k \<and> k \<le> f (Suc n) \<and> hamlet ((Rep_run r) k c)}"
    using nat_interval_union[OF m'] . 
  have 5:"\<forall>k. (f n) < k \<and> k < f (Suc n) \<longrightarrow> \<not>hamlet ((Rep_run r) k c)"
    using * dilating_def dilating_fun_def by (metis Suc_le_eq assms leD strict_mono_less)
  have "tick_count r c (f (Suc n)) = card {k. k \<le> f (Suc n) \<and> hamlet ((Rep_run r) k c)}" using tick_count_def .
  also have "... = card {k. k \<le> f n \<and> hamlet ((Rep_run r) k c)}
                 + card {k. f n < k \<and> k \<le> f (Suc n) \<and> hamlet ((Rep_run r) k c)}"
    using card_Un_disjoint[OF 1 2 3] 4 by presburger
  also have "... = tick_count r c (f n)
                + card {k. f n < k \<and> k \<le> f (Suc n) \<and> hamlet ((Rep_run r) k c)}"
    using tick_count_def[of "r" "c" "f n"] by simp
  also have "... = tick_count r c (f n)
                  + card {k. k = f (Suc n) \<and> hamlet ((Rep_run r) k c)}"
    using 5 m by (metis order_le_less)
  finally show ?thesis .
qed

lemma card_sing_prop:"card {i. i = n \<and> P i} = (if P n then 1 else 0)"
  by (smt card_empty empty_Collect_eq is_singletonI' is_singleton_altdef mem_Collect_eq)

corollary tick_count_f_suc:
  assumes "dilating f sub r"
    shows "tick_count r c (f (Suc n)) = tick_count r c (f n) + (if hamlet ((Rep_run r) (f (Suc n)) c) then 1 else 0)"
using tick_count_fsuc[OF assms] card_sing_prop[of "f (Suc n)" "\<lambda>k. hamlet ((Rep_run r) k c)"] by simp

corollary tick_count_f_suc_suc:
  assumes "dilating f sub r"
    shows "tick_count r c (f (Suc n)) = (if hamlet ((Rep_run r) (f (Suc n)) c)
                                       then Suc (tick_count r c (f n))
                                       else tick_count r c (f n))"
using tick_count_f_suc[OF assms] by simp

lemma tick_count_f_suc_sub:
  assumes "dilating f sub r"
    shows "tick_count r c (f (Suc n)) = (if hamlet ((Rep_run sub) (Suc n) c)
                                         then Suc (tick_count r c (f n))
                                         else tick_count r c (f n))"
using tick_count_f_suc_suc[OF assms] assms by (simp add: dilating_def)

lemma tick_count_sub:
  assumes "dilating f sub r"
  shows "tick_count sub c n = tick_count r c (f n)"
proof -
  have "tick_count sub c n = card {i. i \<le> n \<and> hamlet ((Rep_run sub) i c)}"
    using tick_count_def[of "sub" "c" "n"] .
  also have "... = card (image f {i. i \<le> n \<and> hamlet ((Rep_run sub) i c)})"
    using assms dilating_def dilating_injects[OF assms] by (simp add: card_image)
  also have "... = card {i. i \<le> f n \<and> hamlet ((Rep_run r) i c)}"
    using dilated_prefix[OF assms, symmetric, of "n" "c"] by simp
  also have "... = tick_count r c (f n)"
    using tick_count_def[of "r" "c" "f n"] by simp
  finally show ?thesis .
qed

corollary run_tick_count_sub:
  assumes "dilating f sub r"
  shows "run_tick_count sub c n = run_tick_count r c (f n)"
using tick_count_sub[OF assms] tick_count_is_fun by metis

lemma dil_tick_count:
  assumes "sub \<lless> r"
      and "\<forall>n. run_tick_count sub a n \<le> run_tick_count sub b n"
    shows "run_tick_count r a n \<le> run_tick_count r b n"
proof -
  from assms(1) is_subrun_def obtain f where *:"dilating f sub r" by blast
  show ?thesis
  proof (induction n)
    case 0
    from assms(2) have "tick_count sub a 0 \<le> tick_count sub b 0" using tick_count_is_fun by metis
    hence 1:"tick_count r a (f 0) \<le> tick_count r b (f 0)" using tick_count_sub[OF *] by simp
    from * dilating_def dilating_fun_def have "0 \<le> f 0" by simp
    hence "tick_count r a 0 \<le> tick_count r b 0"
    proof -
      consider (a) "0 < f 0" | (b) "0 = f 0" by linarith thus ?thesis
      proof (cases)
        case a
          from empty_dilated_prefix[OF * this] show ?thesis using tick_count_def[of "r" _ "0"]
          by (metis (mono_tags, lifting) Collect_empty_eq card.empty le_zero_eq) 
      next
        case b thus ?thesis using 1 by simp
      qed
    qed
    thus ?case by (simp add: tick_count_is_fun)
  next
    case (Suc n) 
    from assms(2) have "tick_count sub a (Suc n) \<le> tick_count sub b (Suc n)"
      using tick_count_is_fun by metis
    hence 1:"tick_count r a (f (Suc n)) \<le> tick_count r b (f (Suc n))" using tick_count_sub[OF *] by simp
    thus ?case using assms tick_count_f_suc_sub[OF *] Suc.IH
      by (smt is_subrun_def run_tick_count_sub run_tick_count_suc ticks_imp_ticks_subk)
  qed
qed

text {*
  A time relation is a stricter specification than the equivalent loose time relation.
*}
lemma tagrel_is_loose:
  shows   "\<lbrakk> time-relation \<lfloor>H\<^sub>1,H\<^sub>2\<rfloor> \<in> R \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L \<subseteq> \<lbrakk> loose time-relation \<lfloor>H\<^sub>1,H\<^sub>2\<rfloor> \<in> R \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L"
by auto


end
