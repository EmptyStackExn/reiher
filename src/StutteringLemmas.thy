subsection\<open>Stuttering Lemmas\<close>

theory StutteringLemmas

imports StutteringDefs

begin

lemma bounded_suc_ind:
  assumes \<open>\<And>k. k < m \<Longrightarrow> P (Suc (z + k)) = P (z + k)\<close>
    shows \<open>k < m \<Longrightarrow> P (Suc (z + k)) = P z\<close>
proof (induction k)
  case 0
    with assms(1)[of 0] show ?case by simp
next
  case (Suc k')
    with assms[of \<open>Suc k'\<close>] show ?case by force
qed


subsection \<open>Lemmas used to prove the invariance by stuttering\<close>

text \<open>A dilating function is injective.\<close>

lemma dilating_fun_injects:
  assumes \<open>dilating_fun f r\<close>
  shows   \<open>inj_on f A\<close>
using assms dilating_fun_def strict_mono_imp_inj_on by blast

text \<open>
  If a clock ticks at an instant in a dilated run, that instant is the image
  by the dilating function of an instant of the original run.
\<close>
lemma ticks_image:
  assumes \<open>dilating_fun f r\<close>
  and     \<open>hamlet ((Rep_run r) n c)\<close>
  shows   \<open>\<exists>n\<^sub>0. f n\<^sub>0 = n\<close>
using dilating_fun_def assms by blast

text \<open> 
  The image of the ticks in a interval by a dilating function is the interval 
  bounded by the image of the bound of the original interval.
  This is proven for all 4 kinds of intervals:  \<^verbatim>\<open>]m, n[\<close>, \<^verbatim>\<open>[m, n[\<close>, \<^verbatim>\<open>]m, n]\<close> and \<^verbatim>\<open>[m, n]\<close>.
\<close>

lemma dilating_fun_image_strict:
  assumes \<open>dilating_fun f r\<close>
  shows   \<open>{k. f m < k \<and> k < f n \<and> hamlet ((Rep_run r) k c)}
            = image f {k. m < k \<and> k < n \<and> hamlet ((Rep_run r) (f k) c)}\<close>
  (is \<open>?IMG = image f ?SET\<close>)
proof
  { fix k assume h:\<open>k \<in> ?IMG\<close>
    from h obtain k\<^sub>0 where k0prop:\<open>f k\<^sub>0 = k \<and> hamlet ((Rep_run r) (f k\<^sub>0) c)\<close>
      using ticks_image[OF assms] by blast
    with h have \<open>k \<in> image f ?SET\<close> using assms dilating_fun_def strict_mono_less by blast
  } thus \<open>?IMG \<subseteq> image f ?SET\<close> ..
next
  { fix k assume h:\<open>k \<in> image f ?SET\<close>
    from h obtain k\<^sub>0 where k0prop:\<open>k = f k\<^sub>0 \<and> k\<^sub>0 \<in> ?SET\<close> by blast
    hence \<open>k \<in> ?IMG\<close> using assms by (simp add: dilating_fun_def strict_mono_less)
  } thus \<open>image f ?SET \<subseteq> ?IMG\<close> ..
qed

lemma dilating_fun_image_left:
  assumes \<open>dilating_fun f r\<close>
  shows   \<open>{k. f m \<le> k \<and> k < f n \<and> hamlet ((Rep_run r) k c)}
          = image f {k. m \<le> k \<and> k < n \<and> hamlet ((Rep_run r) (f k) c)}\<close>
  (is \<open>?IMG = image f ?SET\<close>)
proof
  { fix k assume h:\<open>k \<in> ?IMG\<close>
    from h obtain k\<^sub>0 where k0prop:\<open>f k\<^sub>0 = k \<and> hamlet ((Rep_run r) (f k\<^sub>0) c)\<close>
      using ticks_image[OF assms] by blast
    with h have \<open>k \<in> image f ?SET\<close>
      using assms dilating_fun_def strict_mono_less strict_mono_less_eq by fastforce
  } thus \<open>?IMG \<subseteq> image f ?SET\<close> ..
next
  { fix k assume h:\<open>k \<in> image f ?SET\<close>
    from h obtain k\<^sub>0 where k0prop:\<open>k = f k\<^sub>0 \<and> k\<^sub>0 \<in> ?SET\<close> by blast
    hence \<open>k \<in> ?IMG\<close>
      using assms dilating_fun_def strict_mono_less strict_mono_less_eq by fastforce
  } thus \<open>image f ?SET \<subseteq> ?IMG\<close> ..
qed

lemma dilating_fun_image_right:
  assumes \<open>dilating_fun f r\<close>
  shows   \<open>{k. f m < k \<and> k \<le> f n \<and> hamlet ((Rep_run r) k c)}
          = image f {k. m < k \<and> k \<le> n \<and> hamlet ((Rep_run r) (f k) c)}\<close>
  (is \<open>?IMG = image f ?SET\<close>)
proof
  { fix k assume h:\<open>k \<in> ?IMG\<close>
    from h obtain k\<^sub>0 where k0prop:\<open>f k\<^sub>0 = k \<and> hamlet ((Rep_run r) (f k\<^sub>0) c)\<close>
      using ticks_image[OF assms] by blast
    with h have \<open>k \<in> image f ?SET\<close>
      using assms dilating_fun_def strict_mono_less strict_mono_less_eq by fastforce
  } thus \<open>?IMG \<subseteq> image f ?SET\<close> ..
next
  { fix k assume h:\<open>k \<in> image f ?SET\<close>
    from h obtain k\<^sub>0 where k0prop:\<open>k = f k\<^sub>0 \<and> k\<^sub>0 \<in> ?SET\<close> by blast
    hence \<open>k \<in> ?IMG\<close>
      using assms dilating_fun_def strict_mono_less strict_mono_less_eq by fastforce
  } thus \<open>image f ?SET \<subseteq> ?IMG\<close> ..
qed

lemma dilating_fun_image:
  assumes \<open>dilating_fun f r\<close>
  shows   \<open>{k. f m \<le> k \<and> k \<le> f n \<and> hamlet ((Rep_run r) k c)}
          = image f {k. m \<le> k \<and> k \<le> n \<and> hamlet ((Rep_run r) (f k) c)}\<close>
  (is \<open>?IMG = image f ?SET\<close>)
proof
  { fix k assume h:\<open>k \<in> ?IMG\<close>
    from h obtain k\<^sub>0 where k0prop:\<open>f k\<^sub>0 = k \<and> hamlet ((Rep_run r) (f k\<^sub>0) c)\<close>
      using ticks_image[OF assms] by blast
    with h have \<open>k \<in> image f ?SET\<close>
      using assms dilating_fun_def strict_mono_less_eq by blast
  } thus \<open>?IMG \<subseteq> image f ?SET\<close> ..
next
  { fix k assume h:\<open>k \<in> image f ?SET\<close>
    from h obtain k\<^sub>0 where k0prop:\<open>k = f k\<^sub>0 \<and> k\<^sub>0 \<in> ?SET\<close> by blast
    hence \<open>k \<in> ?IMG\<close> using assms by (simp add: dilating_fun_def strict_mono_less_eq)
  } thus \<open>image f ?SET \<subseteq> ?IMG\<close> ..
qed

text {*
  On any clock, the number of ticks in an interval is preserved
  by a dilating function.
*}
lemma ticks_as_often_strict:
  assumes \<open>dilating_fun f r\<close>
  shows   \<open>card {p. n < p \<and> p < m \<and> hamlet ((Rep_run r) (f p) c)}
          = card {p. f n < p \<and> p < f m \<and> hamlet ((Rep_run r) p c)}\<close>
    (is \<open>card ?SET = card ?IMG\<close>)
proof -
  from dilating_fun_injects[OF assms] have \<open>inj_on f ?SET\<close> .
  moreover have \<open>finite ?SET\<close> by simp
  from inj_on_iff_eq_card[OF this] calculation have \<open>card (image f ?SET) = card ?SET\<close> by blast
  moreover from dilating_fun_image_strict[OF assms] have \<open>?IMG = image f ?SET\<close> .
  ultimately show ?thesis by auto
qed

lemma ticks_as_often_left:
  assumes \<open>dilating_fun f r\<close>
  shows   \<open>card {p. n \<le> p \<and> p < m \<and> hamlet ((Rep_run r) (f p) c)}
          = card {p. f n \<le> p \<and> p < f m \<and> hamlet ((Rep_run r) p c)}\<close>
    (is \<open>card ?SET = card ?IMG\<close>)
proof -
  from dilating_fun_injects[OF assms] have \<open>inj_on f ?SET\<close> .
  moreover have \<open>finite ?SET\<close> by simp
  from inj_on_iff_eq_card[OF this] calculation have \<open>card (image f ?SET) = card ?SET\<close> by blast
  moreover from dilating_fun_image_left[OF assms] have \<open>?IMG = image f ?SET\<close> .
  ultimately show ?thesis by auto
qed

lemma ticks_as_often_right:
  assumes \<open>dilating_fun f r\<close>
  shows   \<open>card {p. n < p \<and> p \<le> m \<and> hamlet ((Rep_run r) (f p) c)}
          = card {p. f n < p \<and> p \<le> f m \<and> hamlet ((Rep_run r) p c)}\<close>
    (is \<open>card ?SET = card ?IMG\<close>)
proof -
  from dilating_fun_injects[OF assms] have \<open>inj_on f ?SET\<close> .
  moreover have \<open>finite ?SET\<close> by simp
  from inj_on_iff_eq_card[OF this] calculation have \<open>card (image f ?SET) = card ?SET\<close> by blast
  moreover from dilating_fun_image_right[OF assms] have \<open>?IMG = image f ?SET\<close> .
  ultimately show ?thesis by auto
qed

lemma ticks_as_often:
  assumes \<open>dilating_fun f r\<close>
  shows   \<open>card {p. n \<le> p \<and> p \<le> m \<and> hamlet ((Rep_run r) (f p) c)}
          = card {p. f n \<le> p \<and> p \<le> f m \<and> hamlet ((Rep_run r) p c)}\<close>
    (is \<open>card ?SET = card ?IMG\<close>)
proof -
  from dilating_fun_injects[OF assms] have \<open>inj_on f ?SET\<close> .
  moreover have \<open>finite ?SET\<close> by simp
  from inj_on_iff_eq_card[OF this] calculation have \<open>card (image f ?SET) = card ?SET\<close> by blast
  moreover from dilating_fun_image[OF assms] have \<open>?IMG = image f ?SET\<close> .
  ultimately show ?thesis by auto
qed

lemma dilating_injects:
  assumes \<open>dilating f sub r\<close>
  shows   \<open>inj_on f A\<close>
using assms by (simp add: dilating_def dilating_fun_def strict_mono_imp_inj_on)

text {*
  If there is a tick at instant n in a dilated run, n is necessarily the image
  of some instant in the subrun.
*}
lemma ticks_image_sub:
  assumes \<open>dilating f sub r\<close>
  and     \<open>hamlet ((Rep_run r) n c)\<close>
  shows   \<open>\<exists>n\<^sub>0. f n\<^sub>0 = n\<close>
using assms dilating_def ticks_image by metis

lemma ticks_image_sub':
  assumes \<open>dilating f sub r\<close>
  and     \<open>\<exists>c. hamlet ((Rep_run r) n c)\<close>
  shows   \<open>\<exists>n\<^sub>0. f n\<^sub>0 = n\<close>
using assms dilating_def dilating_fun_def by metis

text \<open>Time is preserved by dilation when ticks occur.\<close>

lemma ticks_tag_image:
  assumes \<open>dilating f sub r\<close>
  and     \<open>\<exists>c. hamlet ((Rep_run r) k c)\<close>
  and     \<open>time ((Rep_run r) k c) = \<tau>\<close>
  shows   \<open>\<exists>k\<^sub>0. f k\<^sub>0 = k \<and> time ((Rep_run sub) k\<^sub>0 c) = \<tau>\<close>
proof -
  from ticks_image_sub'[OF assms(1,2)] have \<open>\<exists>k\<^sub>0. f k\<^sub>0 = k\<close> .
  from this obtain k\<^sub>0 where \<open>f k\<^sub>0 = k\<close> by blast
  moreover with assms(1,3) have \<open>time ((Rep_run sub) k\<^sub>0 c) = \<tau>\<close> by (simp add: dilating_def) 
  ultimately show ?thesis by blast
qed

text \<open>TESL operators are preserved by dilation.\<close>

lemma ticks_sub:
  assumes \<open>dilating f sub r\<close>
  shows   \<open>hamlet ((Rep_run sub) n a) = hamlet ((Rep_run r) (f n) a)\<close>
using assms by (simp add: dilating_def)

lemma no_tick_sub:
  assumes \<open>dilating f sub r\<close>
  shows   \<open>(\<nexists>n\<^sub>0. f n\<^sub>0 = n) \<longrightarrow> \<not>hamlet ((Rep_run r) n a)\<close>
using assms dilating_def dilating_fun_def by blast

text \<open>Lifting a total function to a partial function on an option domain.\<close>

definition opt_lift::\<open>('a \<Rightarrow> 'a) \<Rightarrow> ('a option \<Rightarrow> 'a option)\<close>
where
  \<open>opt_lift f \<equiv> \<lambda>x. case x of None \<Rightarrow> None | Some y \<Rightarrow> Some (f y)\<close>

text {*
  The set of instants when a clock ticks in a dilated run is the image by the dilation function
  of the set of instants when it ticks in the subrun.
*}
lemma tick_set_sub:
  assumes \<open>dilating f sub r\<close>
  shows   \<open>{k. hamlet ((Rep_run r) k c)} = image f {k. hamlet ((Rep_run sub) k c)}\<close>
    (is \<open>?R = image f ?S\<close>)
proof
  { fix k assume h:\<open>k \<in> ?R\<close>
    with no_tick_sub[OF assms] have \<open>\<exists>k\<^sub>0. f k\<^sub>0 = k\<close> by blast
    from this obtain k\<^sub>0 where k0prop:\<open>f k\<^sub>0 = k\<close> by blast
    with ticks_sub[OF assms] h have \<open>hamlet ((Rep_run sub) k\<^sub>0 c)\<close> by blast
    with k0prop have \<open>k \<in> image f ?S\<close> by blast
  }
  thus \<open>?R \<subseteq> image f ?S\<close> by blast
next
  { fix k assume h:\<open>k \<in> image f ?S\<close>
    from this obtain k\<^sub>0 where \<open>f k\<^sub>0 = k \<and> hamlet ((Rep_run sub) k\<^sub>0 c)\<close> by blast
    with assms have \<open>k \<in> ?R\<close> using ticks_sub by blast 
  }
  thus \<open>image f ?S \<subseteq> ?R\<close> by blast
qed

text {*
  Strictly monotonous functions preserve the least element.
*}
lemma Least_strict_mono:
  assumes \<open>strict_mono f\<close>
  and     \<open>\<exists>x \<in> S. \<forall>y \<in> S. x \<le> y\<close>
  shows   \<open>(LEAST y. y \<in> f ` S) = f (LEAST x. x \<in> S)\<close>
using Least_mono[OF strict_mono_mono, OF assms] .

text {*
  A non empty set of @{typ nat}s has a least element.
*}
lemma Least_nat_ex:
  \<open>(n::nat) \<in> S \<Longrightarrow> \<exists>x \<in> S. (\<forall>y \<in> S. x \<le> y)\<close>
by (induction n rule: nat_less_induct, insert not_le_imp_less, blast)

text {*
  The first instant when a clock ticks in a dilated run is the image by the dilation
  function of the first instant when it ticks in the subrun.
*}
lemma Least_sub:
  assumes \<open>dilating f sub r\<close>
  and     \<open>\<exists>k::nat. hamlet ((Rep_run sub) k c)\<close>
  shows   \<open>(LEAST k. k \<in> {t. hamlet ((Rep_run r) t c)}) = f (LEAST k. k \<in> {t. hamlet ((Rep_run sub) t c)})\<close>
          (is \<open>(LEAST k. k \<in> ?R) = f (LEAST k. k \<in> ?S)\<close>)
proof -
  from assms(2) have \<open>\<exists>x. x \<in> ?S\<close> by simp
  hence least:\<open>\<exists>x \<in> ?S. \<forall>y \<in> ?S. x \<le> y\<close>
    using Least_nat_ex ..
  from assms(1) have \<open>strict_mono f\<close> by (simp add: dilating_def dilating_fun_def)
  from Least_strict_mono[OF this least] have
    \<open>(LEAST y. y \<in> f ` ?S)  = f (LEAST x. x \<in> ?S)\<close> .
  with tick_set_sub[OF assms(1), of \<open>c\<close>] show ?thesis by auto
qed

text {*
  If a clock ticks in a run, it ticks in the subrun.
*}
lemma ticks_imp_ticks_sub:
  assumes \<open>dilating f sub r\<close>
  and     \<open>\<exists>k. hamlet ((Rep_run r) k c)\<close>
  shows   \<open>\<exists>k\<^sub>0. hamlet ((Rep_run sub) k\<^sub>0 c)\<close>
proof -
  from assms(2) obtain k where \<open>hamlet ((Rep_run r) k c)\<close> by blast
  with ticks_image_sub[OF assms(1)] ticks_sub[OF assms(1)] show ?thesis by blast
qed

text {*
  Stronger version: it ticks in the subrun and we know when.
*}
lemma ticks_imp_ticks_subk:
  assumes \<open>dilating f sub r\<close>
  and     \<open>hamlet ((Rep_run r) k c)\<close>
  shows   \<open>\<exists>k\<^sub>0. f k\<^sub>0 = k \<and> hamlet ((Rep_run sub) k\<^sub>0 c)\<close>
proof -
  from no_tick_sub[OF assms(1)] assms(2) have \<open>\<exists>k\<^sub>0. f k\<^sub>0 = k\<close> by blast
  from this obtain k\<^sub>0 where \<open>f k\<^sub>0 = k\<close> by blast
  moreover with ticks_sub[OF assms(1)] assms(2) have \<open>hamlet ((Rep_run sub) k\<^sub>0 c)\<close> by blast
  ultimately show ?thesis by blast
qed

text {*
  A dilating function preserves the tick count on an interval for any clock.
*}
lemma dilated_ticks_strict:
  assumes \<open>dilating f sub r\<close>
  shows   \<open>{i. f m < i \<and> i < f n \<and> hamlet ((Rep_run r) i c)}
          = image f {i. m < i \<and> i < n \<and> hamlet ((Rep_run sub) i c)}\<close>
    (is \<open>?RUN = image f ?SUB\<close>)
proof
  { fix i assume h:\<open>i \<in> ?SUB\<close>
    hence \<open>m < i \<and> i < n\<close> by simp
    hence \<open>f m < f i \<and> f i < (f n)\<close> using assms
      by (simp add: dilating_def dilating_fun_def strict_monoD strict_mono_less_eq)
    moreover from h have \<open>hamlet ((Rep_run sub) i c)\<close> by simp
    hence \<open>hamlet ((Rep_run r) (f i) c)\<close> using ticks_sub[OF assms] by blast
    ultimately have \<open>f i \<in> ?RUN\<close> by simp
  } thus \<open>image f ?SUB \<subseteq> ?RUN\<close> by blast
next
  { fix i assume h:\<open>i \<in> ?RUN\<close>
    hence \<open>hamlet ((Rep_run r) i c)\<close> by simp
    from ticks_imp_ticks_subk[OF assms this]
      obtain i\<^sub>0 where i0prop:\<open>f i\<^sub>0 = i \<and> hamlet ((Rep_run sub) i\<^sub>0 c)\<close> by blast
    with h have \<open>f m < f i\<^sub>0 \<and> f i\<^sub>0 < f n\<close> by simp
    moreover have \<open>strict_mono f\<close> using assms dilating_def dilating_fun_def by blast
    ultimately have \<open>m < i\<^sub>0 \<and> i\<^sub>0 < n\<close> using strict_mono_less strict_mono_less_eq by blast
    with i0prop have \<open>\<exists>i\<^sub>0. f i\<^sub>0 = i \<and> i\<^sub>0 \<in> ?SUB\<close> by blast
  } thus \<open>?RUN \<subseteq> image f ?SUB\<close> by blast
qed

lemma dilated_ticks_left:
  assumes \<open>dilating f sub r\<close>
  shows   \<open>{i. f m \<le> i \<and> i < f n \<and> hamlet ((Rep_run r) i c)}
          = image f {i. m \<le> i \<and> i < n \<and> hamlet ((Rep_run sub) i c)}\<close>
    (is \<open>?RUN = image f ?SUB\<close>)
proof
  { fix i assume h:\<open>i \<in> ?SUB\<close>
    hence \<open>m \<le> i \<and> i < n\<close> by simp
    hence \<open>f m \<le> f i \<and> f i < (f n)\<close> using assms
      by (simp add: dilating_def dilating_fun_def strict_monoD strict_mono_less_eq)
    moreover from h have \<open>hamlet ((Rep_run sub) i c)\<close> by simp
    hence \<open>hamlet ((Rep_run r) (f i) c)\<close> using ticks_sub[OF assms] by blast
    ultimately have \<open>f i \<in> ?RUN\<close> by simp
  } thus \<open>image f ?SUB \<subseteq> ?RUN\<close> by blast
next
  { fix i assume h:\<open>i \<in> ?RUN\<close>
    hence \<open>hamlet ((Rep_run r) i c)\<close> by simp
    from ticks_imp_ticks_subk[OF assms this]
      obtain i\<^sub>0 where i0prop:\<open>f i\<^sub>0 = i \<and> hamlet ((Rep_run sub) i\<^sub>0 c)\<close> by blast
    with h have \<open>f m \<le> f i\<^sub>0 \<and> f i\<^sub>0 < f n\<close> by simp
    moreover have \<open>strict_mono f\<close> using assms dilating_def dilating_fun_def by blast
    ultimately have \<open>m \<le> i\<^sub>0 \<and> i\<^sub>0 < n\<close> using strict_mono_less strict_mono_less_eq by blast
    with i0prop have \<open>\<exists>i\<^sub>0. f i\<^sub>0 = i \<and> i\<^sub>0 \<in> ?SUB\<close> by blast
  } thus \<open>?RUN \<subseteq> image f ?SUB\<close> by blast
qed

lemma dilated_ticks_right:
  assumes \<open>dilating f sub r\<close>
  shows   \<open>{i. f m < i \<and> i \<le> f n \<and> hamlet ((Rep_run r) i c)}
          = image f {i. m < i \<and> i \<le> n \<and> hamlet ((Rep_run sub) i c)}\<close>
    (is \<open>?RUN = image f ?SUB\<close>)
proof
  { fix i  assume h:\<open>i \<in> ?SUB\<close>
    hence \<open>m < i \<and> i \<le> n\<close> by simp
    hence \<open>f m < f i \<and> f i \<le> (f n)\<close> using assms
      by (simp add: dilating_def dilating_fun_def strict_monoD strict_mono_less_eq)
    moreover from h have \<open>hamlet ((Rep_run sub) i c)\<close> by simp
    hence \<open>hamlet ((Rep_run r) (f i) c)\<close> using ticks_sub[OF assms] by blast
    ultimately have \<open>f i \<in> ?RUN\<close> by simp
  } thus \<open>image f ?SUB \<subseteq> ?RUN\<close> by blast
next
  { fix i assume h:\<open>i \<in> ?RUN\<close>
    hence \<open>hamlet ((Rep_run r) i c)\<close> by simp
    from ticks_imp_ticks_subk[OF assms this]
      obtain i\<^sub>0 where i0prop:\<open>f i\<^sub>0 = i \<and> hamlet ((Rep_run sub) i\<^sub>0 c)\<close> by blast
    with h have \<open>f m < f i\<^sub>0 \<and> f i\<^sub>0 \<le> f n\<close> by simp
    moreover have \<open>strict_mono f\<close> using assms dilating_def dilating_fun_def by blast
    ultimately have \<open>m < i\<^sub>0 \<and> i\<^sub>0 \<le> n\<close> using strict_mono_less strict_mono_less_eq by blast
    with i0prop have \<open>\<exists>i\<^sub>0. f i\<^sub>0 = i \<and> i\<^sub>0 \<in> ?SUB\<close> by blast
  } thus \<open>?RUN \<subseteq> image f ?SUB\<close> by blast
qed

lemma dilated_ticks:
  assumes \<open>dilating f sub r\<close>
  shows   \<open>{i. f m \<le> i \<and> i \<le> f n \<and> hamlet ((Rep_run r) i c)}
          = image f {i. m \<le> i \<and> i \<le> n \<and> hamlet ((Rep_run sub) i c)}\<close>
    (is \<open>?RUN = image f ?SUB\<close>)
proof
  { fix i assume h:\<open>i \<in> ?SUB\<close>
    hence \<open>m \<le> i \<and> i \<le> n\<close> by simp
    hence \<open>f m \<le> f i \<and> f i \<le> (f n)\<close>
      using assms by (simp add: dilating_def dilating_fun_def strict_mono_less_eq)
    moreover from h have \<open>hamlet ((Rep_run sub) i c)\<close> by simp
    hence \<open>hamlet ((Rep_run r) (f i) c)\<close> using ticks_sub[OF assms] by blast
    ultimately have \<open>f i \<in>?RUN\<close> by simp
  } thus \<open>image f ?SUB \<subseteq> ?RUN\<close> by blast
next
  { fix i assume h:\<open>i \<in> ?RUN\<close>
    hence \<open>hamlet ((Rep_run r) i c)\<close> by simp
    from ticks_imp_ticks_subk[OF assms this]
      obtain i\<^sub>0 where i0prop:\<open>f i\<^sub>0 = i \<and> hamlet ((Rep_run sub) i\<^sub>0 c)\<close> by blast
    with h have \<open>f m \<le> f i\<^sub>0 \<and> f i\<^sub>0 \<le> f n\<close> by simp
    moreover have \<open>strict_mono f\<close> using assms dilating_def dilating_fun_def by blast
    ultimately have \<open>m \<le> i\<^sub>0 \<and> i\<^sub>0 \<le> n\<close> using strict_mono_less_eq by blast
    with i0prop have \<open>\<exists>i\<^sub>0. f i\<^sub>0 = i \<and> i\<^sub>0 \<in> ?SUB\<close> by blast
  } thus \<open>?RUN \<subseteq> image f ?SUB\<close> by blast
qed


text \<open>No tick can occur in a dilated run before the image of 0 by the dilation function. \<close>

lemma empty_dilated_prefix:
  assumes \<open>dilating f sub r\<close>
  and     \<open>n < f 0\<close>
shows   \<open>\<not> hamlet ((Rep_run r) n c)\<close>
proof - (* This one is easy with the new definition of a dilating function. *)
  from assms have False by (simp add: dilating_def dilating_fun_def)
  thus ?thesis ..
qed

corollary empty_dilated_prefix':
  assumes \<open>dilating f sub r\<close>
  shows   \<open>{i. f 0 \<le> i \<and> i \<le> f n \<and> hamlet ((Rep_run r) i c)} = {i. i \<le> f n \<and> hamlet ((Rep_run r) i c)}\<close>
proof -
  from assms have \<open>strict_mono f\<close> by (simp add: dilating_def dilating_fun_def)
  hence \<open>f 0 \<le> f n\<close> unfolding strict_mono_def by (simp add: less_mono_imp_le_mono)
  hence \<open>\<forall>i. i \<le> f n = (i < f 0) \<or> (f 0 \<le> i \<and> i \<le> f n)\<close> by auto
  hence \<open>{i. i \<le> f n \<and> hamlet ((Rep_run r) i c)}
        = {i. i < f 0 \<and> hamlet ((Rep_run r) i c)} \<union> {i. f 0 \<le> i \<and> i \<le> f n \<and> hamlet ((Rep_run r) i c)}\<close>
    by auto
  also have \<open>... = {i. f 0 \<le> i \<and> i \<le> f n \<and> hamlet ((Rep_run r) i c)}\<close>
     using empty_dilated_prefix[OF assms] by blast
  finally show ?thesis by simp
qed

corollary dilated_prefix:
  assumes \<open>dilating f sub r\<close>
  shows   \<open>{i. i \<le> f n \<and> hamlet ((Rep_run r) i c)}
          = image f {i. i \<le> n \<and> hamlet ((Rep_run sub) i c)}\<close>
proof -
  have \<open>{i. 0 \<le> i \<and> i \<le> f n \<and> hamlet ((Rep_run r) i c)}
        = image f {i. 0 \<le> i \<and> i \<le> n \<and> hamlet ((Rep_run sub) i c)}\<close>
    using dilated_ticks[OF assms] empty_dilated_prefix'[OF assms] by blast
  thus ?thesis by simp
qed

corollary dilated_strict_prefix:
  assumes \<open>dilating f sub r\<close>
  shows   \<open>{i. i < f n \<and> hamlet ((Rep_run r) i c)}
          = image f {i. i < n \<and> hamlet ((Rep_run sub) i c)}\<close>
proof -
  from assms have \<open>dilating_fun f r\<close> unfolding dilating_def by simp
  from dilating_fun_image_left[OF this, of \<open>0\<close> \<open>n\<close> \<open>c\<close>]
  have \<open>{i. f 0 \<le> i \<and> i < f n \<and> hamlet ((Rep_run r) i c)}
        = image f {i. 0 \<le> i \<and> i < n \<and> hamlet ((Rep_run r) (f i) c)}\<close> .
  also have \<open>... = image f {i. 0 \<le> i \<and> i < n \<and> hamlet ((Rep_run sub) i c)}\<close>
    using assms dilating_def by blast
  finally show ?thesis
    by (metis (mono_tags, lifting) Collect_cong assms empty_dilated_prefix le0 not_le_imp_less)
qed

text\<open>A singleton of @{typ nat} can be defined with a weaker property.\<close> 
lemma nat_sing_prop:
  \<open>{i::nat. i = k \<and> P(i)} = {i::nat. i = k \<and> P(k)}\<close>
by auto

text \<open>The set definition and the function definition of @{const tick_count} are equivalent.\<close>
lemma tick_count_is_fun[code]:\<open>tick_count r c n = run_tick_count r c n\<close>
proof (induction n)
  case 0
    have \<open>tick_count r c 0 = card {i. i \<le> 0 \<and> hamlet ((Rep_run r) i c)}\<close>
      by (simp add: tick_count_def)
    also have \<open>... = card {i::nat. i = 0 \<and> hamlet ((Rep_run r) 0 c)}\<close>
      using le_zero_eq nat_sing_prop[of \<open>0\<close> \<open>\<lambda>i. hamlet ((Rep_run r) i c)\<close>] by simp
    also have \<open>... = (if hamlet ((Rep_run r) 0 c) then 1 else 0)\<close> by simp
    also have \<open>... = run_tick_count r c 0\<close> by simp
    finally show ?case .
next
  case (Suc k)
    show ?case
    proof (cases \<open>hamlet ((Rep_run r) (Suc k) c)\<close>)
      case True
        hence \<open>{i. i \<le> Suc k \<and> hamlet ((Rep_run r) i c)} = insert (Suc k) {i. i \<le> k \<and> hamlet ((Rep_run r) i c)}\<close>
          by auto
        hence \<open>tick_count r c (Suc k) = Suc (tick_count r c k)\<close>
          by (simp add: tick_count_def)
        with Suc.IH have \<open>tick_count r c (Suc k) = Suc (run_tick_count r c k)\<close> by simp
        thus ?thesis by (simp add: True)
    next
      case False
        hence \<open>{i. i \<le> Suc k \<and> hamlet ((Rep_run r) i c)} = {i. i \<le> k \<and> hamlet ((Rep_run r) i c)}\<close>
          using le_Suc_eq by auto
        hence \<open>tick_count r c (Suc k) = tick_count r c k\<close> by (simp add: tick_count_def)
        thus ?thesis using Suc.IH by (simp add: False)
    qed
qed

text\<open>The set definition and the function definition of @{const tick_count_strict}  are equivalent.\<close> 
lemma tick_count_strict_suc:\<open>tick_count_strict r c (Suc n) = tick_count r c n\<close>
  unfolding tick_count_def tick_count_strict_def using less_Suc_eq_le by auto

lemma tick_count_strict_is_fun[code]:\<open>tick_count_strict r c n = run_tick_count_strictly r c n\<close>
proof (cases \<open>n = 0\<close>)
  case True
    hence \<open>tick_count_strict r c n = 0\<close> unfolding tick_count_strict_def by simp
    also have \<open>... = run_tick_count_strictly r c 0\<close> using run_tick_count_strictly.simps(1)[symmetric] .
    finally show ?thesis using True by simp
next
  case False
  from not0_implies_Suc[OF this] obtain m where *:\<open>n = Suc m\<close> by blast
  hence \<open>tick_count_strict r c n = tick_count r c m\<close> using tick_count_strict_suc by simp
  also have \<open>... = run_tick_count r c m\<close> using tick_count_is_fun[of \<open>r\<close> \<open>c\<close> \<open>m\<close>] .
  also have \<open>... = run_tick_count_strictly r c (Suc m)\<close> using run_tick_count_strictly.simps(2)[symmetric] .
  finally show ?thesis using * by simp
qed

lemma strictly_precedes_alt_def1:
  \<open>{ \<rho>. \<forall>n::nat. (run_tick_count \<rho> K\<^sub>2 n) \<le> (run_tick_count_strictly \<rho> K\<^sub>1 n) }
 = { \<rho>. \<forall>n::nat. (run_tick_count_strictly \<rho> K\<^sub>2 (Suc n)) \<le> (run_tick_count_strictly \<rho> K\<^sub>1 n) }\<close>
  using tick_count_is_fun tick_count_strict_suc tick_count_strict_is_fun by metis

lemma strictly_precedes_alt_def2:
  \<open>{ \<rho>. \<forall>n::nat. (run_tick_count \<rho> K\<^sub>2 n) \<le> (run_tick_count_strictly \<rho> K\<^sub>1 n) }
 = { \<rho>. (\<not>hamlet ((Rep_run \<rho>) 0 K\<^sub>2)) \<and> (\<forall>n::nat. (run_tick_count \<rho> K\<^sub>2 (Suc n)) \<le> (run_tick_count \<rho> K\<^sub>1 n)) }\<close>
  (is \<open>?P = ?P'\<close>)
proof
  { fix r::\<open>'a run\<close>
    assume \<open>r \<in> ?P\<close>
    hence \<open>\<forall>n::nat. (run_tick_count r K\<^sub>2 n) \<le> (run_tick_count_strictly r K\<^sub>1 n)\<close> by simp
    hence 1:\<open>\<forall>n::nat. (tick_count r K\<^sub>2 n) \<le> (tick_count_strict r K\<^sub>1 n)\<close>
      using tick_count_is_fun[symmetric, of r] tick_count_strict_is_fun[symmetric, of r] by simp
    hence \<open>\<forall>n::nat. (tick_count_strict r K\<^sub>2 (Suc n)) \<le> (tick_count_strict r K\<^sub>1 n)\<close>
      using tick_count_strict_suc[symmetric, of \<open>r\<close> \<open>K\<^sub>2\<close>] by simp
    hence \<open>\<forall>n::nat. (tick_count_strict r K\<^sub>2 (Suc (Suc n))) \<le> (tick_count_strict r K\<^sub>1 (Suc n))\<close> by simp
    hence \<open>\<forall>n::nat. (tick_count r K\<^sub>2 (Suc n)) \<le> (tick_count r K\<^sub>1 n)\<close>
      using tick_count_strict_suc[symmetric, of \<open>r\<close>] by simp
    hence *:\<open>\<forall>n::nat. (run_tick_count r K\<^sub>2 (Suc n)) \<le> (run_tick_count r K\<^sub>1 n)\<close>
      by (simp add: tick_count_is_fun)
    have \<open>tick_count_strict r K\<^sub>1 0 = 0\<close> unfolding tick_count_strict_def by simp
    with 1 have \<open>tick_count r K\<^sub>2 0 = 0\<close> by (metis le_zero_eq)
    hence \<open>\<not>hamlet ((Rep_run r) 0 K\<^sub>2)\<close> unfolding tick_count_def by auto
    with * have \<open>r \<in> ?P'\<close> by simp
  } thus \<open>?P \<subseteq> ?P'\<close> ..
  { fix r::\<open>'a run\<close>
    assume h:\<open>r \<in> ?P'\<close>
    hence \<open>\<forall>n::nat. (run_tick_count r K\<^sub>2 (Suc n)) \<le> (run_tick_count r K\<^sub>1 n)\<close> by simp
    hence \<open>\<forall>n::nat. (tick_count r K\<^sub>2 (Suc n)) \<le> (tick_count r K\<^sub>1 n)\<close>
      using tick_count_is_fun[symmetric, of \<open>r\<close>] by metis
    hence \<open>\<forall>n::nat. (tick_count r K\<^sub>2 (Suc n)) \<le> (tick_count_strict r K\<^sub>1 (Suc n))\<close>
      using tick_count_strict_suc[symmetric, of \<open>r\<close> \<open>K\<^sub>1\<close>] by simp
    hence *:\<open>\<forall>n. n > 0 \<longrightarrow> (tick_count r K\<^sub>2 n) \<le> (tick_count_strict r K\<^sub>1 n)\<close>
      using gr0_implies_Suc by blast
    have \<open>tick_count_strict r K\<^sub>1 0 = 0\<close> unfolding tick_count_strict_def by simp
    moreover from h have \<open>\<not>hamlet ((Rep_run r) 0 K\<^sub>2)\<close> by simp
    hence \<open>tick_count r K\<^sub>2 0 = 0\<close> unfolding tick_count_def by auto
    ultimately have \<open>tick_count r K\<^sub>2 0 \<le> tick_count_strict r K\<^sub>1 0\<close> by simp
    with * have \<open>\<forall>n. (tick_count r K\<^sub>2 n) \<le> (tick_count_strict r K\<^sub>1 n)\<close> by (metis gr0I)
    hence \<open>\<forall>n. (run_tick_count r K\<^sub>2 n) \<le> (run_tick_count_strictly r K\<^sub>1 n)\<close>
      using tick_count_is_fun tick_count_strict_is_fun by metis
    hence \<open>r \<in> ?P\<close> ..
  } thus \<open>?P' \<subseteq> ?P\<close> ..
qed

lemma run_tick_count_suc:
  \<open>run_tick_count r c (Suc n) = (if hamlet ((Rep_run r) (Suc n) c)
                                 then Suc (run_tick_count r c n)
                                 else run_tick_count r c n)\<close>
by simp

corollary tick_count_suc:
  \<open>tick_count r c (Suc n) = (if hamlet ((Rep_run r) (Suc n) c)
                             then Suc (tick_count r c n)
                             else tick_count r c n)\<close>
by (simp add: tick_count_is_fun)

lemma card_suc:\<open>card {i. i \<le> (Suc n) \<and> P i} = card {i. i \<le> n \<and> P i} + card {i. i = (Suc n) \<and> P i}\<close>
proof -
  have \<open>{i. i \<le> n \<and> P i} \<inter> {i. i = (Suc n) \<and> P i} = {}\<close> by auto
  moreover have \<open>{i. i \<le> n \<and> P i} \<union> {i. i = (Suc n) \<and> P i} = {i. i \<le> (Suc n) \<and> P i}\<close> by auto
  moreover have \<open>finite {i. i \<le> n \<and> P i}\<close> by simp
  moreover have \<open>finite {i. i = (Suc n) \<and> P i}\<close> by simp
  ultimately show ?thesis using card_Un_disjoint[of \<open>{i. i \<le> n \<and> P i}\<close> \<open>{i. i = Suc n \<and> P i}\<close>] by simp
qed

lemma card_le_leq:
  assumes \<open>m < n\<close>
    shows \<open>card {i::nat. m < i \<and> i \<le> n \<and> P i} = card {i. m < i \<and> i < n \<and> P i} + card {i. i = n \<and> P i}\<close>
proof -
  have \<open>{i::nat. m < i \<and> i < n \<and> P i} \<inter> {i. i = n \<and> P i} = {}\<close> by auto
  moreover with assms have \<open>{i::nat. m < i \<and> i < n \<and> P i} \<union> {i. i = n \<and> P i} = {i. m < i \<and> i \<le> n \<and> P i}\<close> by auto
  moreover have \<open>finite {i. m < i \<and> i < n \<and> P i}\<close> by simp
  moreover have \<open>finite {i. i = n \<and> P i}\<close> by simp
  ultimately show ?thesis using card_Un_disjoint[of \<open>{i. m < i \<and> i < n \<and> P i}\<close> \<open>{i. i = n \<and> P i}\<close>] by simp
qed

lemma card_le_leq_0:\<open>card {i::nat. i \<le> n \<and> P i} = card {i. i < n \<and> P i} + card {i. i = n \<and> P i}\<close>
proof -
  have \<open>{i::nat. i < n \<and> P i} \<inter> {i. i = n \<and> P i} = {}\<close> by auto
  moreover have \<open>{i. i < n \<and> P i} \<union> {i. i = n \<and> P i} = {i. i \<le> n \<and> P i}\<close> by auto
  moreover have \<open>finite {i. i < n \<and> P i}\<close> by simp
  moreover have \<open>finite {i. i = n \<and> P i}\<close> by simp
  ultimately show ?thesis using card_Un_disjoint[of \<open>{i. i < n \<and> P i}\<close> \<open>{i. i = n \<and> P i}\<close>] by simp
qed

lemma card_mnm:
  assumes \<open>m < n\<close>
    shows \<open>card {i::nat. i < n \<and> P i} = card {i. i \<le> m \<and> P i} + card {i. m < i \<and> i < n \<and> P i}\<close>
proof -
  have 1:\<open>{i::nat. i \<le> m \<and> P i} \<inter> {i. m < i \<and> i < n \<and> P i} = {}\<close> by auto
  from assms have \<open>\<forall>i::nat. i < n = (i \<le> m) \<or> (m < i \<and> i < n)\<close>  using less_trans by auto
  hence 2:
    \<open>{i::nat. i < n \<and> P i} = {i. i \<le> m \<and> P i} \<union> {i. m < i \<and> i < n \<and> P i}\<close> by blast
  have 3:\<open>finite {i. i \<le> m \<and> P i}\<close> by simp
  have 4:\<open>finite {i. m < i \<and> i < n \<and> P i}\<close> by simp
  from card_Un_disjoint[OF 3 4 1] 2 show ?thesis by simp
qed


lemma nat_interval_union:
  assumes \<open>m \<le> n\<close>
    shows \<open>{i::nat. i \<le> n \<and> P i} = {i::nat. i \<le> m \<and> P i} \<union> {i::nat. m < i \<and> i \<le> n \<and> P i}\<close>
using assms le_cases nat_less_le by auto

lemma tick_count_fsuc:
  assumes \<open>dilating f sub r\<close>
  shows \<open>tick_count r c (f (Suc n)) = tick_count r c (f n) + card {k. k = f (Suc n) \<and> hamlet ((Rep_run r) k c)}\<close>
proof -
  from assms have *:\<open>\<forall>k. n < k \<and> k < (Suc n) \<longrightarrow> \<not>hamlet ((Rep_run r) k c)\<close>
    using dilating_def dilating_fun_def by linarith
  have 1:\<open>finite {k. k \<le> f n \<and> hamlet ((Rep_run r) k c)}\<close> by simp
  have 2:\<open>finite {k. f n < k \<and> k \<le> f (Suc n) \<and> hamlet ((Rep_run r) k c)}\<close> by simp
  have 3:\<open>{k. k \<le> f n \<and> hamlet ((Rep_run r) k c)} \<inter> {k. f n < k \<and> k \<le> f (Suc n) \<and> hamlet ((Rep_run r) k c)} = {}\<close>
    using assms dilating_def dilating_fun_def by auto
  have \<open>strict_mono f\<close> using assms dilating_def dilating_fun_def by blast
  hence m:\<open>f n < f (Suc n)\<close> by (simp add: strict_monoD)
  hence m':\<open>f n \<le> f (Suc n)\<close> by simp
  have 4:\<open>{k. k \<le> f (Suc n) \<and> hamlet ((Rep_run r) k c)}
          = {k. k \<le> f n \<and> hamlet ((Rep_run r) k c)} \<union> {k. f n < k \<and> k \<le> f (Suc n) \<and> hamlet ((Rep_run r) k c)}\<close>
    using nat_interval_union[OF m'] . 
  have 5:\<open>\<forall>k. (f n) < k \<and> k < f (Suc n) \<longrightarrow> \<not>hamlet ((Rep_run r) k c)\<close>
    using * dilating_def dilating_fun_def by (metis Suc_le_eq assms leD strict_mono_less)
  have \<open>tick_count r c (f (Suc n)) = card {k. k \<le> f (Suc n) \<and> hamlet ((Rep_run r) k c)}\<close> using tick_count_def .
  also have \<open>... = card {k. k \<le> f n \<and> hamlet ((Rep_run r) k c)}
                 + card {k. f n < k \<and> k \<le> f (Suc n) \<and> hamlet ((Rep_run r) k c)}\<close>
    using card_Un_disjoint[OF 1 2 3] 4 by presburger
  also have \<open>... = tick_count r c (f n)
                + card {k. f n < k \<and> k \<le> f (Suc n) \<and> hamlet ((Rep_run r) k c)}\<close>
    using tick_count_def[of \<open>r\<close> \<open>c\<close> \<open>f n\<close>] by simp
  also have \<open>... = tick_count r c (f n)
                  + card {k. k = f (Suc n) \<and> hamlet ((Rep_run r) k c)}\<close>
    using 5 m by (metis order_le_less)
  finally show ?thesis .
qed

lemma card_sing_prop:\<open>card {i. i = n \<and> P i} = (if P n then 1 else 0)\<close>
proof (cases \<open>P n\<close>)
  case True
    hence \<open>{i. i = n \<and> P i} = {n}\<close> by (simp add: Collect_conv_if)
    with \<open>P n\<close> show ?thesis by simp
next
  case False
    hence \<open>{i. i = n \<and> P i} = {}\<close> by (simp add: Collect_conv_if)
    with \<open>\<not>P n\<close> show ?thesis by simp
qed

corollary tick_count_f_suc:
  assumes \<open>dilating f sub r\<close>
    shows \<open>tick_count r c (f (Suc n)) = tick_count r c (f n) + (if hamlet ((Rep_run r) (f (Suc n)) c) then 1 else 0)\<close>
using tick_count_fsuc[OF assms] card_sing_prop[of \<open>f (Suc n)\<close> \<open>\<lambda>k. hamlet ((Rep_run r) k c)\<close>] by simp

corollary tick_count_f_suc_suc:
  assumes \<open>dilating f sub r\<close>
    shows \<open>tick_count r c (f (Suc n)) = (if hamlet ((Rep_run r) (f (Suc n)) c)
                                       then Suc (tick_count r c (f n))
                                       else tick_count r c (f n))\<close>
using tick_count_f_suc[OF assms] by simp

lemma tick_count_f_suc_sub:
  assumes \<open>dilating f sub r\<close>
    shows \<open>tick_count r c (f (Suc n)) = (if hamlet ((Rep_run sub) (Suc n) c)
                                         then Suc (tick_count r c (f n))
                                         else tick_count r c (f n))\<close>
using tick_count_f_suc_suc[OF assms] assms by (simp add: dilating_def)

lemma tick_count_sub:
  assumes \<open>dilating f sub r\<close>
  shows \<open>tick_count sub c n = tick_count r c (f n)\<close>
proof -
  have \<open>tick_count sub c n = card {i. i \<le> n \<and> hamlet ((Rep_run sub) i c)}\<close>
    using tick_count_def[of \<open>sub\<close> \<open>c\<close> \<open>n\<close>] .
  also have \<open>... = card (image f {i. i \<le> n \<and> hamlet ((Rep_run sub) i c)})\<close>
    using assms dilating_def dilating_injects[OF assms] by (simp add: card_image)
  also have \<open>... = card {i. i \<le> f n \<and> hamlet ((Rep_run r) i c)}\<close>
    using dilated_prefix[OF assms, symmetric, of \<open>n\<close> \<open>c\<close>] by simp
  also have \<open>... = tick_count r c (f n)\<close>
    using tick_count_def[of \<open>r\<close> \<open>c\<close> \<open>f n\<close>] by simp
  finally show ?thesis .
qed

corollary run_tick_count_sub:
  assumes \<open>dilating f sub r\<close>
  shows \<open>run_tick_count sub c n = run_tick_count r c (f n)\<close>
using tick_count_sub[OF assms] tick_count_is_fun by metis

lemma tick_count_strict_0:
  assumes \<open>dilating f sub r\<close>
    shows \<open>tick_count_strict r c (f 0) = 0\<close>
by (metis (no_types, lifting) Collect_empty_eq assms card.empty empty_dilated_prefix tick_count_strict_def)

lemma no_tick_before_suc:
  assumes \<open>dilating f sub r\<close>
      and \<open>(f n) < k \<and> k < (f (Suc n))\<close>
    shows \<open>\<not>hamlet ((Rep_run r) k c)\<close>
by (metis assms dilating_def dilating_fun_def not_less_eq strict_mono_less)

lemma tick_count_latest:
  assumes \<open>dilating f sub r\<close>
      and \<open>f n\<^sub>p < n \<and> (\<forall>k. f n\<^sub>p < k \<and> k \<le> n \<longrightarrow> (\<nexists>k\<^sub>0. f k\<^sub>0 = k))\<close>
    shows \<open>tick_count r c n = tick_count r c (f n\<^sub>p)\<close>
proof -
  have union:\<open>{i. i \<le> n \<and> hamlet ((Rep_run r) i c)} =
          {i. i \<le> f n\<^sub>p \<and> hamlet ((Rep_run r) i c)}
        \<union> {i. f n\<^sub>p < i \<and> i \<le> n \<and> hamlet ((Rep_run r) i c)}\<close> using assms(2) by auto
  have partition: \<open>{i. i \<le> f n\<^sub>p \<and> hamlet ((Rep_run r) i c)}
        \<inter> {i. f n\<^sub>p < i \<and> i \<le> n \<and> hamlet ((Rep_run r) i c)} = {}\<close>
    by (simp add: disjoint_iff_not_equal)
  from assms have \<open>{i. f n\<^sub>p < i \<and> i \<le> n \<and> hamlet ((Rep_run r) i c)} = {}\<close>
    using no_tick_sub by fastforce
  with union and partition show ?thesis by (simp add: tick_count_def)
qed

lemma tick_count_strict_stable:
  assumes \<open>dilating f sub r\<close>
  assumes \<open>(f n) < k \<and> k < (f (Suc n))\<close>
    shows \<open>tick_count_strict r c k = tick_count_strict r c (f (Suc n))\<close>
proof -
  have \<open>tick_count_strict r c k = card {i. i < k \<and> hamlet ((Rep_run r) i c)}\<close>
    using tick_count_strict_def[of \<open>r\<close> \<open>c\<close> \<open>k\<close>] .
  from assms(2) have \<open>(f n) < k\<close> by simp
  from card_mnm[OF this] have 1:
    \<open>card {i. i < k \<and> hamlet ((Rep_run r) i c)}
   = card {i. i \<le> (f n) \<and> hamlet ((Rep_run r) i c)}
   + card {i. (f n) < i \<and> i < k \<and> hamlet ((Rep_run r) i c)}\<close>
    by simp
  from assms(2) have \<open>k < f (Suc n)\<close> by simp
  with no_tick_before_suc[OF assms(1)] have
    \<open>card {i. (f n) < i \<and> i < k \<and> hamlet ((Rep_run r) i c)} = 0\<close> by fastforce
  with 1 have
    \<open>card {i. i < k \<and> hamlet ((Rep_run r) i c)}
   = card {i. i \<le> (f n) \<and> hamlet ((Rep_run r) i c)}\<close> by linarith
  hence 
    \<open>card {i. i < k \<and> hamlet ((Rep_run r) i c)}
   = card {i. i < (f (Suc n)) \<and> hamlet ((Rep_run r) i c)}\<close>
    using no_tick_before_suc[OF assms(1)] assms(2) by (metis less_trans not_le order_le_less)
  thus ?thesis using tick_count_strict_def[symmetric, of \<open>k\<close> \<open>r\<close> \<open>c\<close>]
                     tick_count_strict_def[symmetric, of \<open>f (Suc n)\<close> \<open>r\<close> \<open>c\<close>] by simp
qed

lemma tick_count_strict_sub:
  assumes \<open>dilating f sub r\<close>
  shows \<open>tick_count_strict sub c n = tick_count_strict r c (f n)\<close>
proof -
  have \<open>tick_count_strict sub c n = card {i. i < n \<and> hamlet ((Rep_run sub) i c)}\<close>
    using tick_count_strict_def[of \<open>sub\<close> \<open>c\<close> \<open>n\<close>] .
  also have \<open>... = card (image f {i. i < n \<and> hamlet ((Rep_run sub) i c)})\<close>
    using assms dilating_def dilating_injects[OF assms] by (simp add: card_image)
  also have \<open>... = card {i. i < f n \<and> hamlet ((Rep_run r) i c)}\<close>
    using dilated_strict_prefix[OF assms, symmetric, of \<open>n\<close> \<open>c\<close>] by simp
  also have \<open>... = tick_count_strict r c (f n)\<close>
    using tick_count_strict_def[of \<open>r\<close> \<open>c\<close> \<open>f n\<close>] by simp
  finally show ?thesis .
qed

lemma card_prop_mono:
  assumes \<open>m \<le> n\<close>
    shows \<open>card {i::nat. i \<le> m \<and> P i} \<le> card {i. i \<le> n \<and> P i}\<close>
proof -
  from assms have \<open>{i. i \<le> m \<and> P i} \<subseteq> {i. i \<le> n \<and> P i}\<close> by auto
  moreover have \<open>finite {i. i \<le> n \<and> P i}\<close> by simp
  ultimately show ?thesis by (simp add: card_mono)
qed

lemma mono_tick_count:
  \<open>mono (\<lambda> k. tick_count r c k)\<close>
proof
  { fix x y::nat
    assume \<open>x \<le> y\<close>
    from card_prop_mono[OF this] have \<open>tick_count r c x \<le> tick_count r c y\<close>
      unfolding tick_count_def by simp
  } thus \<open>\<And>x y. x \<le> y \<Longrightarrow> tick_count r c x \<le> tick_count r c y\<close> .
qed

lemma greatest_prev_image:
  assumes \<open>dilating f sub r\<close>
    shows \<open>(\<nexists>n\<^sub>0. f n\<^sub>0 = n) \<Longrightarrow> (\<exists>n\<^sub>p. f n\<^sub>p < n \<and> (\<forall>k. f n\<^sub>p < k \<and> k \<le> n \<longrightarrow> (\<nexists>k\<^sub>0. f k\<^sub>0 = k)))\<close>
proof (induction n)
  case 0
    with assms have \<open>f 0 = 0\<close> by (simp add: dilating_def dilating_fun_def)
    thus ?case using "0.prems" by blast
next
  case (Suc n)
  show ?case
  proof (cases \<open>\<exists>n\<^sub>0. f n\<^sub>0 = n\<close>)
    case True
      from this obtain n\<^sub>0 where \<open>f n\<^sub>0 = n\<close> by blast
      hence \<open>f n\<^sub>0 < (Suc n) \<and> (\<forall>k. f n\<^sub>0 < k \<and> k \<le> (Suc n) \<longrightarrow> (\<nexists>k\<^sub>0. f k\<^sub>0 = k))\<close>
        using Suc.prems Suc_leI le_antisym by blast
      thus ?thesis by blast
  next
    case False
    from Suc.IH[OF this] obtain n\<^sub>p
      where \<open>f n\<^sub>p < n \<and> (\<forall>k. f n\<^sub>p < k \<and> k \<le> n \<longrightarrow> (\<nexists>k\<^sub>0. f k\<^sub>0 = k))\<close> by blast
    with Suc(2) have \<open>f n\<^sub>p < (Suc n) \<and> (\<forall>k. f n\<^sub>p < k \<and> k \<le> (Suc n) \<longrightarrow> (\<nexists>k\<^sub>0. f k\<^sub>0 = k))\<close>
      by (metis le_SucE less_Suc_eq)
    thus ?thesis by blast
  qed
qed

lemma strict_mono_suc:
  assumes \<open>strict_mono f\<close>
      and \<open>f sn = Suc (f n)\<close>
    shows \<open>sn = Suc n\<close>
by (metis Suc_lessI assms lessI not_less_eq strict_mono_def strict_mono_less)

lemma next_non_stuttering:
  assumes \<open>dilating f sub r\<close>
      and \<open>f n\<^sub>p < n \<and> (\<forall>k. f n\<^sub>p < k \<and> k \<le> n \<longrightarrow> (\<nexists>k\<^sub>0. f k\<^sub>0 = k))\<close>
      and \<open>f sn\<^sub>0 = Suc n\<close>
    shows \<open>sn\<^sub>0 = Suc n\<^sub>p\<close>
proof -
  from assms(1) have smf:\<open>strict_mono f\<close> by (simp add: dilating_def dilating_fun_def)
  from assms(2) have \<open>f n\<^sub>p < n\<close> by simp
  with smf assms(3) have *:\<open>sn\<^sub>0 > n\<^sub>p\<close> using strict_mono_less by fastforce
  from assms(2) have \<open>f (Suc n\<^sub>p) > n\<close> by (metis lessI not_le_imp_less smf strict_mono_less)
  hence \<open>Suc n \<le> f (Suc n\<^sub>p)\<close> by simp
  hence \<open>sn\<^sub>0 \<le> Suc n\<^sub>p\<close> using assms(3) smf using strict_mono_less_eq by fastforce
  with * show ?thesis by simp
qed

lemma dil_tick_count:
  assumes \<open>sub \<lless> r\<close>
      and \<open>\<forall>n. run_tick_count sub a n \<le> run_tick_count sub b n\<close>
    shows \<open>run_tick_count r a n \<le> run_tick_count r b n\<close>
proof -
  from assms(1) is_subrun_def obtain f where *:\<open>dilating f sub r\<close> by blast
  show ?thesis
  proof (induction n)
    case 0 thus ?case
      by (metis * assms(2) dilating_def dilating_fun_def run_tick_count_sub)
  next
    case (Suc n') thus ?case 
    proof -
      from * have f3: "run_tick_count sub a (v5_1 a (Suc n') sub f) = run_tick_count r a (f (v5_1 a (Suc n') sub f))"
        using run_tick_count_sub by blast
      have f4: "\<forall>f r ra n c. (\<not> dilating f (r::'a run) ra \<or> \<not> hamlet (Rep_run ra n c)) \<or> (\<exists>na. f na = n \<and> hamlet (Rep_run r na c))"
        using ticks_imp_ticks_subk by blast
      obtain nna :: "clock \<Rightarrow> nat \<Rightarrow> 'a run \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> nat" where
        f5: "\<forall>x0 x1 x3 x4. (\<exists>v5. x4 v5 = x1 \<and> hamlet (Rep_run x3 v5 x0)) = (x4 (nna x0 x1 x3 x4) = x1 \<and> hamlet (Rep_run x3 (nna x0 x1 x3 x4) x0))"
        by moura
      have f6: "#\<^sub>\<le> sub b nna a (Suc n') sub f = #\<^sub>\<le> r b f (nna a (Suc n') sub f)"
        using * run_tick_count_sub by blast
      have "#\<^sub>\<le> sub a nna a (Suc n') sub f \<le> #\<^sub>\<le> sub b nna a (Suc n') sub f"
        by (simp add: assms(2))
      then show ?thesis
        using run_tick_count_sub f6 f5 f4 f3 * Suc.IH by fastforce
    qed
\<^cancel>\<open>
    from assms(2) have \<open>tick_count sub a (Suc n') \<le> tick_count sub b (Suc n')\<close>
      using tick_count_is_fun by metis
    hence 1:\<open>tick_count r a (f (Suc n')) \<le> tick_count r b (f (Suc n'))\<close> using tick_count_sub[OF *] by simp
    thus ?case using assms tick_count_f_suc_sub[OF *] Suc.IH
      by (smt * no_tick_sub run_tick_count_sub run_tick_count_suc)
  qed
\<close>
  qed
qed

lemma stutter_no_time:
  assumes \<open>dilating f sub r\<close>
      and \<open>\<forall>k. f n < k \<and> k \<le> m \<longrightarrow> (\<nexists>k\<^sub>0. f k\<^sub>0 = k)\<close>
      and \<open>m > f n\<close>
    shows \<open>time ((Rep_run r) m c) = time ((Rep_run r) (f n) c)\<close>
proof -
  from assms have \<open>\<forall>k. k < m - (f n) \<longrightarrow> (\<nexists>k\<^sub>0. f k\<^sub>0 = Suc ((f n) + k))\<close> by simp
  hence \<open>\<forall>k. k < m - (f n)
            \<longrightarrow> time ((Rep_run r) (Suc ((f n) + k)) c) = time ((Rep_run r) ((f n) + k) c)\<close>
    using assms(1) by (simp add: dilating_def dilating_fun_def)
  hence *:\<open>\<forall>k. k < m - (f n) \<longrightarrow> time ((Rep_run r) (Suc ((f n) + k)) c) = time ((Rep_run r) (f n) c)\<close>
    using bounded_suc_ind[of \<open>m - (f n)\<close> \<open>\<lambda>k. time (Rep_run r k c)\<close> \<open>f n\<close>] by blast
  from assms(3) obtain m\<^sub>0 where m0:\<open>Suc m\<^sub>0 = m - (f n)\<close> using Suc_diff_Suc by blast
  with * have \<open>time ((Rep_run r) (Suc ((f n) + m\<^sub>0)) c) = time ((Rep_run r) (f n) c)\<close> by auto
  moreover from m0 have \<open>Suc ((f n) + m\<^sub>0) = m\<close> by simp
  ultimately show ?thesis by simp
qed

lemma time_stuttering:
  assumes \<open>dilating f sub r\<close>
      and \<open>time ((Rep_run sub) n c) = \<tau>\<close>
      and \<open>\<forall>k. f n < k \<and> k \<le> m \<longrightarrow> (\<nexists>k\<^sub>0. f k\<^sub>0 = k)\<close>
      and \<open>m > f n\<close>
    shows \<open>time ((Rep_run r) m c) = \<tau>\<close>
proof -
  from assms(3) have \<open>time ((Rep_run r) m c) = time ((Rep_run r) (f n) c)\<close>
    using  stutter_no_time[OF assms(1,3,4)] ..
  also from assms(1,2) have \<open>time ((Rep_run r) (f n) c) = \<tau>\<close> by (simp add: dilating_def)
  finally show ?thesis .
qed

lemma first_time_image:
  assumes \<open>dilating f sub r\<close>
  shows \<open>first_time sub c n t = first_time r c (f n) t\<close>
proof
  assume \<open>first_time sub c n t\<close>
  with before_first_time[OF this]
    have *:\<open>time ((Rep_run sub) n c) = t \<and> (\<forall>m < n. time((Rep_run sub) m c) < t)\<close>
      by (simp add: first_time_def)
  hence **:\<open>time ((Rep_run r) (f n) c) = t \<and> (\<forall>m < n. time((Rep_run r) (f m) c) < t)\<close>
    using assms(1) dilating_def by metis
  have \<open>\<forall>m < f n. time ((Rep_run r) m c) < t\<close>
  proof -
  { fix m assume hyp:\<open>m < f n\<close>
    have \<open>time ((Rep_run r) m c) < t\<close>
    proof (cases \<open>\<exists>m\<^sub>0. f m\<^sub>0 = m\<close>)
      case True
        from this obtain m\<^sub>0 where mm0:\<open>m = f m\<^sub>0\<close> by blast
        with hyp have m0n:\<open>m\<^sub>0 < n\<close> using assms(1) by (simp add: dilating_def dilating_fun_def strict_mono_less)
        hence \<open>time ((Rep_run sub) m\<^sub>0 c) < t\<close> using * by blast
        thus ?thesis by (simp add: mm0 m0n **)
    next
      case False
        hence \<open>\<exists>m\<^sub>p. f m\<^sub>p < m \<and> (\<forall>k. f m\<^sub>p < k \<and> k \<le> m \<longrightarrow> (\<nexists>k\<^sub>0. f k\<^sub>0 = k))\<close> using greatest_prev_image[OF assms] by simp
        from this obtain m\<^sub>p where mp:\<open>f m\<^sub>p < m \<and> (\<forall>k. f m\<^sub>p < k \<and> k \<le> m \<longrightarrow> (\<nexists>k\<^sub>0. f k\<^sub>0 = k))\<close> by blast
        hence \<open>time ((Rep_run r) m c) = time ((Rep_run sub) m\<^sub>p c)\<close>  using time_stuttering[OF assms] by blast
        moreover from mp have \<open>time ((Rep_run sub) m\<^sub>p c) < t\<close> using *
          by (meson assms dilating_def dilating_fun_def hyp less_trans strict_mono_less)
        ultimately show ?thesis by simp
      qed
    } thus ?thesis by simp
  qed
  with ** show \<open>first_time r c (f n) t\<close> by (simp add: alt_first_time_def)
next
  assume \<open>first_time r c (f n) t\<close>
  hence *:\<open>time ((Rep_run r) (f n) c) = t \<and> (\<forall>k < f n. time ((Rep_run r) k c) < t)\<close>
    by (simp add: first_time_def before_first_time)
  hence \<open>time ((Rep_run sub) n c) = t\<close> using assms dilating_def by blast
  moreover from * have \<open>(\<forall>k < n. time ((Rep_run sub) k c) < t)\<close>
    using assms dilating_def dilating_fun_def strict_monoD by fastforce
  ultimately show \<open>first_time sub c n t\<close> by (simp add: alt_first_time_def)
qed

end
