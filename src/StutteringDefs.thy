chapter \<open>Properties of TESL\<close>

section \<open>Stuttering Invariance\<close>

theory StutteringDefs

imports Denotational

begin

subsection \<open>Definition of stuttering\<close>

text \<open>
  A dilating function inserts empty instants in a run.
  It is strictly increasing, the image of a @{typ nat} is greater than it,
  no instant is inserted before the first one 
  and if n is not in the image of the function, no clock ticks at instant n.
\<close>
definition dilating_fun
where
  \<open>dilating_fun (f::nat \<Rightarrow> nat) (r::'a::linordered_field run)
    \<equiv> strict_mono f \<and> (f 0 = 0) \<and> (\<forall>n. f n \<ge> n
    \<and> ((\<nexists>n\<^sub>0. f n\<^sub>0 = n) \<longrightarrow> (\<forall>c. \<not>(hamlet ((Rep_run r) n c))))
    \<and> ((\<nexists>n\<^sub>0. f n\<^sub>0 = (Suc n)) \<longrightarrow> (\<forall>c. time ((Rep_run r) (Suc n) c) = time ((Rep_run r) n c)))
   )\<close>

text\<open>
 Dilating a run. A run @{term r} is a dilation of a run @{term sub} by function @{term f} if:
 \<^item> @{term f} is a dilating function on the hamlet of @{term r} 
 \<^item> time is preserved in stuttering instants
 \<^item> the time in @{term r} is the time in @{term sub}  dilated by @{term f}
 \<^item> the hamlet in @{term r} is the hamlet in sub dilated by @{term f}
\<close>
definition dilating
  where \<open>dilating f sub r \<equiv>   dilating_fun f r
                            \<and> (\<forall>n c. time ((Rep_run sub) n c) = time ((Rep_run r) (f n) c))
                            \<and> (\<forall>n c. hamlet ((Rep_run sub) n c) = hamlet ((Rep_run r) (f n) c))\<close>

text \<open>A \<^emph>\<open>run\<close>  is a \<^emph>\<open>subrun\<close> of another run if there exists a dilation between them.\<close>
definition is_subrun ::\<open>'a::linordered_field run \<Rightarrow> 'a run \<Rightarrow> bool\<close> (infixl "\<lless>" 60)
where
  \<open>sub \<lless> r \<equiv> (\<exists>f. dilating f sub r)\<close>

text \<open>A @{term \<open>tick_count r c n\<close>} is a
  number of ticks of clock @{term c} in run @{term r} upto instant @{term n}.
\<close>
definition tick_count :: \<open>'a::linordered_field run \<Rightarrow> clock \<Rightarrow> nat \<Rightarrow> nat\<close>
where
  \<open>tick_count r c n = card {i. i \<le> n \<and> hamlet ((Rep_run r) i c)}\<close>

text \<open>A @{term \<open>tick_count_strict r c n\<close>} is a number of ticks of clock @{term c} in run 
      @{term r} upto but  excluding instant @{term n}. \<close> 
definition tick_count_strict :: \<open>'a::linordered_field run \<Rightarrow> clock \<Rightarrow> nat \<Rightarrow> nat\<close>
where
  \<open>tick_count_strict r c n = card {i. i < n \<and> hamlet ((Rep_run r) i c)}\<close>

definition contracting_fun
  where \<open>contracting_fun g \<equiv> mono g \<and> g 0 = 0 \<and> (\<forall>n. g n \<le> n)\<close>

definition contracting
where 
  \<open>contracting g r sub f \<equiv>  contracting_fun g
                          \<and> (\<forall>n c k. f (g n) \<le> k \<and> k \<le> n
                              \<longrightarrow> time ((Rep_run r) k c) = time ((Rep_run sub) (g n) c))
                          \<and> (\<forall>n c k. f (g n) < k \<and> k \<le> n
                              \<longrightarrow> \<not> hamlet ((Rep_run r) k c))\<close>

lemma
  assumes \<open>dilating f sub r\<close>
    shows \<open>contracting (\<lambda>n. Max {i. f i \<le> n}) r sub f\<close>  (is \<open>contracting ?g r sub f\<close>)
proof -
  have \<open>mono ?g\<close>
  proof -
  { fix x::\<open>nat\<close> and y::\<open>nat\<close> assume hyp:\<open>x \<le> y\<close>
    from assms have "strict_mono f" by (simp add: dilating_def dilating_fun_def)
    hence finite:\<open>finite {i. f i \<le> y}\<close>
      by (metis (full_types) assms dilating_def dilating_fun_def finite_less_ub)
    from assms have "f 0 = 0" by (simp add: dilating_def dilating_fun_def)
    hence notempty:\<open>{i. f i \<le> x} \<noteq> {}\<close> by (metis empty_Collect_eq le0)
    hence inc:\<open>{i. f i \<le> x} \<subseteq> {i. f i \<le> y}\<close>
      by (simp add: hyp Collect_mono le_trans)
    from Max_mono[OF inc notempty finite] have "?g x \<le> ?g y" .
  } thus ?thesis unfolding mono_def by simp
  qed

  from assms have "f 0 = 0" by (simp add: dilating_def dilating_fun_def)
  have \<open>g 0 = 0\<close> sorry
  oops

end
