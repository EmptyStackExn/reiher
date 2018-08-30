theory StutteringDefs

imports Denotational

begin

section {* Invariance of specifications by stuttering *}

subsection {* Definition of stuttering *}

text {*
  A dilating function inserts empty instants in a run.
  It is strictly increasing, the image of a @{typ nat} is greater than it,
  no instant is inserted before the first one 
  and if n is not in the image of the function, no clock ticks at instant n.
*}
definition dilating_fun
where
  "dilating_fun (f::nat \<Rightarrow> nat) (r::'a::linordered_field run)
    \<equiv> strict_mono f \<and> (f 0 = 0) \<and> (\<forall>n. f n \<ge> n
    \<and> ((\<nexists>n\<^sub>0. f n\<^sub>0 = n) \<longrightarrow> (\<forall>c. \<not>(hamlet ((Rep_run r) n c))))
    \<and> ((\<nexists>n\<^sub>0. f n\<^sub>0 = (Suc n)) \<longrightarrow> (\<forall>c. time ((Rep_run r) (Suc n) c) = time ((Rep_run r) n c)))
   )"

text\<open>
 Dilating a run. A run @{term r} is a dilation of a run @{term sub} by function @{term f} if:
 \<^item> @{term f} is a dilating function on the hamlet of @{term r} 
 \<^item> time is preserved in stuttering instants
 \<^item> the time in @{term r} is the time in @{term sub}  dilated by @{term f}
 \<^item> the hamlet in @{term r} is the hamlet in sub dilated by @{term f}
\<close>
definition dilating
  where "dilating f sub r \<equiv>   dilating_fun f r
                            \<and> (\<forall>n c. time ((Rep_run sub) n c) = time ((Rep_run r) (f n) c))
                            \<and> (\<forall>n c. hamlet ((Rep_run sub) n c) = hamlet ((Rep_run r) (f n) c))"

text {* A \<^emph>\<open>run\<close>  is a \<^emph>\<open>subrun\<close> of another run if there exists a dilation between them.
*}
definition is_subrun ::"'a::linordered_field run \<Rightarrow> 'a run \<Rightarrow> bool" (infixl "\<lless>" 60)
where
  "sub \<lless> r \<equiv> (\<exists>f. dilating f sub r)"

text {* A @{term "tick_count r c n"} is a
  number of ticks of clock @{term c} in run @{term r} upto instant @{term n}.
*}
definition tick_count :: "'a::linordered_field run \<Rightarrow> clock \<Rightarrow> nat \<Rightarrow> nat"
where
  "tick_count r c n = card {i. i \<le> n \<and> hamlet ((Rep_run r) i c)}"

text \<open>A @{term "tick_count_strict r c n"} is a number of ticks of clock @{term c} in run 
      @{term r} upto but  excluding instant @{term n}. \<close> 
definition tick_count_strict :: "'a::linordered_field run \<Rightarrow> clock \<Rightarrow> nat \<Rightarrow> nat"
where
  "tick_count_strict r c n = card {i. i < n \<and> hamlet ((Rep_run r) i c)}"


end
