chapter \<open>Properties of TESL\<close>

section \<open>Stuttering Invariance\<close>

theory StutteringDefs

imports Denotational

begin

text \<open>
  When composing systems into more complex systems, it may happen that one system 
  has to perform some action while the rest of the complex system does nothing.
  In order to support the composition of TESL specifications, we want to be able 
  to insert stuttering instants in a run without breaking the conformance of a run 
  to its specification. This is what we call the \<^emph>\<open>stuttering invariance\<close> of TESL.
\<close>

subsection \<open>Definition of stuttering\<close>

text \<open>
  We consider stuttering as the insertion of empty instants (instants at which no 
  clock ticks) in a run. We caracterize this insertion with a dilating function,
  which maps the instant indices of the original run to the corresponding instant
  indices of the dilated run.
  The properties of a dilating function are:
  \<^item> it is strictly increasing because instants are inserted into the run,
  \<^item> the image of an instant index is greater than it because stuttering instant 
    can only delay the original instants of the run, 
  \<^item> no instant is inserted before the first one in oredr to have a well defined 
    initial date on each clock,
  \<^item> if @{term \<open>n\<close>} is not in the image of the function, no clock ticks at 
    instant @{term \<open>n\<close>} and the date on the clocks do not change.
\<close>
definition dilating_fun
where
  \<open>dilating_fun (f::nat \<Rightarrow> nat) (r::'a::linordered_field run)
    \<equiv> strict_mono f \<and> (f 0 = 0) \<and> (\<forall>n. f n \<ge> n
    \<and> ((\<nexists>n\<^sub>0. f n\<^sub>0 = n) \<longrightarrow> (\<forall>c. \<not>(hamlet ((Rep_run r) n c))))
    \<and> ((\<nexists>n\<^sub>0. f n\<^sub>0 = (Suc n)) \<longrightarrow> (\<forall>c. time ((Rep_run r) (Suc n) c)
                                      = time ((Rep_run r) n c)))
   )\<close>

text\<open>
  Dilating a run. A run @{term r} is a dilation of a run @{term sub} by 
  function @{term f} if:
  \<^item> @{term f} is a dilating function for @{term r} 
  \<^item> the time in @{term r} is the time in @{term sub} dilated by @{term f}
  \<^item> the hamlet in @{term r} is the hamlet in sub dilated by @{term f}
\<close>
definition dilating
where
  \<open>dilating f sub r \<equiv> dilating_fun f r
                    \<and> (\<forall>n c. time ((Rep_run sub) n c) = time ((Rep_run r) (f n) c))
                    \<and> (\<forall>n c. hamlet ((Rep_run sub) n c) = hamlet ((Rep_run r) (f n) c))\<close>

text \<open>
  A \<^emph>\<open>run\<close> is a \<^emph>\<open>subrun\<close> of another run if there exists a dilation between them.
\<close>
definition is_subrun ::\<open>'a::linordered_field run \<Rightarrow> 'a run \<Rightarrow> bool\<close> (infixl "\<lless>" 60)
where
  \<open>sub \<lless> r \<equiv> (\<exists>f. dilating f sub r)\<close>

text \<open>
  @{term \<open>tick_count r c n\<close>} is the number of ticks of clock @{term c} in 
  run @{term r} upto instant @{term n}.
\<close>
definition tick_count :: \<open>'a::linordered_field run \<Rightarrow> clock \<Rightarrow> nat \<Rightarrow> nat\<close>
where
  \<open>tick_count r c n = card {i. i \<le> n \<and> hamlet ((Rep_run r) i c)}\<close>

text \<open>
  @{term \<open>tick_count_strict r c n\<close>} is the number of ticks of clock @{term c} 
  in run @{term r} upto but excluding instant @{term n}.
\<close> 
definition tick_count_strict :: \<open>'a::linordered_field run \<Rightarrow> clock \<Rightarrow> nat \<Rightarrow> nat\<close>
where
  \<open>tick_count_strict r c n = card {i. i < n \<and> hamlet ((Rep_run r) i c)}\<close>

text \<open>
  A contracting function is the reverse of a dilating fun, it maps an instant index 
  of a dilated run to the index of the last instant of a non stuttering run that
  precedes it. Since several successive stuttering instants are mapped to the same
  instant of the non stuttering run, such a function is monotonous, but not strictly.
  The image of the first instant of the dilated run is necessarily the first instant
  of the non stuttering run, and the image of an instant index is less that this 
  index because we remove stuttering instants. 
\<close>
definition contracting_fun
  where \<open>contracting_fun g \<equiv> mono g \<and> g 0 = 0 \<and> (\<forall>n. g n \<le> n)\<close>

definition contracting
where 
  \<open>contracting g r sub f \<equiv>  contracting_fun g
                          \<and> (\<forall>n c k. f (g n) \<le> k \<and> k \<le> n
                              \<longrightarrow> time ((Rep_run r) k c) = time ((Rep_run sub) (g n) c))
                          \<and> (\<forall>n c k. f (g n) < k \<and> k \<le> n
                              \<longrightarrow> \<not> hamlet ((Rep_run r) k c))\<close>

definition \<open>dil_inverse f::(nat \<Rightarrow> nat) \<equiv> (\<lambda>n. Max {i. f i \<le> n})\<close>

end
