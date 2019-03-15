section \<open> Defining Runs \<close>

theory Run
imports
    "TESL"
      
begin
text\<open>
  Runs are sequences of instants, each instant mapping a clock to a pair that whether the clock 
  ticks or not and what is the current time on this clock. The first element of the pair is
  called the \<^emph>\<open>hamlet\<close> of the clock (to tick or not to tick), the second element is called the 
  \<^emph>\<open>time\<close>.
\<close>

abbreviation hamlet where "hamlet \<equiv> fst"
abbreviation time   where "time \<equiv> snd"

type_synonym '\<tau> instant = "clock \<Rightarrow> (bool \<times> '\<tau> tag_const)"

text\<open>
  Runs have the additional constraint that time cannot go backwards on any clock in the sequence 
  of instants. Therefore, for any clock, the time projection of a run is monotonous.
\<close>
typedef (overloaded) '\<tau>::linordered_field run =
  "{ \<rho>::nat \<Rightarrow> '\<tau> instant. \<forall>c. mono (\<lambda>n. time (\<rho> n c)) }"
proof
  show "(\<lambda>_ _. (True, \<tau>\<^sub>c\<^sub>s\<^sub>t 0)) \<in> {\<rho>. \<forall>c. mono (\<lambda>n. time (\<rho> n c))}" 
    unfolding mono_def by blast
qed

lemma Abs_run_inverse_rewrite:
  "\<forall>c. mono (\<lambda>n. time (\<rho> n c)) \<Longrightarrow> Rep_run (Abs_run \<rho>) = \<rho>"
  by (simp add: Abs_run_inverse)

text\<open>
  @{term "run_tick_count \<rho> K n"} counts the number of ticks on clock @{term "K"} 
  in the interval \<^verbatim>\<open>[0, n]\<close> of run @{term "\<rho>"}.
\<close>
fun run_tick_count :: "('\<tau>::linordered_field) run \<Rightarrow> clock \<Rightarrow> nat \<Rightarrow> nat" ("#\<^sub>\<le> _ _ _") where
    "(#\<^sub>\<le> \<rho> K 0)       = (if hamlet ((Rep_run \<rho>) 0 K)
                         then 1
                         else 0)"
  | "(#\<^sub>\<le> \<rho> K (Suc n)) = (if hamlet ((Rep_run \<rho>) (Suc n) K)
                         then 1 + (#\<^sub>\<le> \<rho> K n)
                         else (#\<^sub>\<le> \<rho> K n))"

text\<open>
  @{term "run_tick_count_strictly \<rho> K n"} counts the number of ticks on clock @{term "K"} 
  in the interval \<^verbatim>\<open>[0, n[\<close> of run @{term "\<rho>"}.
\<close>
fun run_tick_count_strictly :: "('\<tau>::linordered_field) run \<Rightarrow> clock \<Rightarrow> nat \<Rightarrow> nat" ("#\<^sub>< _ _ _")
where
    "(#\<^sub>< \<rho> K 0)       = 0"
  | "(#\<^sub>< \<rho> K (Suc n)) = #\<^sub>\<le> \<rho> K n"

definition first_time :: "'a::linordered_field run \<Rightarrow> clock \<Rightarrow> nat \<Rightarrow> 'a tag_const \<Rightarrow> bool"
where
  "first_time \<rho> K n \<tau> \<equiv> (time ((Rep_run \<rho>) n K) = \<tau>) \<and> (\<nexists>n'. n' < n \<and> time ((Rep_run \<rho>) n' K) = \<tau>)"

lemma before_first_time:
  assumes "first_time \<rho> K n \<tau>"
      and "m < n"
    shows "time ((Rep_run \<rho>) m K) < \<tau>"
proof -
  have "mono (\<lambda>n. time (Rep_run \<rho> n K))" using Rep_run by blast
  moreover from assms(2) have "m \<le> n" using less_imp_le by simp
  moreover have "mono (\<lambda>n. time (Rep_run \<rho> n K))" using Rep_run by blast
  ultimately have  "time ((Rep_run \<rho>) m K) \<le> time ((Rep_run \<rho>) n K)" by (simp add:mono_def)
  moreover from assms(1) have "time ((Rep_run \<rho>) n K) = \<tau>" using first_time_def by blast
  moreover from assms have "time ((Rep_run \<rho>) m K) \<noteq> \<tau>" using first_time_def by blast
  ultimately show ?thesis by simp
qed

lemma alt_first_time_def:
  assumes "\<forall>m < n. time ((Rep_run \<rho>) m K) < \<tau>"
      and "time ((Rep_run \<rho>) n K) = \<tau>"
    shows "first_time \<rho> K n \<tau>"
proof -
  from assms(1) have "\<forall>m < n. time ((Rep_run \<rho>) m K) \<noteq> \<tau>" by (simp add: less_le)
  with assms(2) show ?thesis by (simp add: first_time_def)
qed

end
