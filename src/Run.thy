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

(*<*)
text\<open>Do we want to explain this trick? Is it still useful?\<close>
(* WARNING: Admitting monotonicity to compute faster. Use for debugging purposes only. *)
lemma Abs_run_inverse_rewrite_unsafe:
  "Rep_run (Abs_run \<rho>) = \<rho>"
oops (* Use [sorry] when testing *)
(*>*)

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


end
