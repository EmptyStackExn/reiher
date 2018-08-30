section \<open> Defining Runs \<close>

theory Run
imports
    "TESL"
      
begin

abbreviation hamlet where "hamlet \<equiv> fst"
abbreviation time   where "time \<equiv> snd"

type_synonym '\<tau> instant = "clock \<Rightarrow> (bool \<times> '\<tau> tag_const)"
typedef (overloaded) '\<tau>::linordered_field run =
  "{ \<rho>::nat \<Rightarrow> '\<tau> instant. \<forall>c. mono (\<lambda>n. time (\<rho> n c)) }"
proof
  show "(\<lambda>_ _. (True, \<tau>\<^sub>c\<^sub>s\<^sub>t 0)) \<in> {\<rho>::nat \<Rightarrow> clock \<Rightarrow> bool \<times> '\<tau> tag_const. \<forall>c::clock. mono (\<lambda>n::nat. time (\<rho> n c))}"
  using mono_def by auto
qed
lemma Abs_run_inverse_rewrite:
  "\<forall>c. mono (\<lambda>n. time (\<rho> n c)) \<Longrightarrow> Rep_run (Abs_run \<rho>) = \<rho>"
  by (simp add: Abs_run_inverse)

(* WARNING: Admitting monotonicity to compute faster. Use for debugging purposes only. *)
lemma Abs_run_inverse_rewrite_unsafe:
  "Rep_run (Abs_run \<rho>) = \<rho>"
  oops (* Use [sorry] when testing *)

(* Counts the number of ticks in run [\<rho>] on clock [K] from indexes 0 to [n] *)
fun run_tick_count :: "('\<tau>::linordered_field) run \<Rightarrow> clock \<Rightarrow> nat \<Rightarrow> nat" ("#\<^sup>\<le> _ _ _") where
    "#\<^sup>\<le> \<rho> K 0       = (if hamlet ((Rep_run \<rho>) 0 K)
                       then 1
                       else 0)"
  | "#\<^sup>\<le> \<rho> K (Suc n) = (if hamlet ((Rep_run \<rho>) (Suc n) K)
                       then 1 + #\<^sup>\<le> \<rho> K n
                       else #\<^sup>\<le> \<rho> K n)"

(* Counts the number of ticks in run [\<rho>] on clock [K] from indexes 0 to [n - 1] *)
fun run_tick_count_strictly :: "('\<tau>::linordered_field) run \<Rightarrow> clock \<Rightarrow> nat \<Rightarrow> nat" ("#\<^sup>< _ _ _") where
    "#\<^sup>< \<rho> K 0       = 0"
  | "#\<^sup>< \<rho> K (Suc n) = #\<^sup>\<le> \<rho> K n"

fun counter_expr_eval :: "('\<tau>::linordered_field) run \<Rightarrow> cnt_expr \<Rightarrow> nat" ("\<lbrakk> _ \<turnstile> _ \<rbrakk>\<^sub>c\<^sub>n\<^sub>t\<^sub>e\<^sub>x\<^sub>p\<^sub>r") where
    "\<lbrakk> \<rho> \<turnstile> #\<^sup>< clk indx \<rbrakk>\<^sub>c\<^sub>n\<^sub>t\<^sub>e\<^sub>x\<^sub>p\<^sub>r = run_tick_count_strictly \<rho> clk indx"
  | "\<lbrakk> \<rho> \<turnstile> #\<^sup>\<le> clk indx \<rbrakk>\<^sub>c\<^sub>n\<^sub>t\<^sub>e\<^sub>x\<^sub>p\<^sub>r = run_tick_count \<rho> clk indx"


end
