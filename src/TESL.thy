chapter\<open>The Core of the TESL Language: Syntax and Basics\<close>

theory TESL
imports Main

begin

section\<open>Syntactic Representation\<close>
text\<open>
  We define here the syntax of TESL specifications.
\<close>

subsection\<open>Basic elements of a specification\<close>
text\<open>
  The following items appear in specifications:
  \<^item> Clocks, which are identified by a name.
  \<^item> Instant indexes, (FIXME) which are natural integers, should not be used directly but appear 
    here for technical and historical reasons.
  \<^item> Tag constants are just constants of a type which denotes the metric time space.
  \<^item> Tag variables represent the time at a given instant on a given clock.
  \<^item> Tag expressions are used to represent either a tag constant or a delayed time with respect 
    to a tag variable.
\<close>

datatype     clock         = Clk \<open>string\<close>
type_synonym instant_index = \<open>nat\<close>

datatype '\<tau> tag_const =
    TConst   '\<tau>                      ("\<tau>\<^sub>c\<^sub>s\<^sub>t")

datatype tag_var =
  TSchematic \<open>clock * instant_index\<close> ("\<tau>\<^sub>v\<^sub>a\<^sub>r")

\<^cancel>\<open>
datatype '\<tau> tag_expr =
  Const    \<open>'\<tau> tag_const\<close>           ("\<lparr> _ \<rparr>")
| AddDelay \<open>tag_var\<close> \<open>'\<tau> tag_const\<close> ("\<lparr> _ \<oplus> _ \<rparr>")
\<close>

subsection\<open>Operators for the TESL language\<close>
text\<open>
  The type of atomic TESL constraints, which can be combined to form specifications.
\<close>
datatype '\<tau> TESL_atomic =
\<^cancel>\<open>
    SporadicOn       \<open>clock\<close> \<open>'\<tau> tag_expr\<close>  \<open>clock\<close>         ("_ sporadic _ on _" 55)
\<close>
    SporadicOn       \<open>clock\<close> \<open>'\<tau> tag_const\<close>  \<open>clock\<close>         ("_ sporadic _ on _" 55)
  | TagRelation      \<open>clock\<close> \<open>clock\<close> \<open>('\<tau> tag_const \<times> '\<tau> tag_const) \<Rightarrow> bool\<close> 
                                                            ("time-relation \<lfloor>_, _\<rfloor> \<in> _" 55)
  | Implies          \<open>clock\<close> \<open>clock\<close>                        (infixr "implies" 55)
  | ImpliesNot       \<open>clock\<close> \<open>clock\<close>                        (infixr "implies not" 55)
  | TimeDelayedBy    \<open>clock\<close> \<open>'\<tau> tag_const\<close> \<open>clock\<close> \<open>clock\<close> ("_ time-delayed by _ on _ implies _" 55)
  | WeaklyPrecedes   \<open>clock\<close> \<open>clock\<close>                        (infixr "weakly precedes" 55)
  | StrictlyPrecedes \<open>clock\<close> \<open>clock\<close>                        (infixr "strictly precedes" 55)
  | Kills            \<open>clock\<close> \<open>clock\<close>                        (infixr "kills" 55)

text\<open>
  A TESL formula is just a list of atomic constraints, with implicit conjunction for the semantics.
\<close>
type_synonym '\<tau> TESL_formula = \<open>'\<tau> TESL_atomic list\<close>

text\<open>
  We call \<^emph>\<open>positive atoms\<close> the atomic constraints that create ticks from nothing.
  Only sporadic constraints are positive in the current version of TESL.
\<close>
fun positive_atom :: \<open>'\<tau> TESL_atomic \<Rightarrow> bool\<close> where
    \<open>positive_atom (_ sporadic _ on _) = True\<close>
  | \<open>positive_atom _                   = False\<close>

text\<open>
  The @{term \<open>NoSporadic\<close>} function removes sporadic constraints from a TESL formula.
\<close>
abbreviation NoSporadic :: \<open>'\<tau> TESL_formula \<Rightarrow> '\<tau> TESL_formula\<close> where 
  \<open>NoSporadic f \<equiv> (List.filter (\<lambda>f\<^sub>a\<^sub>t\<^sub>o\<^sub>m. case f\<^sub>a\<^sub>t\<^sub>o\<^sub>m of
      _ sporadic _ on _ \<Rightarrow> False
    | _ \<Rightarrow> True) f)\<close>

subsection\<open>Field Structure of the Metric Time Space\<close>
text\<open>
  In order to handle tag relations and delays, tag must be in a field.
  We show here that this is the case when the type parameter of @{typ \<open>'\<tau> tag_const\<close>} 
  is itself a field.
\<close>
instantiation tag_const :: (plus)plus
begin
  fun plus_tag_const :: \<open>'a tag_const \<Rightarrow> 'a tag_const \<Rightarrow> 'a tag_const\<close>
  where
      TConst_plus: \<open>(TConst n) + (TConst p) = (TConst (n + p))\<close>

  instance by (rule Groups.class.Groups.plus.of_class.intro)
end

instantiation tag_const :: (minus)minus
begin
  fun minus_tag_const :: \<open>'a tag_const \<Rightarrow> 'a tag_const \<Rightarrow> 'a tag_const\<close>
  where
      TConst_minus: \<open>(TConst n) - (TConst p) = (TConst (n - p))\<close>

  instance by (rule Groups.class.Groups.minus.of_class.intro)
end

instantiation tag_const :: (times)times
begin
  fun times_tag_const :: \<open>'a tag_const \<Rightarrow> 'a tag_const \<Rightarrow> 'a tag_const\<close> 
  where
      TConst_times: \<open>(TConst n) * (TConst p) = (TConst (n * p))\<close>

  instance by (rule Groups.class.Groups.times.of_class.intro)
end

instantiation tag_const :: (divide)divide
begin
  fun divide_tag_const :: \<open>'a tag_const \<Rightarrow> 'a tag_const \<Rightarrow> 'a tag_const\<close> 
  where
      TConst_divide: \<open>divide (TConst n) (TConst p) = (TConst (divide n p))\<close>

  instance by (rule Rings.class.Rings.divide.of_class.intro)
end

instantiation tag_const :: (inverse)inverse
begin
  fun inverse_tag_const :: \<open>'a tag_const \<Rightarrow> 'a tag_const\<close>
  where
      TConst_inverse: \<open>inverse (TConst n) = (TConst (inverse n))\<close>

  instance by (rule Fields.class.Fields.inverse.of_class.intro)
end

instantiation tag_const :: (order)order
begin
  inductive less_eq_tag_const :: \<open>'a tag_const \<Rightarrow> 'a tag_const \<Rightarrow> bool\<close>
  where
    Int_less_eq[simp]:      \<open>n \<le> m \<Longrightarrow> (TConst n) \<le> (TConst m)\<close>

  definition less_tag: \<open>(x::'a tag_const) < y \<longleftrightarrow> (x \<le> y) \<and> (x \<noteq> y)\<close>

  instance proof
    show \<open>\<And>x y :: 'a tag_const. (x < y) = (x \<le> y \<and> \<not> y \<le> x)\<close>
      using less_eq_tag_const.simps less_tag by auto
    show \<open>\<And>x  :: 'a tag_const. x \<le> x\<close>
      by (metis (full_types) Int_less_eq order_refl tag_const.exhaust)
    show \<open>\<And>x y z  :: 'a tag_const. x \<le> y \<Longrightarrow> y \<le> z \<Longrightarrow> x \<le> z\<close>
      using less_eq_tag_const.simps by auto
    show \<open>\<And>x y  :: 'a tag_const. x \<le> y \<Longrightarrow> y \<le> x \<Longrightarrow> x = y\<close>
      using less_eq_tag_const.simps by auto
  qed
end

instantiation tag_const :: (linorder)linorder
begin
  instance proof
    show \<open>\<And>x y. (x::'a tag_const) \<le> y \<or> y \<le> x\<close>
      by (metis (full_types) Int_less_eq le_cases tag_const.exhaust)
  qed
end

end