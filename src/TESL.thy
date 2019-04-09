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
  \<^item> Tag constants are just constants of a type which denotes the metric time space.
\<close>

datatype     clock         = Clk \<open>string\<close>
type_synonym instant_index = \<open>nat\<close>

datatype '\<tau> tag_const =
    TConst   '\<tau>                      ("\<tau>\<^sub>c\<^sub>s\<^sub>t")


subsection\<open>Operators for the TESL language\<close>
text\<open>
  The type of atomic TESL constraints, which can be combined to form specifications.
\<close>
datatype '\<tau> TESL_atomic =
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
abbreviation NoSporadic :: \<open>'\<tau> TESL_formula \<Rightarrow> '\<tau> TESL_formula\<close>
where 
  \<open>NoSporadic f \<equiv> (List.filter (\<lambda>f\<^sub>a\<^sub>t\<^sub>o\<^sub>m. case f\<^sub>a\<^sub>t\<^sub>o\<^sub>m of
      _ sporadic _ on _ \<Rightarrow> False
    | _ \<Rightarrow> True) f)\<close>

subsection\<open>Field Structure of the Metric Time Space\<close>
text\<open>
  In order to handle tag relations and delays, tags must belong to a field.
  We show here that this is the case when the type parameter of @{typ \<open>'\<tau> tag_const\<close>} 
  is itself a field.
\<close>
instantiation tag_const ::(field)field
begin
  fun inverse_tag_const
  where \<open>inverse (\<tau>\<^sub>c\<^sub>s\<^sub>t t) = \<tau>\<^sub>c\<^sub>s\<^sub>t (inverse t)\<close>

  fun divide_tag_const 
    where \<open>divide (\<tau>\<^sub>c\<^sub>s\<^sub>t t\<^sub>1) (\<tau>\<^sub>c\<^sub>s\<^sub>t t\<^sub>2) = \<tau>\<^sub>c\<^sub>s\<^sub>t (divide t\<^sub>1 t\<^sub>2)\<close>

  fun uminus_tag_const
    where \<open>uminus (\<tau>\<^sub>c\<^sub>s\<^sub>t t) = \<tau>\<^sub>c\<^sub>s\<^sub>t (uminus t)\<close>

fun minus_tag_const
  where \<open>minus (\<tau>\<^sub>c\<^sub>s\<^sub>t t\<^sub>1) (\<tau>\<^sub>c\<^sub>s\<^sub>t t\<^sub>2) = \<tau>\<^sub>c\<^sub>s\<^sub>t (minus t\<^sub>1 t\<^sub>2)\<close>

definition \<open>one_tag_const \<equiv> \<tau>\<^sub>c\<^sub>s\<^sub>t 1\<close>

fun times_tag_const
  where \<open>times (\<tau>\<^sub>c\<^sub>s\<^sub>t t\<^sub>1) (\<tau>\<^sub>c\<^sub>s\<^sub>t t\<^sub>2) = \<tau>\<^sub>c\<^sub>s\<^sub>t (times t\<^sub>1 t\<^sub>2)\<close>

definition \<open>zero_tag_const \<equiv> \<tau>\<^sub>c\<^sub>s\<^sub>t 0\<close>

fun plus_tag_const
  where \<open>plus (\<tau>\<^sub>c\<^sub>s\<^sub>t t\<^sub>1) (\<tau>\<^sub>c\<^sub>s\<^sub>t t\<^sub>2) = \<tau>\<^sub>c\<^sub>s\<^sub>t (plus t\<^sub>1 t\<^sub>2)\<close>

instance proof
  show \<open>\<And>(a::('\<tau>::field tag_const)) b c. a * b * c = a * (b * c)\<close> 
    by (metis (mono_tags, hide_lams) TESL.inverse_tag_const.cases TESL.times_tag_const.simps semiring_normalization_rules(18))
  show \<open>\<And>(a::('\<tau>::field tag_const)) b. a * b = b * a\<close>
    by (metis (full_types) TESL.inverse_tag_const.cases TESL.times_tag_const.simps semiring_normalization_rules(7))
  show \<open>\<And>(a::('\<tau>::field tag_const)). 1 * a = a\<close>
    by (metis (mono_tags) TESL.inverse_tag_const.cases TESL.times_tag_const.simps comm_monoid_mult_class.mult_1 one_tag_const_def)
  show \<open>\<And>(a::('\<tau>::field tag_const)) b c. a + b + c = a + (b + c)\<close>
    by (metis (mono_tags, hide_lams) TESL.inverse_tag_const.cases TESL.plus_tag_const.simps semiring_normalization_rules(25))
  show \<open>\<And>(a::('\<tau>::field tag_const)) b. a + b = b + a\<close>
    by (metis (full_types) TESL.inverse_tag_const.cases TESL.plus_tag_const.simps semiring_normalization_rules(24))
  show \<open>\<And>(a::('\<tau>::field tag_const)). 0 + a = a\<close>
    by (metis (mono_tags) TESL.plus_tag_const.simps semiring_normalization_rules(5) tag_const.exhaust zero_tag_const_def)
  show \<open>\<And>(a::('\<tau>::field tag_const)). - a + a = 0\<close>
    by (metis (mono_tags) TESL.plus_tag_const.simps TESL.uminus_tag_const.elims ab_group_add_class.ab_left_minus zero_tag_const_def)
  show \<open>\<And>(a::('\<tau>::field tag_const)) b. a - b = a + - b\<close>
    by (metis (mono_tags, hide_lams) TESL.minus_tag_const.elims TESL.plus_tag_const.simps TESL.uminus_tag_const.simps add.commute uminus_add_conv_diff)
  show \<open>\<And>(a::('\<tau>::field tag_const)) b c. (a + b) * c = a * c + b * c\<close>
  proof -
    fix a :: "'\<tau> tag_const" and b :: "'\<tau> tag_const" and c :: "'\<tau> tag_const"
  obtain tt :: "'\<tau> tag_const \<Rightarrow> '\<tau>" where
    f1: "\<forall>t. t = \<tau>\<^sub>c\<^sub>s\<^sub>t (tt t)"
    by (meson TESL.inverse_tag_const.cases)
    then have f2: "\<forall>t ta. \<tau>\<^sub>c\<^sub>s\<^sub>t (ta * tt t) = \<tau>\<^sub>c\<^sub>s\<^sub>t ta * t"
      by (metis TESL.times_tag_const.simps)
    have "\<forall>t ta. \<tau>\<^sub>c\<^sub>s\<^sub>t (tt ta * t) = ta * \<tau>\<^sub>c\<^sub>s\<^sub>t t"
  using f1 by (metis (no_types) TESL.times_tag_const.simps)
    then have f3: "\<forall>t ta tb. \<tau>\<^sub>c\<^sub>s\<^sub>t (tb::'\<tau>) * t + t * \<tau>\<^sub>c\<^sub>s\<^sub>t ta = t * \<tau>\<^sub>c\<^sub>s\<^sub>t (tb + ta)"
      using f2 by (metis TESL.plus_tag_const.simps distrib_left semiring_normalization_rules(7))
  have f4: "\<forall>t ta. (ta::'\<tau> tag_const) * t = t * ta"
    using f2 f1 by (metis semiring_normalization_rules(7))
    have "\<forall>t ta tb. (tb::'\<tau> tag_const) * ta + ta * t = ta * (tb + t)"
      using f3 f1 by (metis TESL.plus_tag_const.simps)
    then have "c * a + c * b = c * (a + b)"
      using f4 by force
  then show "(a + b) * c = a * c + b * c"
    using f4 by auto
  qed
  show \<open>(0::('\<tau>::field tag_const)) \<noteq> 1\<close>
    by (simp add: one_tag_const_def zero_tag_const_def)
  show \<open>\<And>(a::('\<tau>::field tag_const)). a \<noteq> 0 \<Longrightarrow> inverse a * a = 1\<close>
  proof -
    { fix a::\<open>('\<tau>::field tag_const)\<close> assume \<open>a \<noteq> 0\<close>
      hence \<open>\<exists>t. t\<noteq>0 \<and> a = \<tau>\<^sub>c\<^sub>s\<^sub>t t\<close>
        by (metis (mono_tags, hide_lams) tag_const.exhaust zero_tag_const_def)
      from this obtain t where \<open>t \<noteq> 0\<close> and \<open>a = \<tau>\<^sub>c\<^sub>s\<^sub>t t\<close> by blast
      hence \<open>inverse a = \<tau>\<^sub>c\<^sub>s\<^sub>t (inverse t)\<close>
        by (simp add: TESL.inverse_tag_const.simps)
      hence \<open>inverse a * a = 1\<close> sledgehammer
        by (simp add: TESL.times_tag_const.simps \<open>a = \<tau>\<^sub>c\<^sub>s\<^sub>t t\<close> \<open>t \<noteq> 0\<close> one_tag_const_def)
    } thus \<open>\<And>(a::('\<tau>::field tag_const)). a \<noteq> 0 \<Longrightarrow> inverse a * a = 1\<close> by simp
  qed
  show \<open>\<And>(a::('\<tau>::field tag_const)) b. a div b = a * inverse b\<close>
  proof -
    { fix a b::\<open>('\<tau>::field tag_const)\<close>
      have \<open>\<exists>u. a = \<tau>\<^sub>c\<^sub>s\<^sub>t u\<close> using TESL.inverse_tag_const.cases by auto
      from this obtain u where au:\<open>a = \<tau>\<^sub>c\<^sub>s\<^sub>t u\<close> by blast
      have \<open>\<exists>v. b = \<tau>\<^sub>c\<^sub>s\<^sub>t v\<close> using TESL.inverse_tag_const.cases by auto
      from this obtain v where bv:\<open>b = \<tau>\<^sub>c\<^sub>s\<^sub>t v\<close> by blast
      from au bv have \<open>divide a b = \<tau>\<^sub>c\<^sub>s\<^sub>t (divide u v)\<close>
        by (simp add: TESL.divide_tag_const.simps)
      also have \<open>... = \<tau>\<^sub>c\<^sub>s\<^sub>t (times u (inverse v))\<close>
        by (simp add: divide_inverse)
      finally have \<open>divide a b = times a (inverse b)\<close>
        by (simp add: TESL.inverse_tag_const.simps TESL.times_tag_const.simps au bv)
    } thus \<open>\<And>(a::('\<tau>::field tag_const)) b. a div b = a * inverse b\<close> by simp
  qed
  show \<open>inverse (0::('\<tau>::field tag_const)) = 0\<close>
    by (simp add: TESL.inverse_tag_const.simps zero_tag_const_def)
qed

end

\<^cancel>\<open>
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
\<close>

instantiation tag_const :: (order)order
begin
  inductive less_eq_tag_const :: \<open>'a tag_const \<Rightarrow> 'a tag_const \<Rightarrow> bool\<close>
  where
    Int_less_eq[simp]:      \<open>n \<le> m \<Longrightarrow> (TConst n) \<le> (TConst m)\<close>

  definition less_tag: \<open>(x::'a tag_const) < y \<longleftrightarrow> (x \<le> y) \<and> (x \<noteq> y)\<close>

  instance proof
    show \<open>\<And>x y :: 'a tag_const. (x < y) = (x \<le> y \<and> \<not> y \<le> x)\<close>
      using less_eq_tag_const.simps less_tag by auto
  next
    { fix x::\<open>'a tag_const\<close>
      from tag_const.exhaust obtain x\<^sub>0::'a where xx0:\<open>x = TConst x\<^sub>0\<close> by blast
      with Int_less_eq have \<open>x \<le> x\<close> by simp
    } thus \<open>\<And>x::'a tag_const. x \<le> x\<close> .
  next
    show \<open>\<And>x y z  :: 'a tag_const. x \<le> y \<Longrightarrow> y \<le> z \<Longrightarrow> x \<le> z\<close>
      using less_eq_tag_const.simps by auto
  next
    show \<open>\<And>x y  :: 'a tag_const. x \<le> y \<Longrightarrow> y \<le> x \<Longrightarrow> x = y\<close>
      using less_eq_tag_const.simps by auto
  qed

end

instantiation tag_const :: (linorder)linorder
begin
  instance proof
    { fix x::\<open>'a tag_const\<close> and y::\<open>'a tag_const\<close>
      from tag_const.exhaust obtain x\<^sub>0::'a where \<open>x = TConst x\<^sub>0\<close> by blast
      moreover from tag_const.exhaust obtain y\<^sub>0::'a where \<open>y = TConst y\<^sub>0\<close> by blast
      ultimately have \<open>x \<le> y \<or> y \<le> x\<close> using less_eq_tag_const.simps by fastforce
    }
    thus \<open>\<And>x y. (x::'a tag_const) \<le> y \<or> y \<le> x\<close> .
  qed

end

end
