chapter\<open>The Core of the TESL Language: Syntax and Basics\<close>

theory TESL
imports Main

begin

section\<open>Syntactic Representation\<close>
text {* We define as follows the syntax of primitives to describe symbolic runs *}

(** Clocks **)
datatype     clock         = Clk "string"
type_synonym instant_index = "nat"

(** Tags **) 
(* Constants *)
datatype '\<tau> tag_const =
    TConst   '\<tau>                    ("\<tau>\<^sub>c\<^sub>s\<^sub>t")
(* Variables *)
datatype tag_var =
    TSchematic "clock * instant_index" ("\<tau>\<^sub>v\<^sub>a\<^sub>r")
(* Expressions *)
datatype '\<tau> tag_expr =
    Const    "'\<tau> tag_const"          ("\<lparr> _ \<rparr>")
  | AddDelay "tag_var" "'\<tau> tag_const" ("\<lparr> _ \<oplus> _ \<rparr>")

text{* Define as follows the syntax of TESL *}

subsection\<open>Operators for the TESL language\<close> 
datatype '\<tau> TESL_atomic =
    SporadicOn     "clock" "'\<tau> tag_expr"  "clock"             ("_ sporadic _ on _" 55)
  | TagRelation    "clock" "clock" "('\<tau> tag_const \<times> '\<tau> tag_const) \<Rightarrow> bool" ("time-relation \<lfloor>_, _\<rfloor> \<in> _" 55)
  | Implies        "clock" "clock"                         (infixr "implies" 55)
  | ImpliesNot     "clock" "clock"                         (infixr "implies not" 55)
  | TimeDelayedBy  "clock" "'\<tau> tag_const" "clock" "clock"     ("_ time-delayed by _ on _ implies _" 55)
  | WeaklyPrecedes "clock" "clock"                         (infixr "weakly precedes" 55)
  | StrictlyPrecedes "clock" "clock"                       (infixr "strictly precedes" 55)
  | Kills          "clock" "clock"                         (infixr "kills" 55)

type_synonym '\<tau> TESL_formula = "'\<tau> TESL_atomic list"

fun positive_atom :: "'\<tau> TESL_atomic \<Rightarrow> bool" where
    "positive_atom (_ sporadic _ on _) = True"
  | "positive_atom _                   = False"

abbreviation NoSporadic :: "'\<tau> TESL_formula \<Rightarrow> '\<tau> TESL_formula" where 
  "NoSporadic f \<equiv> (List.filter (\<lambda>f\<^sub>a\<^sub>t\<^sub>o\<^sub>m. case f\<^sub>a\<^sub>t\<^sub>o\<^sub>m of
      _ sporadic _ on _ \<Rightarrow> False
    | _ \<Rightarrow> True) f)"


(* Instanciating tag_const to give field structure *)
instantiation tag_const :: (plus)plus
begin
  fun plus_tag_const :: "'a tag_const \<Rightarrow> 'a tag_const \<Rightarrow> 'a tag_const" where
      TConst_plus: "(TConst n) + (TConst p) = (TConst (n + p))"
  instance by (rule Groups.class.Groups.plus.of_class.intro)
end

instantiation tag_const :: (minus)minus
begin
  fun minus_tag_const :: "'a tag_const \<Rightarrow> 'a tag_const \<Rightarrow> 'a tag_const" where
      TConst_minus: "(TConst n) - (TConst p) = (TConst (n - p))"
  instance by (rule Groups.class.Groups.minus.of_class.intro)
end

instantiation tag_const :: (times)times
begin
  fun times_tag_const :: "'a tag_const \<Rightarrow> 'a tag_const \<Rightarrow> 'a tag_const" where
      TConst_times: "(TConst n) * (TConst p) = (TConst (n * p))"
  instance by (rule Groups.class.Groups.times.of_class.intro)
end

instantiation tag_const :: (divide)divide
begin
  fun divide_tag_const :: "'a tag_const \<Rightarrow> 'a tag_const \<Rightarrow> 'a tag_const" where
      TConst_divide: "divide (TConst n) (TConst p) = (TConst (divide n p))"
  instance by (rule Rings.class.Rings.divide.of_class.intro)
end

instantiation tag_const :: (inverse)inverse
begin
  fun inverse_tag_const :: "'a tag_const \<Rightarrow> 'a tag_const" where
      TConst_inverse: "inverse (TConst n) = (TConst (inverse n))"
  instance by (rule Fields.class.Fields.inverse.of_class.intro)
end

instantiation tag_const :: (order)order
begin
  inductive less_eq_tag_const :: "'a tag_const \<Rightarrow> 'a tag_const \<Rightarrow> bool" where
    Int_less_eq[simp]:      "n \<le> m \<Longrightarrow> (TConst n) \<le> (TConst m)"
  definition less_tag: "(x::'a tag_const) < y \<longleftrightarrow> (x \<le> y) \<and> (x \<noteq> y)"
  instance proof
    show "\<And>x y :: 'a tag_const. (x < y) = (x \<le> y \<and> \<not> y \<le> x)"
      using less_eq_tag_const.simps less_tag by auto
    show "\<And>x  :: 'a tag_const. x \<le> x"
      by (metis (full_types) Int_less_eq order_refl tag_const.exhaust)
    show "\<And>x y z  :: 'a tag_const. x \<le> y \<Longrightarrow> y \<le> z \<Longrightarrow> x \<le> z"
      using less_eq_tag_const.simps by auto
    show "\<And>x y  :: 'a tag_const. x \<le> y \<Longrightarrow> y \<le> x \<Longrightarrow> x = y"
      using less_eq_tag_const.simps by auto
  qed
end

instantiation tag_const :: (linorder)linorder
begin
  instance proof
    show "\<And>x y. (x::'a tag_const) \<le> y \<or> y \<le> x"
      by (metis (full_types) Int_less_eq le_cases tag_const.exhaust)
  qed
end

end