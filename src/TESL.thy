theory TESL
imports Main Rat Real

begin
text {* We define as follows the syntax of primitives to describe symbolic runs *}

(** Clocks **)
datatype '\<kappa> clock = Clk "'\<kappa>"        ("\<lceil> _ \<rceil>")
type_synonym instant_index = "nat"

(** Tags **) 
(* Constants *)
datatype '\<tau> tag_const =
    CConst   "'\<tau>"                   ("\<tau>\<^sub>r\<^sub>a\<^sub>t")
(* Variables *)
datatype '\<kappa> tag_var =
    Schematic "'\<kappa> clock * instant_index" ("\<tau>\<^sub>v\<^sub>a\<^sub>r")
(* Expressions *)
datatype ('\<kappa>, '\<tau>) tag_expr =
    Const    "'\<tau> tag_const"           ("\<lfloor> _ \<rfloor>")
  | AddDelay "'\<kappa> tag_var" "'\<tau> tag_const" ("\<lfloor> _ \<oplus> _ \<rfloor>")

(* Primitives for symbolic runs *)
datatype ('\<kappa>, '\<tau>) constr =
    Timestamp "'\<kappa> clock"   "instant_index" "('\<kappa>, '\<tau>) tag_expr"            ("_ \<Down> _ @ _")
  | Ticks     "'\<kappa> clock"   "instant_index"                       ("_ \<Up> _")
  | NotTicks  "'\<kappa> clock"   "instant_index"                       ("_ \<not>\<Up> _")
  | Affine    "'\<kappa> tag_var" "'\<tau> tag_const"     "'\<kappa> tag_var" "'\<tau> tag_const" ("_ \<doteq> _ * _ + _")
  | ArithGen  "'\<kappa> tag_var" "'\<kappa> tag_var" "('\<tau> tag_const \<times> '\<tau> tag_const) \<Rightarrow> bool" ("\<langle>_, _\<rangle> \<epsilon> _")

type_synonym ('\<kappa>, '\<tau>) system = "('\<kappa>, '\<tau>) constr list"

text{* Define as follows the syntax of TESL *}

(* TESL language *)
datatype ('\<kappa>, '\<tau>) TESL_atomic =
    Sporadic       "'\<kappa> clock" "'\<tau> tag_const"                     (infixr "sporadic" 55)
  | SporadicOn     "'\<kappa> clock" "('\<kappa>, '\<tau>) tag_expr"  "'\<kappa> clock"             ("_ sporadic _ on _" 55)
  | TagRelation    "'\<kappa> clock" "'\<tau> tag_const" "'\<kappa> clock" "'\<tau> tag_const" ("tag-relation _ = _ * _ + _" 55)
  | TagRelationGen "'\<kappa> clock" "'\<kappa> clock" "('\<tau> tag_const \<times> '\<tau> tag_const) \<Rightarrow> bool" ("tag-relation \<langle>_, _\<rangle> \<in> _" 55)
  | Implies        "'\<kappa> clock" "'\<kappa> clock"                         (infixr "implies" 55)
  | TimeDelayedBy  "'\<kappa> clock" "'\<tau> tag_const" "'\<kappa> clock" "'\<kappa> clock"     ("_ time-delayed by _ on _ implies _" 55)

type_synonym ('\<kappa>, '\<tau>) TESL_formula = "('\<kappa>, '\<tau>) TESL_atomic list"

fun positive_atom :: "('\<kappa>, '\<tau>::{plus,minus,times,divide,inverse,order,linorder}) TESL_atomic \<Rightarrow> bool" where
    "positive_atom (_ sporadic _)      = True"
  | "positive_atom (_ sporadic _ on _) = True"
  | "positive_atom _                   = False"

abbreviation NoSporadic :: "('\<kappa>, '\<tau>::{plus,minus,times,divide,inverse,order,linorder}) TESL_formula \<Rightarrow> ('\<kappa>, '\<tau>) TESL_formula" where 
  "NoSporadic f \<equiv> (List.filter (\<lambda>f\<^sub>a\<^sub>t\<^sub>o\<^sub>m. case f\<^sub>a\<^sub>t\<^sub>o\<^sub>m of
      _ sporadic _  \<Rightarrow> False
    | _ sporadic _ on _ \<Rightarrow> False
    | _ \<Rightarrow> True) f)"

(* The abstract machine
   Follows the intuition: past [\<Gamma>], current index [n], present [\<psi>], future [\<phi>]
   Beware: This type is slightly different from which originally implemented in Heron
*)
type_synonym ('\<kappa>, '\<tau>) config = "('\<kappa>, '\<tau>) system * instant_index * ('\<kappa>, '\<tau>) TESL_formula * ('\<kappa>, '\<tau>) TESL_formula"

(*declare[[show_sorts]]*)

(* Instanciating tag_const to give field structure *)
instantiation tag_const :: (plus)plus
begin
  fun plus_tag_const :: "'a tag_const \<Rightarrow> 'a tag_const \<Rightarrow> 'a tag_const" where
      CConst_plus: " (CConst n) + (CConst p) = (CConst (n + p))"
  instance proof qed
end

instantiation tag_const :: (minus)minus
begin
  fun minus_tag_const :: "'a tag_const \<Rightarrow> 'a tag_const \<Rightarrow> 'a tag_const" where
      CConst_minus: "(CConst n) - (CConst p) = (CConst (n - p))"
  instance proof qed
end

instantiation tag_const :: (times)times
begin
  fun times_tag_const :: "'a tag_const \<Rightarrow> 'a tag_const \<Rightarrow> 'a tag_const" where
      CConst_times: "(CConst n) * (CConst p) = (CConst (n * p))"
  instance proof qed
end

instantiation tag_const :: (divide)divide
begin
  fun divide_tag_const :: "'a tag_const \<Rightarrow> 'a tag_const \<Rightarrow> 'a tag_const" where
      CConst_divide: "divide (CConst n) (CConst p) = (CConst (divide n p))"
  instance proof qed
end

instantiation tag_const :: (inverse)inverse
begin
  fun inverse_tag_const :: "'a tag_const \<Rightarrow> 'a tag_const" where
      CConst_inverse: "inverse (CConst n) = (CConst (inverse n))"
  instance proof qed
end

instantiation tag_const :: (order)order
begin
  inductive less_eq_tag_const :: "'a tag_const \<Rightarrow> 'a tag_const \<Rightarrow> bool" where
    Int_less_eq[simp]:      "n \<le> m \<Longrightarrow> (CConst n) \<le> (CConst m)"
  definition less_tag_const :: "'a tag_const \<Rightarrow> 'a tag_const \<Rightarrow> bool" where
    "less_tag_const x y \<longleftrightarrow> (x \<le> y) \<and> (x \<noteq> y)" (* NORMAL ? *)
  instance proof
    show "\<And>x y :: 'a tag_const. (x < y) = (x \<le> y \<and> \<not> y \<le> x)"
      using less_eq_tag_const.simps less_tag_const_def by auto
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