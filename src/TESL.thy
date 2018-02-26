theory TESL
imports Main

begin
text {* We define as follows the syntax of primitives to describe symbolic runs *}

(** Clocks **)
datatype clock = Clk "string"        (* ("\<lceil> _ \<rceil>") *)
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

datatype cnt_expr =
    NatCst "nat"
  | TickCountLe "clock" "instant_index"  ("#\<^sup><")
  | TickCountLeq "clock" "instant_index" ("#\<^sup>\<le>")
  | Plus "cnt_expr" "cnt_expr"
  | LTimes "nat" "cnt_expr"

(* Primitives for symbolic runs *)
datatype '\<tau> constr =
    Timestamp     "clock"   "instant_index" "'\<tau> tag_expr"          ("_ \<Down> _ @ _")
  | Ticks         "clock"   "instant_index"                       ("_ \<Up> _")
  | NotTicks      "clock"   "instant_index"                       ("_ \<not>\<Up> _")
  | NotTicksUntil "clock"   "instant_index"                       ("_ \<not>\<Up>\<^sup>< _")
  | NotTicksFrom  "clock"   "instant_index"                       ("_ \<not>\<Up>\<^sup>\<ge> _")
  | TagArith      "tag_var" "tag_var" "('\<tau> tag_const \<times> '\<tau> tag_const) \<Rightarrow> bool" ("\<lfloor>_, _\<rfloor> \<in> _")
  | TickCntArith  "cnt_expr" "cnt_expr" "(nat \<times> nat) \<Rightarrow> bool"               ("\<lceil>_, _\<rceil> \<in> _")
  | TickCntLeq    "cnt_expr" "cnt_expr"                           ("_ \<preceq> _")
  (* | Affine        "tag_var" "'\<tau> tag_const"     "tag_var" "'\<tau> tag_const" ("_ \<doteq> _ * _ + _") *)

type_synonym '\<tau> system = "'\<tau> constr list"

text{* Define as follows the syntax of TESL *}

(* TESL language *)
datatype '\<tau> TESL_atomic =
  (* Sporadic       "clock" "'\<tau> tag_const"                     (infixr "sporadic" 55) *)
    SporadicOn     "clock" "'\<tau> tag_expr"  "clock"             ("_ sporadic _ on _" 55)
  (* | TagRelationAff "clock" "'\<tau> tag_const" "clock" "'\<tau> tag_const" ("tag-relation _ = _ * _ + _" 55) *)
  | TagRelation    "clock" "clock" "('\<tau> tag_const \<times> '\<tau> tag_const) \<Rightarrow> bool" ("tag-relation \<lfloor>_, _\<rfloor> \<in> _" 55)
  | Implies        "clock" "clock"                         (infixr "implies" 55)
  | ImpliesNot     "clock" "clock"                         (infixr "implies not" 55)
  | TimeDelayedBy  "clock" "'\<tau> tag_const" "clock" "clock"     ("_ time-delayed by _ on _ implies _" 55)
  | Precedes       "clock" "clock"                         (infixr "precedes" 55)

type_synonym '\<tau> TESL_formula = "'\<tau> TESL_atomic list"

fun positive_atom :: "'\<tau> TESL_atomic \<Rightarrow> bool" where
    "positive_atom (_ sporadic _ on _) = True"
  | "positive_atom _                   = False"

abbreviation NoSporadic :: "'\<tau> TESL_formula \<Rightarrow> '\<tau> TESL_formula" where 
  "NoSporadic f \<equiv> (List.filter (\<lambda>f\<^sub>a\<^sub>t\<^sub>o\<^sub>m. case f\<^sub>a\<^sub>t\<^sub>o\<^sub>m of
      _ sporadic _ on _ \<Rightarrow> False
    | _ \<Rightarrow> True) f)"

(* The abstract machine
   Follows the intuition: past [\<Gamma>], current index [n], present [\<Psi>], future [\<Phi>]
   Beware: This type is slightly different from which originally implemented in Heron
*)
type_synonym '\<tau> config = "'\<tau> system * instant_index * '\<tau> TESL_formula * '\<tau> TESL_formula"

(*declare[[show_sorts]]*)

(* Instanciating tag_const to give field structure *)
instantiation tag_const :: (plus)plus
begin
  fun plus_tag_const :: "'a tag_const \<Rightarrow> 'a tag_const \<Rightarrow> 'a tag_const" where
      TConst_plus: "(TConst n) + (TConst p) = (TConst (n + p))"
  instance proof qed
end

instantiation tag_const :: (minus)minus
begin
  fun minus_tag_const :: "'a tag_const \<Rightarrow> 'a tag_const \<Rightarrow> 'a tag_const" where
      TConst_minus: "(TConst n) - (TConst p) = (TConst (n - p))"
  instance proof qed
end

instantiation tag_const :: (times)times
begin
  fun times_tag_const :: "'a tag_const \<Rightarrow> 'a tag_const \<Rightarrow> 'a tag_const" where
      TConst_times: "(TConst n) * (TConst p) = (TConst (n * p))"
  instance proof qed
end

instantiation tag_const :: (divide)divide
begin
  fun divide_tag_const :: "'a tag_const \<Rightarrow> 'a tag_const \<Rightarrow> 'a tag_const" where
      TConst_divide: "divide (TConst n) (TConst p) = (TConst (divide n p))"
  instance proof qed
end

instantiation tag_const :: (inverse)inverse
begin
  fun inverse_tag_const :: "'a tag_const \<Rightarrow> 'a tag_const" where
      TConst_inverse: "inverse (TConst n) = (TConst (inverse n))"
  instance proof qed
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