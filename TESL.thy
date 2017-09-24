theory TESL
imports Main Rat

begin
text {* We define as follows the syntax of primitives to describe symbolic runs *}

(** Clocks **)
datatype clock = Clk "string"        ("\<lceil> _ \<rceil>")
type_synonym instant_index = "nat"

(** Tags **) 
(* Constants *)
datatype tag_const =
    Rational   "rat"                   ("\<tau>\<^sub>r\<^sub>a\<^sub>t")
(* Variables *)
datatype tag_var =
    Schematic "clock * instant_index" ("\<tau>\<^sub>v\<^sub>a\<^sub>r")
(* Expressions *)
datatype tag_expr =
    Const    "tag_const"           ("\<lfloor> _ \<rfloor>")
  | AddDelay "tag_var" "tag_const" ("\<lfloor> _ \<oplus> _ \<rfloor>")

(* Primitives for symbolic runs *)
datatype constr =
    Timestamp "clock"   "instant_index" "tag_expr"            ("_ \<Down> _ @ _")
  | Ticks     "clock"   "instant_index"                       ("_ \<Up> _")
  | NotTicks  "clock"   "instant_index"                       ("_ \<not>\<Up> _")
  | Affine    "tag_var" "tag_const"     "tag_var" "tag_const" ("_ \<doteq> _ * _ + _")

type_synonym system = "constr list"

text{* Define as follows the syntax of TESL *}

(* TESL language *)
datatype TESL_atomic =
    Sporadic       "clock" "tag_const"                     (infixr "sporadic" 55)
  | SporadicOn     "clock" "tag_expr"  "clock"             ("_ sporadic _ on _" 55)
  | TagRelation    "clock" "tag_const" "clock" "tag_const" ("tag-relation _ = _ * _ + _" 55)
  | Implies        "clock" "clock"                         (infixr "implies" 55)
  | TimeDelayedBy  "clock" "tag_const" "clock" "clock"     ("_ time-delayed by _ on _ implies _" 55)

type_synonym TESL_formula = "TESL_atomic list"

fun positive_atom :: "TESL_atomic \<Rightarrow> bool" where
    "positive_atom (_ sporadic _)      = True"
  | "positive_atom (_ sporadic _ on _) = True"
  | "positive_atom _                   = False"

abbreviation NoSporadic :: "TESL_formula \<Rightarrow> TESL_formula" where 
  "NoSporadic f \<equiv> (List.filter (\<lambda>f\<^sub>a\<^sub>t\<^sub>o\<^sub>m. case f\<^sub>a\<^sub>t\<^sub>o\<^sub>m of
      _ sporadic _  \<Rightarrow> False
    | _ sporadic _ on _ \<Rightarrow> False
    | _ \<Rightarrow> True) f)"

(* The abstract machine
   Follows the intuition: past [\<Gamma>], current index [n], present [\<psi>], future [\<phi>]
   Beware: This type is slightly different from which originally implemented in Heron
*)
type_synonym config = "system * instant_index * TESL_formula * TESL_formula"

(*declare[[show_sorts]]*)

(* Instanciating tag_const to give field structure *)
instantiation tag_const :: plus
begin
  fun plus_tag_const :: "tag_const \<Rightarrow> tag_const \<Rightarrow> tag_const" where
      Rational_plus: "(Rational n) + (Rational p) = (Rational (n + p))"
  instance proof qed
end

instantiation tag_const :: minus
begin
  fun minus_tag_const :: "tag_const \<Rightarrow> tag_const \<Rightarrow> tag_const" where
      Rational_minus: "(Rational n) - (Rational p) = (Rational (n - p))"
  instance proof qed
end

instantiation tag_const :: times
begin
  fun times_tag_const :: "tag_const \<Rightarrow> tag_const \<Rightarrow> tag_const" where
      Rational_times: "(Rational n) * (Rational p) = (Rational (n * p))"
  instance proof qed
end

instantiation tag_const :: divide
begin
  fun divide_tag_const :: "tag_const \<Rightarrow> tag_const \<Rightarrow> tag_const" where
      Rational_divide: "divide (Rational n) (Rational p) = (Rational (divide n p))"
  instance proof qed
end

instantiation tag_const :: inverse
begin
  fun inverse_tag_const :: "tag_const \<Rightarrow> tag_const" where
      Rational_inverse: "inverse (Rational n) = (Rational (inverse n))"
  instance proof qed
end

instantiation tag_const :: order
begin
  inductive less_eq_tag_const :: "tag_const \<Rightarrow> tag_const \<Rightarrow> bool" where
    Int_less_eq[simp]:      "n \<le> m \<Longrightarrow> (Rational n) \<le> (Rational m)"
  definition less_tag: "(x::tag_const) < y \<longleftrightarrow> (x \<le> y) \<and> (x \<noteq> y)"
  instance proof
    show "\<And>x y :: tag_const. (x < y) = (x \<le> y \<and> \<not> y \<le> x)"
      using less_eq_tag_const.simps less_tag by auto
    show "\<And>x  :: tag_const. x \<le> x"
      by (metis (full_types) Int_less_eq order_refl tag_const.exhaust)
    show "\<And>x y z  :: tag_const. x \<le> y \<Longrightarrow> y \<le> z \<Longrightarrow> x \<le> z"
      using less_eq_tag_const.simps by auto
    show "\<And>x y  :: tag_const. x \<le> y \<Longrightarrow> y \<le> x \<Longrightarrow> x = y"
      using less_eq_tag_const.simps by auto
  qed
end

instantiation tag_const :: linorder
begin
  instance proof
    show "\<And>x y. (x::tag_const) \<le> y \<or> y \<le> x"
      by (metis (full_types) Int_less_eq le_cases tag_const.exhaust)
  qed
end

end