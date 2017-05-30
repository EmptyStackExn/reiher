theory TESL
imports Main 

begin
text {* We define as follows the syntax of primitives to describe symbolic runs *}

(** Clocks **)
datatype clock = Clk "string"        ("\<lceil> _ \<rceil>")
type_synonym instant_index = "nat"

(** Tags **) 
(* Constants *)
datatype tag_const =
    Unit                              ("\<tau>\<^sub>u\<^sub>n\<^sub>i\<^sub>t")
  | Integer   "int"                   ("\<tau>\<^sub>i\<^sub>n\<^sub>t")
(* Variables *)
datatype tag_var =
    Schematic "clock * instant_index" ("\<tau>\<^sub>v\<^sub>a\<^sub>r")
(* Expressions *)
datatype tag_expr =
    Const    "tag_const"           ("\<lfloor> _ \<rfloor>")
  | AddDelay "tag_var" "tag_const" ("\<lfloor> _ \<oplus> _ \<rfloor>")

(* Primitives for symbolic runs *)
datatype constr =
    Timestamp "clock" "instant_index" "tag_expr"          ("_ \<Down> _ @ _")
  | Ticks     "clock" "instant_index"                     ("_ \<Up> _")
  | NotTicks  "clock" "instant_index"                     ("_ \<not>\<Up> _")
  | Affine    "tag_var" "tag_const" "tag_var" "tag_const" ("_ \<doteq> _ * _ + _")

type_synonym system = "constr list"

text{* Define as follows the syntax of TESL *}

(* TESL language *)
datatype TESL_atomic =
    Sporadic       "clock" "tag_const"                     (infixr "sporadic" 55)
  | TagRelation    "clock" "tag_const" "clock" "tag_const" ("tag-relation _ = _ * _ + _" 55)
  | Implies        "clock" "clock"                         (infixr "implies" 55)
  | TimeDelayedBy  "clock" "tag_const" "clock" "clock"     ("_ time-delayed by _ on _ implies _" 55)
  | SporadicOn     "clock" "tag_expr" "clock"              ("_ sporadic _ on _" 55)

type_synonym TESL_formula = "TESL_atomic list"

(* The abstract machine
   Follows the intuition: past [\<Gamma>], current index [n], present [\<psi>], future [\<phi>]
   Beware: This type is slightly different from which originally implemented in Heron
*)
type_synonym TESL_ARS_conf = "system * instant_index * TESL_formula * TESL_formula"

(* Instanciating tag_const to give some kind of semi-ring structure *)
instantiation tag_const :: plus
begin
  fun plus_tag_const :: "tag_const \<Rightarrow> tag_const \<Rightarrow> tag_const" where
      Unit_plus:    "Unit + Unit = Unit"
    | Integer_plus: "(Integer n) + (Integer p) = (Integer (n + p))"
  instance proof qed
end

instantiation tag_const :: times
begin
  fun times_tag_const :: "tag_const \<Rightarrow> tag_const \<Rightarrow> tag_const" where
      Unit_times:    "Unit * Unit = Unit"
    | Integer_times: "(Integer n) * (Integer p) = (Integer (n * p))"
  instance proof qed
end

instantiation tag_const :: order
begin
  inductive less_eq_tag_const :: "tag_const \<Rightarrow> tag_const \<Rightarrow> bool" where
    Int_less_eq[simp]:  "n \<le> m \<Longrightarrow> (Integer n) \<le> (Integer m)"
  | Unit_less_eq[simp]: "Unit \<le> Unit"
  definition less_tag: "(x::tag_const) < y \<longleftrightarrow> (x \<le> y) \<and> (x \<noteq> y)"
  instance proof
    show "\<And>x y :: tag_const. (x < y) = (x \<le> y \<and> \<not> y \<le> x)"
      using less_eq_tag_const.simps less_tag by auto
    show "\<And>x  :: tag_const. x \<le> x"
      using [[smt_solver = cvc4]]
      by (smt less_eq_tag_const.simps times_tag_const.elims)
    show "\<And>x y z  :: tag_const. x \<le> y \<Longrightarrow> y \<le> z \<Longrightarrow> x \<le> z"
      using less_eq_tag_const.simps by auto
    show "\<And>x y  :: tag_const. x \<le> y \<Longrightarrow> y \<le> x \<Longrightarrow> x = y"
      using less_eq_tag_const.simps by auto
  qed
end

end