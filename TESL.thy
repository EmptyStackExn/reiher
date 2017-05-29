theory TESL
imports Main 

begin
text {* We define as follows the syntax of primitives to describe symbolic runs *}

(* Clocks *)
datatype clock = Clk "string"        ("\<lceil> _ \<rceil>")
type_synonym instant_index = "nat"

(* Tags *) 
datatype tag =
    Unit                              ("\<tau>\<^sub>u\<^sub>n\<^sub>i\<^sub>t")
  | Integer   "int"                   ("\<tau>\<^sub>i\<^sub>n\<^sub>t")
  | Schematic "clock * instant_index" ("\<tau>\<^sub>v\<^sub>a\<^sub>r")
  | Add       "tag * tag"

abbreviation is_concrete where
  "is_concrete \<tau> \<equiv> case \<tau> of Unit \<Rightarrow> True | Integer _ \<Rightarrow> True | _ \<Rightarrow> False"

(* Primitives for symbolic runs *)
datatype constr =
    Timestamp "clock" "instant_index" "tag" ("_ \<Down> _, _")
  | Ticks     "clock" "instant_index"       ("_ \<Up> _")
  | NotTicks  "clock" "instant_index"       ("_ \<not>\<Up> _")
  | Affine    "tag * tag * tag * tag"       ("\<doteq>")

type_synonym system = "constr list"

text{* Define as follows the syntax of TESL *}

(* TESL language *)
datatype TESL_atomic =
    Sporadic       "clock" "tag"                 (infixr "sporadic" 55)
  | TagRelation    "clock" "tag" "clock" "tag"   ("tag-relation _ = _ * _ + _" 55)
  | Implies        "clock" "clock"               (infixr "implies" 55)
  | TimeDelayedBy  "clock" "tag" "clock" "clock" ("_ time-delayed by _ on _ implies _" 55)
  | SporadicOn     "clock" "tag" "clock"         ("_ sporadic _ on _" 55)

type_synonym TESL_formula = "TESL_atomic list"

(* The abstract machine
   Follows the intuition: past [\<Gamma>], current index [n], present [\<psi>], future [\<phi>]
   Beware: This type is slightly different from which originally implemented in Heron
*)
type_synonym TESL_ARS_conf = "system * instant_index * TESL_formula * TESL_formula"


end