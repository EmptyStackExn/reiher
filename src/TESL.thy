theory TESLTypes
imports Main

begin

text {* We define as follows the syntax of the Horn Affine Arithmetic *}

datatype clock = Clk "int"
type_synonym instant_index = "int"

datatype tag =
    Integer   "int"
  | Unit
  | Schematic "clock * instant_index"
  | Add       "tag * tag"

datatype HAA_atomic =
    Timestamp "clock * instant_index * tag"
  | Ticks     "clock * instant_index"
  | NotTicks  "clock * instant_index"
  | Affine    "tag * tag * tag * tag"

type_synonym HAA_system = "HAA_atomic set"

text{* Define as follows the syntax of TESL *}

datatype TESL_atomic =
    Sporadic       "clock * tag"
  | TagRelation    "clock * tag * clock * tag"
  | Implies        "clock * clock"
  | TimeDelayedBy  "clock * tag * clock * clock"
  | WhenTickingOn  "clock * tag * clock"           (* Intermediate Form *)
  | DelayedBy      "clock * int * clock * clock"
  | TimesImpliesOn "clock * int * clock"           (* Intermediate Form *)
  | FilteredBy     "clock * int * int * int * int * clock"
  | SustainedFrom  "clock * clock * clock * clock"
  | UntilRestart   "clock * clock * clock * clock" (* Intermediate Form *)
  | Await          "clock list * clock list * clock list * clock"
  | WhenClock      "clock * clock * clock"
  | WhenNotClock   "clock * clock * clock"

type_synonym TESL_formula = "TESL_atomic set"

text{* Define as follows syntax and operations over ARS *}
type_synonym TESL_ARS_conf = "HAA_system * instant_index * TESL_formula * TESL_formula"

abbreviation ConstantlySubs where 
  "ConstantlySubs f \<equiv> { f\<^sub>a \<in> f. case f\<^sub>a of
    Implies _      \<Rightarrow> True
  | TagRelation _  \<Rightarrow> True
  | WhenClock _    \<Rightarrow> True
  | WhenNotClock _ \<Rightarrow> True
  | _ \<Rightarrow> False }"
abbreviation ConsumingSubs where 
  "ConsumingSubs f \<equiv> { f\<^sub>a \<in> f. case f\<^sub>a of
    Sporadic _       \<Rightarrow> True
  | WhenTickingOn _  \<Rightarrow> True
  | TimesImpliesOn _ \<Rightarrow> True
  | _ \<Rightarrow> False }"
abbreviation ReproductiveSubs where 
  "ReproductiveSubs f \<equiv> { f\<^sub>a \<in> f. case f\<^sub>a of
    DelayedBy _     => True
  | TimeDelayedBy _ => True
  | _ \<Rightarrow> False }"
abbreviation SelfModifyingSubs where 
  "SelfModifyingSubs f \<equiv> { f\<^sub>a \<in> f. case f\<^sub>a of
    TimesImpliesOn _ => True
  | FilteredBy _     => True
  | SustainedFrom _  => True
  | UntilRestart _   => True
  | Await _          => True
  | _ \<Rightarrow> False }"

(* Asserts if two tags have the same type *)
abbreviation tags_have_same_type ("_ \<sim>: _") where
  "\<tau> \<sim>: \<tau>' \<equiv> (case (\<tau>, \<tau>') of
    (Integer _, Integer _) \<Rightarrow> True
  | (Unit, Unit)           \<Rightarrow> True
  | _                      \<Rightarrow> False)"

(* Asserts if two tags have the same type *)
abbreviation tags_leq ("_ \<le>: _") where
  "\<tau> \<le>: \<tau>' \<equiv> (case (\<tau>, \<tau>') of
    (Integer i1, Integer i2) \<Rightarrow> i1 \<le> i2
  | (Unit, Unit)             \<Rightarrow> True
  | _                        \<Rightarrow> False)"

(* Decides if two configurations are structurally equivalent *)
abbreviation ARS_cfg_eq :: "TESL_ARS_conf \<Rightarrow> TESL_ARS_conf \<Rightarrow> bool" ("_ @\<equiv> _") where
  "cf1 @\<equiv> cf2 \<equiv> case (cf1, cf2) of ((\<Gamma>\<^sub>1, s\<^sub>1, \<phi>\<^sub>1, \<psi>\<^sub>1), (\<Gamma>\<^sub>2, s\<^sub>2, \<phi>\<^sub>2, \<psi>\<^sub>2)) \<Rightarrow>
    (\<Gamma>\<^sub>1 = \<Gamma>\<^sub>2) \<and> (s\<^sub>1 = s\<^sub>2) \<and> (\<phi>\<^sub>1 = \<phi>\<^sub>2) \<and> (\<psi>\<^sub>1 = \<psi>\<^sub>2)"

  (*
function fpx :: "('a \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> 'a"  where
  "fpx ff x = (let x' = (ff x) 
               in  if x = x' then x 
                             else fpx (ff) x' 
              )"
by pat_completeness auto
*)
  
function fpx :: "('a \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> 'a"  where
  "fpx ff x = (let x' = (ff x) 
               in  if x = x' then x 
                             else fpx (ff) x' 
              )"
by pat_completeness auto
termination
  sorry
  
value "(fpx (\<lambda>x. x) []) = []"


(* value "ConstantlySubs { Sporadic(Clk (1::int), Integer 1), Implies (Clk 1, Clk 2) }" *)

end