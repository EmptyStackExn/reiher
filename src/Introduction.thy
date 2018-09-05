chapter\<open>A Gentle Introduction to TESL\<close>

(*<*)
theory Introduction
  imports Main
begin

(*>*)

section \<open>Context\<close>
text\<open>
The design of complex systems involves different formalisms for modeling their different parts or 
aspects. The global model of a system may therefore consist of a coordination of concurrent 
sub-models that use different paradigms such as differential equations, state machines, 
synchronous data-flow networks, 
discrete event models and so on, as illustrated in \autoref{fig:het-timed-system}. 
This raises the interest in architectural composition languages 
that allow for ``bolting the respective sub-models together'', along their various interfaces, and 
specifying the various ways of collaboration and coordination~@{cite "nguyenvan:hal-01583815"}.

We are interested in languages that allow for specifying the timed coordination of subsystems by 
addressing the following conceptual issues:
\<^item> events may occur in different sub-systems at unrelated times, leading to polychronous systems, 
  which do not necessarily have a common base clock,
\<^item> the behavior of the sub-systems is observed only at a series of discrete instants, and time 
  coordination has to take this discretization into account,
\<^item> the instants at which a system is observed may be arbitrary and should not change its behavior 
  (stuttering invariance),
\<^item> coordination between subsystems involves causality, so the occurrence of an event may enforce 
  the occurrence of other events, possibly after a certain duration has elapsed or an event has 
  occurred a given number of times,
\<^item> the domain of time (discrete, rational, continuous,. . . ) may be different in the subsystems, 
  leading to polytimed systems,
\<^item> the time frames of different sub-systems may be related (for instance, time in a GPS satellite 
  and in a GPS receiver on Earth are related although they are not the same).
\<close>

text\<open>
\begin{figure}[htbp]
 \centering
 \includegraphics{glue.pdf}
 \caption{A Heterogeneous Timed System Model}
 \label{fig:het-timed-system}
\end{figure}\<close>

(*<*)
consts dummyInfty :: "'a \<Rightarrow> 'a"   ("(_\<^sup>\<infinity>)" [1000] 999)
consts dummyTESLSTAR :: "'a"          ("TESL\<^sup>*")
consts dummyFUN   :: "'a set \<Rightarrow> 'b set \<Rightarrow> 'c set"          (infixl "\<rightarrow>" 100)
consts dummyCLOCK :: "'a set"     ("\<K>") 
consts dummyBOOL :: "bool set"     ("\<bool>") 
consts dummyTIMES :: "'a set"      ("\<T>") 
consts dummyLEQ   :: "'a \<Rightarrow> 'a \<Rightarrow> bool"          (infixl "\<le>\<^sub>\<T>" 100)

(*>*)

text\<open>
In order to tackle the heterogeneous nature of the subsystems, we abstract their behavior as clocks. 
Each clock models an event – something that can occur or not at a given time. This time is measured 
in a time frame associated with each clock, and the nature of time (integer, rational, real or any 
type with a linear order) is specific to each clock. 
When the event associated with a clock occurs, the clock ticks. In order to support any kind of 
behavior for the subsystems, we are only interested in specifying what we can observe at a series 
of discrete instants. There are two constraints on observations: a clock may tick only at an 
observation instant, and the time on any clock cannot decrease from an instant to the next one. 
However, it is always possible to add arbitrary observation instants, which allows for stuttering 
and modular composition of systems. 
As a consequence, the key concept of our setting is the notion of a clock-indexed Kripke model: 
@{term "\<Sigma>\<^sup>\<infinity> = \<nat> \<rightarrow> \<K> \<rightarrow> (\<bool> \<times> \<T>)"}, where @{term "\<K>"} is an enumerable set of clocks, @{term "\<bool>"} 
is the set of booleans – used to  indicate that a clock ticks at a given instant – and @{term "\<T>"} 
is a universal metric time space for which we only assume that it is large enough to contain all 
individual time spaces of clocks and that it is ordered by some linear ordering @{term "(\<le>\<^sub>\<T>)"}.
\<close>

text\<open>
  The elements of @{term "\<Sigma>\<^sup>\<infinity>"} are called runs. A specification language is a set of 
  operators that constrains the set of possible monotonic runs. Specifications are composed by 
  intersecting the denoted run sets of constraint operators.
  Consequently, such specification languages do not limit the number of clocks used to model a 
  system (as long as it is finite) and it is always possible to add clocks to a specification. 
  Moreover they are compositional by construction since the composition of specifications 
  consists of the conjunction of their constraints.
\<close>

text\<open>
  This work provides the following contributions:
  \<^item> defining the non-trivial language @{term "TESL\<^sup>*"} in terms of clock-indexed Kripke models, 
  \<^item> proving that this denotational semantics is stuttering invariant,
  \<^item> defining an adapted form of symbolic primitives and presenting the set of operational semantic rules,
  \<^item> presenting formal proofs for soundness, completeness, and progress of the latter.
\<close>

section\<open>The TESL Language\<close>
   
text\<open>
  The TESL language was initially designed to coordinate the execution of heterogeneous components
  during the simulation of a system \<^cancel>\<open>@{cite "XXX"}\<close>. We define here a minimal kernel of operators 
  that will form the basis of a family of specification languages, including the original TESL 
  language.
\<close>  
   
(*<*)
no_notation dummyInfty      ("(_\<^sup>\<infinity>)" )
no_notation dummyTESLSTAR   ("TESL\<^sup>*")
no_notation dummyFUN        (infixl "\<rightarrow>" 100)
no_notation dummyCLOCK      ("\<K>") 
no_notation dummyBOOL       ("\<bool>") 
no_notation dummyTIMES      ("\<T>") 
no_notation dummyLEQ        (infixl "\<le>\<^sub>\<T>" 100)


end
(*>*)