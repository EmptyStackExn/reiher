chapter\<open>A Gentle Introduction into the TESL Language\<close>

(*<*)
theory Introduction
  imports Main
begin

(*>*)

section \<open>Context\<close>
text\<open>
The design of complex systems involves different formalisms for modeling their different parts or 
aspects. The global model of a system may therefore consist of a coordination of concurrent 
sub-models that use differential equations, state machines, synchronous data-flow networks, 
discrete event models and so on. This raises the interest in architectural composition languages 
that allow for “bolting the respective sub-models together”, along their various interfaces, and 
specifying the various ways of collaboration and coordination~\cite{nguyenvan:hal-01583815}.

We are interested in languages that allow for specifying timed coordination of subsystems by 
addressing the following conceptual issues:
\<^item> events may occur in different sub-systems at unrelated times, leading to polychronous systems, 
  which do not necessarily have a base clock,
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
end
(*>*)