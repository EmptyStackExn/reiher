theory Hygge_Theory
imports
  "Hygge"
  "Denotational"

begin
(** TODO list of desired properties
  - Soundness
  - Completeness
  - Termination
  - Composition
  - Decidability
*)


(**) section \<open>Soundness\<close> (**)

(* For each reduction step, the formula [\<psi>] in elimination, produces
     1. Two primitives         [\<gamma>\<^sub>1] and [\<gamma>\<^sub>2]
     2. A residual formula     [\<psi>\<^sub>n\<^sub>o\<^sub>w]
     3. A continuation formula [\<psi>\<^sub>f\<^sub>u\<^sub>t]
   Their combination is a refinement of the eliminated formula.
*)
theorem elimination_soundness:
  assumes "\<Gamma>, n \<turnstile> \<psi> # \<Psi> \<triangleright> \<Phi>  \<hookrightarrow>  \<gamma>\<^sub>1 # \<gamma>\<^sub>2 # \<Gamma>, n \<turnstile> \<psi>\<^sub>n\<^sub>o\<^sub>w # \<Psi> \<triangleright> \<psi>\<^sub>f\<^sub>u\<^sub>t # \<Phi>"
  shows "\<lbrakk> \<psi> \<nabla> n \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L \<supseteq> \<lbrakk> \<gamma>\<^sub>1 \<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n \<inter> \<lbrakk> \<gamma>\<^sub>2 \<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n \<inter> \<lbrakk> \<psi>\<^sub>n\<^sub>o\<^sub>w \<nabla> n \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L \<inter> \<lbrakk> \<psi>\<^sub>f\<^sub>u\<^sub>t \<nabla> Suc n \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L"
  proof (insert assms, erule operational_semantics_step.cases)
    show "\<And>\<Gamma>' na \<Phi>'.
       (\<Gamma>, n \<turnstile> \<psi> # \<Psi> \<triangleright> \<Phi>) = (\<Gamma>', na \<turnstile> [] \<triangleright> \<Phi>') \<Longrightarrow>
       (\<gamma>\<^sub>1 # \<gamma>\<^sub>2 # \<Gamma>, n \<turnstile> \<psi>\<^sub>n\<^sub>o\<^sub>w # \<Psi> \<triangleright> \<psi>\<^sub>f\<^sub>u\<^sub>t # \<Phi>) = (\<Gamma>', Suc na \<turnstile> \<Phi>' \<triangleright> []) \<Longrightarrow>
       consistent_run \<Gamma>' \<Longrightarrow>
       \<lbrakk> \<gamma>\<^sub>1 \<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n \<inter> \<lbrakk> \<gamma>\<^sub>2 \<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n \<inter> \<lbrakk> \<psi>\<^sub>n\<^sub>o\<^sub>w \<nabla> n \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L \<inter> \<lbrakk> \<psi>\<^sub>f\<^sub>u\<^sub>t \<nabla> Suc n \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L \<subseteq> \<lbrakk> \<psi> \<nabla> n \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L"
      by simp
    show "\<And>\<Gamma>' na K \<tau> \<Psi>' \<Phi>'.
       (\<Gamma>, n \<turnstile> \<psi> # \<Psi> \<triangleright> \<Phi>) = (\<Gamma>', na \<turnstile> (K sporadic \<tau>) # \<Psi>' \<triangleright> \<Phi>') \<Longrightarrow>
       (\<gamma>\<^sub>1 # \<gamma>\<^sub>2 # \<Gamma>, n \<turnstile> \<psi>\<^sub>n\<^sub>o\<^sub>w # \<Psi> \<triangleright> \<psi>\<^sub>f\<^sub>u\<^sub>t # \<Phi>) = (\<top>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n # \<top>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n # \<Gamma>', na \<turnstile> \<top>\<^sub>T\<^sub>E\<^sub>S\<^sub>L # \<Psi>' \<triangleright> (K sporadic \<tau>) # \<Phi>') \<Longrightarrow>
       consistent_run \<Gamma>' \<Longrightarrow>
       \<lbrakk> \<gamma>\<^sub>1 \<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n \<inter> \<lbrakk> \<gamma>\<^sub>2 \<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n \<inter> \<lbrakk> \<psi>\<^sub>n\<^sub>o\<^sub>w \<nabla> n \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L \<inter> \<lbrakk> \<psi>\<^sub>f\<^sub>u\<^sub>t \<nabla> Suc n \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L \<subseteq> \<lbrakk> \<psi> \<nabla> n \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L"
      using TESL_interp_at_index_sporadic_cases by blast
    show "\<And>K na \<tau> \<Gamma>' \<Psi>' \<Phi>'.
       (\<Gamma>, n \<turnstile> \<psi> # \<Psi> \<triangleright> \<Phi>) = (\<Gamma>', na \<turnstile> (K sporadic \<tau>) # \<Psi>' \<triangleright> \<Phi>') \<Longrightarrow>
       (\<gamma>\<^sub>1 # \<gamma>\<^sub>2 # \<Gamma>, n \<turnstile> \<psi>\<^sub>n\<^sub>o\<^sub>w # \<Psi> \<triangleright> \<psi>\<^sub>f\<^sub>u\<^sub>t # \<Phi>) = (K \<Up> na # K \<Down> na @ \<lfloor> \<tau> \<rfloor> # \<Gamma>', na \<turnstile> \<top>\<^sub>T\<^sub>E\<^sub>S\<^sub>L # \<Psi>' \<triangleright> \<top>\<^sub>T\<^sub>E\<^sub>S\<^sub>L # \<Phi>') \<Longrightarrow>
       consistent_run (K \<Up> na # K \<Down> na @ \<lfloor> \<tau> \<rfloor> # \<Gamma>') \<Longrightarrow>
       \<lbrakk> \<gamma>\<^sub>1 \<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n \<inter> \<lbrakk> \<gamma>\<^sub>2 \<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n \<inter> \<lbrakk> \<psi>\<^sub>n\<^sub>o\<^sub>w \<nabla> n \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L \<inter> \<lbrakk> \<psi>\<^sub>f\<^sub>u\<^sub>t \<nabla> Suc n \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L \<subseteq> \<lbrakk> \<psi> \<nabla> n \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L"
      using TESL_interp_at_index_sporadic_cases by blast
    show "\<And>\<Gamma>' na K\<^sub>1 \<tau> K\<^sub>2 \<Psi>' \<Phi>'.
       (\<Gamma>, n \<turnstile> \<psi> # \<Psi> \<triangleright> \<Phi>) = (\<Gamma>', na \<turnstile> (K\<^sub>1 sporadic \<tau> on K\<^sub>2) # \<Psi>' \<triangleright> \<Phi>') \<Longrightarrow>
       (\<gamma>\<^sub>1 # \<gamma>\<^sub>2 # \<Gamma>, n \<turnstile> \<psi>\<^sub>n\<^sub>o\<^sub>w # \<Psi> \<triangleright> \<psi>\<^sub>f\<^sub>u\<^sub>t # \<Phi>) = (\<top>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n # \<top>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n # \<Gamma>', na \<turnstile> \<top>\<^sub>T\<^sub>E\<^sub>S\<^sub>L # \<Psi>' \<triangleright> (K\<^sub>1 sporadic \<tau> on K\<^sub>2) # \<Phi>') \<Longrightarrow>
       consistent_run \<Gamma>' \<Longrightarrow>
       \<lbrakk> \<gamma>\<^sub>1 \<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n \<inter> \<lbrakk> \<gamma>\<^sub>2 \<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n \<inter> \<lbrakk> \<psi>\<^sub>n\<^sub>o\<^sub>w \<nabla> n \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L \<inter> \<lbrakk> \<psi>\<^sub>f\<^sub>u\<^sub>t \<nabla> Suc n \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L \<subseteq> \<lbrakk> \<psi> \<nabla> n \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L"
      using TESL_interp_at_index_sporadicon_cases by blast
    show "\<And>K\<^sub>1 na K\<^sub>2 \<tau> \<Gamma>' \<Psi>' \<Phi>'.
       (\<Gamma>, n \<turnstile> \<psi> # \<Psi> \<triangleright> \<Phi>) = (\<Gamma>', na \<turnstile> (K\<^sub>1 sporadic \<tau> on K\<^sub>2) # \<Psi>' \<triangleright> \<Phi>') \<Longrightarrow>
       (\<gamma>\<^sub>1 # \<gamma>\<^sub>2 # \<Gamma>, n \<turnstile> \<psi>\<^sub>n\<^sub>o\<^sub>w # \<Psi> \<triangleright> \<psi>\<^sub>f\<^sub>u\<^sub>t # \<Phi>) =
       (K\<^sub>1 \<Up> na # K\<^sub>2 \<Down> na @ \<tau> # \<Gamma>', na \<turnstile> \<top>\<^sub>T\<^sub>E\<^sub>S\<^sub>L # \<Psi>' \<triangleright> \<top>\<^sub>T\<^sub>E\<^sub>S\<^sub>L # \<Phi>') \<Longrightarrow>
       consistent_run (K\<^sub>1 \<Up> na # K\<^sub>2 \<Down> na @ \<tau> # \<Gamma>') \<Longrightarrow>
       \<lbrakk> \<gamma>\<^sub>1 \<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n \<inter> \<lbrakk> \<gamma>\<^sub>2 \<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n \<inter> \<lbrakk> \<psi>\<^sub>n\<^sub>o\<^sub>w \<nabla> n \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L \<inter> \<lbrakk> \<psi>\<^sub>f\<^sub>u\<^sub>t \<nabla> Suc n \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L \<subseteq> \<lbrakk> \<psi> \<nabla> n \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L"
      using TESL_interp_at_index_sporadicon_cases by blast
    show "\<And>K\<^sub>1 na \<alpha> K\<^sub>2 \<beta> \<Gamma>' \<Psi>' \<Phi>'.
       (\<Gamma>, n \<turnstile> \<psi> # \<Psi> \<triangleright> \<Phi>) = (\<Gamma>', na \<turnstile> (tag-relation K\<^sub>1 = \<alpha> * K\<^sub>2 + \<beta>) # \<Psi>' \<triangleright> \<Phi>') \<Longrightarrow>
       (\<gamma>\<^sub>1 # \<gamma>\<^sub>2 # \<Gamma>, n \<turnstile> \<psi>\<^sub>n\<^sub>o\<^sub>w # \<Psi> \<triangleright> \<psi>\<^sub>f\<^sub>u\<^sub>t # \<Phi>) =
       (\<top>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n #
        \<tau>\<^sub>v\<^sub>a\<^sub>r (K\<^sub>1, na) \<doteq> \<alpha> * \<tau>\<^sub>v\<^sub>a\<^sub>r (K\<^sub>2, na) + \<beta> #
        \<Gamma>', na \<turnstile> \<top>\<^sub>T\<^sub>E\<^sub>S\<^sub>L # \<Psi>' \<triangleright> (tag-relation K\<^sub>1 = \<alpha> * K\<^sub>2 + \<beta>) # \<Phi>') \<Longrightarrow>
       consistent_run (\<tau>\<^sub>v\<^sub>a\<^sub>r (K\<^sub>1, na) \<doteq> \<alpha> * \<tau>\<^sub>v\<^sub>a\<^sub>r (K\<^sub>2, na) + \<beta> # \<Gamma>') \<Longrightarrow>
       \<lbrakk> \<gamma>\<^sub>1 \<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n \<inter> \<lbrakk> \<gamma>\<^sub>2 \<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n \<inter> \<lbrakk> \<psi>\<^sub>n\<^sub>o\<^sub>w \<nabla> n \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L \<inter> \<lbrakk> \<psi>\<^sub>f\<^sub>u\<^sub>t \<nabla> Suc n \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L \<subseteq> \<lbrakk> \<psi> \<nabla> n \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L"
      using TESL_interp_at_index_tagrel_cases by blast
    show "\<And>K\<^sub>1 na \<Gamma>' K\<^sub>2 \<Psi>' \<Phi>'.
       (\<Gamma>, n \<turnstile> \<psi> # \<Psi> \<triangleright> \<Phi>) = (\<Gamma>', na \<turnstile> (K\<^sub>1 implies K\<^sub>2) # \<Psi>' \<triangleright> \<Phi>') \<Longrightarrow>
       (\<gamma>\<^sub>1 # \<gamma>\<^sub>2 # \<Gamma>, n \<turnstile> \<psi>\<^sub>n\<^sub>o\<^sub>w # \<Psi> \<triangleright> \<psi>\<^sub>f\<^sub>u\<^sub>t # \<Phi>) =
       (\<top>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n # K\<^sub>1 \<not>\<Up> na # \<Gamma>', na \<turnstile> \<top>\<^sub>T\<^sub>E\<^sub>S\<^sub>L # \<Psi>' \<triangleright> (K\<^sub>1 implies K\<^sub>2) # \<Phi>') \<Longrightarrow>
       consistent_run (K\<^sub>1 \<not>\<Up> na # \<Gamma>') \<Longrightarrow>
       \<lbrakk> \<gamma>\<^sub>1 \<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n \<inter> \<lbrakk> \<gamma>\<^sub>2 \<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n \<inter> \<lbrakk> \<psi>\<^sub>n\<^sub>o\<^sub>w \<nabla> n \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L \<inter> \<lbrakk> \<psi>\<^sub>f\<^sub>u\<^sub>t \<nabla> Suc n \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L \<subseteq> \<lbrakk> \<psi> \<nabla> n \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L"
      using TESL_interp_at_index_implies_cases by blast
    show "\<And>K\<^sub>1 na K\<^sub>2 \<Gamma>' \<Psi>' \<Phi>'.
       (\<Gamma>, n \<turnstile> \<psi> # \<Psi> \<triangleright> \<Phi>) = (\<Gamma>', na \<turnstile> (K\<^sub>1 implies K\<^sub>2) # \<Psi>' \<triangleright> \<Phi>') \<Longrightarrow>
       (\<gamma>\<^sub>1 # \<gamma>\<^sub>2 # \<Gamma>, n \<turnstile> \<psi>\<^sub>n\<^sub>o\<^sub>w # \<Psi> \<triangleright> \<psi>\<^sub>f\<^sub>u\<^sub>t # \<Phi>) = (K\<^sub>1 \<Up> na # K\<^sub>2 \<Up> na # \<Gamma>', na \<turnstile> \<top>\<^sub>T\<^sub>E\<^sub>S\<^sub>L # \<Psi>' \<triangleright> (K\<^sub>1 implies K\<^sub>2) # \<Phi>') \<Longrightarrow>
       consistent_run (K\<^sub>1 \<Up> na # K\<^sub>2 \<Up> na # \<Gamma>') \<Longrightarrow>
       \<lbrakk> \<gamma>\<^sub>1 \<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n \<inter> \<lbrakk> \<gamma>\<^sub>2 \<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n \<inter> \<lbrakk> \<psi>\<^sub>n\<^sub>o\<^sub>w \<nabla> n \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L \<inter> \<lbrakk> \<psi>\<^sub>f\<^sub>u\<^sub>t \<nabla> Suc n \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L \<subseteq> \<lbrakk> \<psi> \<nabla> n \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L"
      using TESL_interp_at_index_implies_cases by blast
    show "\<And>K\<^sub>1 na \<Gamma>' \<delta>\<tau> K\<^sub>2 K\<^sub>3 \<Psi>' \<Phi>'.
       (\<Gamma>, n \<turnstile> \<psi> # \<Psi> \<triangleright> \<Phi>) = (\<Gamma>', na \<turnstile> (K\<^sub>1 time-delayed by \<delta>\<tau> on K\<^sub>2 implies K\<^sub>3) # \<Psi>' \<triangleright> \<Phi>') \<Longrightarrow>
       (\<gamma>\<^sub>1 # \<gamma>\<^sub>2 # \<Gamma>, n \<turnstile> \<psi>\<^sub>n\<^sub>o\<^sub>w # \<Psi> \<triangleright> \<psi>\<^sub>f\<^sub>u\<^sub>t # \<Phi>) = (\<top>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n # K\<^sub>1 \<not>\<Up> na # \<Gamma>', na \<turnstile> \<top>\<^sub>T\<^sub>E\<^sub>S\<^sub>L # \<Psi>' \<triangleright> (K\<^sub>1 time-delayed by \<delta>\<tau> on K\<^sub>2 implies K\<^sub>3) # \<Phi>') \<Longrightarrow>
       consistent_run (K\<^sub>1 \<not>\<Up> na # \<Gamma>') \<Longrightarrow>
       \<lbrakk> \<gamma>\<^sub>1 \<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n \<inter> \<lbrakk> \<gamma>\<^sub>2 \<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n \<inter> \<lbrakk> \<psi>\<^sub>n\<^sub>o\<^sub>w \<nabla> n \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L \<inter> \<lbrakk> \<psi>\<^sub>f\<^sub>u\<^sub>t \<nabla> Suc n \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L \<subseteq> \<lbrakk> \<psi> \<nabla> n \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L"
      using TESL_interp_at_index_timedelayed_cases by blast
    show "\<And>K\<^sub>1 na \<Gamma>' \<delta>\<tau> K\<^sub>2 K\<^sub>3 \<Psi>' \<Phi>'.
       (\<Gamma>, n \<turnstile> \<psi> # \<Psi> \<triangleright> \<Phi>) = (\<Gamma>', na \<turnstile> (K\<^sub>1 time-delayed by \<delta>\<tau> on K\<^sub>2 implies K\<^sub>3) # \<Psi>' \<triangleright> \<Phi>') \<Longrightarrow>
       (\<gamma>\<^sub>1 # \<gamma>\<^sub>2 # \<Gamma>, n \<turnstile> \<psi>\<^sub>n\<^sub>o\<^sub>w # \<Psi> \<triangleright> \<psi>\<^sub>f\<^sub>u\<^sub>t # \<Phi>)
         = (\<top>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n # K\<^sub>1 \<Up> na # \<Gamma>', na \<turnstile> (K\<^sub>3 sporadic \<lfloor> \<tau>\<^sub>v\<^sub>a\<^sub>r (K\<^sub>2, na) \<oplus> \<delta>\<tau> \<rfloor> on K\<^sub>2) # \<Psi>' \<triangleright> (K\<^sub>1 time-delayed by \<delta>\<tau> on K\<^sub>2 implies K\<^sub>3) # \<Phi>') \<Longrightarrow>
       consistent_run (K\<^sub>1 \<Up> na # \<Gamma>') \<Longrightarrow>
       \<lbrakk> \<gamma>\<^sub>1 \<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n \<inter> \<lbrakk> \<gamma>\<^sub>2 \<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n \<inter> \<lbrakk> \<psi>\<^sub>n\<^sub>o\<^sub>w \<nabla> n \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L \<inter> \<lbrakk> \<psi>\<^sub>f\<^sub>u\<^sub>t \<nabla> Suc n \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L \<subseteq> \<lbrakk> \<psi> \<nabla> n \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L"
      using TESL_interp_at_index_timedelayed_cases by blast
  qed

lemma elimination_refinement:
  assumes "\<Gamma>, n \<turnstile> \<psi> # \<Psi> \<triangleright> \<Phi>  \<hookrightarrow>  \<gamma>\<^sub>1 # \<gamma>\<^sub>2 # \<Gamma>, n \<turnstile> \<psi>\<^sub>n\<^sub>o\<^sub>w # \<Psi> \<triangleright> \<psi>\<^sub>f\<^sub>u\<^sub>t # \<Phi>"
  shows "\<lbrakk>\<lbrakk> \<Gamma> \<rbrakk>\<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n \<inter> \<lbrakk> \<psi> \<nabla> n \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L \<inter> \<lbrakk>\<lbrakk> \<Psi> \<nabla> n \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L \<inter> \<lbrakk>\<lbrakk> \<Phi> \<nabla> Suc n \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L
          \<supseteq> \<lbrakk> \<gamma>\<^sub>1 \<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n \<inter> \<lbrakk> \<gamma>\<^sub>2 \<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n \<inter> \<lbrakk>\<lbrakk> \<Gamma> \<rbrakk>\<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n \<inter> \<lbrakk> \<psi>\<^sub>n\<^sub>o\<^sub>w \<nabla> n \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L \<inter> \<lbrakk>\<lbrakk> \<Psi> \<nabla> n \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L \<inter> \<lbrakk> \<psi>\<^sub>f\<^sub>u\<^sub>t \<nabla> Suc n \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L \<inter> \<lbrakk>\<lbrakk> \<Phi> \<nabla> Suc n \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L"
  using assms elimination_soundness by blast

theorem reduction_refinement:
  assumes "\<Gamma>\<^sub>1, n\<^sub>1 \<turnstile> \<Psi>\<^sub>1 \<triangleright> \<Phi>\<^sub>1  \<hookrightarrow>  \<Gamma>\<^sub>2, n\<^sub>2 \<turnstile> \<Psi>\<^sub>2 \<triangleright> \<Phi>\<^sub>2"
  shows "\<lbrakk>\<lbrakk> \<Gamma>\<^sub>1 \<rbrakk>\<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n \<inter> \<lbrakk>\<lbrakk> \<Psi>\<^sub>1 \<nabla> n\<^sub>1 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L \<inter> \<lbrakk>\<lbrakk> \<Phi>\<^sub>1 \<nabla> Suc n\<^sub>1 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L  \<supseteq>  \<lbrakk>\<lbrakk> \<Gamma>\<^sub>2 \<rbrakk>\<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n \<inter> \<lbrakk>\<lbrakk> \<Psi>\<^sub>2 \<nabla> n\<^sub>2 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L \<inter> \<lbrakk>\<lbrakk> \<Phi>\<^sub>2 \<nabla> Suc n\<^sub>2 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L"
  proof (insert assms, erule operational_semantics_step.cases)
  show "\<And>\<Gamma> n \<Phi>.
       (\<Gamma>\<^sub>1, n\<^sub>1 \<turnstile> \<Psi>\<^sub>1 \<triangleright> \<Phi>\<^sub>1) = (\<Gamma>, n \<turnstile> [] \<triangleright> \<Phi>) \<Longrightarrow>
       (\<Gamma>\<^sub>2, n\<^sub>2 \<turnstile> \<Psi>\<^sub>2 \<triangleright> \<Phi>\<^sub>2) = (\<Gamma>, Suc n \<turnstile> \<Phi> \<triangleright> []) \<Longrightarrow>
       consistent_run \<Gamma> \<Longrightarrow>
       \<lbrakk>\<lbrakk> \<Gamma>\<^sub>2 \<rbrakk>\<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n \<inter> \<lbrakk>\<lbrakk> \<Psi>\<^sub>2 \<nabla> n\<^sub>2 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L \<inter> \<lbrakk>\<lbrakk> \<Phi>\<^sub>2 \<nabla> Suc n\<^sub>2 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L \<subseteq> \<lbrakk>\<lbrakk> \<Gamma>\<^sub>1 \<rbrakk>\<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n \<inter> \<lbrakk>\<lbrakk> \<Psi>\<^sub>1 \<nabla> n\<^sub>1 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L \<inter> \<lbrakk>\<lbrakk> \<Phi>\<^sub>1 \<nabla> Suc n\<^sub>1 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L"
    by auto
  show "\<And>\<Gamma> n K \<tau> \<Psi> \<Phi>.
       (\<Gamma>\<^sub>1, n\<^sub>1 \<turnstile> \<Psi>\<^sub>1 \<triangleright> \<Phi>\<^sub>1) = (\<Gamma>, n \<turnstile> (K sporadic \<tau>) # \<Psi> \<triangleright> \<Phi>) \<Longrightarrow>
       (\<Gamma>\<^sub>2, n\<^sub>2 \<turnstile> \<Psi>\<^sub>2 \<triangleright> \<Phi>\<^sub>2) = (\<top>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n # \<top>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n # \<Gamma>, n \<turnstile> \<top>\<^sub>T\<^sub>E\<^sub>S\<^sub>L # \<Psi> \<triangleright> (K sporadic \<tau>) # \<Phi>) \<Longrightarrow>
       consistent_run \<Gamma> \<Longrightarrow>
       \<lbrakk>\<lbrakk> \<Gamma>\<^sub>2 \<rbrakk>\<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n \<inter> \<lbrakk>\<lbrakk> \<Psi>\<^sub>2 \<nabla> n\<^sub>2 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L \<inter> \<lbrakk>\<lbrakk> \<Phi>\<^sub>2 \<nabla> Suc n\<^sub>2 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L \<subseteq> \<lbrakk>\<lbrakk> \<Gamma>\<^sub>1 \<rbrakk>\<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n \<inter> \<lbrakk>\<lbrakk> \<Psi>\<^sub>1 \<nabla> n\<^sub>1 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L \<inter> \<lbrakk>\<lbrakk> \<Phi>\<^sub>1 \<nabla> Suc n\<^sub>1 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L"
    using elimination_refinement
    by (metis (no_types, lifting) Pair_inject TESL_interpretation_at_index_cons_morph assms inf_sup_aci(2) symbolic_run_interpretation.simps(2))
  show "\<And>K n \<tau> \<Gamma> \<Psi> \<Phi>.
       (\<Gamma>\<^sub>1, n\<^sub>1 \<turnstile> \<Psi>\<^sub>1 \<triangleright> \<Phi>\<^sub>1) = (\<Gamma>, n \<turnstile> (K sporadic \<tau>) # \<Psi> \<triangleright> \<Phi>) \<Longrightarrow>
       (\<Gamma>\<^sub>2, n\<^sub>2 \<turnstile> \<Psi>\<^sub>2 \<triangleright> \<Phi>\<^sub>2) = (K \<Up> n # K \<Down> n @ \<lfloor> \<tau> \<rfloor> # \<Gamma>, n \<turnstile> \<top>\<^sub>T\<^sub>E\<^sub>S\<^sub>L # \<Psi> \<triangleright> \<top>\<^sub>T\<^sub>E\<^sub>S\<^sub>L # \<Phi>) \<Longrightarrow>
       consistent_run (K \<Up> n # K \<Down> n @ \<lfloor> \<tau> \<rfloor> # \<Gamma>) \<Longrightarrow>
       \<lbrakk>\<lbrakk> \<Gamma>\<^sub>2 \<rbrakk>\<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n \<inter> \<lbrakk>\<lbrakk> \<Psi>\<^sub>2 \<nabla> n\<^sub>2 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L \<inter> \<lbrakk>\<lbrakk> \<Phi>\<^sub>2 \<nabla> Suc n\<^sub>2 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L \<subseteq> \<lbrakk>\<lbrakk> \<Gamma>\<^sub>1 \<rbrakk>\<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n \<inter> \<lbrakk>\<lbrakk> \<Psi>\<^sub>1 \<nabla> n\<^sub>1 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L \<inter> \<lbrakk>\<lbrakk> \<Phi>\<^sub>1 \<nabla> Suc n\<^sub>1 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L"
    using elimination_refinement by auto
  show "\<And>\<Gamma> n K\<^sub>1 \<tau> K\<^sub>2 \<Psi> \<Phi>.
       (\<Gamma>\<^sub>1, n\<^sub>1 \<turnstile> \<Psi>\<^sub>1 \<triangleright> \<Phi>\<^sub>1) = (\<Gamma>, n \<turnstile> (K\<^sub>1 sporadic \<tau> on K\<^sub>2) # \<Psi> \<triangleright> \<Phi>) \<Longrightarrow>
       (\<Gamma>\<^sub>2, n\<^sub>2 \<turnstile> \<Psi>\<^sub>2 \<triangleright> \<Phi>\<^sub>2) = (\<top>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n # \<top>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n # \<Gamma>, n \<turnstile> \<top>\<^sub>T\<^sub>E\<^sub>S\<^sub>L # \<Psi> \<triangleright> (K\<^sub>1 sporadic \<tau> on K\<^sub>2) # \<Phi>) \<Longrightarrow>
       consistent_run \<Gamma> \<Longrightarrow>
       \<lbrakk>\<lbrakk> \<Gamma>\<^sub>2 \<rbrakk>\<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n \<inter> \<lbrakk>\<lbrakk> \<Psi>\<^sub>2 \<nabla> n\<^sub>2 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L \<inter> \<lbrakk>\<lbrakk> \<Phi>\<^sub>2 \<nabla> Suc n\<^sub>2 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L \<subseteq> \<lbrakk>\<lbrakk> \<Gamma>\<^sub>1 \<rbrakk>\<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n \<inter> \<lbrakk>\<lbrakk> \<Psi>\<^sub>1 \<nabla> n\<^sub>1 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L \<inter> \<lbrakk>\<lbrakk> \<Phi>\<^sub>1 \<nabla> Suc n\<^sub>1 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L"
    using elimination_refinement assms by fastforce
  show "\<And>K\<^sub>1 n K\<^sub>2 \<tau> \<Gamma> \<Psi> \<Phi>.
       (\<Gamma>\<^sub>1, n\<^sub>1 \<turnstile> \<Psi>\<^sub>1 \<triangleright> \<Phi>\<^sub>1) = (\<Gamma>, n \<turnstile> (K\<^sub>1 sporadic \<tau> on K\<^sub>2) # \<Psi> \<triangleright> \<Phi>) \<Longrightarrow>
       (\<Gamma>\<^sub>2, n\<^sub>2 \<turnstile> \<Psi>\<^sub>2 \<triangleright> \<Phi>\<^sub>2) = (K\<^sub>1 \<Up> n # K\<^sub>2 \<Down> n @ \<tau> # \<Gamma>, n \<turnstile> \<top>\<^sub>T\<^sub>E\<^sub>S\<^sub>L # \<Psi> \<triangleright> \<top>\<^sub>T\<^sub>E\<^sub>S\<^sub>L # \<Phi>) \<Longrightarrow>
       consistent_run (K\<^sub>1 \<Up> n # K\<^sub>2 \<Down> n @ \<tau> # \<Gamma>) \<Longrightarrow>
       \<lbrakk>\<lbrakk> \<Gamma>\<^sub>2 \<rbrakk>\<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n \<inter> \<lbrakk>\<lbrakk> \<Psi>\<^sub>2 \<nabla> n\<^sub>2 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L \<inter> \<lbrakk>\<lbrakk> \<Phi>\<^sub>2 \<nabla> Suc n\<^sub>2 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L \<subseteq> \<lbrakk>\<lbrakk> \<Gamma>\<^sub>1 \<rbrakk>\<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n \<inter> \<lbrakk>\<lbrakk> \<Psi>\<^sub>1 \<nabla> n\<^sub>1 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L \<inter> \<lbrakk>\<lbrakk> \<Phi>\<^sub>1 \<nabla> Suc n\<^sub>1 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L"
    using elimination_refinement assms by fastforce
  show "\<And>K\<^sub>1 n \<alpha> K\<^sub>2 \<beta> \<Gamma> \<Psi> \<Phi>.
       (\<Gamma>\<^sub>1, n\<^sub>1 \<turnstile> \<Psi>\<^sub>1 \<triangleright> \<Phi>\<^sub>1) = (\<Gamma>, n \<turnstile> (tag-relation K\<^sub>1 = \<alpha> * K\<^sub>2 + \<beta>) # \<Psi> \<triangleright> \<Phi>) \<Longrightarrow>
       (\<Gamma>\<^sub>2, n\<^sub>2 \<turnstile> \<Psi>\<^sub>2 \<triangleright> \<Phi>\<^sub>2) = (\<top>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n # \<tau>\<^sub>v\<^sub>a\<^sub>r (K\<^sub>1, n) \<doteq> \<alpha> * \<tau>\<^sub>v\<^sub>a\<^sub>r (K\<^sub>2, n) + \<beta> # \<Gamma>, n \<turnstile> \<top>\<^sub>T\<^sub>E\<^sub>S\<^sub>L # \<Psi> \<triangleright> (tag-relation K\<^sub>1 = \<alpha> * K\<^sub>2 + \<beta>) # \<Phi>) \<Longrightarrow>
       consistent_run (\<tau>\<^sub>v\<^sub>a\<^sub>r (K\<^sub>1, n) \<doteq> \<alpha> * \<tau>\<^sub>v\<^sub>a\<^sub>r (K\<^sub>2, n) + \<beta> # \<Gamma>) \<Longrightarrow>
       \<lbrakk>\<lbrakk> \<Gamma>\<^sub>2 \<rbrakk>\<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n \<inter> \<lbrakk>\<lbrakk> \<Psi>\<^sub>2 \<nabla> n\<^sub>2 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L \<inter> \<lbrakk>\<lbrakk> \<Phi>\<^sub>2 \<nabla> Suc n\<^sub>2 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L \<subseteq> \<lbrakk>\<lbrakk> \<Gamma>\<^sub>1 \<rbrakk>\<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n \<inter> \<lbrakk>\<lbrakk> \<Psi>\<^sub>1 \<nabla> n\<^sub>1 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L \<inter> \<lbrakk>\<lbrakk> \<Phi>\<^sub>1 \<nabla> Suc n\<^sub>1 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L"
    using elimination_refinement
    by (metis (no_types, lifting) Pair_inject TESL_interpretation_at_index_cons_morph assms inf_sup_aci(2) symbolic_run_interpretation.simps(2))
  show "\<And>K\<^sub>1 n \<Gamma> K\<^sub>2 \<Psi> \<Phi>.
       (\<Gamma>\<^sub>1, n\<^sub>1 \<turnstile> \<Psi>\<^sub>1 \<triangleright> \<Phi>\<^sub>1) = (\<Gamma>, n \<turnstile> (K\<^sub>1 implies K\<^sub>2) # \<Psi> \<triangleright> \<Phi>) \<Longrightarrow>
       (\<Gamma>\<^sub>2, n\<^sub>2 \<turnstile> \<Psi>\<^sub>2 \<triangleright> \<Phi>\<^sub>2) = (\<top>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n # K\<^sub>1 \<not>\<Up> n # \<Gamma>, n \<turnstile> \<top>\<^sub>T\<^sub>E\<^sub>S\<^sub>L # \<Psi> \<triangleright> (K\<^sub>1 implies K\<^sub>2) # \<Phi>) \<Longrightarrow>
       consistent_run (K\<^sub>1 \<not>\<Up> n # \<Gamma>) \<Longrightarrow>
       \<lbrakk>\<lbrakk> \<Gamma>\<^sub>2 \<rbrakk>\<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n \<inter> \<lbrakk>\<lbrakk> \<Psi>\<^sub>2 \<nabla> n\<^sub>2 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L \<inter> \<lbrakk>\<lbrakk> \<Phi>\<^sub>2 \<nabla> Suc n\<^sub>2 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L \<subseteq> \<lbrakk>\<lbrakk> \<Gamma>\<^sub>1 \<rbrakk>\<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n \<inter> \<lbrakk>\<lbrakk> \<Psi>\<^sub>1 \<nabla> n\<^sub>1 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L \<inter> \<lbrakk>\<lbrakk> \<Phi>\<^sub>1 \<nabla> Suc n\<^sub>1 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L"
    using elimination_refinement
    by (metis (no_types, lifting) Pair_inject TESL_interpretation_at_index_cons_morph assms inf.assoc symbolic_run_interpretation.simps(2))
  show "\<And>K\<^sub>1 n K\<^sub>2 \<Gamma> \<Psi> \<Phi>.
       (\<Gamma>\<^sub>1, n\<^sub>1 \<turnstile> \<Psi>\<^sub>1 \<triangleright> \<Phi>\<^sub>1) = (\<Gamma>, n \<turnstile> (K\<^sub>1 implies K\<^sub>2) # \<Psi> \<triangleright> \<Phi>) \<Longrightarrow>
       (\<Gamma>\<^sub>2, n\<^sub>2 \<turnstile> \<Psi>\<^sub>2 \<triangleright> \<Phi>\<^sub>2) = (K\<^sub>1 \<Up> n # K\<^sub>2 \<Up> n # \<Gamma>, n \<turnstile> \<top>\<^sub>T\<^sub>E\<^sub>S\<^sub>L # \<Psi> \<triangleright> (K\<^sub>1 implies K\<^sub>2) # \<Phi>) \<Longrightarrow>
       consistent_run (K\<^sub>1 \<Up> n # K\<^sub>2 \<Up> n # \<Gamma>) \<Longrightarrow>
       \<lbrakk>\<lbrakk> \<Gamma>\<^sub>2 \<rbrakk>\<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n \<inter> \<lbrakk>\<lbrakk> \<Psi>\<^sub>2 \<nabla> n\<^sub>2 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L \<inter> \<lbrakk>\<lbrakk> \<Phi>\<^sub>2 \<nabla> Suc n\<^sub>2 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L \<subseteq> \<lbrakk>\<lbrakk> \<Gamma>\<^sub>1 \<rbrakk>\<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n \<inter> \<lbrakk>\<lbrakk> \<Psi>\<^sub>1 \<nabla> n\<^sub>1 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L \<inter> \<lbrakk>\<lbrakk> \<Phi>\<^sub>1 \<nabla> Suc n\<^sub>1 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L"
    using elimination_refinement
    by (metis (no_types, lifting) Pair_inject TESL_interpretation_at_index_cons_morph assms inf_assoc symbolic_run_interpretation.simps(2))
  show "\<And>K\<^sub>1 n \<Gamma> \<delta>\<tau> K\<^sub>2 K\<^sub>3 \<Psi> \<Phi>.
       (\<Gamma>\<^sub>1, n\<^sub>1 \<turnstile> \<Psi>\<^sub>1 \<triangleright> \<Phi>\<^sub>1) = (\<Gamma>, n \<turnstile> (K\<^sub>1 time-delayed by \<delta>\<tau> on K\<^sub>2 implies K\<^sub>3) # \<Psi> \<triangleright> \<Phi>) \<Longrightarrow>
       (\<Gamma>\<^sub>2, n\<^sub>2 \<turnstile> \<Psi>\<^sub>2 \<triangleright> \<Phi>\<^sub>2) = (\<top>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n # K\<^sub>1 \<not>\<Up> n # \<Gamma>, n \<turnstile> \<top>\<^sub>T\<^sub>E\<^sub>S\<^sub>L # \<Psi> \<triangleright> (K\<^sub>1 time-delayed by \<delta>\<tau> on K\<^sub>2 implies K\<^sub>3) # \<Phi>) \<Longrightarrow>
       consistent_run (K\<^sub>1 \<not>\<Up> n # \<Gamma>) \<Longrightarrow>
       \<lbrakk>\<lbrakk> \<Gamma>\<^sub>2 \<rbrakk>\<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n \<inter> \<lbrakk>\<lbrakk> \<Psi>\<^sub>2 \<nabla> n\<^sub>2 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L \<inter> \<lbrakk>\<lbrakk> \<Phi>\<^sub>2 \<nabla> Suc n\<^sub>2 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L \<subseteq> \<lbrakk>\<lbrakk> \<Gamma>\<^sub>1 \<rbrakk>\<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n \<inter> \<lbrakk>\<lbrakk> \<Psi>\<^sub>1 \<nabla> n\<^sub>1 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L \<inter> \<lbrakk>\<lbrakk> \<Phi>\<^sub>1 \<nabla> Suc n\<^sub>1 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L"
    using elimination_refinement
    by (metis (no_types, lifting) Int_assoc Pair_inject TESL_interpretation_at_index_cons_morph assms symbolic_run_interpretation.simps(2))
  show "\<And>K\<^sub>1 n \<Gamma> \<delta>\<tau> K\<^sub>2 K\<^sub>3 \<Psi> \<Phi>.
       (\<Gamma>\<^sub>1, n\<^sub>1 \<turnstile> \<Psi>\<^sub>1 \<triangleright> \<Phi>\<^sub>1) = (\<Gamma>, n \<turnstile> (K\<^sub>1 time-delayed by \<delta>\<tau> on K\<^sub>2 implies K\<^sub>3) # \<Psi> \<triangleright> \<Phi>) \<Longrightarrow>
       (\<Gamma>\<^sub>2, n\<^sub>2 \<turnstile> \<Psi>\<^sub>2 \<triangleright> \<Phi>\<^sub>2) = (\<top>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n # K\<^sub>1 \<Up> n # \<Gamma>, n \<turnstile> (K\<^sub>3 sporadic \<lfloor> \<tau>\<^sub>v\<^sub>a\<^sub>r (K\<^sub>2, n) \<oplus> \<delta>\<tau> \<rfloor> on K\<^sub>2) # \<Psi> \<triangleright> (K\<^sub>1 time-delayed by \<delta>\<tau> on K\<^sub>2 implies K\<^sub>3) # \<Phi>) \<Longrightarrow>
       consistent_run (K\<^sub>1 \<Up> n # \<Gamma>) \<Longrightarrow>
       \<lbrakk>\<lbrakk> \<Gamma>\<^sub>2 \<rbrakk>\<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n \<inter> \<lbrakk>\<lbrakk> \<Psi>\<^sub>2 \<nabla> n\<^sub>2 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L \<inter> \<lbrakk>\<lbrakk> \<Phi>\<^sub>2 \<nabla> Suc n\<^sub>2 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L \<subseteq> \<lbrakk>\<lbrakk> \<Gamma>\<^sub>1 \<rbrakk>\<rbrakk>\<^sub>s\<^sub>y\<^sub>m\<^sub>r\<^sub>u\<^sub>n \<inter> \<lbrakk>\<lbrakk> \<Psi>\<^sub>1 \<nabla> n\<^sub>1 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L \<inter> \<lbrakk>\<lbrakk> \<Phi>\<^sub>1 \<nabla> Suc n\<^sub>1 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L"
    using elimination_refinement
    by (metis (no_types, lifting) Pair_inject TESL_interpretation_at_index_cons_morph assms inf.assoc symbolic_run_interpretation.simps(2))
  qed

lemma run_index_progress:
  assumes "\<Gamma>\<^sub>1, n\<^sub>1 \<turnstile> \<Psi>\<^sub>1 \<triangleright> \<Phi>\<^sub>1  \<hookrightarrow>  \<Gamma>\<^sub>2, n\<^sub>2 \<turnstile> \<Psi>\<^sub>2 \<triangleright> \<Phi>\<^sub>2"
  shows "n\<^sub>2 = Suc n\<^sub>1 \<or> n\<^sub>2 = n\<^sub>1"
  by (insert assms, erule operational_semantics_step.cases, auto)

lemma run_index_progress_simlstep:
  assumes "(\<Gamma>\<^sub>1, n\<^sub>1 \<turnstile> \<Psi>\<^sub>1 \<triangleright> \<Phi>\<^sub>1, \<Gamma>\<^sub>2, n\<^sub>2 \<turnstile> \<Psi>\<^sub>2 \<triangleright> \<Phi>\<^sub>2) \<in> \<hookrightarrow>\<^sup>\<nabla>"
  shows "n\<^sub>2 = Suc n\<^sub>1"
  apply (insert assms)
  apply auto
  sorry

(**) section \<open>Composition\<close> (**)

lemma run_composition:
  assumes "\<Gamma>, n \<turnstile> \<Psi>\<^sub>1 \<triangleright> (\<Phi>\<^sub>1 @ \<Phi>\<^sub>2)  \<hookrightarrow>  \<Gamma>', n' \<turnstile> \<Psi>\<^sub>2 \<triangleright> (\<Phi>\<^sub>1' @ \<Phi>\<^sub>2')"
  shows "\<lbrakk>\<lbrakk> \<Phi>\<^sub>1 @ \<Phi>\<^sub>2 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L = \<lbrakk>\<lbrakk> \<Phi>\<^sub>1' @ \<Phi>\<^sub>2' \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L"
  apply (insert assms, erule operational_semantics_step.cases, auto)
  (* nitpick *)
  sorry

lemma composition:
  assumes "K\<^sub>1 time-delayed by \<delta>\<tau> on K\<^sub>2 implies K\<^sub>3 \<notin> set \<Phi> \<union> set \<Phi>'"
  assumes "\<TTurnstile> \<Gamma>\<^sub>1, n \<turnstile> [] \<triangleright> \<Phi>\<^sub>1"
  assumes "\<TTurnstile> \<Gamma>\<^sub>2, n \<turnstile> [] \<triangleright> \<Phi>\<^sub>2"
  assumes "consistency_run (\<Gamma>\<^sub>1 @ \<Gamma>\<^sub>2)"
  shows   "\<TTurnstile> \<Gamma>\<^sub>1 @ \<Gamma>\<^sub>2, n \<turnstile> [] \<triangleright> \<Phi>\<^sub>1 @ \<Phi>\<^sub>2"
  oops

(**) section \<open>Decidability\<close> (**)
fun tagrel_consistent :: "TESL_formula \<Rightarrow> bool" where
  "tagrel_consistent \<Phi> = undefined"

lemma existence:
  (* Assumption that the linear system made of tag relations is consistent *)
  assumes "tagrel_consistent \<Phi>"
  shows "\<exists>\<rho>. \<rho> \<in> \<lbrakk>\<lbrakk> \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L"
oops
(* proof (induction \<Phi>) *)

end