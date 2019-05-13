theory Config_Morphisms
  imports Hygge_Theory
begin

consts morphism :: \<open>'a \<Rightarrow> ('\<tau>::linorder \<Rightarrow> '\<tau>::linorder) \<Rightarrow> 'a\<close> (infixl "\<Otimes>" 100)

overloading morphism_tagconst \<equiv> "morphism :: '\<tau> tag_const \<Rightarrow> ('\<tau>::linorder \<Rightarrow> '\<tau>) \<Rightarrow> '\<tau> tag_const" 
begin 
  definition morphism_tagconst :  
          "(x::'\<tau> tag_const) \<Otimes> (f::('\<tau>::linorder \<Rightarrow> '\<tau>)) = (\<tau>\<^sub>c\<^sub>s\<^sub>t o f)(the_tag_const x) " 
end

overloading morphism_TESL_atomic \<equiv> 
            "morphism :: '\<tau> TESL_atomic \<Rightarrow> ('\<tau>::linorder \<Rightarrow> '\<tau>) \<Rightarrow> '\<tau> TESL_atomic" 
begin 
definition morphism_TESL_atomic : 
          "(\<Psi>::'\<tau> TESL_atomic) \<Otimes> (f::('\<tau>::linorder \<Rightarrow> '\<tau>)) = 
              (case \<Psi> of
                (C sporadic t on C')     \<Rightarrow> (C sporadic (t\<Otimes>f) on C') 
              | (time-relation \<lfloor>C, C'\<rfloor>\<in>R)\<Rightarrow> (time-relation \<lfloor>C, C'\<rfloor> \<in> (\<lambda>(t, t'). R(t\<Otimes>f,t'\<Otimes>f)))
              | (C implies C')           \<Rightarrow> (C implies C')
              | (C implies not C')       \<Rightarrow> (C implies not C')       
              | (C time-delayed by t on C' implies C'') 
                                         \<Rightarrow> (C time-delayed by t\<Otimes>f on C' implies C'')
              | (C weakly precedes C')   \<Rightarrow> (C weakly precedes C')
              | (C strictly precedes C') \<Rightarrow> (C strictly precedes C') 
              | (C kills C')             \<Rightarrow> (C kills C'))" 
end

overloading morphism_TESL_formula \<equiv> 
            "morphism :: '\<tau> TESL_formula \<Rightarrow> ('\<tau>::linorder \<Rightarrow> '\<tau>) \<Rightarrow> '\<tau> TESL_formula" 
begin 
definition  morphism_TESL_formula : 
           "(\<Psi>::'\<tau> TESL_formula) \<Otimes> (f::('\<tau>::linorder \<Rightarrow> '\<tau>)) = map (\<lambda>x. x \<Otimes> f) \<Psi>" 
end


overloading morphism_TESL_config \<equiv> 
            "morphism :: ('\<tau>::linordered_field) config \<Rightarrow> ('\<tau> \<Rightarrow> '\<tau>) \<Rightarrow> '\<tau> config" 
begin 
fun  morphism_TESL_config 
  where  "((\<Gamma>, n \<turnstile> \<Psi> \<triangleright> \<Phi>)::('\<tau>::linordered_field) config) \<Otimes> (f::('\<tau> \<Rightarrow> '\<tau>)) =
           (\<Gamma>, n \<turnstile> (\<Psi>\<Otimes>f) \<triangleright> (\<Phi>\<Otimes>f))" 
end

find_theorems name:consistent
definition consistent :: "('\<tau>::linordered_field) TESL_formula \<Rightarrow> bool" 
  where   "consistent \<Psi> \<equiv> \<lbrakk>\<lbrakk> \<Psi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L \<noteq> {}"


theorem consistency_coinduct : 
  assumes start             : "([], 0 \<turnstile> \<Psi> \<triangleright> [])  \<hookrightarrow>\<^sup>*\<^sup>* (\<Gamma>\<^sub>1, n\<^sub>1 \<turnstile> \<Psi>\<^sub>1 \<triangleright> \<Phi>\<^sub>1)"
   and    loop              : "(\<Gamma>\<^sub>1, n\<^sub>1 \<turnstile> \<Psi>\<^sub>1 \<triangleright> \<Phi>\<^sub>1) \<hookrightarrow>\<^sup>+\<^sup>+ (\<Gamma>\<^sub>2, n\<^sub>2 \<turnstile> \<Psi>\<^sub>2 \<triangleright> \<Phi>\<^sub>2)"
   and    init_invariant    : "consistent_context \<Gamma>\<^sub>1"
   and    post_invariant    : "consistent_context \<Gamma>\<^sub>2"
   and    retract_condition : "(\<Gamma>\<^sub>2, n\<^sub>2 \<turnstile> \<Psi>\<^sub>2 \<triangleright> \<Phi>\<^sub>2) \<Otimes> f = (\<Gamma>\<^sub>2, n\<^sub>2 \<turnstile> \<Psi>\<^sub>1 \<triangleright> \<Phi>\<^sub>1) " 
  shows   "consistent \<Psi>"    
   sorry


end