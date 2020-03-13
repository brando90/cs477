theory my_examples
imports Main
begin

thm impI
thm conjI

lemma trivial: "A \<longrightarrow> A"
apply (rule_tac impI)
apply assumption
done (* of lemma proof *)

thm trivial

(* introduction exmaple *)
lemma lec_A_B_implies_A_and_A: "A \<longrightarrow> (B \<longrightarrow> (A \<and> B))"
  apply (rule_tac impI)
  apply (rule_tac impI)
  apply (rule_tac conjI)
   apply assumption
   apply assumption
  done

lemma conj_rule: "\<lbrakk> P; Q \<rbrakk> \<Longrightarrow> P \<and> (Q \<and> P)"
  apply (rule conjI)
   apply assumption
  apply (rule conjI)
   apply assumption
  apply assumption
  done

lemma disj_swap: "P \<or> Q \<Longrightarrow> Q \<or> P"
  apply (erule disjE)
   apply (rule disjI2)
   apply assumption
  apply (rule disjI1)
  apply assumption
  done

lemma hw2_p2: "A \<or> A \<longrightarrow> B \<or> A"
  apply (rule impI)
  apply (rule disjI2)
  apply (erule disjE)
   apply assumption
  apply assumption
  done

end (* of theory file *)
