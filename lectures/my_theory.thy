theory my_theory
imports Main
begin

thm impI

lemma trivial: "A \<longrightarrow> A"
apply (rule_tac impI)
apply assumption
done (* of lemma proof *)

thm trivial

lemma trivial2: "A \<longrightarrow> A"
proof (rule_tac impI)
  assume H1: "A"
  from H1
  show "A"
    by (rule_tac H1)
qed 


end (* of theory file *)
