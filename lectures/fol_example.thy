theory fol_example
  imports Main
begin

lemma ex1:
shows "(\<exists> x::int. \<forall> y::int. x \<le> y) \<longrightarrow>(\<forall> x::int. \<exists> y::int. y \<le> x)"
  apply (rule impI)
  apply (rule allI)
  apply (rule exE)
  apply assumption
  thm exI
  apply (rule_tac x = "xa" in exI)
  apply (rule_tac x = "x" in allE)
   apply assumption
  apply assumption
  done

lemma ex2:
  shows "(\<forall> x::int. \<exists> y::int. y \<le> x) \<longrightarrow> (\<exists> x::int. \<forall> y::int. x \<le> y)"
  apply (rule impI)
  apply (rule exI)
  apply (rule allI)
  apply (rule_tac x = "y" in allE)
  apply assumption
  apply (rule exE)
   apply assumption
  apply assumption
  oops

end
