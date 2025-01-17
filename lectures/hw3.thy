theory hw3
imports Main
begin

thm allE

lemma problem1: "(\<forall>x. \<forall>y. P x \<longrightarrow> Q y) \<longrightarrow>( (\<exists>x. P x) \<longrightarrow> (\<forall>y. Q y) )"
  apply (rule impI)
  apply (rule impI)
  apply (rule allI)
  apply (erule exE)
  apply (erule allE)
  apply (erule allE)
  apply (erule impE)
   apply assumption
  apply assumption
  done


lemma problem2: "(\<forall>x. \<forall>y. (P x \<and> P y)) \<longrightarrow> ( (\<forall> x. P x) \<and> (\<forall> y. P y) )"
  apply (rule impI)
  apply (erule allE)
  apply (rule conjI)
   apply (rule allI)
   apply (erule allE)
   apply (erule conjE)
  apply assumption
  apply (rule allI)
  apply (erule allE)
  apply (erule conjE)
  apply assumption
  done

