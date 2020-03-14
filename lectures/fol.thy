theory fol
  imports Main
begin

thm exI
thm allI
thm exE
thm allE

thm impE

(*
exI: ?P ?x \<Longrightarrow> \<exists>x. ?P x
allI: (\<And>x. ?P x) \<Longrightarrow> \<forall>x. ?P x
exE: \<exists>x. ?P x \<Longrightarrow> (\<And>x. ?P x \<Longrightarrow> ?Q) \<Longrightarrow> ?Q
allE: \<forall>x. ?P x \<Longrightarrow> (?P ?x \<Longrightarrow> ?R) \<Longrightarrow> ?R
*)

lemma ex1: "(\<exists>x::int. \<forall>y::int. x \<le> y) \<longrightarrow> (\<forall>x::int. \<exists>y::int. y \<le> x)"
  apply (rule impI)
  apply (rule allI)
  (* apply (rule exE) *)
  (* apply (rule_tac P = "\<lambda>x. \<forall>y. x<y" and Q = "\<exists>y. y \<le> x" in exE) *)
  apply (rule_tac P = "\<lambda>x. \<forall>y. x\<le>y" in exE)
   apply assumption
  apply (rule_tac x = "xa" in exI)
  apply (rule_tac x = "x" in allE)
   apply (assumption)
  apply (assumption)
  done

lemma ex2: "(\<forall>x.\<forall>y. P x \<longrightarrow> Q y) \<longrightarrow> ( (\<exists>x. P x)\<longrightarrow>(\<forall>y. Q y) )"
  apply (rule impI)
  apply (rule impI)
  apply (rule allI) (* introduces \<and>y for Q y in final goal *)
  apply (rule_tac P = "\<lambda>x. P x" in exE) (* introduces \<and>x for the existential to have P x *)
   apply assumption
  apply (rule_tac P = "\<lambda>x. \<forall>y. P x \<longrightarrow> Q y" and x = "x" in allE)
   apply assumption
  apply (rule_tac P = "\<lambda>y. P x \<longrightarrow> Q y" and x = "y" in allE)
  (* apply (rule allE) *)
   apply assumption
  apply (erule impE)
   apply assumption
  apply assumption
  done

(* TODO do same proof as above but let isabelle unify for you *)

lemma ex3: "(\<forall>x. \<forall>y. P x \<and> P y) \<longrightarrow> ( (\<forall> x. P x) \<and> (\<forall>y. P y) )"
  apply (rule impI)
  thm conjI
  apply (rule conjI)
   apply (rule allI)
   apply (rule_tac P = "\<lambda> x. \<forall>y. P x \<and> P y" and x = "x" in allE)
    apply assumption
   apply (rule_tac P = "\<lambda>y. P x \<and> P y" and x = "x" in allE)
    apply assumption
   apply (erule conjE)
   apply assumption
  apply (rule allI)
  apply (rule_tac P = "\<lambda>x. \<forall> y. P x \<and> P y" and x = "y" in allE)
   apply assumption
  apply (rule_tac P = "\<lambda>ya. P y \<and> P ya" and x = "y" in allE)
   apply assumption
  apply (erule conjE)
  apply assumption

