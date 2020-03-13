theory fol
  imports Main
begin

thm exI
thm allI
thm exE
thm allE

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
  apply (rule exI) 



lemma ex2: "(\<exists>x::int. \<forall>y::int. x \<le> y) \<longrightarrow> (\<forall>x::int. \<exists>y::int. y \<le> x)"
  apply (rule impI)
  apply (rule allI)
(* why can't we use this?
  apply (rule exI)
*)
  oops