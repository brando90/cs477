theory basics
imports Main
begin

thm impI
thm conjI
(* thm assumption *)

(* Introduction proofs *)

lemma proof1: "A \<longrightarrow> A"
  thm impI
  apply (rule impI)
  apply assumption
  done

lemma proof2: "A \<Longrightarrow> A"
  apply assumption
  done

lemma proof3: "A \<longrightarrow> (B \<longrightarrow> (B \<and> A))"
  thm impI
  apply (rule impI)
  apply (rule impI)
  apply (rule conjI)
  apply assumption
  apply assumption
  done

(* Elimination proofs *)

lemma proof4: "A \<and> B \<longrightarrow> A \<or> B"
  thm impI
  apply (rule impI)
  thm disjI1
  apply (rule disjI1)
  thm conjE
  apply (erule conjE)
  apply (assumption)
  done

lemma proof5: "(A \<longrightarrow> B) \<longrightarrow> ( ( B \<longrightarrow> C) \<longrightarrow> (A \<longrightarrow> C) )"
  thm impI
  apply (rule impI)
  apply (rule impI)
  apply (rule impI)
  thm impE
  apply (erule impE)
   apply assumption
  apply (erule impE)
  apply assumption
  apply assumption
  done


