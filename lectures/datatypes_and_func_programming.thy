theory datatypes_and_func_programming
  imports Main
begin

hide_type list

datatype 'a list =
  Nil  ("[]")
  | Cons 'a "'a list"  (infixr "#" 65)

value "Nil :: int list"

(* This is the append function: *)
(*
primrec app :: "'a list => 'a list => 'a list" (infixr "@" 65)
where
"[] @ ys = ys" |
"(x # xs) @ ys = x # (xs @ ys)"
*)

consts app :: "'a list \<Longrightarrow> 'a list \<Longrightarrow> 'a list"
fun
app Nil ys = ys
app (cons x xs) ys = Cons x (app xs ys)