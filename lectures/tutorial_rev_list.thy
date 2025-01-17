theory tutorial_rev_list
imports Main
begin

no_notation Nil ("[]") and Cons (infixr "#" 65) and append (infixr "@" 65)
hide_type list
hide_const rev

datatype 'a list = Nil ("[]")
  | Cons 'a "'a list" (infixr "#" 65)

(* This is the append function: *)
primrec app :: "'a list \<Rightarrow> 'a list => 'a list" (infixr "@" 65) 
where
"[] @ ys = ys" |
"(x # xs) @ ys = x # (xs @ ys)"

primrec rev :: "'a list => 'a list" where
"rev [] = []" |
"rev (x # xs) = (rev xs) @ (x # [])"

value "rev (True # False # [])"
