def isDistinctList {t : Type} [DecidableEq t] (l : List t) : Bool :=
  match l with
  | [] => true
  | x :: xs => List.all xs (· != x) && isDistinctList xs

def ListDisjoint {t : Type} [DecidableEq t] (l1 l2 : List t) : Bool :=
  l1.filter (List.elem · l2) == []
