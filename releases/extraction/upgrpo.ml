
type empty_set = |

type nat =
| O
| S of nat

type ('a, 'b) sum =
| Inl of 'a
| Inr of 'b

type 'a list =
| Nil
| Cons of 'a * 'a list

type 'a id =
| Id_refl

type ('a, 'b) or0 = ('a, 'b) sum

type 'a not = 'a -> empty_set

(** val count_g :
    ('a1 -> 'a1 -> ('a1 id, 'a1 id not) or0) -> 'a1 -> 'a1 list -> nat **)

let rec count_g grp_eq_dec j = function
| Nil -> O
| Cons (x, rest) ->
  (match grp_eq_dec x j with
   | Inl _ -> S (count_g grp_eq_dec j rest)
   | Inr _ -> count_g grp_eq_dec j rest)

(** val removeT_g :
    ('a1 -> 'a1 -> ('a1 id, 'a1 id not) or0) -> 'a1 -> 'a1 list -> 'a1 list **)

let rec removeT_g grp_eq_dec j = function
| Nil -> Nil
| Cons (x, rest) ->
  (match grp_eq_dec x j with
   | Inl _ -> removeT_g grp_eq_dec j rest
   | Inr _ -> Cons (x, (removeT_g grp_eq_dec j rest)))
