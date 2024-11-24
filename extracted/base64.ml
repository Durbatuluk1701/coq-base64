
type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

type nat =
| O
| S of nat

(** val app : 'a1 list -> 'a1 list -> 'a1 list **)

let rec app l m =
  match l with
  | [] -> m
  | a :: l1 -> a :: (app l1 m)

type ('a, 'p) sigT =
| ExistT of 'a * 'p

(** val projT1 : ('a1, 'a2) sigT -> 'a1 **)

let projT1 = function
| ExistT (a, _) -> a



type ('a, 'b) strictEncodable = { strict_encode : ('a -> 'b);
                                  strict_decode : ('b -> 'a) }

type 'a eqClass =
  'a -> 'a -> bool
  (* singleton inductive, whose constructor was Build_EqClass *)

type 'a decEq =
  'a -> 'a -> bool
  (* singleton inductive, whose constructor was Build_DecEq *)

(** val decEq_from_EqClass : 'a1 eqClass -> 'a1 decEq **)

let decEq_from_EqClass h x y =
  let b = h x y in if b then true else false

(** val eqClass_Ascii : char eqClass **)

let eqClass_Ascii =
  (=)

(** val strict_in_dec : 'a1 eqClass -> 'a1 -> 'a1 list -> bool **)

let rec strict_in_dec h x = function
| [] -> false
| y :: l0 -> if strict_in_dec h x l0 then true else decEq_from_EqClass h x y

(** val string_get_ascii_safe : nat -> (char list, __) sigT -> char **)

let rec string_get_ascii_safe n = function
| ExistT (x, _) ->
  (match x with
   | [] -> assert false (* absurd case *)
   | a::s0 ->
     (match n with
      | O -> a
      | S n0 -> string_get_ascii_safe n0 (ExistT (s0, __))))

(** val map_with_invariant :
    (('a1, __) sigT -> 'a2) -> 'a1 list -> 'a2 list **)

let rec map_with_invariant f = function
| [] -> []
| h :: t -> (f (ExistT (h, __))) :: (map_with_invariant f t)

(** val nth_safe : nat -> 'a1 list -> 'a1 **)

let rec nth_safe n = function
| [] -> assert false (* absurd case *)
| a :: l0 -> (match n with
              | O -> a
              | S n0 -> nth_safe n0 l0)

(** val index_of_safe : 'a1 eqClass -> 'a1 -> 'a1 list -> nat **)

let rec index_of_safe h s = function
| [] -> assert false (* absurd case *)
| a :: l0 ->
  let s0 = decEq_from_EqClass h s a in
  if s0 then O else S (index_of_safe h s l0)

type sextet =
| Sextet of bool * bool * bool * bool * bool * bool

(** val sextet_to_nat : sextet -> nat **)

let sextet_to_nat = function
| Sextet (b1, b2, b3, b4, b5, b6) ->
  if b1
  then if b2
       then if b3
            then if b4
                 then if b5
                      then if b6
                           then S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                                  (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                                  (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                                  (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                                  (S (S (S (S (S (S
                                  O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                           else S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                                  (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                                  (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                                  (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                                  (S (S (S (S (S
                                  O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                      else if b6
                           then S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                                  (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                                  (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                                  (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                                  (S (S (S (S
                                  O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                           else S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                                  (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                                  (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                                  (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                                  (S (S (S
                                  O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                 else if b5
                      then if b6
                           then S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                                  (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                                  (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                                  (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                                  (S (S
                                  O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                           else S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                                  (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                                  (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                                  (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                                  (S
                                  O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                      else if b6
                           then S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                                  (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                                  (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                                  (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                                  O))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                           else S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                                  (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                                  (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                                  (S (S (S (S (S (S (S (S (S (S (S (S (S
                                  O)))))))))))))))))))))))))))))))))))))))))))))))))))))))
            else if b4
                 then if b5
                      then if b6
                           then S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                                  (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                                  (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                                  (S (S (S (S (S (S (S (S (S (S (S (S
                                  O))))))))))))))))))))))))))))))))))))))))))))))))))))))
                           else S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                                  (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                                  (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                                  (S (S (S (S (S (S (S (S (S (S (S
                                  O)))))))))))))))))))))))))))))))))))))))))))))))))))))
                      else if b6
                           then S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                                  (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                                  (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                                  (S (S (S (S (S (S (S (S (S (S
                                  O))))))))))))))))))))))))))))))))))))))))))))))))))))
                           else S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                                  (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                                  (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                                  (S (S (S (S (S (S (S (S (S
                                  O)))))))))))))))))))))))))))))))))))))))))))))))))))
                 else if b5
                      then if b6
                           then S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                                  (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                                  (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                                  (S (S (S (S (S (S (S (S
                                  O))))))))))))))))))))))))))))))))))))))))))))))))))
                           else S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                                  (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                                  (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                                  (S (S (S (S (S (S (S
                                  O)))))))))))))))))))))))))))))))))))))))))))))))))
                      else if b6
                           then S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                                  (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                                  (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                                  (S (S (S (S (S (S
                                  O))))))))))))))))))))))))))))))))))))))))))))))))
                           else S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                                  (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                                  (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                                  (S (S (S (S (S
                                  O)))))))))))))))))))))))))))))))))))))))))))))))
       else if b3
            then if b4
                 then if b5
                      then if b6
                           then S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                                  (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                                  (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                                  (S (S (S (S
                                  O))))))))))))))))))))))))))))))))))))))))))))))
                           else S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                                  (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                                  (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                                  (S (S (S
                                  O)))))))))))))))))))))))))))))))))))))))))))))
                      else if b6
                           then S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                                  (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                                  (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                                  (S (S
                                  O))))))))))))))))))))))))))))))))))))))))))))
                           else S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                                  (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                                  (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                                  (S
                                  O)))))))))))))))))))))))))))))))))))))))))))
                 else if b5
                      then if b6
                           then S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                                  (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                                  (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                                  O))))))))))))))))))))))))))))))))))))))))))
                           else S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                                  (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                                  (S (S (S (S (S (S (S (S (S (S (S (S (S
                                  O)))))))))))))))))))))))))))))))))))))))))
                      else if b6
                           then S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                                  (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                                  (S (S (S (S (S (S (S (S (S (S (S (S
                                  O))))))))))))))))))))))))))))))))))))))))
                           else S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                                  (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                                  (S (S (S (S (S (S (S (S (S (S (S
                                  O)))))))))))))))))))))))))))))))))))))))
            else if b4
                 then if b5
                      then if b6
                           then S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                                  (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                                  (S (S (S (S (S (S (S (S (S (S
                                  O))))))))))))))))))))))))))))))))))))))
                           else S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                                  (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                                  (S (S (S (S (S (S (S (S (S
                                  O)))))))))))))))))))))))))))))))))))))
                      else if b6
                           then S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                                  (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                                  (S (S (S (S (S (S (S (S
                                  O))))))))))))))))))))))))))))))))))))
                           else S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                                  (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                                  (S (S (S (S (S (S (S
                                  O)))))))))))))))))))))))))))))))))))
                 else if b5
                      then if b6
                           then S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                                  (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                                  (S (S (S (S (S (S
                                  O))))))))))))))))))))))))))))))))))
                           else S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                                  (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                                  (S (S (S (S (S
                                  O)))))))))))))))))))))))))))))))))
                      else if b6
                           then S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                                  (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                                  (S (S (S (S
                                  O))))))))))))))))))))))))))))))))
                           else S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                                  (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                                  (S (S (S O)))))))))))))))))))))))))))))))
  else if b2
       then if b3
            then if b4
                 then if b5
                      then if b6
                           then S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                                  (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                                  (S (S O))))))))))))))))))))))))))))))
                           else S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                                  (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                                  (S O)))))))))))))))))))))))))))))
                      else if b6
                           then S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                                  (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                                  O))))))))))))))))))))))))))))
                           else S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                                  (S (S (S (S (S (S (S (S (S (S (S (S (S
                                  O)))))))))))))))))))))))))))
                 else if b5
                      then if b6
                           then S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                                  (S (S (S (S (S (S (S (S (S (S (S (S
                                  O))))))))))))))))))))))))))
                           else S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                                  (S (S (S (S (S (S (S (S (S (S (S
                                  O)))))))))))))))))))))))))
                      else if b6
                           then S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                                  (S (S (S (S (S (S (S (S (S (S
                                  O))))))))))))))))))))))))
                           else S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                                  (S (S (S (S (S (S (S (S (S
                                  O)))))))))))))))))))))))
            else if b4
                 then if b5
                      then if b6
                           then S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                                  (S (S (S (S (S (S (S (S
                                  O))))))))))))))))))))))
                           else S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                                  (S (S (S (S (S (S (S O)))))))))))))))))))))
                      else if b6
                           then S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                                  (S (S (S (S (S (S O))))))))))))))))))))
                           else S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                                  (S (S (S (S (S O)))))))))))))))))))
                 else if b5
                      then if b6
                           then S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                                  (S (S (S (S O))))))))))))))))))
                           else S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                                  (S (S (S O)))))))))))))))))
                      else if b6
                           then S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                                  (S (S O))))))))))))))))
                           else S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                                  (S O)))))))))))))))
       else if b3
            then if b4
                 then if b5
                      then if b6
                           then S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                                  O))))))))))))))
                           else S (S (S (S (S (S (S (S (S (S (S (S (S (S
                                  O)))))))))))))
                      else if b6
                           then S (S (S (S (S (S (S (S (S (S (S (S (S
                                  O))))))))))))
                           else S (S (S (S (S (S (S (S (S (S (S (S
                                  O)))))))))))
                 else if b5
                      then if b6
                           then S (S (S (S (S (S (S (S (S (S (S O))))))))))
                           else S (S (S (S (S (S (S (S (S (S O)))))))))
                      else if b6
                           then S (S (S (S (S (S (S (S (S O))))))))
                           else S (S (S (S (S (S (S (S O)))))))
            else if b4
                 then if b5
                      then if b6
                           then S (S (S (S (S (S (S O))))))
                           else S (S (S (S (S (S O)))))
                      else if b6 then S (S (S (S (S O)))) else S (S (S (S O)))
                 else if b5
                      then if b6 then S (S (S O)) else S (S O)
                      else if b6 then S O else O

(** val sextet_from_nat_safe : nat -> sextet **)

let sextet_from_nat_safe = function
| O -> Sextet (false, false, false, false, false, false)
| S n0 ->
  (match n0 with
   | O -> Sextet (false, false, false, false, false, true)
   | S n1 ->
     (match n1 with
      | O -> Sextet (false, false, false, false, true, false)
      | S n2 ->
        (match n2 with
         | O -> Sextet (false, false, false, false, true, true)
         | S n3 ->
           (match n3 with
            | O -> Sextet (false, false, false, true, false, false)
            | S n4 ->
              (match n4 with
               | O -> Sextet (false, false, false, true, false, true)
               | S n5 ->
                 (match n5 with
                  | O -> Sextet (false, false, false, true, true, false)
                  | S n6 ->
                    (match n6 with
                     | O -> Sextet (false, false, false, true, true, true)
                     | S n7 ->
                       (match n7 with
                        | O ->
                          Sextet (false, false, true, false, false, false)
                        | S n8 ->
                          (match n8 with
                           | O ->
                             Sextet (false, false, true, false, false, true)
                           | S n9 ->
                             (match n9 with
                              | O ->
                                Sextet (false, false, true, false, true,
                                  false)
                              | S n10 ->
                                (match n10 with
                                 | O ->
                                   Sextet (false, false, true, false, true,
                                     true)
                                 | S n11 ->
                                   (match n11 with
                                    | O ->
                                      Sextet (false, false, true, true,
                                        false, false)
                                    | S n12 ->
                                      (match n12 with
                                       | O ->
                                         Sextet (false, false, true, true,
                                           false, true)
                                       | S n13 ->
                                         (match n13 with
                                          | O ->
                                            Sextet (false, false, true, true,
                                              true, false)
                                          | S n14 ->
                                            (match n14 with
                                             | O ->
                                               Sextet (false, false, true,
                                                 true, true, true)
                                             | S n15 ->
                                               (match n15 with
                                                | O ->
                                                  Sextet (false, true, false,
                                                    false, false, false)
                                                | S n16 ->
                                                  (match n16 with
                                                   | O ->
                                                     Sextet (false, true,
                                                       false, false, false,
                                                       true)
                                                   | S n17 ->
                                                     (match n17 with
                                                      | O ->
                                                        Sextet (false, true,
                                                          false, false, true,
                                                          false)
                                                      | S n18 ->
                                                        (match n18 with
                                                         | O ->
                                                           Sextet (false,
                                                             true, false,
                                                             false, true,
                                                             true)
                                                         | S n19 ->
                                                           (match n19 with
                                                            | O ->
                                                              Sextet (false,
                                                                true, false,
                                                                true, false,
                                                                false)
                                                            | S n20 ->
                                                              (match n20 with
                                                               | O ->
                                                                 Sextet
                                                                   (false,
                                                                   true,
                                                                   false,
                                                                   true,
                                                                   false,
                                                                   true)
                                                               | S n21 ->
                                                                 (match n21 with
                                                                  | O ->
                                                                    Sextet
                                                                    (false,
                                                                    true,
                                                                    false,
                                                                    true,
                                                                    true,
                                                                    false)
                                                                  | S n22 ->
                                                                    (match n22 with
                                                                    | O ->
                                                                    Sextet
                                                                    (false,
                                                                    true,
                                                                    false,
                                                                    true,
                                                                    true,
                                                                    true)
                                                                    | S n23 ->
                                                                    (match n23 with
                                                                    | O ->
                                                                    Sextet
                                                                    (false,
                                                                    true,
                                                                    true,
                                                                    false,
                                                                    false,
                                                                    false)
                                                                    | S n24 ->
                                                                    (match n24 with
                                                                    | O ->
                                                                    Sextet
                                                                    (false,
                                                                    true,
                                                                    true,
                                                                    false,
                                                                    false,
                                                                    true)
                                                                    | S n25 ->
                                                                    (match n25 with
                                                                    | O ->
                                                                    Sextet
                                                                    (false,
                                                                    true,
                                                                    true,
                                                                    false,
                                                                    true,
                                                                    false)
                                                                    | S n26 ->
                                                                    (match n26 with
                                                                    | O ->
                                                                    Sextet
                                                                    (false,
                                                                    true,
                                                                    true,
                                                                    false,
                                                                    true,
                                                                    true)
                                                                    | S n27 ->
                                                                    (match n27 with
                                                                    | O ->
                                                                    Sextet
                                                                    (false,
                                                                    true,
                                                                    true,
                                                                    true,
                                                                    false,
                                                                    false)
                                                                    | S n28 ->
                                                                    (match n28 with
                                                                    | O ->
                                                                    Sextet
                                                                    (false,
                                                                    true,
                                                                    true,
                                                                    true,
                                                                    false,
                                                                    true)
                                                                    | S n29 ->
                                                                    (match n29 with
                                                                    | O ->
                                                                    Sextet
                                                                    (false,
                                                                    true,
                                                                    true,
                                                                    true,
                                                                    true,
                                                                    false)
                                                                    | S n30 ->
                                                                    (match n30 with
                                                                    | O ->
                                                                    Sextet
                                                                    (false,
                                                                    true,
                                                                    true,
                                                                    true,
                                                                    true,
                                                                    true)
                                                                    | S n31 ->
                                                                    (match n31 with
                                                                    | O ->
                                                                    Sextet
                                                                    (true,
                                                                    false,
                                                                    false,
                                                                    false,
                                                                    false,
                                                                    false)
                                                                    | S n32 ->
                                                                    (match n32 with
                                                                    | O ->
                                                                    Sextet
                                                                    (true,
                                                                    false,
                                                                    false,
                                                                    false,
                                                                    false,
                                                                    true)
                                                                    | S n33 ->
                                                                    (match n33 with
                                                                    | O ->
                                                                    Sextet
                                                                    (true,
                                                                    false,
                                                                    false,
                                                                    false,
                                                                    true,
                                                                    false)
                                                                    | S n34 ->
                                                                    (match n34 with
                                                                    | O ->
                                                                    Sextet
                                                                    (true,
                                                                    false,
                                                                    false,
                                                                    false,
                                                                    true,
                                                                    true)
                                                                    | S n35 ->
                                                                    (match n35 with
                                                                    | O ->
                                                                    Sextet
                                                                    (true,
                                                                    false,
                                                                    false,
                                                                    true,
                                                                    false,
                                                                    false)
                                                                    | S n36 ->
                                                                    (match n36 with
                                                                    | O ->
                                                                    Sextet
                                                                    (true,
                                                                    false,
                                                                    false,
                                                                    true,
                                                                    false,
                                                                    true)
                                                                    | S n37 ->
                                                                    (match n37 with
                                                                    | O ->
                                                                    Sextet
                                                                    (true,
                                                                    false,
                                                                    false,
                                                                    true,
                                                                    true,
                                                                    false)
                                                                    | S n38 ->
                                                                    (match n38 with
                                                                    | O ->
                                                                    Sextet
                                                                    (true,
                                                                    false,
                                                                    false,
                                                                    true,
                                                                    true,
                                                                    true)
                                                                    | S n39 ->
                                                                    (match n39 with
                                                                    | O ->
                                                                    Sextet
                                                                    (true,
                                                                    false,
                                                                    true,
                                                                    false,
                                                                    false,
                                                                    false)
                                                                    | S n40 ->
                                                                    (match n40 with
                                                                    | O ->
                                                                    Sextet
                                                                    (true,
                                                                    false,
                                                                    true,
                                                                    false,
                                                                    false,
                                                                    true)
                                                                    | S n41 ->
                                                                    (match n41 with
                                                                    | O ->
                                                                    Sextet
                                                                    (true,
                                                                    false,
                                                                    true,
                                                                    false,
                                                                    true,
                                                                    false)
                                                                    | S n42 ->
                                                                    (match n42 with
                                                                    | O ->
                                                                    Sextet
                                                                    (true,
                                                                    false,
                                                                    true,
                                                                    false,
                                                                    true,
                                                                    true)
                                                                    | S n43 ->
                                                                    (match n43 with
                                                                    | O ->
                                                                    Sextet
                                                                    (true,
                                                                    false,
                                                                    true,
                                                                    true,
                                                                    false,
                                                                    false)
                                                                    | S n44 ->
                                                                    (match n44 with
                                                                    | O ->
                                                                    Sextet
                                                                    (true,
                                                                    false,
                                                                    true,
                                                                    true,
                                                                    false,
                                                                    true)
                                                                    | S n45 ->
                                                                    (match n45 with
                                                                    | O ->
                                                                    Sextet
                                                                    (true,
                                                                    false,
                                                                    true,
                                                                    true,
                                                                    true,
                                                                    false)
                                                                    | S n46 ->
                                                                    (match n46 with
                                                                    | O ->
                                                                    Sextet
                                                                    (true,
                                                                    false,
                                                                    true,
                                                                    true,
                                                                    true,
                                                                    true)
                                                                    | S n47 ->
                                                                    (match n47 with
                                                                    | O ->
                                                                    Sextet
                                                                    (true,
                                                                    true,
                                                                    false,
                                                                    false,
                                                                    false,
                                                                    false)
                                                                    | S n48 ->
                                                                    (match n48 with
                                                                    | O ->
                                                                    Sextet
                                                                    (true,
                                                                    true,
                                                                    false,
                                                                    false,
                                                                    false,
                                                                    true)
                                                                    | S n49 ->
                                                                    (match n49 with
                                                                    | O ->
                                                                    Sextet
                                                                    (true,
                                                                    true,
                                                                    false,
                                                                    false,
                                                                    true,
                                                                    false)
                                                                    | S n50 ->
                                                                    (match n50 with
                                                                    | O ->
                                                                    Sextet
                                                                    (true,
                                                                    true,
                                                                    false,
                                                                    false,
                                                                    true,
                                                                    true)
                                                                    | S n51 ->
                                                                    (match n51 with
                                                                    | O ->
                                                                    Sextet
                                                                    (true,
                                                                    true,
                                                                    false,
                                                                    true,
                                                                    false,
                                                                    false)
                                                                    | S n52 ->
                                                                    (match n52 with
                                                                    | O ->
                                                                    Sextet
                                                                    (true,
                                                                    true,
                                                                    false,
                                                                    true,
                                                                    false,
                                                                    true)
                                                                    | S n53 ->
                                                                    (match n53 with
                                                                    | O ->
                                                                    Sextet
                                                                    (true,
                                                                    true,
                                                                    false,
                                                                    true,
                                                                    true,
                                                                    false)
                                                                    | S n54 ->
                                                                    (match n54 with
                                                                    | O ->
                                                                    Sextet
                                                                    (true,
                                                                    true,
                                                                    false,
                                                                    true,
                                                                    true,
                                                                    true)
                                                                    | S n55 ->
                                                                    (match n55 with
                                                                    | O ->
                                                                    Sextet
                                                                    (true,
                                                                    true,
                                                                    true,
                                                                    false,
                                                                    false,
                                                                    false)
                                                                    | S n56 ->
                                                                    (match n56 with
                                                                    | O ->
                                                                    Sextet
                                                                    (true,
                                                                    true,
                                                                    true,
                                                                    false,
                                                                    false,
                                                                    true)
                                                                    | S n57 ->
                                                                    (match n57 with
                                                                    | O ->
                                                                    Sextet
                                                                    (true,
                                                                    true,
                                                                    true,
                                                                    false,
                                                                    true,
                                                                    false)
                                                                    | S n58 ->
                                                                    (match n58 with
                                                                    | O ->
                                                                    Sextet
                                                                    (true,
                                                                    true,
                                                                    true,
                                                                    false,
                                                                    true,
                                                                    true)
                                                                    | S n59 ->
                                                                    (match n59 with
                                                                    | O ->
                                                                    Sextet
                                                                    (true,
                                                                    true,
                                                                    true,
                                                                    true,
                                                                    false,
                                                                    false)
                                                                    | S n60 ->
                                                                    (match n60 with
                                                                    | O ->
                                                                    Sextet
                                                                    (true,
                                                                    true,
                                                                    true,
                                                                    true,
                                                                    false,
                                                                    true)
                                                                    | S n61 ->
                                                                    (match n61 with
                                                                    | O ->
                                                                    Sextet
                                                                    (true,
                                                                    true,
                                                                    true,
                                                                    true,
                                                                    true,
                                                                    false)
                                                                    | S n62 ->
                                                                    (match n62 with
                                                                    | O ->
                                                                    Sextet
                                                                    (true,
                                                                    true,
                                                                    true,
                                                                    true,
                                                                    true,
                                                                    true)
                                                                    | S _ ->
                                                                    assert false
                                                                    (* absurd case *))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

type quadSextetList =
| QSnil
| QScons_one_pad of ((sextet * sextet) * sextet)
| QScons_two_pad of (sextet * sextet)
| QScons_all of (((sextet * sextet) * sextet) * sextet) * quadSextetList

type base64Options =
| Base64Standard
| Base64UrlAndFilenameSafe

(** val base64Alphabet : base64Options -> char list **)

let base64Alphabet = function
| Base64Standard ->
  let x =
    app
      (('A'::[]) :: (('B'::[]) :: (('C'::[]) :: (('D'::[]) :: (('E'::[]) :: (('F'::[]) :: (('G'::[]) :: (('H'::[]) :: (('I'::[]) :: (('J'::[]) :: (('K'::[]) :: (('L'::[]) :: (('M'::[]) :: (('N'::[]) :: (('O'::[]) :: (('P'::[]) :: (('Q'::[]) :: (('R'::[]) :: (('S'::[]) :: (('T'::[]) :: (('U'::[]) :: (('V'::[]) :: (('W'::[]) :: (('X'::[]) :: (('Y'::[]) :: (('Z'::[]) :: (('a'::[]) :: (('b'::[]) :: (('c'::[]) :: (('d'::[]) :: (('e'::[]) :: (('f'::[]) :: (('g'::[]) :: (('h'::[]) :: (('i'::[]) :: (('j'::[]) :: (('k'::[]) :: (('l'::[]) :: (('m'::[]) :: (('n'::[]) :: (('o'::[]) :: (('p'::[]) :: (('q'::[]) :: (('r'::[]) :: (('s'::[]) :: (('t'::[]) :: (('u'::[]) :: (('v'::[]) :: (('w'::[]) :: (('x'::[]) :: (('y'::[]) :: (('z'::[]) :: (('0'::[]) :: (('1'::[]) :: (('2'::[]) :: (('3'::[]) :: (('4'::[]) :: (('5'::[]) :: (('6'::[]) :: (('7'::[]) :: (('8'::[]) :: (('9'::[]) :: []))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
      (('+'::[]) :: (('/'::[]) :: []))
  in
  map_with_invariant (string_get_ascii_safe O) x
| Base64UrlAndFilenameSafe ->
  let x =
    app
      (('A'::[]) :: (('B'::[]) :: (('C'::[]) :: (('D'::[]) :: (('E'::[]) :: (('F'::[]) :: (('G'::[]) :: (('H'::[]) :: (('I'::[]) :: (('J'::[]) :: (('K'::[]) :: (('L'::[]) :: (('M'::[]) :: (('N'::[]) :: (('O'::[]) :: (('P'::[]) :: (('Q'::[]) :: (('R'::[]) :: (('S'::[]) :: (('T'::[]) :: (('U'::[]) :: (('V'::[]) :: (('W'::[]) :: (('X'::[]) :: (('Y'::[]) :: (('Z'::[]) :: (('a'::[]) :: (('b'::[]) :: (('c'::[]) :: (('d'::[]) :: (('e'::[]) :: (('f'::[]) :: (('g'::[]) :: (('h'::[]) :: (('i'::[]) :: (('j'::[]) :: (('k'::[]) :: (('l'::[]) :: (('m'::[]) :: (('n'::[]) :: (('o'::[]) :: (('p'::[]) :: (('q'::[]) :: (('r'::[]) :: (('s'::[]) :: (('t'::[]) :: (('u'::[]) :: (('v'::[]) :: (('w'::[]) :: (('x'::[]) :: (('y'::[]) :: (('z'::[]) :: (('0'::[]) :: (('1'::[]) :: (('2'::[]) :: (('3'::[]) :: (('4'::[]) :: (('5'::[]) :: (('6'::[]) :: (('7'::[]) :: (('8'::[]) :: (('9'::[]) :: []))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
      (('-'::[]) :: (('_'::[]) :: []))
  in
  map_with_invariant (string_get_ascii_safe O) x

type base64_Ascii = (char, __) sigT

type base64_String = (char list, __) sigT

(** val base64Padding : bool -> char **)

let base64Padding _ =
  '='

(** val packet_encode : base64Options -> sextet -> base64_Ascii **)

let packet_encode b p =
  ExistT ((nth_safe (sextet_to_nat p) (base64Alphabet b)), __)

(** val packet_decode : base64Options -> base64_Ascii -> sextet **)

let packet_decode b s =
  sextet_from_nat_safe
    (index_of_safe eqClass_Ascii (projT1 s) (base64Alphabet b))

(** val encodable_sextet_base64_ascii :
    base64Options -> (sextet, base64_Ascii) strictEncodable **)

let encodable_sextet_base64_ascii b =
  { strict_encode = (packet_encode b); strict_decode = (packet_decode b) }

(** val quadSextetList_encode :
    base64Options -> bool -> (sextet, base64_Ascii) strictEncodable ->
    quadSextetList -> base64_String **)

let rec quadSextetList_encode b padding h = function
| QSnil -> ExistT ([], __)
| QScons_one_pad p ->
  let (p0, p3) = p in
  let (p1, p2) = p0 in
  let ExistT (r1, _) = h.strict_encode p1 in
  let ExistT (r2, _) = h.strict_encode p2 in
  let ExistT (r3, _) = h.strict_encode p3 in
  ExistT ((r1::(r2::(r3::((base64Padding padding)::[])))), __)
| QScons_two_pad p ->
  let (p1, p2) = p in
  let ExistT (r1, _) = h.strict_encode p1 in
  let ExistT (r2, _) = h.strict_encode p2 in
  ExistT
  ((r1::(r2::((base64Padding padding)::((base64Padding padding)::[])))), __)
| QScons_all (p, rest) ->
  let (p0, p4) = p in
  let (p5, p3) = p0 in
  let (p1, p2) = p5 in
  let ExistT (r1, _) = h.strict_encode p1 in
  let ExistT (r2, _) = h.strict_encode p2 in
  let ExistT (r3, _) = h.strict_encode p3 in
  let ExistT (r4, _) = h.strict_encode p4 in
  let ExistT (rec0, _) = quadSextetList_encode b padding h rest in
  ExistT ((r1::(r2::(r3::(r4::rec0)))), __)

(** val quadSextetList_decode' :
    base64Options -> bool -> (sextet, base64_Ascii) strictEncodable ->
    char list -> quadSextetList **)

let rec quadSextetList_decode' b padding h = function
| [] -> if padding then QSnil else assert false (* absurd case *)
| a::s0 ->
  (match s0 with
   | [] -> assert false (* absurd case *)
   | a0::s1 ->
     (match s1 with
      | [] -> assert false (* absurd case *)
      | a1::s2 ->
        (match s2 with
         | [] -> assert false (* absurd case *)
         | a2::s3 ->
           let s4 = strict_in_dec eqClass_Ascii a (base64Alphabet b) in
           if s4
           then let s5 = strict_in_dec eqClass_Ascii a0 (base64Alphabet b) in
                if s5
                then let s6 =
                       strict_in_dec eqClass_Ascii a1 (base64Alphabet b)
                     in
                     if s6
                     then let s7 =
                            strict_in_dec eqClass_Ascii a2 (base64Alphabet b)
                          in
                          if s7
                          then if padding
                               then let a1' = h.strict_decode (ExistT (a, __))
                                    in
                                    let a2' =
                                      h.strict_decode (ExistT (a0, __))
                                    in
                                    let a3' =
                                      h.strict_decode (ExistT (a1, __))
                                    in
                                    let a4' =
                                      h.strict_decode (ExistT (a2, __))
                                    in
                                    let rec0 =
                                      quadSextetList_decode' b padding h s3
                                    in
                                    QScons_all ((((a1', a2'), a3'), a4'),
                                    rec0)
                               else assert false (* absurd case *)
                          else if padding
                               then let a1' = h.strict_decode (ExistT (a, __))
                                    in
                                    let a2' =
                                      h.strict_decode (ExistT (a0, __))
                                    in
                                    let a3' =
                                      h.strict_decode (ExistT (a1, __))
                                    in
                                    let b3 = (=) a2 '=' in
                                    if b3
                                    then (match s3 with
                                          | [] ->
                                            QScons_one_pad ((a1', a2'), a3')
                                          | _::_ ->
                                            assert false (* absurd case *))
                                    else assert false (* absurd case *)
                               else assert false (* absurd case *)
                     else if padding
                          then let a1' = h.strict_decode (ExistT (a, __)) in
                               let a2' = h.strict_decode (ExistT (a0, __)) in
                               let b2 = (=) a1 '=' in
                               if b2
                               then let b3 = (=) a2 '=' in
                                    if b3
                                    then (match s3 with
                                          | [] -> QScons_two_pad (a1', a2')
                                          | _::_ ->
                                            assert false (* absurd case *))
                                    else assert false (* absurd case *)
                               else assert false (* absurd case *)
                          else assert false (* absurd case *)
                else assert false (* absurd case *)
           else assert false (* absurd case *))))

(** val quadSextetList_decode :
    base64Options -> bool -> (sextet, base64_Ascii) strictEncodable ->
    base64_String -> quadSextetList **)

let quadSextetList_decode b padding h = function
| ExistT (x0, _) -> quadSextetList_decode' b padding h x0

(** val strictEncodable_quadsextetlist_base64_string :
    base64Options -> bool -> (sextet, base64_Ascii) strictEncodable ->
    (quadSextetList, base64_String) strictEncodable **)

let strictEncodable_quadsextetlist_base64_string b padding h =
  { strict_encode = (quadSextetList_encode b padding h); strict_decode =
    (quadSextetList_decode b padding h) }

(** val string_to_quadsextetlist :
    ((char * char) * char, ((sextet * sextet) * sextet) * sextet)
    strictEncodable -> (char * char, (sextet * sextet) * sextet)
    strictEncodable -> (char, sextet * sextet) strictEncodable -> char list
    -> quadSextetList **)

let rec string_to_quadsextetlist hE1 hE2 hE3 = function
| [] -> QSnil
| a1::s' ->
  (match s' with
   | [] -> QScons_two_pad (hE3.strict_encode a1)
   | a2::s'' ->
     (match s'' with
      | [] -> QScons_one_pad (hE2.strict_encode (a1, a2))
      | a3::rest ->
        QScons_all ((hE1.strict_encode ((a1, a2), a3)),
          (string_to_quadsextetlist hE1 hE2 hE3 rest))))

(** val strictEncodable_ascii_two_sextet :
    (char, sextet * sextet) strictEncodable **)

let strictEncodable_ascii_two_sextet =
  { strict_encode = (fun a ->
    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
      (fun b7 b6 b5 b4 b3 b2 b1 b0 -> ((Sextet (b0, b1, b2, b3, b4, b5)),
      (Sextet (b6, b7, false, false, false, false))))
      a); strict_decode = (fun pat ->
    let (p1, p2) = pat in
    let Sextet (b0, b1, b2, b3, b4, b5) = p1 in
    let Sextet (b6, b7, _, _, _, _) = p2 in
    (* If this appears, you're using Ascii internals. Please don't *)
 (fun (b0,b1,b2,b3,b4,b5,b6,b7) ->
  let f b i = if b then 1 lsl i else 0 in
  Char.chr (f b0 0 + f b1 1 + f b2 2 + f b3 3 + f b4 4 + f b5 5 + f b6 6 + f b7 7))
    (b7, b6, b5, b4, b3, b2, b1, b0)) }

(** val strictEncodable_two_ascii_three_sextet :
    (char * char, (sextet * sextet) * sextet) strictEncodable **)

let strictEncodable_two_ascii_three_sextet =
  { strict_encode = (fun pat ->
    let (a1, a2) = pat in
    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
      (fun b7 b6 b5 b4 b3 b2 b1 b0 ->
      (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
        (fun b15 b14 b13 b12 b11 b10 b9 b8 -> (((Sextet (b0, b1, b2, b3, b4,
        b5)), (Sextet (b6, b7, b8, b9, b10, b11))), (Sextet (b12, b13, b14,
        b15, false, false))))
        a2)
      a1); strict_decode = (fun pat ->
    let (y, p3) = pat in
    let (p1, p2) = y in
    let Sextet (b0, b1, b2, b3, b4, b5) = p1 in
    let Sextet (b6, b7, b8, b9, b10, b11) = p2 in
    let Sextet (b12, b13, b14, b15, _, _) = p3 in
    (((* If this appears, you're using Ascii internals. Please don't *)
 (fun (b0,b1,b2,b3,b4,b5,b6,b7) ->
  let f b i = if b then 1 lsl i else 0 in
  Char.chr (f b0 0 + f b1 1 + f b2 2 + f b3 3 + f b4 4 + f b5 5 + f b6 6 + f b7 7))
    (b7, b6, b5, b4, b3, b2, b1, b0)),
    ((* If this appears, you're using Ascii internals. Please don't *)
 (fun (b0,b1,b2,b3,b4,b5,b6,b7) ->
  let f b i = if b then 1 lsl i else 0 in
  Char.chr (f b0 0 + f b1 1 + f b2 2 + f b3 3 + f b4 4 + f b5 5 + f b6 6 + f b7 7))
    (b15, b14, b13, b12, b11, b10, b9, b8)))) }

(** val strictEncodable_three_ascii_four_sextet :
    ((char * char) * char, ((sextet * sextet) * sextet) * sextet)
    strictEncodable **)

let strictEncodable_three_ascii_four_sextet =
  { strict_encode = (fun pat ->
    let (y, a3) = pat in
    let (a1, a2) = y in
    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
      (fun b7 b6 b5 b4 b3 b2 b1 b0 ->
      (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
        (fun b15 b14 b13 b12 b11 b10 b9 b8 ->
        (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
          (fun b23 b22 b21 b20 b19 b18 b17 b16 -> ((((Sextet (b0, b1, b2, b3,
          b4, b5)), (Sextet (b6, b7, b8, b9, b10, b11))), (Sextet (b12, b13,
          b14, b15, b16, b17))), (Sextet (b18, b19, b20, b21, b22, b23))))
          a3)
        a2)
      a1); strict_decode = (fun pat ->
    let (y, p4) = pat in
    let (y0, p3) = y in
    let (p1, p2) = y0 in
    let Sextet (b0, b1, b2, b3, b4, b5) = p1 in
    let Sextet (b6, b7, b8, b9, b10, b11) = p2 in
    let Sextet (b12, b13, b14, b15, b16, b17) = p3 in
    let Sextet (b18, b19, b20, b21, b22, b23) = p4 in
    ((((* If this appears, you're using Ascii internals. Please don't *)
 (fun (b0,b1,b2,b3,b4,b5,b6,b7) ->
  let f b i = if b then 1 lsl i else 0 in
  Char.chr (f b0 0 + f b1 1 + f b2 2 + f b3 3 + f b4 4 + f b5 5 + f b6 6 + f b7 7))
    (b7, b6, b5, b4, b3, b2, b1, b0)),
    ((* If this appears, you're using Ascii internals. Please don't *)
 (fun (b0,b1,b2,b3,b4,b5,b6,b7) ->
  let f b i = if b then 1 lsl i else 0 in
  Char.chr (f b0 0 + f b1 1 + f b2 2 + f b3 3 + f b4 4 + f b5 5 + f b6 6 + f b7 7))
    (b15, b14, b13, b12, b11, b10, b9, b8))),
    ((* If this appears, you're using Ascii internals. Please don't *)
 (fun (b0,b1,b2,b3,b4,b5,b6,b7) ->
  let f b i = if b then 1 lsl i else 0 in
  Char.chr (f b0 0 + f b1 1 + f b2 2 + f b3 3 + f b4 4 + f b5 5 + f b6 6 + f b7 7))
    (b23, b22, b21, b20, b19, b18, b17, b16)))) }

(** val string_from_quadsextetlist :
    ((char * char) * char, ((sextet * sextet) * sextet) * sextet)
    strictEncodable -> (char * char, (sextet * sextet) * sextet)
    strictEncodable -> (char, sextet * sextet) strictEncodable ->
    quadSextetList -> char list **)

let rec string_from_quadsextetlist hE1 hE2 hE3 = function
| QSnil -> []
| QScons_one_pad p -> let (a1, a2) = hE2.strict_decode p in a1::(a2::[])
| QScons_two_pad p -> let a1 = hE3.strict_decode p in a1::[]
| QScons_all (p, rest) ->
  let (y, a3) = hE1.strict_decode p in
  let (a1, a2) = y in
  a1::(a2::(a3::(string_from_quadsextetlist hE1 hE2 hE3 rest)))

(** val strictEncodable_string_quadsextetlist :
    ((char * char) * char, ((sextet * sextet) * sextet) * sextet)
    strictEncodable -> (char * char, (sextet * sextet) * sextet)
    strictEncodable -> (char, sextet * sextet) strictEncodable -> (char list,
    quadSextetList) strictEncodable **)

let strictEncodable_string_quadsextetlist hE1 hE2 hE3 =
  { strict_encode = (string_to_quadsextetlist hE1 hE2 hE3); strict_decode =
    (string_from_quadsextetlist hE1 hE2 hE3) }

(** val strictEncodable_string_base64_string_pad :
    base64Options -> bool -> (char list, base64_String) strictEncodable **)

let strictEncodable_string_base64_string_pad b padding =
  let h =
    strictEncodable_string_quadsextetlist
      strictEncodable_three_ascii_four_sextet
      strictEncodable_two_ascii_three_sextet strictEncodable_ascii_two_sextet
  in
  let h0 =
    strictEncodable_quadsextetlist_base64_string b padding
      (encodable_sextet_base64_ascii b)
  in
  { strict_encode = (fun s -> h0.strict_encode (h.strict_encode s));
  strict_decode = (fun s -> h.strict_decode (h0.strict_decode s)) }

(** val string_to_base64_string_no_pad :
    base64Options -> bool -> (sextet, base64_Ascii) strictEncodable ->
    ((char * char) * char, ((sextet * sextet) * sextet) * sextet)
    strictEncodable -> (char * char, (sextet * sextet) * sextet)
    strictEncodable -> (char, sextet * sextet) strictEncodable -> char list
    -> base64_String **)

let rec string_to_base64_string_no_pad b padding h hE1 hE2 hE3 = function
| [] -> ExistT ([], __)
| a::s0 ->
  (match s0 with
   | [] ->
     let h0 = hE3.strict_encode a in
     let (s1, s2) = h0 in
     let y = h.strict_encode s1 in
     let ExistT (x, _) = y in
     let y0 = h.strict_encode s2 in
     let ExistT (x0, _) = y0 in ExistT ((x::(x0::[])), __)
   | a0::s1 ->
     (match s1 with
      | [] ->
        let h0 = hE2.strict_encode (a, a0) in
        let (p, s2) = h0 in
        let (s3, s4) = p in
        let y = h.strict_encode s3 in
        let ExistT (x, _) = y in
        let y0 = h.strict_encode s4 in
        let ExistT (x0, _) = y0 in
        let y1 = h.strict_encode s2 in
        let ExistT (x1, _) = y1 in ExistT ((x::(x0::(x1::[]))), __)
      | a1::s2 ->
        let h0 = hE1.strict_encode ((a, a0), a1) in
        let (p, s3) = h0 in
        let (p0, s4) = p in
        let (s5, s6) = p0 in
        let y = h.strict_encode s5 in
        let ExistT (x, _) = y in
        let y0 = h.strict_encode s6 in
        let ExistT (x0, _) = y0 in
        let y1 = h.strict_encode s4 in
        let ExistT (x1, _) = y1 in
        let y2 = h.strict_encode s3 in
        let ExistT (x2, _) = y2 in
        let b0 = string_to_base64_string_no_pad b padding h hE1 hE2 hE3 s2 in
        let ExistT (x3, _) = b0 in ExistT ((x::(x0::(x1::(x2::x3)))), __)))

(** val base64_string_to_string_no_pad' :
    base64Options -> bool -> (sextet, base64_Ascii) strictEncodable ->
    ((char * char) * char, ((sextet * sextet) * sextet) * sextet)
    strictEncodable -> (char * char, (sextet * sextet) * sextet)
    strictEncodable -> (char, sextet * sextet) strictEncodable -> char list
    -> char list **)

let rec base64_string_to_string_no_pad' b padding h hE1 hE2 hE3 = function
| [] -> []
| a::s0 ->
  (match s0 with
   | [] -> assert false (* absurd case *)
   | a0::s1 ->
     (match s1 with
      | [] ->
        let s2 = strict_in_dec eqClass_Ascii a (base64Alphabet b) in
        if s2
        then let s3 = strict_in_dec eqClass_Ascii a0 (base64Alphabet b) in
             if s3
             then let sx1 = h.strict_decode (ExistT (a, __)) in
                  let sx2 = h.strict_decode (ExistT (a0, __)) in
                  let s4 = hE3.strict_decode (sx1, sx2) in s4::[]
             else assert false (* absurd case *)
        else assert false (* absurd case *)
      | a1::s2 ->
        (match s2 with
         | [] ->
           let s3 = strict_in_dec eqClass_Ascii a (base64Alphabet b) in
           if s3
           then let s4 = strict_in_dec eqClass_Ascii a0 (base64Alphabet b) in
                if s4
                then let s5 =
                       strict_in_dec eqClass_Ascii a1 (base64Alphabet b)
                     in
                     if s5
                     then let sx1 = h.strict_decode (ExistT (a, __)) in
                          let sx2 = h.strict_decode (ExistT (a0, __)) in
                          let sx3 = h.strict_decode (ExistT (a1, __)) in
                          let y = hE2.strict_decode ((sx1, sx2), sx3) in
                          let (a2, a3) = y in a2::(a3::[])
                     else assert false (* absurd case *)
                else assert false (* absurd case *)
           else assert false (* absurd case *)
         | a2::s3 ->
           let s4 = strict_in_dec eqClass_Ascii a (base64Alphabet b) in
           if s4
           then let s5 = strict_in_dec eqClass_Ascii a0 (base64Alphabet b) in
                if s5
                then let s6 =
                       strict_in_dec eqClass_Ascii a1 (base64Alphabet b)
                     in
                     if s6
                     then let s7 =
                            strict_in_dec eqClass_Ascii a2 (base64Alphabet b)
                          in
                          if s7
                          then let sx1 = h.strict_decode (ExistT (a, __)) in
                               let sx2 = h.strict_decode (ExistT (a0, __)) in
                               let sx3 = h.strict_decode (ExistT (a1, __)) in
                               let sx4 = h.strict_decode (ExistT (a2, __)) in
                               let y =
                                 hE1.strict_decode (((sx1, sx2), sx3), sx4)
                               in
                               let (p, a3) = y in
                               let (a4, a5) = p in
                               let rec0 =
                                 base64_string_to_string_no_pad' b padding h
                                   hE1 hE2 hE3 s3
                               in
                               a4::(a5::(a3::rec0))
                          else if padding
                               then assert false (* absurd case *)
                               else s3
                     else if padding
                          then assert false (* absurd case *)
                          else s3
                else assert false (* absurd case *)
           else assert false (* absurd case *))))

(** val base64_string_to_string_no_pad :
    base64Options -> bool -> (sextet, base64_Ascii) strictEncodable ->
    ((char * char) * char, ((sextet * sextet) * sextet) * sextet)
    strictEncodable -> (char * char, (sextet * sextet) * sextet)
    strictEncodable -> (char, sextet * sextet) strictEncodable ->
    base64_String -> char list **)

let base64_string_to_string_no_pad b padding h hE1 hE2 hE3 = function
| ExistT (x0, _) -> base64_string_to_string_no_pad' b padding h hE1 hE2 hE3 x0

(** val strictEncodable_string_base64_string_no_pad :
    base64Options -> bool -> (sextet, base64_Ascii) strictEncodable ->
    ((char * char) * char, ((sextet * sextet) * sextet) * sextet)
    strictEncodable -> (char * char, (sextet * sextet) * sextet)
    strictEncodable -> (char, sextet * sextet) strictEncodable -> (char list,
    base64_String) strictEncodable **)

let strictEncodable_string_base64_string_no_pad b padding h hE1 hE2 hE3 =
  { strict_encode = (string_to_base64_string_no_pad b padding h hE1 hE2 hE3);
    strict_decode = (base64_string_to_string_no_pad b padding h hE1 hE2 hE3) }

(** val strictEncodable_string_base64_string :
    base64Options -> bool -> (char list, base64_String) strictEncodable **)

let strictEncodable_string_base64_string b padding = match padding with
| true -> strictEncodable_string_base64_string_pad b padding
| false ->
  strictEncodable_string_base64_string_no_pad b padding
    (encodable_sextet_base64_ascii b) strictEncodable_three_ascii_four_sextet
    strictEncodable_two_ascii_three_sextet strictEncodable_ascii_two_sextet

(** val standardPaddedStringEncoder :
    (char list, base64_String) strictEncodable **)

let standardPaddedStringEncoder =
  strictEncodable_string_base64_string Base64Standard true
