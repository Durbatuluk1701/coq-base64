
type __ = Obj.t

type nat =
| O
| S of nat

val app : 'a1 list -> 'a1 list -> 'a1 list

type ('a, 'p) sigT =
| ExistT of 'a * 'p

val projT1 : ('a1, 'a2) sigT -> 'a1



type ('a, 'b) strictEncodable = { strict_encode : ('a -> 'b);
                                  strict_decode : ('b -> 'a) }

type 'a eqClass =
  'a -> 'a -> bool
  (* singleton inductive, whose constructor was Build_EqClass *)

type 'a decEq =
  'a -> 'a -> bool
  (* singleton inductive, whose constructor was Build_DecEq *)

val decEq_from_EqClass : 'a1 eqClass -> 'a1 decEq

val eqClass_Ascii : char eqClass

val strict_in_dec : 'a1 eqClass -> 'a1 -> 'a1 list -> bool

val string_get_ascii_safe : nat -> (char list, __) sigT -> char

val map_with_invariant : (('a1, __) sigT -> 'a2) -> 'a1 list -> 'a2 list

val nth_safe : nat -> 'a1 list -> 'a1

val index_of_safe : 'a1 eqClass -> 'a1 -> 'a1 list -> nat

type sextet =
| Sextet of bool * bool * bool * bool * bool * bool

val sextet_to_nat : sextet -> nat

val sextet_from_nat_safe : nat -> sextet

type quadSextetList =
| QSnil
| QScons_one_pad of ((sextet * sextet) * sextet)
| QScons_two_pad of (sextet * sextet)
| QScons_all of (((sextet * sextet) * sextet) * sextet) * quadSextetList

type base64Options =
| Base64Standard
| Base64UrlAndFilenameSafe

val base64Alphabet : base64Options -> char list

type base64_Ascii = (char, __) sigT

type base64_String = (char list, __) sigT

val base64Padding : bool -> char

val packet_encode : base64Options -> sextet -> base64_Ascii

val packet_decode : base64Options -> base64_Ascii -> sextet

val encodable_sextet_base64_ascii :
  base64Options -> (sextet, base64_Ascii) strictEncodable

val quadSextetList_encode :
  base64Options -> bool -> (sextet, base64_Ascii) strictEncodable ->
  quadSextetList -> base64_String

val quadSextetList_decode' :
  base64Options -> bool -> (sextet, base64_Ascii) strictEncodable ->
  char list -> quadSextetList

val quadSextetList_decode :
  base64Options -> bool -> (sextet, base64_Ascii) strictEncodable ->
  base64_String -> quadSextetList

val strictEncodable_quadsextetlist_base64_string :
  base64Options -> bool -> (sextet, base64_Ascii) strictEncodable ->
  (quadSextetList, base64_String) strictEncodable

val string_to_quadsextetlist :
  ((char * char) * char, ((sextet * sextet) * sextet) * sextet)
  strictEncodable -> (char * char, (sextet * sextet) * sextet)
  strictEncodable -> (char, sextet * sextet) strictEncodable -> char list ->
  quadSextetList

val strictEncodable_ascii_two_sextet : (char, sextet * sextet) strictEncodable

val strictEncodable_two_ascii_three_sextet :
  (char * char, (sextet * sextet) * sextet) strictEncodable

val strictEncodable_three_ascii_four_sextet :
  ((char * char) * char, ((sextet * sextet) * sextet) * sextet)
  strictEncodable

val string_from_quadsextetlist :
  ((char * char) * char, ((sextet * sextet) * sextet) * sextet)
  strictEncodable -> (char * char, (sextet * sextet) * sextet)
  strictEncodable -> (char, sextet * sextet) strictEncodable ->
  quadSextetList -> char list

val strictEncodable_string_quadsextetlist :
  ((char * char) * char, ((sextet * sextet) * sextet) * sextet)
  strictEncodable -> (char * char, (sextet * sextet) * sextet)
  strictEncodable -> (char, sextet * sextet) strictEncodable -> (char list,
  quadSextetList) strictEncodable

val strictEncodable_string_base64_string_pad :
  base64Options -> bool -> (char list, base64_String) strictEncodable

val string_to_base64_string_no_pad :
  base64Options -> bool -> (sextet, base64_Ascii) strictEncodable ->
  ((char * char) * char, ((sextet * sextet) * sextet) * sextet)
  strictEncodable -> (char * char, (sextet * sextet) * sextet)
  strictEncodable -> (char, sextet * sextet) strictEncodable -> char list ->
  base64_String

val base64_string_to_string_no_pad' :
  base64Options -> bool -> (sextet, base64_Ascii) strictEncodable ->
  ((char * char) * char, ((sextet * sextet) * sextet) * sextet)
  strictEncodable -> (char * char, (sextet * sextet) * sextet)
  strictEncodable -> (char, sextet * sextet) strictEncodable -> char list ->
  char list

val base64_string_to_string_no_pad :
  base64Options -> bool -> (sextet, base64_Ascii) strictEncodable ->
  ((char * char) * char, ((sextet * sextet) * sextet) * sextet)
  strictEncodable -> (char * char, (sextet * sextet) * sextet)
  strictEncodable -> (char, sextet * sextet) strictEncodable -> base64_String
  -> char list

val strictEncodable_string_base64_string_no_pad :
  base64Options -> bool -> (sextet, base64_Ascii) strictEncodable ->
  ((char * char) * char, ((sextet * sextet) * sextet) * sextet)
  strictEncodable -> (char * char, (sextet * sextet) * sextet)
  strictEncodable -> (char, sextet * sextet) strictEncodable -> (char list,
  base64_String) strictEncodable

val strictEncodable_string_base64_string :
  base64Options -> bool -> (char list, base64_String) strictEncodable

val standardPaddedStringEncoder : (char list, base64_String) strictEncodable
