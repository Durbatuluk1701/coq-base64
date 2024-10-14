(* 
  This is an implementation of the Base64 encoding and decoding algorithm in Coq.

  Specifically, this will abide by RFC4648, which is the (current) standard for Base64 encoding and decoding.
*)
Require Import Coq.Strings.String Coq.Lists.List.
Import ListNotations.
Open Scope string_scope.
Require Import Lia.

(* Some Ltac *)
Ltac break_match :=
  match goal with
  | |- context [match ?x with _ => _ end] => destruct x eqn:?
  | H : context [match ?x with _ => _ end] |- _ => destruct x eqn:?
  end.

Ltac inv H := inversion H; subst; clear H.

Class StrictEncodable (A B : Type) := {
  strict_encode : A -> B;
  strict_decode : B -> A;
  strict_invol : forall a, strict_decode (strict_encode a) = a
}.

Class Encodable (A B : Type) := {
  encode : A -> B;
  decode : B -> option A;
  invol : forall a, decode (encode a) = Some a
}.

Class DecEq (A : Type) := {
  eqb : A -> A -> bool;
  eqb_eq : forall x y, eqb x y = true <-> x = y
}.

Lemma eqb_refl : forall A `{DecEq A} (a : A),
  eqb a a = true.
Proof.
  intros; rewrite eqb_eq; reflexivity.
Qed.

Global Instance DecEq_nat : DecEq nat := {
  eqb := Nat.eqb;
  eqb_eq := PeanoNat.Nat.eqb_eq
}.

Global Instance DecEq_Ascii : DecEq Ascii.ascii := {
  eqb := Ascii.eqb;
  eqb_eq := Ascii.eqb_eq
}.

Global Instance DecEq_string : DecEq string := {
  eqb := String.eqb;
  eqb_eq := String.eqb_eq
}.

Inductive Base64Options :=
| Base64Standard
| Base64UrlAndFilenameSafe.

Inductive Sextet := sextet (_ _ _ _ _ _ : bool).

Definition Sextet_to_nat (s : Sextet) : nat :=
  let '(sextet b1 b2 b3 b4 b5 b6) := s in
  match b1, b2, b3, b4, b5, b6 with
  | false, false, false, false, false, false => 0
  | false, false, false, false, false, true => 1
  | false, false, false, false, true, false => 2
  | false, false, false, false, true, true => 3
  | false, false, false, true, false, false => 4
  | false, false, false, true, false, true => 5
  | false, false, false, true, true, false => 6
  | false, false, false, true, true, true => 7
  | false, false, true, false, false, false => 8
  | false, false, true, false, false, true => 9
  | false, false, true, false, true, false => 10
  | false, false, true, false, true, true => 11
  | false, false, true, true, false, false => 12
  | false, false, true, true, false, true => 13
  | false, false, true, true, true, false => 14
  | false, false, true, true, true, true => 15
  | false, true, false, false, false, false => 16
  | false, true, false, false, false, true => 17
  | false, true, false, false, true, false => 18
  | false, true, false, false, true, true => 19
  | false, true, false, true, false, false => 20
  | false, true, false, true, false, true => 21
  | false, true, false, true, true, false => 22
  | false, true, false, true, true, true => 23
  | false, true, true, false, false, false => 24
  | false, true, true, false, false, true => 25
  | false, true, true, false, true, false => 26
  | false, true, true, false, true, true => 27
  | false, true, true, true, false, false => 28
  | false, true, true, true, false, true => 29
  | false, true, true, true, true, false => 30
  | false, true, true, true, true, true => 31
  | true, false, false, false, false, false => 32
  | true, false, false, false, false, true => 33
  | true, false, false, false, true, false => 34
  | true, false, false, false, true, true => 35
  | true, false, false, true, false, false => 36
  | true, false, false, true, false, true => 37
  | true, false, false, true, true, false => 38
  | true, false, false, true, true, true => 39
  | true, false, true, false, false, false => 40
  | true, false, true, false, false, true => 41
  | true, false, true, false, true, false => 42
  | true, false, true, false, true, true => 43
  | true, false, true, true, false, false => 44
  | true, false, true, true, false, true => 45
  | true, false, true, true, true, false => 46
  | true, false, true, true, true, true => 47
  | true, true, false, false, false, false => 48
  | true, true, false, false, false, true => 49
  | true, true, false, false, true, false => 50
  | true, true, false, false, true, true => 51
  | true, true, false, true, false, false => 52
  | true, true, false, true, false, true => 53
  | true, true, false, true, true, false => 54
  | true, true, false, true, true, true => 55
  | true, true, true, false, false, false => 56
  | true, true, true, false, false, true => 57
  | true, true, true, false, true, false => 58
  | true, true, true, false, true, true => 59
  | true, true, true, true, false, false => 60
  | true, true, true, true, false, true => 61
  | true, true, true, true, true, false => 62
  | true, true, true, true, true, true => 63
  end.

Definition Sextet_from_nat (n : nat) : option Sextet :=
  match n with
  | 0 => Some (sextet false false false false false false)
  | 1 => Some (sextet false false false false false true)
  | 2 => Some (sextet false false false false true false)
  | 3 => Some (sextet false false false false true true)
  | 4 => Some (sextet false false false true false false)
  | 5 => Some (sextet false false false true false true)
  | 6 => Some (sextet false false false true true false)
  | 7 => Some (sextet false false false true true true)
  | 8 => Some (sextet false false true false false false)
  | 9 => Some (sextet false false true false false true)
  | 10 => Some (sextet false false true false true false)
  | 11 => Some (sextet false false true false true true)
  | 12 => Some (sextet false false true true false false)
  | 13 => Some (sextet false false true true false true)
  | 14 => Some (sextet false false true true true false)
  | 15 => Some (sextet false false true true true true)
  | 16 => Some (sextet false true false false false false)
  | 17 => Some (sextet false true false false false true)
  | 18 => Some (sextet false true false false true false)
  | 19 => Some (sextet false true false false true true)
  | 20 => Some (sextet false true false true false false)
  | 21 => Some (sextet false true false true false true)
  | 22 => Some (sextet false true false true true false)
  | 23 => Some (sextet false true false true true true)
  | 24 => Some (sextet false true true false false false)
  | 25 => Some (sextet false true true false false true)
  | 26 => Some (sextet false true true false true false)
  | 27 => Some (sextet false true true false true true)
  | 28 => Some (sextet false true true true false false)
  | 29 => Some (sextet false true true true false true)
  | 30 => Some (sextet false true true true true false)
  | 31 => Some (sextet false true true true true true)
  | 32 => Some (sextet true false false false false false)
  | 33 => Some (sextet true false false false false true)
  | 34 => Some (sextet true false false false true false)
  | 35 => Some (sextet true false false false true true)
  | 36 => Some (sextet true false false true false false)
  | 37 => Some (sextet true false false true false true)
  | 38 => Some (sextet true false false true true false)
  | 39 => Some (sextet true false false true true true)
  | 40 => Some (sextet true false true false false false)
  | 41 => Some (sextet true false true false false true)
  | 42 => Some (sextet true false true false true false)
  | 43 => Some (sextet true false true false true true)
  | 44 => Some (sextet true false true true false false)
  | 45 => Some (sextet true false true true false true)
  | 46 => Some (sextet true false true true true false)
  | 47 => Some (sextet true false true true true true)
  | 48 => Some (sextet true true false false false false)
  | 49 => Some (sextet true true false false false true)
  | 50 => Some (sextet true true false false true false)
  | 51 => Some (sextet true true false false true true)
  | 52 => Some (sextet true true false true false false)
  | 53 => Some (sextet true true false true false true)
  | 54 => Some (sextet true true false true true false)
  | 55 => Some (sextet true true false true true true)
  | 56 => Some (sextet true true true false false false)
  | 57 => Some (sextet true true true false false true)
  | 58 => Some (sextet true true true false true false)
  | 59 => Some (sextet true true true false true true)
  | 60 => Some (sextet true true true true false false)
  | 61 => Some (sextet true true true true false true)
  | 62 => Some (sextet true true true true true false)
  | 63 => Some (sextet true true true true true true)
  | _ => None
  end.

Ltac dec_encode :=
  let v := fresh "v" in
  intros v;
  destruct v;
  simpl in *;
  repeat (break_match; simpl in *; try simple congruence 3; eauto;
    try lia); eauto.

Global Instance encodable_sextet_nat : Encodable Sextet nat.
eapply Build_Encodable with 
  (encode := Sextet_to_nat)
  (decode := Sextet_from_nat).
dec_encode.
Defined.

Lemma Sextet_to_nat_lt_64 : forall p,
  Sextet_to_nat p < 64.
Proof.
  induction p; simpl in *;
  repeat match goal with
  | b : bool |- _ => destruct b; try lia
  end.
Qed.

Inductive QuadSextetList :=
| QSnil
| QScons_one_pad : Sextet * Sextet * Sextet -> QuadSextetList
| QScons_two_pad : Sextet * Sextet -> QuadSextetList
| QScons_all : 
  Sextet * Sextet * Sextet * Sextet -> 
  QuadSextetList -> QuadSextetList.

(* Option Notation *)
Notation "x <- a ;; b" := 
  (match a with
  | Some x => b
  | None => None
  end) (right associativity, at level 60).

(*
Notation "' pat <- a ;; b" := 
  (match a with
  | Some pat => b
  | None => None
  end) (right associativity, at level 60, pat pattern). *)

Module Base64.

  Parameter b : Base64Options.

  Fixpoint string_get_ascii_safe (n : nat) 
    (s : { s & n < String.length s }) : Ascii.ascii.
    (* `{HL : n < String.length s} : Ascii.ascii. *)
    destruct s eqn:E; simpl in *.
    destruct x eqn:E1; simpl in *.
    - lia.
    - destruct n.
      * (* n = 0 *) exact a.
      * (* n = S n' *)
        eapply (string_get_ascii_safe n).
        econstructor.
        eapply (PeanoNat.lt_S_n _ _ l).
  Defined.

  Print List.map.

  Definition map_with_invariant {A B : Type} (P : A -> Prop) 
      (f : { a & P a} -> B) :
      forall a : list A, (forall x, In x a -> P x) -> list B.
    refine (fix F l HL :=
      (match l as l' return l = l' -> list B with
      | [] => fun Heq => []
      | h :: t => fun Heq => f _ :: F t _
      end) eq_refl); subst; simpl in *.
    - econstructor; eapply (HL h); eauto.
    - eauto.
  Defined.

  Definition Base64Alphabet : list Ascii.ascii.
    set (x :=
    List.app [
    "A"; "B"; "C"; "D"; "E"; "F"; "G"; "H";
    "I"; "J"; "K"; "L"; "M"; "N"; "O"; "P";
    "Q"; "R"; "S"; "T"; "U"; "V"; "W"; "X"; 
    "Y"; "Z"; "a"; "b"; "c"; "d"; "e"; "f"; 
    "g"; "h"; "i"; "j"; "k"; "l"; "m"; "n"; 
    "o"; "p"; "q"; "r"; "s"; "t"; "u"; "v"; 
    "w"; "x"; "y"; "z"; "0"; "1"; "2"; "3";
    "4"; "5"; "6"; "7"; "8"; "9" ] 
    (match b with
    | Base64Standard => ["+"; "/"]
    | Base64UrlAndFilenameSafe => ["-"; "_"]
    end)).
    destruct b; simpl in *;
    eapply (map_with_invariant _ (string_get_ascii_safe 0) x);
    intros; subst x; simpl in *;
    repeat match goal with
    | H : _ \/ _ |- _ => destruct H; simpl in *; subst; eauto
    end; intuition.
  Defined.

  Definition Base64Padding_special : Ascii.ascii. 
    set (x := string_get_ascii_safe 0).
    eapply x.
    eapply (existT) with (x := "=");
    simpl in *.
    lia.
  Defined.

  Definition Base64Padding : Ascii.ascii := 
    Ascii.Ascii true false true true true true false false.
  
  Lemma Base64Padding_eq_special : Base64Padding = Base64Padding_special.
  reflexivity.
  Qed.

  Lemma Base64AlphabetLengthCorrect : List.length Base64Alphabet = 64.
  Proof.
    unfold Base64Alphabet; destruct b; reflexivity.
  Qed.

  Lemma NoDupBase64Alphabet : NoDup Base64Alphabet.
  Proof.
    unfold Base64Alphabet; simpl in *.
    destruct b; simpl in *;
    repeat (econstructor; [ 
      intros HC;
      repeat match goal with
      | H : _ |- _ =>
        inv H; try congruence
      end | ]);
    econstructor.
  Qed.

  Fixpoint nth_safe {A : Type} (n : nat) (l : list A)
      `{HL : n < List.length l} : A.
    destruct l eqn:E; simpl in *.
    - lia.
    - destruct n.
      * (* n = 0 *) exact a.
      * (* n = S n' *)
        eapply (nth_safe _ n l0);
        eapply (PeanoNat.lt_S_n _ _ HL).
  Defined.

  Definition packet_encode (p : Sextet) : Ascii.ascii.
    refine (nth_safe (encode p) Base64Alphabet).
  rewrite Base64AlphabetLengthCorrect;
  eapply Sextet_to_nat_lt_64.
  Defined.

  Lemma in_nth_safe : forall A (l : list A) n `{HL : n < List.length l},
    In (@nth_safe _ n l HL) l.
  Proof.
    induction l; simpl in *; intuition; try lia.
    destruct n; eauto.
  Qed.

  Lemma packet_encode_in_alphabet : forall p,
    In (packet_encode p) Base64Alphabet.
  Proof.
    induction p.
    unfold packet_encode.
    eapply in_nth_safe.
  Qed.

  Lemma Base64Padding_not_in_alphabet : 
    ~ In Base64Padding Base64Alphabet.
  Proof.
    unfold Base64Alphabet, Base64Padding;
    destruct b; simpl in *; intros HC;
    repeat match goal with
    | H : _ \/ _ |- _ => 
      destruct H; simpl in *; try congruence; subst; eauto
    end.
  Qed.

  Fixpoint index_of {A : Type} `{DecEq A} (s : A) (l : list A) : option nat :=
    match l with
    | [] => None
    | h :: t => if eqb s h then Some 0 else
      match index_of s t with
      | Some n => Some (S n)
      | None => None
      end
    end.

  Definition packet_decode (s : Ascii.ascii) : option Sextet.
    refine (match index_of s Base64Alphabet with
    | Some n => decode n
    | None => None
    end).
  Defined.

  Lemma nodup_nth_safe_same_false : forall A `{DecEq A} (l : list A) n `{HL : n < List.length l},
    NoDup ((@nth_safe _ n l HL) :: l) ->
    False.
  Proof.
    induction l; simpl in *; intros; try lia.
    destruct n; simpl in *; eauto; try lia.
    - inversion H0; subst; destruct H3; simpl in *; eauto.
    - pose proof (NoDup_remove_1 [@nth_safe _ n l (PeanoNat.lt_S_n _ _ HL)] l a);
      simpl in *; eauto.
  Qed.

  Lemma index_of_nth_safe_invol : forall A `{DecEq A} l n `{HL : n <  List.length l},
    NoDup l -> 
    index_of (@nth_safe _ n l HL) l = Some n.
  Proof.
    induction l; intros; simpl in *; try lia.
    destruct n; simpl in *.
    - rewrite eqb_refl; eauto.
    - erewrite IHl.
      * break_match; eauto;
        rewrite eqb_eq in *; subst;
        eapply nodup_nth_safe_same_false in H0; intuition.
      * inversion H0; eauto.
  Qed.
  
  Lemma packet_decode_encode_invol : forall p,
    packet_decode (packet_encode p) = Some p.
  Proof.
    dec_encode.
    unfold packet_encode, packet_decode.
    rewrite index_of_nth_safe_invol; try rewrite invol; eauto.
    eapply NoDupBase64Alphabet.
  Qed.

  
  Global Instance Encodable_sextet_ascii : Encodable Sextet Ascii.ascii := {
    encode := packet_encode;
    decode := packet_decode;
    invol := packet_decode_encode_invol
  }.

  Fixpoint QuadSextetList_encode `{Encodable Sextet Ascii.ascii} (l : QuadSextetList) : string :=
    match l with
    | QSnil => ""
    | QScons_one_pad (p1, p2, p3) => 
      String (encode p1) (
        String (encode p2) (
          String (encode p3) (String Base64Padding "")
        )
      )
    | QScons_two_pad (p1, p2) =>
      String (encode p1) (
        String (encode p2) (String Base64Padding (String Base64Padding ""))
      )
    | QScons_all (p1, p2, p3, p4) rest => 
      String (encode p1) (
        String (encode p2) (
          String (encode p3) (
            String (encode p4) (QuadSextetList_encode rest)
          )
        )
      )
    end.
  
  Fixpoint QuadSextetList_decode `{Encodable Sextet Ascii.ascii} (s : string) : option QuadSextetList :=
    match s with
    | EmptyString => Some QSnil
    | String a1 s' =>
      match s' with
      | EmptyString => None
      | String a2 s'' =>
        match s'' with
        | EmptyString => None
        | String a3 s''' =>
          match s''' with
          | EmptyString => None
          | String a4 rest =>
            p1 <- decode a1 ;;
            p2 <- decode a2 ;;
            if (eqb a3 Base64Padding) 
            then if (eqb a4 Base64Padding) 
              then Some (QScons_two_pad (p1,p2))
              else (* if first is padding, but the second isnt, very bad *)
                None
            else 
              p3 <- decode a3 ;;
              if (eqb a4 Base64Padding) 
              then (* if first isnt padding, but second is, this is one pad *)
                Some (QScons_one_pad (p1,p2,p3))
              else 
                p4 <- decode a4 ;;
                l' <- QuadSextetList_decode rest ;;
                Some (QScons_all (p1,p2,p3,p4) l')
          end
        end
      end
    end.

  Global Instance Encodable_quadsextetlist_string : Encodable QuadSextetList string.
    eapply Build_Encodable with 
      (encode := QuadSextetList_encode)
      (decode := QuadSextetList_decode).
    induction a.
    - simpl in *; eauto.
    - simpl in *; repeat break_match; subst.
      unfold QuadSextetList_decode; simpl in *.
      repeat break_match;
      repeat rewrite packet_decode_encode_invol in *;
      repeat match goal with
      | H : Some _ = Some _ |- _ => inv H
      | H : Some _ = None |- _ => inv H
      end; eauto.
      rewrite Ascii.eqb_eq in *.
      pose proof (packet_encode_in_alphabet s).
      pose proof Base64Padding_not_in_alphabet.
      rewrite Heqb0 in *.
      intuition.
    - simpl in *; repeat break_match; subst.
      unfold QuadSextetList_decode; simpl in *.
      repeat break_match;
      repeat rewrite packet_decode_encode_invol in *;
      repeat match goal with
      | H : Some _ = Some _ |- _ => inv H
      | H : Some _ = None |- _ => inv H
      end; eauto.
    - simpl in *; repeat break_match; subst.
      simpl in *.
      repeat break_match;
      repeat rewrite packet_decode_encode_invol in *;
      repeat match goal with
      | H : Some _ = Some _ |- _ => inv H
      | H : Some _ = None |- _ => inv H
      end; eauto;
      repeat rewrite Ascii.eqb_eq in *;
      try match goal with
      | H : packet_encode ?x = Base64Padding |- _ =>
        pose proof (packet_encode_in_alphabet x);
        pose proof Base64Padding_not_in_alphabet;
        congruence
      end; congruence.
  Defined.

  Global Instance StrictEncodable_ascii_two_sextet 
    : StrictEncodable Ascii.ascii (Sextet * Sextet).
    eapply Build_StrictEncodable with 
      (strict_encode := fun a =>
        let '(Ascii.Ascii b0 b1 b2 b3 b4 b5 b6 b7) := a in
        ((sextet b0 b1 b2 b3 b4 b5), (sextet b6 b7 false false false false)))
      (strict_decode := fun '(p1,p2) =>
        let '(sextet b0 b1 b2 b3 b4 b5) := p1 in
        let '(sextet b6 b7 _ _ _ _) := p2 in
        (Ascii.Ascii b0 b1 b2 b3 b4 b5 b6 b7)).
    dec_encode.
  Defined.

  Global Instance StrictEncodable_two_ascii_three_sextet 
    : StrictEncodable (Ascii.ascii * Ascii.ascii) (Sextet * Sextet * Sextet).
  eapply Build_StrictEncodable with
    (strict_encode := (fun '(a1,a2) => 
      let '(Ascii.Ascii b0 b1 b2 b3 b4 b5 b6 b7) := a1 in
      let '(Ascii.Ascii b8 b9 b10 b11 b12 b13 b14 b15) := a2 in
      ((sextet b0 b1 b2 b3 b4 b5), (sextet b6 b7 b8 b9 b10 b11), (sextet b12 b13 b14 b15 false false))))
    (strict_decode := (fun '(p1,p2,p3) => 
      let '(sextet b0 b1 b2 b3 b4 b5) := p1 in
      let '(sextet b6 b7 b8 b9 b10 b11) := p2 in
      let '(sextet b12 b13 b14 b15 _ _) := p3 in
      (Ascii.Ascii b0 b1 b2 b3 b4 b5 b6 b7, 
        Ascii.Ascii b8 b9 b10 b11 b12 b13 b14 b15))).
    dec_encode.
  Defined.

  Global Instance StrictEncodable_three_ascii_four_sextet 
    : StrictEncodable (Ascii.ascii * Ascii.ascii * Ascii.ascii) (Sextet * Sextet * Sextet * Sextet).
  eapply Build_StrictEncodable with
    (strict_encode := (fun '(a1,a2,a3) => 
      let '(Ascii.Ascii b0 b1 b2 b3 b4 b5 b6 b7) := a1 in
      let '(Ascii.Ascii b8 b9 b10 b11 b12 b13 b14 b15) := a2 in
      let '(Ascii.Ascii b16 b17 b18 b19 b20 b21 b22 b23) := a3 in
      ((sextet b0 b1 b2 b3 b4 b5), (sextet b6 b7 b8 b9 b10 b11), (sextet b12 b13 b14 b15 b16 b17), (sextet b18 b19 b20 b21 b22 b23))))
    (strict_decode := (fun '(p1,p2,p3,p4) => 
      let '(sextet b0 b1 b2 b3 b4 b5) := p1 in
      let '(sextet b6 b7 b8 b9 b10 b11) := p2 in
      let '(sextet b12 b13 b14 b15 b16 b17) := p3 in
      let '(sextet b18 b19 b20 b21 b22 b23) := p4 in
      (Ascii.Ascii b0 b1 b2 b3 b4 b5 b6 b7, 
        Ascii.Ascii b8 b9 b10 b11 b12 b13 b14 b15,
        Ascii.Ascii b16 b17 b18 b19 b20 b21 b22 b23))).
    dec_encode.
  Defined.

  Fixpoint string_to_quadsextetlist 
    `{HE1 : StrictEncodable (Ascii.ascii * Ascii.ascii * Ascii.ascii) (Sextet * Sextet * Sextet * Sextet)}
    `{HE2 : StrictEncodable (Ascii.ascii * Ascii.ascii) (Sextet * Sextet * Sextet)}
    `{HE3 : StrictEncodable (Ascii.ascii) (Sextet * Sextet)}
    (s : string) 
    : QuadSextetList :=
    match s with
    | EmptyString => QSnil
    (* we need to pull off 3, or do padding *)
    | String a1 s' =>
      match s' with
      | EmptyString => QScons_two_pad (strict_encode a1)
      | String a2 s'' =>
        match s'' with
        | EmptyString => QScons_one_pad (strict_encode (a1, a2))
        | String a3 rest => 
          QScons_all (strict_encode (a1,a2,a3)) (string_to_quadsextetlist rest)
        end
      end
    end.

  Fixpoint string_from_quadsextetlist 
    `{HE1 : StrictEncodable (Ascii.ascii * Ascii.ascii * Ascii.ascii) (Sextet * Sextet * Sextet * Sextet)}
    `{HE2 : StrictEncodable (Ascii.ascii * Ascii.ascii) (Sextet * Sextet * Sextet)}
    `{HE3 : StrictEncodable (Ascii.ascii) (Sextet * Sextet)}
    (l : QuadSextetList) 
    : string :=
    match l with
    | QSnil => EmptyString
    | QScons_one_pad p => 
      let '(a1,a2) := strict_decode p in
      String a1 (String a2 EmptyString)
    | QScons_two_pad p =>
      let a1 := strict_decode p in
      String a1 EmptyString
    | QScons_all p rest =>
      let '(a1,a2,a3) := strict_decode p in
      String a1 (String a2 (String a3 (string_from_quadsextetlist rest)))
    end.

  Definition string_ind4 := 
    fun (P : string -> Prop) 
      (f0 : P EmptyString)
      (f1 : forall a, P (String a EmptyString))
      (f2 : forall a1 a2, P (String a1 (String a2 EmptyString)))
      (f3 : forall a1 a2 a3 rest, 
        P rest ->
        P (String a1 (String a2 (String a3 rest)))) =>
    fix F (s1 : string) : P s1 :=
    match s1 with
    | EmptyString => f0
    | String a1 s2 => 
      match s2 with
      | EmptyString => f1 a1
      | String a2 s3 =>
        match s3 with
        | EmptyString => f2 a1 a2
        | String a3 rest => f3 a1 a2 a3 rest (F rest)
        end
      end
    end.

  Global Instance StrictEncodable_string_quadsextetlist 
    `{HE1 : StrictEncodable (Ascii.ascii * Ascii.ascii * Ascii.ascii) (Sextet * Sextet * Sextet * Sextet)}
    `{HE2 : StrictEncodable (Ascii.ascii * Ascii.ascii) (Sextet * Sextet * Sextet)}
    `{HE3 : StrictEncodable (Ascii.ascii) (Sextet * Sextet)}
    : StrictEncodable string QuadSextetList.
  eapply Build_StrictEncodable with
    (strict_encode := string_to_quadsextetlist)
    (strict_decode := string_from_quadsextetlist).
  induction a using string_ind4; simpl in *; eauto;
  repeat rewrite strict_invol; eauto; rewrite IHa; eauto.
  Defined.
  
  Definition encode_string (s : string) : string :=
    encode (strict_encode s).

  Definition decode_string (s : string) : option string :=
    s' <- decode s ;;
    Some (strict_decode s').

  Lemma strict_encode_inj : forall A B `{StrictEncodable A B} a b,
    Some (strict_encode a) = Some b ->
    strict_encode a = b.
  Proof.
    intros.
    inversion H0; eauto.
  Qed.

  Global Instance Encodable_string_string : Encodable string string.
  eapply Build_Encodable with
    (encode := encode_string)
    (decode := decode_string).
  unfold encode_string, decode_string; intros.
  break_match; repeat rewrite invol in *; eauto;
  try congruence.
  eapply strict_encode_inj in Heqo; subst.
  rewrite strict_invol; eauto.
  Defined.

End Base64.
