(* 
  This is an implementation of the Base64 encoding and decoding algorithm in Coq.

  Specifically, this will abide by RFC4648, which is the (current) standard for Base64 encoding and decoding.

  However, there is one main divergence from the standard, which is that we will REQUIRE padding to be used in the encoding/decoding.
*)
Require Import Coq.Strings.String Coq.Lists.List.
Import ListNotations.
Open Scope string_scope.

(* Some Ltac *)
Ltac break_match :=
  match goal with
  | |- context [match ?x with _ => _ end] => destruct x eqn:?
  | H : context [match ?x with _ => _ end] |- _ => destruct x eqn:?
  end.

Ltac inv H := inversion H; subst; clear H.

Class Encodable (A B : Type) := {
  encode : A -> B;
  decode : B -> option A;
  invol : forall a, decode (encode a) = Some a
}.

Class StrictEncodable (A B : Type) := {
  strict_encode : A -> B;
  strict_decode : B -> A;
  strict_invol : forall a, strict_decode (strict_encode a) = a
}.

Global Instance Encodable_from_strict (A B : Type) `{StrictEncodable A B} : Encodable A B.
eapply Build_Encodable with
  (encode := strict_encode)
  (decode := fun b => Some (strict_decode b)).
intros; erewrite strict_invol; eauto.
Defined.

Class EqClass (A : Type) := {
  eqb : A -> A -> bool;
  eqb_eq : forall x y, eqb x y = true <-> x = y
}.

Class DecEq (A : Type) := {
  decEq : forall x y : A, {x = y} + {x <> y}
}.

Lemma eqb_refl : forall A `{EqClass A} (a : A),
  eqb a a = true.
Proof.
  intros; rewrite eqb_eq; reflexivity.
Qed.

Lemma eqb_neq : forall A `{EqClass A} (a b : A),
  eqb a b = false <-> a <> b.
Proof.
  split; intros; destruct (eqb a b) eqn:E; eauto; try congruence;
  try rewrite eqb_eq in *; try congruence.
  intros HC; rewrite <- eqb_eq in HC; congruence.
Qed.

Theorem decEq_impl_id_irrel : forall A `{DecEq A} (x y : A) (H1 H2 : x = y),
  H1 = H2.
Proof.
  intros.
  eapply Eqdep_dec.eq_proofs_unicity.
  intros.
  destruct (decEq x0 y0); eauto.
Qed.

Global Instance DecEq_from_EqClass (A : Type) `{EqClass A} : DecEq A.
econstructor; intros.
destruct (eqb x y) eqn:E.
- rewrite eqb_eq in *; subst; eauto.
- rewrite eqb_neq in *; eauto.
Qed.

Global Instance EqClass_nat : EqClass nat := {
  eqb := Nat.eqb;
  eqb_eq := PeanoNat.Nat.eqb_eq
}.

Global Instance EqClass_Ascii : EqClass Ascii.ascii := {
  eqb := Ascii.eqb;
  eqb_eq := Ascii.eqb_eq
}.

Global Instance EqClass_string : EqClass string := {
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

Definition Sextet_from_nat_safe (n : nat) (Hnlt : n < 64) : Sextet.
  refine (match n as n' return n = n' -> Sextet with
  | 0 => fun HN => (sextet false false false false false false)
  | 1 => fun HN => (sextet false false false false false true)
  | 2 => fun HN => (sextet false false false false true false)
  | 3 => fun HN => (sextet false false false false true true)
  | 4 => fun HN => (sextet false false false true false false)
  | 5 => fun HN => (sextet false false false true false true)
  | 6 => fun HN => (sextet false false false true true false)
  | 7 => fun HN => (sextet false false false true true true)
  | 8 => fun HN => (sextet false false true false false false)
  | 9 => fun HN => (sextet false false true false false true)
  | 10 => fun HN => (sextet false false true false true false)
  | 11 => fun HN => (sextet false false true false true true)
  | 12 => fun HN => (sextet false false true true false false)
  | 13 => fun HN => (sextet false false true true false true)
  | 14 => fun HN => (sextet false false true true true false)
  | 15 => fun HN => (sextet false false true true true true)
  | 16 => fun HN => (sextet false true false false false false)
  | 17 => fun HN => (sextet false true false false false true)
  | 18 => fun HN => (sextet false true false false true false)
  | 19 => fun HN => (sextet false true false false true true)
  | 20 => fun HN => (sextet false true false true false false)
  | 21 => fun HN => (sextet false true false true false true)
  | 22 => fun HN => (sextet false true false true true false)
  | 23 => fun HN => (sextet false true false true true true)
  | 24 => fun HN => (sextet false true true false false false)
  | 25 => fun HN => (sextet false true true false false true)
  | 26 => fun HN => (sextet false true true false true false)
  | 27 => fun HN => (sextet false true true false true true)
  | 28 => fun HN => (sextet false true true true false false)
  | 29 => fun HN => (sextet false true true true false true)
  | 30 => fun HN => (sextet false true true true true false)
  | 31 => fun HN => (sextet false true true true true true)
  | 32 => fun HN => (sextet true false false false false false)
  | 33 => fun HN => (sextet true false false false false true)
  | 34 => fun HN => (sextet true false false false true false)
  | 35 => fun HN => (sextet true false false false true true)
  | 36 => fun HN => (sextet true false false true false false)
  | 37 => fun HN => (sextet true false false true false true)
  | 38 => fun HN => (sextet true false false true true false)
  | 39 => fun HN => (sextet true false false true true true)
  | 40 => fun HN => (sextet true false true false false false)
  | 41 => fun HN => (sextet true false true false false true)
  | 42 => fun HN => (sextet true false true false true false)
  | 43 => fun HN => (sextet true false true false true true)
  | 44 => fun HN => (sextet true false true true false false)
  | 45 => fun HN => (sextet true false true true false true)
  | 46 => fun HN => (sextet true false true true true false)
  | 47 => fun HN => (sextet true false true true true true)
  | 48 => fun HN => (sextet true true false false false false)
  | 49 => fun HN => (sextet true true false false false true)
  | 50 => fun HN => (sextet true true false false true false)
  | 51 => fun HN => (sextet true true false false true true)
  | 52 => fun HN => (sextet true true false true false false)
  | 53 => fun HN => (sextet true true false true false true)
  | 54 => fun HN => (sextet true true false true true false)
  | 55 => fun HN => (sextet true true false true true true)
  | 56 => fun HN => (sextet true true true false false false)
  | 57 => fun HN => (sextet true true true false false true)
  | 58 => fun HN => (sextet true true true false true false)
  | 59 => fun HN => (sextet true true true false true true)
  | 60 => fun HN => (sextet true true true true false false)
  | 61 => fun HN => (sextet true true true true false true)
  | 62 => fun HN => (sextet true true true true true false)
  | 63 => fun HN => (sextet true true true true true true)
  | _ => fun HN => _
  end eq_refl).
  subst.
  destruct n63;
  repeat eapply PeanoNat.lt_S_n in Hnlt;
  edestruct PeanoNat.Nat.nlt_0_r; eauto.
Defined.

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
  repeat (break_match; simpl in *; try simple congruence 3; eauto); eauto.

Lemma Sextet_from_nat_safe_to_nat_invol : forall p HNlt,
  Sextet_from_nat_safe (Sextet_to_nat p) HNlt = p.
Proof.
  intros p H.
  destruct p.
  repeat match goal with
  | b : bool |- _ => destruct b; simpl in *; eauto
  end.
Qed.

Lemma Sextet_to_nat_from_safe_invol : forall n Hnlt,
  Sextet_to_nat (Sextet_from_nat_safe n Hnlt) = n.
Proof.
  intros n H.
  do 64 (destruct n; [ reflexivity | ]).

  Require Import Lia.
  lia.
Qed.

Lemma Sextet_from_to_nat_invol : forall p,
  Sextet_from_nat (Sextet_to_nat p) = Some p.
Proof.
  dec_encode.
Qed.

Global Instance encodable_sextet_nat : Encodable Sextet nat := {
  encode := Sextet_to_nat;
  decode := Sextet_from_nat;
  invol := Sextet_from_to_nat_invol
}.

Lemma Sextet_to_nat_lt_64 : forall p,
  Sextet_to_nat p < 64.
Proof.
  induction p; simpl in *;
  repeat match goal with
  | b : bool |- _ => destruct b; try (repeat econstructor; fail)
  end.
Qed.

Lemma Sextet_from_nat_lt_64_some : forall n,
  n < 64 ->
  exists p, Sextet_from_nat n = Some p.
Proof.
  intros.
  repeat (destruct n; simpl in *; eauto;
  try eapply PeanoNat.Nat.succ_lt_mono in H;
  try (edestruct PeanoNat.Nat.nlt_0_r; eauto; fail)).
Defined.

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
Require Import StrictProp.

(* inspired by Bonak: https://github.com/artagnon/bonak/blob/master/theories/%CE%BDType/LeYoneda.v *)
Inductive SFalse : SProp :=.
Inductive STrue : SProp := sI.
(* Equality in SProp is =S *)
Global Hint Constructors STrue SFalse Box Squash : core.
Inductive eqsprop {A: SProp} (x: A): A -> Prop := eqsprop_refl: eqsprop x x.
Infix "=S" := eqsprop (at level 70): type_scope.

Fixpoint strict_In {A : Type} `{EqClass A} (x : A) (l : list A) : SProp :=
  match l with
  | [] => SFalse
  | h :: t => 
    match decEq x h with
    | left _ => STrue
    | right _ => strict_In x t
    end
  end.

Theorem strict_in_dec {A : Type} `{EqClass A} (x : A) (l : list A) : 
  {Box (strict_In x l)} + {~ Box (strict_In x l)}.
Proof.
  induction l; simpl in *.
  - right; intros HC; inv HC; intuition.
  - destruct IHl.
    * (* strict_In x l *)
      destruct decEq; intuition; eauto.
    * (* ~ strict_In x l *)
      destruct decEq; intuition; eauto.
Qed.

Theorem strict_In_iff_In : forall A `{EqClass A} l x,
  Box (strict_In x l) <-> In x l.
Proof.
  induction l; simpl in *; intuition.
  - inv H0; intuition.
  - inv H0.
    repeat break_match; subst; intuition.
    right; eapply IHl; eauto.
  - subst; destruct decEq; eauto; intuition.
  - destruct decEq; eauto; erewrite IHl; eauto.
Qed.
Global Hint Rewrite strict_In_iff_In : core.

Theorem strict_In_irrel : forall A `{EqClass A} x l (H1 H2 : strict_In x l),
  H1 =S H2.
Proof.
  now reflexivity.
Qed.

Fixpoint strict_NoDup {A : Type} `{EqClass A} (l : list A) : SProp :=
  match l with
  | [] => STrue
  | h :: t => 
    match strict_in_dec h t with
    | left _ => SFalse
    | right _ => strict_NoDup t
    end
  end.

Theorem strict_NoDup_iff_NoDup : forall A `{EqClass A} l,
  Box (strict_NoDup l) <-> NoDup l.
Proof.
  induction l; simpl in *; intuition.
  - econstructor.
  - destruct strict_in_dec; subst; intuition.
    * inv H2; intuition.
    * econstructor; eauto.
      intros HC; eapply n.
      erewrite strict_In_iff_In; eauto.
  - destruct strict_in_dec; subst; intuition.
    * inv H2; intuition. 
      exfalso; eapply H5.
      rewrite <- strict_In_iff_In; eauto.
    * inv H2; intuition.
Qed.

Lemma strict_NoDup_irrel : forall A `{EqClass A} l (H1 H2 : strict_NoDup l),
  H1 =S H2.
Proof.
  now reflexivity.
Qed.

Section Base64.

  Variable b : Base64Options.

  Fixpoint string_get_ascii_safe (n : nat) 
    (s : { s & n < String.length s }) : Ascii.ascii.
    (* `{HL : n < String.length s} : Ascii.ascii. *)
    destruct s eqn:E; simpl in *.
    destruct x eqn:E1; simpl in *.
    - edestruct PeanoNat.Nat.nlt_0_r; eauto.
    - destruct n.
      * (* n = 0 *) exact a.
      * (* n = S n' *)
        eapply (string_get_ascii_safe n).
        econstructor.
        eapply (PeanoNat.lt_S_n _ _ l).
  Defined.

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
    econstructor.
  Defined.
  
  Fixpoint Base64Encoded (s1 : string) : SProp :=
    match s1 with
    | EmptyString => STrue
    | String a1 s2 => 
      match s2 with
      | EmptyString => 
        (* no strings of length n where n % 4 <> 0 are base 64 encoded *)
        SFalse
      | String a2 s3 =>
        match s3 with
        | EmptyString => SFalse
        | String a3 s4 =>
          match s4 with
          | EmptyString => SFalse
          | String a4 s5 =>
            (* first two must always be in alphabet *)
            if (strict_in_dec a1 Base64Alphabet)
            then if (strict_in_dec a2 Base64Alphabet)
            then 
              (* third is either in alphabet, 
                OR both 3 and 4 are pads and s5 == empty *)
              if (strict_in_dec a3 Base64Alphabet)
              then 
                (* fourth is either in alphabet,
                  OR it is a pad and s5 == empty *)
                if (strict_in_dec a4 Base64Alphabet)
                then Base64Encoded s5
                else 
                  if (Ascii.eqb a4 Base64Padding_special)
                  then
                    match s5 with
                    | EmptyString => STrue
                    | _ => SFalse
                    end
                  else SFalse
              else 
                (* if 3 is a pad, so must 4 be *)
                if (Ascii.eqb a3 Base64Padding_special)
                then 
                  if (Ascii.eqb a4 Base64Padding_special)
                  then 
                    match s5 with
                    | EmptyString => STrue
                    | _ => SFalse
                    end
                  else SFalse
                else SFalse
            else SFalse
            else SFalse
          end
        end
      end
    end.

  Definition Base64_Ascii := {a : Ascii.ascii & Box (strict_In a Base64Alphabet)}.

  Definition Base64_String := {s : string & Box (Base64Encoded s)}.

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
    - edestruct PeanoNat.Nat.nlt_0_r; eauto.
    - destruct n.
      * (* n = 0 *) exact a.
      * (* n = S n' *)
        eapply (nth_safe _ n l0);
        eapply (PeanoNat.lt_S_n _ _ HL).
  Defined.
  
  Lemma in_nth_safe : forall A (l : list A) n `{HL : n < List.length l},
    In (@nth_safe _ n l HL) l.
  Proof.
    induction l; simpl in *; intuition; try (inversion HL; fail).
    destruct n; eauto.
  Qed.

  Lemma strict_In_nth_safe : forall A `{EqClass A} (l : list A) n `{HL : n < List.length l},
    strict_In (@nth_safe _ n l HL) l.
  Proof.
    induction l; simpl in *; intuition; try (inversion HL; fail).
    destruct decEq; eauto.
    destruct n; simpl in *; eauto.
    congruence.
  Qed.

  Lemma sextet_to_nat_lt_base64alphabet_length : forall s,
    Sextet_to_nat s < List.length Base64Alphabet.
  Proof.
    rewrite Base64AlphabetLengthCorrect.
    eapply Sextet_to_nat_lt_64.
  Qed.

  Definition packet_encode (p : Sextet) : Base64_Ascii.
    eapply existT with (x := @nth_safe _ (Sextet_to_nat p) Base64Alphabet (sextet_to_nat_lt_base64alphabet_length p)).
    econstructor.
    eapply strict_In_nth_safe.
  Defined.

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

  Fixpoint index_of {A : Type} `{EqClass A} (s : A) (l : list A) : option nat :=
    match l with
    | [] => None
    | h :: t => if eqb s h then Some 0 else
      match index_of s t with
      | Some n => Some (S n)
      | None => None
      end
    end.
  
  Fixpoint index_of_safe {A : Type} `{EqClass A} (s : A) (l : list A) 
      (HIn : strict_In s l) {struct l} : nat.
    destruct l; simpl in *.
    - inversion HIn.
    - destruct decEq.
      * exact 0.
      * eapply (S (index_of_safe _ _ s l HIn)).
  Defined.

  (* Lemma index_of_safe : forall A `{EqClass A} (l : list A) v,
    In v l ->
    index_of v l <> None.
  Proof.
    induction l; simpl in *; intuition; subst; eauto.
    - rewrite eqb_refl in *; congruence.
    - destruct (eqb v a) eqn:E; eauto; try congruence;
      break_match; eauto; try congruence.
  Qed. *)

  Lemma index_of_nth_lt_length : forall A `{EqClass A} (l : list A) v HL,
    index_of_safe v l HL < List.length l.
  Proof.
    induction l; simpl in *; intuition; try congruence.
    destruct decEq.
    - eapply PeanoNat.Nat.lt_0_succ.
    - erewrite <- PeanoNat.Nat.succ_lt_mono.
      eapply IHl.
  Qed.

  Definition box_proj {A} :=
    fun (x : Box A) => match x with
    | box x' => x'
    end.

  Definition packet_decode (s : Base64_Ascii) : Sextet.
    refine (
      Sextet_from_nat_safe (index_of_safe (projT1 s) Base64Alphabet (box_proj (projT2 s))) _).
    erewrite <- Base64AlphabetLengthCorrect.
    eapply index_of_nth_lt_length.
  Defined.
    (* - eapply index_of_nth_lt_length in e. 
      rewrite Base64AlphabetLengthCorrect in *; eauto.
    - eapply index_of_safe in HN; intuition.
      eapply (projT2 x).
    - eauto.
  Defined. *)

  Lemma nodup_nth_safe_same_false : forall A `{EqClass A} (l : list A) n `{HL : n < List.length l},
    NoDup ((@nth_safe _ n l HL) :: l) ->
    False.
  Proof.
    induction l; simpl in *; intros; try (inversion HL; fail).
    destruct n; simpl in *; eauto.
    - inversion H0; subst; destruct H3; simpl in *; eauto.
    - pose proof (NoDup_remove_1 [@nth_safe _ n l (PeanoNat.lt_S_n _ _ HL)] l a);
      simpl in *; eauto.
  Qed.

  Lemma index_of_nth_safe_invol : forall A `{EqClass A} l n `{HL : n <  List.length l} HL',
    NoDup l -> 
    index_of_safe (@nth_safe _ n l HL) l HL' = n.
  Proof.
    induction l; intros; simpl in *; try (inversion HL; fail).
    destruct n; simpl in *.
    - set (x := eqb a a).
      simpl in *.
      (* Set Printing All. *)
      set (x' := 
      @eq_ind_r A a (fun a0 : A => forall _ : @eq bool (@eqb A H a a0) false,
      @In A a l)
      (fun E0 : @eq bool x false =>
      False_ind (@In A a l)
      (@eq_ind bool true
      (fun e : bool =>
      match e return Prop with
      | true => True
      | false => False
      end) I false
      (@eq_ind bool x (fun b0 : bool => @eq bool b0 false) E0 true
      (@eqb_refl A H a)))) a).
      simpl in *.
      clearbody x'.
      destruct decEq; simpl in *; eauto; try congruence.
    - break_match; subst; eauto.
      * edestruct nodup_nth_safe_same_false; eauto.
      * f_equal.
        eapply IHl; inversion H0; eauto.
  Qed.
  
  Lemma packet_decode_encode_invol : forall p,
    packet_decode (packet_encode p) = p.
  Proof.
    unfold packet_encode, packet_decode.
    simpl in *.
    intros p.
    Set Printing All.
    set (x' := 
    (@eq_ind nat (@Datatypes.length Ascii.ascii Base64Alphabet)
(fun n : nat =>
lt
(@index_of_safe Ascii.ascii EqClass_Ascii
(@nth_safe Ascii.ascii (Sextet_to_nat p) Base64Alphabet
(sextet_to_nat_lt_base64alphabet_length p)) Base64Alphabet
(@strict_In_nth_safe Ascii.ascii EqClass_Ascii Base64Alphabet
(Sextet_to_nat p) (sextet_to_nat_lt_base64alphabet_length p))) n)
(@index_of_nth_lt_length Ascii.ascii EqClass_Ascii Base64Alphabet
(@nth_safe Ascii.ascii (Sextet_to_nat p) Base64Alphabet
(sextet_to_nat_lt_base64alphabet_length p))
(@strict_In_nth_safe Ascii.ascii EqClass_Ascii Base64Alphabet
(Sextet_to_nat p) (sextet_to_nat_lt_base64alphabet_length p)))
(S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) Base64AlphabetLengthCorrect)).
  clearbody x'.
  simpl in *.
    Unset Printing All.
    generalize dependent x'.
    erewrite index_of_nth_safe_invol.
    - intros.
      erewrite (Sextet_from_nat_safe_to_nat_invol p); eauto.
    - eapply NoDupBase64Alphabet.
  Qed.
  
  Global Instance Encodable_sextet_base64_ascii : StrictEncodable Sextet Base64_Ascii := {
    strict_encode := packet_encode;
    strict_decode := packet_decode;
    strict_invol := packet_decode_encode_invol
  }.

  (* Lemma base64_ascii_in_alphabet : forall a : Base64_Ascii,
    In (projT1 a) Base64Alphabet. *)

  Definition QuadSextetList_encode `{StrictEncodable Sextet Base64_Ascii}
      : QuadSextetList -> Base64_String.
    refine (
      fix F l : Base64_String :=
      match l with
      | QSnil => existT _ "" _
      | QScons_one_pad (p1, p2, p3) => 
        let '(existT _ r1 Hr1) := strict_encode p1 in
        let '(existT _ r2 Hr2) := strict_encode p2 in
        let '(existT _ r3 Hr3) := strict_encode p3 in
        existT _ (String r1 (String r2 (String r3 (String Base64Padding "")))) _
      | QScons_two_pad (p1, p2) =>
        let '(existT _ r1 Hr1) := strict_encode p1 in
        let '(existT _ r2 Hr2) := strict_encode p2 in
        existT _ (String r1 (String r2 (String Base64Padding (String Base64Padding "")))) _
      | QScons_all (p1, p2, p3, p4) rest =>
        let '(existT _ r1 Hr1) := strict_encode p1 in
        let '(existT _ r2 Hr2) := strict_encode p2 in
        let '(existT _ r3 Hr3) := strict_encode p3 in
        let '(existT _ r4 Hr4) := strict_encode p4 in
        let '(existT _ rec Hrec) := F rest in
        existT _ (String r1 (String r2 (String r3 (String r4 rec)))) _
      end).
    - simpl in *; repeat destruct strict_in_dec; eauto; try congruence.
    - simpl in *; repeat destruct strict_in_dec; eauto; try congruence.
    - simpl in *; repeat destruct strict_in_dec; eauto; try congruence.
    - simpl in *; repeat destruct strict_in_dec; eauto; try congruence.
  Defined.

  Lemma wf_proj_len : 
    well_founded (fun x y : Base64_String => String.length (projT1 x) < String.length (projT1 y)).
  Proof.
    eapply Wf_nat.well_founded_ltof.
  Defined.

  Definition QuadSextetList_decode' `{StrictEncodable Sextet Base64_Ascii} : 
    forall s : string, Box (Base64Encoded s) -> QuadSextetList.
    refine (
      fix F s HS : QuadSextetList :=
      _
    ).
    destruct s as [| a1 [ | a2 [ | a3 [ | a4 s5 ]]]];
    try (simpl in *; try inv HS; intuition; fail).
    + eapply QSnil.
    + simpl in *.
      repeat destruct strict_in_dec; simpl in *; try congruence.
      * set (a1' := strict_decode (existT _ a1 b0)).
        set (a2' := strict_decode (existT _ a2 b1)).
        set (a3' := strict_decode (existT _ a3 b2)).
        set (a4' := strict_decode (existT _ a4 b3)).
        set (rec := F s5 HS).
        eapply (QScons_all (a1', a2', a3',a4') rec).
      * set (a1' := strict_decode (existT _ a1 b0)).
        set (a2' := strict_decode (existT _ a2 b1)).
        set (a3' := strict_decode (existT _ a3 b2)).
        repeat (break_match; try inv HS; intuition).
        eapply (QScons_one_pad (a1', a2', a3')).
      * set (a1' := strict_decode (existT _ a1 b0)).
        set (a2' := strict_decode (existT _ a2 b1)).
        repeat (break_match; try inv HS; intuition).
        eapply (QScons_two_pad (a1', a2')).
      * inv HS; intuition.
      * inv HS; intuition.
  Defined.

  Definition QuadSextetList_decode `{StrictEncodable Sextet Base64_Ascii} 
      : Base64_String -> QuadSextetList.
    intros.
    destruct H0 as [s HS].
    generalize dependent s.
    eapply QuadSextetList_decode'.
  Defined.
  
  Ltac breakup :=
    repeat break_match; intuition; eauto;
    repeat (destruct strict_in_dec; simpl in *; try congruence;
        subst; simpl in *; eauto);
    subst; simpl in *;
    repeat (destruct strict_in_dec; simpl in *; try congruence);
    try (exfalso; eauto; fail).

  Ltac fix_eq_helper :=
    intros; breakup.

  Definition box_irrelevant (A:SProp) (x y : Box A) : x = y
  := match x, y with box x, box y => eq_refl end.

  Ltac collapse_boxes := 
    repeat match goal with
    | B1 : Box (strict_In ?x _),
      B2 : Box (strict_In ?x _) |- _ =>
      pose proof (box_irrelevant _ B1 B2); subst
    end.

  Ltac clean :=
    match goal with
      | [ H : ?X = ?X |- _ ] => clear H
    end.

  Ltac subst_max :=
    repeat clean;
    repeat match goal with
            | [ H : ?X = _ |- _ ]  => subst X
            | [H : _ = ?X |- _] => subst X
          end.

  Ltac find_rew :=
    subst_max;
    match goal with
    | [ H : ?X _ _ _ _ = _, H' : ?X _ _ _ _ = _ |- _ ] => rewrite H in H'
    | [ H : ?X = _, H' : ?X = _ |- _ ] => rewrite H in H'
    | [ H : ?X = _, H' : context [ ?X ] |- _ ] => rewrite H in H'
    | [ H : ?X = _ |- context [ ?X ] ] => rewrite H
    end. 

  Ltac find_rev_rew :=
    subst_max;
    match goal with
      | [ H : _ = ?X _ _ _ _, H' : ?X _ _ _ _ = _ |- _ ] => rewrite <- H in H'
      | [ H : _ = ?X, H' : context [ ?X ] |- _ ] => rewrite <- H in H'
      | [ H : _ = ?X |- context [ ?X ] ] => rewrite <- H
    end.

  Theorem qsl_strict_invol : forall `{StrictEncodable Sextet Base64_Ascii} a,
    QuadSextetList_decode (QuadSextetList_encode a) = a.
  Proof.
    induction a; try (simpl in *; eauto; fail).
    - simpl in *; repeat break_match; subst.
      unfold QuadSextetList_decode; simpl in *;
      pose proof Base64Padding_not_in_alphabet;
      repeat destruct strict_in_dec;
      try (rewrite <- strict_In_iff_In in *; 
        exfalso; eauto; intuition; congruence);
      repeat collapse_boxes;
      repeat find_rev_rew;
      repeat rewrite strict_invol; eauto.
    - simpl in *; repeat break_match; subst;
      unfold QuadSextetList_decode; simpl in *;
      pose proof Base64Padding_not_in_alphabet;
      repeat destruct strict_in_dec;
      try (rewrite <- strict_In_iff_In in *; 
        exfalso; eauto; intuition; congruence);
      repeat collapse_boxes;
      repeat find_rev_rew;
      repeat rewrite strict_invol; eauto.
    - simpl in *.
      destruct p as [[[p1 p2] p3] p4].
      destruct (strict_encode p1) as [a1 Ha1] eqn:E1.
      destruct (strict_encode p2) as [a2 Ha2] eqn:E2.
      destruct (strict_encode p3) as [a3 Ha3] eqn:E3.
      destruct (strict_encode p4) as [a4 Ha4] eqn:E4.
      destruct (QuadSextetList_encode a) as [rec Hrec].
      unfold QuadSextetList_decode in IHa.
      set (x := match
strict_in_dec a1 Base64Alphabet as s
return
(Box
(if s
then
if strict_in_dec a2 Base64Alphabet
then
if strict_in_dec a3 Base64Alphabet
then
if strict_in_dec a4 Base64Alphabet
then Base64Encoded rec
else
if Ascii.eqb a4 Base64Padding_special
then match rec with
| "" => STrue
| String _ _ => SFalse
end
else SFalse
else
if Ascii.eqb a3 Base64Padding_special
then
if Ascii.eqb a4 Base64Padding_special
then match rec with
| "" => STrue
| String _ _ => SFalse
end
else SFalse
else SFalse
else SFalse
else SFalse))
with
| left _ =>
match
strict_in_dec a2 Base64Alphabet as s
return
(Box
(if s
then
if strict_in_dec a3 Base64Alphabet
then
if strict_in_dec a4 Base64Alphabet
then Base64Encoded rec
else
if Ascii.eqb a4 Base64Padding_special
then match rec with
| "" => STrue
| String _ _ => SFalse
end
else SFalse
else
if Ascii.eqb a3 Base64Padding_special
then
if Ascii.eqb a4 Base64Padding_special
then match rec with
| "" => STrue
| String _ _ => SFalse
end
else SFalse
else SFalse
else SFalse))
with
| left _ =>
match
strict_in_dec a3 Base64Alphabet as s
return
(Box
(if s
then
if strict_in_dec a4 Base64Alphabet
then Base64Encoded rec
else
if Ascii.eqb a4 Base64Padding_special
then match rec with
| "" => STrue
| String _ _ => SFalse
end
else SFalse
else
if Ascii.eqb a3 Base64Padding_special
then
if Ascii.eqb a4 Base64Padding_special
then match rec with
| "" => STrue
| String _ _ => SFalse
end
else SFalse
else SFalse))
with
| left _ =>
match
strict_in_dec a4 Base64Alphabet as s
return
(Box
(if s
then Base64Encoded rec
else
if Ascii.eqb a4 Base64Padding_special
then match rec with
| "" => STrue
| String _ _ => SFalse
end
else SFalse))
with
| left _ => Hrec
| right n =>
False_ind
(Box
(if Ascii.eqb a4 Base64Padding_special
then match rec with
| "" => STrue
| String _ _ => SFalse
end
else SFalse)) (n Ha4)
end
| right n =>
False_ind
(Box
(if Ascii.eqb a3 Base64Padding_special
then
if Ascii.eqb a4 Base64Padding_special
then match rec with
| "" => STrue
| String _ _ => SFalse
end
else SFalse
else SFalse)) (n Ha3)
end
| right n => False_ind (Box SFalse) (n Ha2)
end
| right n => False_ind (Box SFalse) (n Ha1)
end).
clearbody x.
  simpl.
  destruct strict_in_dec; intuition; eauto; try congruence.
  destruct strict_in_dec; intuition; eauto; try congruence.
  destruct strict_in_dec; intuition; eauto; try congruence.
  destruct strict_in_dec; intuition; eauto; try congruence.
  collapse_boxes.
  pose proof (box_irrelevant _ Hrec x); subst.
  repeat find_rev_rew.
  repeat rewrite strict_invol; eauto.
  Unshelve. all: eapply EqClass_Ascii.
Qed. 

  Global Instance StrictEncodable_quadsextetlist_base64_string  
      `{StrictEncodable Sextet Base64_Ascii} :
      StrictEncodable QuadSextetList Base64_String := {
    strict_encode := QuadSextetList_encode;
    strict_decode := QuadSextetList_decode;
    strict_invol := qsl_strict_invol
  }.

  (* Global Instance StrictEncodable_ascii_two_sextet 
    : StrictEncodable Ascii.ascii (Sextet * Sextet).
    eapply Build_StrictEncodable with 
      (strict_encode := fun a =>
        let '(Ascii.Ascii b7 b6 b5 b4 b3 b2 b1 b0) := a in
        ((sextet b0 b1 b2 b3 b4 b5), (sextet b6 b7 false false false false)))
      (strict_decode := fun '(p1,p2) =>
        let '(sextet b0 b1 b2 b3 b4 b5) := p1 in
        let '(sextet b6 b7 _ _ _ _) := p2 in
        (Ascii.Ascii b7 b6 b5 b4 b3 b2 b1 b0)).
    dec_encode.
  Defined.

  Global Instance StrictEncodable_two_ascii_three_sextet 
    : StrictEncodable (Ascii.ascii * Ascii.ascii) (Sextet * Sextet * Sextet).
  eapply Build_StrictEncodable with
    (strict_encode := (fun '(a1,a2) => 
      let '(Ascii.Ascii b7 b6 b5 b4 b3 b2 b1 b0) := a1 in
      let '(Ascii.Ascii b15 b14 b13 b12 b11 b10 b9 b8) := a2 in
      ((sextet b0 b1 b2 b3 b4 b5), (sextet b6 b7 b8 b9 b10 b11), (sextet b12 b13 b14 b15 false false))))
    (strict_decode := (fun '(p1,p2,p3) => 
      let '(sextet b0 b1 b2 b3 b4 b5) := p1 in
      let '(sextet b6 b7 b8 b9 b10 b11) := p2 in
      let '(sextet b12 b13 b14 b15 _ _) := p3 in
      (Ascii.Ascii b7 b6 b5 b4 b3 b2 b1 b0, 
        Ascii.Ascii b15 b14 b13 b12 b11 b10 b9 b8))).
    dec_encode.
  Defined.

  Global Instance StrictEncodable_three_ascii_four_sextet 
    : StrictEncodable (Ascii.ascii * Ascii.ascii * Ascii.ascii) (Sextet * Sextet * Sextet * Sextet).
  eapply Build_StrictEncodable with
    (strict_encode := (fun '(a1,a2,a3) => 
      let '(Ascii.Ascii b7 b6 b5 b4 b3 b2 b1 b0) := a1 in
      let '(Ascii.Ascii b15 b14 b13 b12 b11 b10 b9 b8) := a2 in
      let '(Ascii.Ascii b23 b22 b21 b20 b19 b18 b17 b16) := a3 in
      ((sextet b0 b1 b2 b3 b4 b5), (sextet b6 b7 b8 b9 b10 b11), (sextet b12 b13 b14 b15 b16 b17), (sextet b18 b19 b20 b21 b22 b23))))
    (strict_decode := (fun '(p1,p2,p3,p4) => 
      let '(sextet b0 b1 b2 b3 b4 b5) := p1 in
      let '(sextet b6 b7 b8 b9 b10 b11) := p2 in
      let '(sextet b12 b13 b14 b15 b16 b17) := p3 in
      let '(sextet b18 b19 b20 b21 b22 b23) := p4 in
      (Ascii.Ascii b7 b6 b5 b4 b3 b2 b1 b0, 
        Ascii.Ascii b15 b14 b13 b12 b11 b10 b9 b8,
        Ascii.Ascii b23 b22 b21 b20 b19 b18 b17 b16))).
    dec_encode.
  Defined. *)

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
    : Base64. 
    destruct l.
    - econstructor; eapply existT with (x := ""); simpl in *; eauto.
    - 
      econstructor; eapply existT with (x := String a1 (String a2 "")); simpl in *; eauto.
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


Section Base64_Testing.
  Local Instance StandardStringEncoder : Encodable string string :=
    @Encodable_string_string Base64Standard.

  Example encode_test_1 : 
    encode "Hello, World!" = "SGVsbG8sIFdvcmxkIQ==" := eq_refl.
  Example decode_test_1 : 
    decode "SGVsbG8sIFdvcmxkIQ==" = Some "Hello, World!" := eq_refl.
End Base64_Testing.


