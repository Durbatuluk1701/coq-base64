Require Import ClassesAndLtac.

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