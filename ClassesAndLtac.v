Require Import String List.

Definition string_ind4 := 
  fun (P : string -> Prop) 
    (f0 : P EmptyString)
    (f1 : forall a, P (String a EmptyString))
    (f2 : forall a1 a2, P (String a1 (String a2 EmptyString)))
    (f3 : forall a1 a2 a3,
      P (String a1 (String a2 (String a3 EmptyString))))
    (f4 : forall a1 a2 a3 a4 rest, 
      P rest ->
      P (String a1 (String a2 (String a3 (String a4 rest))))) =>
  fix F (s1 : string) : P s1 :=
  match s1 with
  | EmptyString => f0
  | String a1 s2 => 
    match s2 with
    | EmptyString => f1 a1
    | String a2 s3 =>
      match s3 with
      | EmptyString => f2 a1 a2
      | String a3 s4 => 
        match s4 with
        | EmptyString => f3 a1 a2 a3
        | String a4 rest => f4 a1 a2 a3 a4 rest (F rest)
        end
      end
    end
  end.

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

Theorem strict_encode_inj {A B} `{StrictEncodable A B} : forall a1 a2,
  strict_encode a1 = strict_encode a2 -> a1 = a2.
Proof.
  intros.
  rewrite <- (strict_invol a1), <- (strict_invol a2).
  congruence.
Qed.

Global Instance StrictEncodable_refl {A : Type} : StrictEncodable A A := {|
  strict_encode := fun x => x;
  strict_decode := fun x => x;
  strict_invol := fun x => eq_refl
|}.

Global Instance StrictEncodable_trans {A B C : Type} 
  `{StrictEncodable A B, StrictEncodable B C} : StrictEncodable A C. 
refine ({|
  strict_encode := fun a => strict_encode (strict_encode a);
  strict_decode := fun c => strict_decode (strict_decode c);
  strict_invol := _
|}).
intros; repeat erewrite strict_invol; eauto.
Defined.

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
