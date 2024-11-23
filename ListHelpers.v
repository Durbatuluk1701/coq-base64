Require Import ClassesAndLtac.

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

Lemma index_of_nth_lt_length : forall A `{EqClass A} (l : list A) v HL,
  index_of_safe v l HL < List.length l.
Proof.
  induction l; simpl in *; intuition; try congruence.
  destruct decEq.
  - eapply PeanoNat.Nat.lt_0_succ.
  - erewrite <- PeanoNat.Nat.succ_lt_mono.
    eapply IHl.
Qed.

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

Ltac breakup :=
  repeat break_match; intuition; eauto;
  repeat (destruct strict_in_dec; simpl in *; try congruence;
      subst; simpl in *; eauto);
  subst; simpl in *;
  repeat (destruct strict_in_dec; simpl in *; try congruence);
  try (exfalso; eauto; fail).

Ltac fix_eq_helper :=
  intros; breakup.

