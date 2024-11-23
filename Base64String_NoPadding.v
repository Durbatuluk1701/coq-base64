(* 
  This is an implementation of the Base64 encoding and decoding algorithm in Coq.

  Specifically, this will abide by RFC4648, which is the (current) standard for Base64 encoding and decoding.

  This file is for the case where length is KNOWN, thus we do not need any padding
*)
Require Import ClassesAndLtac ListHelpers Base64Helpers.
Open Scope string_scope.

Inductive Base64Options :=
| Base64Standard
| Base64UrlAndFilenameSafe.

Section Base64.

  Variable b : Base64Options.

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

  Fixpoint Base64Encoded (s1 : string) : SProp :=
    match s1 with
    | EmptyString => STrue
    | String a1 s2 => 
      if strict_in_dec a1 Base64Alphabet 
      then Base64Encoded s2
      else SFalse
    end.

  Definition Base64_Ascii := {a : Ascii.ascii & Box (strict_In a Base64Alphabet)}.

  Definition Base64_String := {s : string & Box (Base64Encoded s)}.
  
  Fixpoint Base64Encoded_bool (s1 : string) : bool :=
    match s1 with
    | EmptyString => true
    | String a1 s2 => 
      if strict_in_dec a1 Base64Alphabet 
      then Base64Encoded_bool s2
      else false
    end.

  Theorem Base64Encoded_bool_iff : forall s,
    Base64Encoded_bool s = true <-> Box (Base64Encoded s).
  Proof.
    induction s; simpl in *; intuition;
    break_match; eauto; try congruence; 
    try exfalso; inv H1; intuition.
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

  Definition packet_decode (s : Base64_Ascii) : Sextet.
    refine (
      Sextet_from_nat_safe (index_of_safe (projT1 s) Base64Alphabet (box_proj (projT2 s))) _).
    erewrite <- Base64AlphabetLengthCorrect.
    eapply index_of_nth_lt_length.
  Defined.

  Lemma packet_decode_encode_invol : forall p,
    packet_decode (packet_encode p) = p.
  Proof.
    unfold packet_encode, packet_decode.
    simpl in *.
    intros p.
    Set Printing All.
    set (x' := (@eq_ind nat (@Datatypes.length Ascii.ascii Base64Alphabet) (fun n : nat => lt (@index_of_safe Ascii.ascii EqClass_Ascii (@nth_safe Ascii.ascii (Sextet_to_nat p) Base64Alphabet (sextet_to_nat_lt_base64alphabet_length p)) Base64Alphabet (@strict_In_nth_safe Ascii.ascii EqClass_Ascii Base64Alphabet (Sextet_to_nat p) (sextet_to_nat_lt_base64alphabet_length p))) n) (@index_of_nth_lt_length Ascii.ascii EqClass_Ascii Base64Alphabet (@nth_safe Ascii.ascii (Sextet_to_nat p) Base64Alphabet (sextet_to_nat_lt_base64alphabet_length p)) (@strict_In_nth_safe Ascii.ascii EqClass_Ascii Base64Alphabet (Sextet_to_nat p) (sextet_to_nat_lt_base64alphabet_length p))) (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) Base64AlphabetLengthCorrect)).
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

  (* Definition QuadSextetList_encode `{StrictEncodable Sextet Base64_Ascii}
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
      set (x := match strict_in_dec a1 Base64Alphabet as s return (Box (if s then if strict_in_dec a2 Base64Alphabet then if strict_in_dec a3 Base64Alphabet then if strict_in_dec a4 Base64Alphabet then Base64Encoded rec else if Ascii.eqb a4 Base64Padding_special then match rec with | "" => STrue | String _ _ => SFalse end else SFalse else if Ascii.eqb a3 Base64Padding_special then if Ascii.eqb a4 Base64Padding_special then match rec with | "" => STrue | String _ _ => SFalse end else SFalse else SFalse else SFalse else SFalse)) with | left _ => match strict_in_dec a2 Base64Alphabet as s return (Box (if s then if strict_in_dec a3 Base64Alphabet then if strict_in_dec a4 Base64Alphabet then Base64Encoded rec else if Ascii.eqb a4 Base64Padding_special then match rec with | "" => STrue | String _ _ => SFalse end else SFalse else if Ascii.eqb a3 Base64Padding_special then if Ascii.eqb a4 Base64Padding_special then match rec with | "" => STrue | String _ _ => SFalse end else SFalse else SFalse else SFalse)) with | left _ => match strict_in_dec a3 Base64Alphabet as s return (Box (if s then if strict_in_dec a4 Base64Alphabet then Base64Encoded rec else if Ascii.eqb a4 Base64Padding_special then match rec with | "" => STrue | String _ _ => SFalse end else SFalse else if Ascii.eqb a3 Base64Padding_special then if Ascii.eqb a4 Base64Padding_special then match rec with | "" => STrue | String _ _ => SFalse end else SFalse else SFalse)) with | left _ => match strict_in_dec a4 Base64Alphabet as s return (Box (if s then Base64Encoded rec else if Ascii.eqb a4 Base64Padding_special then match rec with | "" => STrue | String _ _ => SFalse end else SFalse)) with | left _ => Hrec | right n => False_ind (Box (if Ascii.eqb a4 Base64Padding_special then match rec with | "" => STrue | String _ _ => SFalse end else SFalse)) (n Ha4) end | right n => False_ind (Box (if Ascii.eqb a3 Base64Padding_special then if Ascii.eqb a4 Base64Padding_special then match rec with | "" => STrue | String _ _ => SFalse end else SFalse else SFalse)) (n Ha3) end | right n => False_ind (Box SFalse) (n Ha2) end | right n => False_ind (Box SFalse) (n Ha1) end).
      clearbody x.
      simpl.
      destruct strict_in_dec; intuition; eauto; try congruence.
      destruct strict_in_dec; intuition; eauto; try congruence.
      destruct strict_in_dec; intuition; eauto; try congruence.
      destruct strict_in_dec; intuition; eauto; try congruence.
      repeat collapse_boxes.
      repeat find_rev_rew.
      repeat rewrite strict_invol; eauto.
      Unshelve. all: eapply EqClass_Ascii.
  Qed.  *)

  Global Instance StrictEncodable_quadsextetlist_base64_string  
      `{StrictEncodable Sextet Base64_Ascii} :
      StrictEncodable QuadSextetList Base64_String := {
    strict_encode := QuadSextetList_encode;
    strict_decode := QuadSextetList_decode;
    strict_invol := qsl_strict_invol
  }.

  Definition decode_string_base64 (s : string) : option Base64_String.
    destruct (Base64Encoded_bool s) eqn:E.
    - eapply (Some (existT _ s (proj_iff_1 (Base64Encoded_bool_iff s) E))).
    - eapply None.
  Defined.

  Theorem Base64Encoder_invol : forall s,
    decode_string_base64 (projT1 s) = Some s.
  Proof.
    destruct s; simpl in *;
    unfold decode_string_base64.
    set (x' := (proj_iff_1 (Base64Encoded_bool_iff x))).
    clearbody x'.
    generalize dependent b0.
    destruct Base64Encoded_bool eqn:E; eauto.
    - intros.
      set (x'' := x' eq_refl).
      clearbody x''.
      repeat f_equal; eapply box_irrelevant.
    - intros.
      exfalso.
      rewrite <- Base64Encoded_bool_iff in b0; congruence.
  Qed.
  
  (* NOTE: This is maybe a bit confusing, but this is for converting
  a string that we THINK may be a base64 into the actual Base64_String type.
  
  DO NOT use this to try to convert to and from base64, as that is not the purpose of this. The "conversions" are just Identity function where the type is allowed to change beneath. *)
  Global Instance Encodable_base64_string_string : Encodable Base64_String string := {
    encode := fun s => projT1 s;
    decode := decode_string_base64;
    invol := Base64Encoder_invol
  }.

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
  
  Global Instance StrictEncodable_ascii_two_sextet 
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
  Defined.

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

  Global Instance StrictEncodable_string_quadsextetlist 
    `{HE1 : StrictEncodable (Ascii.ascii * Ascii.ascii * Ascii.ascii) (Sextet * Sextet * Sextet * Sextet)}
    `{HE2 : StrictEncodable (Ascii.ascii * Ascii.ascii) (Sextet * Sextet * Sextet)}
    `{HE3 : StrictEncodable (Ascii.ascii) (Sextet * Sextet)}
    : StrictEncodable string QuadSextetList.
  eapply Build_StrictEncodable with
    (strict_encode := string_to_quadsextetlist)
    (strict_decode := string_from_quadsextetlist).
  induction a using string_ind3; simpl in *; eauto;
  repeat rewrite strict_invol; eauto; rewrite IHa; eauto.
  Defined.

  (* If you are wanting to convert strings to/from Base64 strings, this
  is the typeclass instance you are wanting to use!!! *)
  Global Instance StrictEncodable_string_base64_string 
    `{StrictEncodable string QuadSextetList}
    `{StrictEncodable QuadSextetList Base64_String}
    : StrictEncodable string Base64_String.
    eapply Build_StrictEncodable with
      (strict_encode := fun s => strict_encode (strict_encode s))
      (strict_decode := fun s => strict_decode (strict_decode s)).
    intros.
    repeat rewrite strict_invol; eauto.
  Defined.
  
End Base64.


Section Base64_Testing.
  Local Instance StandardStringEncoder : StrictEncodable string (Base64_String Base64Standard) :=
    @StrictEncodable_string_base64_string Base64Standard _ _.

  Definition test_str := "Hello, World!".
  Definition newline := String (Ascii.Ascii false true false true false false false false) EmptyString.
  Definition test_str_2 := String.concat "" ["a"; newline; "a"].

  Definition base64_test_str := "SGVsbG8sIFdvcmxkIQ==".
  Definition base64_encoded_base64_test_str 
    : Box (Base64Encoded Base64Standard base64_test_str).
    erewrite <- Base64Encoded_bool_iff.
      (* Base64Encoded_bool Base64Standard base64_test_str = true. *)
    unfold base64_test_str.
    unfold Base64Encoded_bool.
    repeat (destruct strict_in_dec; 
      [ match goal with
      | H : Box _ |- _ => clear H
      end | 
        match goal with
        | H : ~ Box _ |- _ => 
          try (exfalso; eapply H; clear H;
            vm_compute; destruct (DecEq_from_EqClass Ascii.ascii);
            repeat (destruct decEq as [ H' | ? ]; [ inv H' | ]); eauto;
            exfalso; eauto; fail)
        end ]; eauto).
  Qed.

  Definition base64_test_str_base64_type : Base64_String Base64Standard :=
    existT _ base64_test_str base64_encoded_base64_test_str.

  (* NOTE: We are using the projection out of this, since that is the real string value.
  
  Technically, since we have all the involutivity proofs completed as part of the StrictEncodable, they should be strictly equivalent. However this takes an IMMENSE amount of time to verify, so it is just simpler to complete it this way instead *)
  Example encode_test_1 : 
    projT1 (strict_encode test_str) = projT1 (base64_test_str_base64_type).
  Proof.
    reflexivity.
  Qed.

End Base64_Testing.


