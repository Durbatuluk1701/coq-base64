(* 
  This is an implementation of the Base64 encoding and decoding algorithm in Coq.

  Specifically, this will abide by RFC4648, which is the (current) standard for Base64 encoding and decoding.
*)
From base64 Require Import ClassesAndLtac ListHelpers Base64Helpers.
Open Scope string_scope.

Inductive Base64Options :=
| Base64Standard 
| Base64UrlAndFilenameSafe.

Section Base64.

  Variable b : Base64Options.

  Variable padding : bool.

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

  Definition Base64Padding_special : padding = true -> Ascii.ascii. 
    intros; destruct padding; try congruence.
    refine (string_get_ascii_safe 0 (existT _ "=" (le_n _))).
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
        | EmptyString => 
          (* first two must always be in alphabet *)
          if (strict_in_dec a1 Base64Alphabet)
          then if (strict_in_dec a2 Base64Alphabet)
          then 
            match padding with
            | true => SFalse
            | false => STrue
            end
          else SFalse
          else SFalse
        | String a3 s4 =>
          match s4 with
          | EmptyString => 
            (* first two must always be in alphabet *)
            if (strict_in_dec a1 Base64Alphabet)
            then if (strict_in_dec a2 Base64Alphabet)
            then 
              (* third is either in alphabet, 
                OR both 3 and 4 are pads and s5 == empty *)
              if (strict_in_dec a3 Base64Alphabet)
              then 
                match padding with
                | true => SFalse
                | false => STrue
                end
              else SFalse
            else SFalse
            else SFalse
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
                  match padding as p return padding = p -> _ with
                  | true => fun Hpad =>
                    if (Ascii.eqb a4 (Base64Padding_special Hpad))
                    then
                      match s5 with
                      | EmptyString => STrue
                      | _ => SFalse
                      end
                    else SFalse
                  | false => fun Hpad => SFalse
                  end eq_refl
              else 
                (* if 3 is a pad, so must 4 be *)
                match padding as p return padding = p -> _ with
                | true => fun Hpad =>
                  if (Ascii.eqb a3 (Base64Padding_special Hpad))
                  then 
                    if (Ascii.eqb a4 (Base64Padding_special Hpad))
                    then 
                      match s5 with
                      | EmptyString => STrue
                      | _ => SFalse
                      end
                    else SFalse
                  else SFalse
                | false => fun Hpad => SFalse
                end eq_refl
            else SFalse
            else SFalse
          end
        end
      end
    end.

  Definition Base64_Ascii := {a : Ascii.ascii & Box (strict_In a Base64Alphabet)}.
  
  Definition Base64_String := {s : string & Box (Base64Encoded s)}.
  
  Fixpoint Base64Encoded_bool (s1 : string) : bool.
    destruct s1 as [| a1 [| a2 [| a3 [| a4 s5]]]].
    - eapply true.
    - eapply false.
    - destruct (strict_in_dec a1 Base64Alphabet).
      * destruct (strict_in_dec a2 Base64Alphabet).
        ** eapply (negb padding).
        ** eapply false.
      * eapply false.
    - destruct (strict_in_dec a1 Base64Alphabet).
      * destruct (strict_in_dec a2 Base64Alphabet).
        ** destruct (strict_in_dec a3 Base64Alphabet).
          *** eapply (negb padding).
          *** eapply false.
        ** eapply false.
      * eapply false.
    - 
      destruct (strict_in_dec a1 Base64Alphabet).
      * destruct (strict_in_dec a2 Base64Alphabet).
        ** destruct (strict_in_dec a3 Base64Alphabet).
          *** destruct (strict_in_dec a4 Base64Alphabet).
            **** eapply (Base64Encoded_bool s5).
            **** 
              destruct padding eqn:Hpad.
              + 
              destruct (Ascii.eqb a4 (Base64Padding_special Hpad)).
              ***** destruct s5.
                ****** eapply true.
                ****** eapply false.
              ***** eapply false.
              + eapply false.
          *** 
            destruct padding eqn:Hpad.
            + 
            destruct (Ascii.eqb a3 (Base64Padding_special Hpad)).
            **** destruct (Ascii.eqb a4 (Base64Padding_special Hpad)).
              ***** destruct s5.
                ****** eapply true.
                ****** eapply false.
              ***** eapply false.
            **** eapply false.
            + eapply false.
        ** eapply false.
      * eapply false.
  Defined.

  Theorem Base64Encoded_bool_iff : forall s,
    Base64Encoded_bool s = true <-> Box (Base64Encoded s).
  Proof.
    induction s using string_ind4; [
      vm_compute; split; intros ?; [ exact (box sI) | reflexivity ]
      | vm_compute; split; intros HC; [ discriminate HC | box_simpl ]
      | vm_compute; split; intros H; repeat (destruct strict_in_dec as [bv | bv]; [ clear bv | ]); destruct padding; try (simple congruence 1); box_simpl
      | vm_compute; split; intros H; repeat (destruct strict_in_dec as [bv | bv]; [ clear bv | ]); destruct padding; try (simple congruence 1); box_simpl
      | simpl;
      repeat (destruct strict_in_dec as [bv | bv]; [ clear bv | ]);
      [ 
        exact IHs
        | set (x' := Base64Padding_special) in *; clearbody x';
        repeat (break_match; [ | split; intros HC; [ discriminate HC | box_simpl ] ]); split; intros ?; [ box_simpl | reflexivity ]
        | set (x' := Base64Padding_special) in *; clearbody x';
        repeat (break_match; [ | split; intros HC; [ discriminate HC | box_simpl ] ]); split; intros ?; [ box_simpl | reflexivity ]
        | split; intros HC; [ discriminate HC | box_simpl ]
        | split; intros HC; [ discriminate HC | box_simpl ]
      ]
    ].
  Qed.

  Definition Base64Padding : padding = true -> Ascii.ascii := 
    fun _ => Ascii.Ascii true false true true true true false false.
  
  Lemma Base64Padding_eq_special (Hpad : padding = true) 
    : (Base64Padding Hpad) = (Base64Padding_special Hpad).
  unfold Base64Padding, Base64Padding_special;
  subst; simpl in *; reflexivity.
  Qed.

  Lemma Base64AlphabetLengthCorrect : List.length Base64Alphabet = 64.
  Proof.
    unfold Base64Alphabet; destruct b; reflexivity.
  Qed.

  Lemma NoDupBase64Alphabet : NoDup Base64Alphabet.
  Proof.
    unfold Base64Alphabet;
    destruct b; vm_compute;
    clear b padding;
    repeat (econstructor; [
      intros HC;
      repeat (destruct HC as [HC | HC]; [ simple congruence 1 | ]);
      destruct HC
      |
    ]); exact (NoDup_nil _).
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

  Lemma Base64Padding_not_in_alphabet (Hpad : padding = true) :
    ~ In (Base64Padding Hpad) Base64Alphabet.
  Proof.
    unfold Base64Alphabet, Base64Padding;
    destruct b; vm_compute;
    intros HC; clear padding Hpad b;
    repeat (destruct HC as [HC | HC]; [ simple congruence 1 | ]);
    exact HC.
  Qed.

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

  Definition QuadSextetList_encode `{StrictEncodable Sextet Base64_Ascii}
      (Hpad : padding = true) : QuadSextetList -> Base64_String.
    refine (
      fix F l : Base64_String :=
      match l with
      | QSnil => existT _ "" _
      | QScons_one_pad (p1, p2, p3) => 
        let '(existT _ r1 Hr1) := strict_encode p1 in
        let '(existT _ r2 Hr2) := strict_encode p2 in
        let '(existT _ r3 Hr3) := strict_encode p3 in
        existT _ (String r1 (String r2 (String r3 (String (Base64Padding Hpad) "")))) _
      | QScons_two_pad (p1, p2) =>
        let '(existT _ r1 Hr1) := strict_encode p1 in
        let '(existT _ r2 Hr2) := strict_encode p2 in
        existT _ (String r1 (String r2 (String (Base64Padding Hpad) (String (Base64Padding Hpad) "")))) _
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
      set (x := ((if padding as p4 return (padding = p4 -> SProp) then fun Hpad0 : padding = true => if match Base64Padding_special Hpad0 with | Ascii.Ascii b3 b4 b5 b6 b7 b8 b9 b10 => if if if if if if if if b3 then true else false then if b4 then false else true else false then if b5 then true else false else false then if b6 then true else false else false then if b7 then true else false else false then if b8 then true else false else false then if b9 then false else true else false then if b10 then false else true else false end then STrue else SFalse else fun _ : padding = false => SFalse) eq_refl)).
      simpl in *.
      collapse_boxes.
      set (y := eq_refl) in *; clearbody y.
      unfold Base64Padding_special in *.
      simpl in *.
      set (z := (eq_ind false (fun e : bool => if e then False else True) I true)) in *; clearbody z.
      clear n.
      destruct padding; try congruence; subst x; eauto.
    - simpl in *; repeat destruct strict_in_dec; eauto; try congruence.
      clear n.
      unfold Base64Padding_special; simpl in *.
      set (z := (eq_ind false (fun e : bool => if e then False else True) I true)) in *; clearbody z.
      destruct padding; try congruence; eauto.
    - simpl in *; repeat destruct strict_in_dec; eauto; try congruence.
  Defined.

  Definition QuadSextetList_decode' `{StrictEncodable Sextet Base64_Ascii} 
    (Hpad : padding = true) :
    forall s : string, Box (Base64Encoded s) -> QuadSextetList.
    refine (
      fix F s HS : QuadSextetList :=
      _
    ).
    destruct s as [| a1 [ | a2 [ | a3 [ | a4 s5 ]]]];
    try (simpl in *; try destruct padding; box_simpl; 
      try congruence; intuition; fail);
    try (simpl in *; repeat destruct strict_in_dec;
      try destruct padding; repeat box_simpl; try congruence).
    * eapply QSnil.
    * set (a1' := strict_decode (existT _ a1 b0)).
      set (a2' := strict_decode (existT _ a2 b1)).
      set (a3' := strict_decode (existT _ a3 b2)).
      set (a4' := strict_decode (existT _ a4 b3)).
      set (rec := F s5 HS).
      eapply (QScons_all (a1', a2', a3',a4') rec).
    * unfold Base64Padding_special in *; simpl in *;
      set (z := eq_ind false (fun e : bool => if e then False else True) I true) in *; clearbody z;
      destruct padding; box_simpl;
      set (a1' := strict_decode (existT _ a1 b0)).
      set (a2' := strict_decode (existT _ a2 b1)).
      set (a3' := strict_decode (existT _ a3 b2)).
      repeat (break_match; try inv HS; intuition).
      eapply (QScons_one_pad (a1', a2', a3')).
    * unfold Base64Padding_special in *; simpl in *;
      set (z := eq_ind false (fun e : bool => if e then False else True) I true) in *; clearbody z;
      destruct padding; box_simpl;
      set (a1' := strict_decode (existT _ a1 b0)).
      set (a2' := strict_decode (existT _ a2 b1)).
      repeat (break_match; try inv HS; intuition).
      eapply (QScons_two_pad (a1', a2')).
  Defined.

  Definition QuadSextetList_decode `{StrictEncodable Sextet Base64_Ascii} 
      (Hpad : padding = true) : Base64_String -> QuadSextetList.
    intros.
    destruct H0 as [s HS].
    generalize dependent s.
    eapply (QuadSextetList_decode' Hpad).
  Defined.
  
  Theorem qsl_strict_invol : forall `{StrictEncodable Sextet Base64_Ascii} 
    (Hpad : padding = true) a,
    QuadSextetList_decode Hpad (QuadSextetList_encode Hpad a) = a.
  Proof.
    induction a; try (simpl in *; eauto; fail).
    - simpl in *; repeat break_match; subst; try congruence.
    - simpl in *; repeat break_match; subst.
      unfold QuadSextetList_decode; simpl in *;
      pose proof Base64Padding_not_in_alphabet;
      repeat destruct strict_in_dec;
      try (exfalso; intuition; rewrite strict_In_iff_In in *; 
        exfalso; eauto; intuition; congruence);
      repeat collapse_boxes;
      repeat find_rev_rew;
      repeat rewrite strict_invol; eauto.
      clear n H0.
      destruct padding; eauto.
      destruct False_ind; inv unbox.
    - simpl in *; repeat break_match; subst;
      unfold QuadSextetList_decode; simpl in *;
      pose proof Base64Padding_not_in_alphabet;
      repeat destruct strict_in_dec;
      try (exfalso; intuition; rewrite strict_In_iff_In in *; 
        exfalso; eauto; intuition; congruence);
      repeat collapse_boxes;
      repeat find_rev_rew;
      repeat rewrite strict_invol; eauto.
      clear n H0.
      destruct padding; eauto.
      destruct False_ind; inv unbox.
    - simpl in *.
      destruct p as [[[p1 p2] p3] p4].
      destruct (strict_encode p1) as [a1 Ha1] eqn:E1.
      destruct (strict_encode p2) as [a2 Ha2] eqn:E2.
      destruct (strict_encode p3) as [a3 Ha3] eqn:E3.
      destruct (strict_encode p4) as [a4 Ha4] eqn:E4.
      destruct (QuadSextetList_encode Hpad a) as [rec Hrec].
      unfold QuadSextetList_decode in IHa.
      set (x := match strict_in_dec a1 Base64Alphabet as s return (Box (if s then if strict_in_dec a2 Base64Alphabet then if strict_in_dec a3 Base64Alphabet then if strict_in_dec a4 Base64Alphabet then Base64Encoded rec else (if padding as p return (padding = p -> SProp) then fun Hpad0 : padding = true => if Ascii.eqb a4 (Base64Padding_special Hpad0) then match rec with | "" => STrue | String _ _ => SFalse end else SFalse else fun _ : padding = false => SFalse) eq_refl else (if padding as p return (padding = p -> SProp) then fun Hpad0 : padding = true => if Ascii.eqb a3 (Base64Padding_special Hpad0) then if Ascii.eqb a4 (Base64Padding_special Hpad0) then match rec with | "" => STrue | String _ _ => SFalse end else SFalse else SFalse else fun _ : padding = false => SFalse) eq_refl else SFalse else SFalse)) with | left _ => match strict_in_dec a2 Base64Alphabet as s return (Box (if s then if strict_in_dec a3 Base64Alphabet then if strict_in_dec a4 Base64Alphabet then Base64Encoded rec else (if padding as p return (padding = p -> SProp) then fun Hpad0 : padding = true => if Ascii.eqb a4 (Base64Padding_special Hpad0) then match rec with | "" => STrue | String _ _ => SFalse end else SFalse else fun _ : padding = false => SFalse) eq_refl else (if padding as p return (padding = p -> SProp) then fun Hpad0 : padding = true => if Ascii.eqb a3 (Base64Padding_special Hpad0) then if Ascii.eqb a4 (Base64Padding_special Hpad0) then match rec with | "" => STrue | String _ _ => SFalse end else SFalse else SFalse else fun _ : padding = false => SFalse) eq_refl else SFalse)) with | left _ => match strict_in_dec a3 Base64Alphabet as s return (Box (if s then if strict_in_dec a4 Base64Alphabet then Base64Encoded rec else (if padding as p return (padding = p -> SProp) then fun Hpad0 : padding = true => if Ascii.eqb a4 (Base64Padding_special Hpad0) then match rec with | "" => STrue | String _ _ => SFalse end else SFalse else fun _ : padding = false => SFalse) eq_refl else (if padding as p return (padding = p -> SProp) then fun Hpad0 : padding = true => if Ascii.eqb a3 (Base64Padding_special Hpad0) then if Ascii.eqb a4 (Base64Padding_special Hpad0) then match rec with | "" => STrue | String _ _ => SFalse end else SFalse else SFalse else fun _ : padding = false => SFalse) eq_refl)) with | left _ => match strict_in_dec a4 Base64Alphabet as s return (Box (if s then Base64Encoded rec else (if padding as p return (padding = p -> SProp) then fun Hpad0 : padding = true => if Ascii.eqb a4 (Base64Padding_special Hpad0) then match rec with | "" => STrue | String _ _ => SFalse end else SFalse else fun _ : padding = false => SFalse) eq_refl)) with | left _ => Hrec | right n => False_ind (Box ((if padding as p return (padding = p -> SProp) then fun Hpad0 : padding = true => if Ascii.eqb a4 (Base64Padding_special Hpad0) then match rec with | "" => STrue | String _ _ => SFalse end else SFalse else fun _ : padding = false => SFalse) eq_refl)) (n Ha4) end | right n => False_ind (Box ((if padding as p return (padding = p -> SProp) then fun Hpad0 : padding = true => if Ascii.eqb a3 (Base64Padding_special Hpad0) then if Ascii.eqb a4 (Base64Padding_special Hpad0) then match rec with | "" => STrue | String _ _ => SFalse end else SFalse else SFalse else fun _ : padding = false => SFalse) eq_refl)) (n Ha3) end | right n => False_ind (Box SFalse) (n Ha2) end | right n => False_ind (Box SFalse) (n Ha1) end); clearbody x.
      simpl.
      destruct strict_in_dec; intuition; eauto; try congruence.
      destruct strict_in_dec; intuition; eauto; try congruence.
      destruct strict_in_dec; intuition; eauto; try congruence.
      destruct strict_in_dec; intuition; eauto; try congruence.
      repeat collapse_boxes.
      repeat find_rev_rew.
      repeat rewrite strict_invol; eauto.
      set (x' := eq_ind false (fun e : bool => if e then False else True) I true); clearbody x';
      simpl in *.
      set (x'' := (fun Hpad0 : false = true => False_rec QuadSextetList (x' Hpad0))).
      clearbody x''.
      set (Z := QScons_all (p1, p2, p3, p4) (QuadSextetList_decode' Hpad rec x)); clearbody Z.
      destruct padding; eauto; congruence.
  Qed. 

  Global Instance StrictEncodable_quadsextetlist_base64_string  
      `{StrictEncodable Sextet Base64_Ascii} 
      (Hpad : padding = true) :
      StrictEncodable QuadSextetList Base64_String := {
    strict_encode := (QuadSextetList_encode Hpad);
    strict_decode := (QuadSextetList_decode Hpad);
    strict_invol := (qsl_strict_invol Hpad)
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

  Global Instance StrictEncodable_string_base64_string_pad 
    (Hpad : padding = true)
    : StrictEncodable string Base64_String.
    pose proof (StrictEncodable_string_quadsextetlist).
    pose proof (StrictEncodable_quadsextetlist_base64_string Hpad).
    eapply Build_StrictEncodable with
      (strict_encode := fun s => strict_encode (strict_encode s))
      (strict_decode := fun s => strict_decode (strict_decode s)).
    intros.
    repeat rewrite strict_invol; eauto.
  Defined.
    
  Fixpoint string_to_base64_string_no_pad
    `{StrictEncodable Sextet Base64_Ascii}
    `{HE1 : StrictEncodable (Ascii.ascii * Ascii.ascii * Ascii.ascii) (Sextet * Sextet * Sextet * Sextet)}
    `{HE2 : StrictEncodable (Ascii.ascii * Ascii.ascii) (Sextet * Sextet * Sextet)}
    `{HE3 : StrictEncodable (Ascii.ascii) (Sextet * Sextet)}
    (Hpad : padding = false)
    (s : string)
    : Base64_String.
  destruct s as [| a1 [ | a2 [ | a3  s4 ]]].
  - eapply (existT _ "" _).
    Unshelve. simpl in *; eauto.
  - pose proof (strict_encode a1) as [sx1 sx2].
    destruct (strict_encode sx1) as [a1' Ha1'].
    destruct (strict_encode sx2) as [a2' Ha2'].
    eapply (existT _ (String a1' (String a2' "")) _).
    Unshelve.  simpl in *; rewrite Hpad; eauto.
    repeat destruct strict_in_dec; eauto;
    collapse_boxes; try (exfalso; eauto).
  - pose proof (strict_encode (a1, a2)) as [[sx1 sx2] sx3].
    destruct (strict_encode sx1) as [a1' Ha1'].
    destruct (strict_encode sx2) as [a2' Ha2'].
    destruct (strict_encode sx3) as [a3' Ha3'].
    eapply (existT _ (String a1' (String a2' (String a3' ""))) _).
    Unshelve.  simpl in *; rewrite Hpad; eauto.
    repeat destruct strict_in_dec; eauto;
    collapse_boxes; try (exfalso; eauto).
  - pose proof (strict_encode (a1, a2, a3)) as [[[sx1 sx2] sx3] sx4].
    destruct (strict_encode sx1) as [a1' Ha1'].
    destruct (strict_encode sx2) as [a2' Ha2'].
    destruct (strict_encode sx3) as [a3' Ha3'].
    destruct (strict_encode sx4) as [a4' Ha4'].
    destruct (string_to_base64_string_no_pad _ _ _ _ Hpad s4) as [rec Hrec].
    eapply (existT _ (String a1' (String a2' (String a3' (String a4' rec)))) _).
    Unshelve. simpl in *.
    repeat destruct strict_in_dec; try congruence.
  Defined.
  
  Definition base64_string_to_string_no_pad' 
    `{StrictEncodable Sextet Base64_Ascii}
    `{HE1 : StrictEncodable (Ascii.ascii * Ascii.ascii * Ascii.ascii) (Sextet * Sextet * Sextet * Sextet)}
    `{HE2 : StrictEncodable (Ascii.ascii * Ascii.ascii) (Sextet * Sextet * Sextet)}
    `{HE3 : StrictEncodable (Ascii.ascii) (Sextet * Sextet)}
    (Hpad : padding = false) 
    : forall s : string, Box (Base64Encoded s) -> string.
    refine (
      fix F s HS : string :=
      _
    ).
  destruct s as [| a1 [| a2 [| a3 [| a4 s4]]]].
  - eapply "".
  - simpl in *; box_simpl.
  - simpl in *.
    repeat destruct strict_in_dec; box_simpl.
    set (sx1 := strict_decode (existT _ a1 b0)).
    set (sx2 := strict_decode (existT _ a2 b1)).
    set (s1 := strict_decode (sx1, sx2)).
    eapply (String s1 EmptyString).
  - simpl in *.
    repeat destruct strict_in_dec; box_simpl.
    set (sx1 := strict_decode (existT _ a1 b0)).
    set (sx2 := strict_decode (existT _ a2 b1)).
    set (sx3 := strict_decode (existT _ a3 b2)).
    destruct (strict_decode (sx1, sx2, sx3)) as [s1 s2].
    eapply (String s1 (String s2 EmptyString)).
  - simpl in *.
    repeat destruct strict_in_dec; box_simpl.
    * 
    set (sx1 := strict_decode (existT _ a1 b0)).
    set (sx2 := strict_decode (existT _ a2 b1)).
    set (sx3 := strict_decode (existT _ a3 b2)).
    set (sx4 := strict_decode (existT _ a4 b3)).
    destruct (strict_decode (sx1, sx2, sx3, sx4)) as [[s1 s2] s3].
    set (rec := (F _ HS)).
    eapply (String s1 (String s2 (String s3 rec))).
    * set (y := fun Hpad : padding = true => if Ascii.eqb a4 (Base64Padding_special Hpad) then match s4 with | "" => STrue | String _ _ => SFalse end else SFalse) in *; clearbody y.
      destruct padding; try congruence.
    * set (y := fun Hpad : padding = true => if Ascii.eqb a3 (Base64Padding_special Hpad) then if Ascii.eqb a4 (Base64Padding_special Hpad) then match s4 with | "" => STrue | String _ _ => SFalse end else SFalse else SFalse) in *; clearbody y.
      destruct padding; try congruence.
  Defined.

  Definition base64_string_to_string_no_pad 
    `{StrictEncodable Sextet Base64_Ascii}
    `{HE1 : StrictEncodable (Ascii.ascii * Ascii.ascii * Ascii.ascii) (Sextet * Sextet * Sextet * Sextet)}
    `{HE2 : StrictEncodable (Ascii.ascii * Ascii.ascii) (Sextet * Sextet * Sextet)}
    `{HE3 : StrictEncodable (Ascii.ascii) (Sextet * Sextet)}
    (Hpad : padding = false) : Base64_String -> string.
    intros.
    destruct H0 as [s HS].
    generalize dependent s.
    eapply (base64_string_to_string_no_pad' Hpad).
  Defined.
  
  Global Instance StrictEncodable_string_base64_string_no_pad 
    `{StrictEncodable Sextet Base64_Ascii}
    `{HE1 : StrictEncodable (Ascii.ascii * Ascii.ascii * Ascii.ascii) (Sextet * Sextet * Sextet * Sextet)}
    `{HE2 : StrictEncodable (Ascii.ascii * Ascii.ascii) (Sextet * Sextet * Sextet)}
    `{HE3 : StrictEncodable (Ascii.ascii) (Sextet * Sextet)}
    (Hpad : padding = false)
    : StrictEncodable string Base64_String.
  refine ({|
    strict_encode := (string_to_base64_string_no_pad Hpad);
    strict_decode := (base64_string_to_string_no_pad Hpad);
    strict_invol := _
  |}).
    induction a using string_ind3; try (simpl in *; eauto; fail).
    - simpl; repeat break_match; 
      unfold base64_string_to_string_no_pad;
      simpl in *.
      repeat destruct strict_in_dec; try congruence;
      repeat collapse_boxes;
      repeat find_rev_rew; repeat rewrite strict_invol; eauto;
      repeat find_rev_rew; repeat rewrite strict_invol; eauto.
    - simpl; repeat break_match; 
      unfold base64_string_to_string_no_pad;
      simpl in *.
      repeat destruct strict_in_dec; try congruence;
      repeat collapse_boxes;
      repeat find_rev_rew; repeat rewrite strict_invol; eauto;
      repeat find_rev_rew; repeat rewrite strict_invol; eauto.
    - 
      simpl.
      repeat break_match;
      unfold base64_string_to_string_no_pad;
      simpl; subst;
      try (set (x' := Base64Padding_special) in *; clearbody x');
      repeat (destruct strict_in_dec); collapse_boxes;
      try (destruct padding); try (simple congruence 1);
      try (erewrite <- Heqb0; clear Heqb0; erewrite strict_invol);
      try (erewrite <- Heqb1; clear Heqb1; erewrite strict_invol);
      try (erewrite <- Heqb2; clear Heqb2; erewrite strict_invol);
      try (erewrite <- Heqb3; clear Heqb3; erewrite strict_invol);
      try (erewrite <- Heqp; clear Heqp; erewrite strict_invol);
      try (reflexivity).
  Defined.

  (* If you are wanting to convert strings to/from Base64 strings, this
  is the typeclass instance you are wanting to use!!! *)
  Global Instance StrictEncodable_string_base64_string 
    : StrictEncodable string Base64_String :=
  match padding as p return padding = p -> _ with
  | true => fun Hpad => StrictEncodable_string_base64_string_pad Hpad
  | false => fun Hpad => StrictEncodable_string_base64_string_no_pad Hpad
  end eq_refl.
  
End Base64.

Definition no_null_bytes (s : string) : Prop :=
  ~ (In Ascii.zero (list_ascii_of_string s)).

Lemma null_byte_not_in_alphabet : forall b,
  ~ (In Ascii.zero (Base64Alphabet b)).
Proof.
  intros b HC.
  destruct b; unfold Base64Alphabet; vm_compute in HC;
  repeat (destruct HC as [HC | HC]; [ discriminate HC | ]);
  exact HC.
Qed.

Theorem base64_no_null_bytes : forall b pad (s : Base64_String b pad),
  no_null_bytes (projT1 s).
Proof.
  induction s; simpl in *.
  induction x using string_ind4; unfold no_null_bytes; simpl in *;
  intros HC; intuition; subst; eauto; box_simpl;
  try (repeat destruct strict_in_dec; box_simpl;
  eapply null_byte_not_in_alphabet;
  erewrite <- strict_In_iff_In; eauto; fail).
  - repeat destruct strict_in_dec; box_simpl;
    try (eapply null_byte_not_in_alphabet;
    erewrite <- strict_In_iff_In; eauto; fail);
    destruct pad; simpl in *; box_simpl.
  - repeat destruct strict_in_dec; box_simpl;
    try (eapply null_byte_not_in_alphabet;
    erewrite <- strict_In_iff_In; eauto; fail);
    destruct pad; simpl in *; box_simpl.
    destruct Ascii.eqb; box_simpl.
  - repeat destruct strict_in_dec; box_simpl;
    try (eapply null_byte_not_in_alphabet;
    erewrite <- strict_In_iff_In; eauto; fail);
    destruct pad; simpl in *; box_simpl; intuition; eauto.
    * destruct Ascii.eqb; box_simpl.
      destruct x; box_simpl; simpl in *; intuition.
    * destruct Ascii.eqb; box_simpl.
      destruct Ascii.eqb; box_simpl.
      destruct x; box_simpl; simpl in *; intuition.
Qed.

Local Instance StandardPaddedStringEncoder : StrictEncodable string (Base64_String Base64Standard true).
  typeclasses eauto.
Defined.
Local Instance StandardNoPadStringEncoder : StrictEncodable string (Base64_String Base64Standard false).
  typeclasses eauto.
Defined.

(* 
(** NOTE: These examples should all compile, but it is really 
    costly to calculate them all the time, so they are current commented out. 
*)

Section Base64_Testing.

  Definition test_str := "Hello".
  Definition newline := String (Ascii.Ascii false true false true false false false false) EmptyString.
  Definition test_str_2 := String.concat "" ["a"; newline; "a"].

  Definition base64_test_str := "SGVsbG8=".
  Definition base64_test_str_no_pad := "SGVsbG8".
  Definition base64_encoded_base64_test_str 
    : Box (Base64Encoded Base64Standard true base64_test_str).
    erewrite <- Base64Encoded_bool_iff;
      (* Base64Encoded_bool Base64Standard base64_test_str = true. *)
    unfold base64_test_str;
    vm_compute;
    repeat (destruct strict_in_dec as [b | b]; [ clear b | ]);
    try reflexivity;
    vm_compute in *;
    exfalso;
    eapply b; clear b; refine (box _);
    destruct (DecEq_from_EqClass Ascii.ascii);
    repeat (destruct decEq; [ try (discriminate e); exact sI | try (exact (False_sind _ (n eq_refl))); clear n ]).
  Qed.
  Definition base64_encoded_base64_test_str_no_pad
    : Box (Base64Encoded Base64Standard false base64_test_str_no_pad).
    erewrite <- Base64Encoded_bool_iff.
      (* Base64Encoded_bool Base64Standard base64_test_str = true. *)
    unfold base64_test_str_no_pad.
    unfold Base64Encoded_bool.
    repeat (destruct strict_in_dec as [b | b]; [ clear b | ]);
    try reflexivity;
    vm_compute in *;
    exfalso;
    eapply b; clear b; refine (box _);
    destruct (DecEq_from_EqClass Ascii.ascii);
    repeat (destruct decEq; [ try (discriminate e); exact sI | try (exact (False_sind _ (n eq_refl))); clear n ]).
  Qed.

  Definition base64_test_str_base64_type : Base64_String Base64Standard true :=
    existT _ base64_test_str base64_encoded_base64_test_str.

  (* NOTE: We are using the projection out of this, since that is the real string value.
  
  Technically, since we have all the involutivity proofs completed as part of the StrictEncodable, they should be strictly equivalent. However this takes an IMMENSE amount of time to verify, so it is just simpler to complete it this way instead *)
  Example encode_test_1 : 
    projT1 (@strict_encode _ _ StandardPaddedStringEncoder test_str) = projT1 (base64_test_str_base64_type).
  Proof.
    unfold base64_test_str_base64_type.
    simpl.
    unfold base64_test_str.
    reflexivity.
  Qed.

  Definition oww_str := "Oww".

  Lemma oww_str_base64_encoded : 
    Box (Base64Encoded Base64Standard false oww_str).
  Proof.
    unfold oww_str.
    vm_compute.
    repeat destruct strict_in_dec.
    - unfold strict_In in *; 
      repeat (destruct decEq; [ simple congruence 1 | ]); box_simpl;
      eauto.
    - exfalso; eapply n;
      unfold strict_In in *;
      repeat (repeat (destruct decEq; [ simple congruence 1 | ]);
      repeat (destruct decEq; [ | simple congruence 1 ])).
      congruence.
    - exfalso; eapply n;
      unfold strict_In in *;
      repeat (repeat (destruct decEq; [ simple congruence 1 | ]);
      repeat (destruct decEq; [ | simple congruence 1 ])).
      destruct n.
      eauto.
  Qed.

  Definition base64_test_str_oww : Base64_String Base64Standard false :=
    existT _ oww_str oww_str_base64_encoded.
  
  Lemma base64_test_str_oww_invol : 
    strict_decode base64_test_str_oww = 
    (String (Ascii.Ascii true true false true true true false false) (String (Ascii.Ascii false false true true false false false false) EmptyString)).
  Proof.
    unfold base64_test_str_oww.
    unfold strict_decode, StandardNoPadStringEncoder, StrictEncodable_string_base64_string,
    StrictEncodable_string_base64_string_no_pad,
    base64_string_to_string_no_pad.
    unfold oww_str.
    set (z := oww_str_base64_encoded).
    clearbody z.
    unfold oww_str in *.
    unfold Base64Encoded in z.
    unfold base64_string_to_string_no_pad'.
    set (x := strict_in_dec (Ascii.Ascii true true true true false false true false) (Base64Alphabet Base64Standard)) in *.
    set (x' := strict_in_dec (Ascii.Ascii true true true false true true true false) (Base64Alphabet Base64Standard)) in *. 
    set (x'' := fun HS1 : Box SFalse => match HS1 with | {| unbox := unbox |} => SFalse_rec (fun _ : SFalse => string) unbox end) in *.
    clearbody x''.
    set (y := if x' then STrue else SFalse) in *.
    set (y' := if x' then y else SFalse) in *.
    clearbody x.
    clearbody x'.
    destruct x, x'; box_simpl.
    - subst y y'.
      clear x''.
      set (F := (fun a : Ascii.ascii => Box (strict_In a (Base64Alphabet Base64Standard)))) in *.
      unfold strict_decode,
        StrictEncodable_two_ascii_three_sextet,
        Encodable_sextet_base64_ascii,
        packet_decode.
      unfold projT1, projT2.
      set (a1 := (eq_ind (Datatypes.length (Base64Alphabet Base64Standard)) (fun n : nat => index_of_safe (Ascii.Ascii true true true false true true true false) (Base64Alphabet Base64Standard) (box_proj b0) < n) (index_of_nth_lt_length Ascii.ascii (Base64Alphabet Base64Standard) (Ascii.Ascii true true true false true true true false) (box_proj b0)) 64 (Base64AlphabetLengthCorrect Base64Standard))).
      clearbody a1.
      set (a2 := (eq_ind (Datatypes.length (Base64Alphabet Base64Standard)) (fun n : nat => index_of_safe (Ascii.Ascii true true true true false false true false) (Base64Alphabet Base64Standard) (box_proj b) < n))).
      clearbody a2.
      set (a3 := (a2 (index_of_nth_lt_length Ascii.ascii (Base64Alphabet Base64Standard) (Ascii.Ascii true true true true false false true false) (box_proj b)) 64 (Base64AlphabetLengthCorrect Base64Standard))).
      clearbody a3.
      clear a2.
      clear F.
      destruct b, b0.
      unfold box_proj in *.
      set (i1 := index_of_safe (Ascii.Ascii true true true false true true true false) (Base64Alphabet Base64Standard) unbox0) in *.
      set (i2 := index_of_safe (Ascii.Ascii true true true true false false true false) (Base64Alphabet Base64Standard) unbox) in *.
      set (B := Base64Alphabet Base64Standard) in *.
      unfold Base64Alphabet in B.
      vm_compute in B.
      assert (index_of_safe (Ascii.Ascii true true true false true true true false) B unbox0 = 48). {
        clear -B.
        subst B.
        eapply index_of_impl_index_of_safe.
        clear unbox0.
        simpl; eauto.
      }
      assert (index_of_safe (Ascii.Ascii true true true true false false true false) B unbox = 14). {
        clear -B.
        subst B.
        eapply index_of_impl_index_of_safe.
        simpl; eauto.
      }
      assert (Sextet_from_nat_safe i1 a1 = sextet true true false false false false). {
        subst i1.
        eapply Sextet_from_nat_impl_Sextet_from_nat_safe.
        rewrite H.
        simpl.
        eauto.
      }
      assert (Sextet_from_nat_safe i2 a3 = sextet false false true true true false). {
        subst i2.
        eapply Sextet_from_nat_impl_Sextet_from_nat_safe.
        rewrite H0.
        simpl.
        eauto.
      }
      rewrite H1, H2.
      eauto.
    - exfalso.
      eapply n.
      clear b z x'' y y' n.
      simpl.

      repeat (destruct decEq; [ try (discriminate e); exact (box sI) | try (exact (box (False_sind _ (n eq_refl)))); clear n ]).
  Qed.

End Base64_Testing.
*)
