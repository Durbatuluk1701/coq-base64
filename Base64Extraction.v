Require Import Base64String.
Require Import Extraction.

(*
  Base64 Extraction
  =================

  This file contains the extraction of the Base64 encoding and decoding functions
  to OCaml. The extraction is done using the `Extraction` command from Coq.
*)

Extraction Language OCaml.

Require Import ExtrOcamlBasic.
Require Import ExtrOcamlString.

Set Extraction Output Directory "extracted".

Extraction "base64.ml" StandardPaddedStringEncoder.