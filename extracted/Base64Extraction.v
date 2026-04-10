From base64 Require Import Base64String.
From Corelib Require Import Extraction.

(*
  Base64 Extraction
  =================

  This file contains the extraction of the Base64 encoding and decoding functions
  to OCaml. The extraction is done using the `Extraction` command from Coq.
*)

Extraction Language OCaml.

From Stdlib Require Import ExtrOcamlBasic.
From Stdlib Require Import ExtrOcamlString.

Set Extraction Output Directory ".".

Extraction "base64.ml" StandardPaddedStringEncoder.