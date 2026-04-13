(** Base64 implementation benchmark.
    Run:  dune exec bench/bench.exe
*)

(* ---------- Shared proof stub for the Coq decoders ---------- *)
let coq_proof : Base64.__ =
  Obj.repr
    (let rec f _ = Obj.repr f in
     Obj.repr f)
;;

(* ---------- String ↔ char list ---------- *)
let str_to_clist (s : string) : char list =
  List.init (String.length s) (String.unsafe_get s)
;;

let clist_to_str (cl : char list) : string =
  let n = List.length cl in
  let buf = Bytes.create n in
  List.iteri (Bytes.unsafe_set buf) cl;
  Bytes.unsafe_to_string buf
;;

(* ---------- Coq V0 wrappers ---------- *)
let coq_v0_encode (src : string) : string =
  let (Base64.ExistT (cl_out, _)) =
    Base64.standardPaddedStringEncoder.Base64.strict_encode (str_to_clist src)
  in
  clist_to_str cl_out
;;

let coq_v0_decode (src : string) : string =
  clist_to_str
    (Base64.standardPaddedStringEncoder.Base64.strict_decode
       (Base64.ExistT (str_to_clist src, coq_proof)))
;;

(* ---------- Timing helpers ---------- *)
let now () = Unix.gettimeofday ()

let time_iters iters f =
  let t0 = now () in
  for _ = 1 to iters do
    ignore (f ())
  done;
  now () -. t0
;;

(** Pick an iteration count so the run takes roughly [target_s] seconds.
    When [cap] is very small (≤ 3), skip the probe run and just use [cap]
    directly – avoids a 68-117 s probe for V0/V1 on large inputs. *)
let calibrate ?(cap = max_int) f target_s =
  if cap <= 3
  then cap
  else (
    let t1 = now () in
    ignore (f ());
    let t1 = now () -. t1 in
    let n = if t1 < 1e-9 then cap else int_of_float (target_s /. t1) in
    max 1 (min cap n))
;;

(* ---------- Output helpers ---------- *)
let hline () = Printf.printf "  %s\n" (String.make 68 '-')

let print_row ~label ~bytes_per_iter ~iters ~elapsed =
  let mb_s = float_of_int (bytes_per_iter * iters) /. elapsed /. 1e6 in
  let us_op = elapsed /. float_of_int iters *. 1e6 in
  Printf.printf "  %-30s  %9.2f MB/s  %10.2f µs/op\n%!" label mb_s us_op
;;

(* ---------- Correctness sanity check ---------- *)
let check encoder1 encoder2 decoder1 decoder2 =
  let inputs =
    [ ""
    ; "a"
    ; "ab"
    ; "abc"
    ; "Hello, World!"
    ; "The quick brown fox jumps over the lazy dog"
    ; String.init 256 Char.chr
    ]
  in
  let ok = ref true in
  List.iter
    (fun plain ->
       let v0 = encoder1 plain in
       let v1 = encoder2 plain in
       if v0 <> v1
       then (
         Printf.printf "  ENCODE MISMATCH for %S:\n" plain;
         Printf.printf "    v0=%S\n    v1=%S\n" v0 v1;
         ok := false);
       let v0d = decoder1 v0 in
       let v1d = decoder2 v1 in
       if v0d <> plain || v1d <> plain
       then (
         Printf.printf "  DECODE MISMATCH for %S:\n" plain;
         Printf.printf "    v0d=%S\n    v1d=%S\n" v0d v1d;
         ok := false))
    inputs;
  if !ok
  then Printf.printf "  All correctness checks PASSED.\n%!"
  else Printf.printf "  CORRECTNESS FAILURES DETECTED.\n%!"
;;

(* ---------- Main ---------- *)
let () =
  Random.self_init ();
  Printf.printf "\n╔══════════════════════════════════════════════════════════════╗\n";
  Printf.printf "║           Base64 Implementation Benchmark                   ║\n";
  Printf.printf "╚══════════════════════════════════════════════════════════════╝\n";
  Printf.printf "OCaml %s\n\n" Sys.ocaml_version;
  let sizes = [| 4; 16; 64 |] in
  let target = 0.4 in
  (* ----- ENCODE ----- *)
  Printf.printf "=== Encode throughput (plain bytes → base64) ===\n";
  Printf.printf "  %-30s  %9s  %12s\n" "Implementation" "MB/s" "µs/op%!";
  hline ();
  Array.iter
    (fun n ->
       Printf.printf "\n  ── input: %d bytes ──\n%!" n;
       let src = String.init n (fun _ -> Char.chr (Random.int 256)) in
       let i = calibrate (fun () -> coq_v0_encode src) target in
       let t = time_iters i (fun () -> coq_v0_encode src) in
       print_row ~label:"coq_v0  (baseline)" ~bytes_per_iter:n ~iters:i ~elapsed:t)
    sizes;
  (* ----- DECODE ----- *)
  Printf.printf "\n=== Decode throughput (base64 → plain bytes) ===\n";
  Printf.printf "  %-30s  %9s  %12s\n" "Implementation" "MB/s" "µs/op%!";
  hline ();
  Array.iter
    (fun n ->
       let src = String.init n (fun _ -> Char.chr (Random.int 256)) in
       let encoded = coq_v0_encode src in
       (* let encoded = Native_base64.encode src in *)
       let enc_n = String.length encoded in
       Printf.printf "\n  ── encoded: %d bytes (plain: %d) ──\n%!" enc_n n;
       let i = calibrate (fun () -> coq_v0_decode encoded) target in
       let t = time_iters i (fun () -> coq_v0_decode encoded) in
       print_row ~label:"coq_v0  (baseline)" ~bytes_per_iter:enc_n ~iters:i ~elapsed:t)
    sizes;
  Printf.printf "\n"
;;
