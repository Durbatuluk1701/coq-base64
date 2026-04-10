open Base64

let string_to_char_list (s: string) : char list =
  List.init (String.length s) (String.get s)

let char_list_to_string (cl: char list) : string =
  String.init (List.length cl) (List.nth cl)

let usage () =
  print_endline "Usage: test_base64 [encode|decode] <string>"

let () = 
  let args = Array.to_list Sys.argv in
  let { strict_encode; strict_decode } = standardPaddedStringEncoder in
  match args with
  | [ _; "encode"; x ] -> 
      string_to_char_list x
      |> strict_encode
      |> projT1
      |> char_list_to_string
      |> print_endline
  | [ _; "decode"; x ] -> 
      let __ = let rec f _ = Obj.repr f in Obj.repr f in
      string_to_char_list x
      |> fun cl -> strict_decode (ExistT (cl, __))
      |> char_list_to_string
      |> print_endline
  | _ -> usage ()