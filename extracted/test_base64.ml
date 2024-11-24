open Base64

let test_val = "Hello, World!"

let string_to_char_list (s: string) : char list =
  List.init (String.length s) (String.get s)

let char_list_to_string (cl: char list) : string =
  String.init (List.length cl) (List.nth cl)

let test_val_list = string_to_char_list test_val

let test_enc = standardPaddedStringEncoder.strict_encode test_val_list

let _ = print_endline (char_list_to_string (projT1 test_enc))