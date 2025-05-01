let describe_number n =
  if n < 0 then
    "Negative"
  else if n = 0 then
    "Zero"
  else
    "Positive"

let describe_list lst =
  match lst with
  | [] -> "Empty list"
  | [x] -> "Single element list"
  | x :: y :: _ -> "Longer list"

let () =
  let n = 5 in
  let lst = [1; 2; 3] in
  Printf.printf "Number %d is: %s\n" n (describe_number n);
  Printf.printf "List description: %s\n" (describe_list lst)
