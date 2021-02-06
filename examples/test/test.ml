let rec print_list list = 
  let result = "" in 
  match list with 
  |l::list'->(sprintf "%s" l)^(print_list list')
  |[] -> sprintf ""

  let rec getHead list = 
    match list with 
    | hd::list' -> sprintf "%s" hd
    |[] -> sprintf " "