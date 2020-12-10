let test_permutations candidate =
  let b0 = (candidate [] =
              [[]])
  and b1 = (candidate [1] =
              [[1]])
  and b2 = (candidate [2; 1] =
              [[2; 1]; [1; 2]])
  and b3 = (candidate [3; 2; 1] =
              [[3; 2; 1]; [2; 3; 1]; [2; 1; 3]; [3; 1; 2]; [1; 3; 2]; [1; 2; 3]])
  in b0 && b1 && b2 && b3;;

let test_inject candidate =
  let b0 = (candidate 1 [] =
              [[1]])
  and b1 = (candidate 2 [1] =
              [[2; 1]; [1; 2]])
  and b2 = (candidate 3 [2; 1] =
              [[3; 2; 1]; [2; 3; 1]; [2; 1; 3]])
  in b0 && b1 && b2;;

let inject x xs_given =
  let rec visit xs a =
    (List.rev_append a (x :: xs)) :: (match xs with
                                      | [] ->
                                         []
                                      | x' :: xs' ->
                                         visit xs' (x' :: a))   
  in visit xs_given [];;

let () = assert (test_inject inject);;

let map_append f vs =
  let rec visit vs =
    match vs with
    | []  ->
       []
    | v :: vs' ->
       List.append (f v) (visit vs')
  in visit vs;;

let permutations vs_given =
  let rec visit vs =
    match vs with
    | [] ->
       [[]]
    | v :: vs' ->
       map_append (fun ih -> inject v ih) (visit vs')
  in visit vs_given;;

let () = assert (test_permutations permutations);;
