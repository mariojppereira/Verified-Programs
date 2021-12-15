let rec fold_left (l0: 'a list [@ghost]) (v: 'a list [@ghost]) f acc = function
  | [] -> acc
  | x :: r -> fold_left l0 (v @ [x]) f (f acc x) r
(*@ fold_left l0 visited f acc param
      requires l0 = visited @ param
      variant  List.length param *)

type 'a tree = Empty | Node of 'a * 'a forest
and 'a forest = 'a tree list

(*@ predicate not_middle_empty (f: 'a forest) =
      match f with
      | [] -> true
      | x :: r -> x <> Empty && not_middle_empty r *)

(*@ predicate not_empty (t: 'a tree) =
      match t with
      | Empty -> true
      | Node _ ff -> not_middle_empty ff *)

(*@ lemma not_middle_empty: forall f: 'a forest, t: 'a tree.
      not_middle_empty f -> List.mem t f -> not_empty t *)

let[@logic] [@ghost] rec size_tree = function
  | Empty -> 0
  | Node (_, ff) -> 1 + size_forest ff
(*@ ensures result >= 0 *)
and size_forest = function
  | [] -> 0
  | x :: r -> 1 + size_tree x + size_forest r
(*@ ensures result >= 0 *)

(*@ lemma size_forest_app: forall f1 f2: 'a forest.
      size_forest (f1 @ f2) = size_forest f1 + size_forest f2 *)

let rec fold_tree f acc = function
  | Empty -> acc
  | Node (x, ff) -> fold_forest f (f acc x) ff
(*@ r = fold_tree f acc param
      requires not_empty param
      variant  size_tree param *)
and fold_forest f acc l =
  fold_left l []
    (fun [@gospel {| requires List.mem x l |}] x acc -> fold_tree f acc x) acc l
(*@ requires not_middle_empty l
    variant  size_forest l *)
