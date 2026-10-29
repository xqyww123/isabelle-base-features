(*  Regression cases for an implementation of INET, and the replay that runs an Item_Net built on
    it through the histories of the container of reverted abbreviations against the stock
    Item_Net on Net.  A case returns its failure message; a non-interrupt exception is a failure.
*)

signature INET_REGRESSION =
sig
  val replay: ('a * 'a -> bool) -> ('a -> term list) -> 'a list -> string list
  val failures: unit -> string list
end;

functor INet_Regression(N: INET): INET_REGRESSION =
struct

structure Items = Item_Net(N);

fun guarded name f =
  (case Exn.capture f () of
    Exn.Res msgs => map (fn msg => name ^ ": " ^ msg) msgs
  | Exn.Exn exn =>
      if Exn.is_interrupt exn then Exn.reraise exn
      else [name ^ ": exception " ^ Runtime.exn_message exn]);


(* replay *)

(*the stride subset that is re-updated and removed; the overlapping halves that are merged*)
fun picked xs = map_filter (fn (i, x) => if i mod 7 = 3 then SOME x else NONE) (map_index I xs);
fun halves xs =
  let val n = length xs
  in (drop (n * 2 div 5) xs, take (n * 3 div 5) xs) end;

(*after each history, content and every item's lookup equal the stock ones.  lookup asks
  unify_term with the item's own pattern and keeps the entries eq to it (member's path), so on
  correct code it gives one copy of an item in content and none otherwise, on both nets*)
fun replay eq index items =
  let
    fun same xs ys = length xs = length ys andalso forall eq (xs ~~ ys);
    fun build_S xs = fold_rev Item_Net.update xs (Item_Net.init eq index);
    fun build_N xs = fold_rev Items.update xs (Items.init eq index);
    val re = picked items;
    val (older, newer) = halves items;
    val histories =
     [("build", fn () => (build_S items, build_N items)),
      ("re-update", fn () =>
        (fold Item_Net.update re (build_S items), fold Items.update re (build_N items))),
      ("removal", fn () =>
        (fold Item_Net.remove re (build_S items), fold Items.remove re (build_N items))),
      ("merge", fn () =>
        (Item_Net.merge (build_S older, build_S newer),
          Items.merge (build_N older, build_N newer))),
      ("merge reversed", fn () =>
        (Item_Net.merge (build_S newer, build_S older),
          Items.merge (build_N newer, build_N older)))];
    fun check (name, history) =
      guarded ("replay, " ^ name) (fn () =>
        let
          val (s, n) = history ();
          val content = if same (Item_Net.content s) (Items.content n) then [] else ["content"];
          val lookup =
            map_index I items
            |> filter_out (fn (_, x) => same (Item_Net.lookup s x) (Items.lookup n x))
            |> map (fn (i, _) => "lookup of item " ^ string_of_int i);
        in content @ lookup end);
  in maps check histories end;


(* cases *)

val nT = Type ("n", []);
val aT = TFree ("'a", []);
fun c name T = Const (name, T);
fun v name T = Var ((name, 0), T);
fun all T = c "fall" ((T --> nT) --> nT);
fun itself T = Const ("Pure.type", Type ("itself", [T]));
fun lstT T = Type ("lst", [T]);

(*pattern, object: the object is an instance of the pattern up to beta-eta*)
val retrieved =
 [("eta-unstable, de Morgan",
    all nT $ Abs ("x", nT, c "nt" (nT --> nT) $ (v "P" (nT --> nT) $ Bound 0)),
    all nT $ Abs ("x", nT, c "nt" (nT --> nT) $ Bound 0)),
  ("eta-unstable, repeated bound",
    Abs ("x", nT, v "P" (nT --> nT --> nT) $ Bound 0 $ Bound 0),
    c "f" (nT --> nT)),
  ("eta-unstable, swapped bounds",
    Abs ("x", nT, Abs ("y", nT, v "P" (nT --> nT --> nT) $ Bound 0 $ Bound 1)),
    c "k" (nT --> nT --> nT)),
  ("front-rigid",
    Abs ("x", nT, c "g" (nT --> nT --> nT) $ (v "F" (nT --> nT) $ Bound 0) $ Bound 0),
    c "g" (nT --> nT --> nT) $ c "d" nT),
  ("raw insert",
    Abs ("x", nT,
      c "g" (nT --> nT --> nT) $ (Abs ("y", nT, c "z" nT) $ Bound 0) $
        (v "F" (nT --> nT) $ Bound 0)),
    c "g" (nT --> nT --> nT) $ c "z" nT),
  ("TYPE, schematic",
    c "tf" (Term.itselfT nT --> lstT nT --> nT) $ itself (TVar (("'a", 0), [])) $
      (c "rv" (lstT nT --> lstT nT) $ v "xs" (lstT nT)),
    c "tf" (Term.itselfT nT --> lstT nT --> nT) $ itself nT $
      (c "rv" (lstT nT --> lstT nT) $ Free ("xs", lstT nT)))];

(*pattern, object: no instance of the pattern is the object*)
val not_retrieved =
 [("TYPE, other type",
    c "tf" (Term.itselfT nT --> lstT nT --> nT) $ itself nT $ v "xs" (lstT nT),
    c "tf" (Term.itselfT aT --> lstT aT --> nT) $ itself aT $ Free ("ys", lstT aT)),
  ("lambda bodies",
    all nT $ Abs ("x", nT, c "f2" (nT --> nT --> nT) $ Bound 0 $ Bound 0),
    all nT $ Abs ("x", nT, c "f1" (nT --> nT --> nT) $ Bound 0 $ Bound 0))];

val eq_string: string * string -> bool = op =;

fun retrieval_cases () =
  (retrieved |> maps (fn (name, pat, obj) =>
    guarded name (fn () =>
      let val net = N.insert_term eq_string (pat, name) N.empty in
        (if member eq_string (N.match_term net obj) name then [] else ["match_term misses it"]) @
        (if member eq_string (N.unify_term net obj) name then [] else ["unify_term misses it"])
      end))) @
  (not_retrieved |> maps (fn (name, pat, obj) =>
    guarded name (fn () =>
      let val net = N.insert_term eq_string (pat, name) N.empty in
        if member eq_string (N.match_term net obj) name then ["match_term returns it"] else []
      end)));

fun deletion_cases () =
  guarded "deletion" (fn () =>
    let
      val pats = map #2 retrieved;
      val net =
        fold (fn (i, t) => N.insert_term eq_string (t, string_of_int i)) (map_index I pats) N.empty;
      val net' = N.delete_term eq_string (hd pats, "0") net;
      val remaining = fold (fn (i, t) => N.delete_term eq_string (t, string_of_int i))
        (tl (map_index I pats)) net';
    in
      (if member eq_string (N.match_term net' (#3 (hd retrieved))) "0"
       then ["deleted item retrieved"] else []) @
      (if member eq_string (N.match_term net' (#3 (nth retrieved 1))) "1" then []
       else ["other item lost"]) @
      (if N.is_empty remaining then [] else ["not empty after deleting everything"])
    end);

fun membership_cases () =
  guarded "membership" (fn () =>
    let
      val eq = fn ((t, u), (t', u')) => t aconv t' andalso u aconv u';
      val items = map (fn (name, pat, _) => (pat, Free (name, nT))) retrieved;
      val net = fold_rev Items.update items (Items.init eq (single o #1));
      val net' = Items.update (hd items) net;
      val net'' = Items.remove (hd items) net';
    in
      (if forall (Items.member net) items then [] else ["an updated item is not a member"]) @
      (if Items.length net' = length items then [] else ["update of a member adds a copy"]) @
      (if Items.member net'' (hd items) then ["a removed item is a member"] else [])
    end);

fun failures () =
  retrieval_cases () @ deletion_cases () @ membership_cases () @
  replay (fn ((t, u), (t', u')) => t aconv t' andalso u aconv u') (single o #1)
    (map (fn (name, pat, _) => (pat, Free (name, nT))) (retrieved @ not_retrieved) @
     map (fn (name, _, obj) => (obj, Free (name ^ ", object", nT))) (retrieved @ not_retrieved));

end;
