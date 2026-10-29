theory Fixture_Ratio
  imports Fast_Abbrev_Printing_Fixture.Fixture_Base Candidates
begin

text \<open>The ratio assertion: in a context of 1,000 abbreviations whose patterns hold a
  lambda-abstraction, the patched \<^ML>\<open>Proof_Context.contract_abbrevs\<close> is at least \<open>R\<close> times
  faster than the stock route, min of 5 after an untimed run.  It is the one automatic guard
  against a port that sends the contraction back to the stock route, which keeps every byte.\<close>

ML \<open>
structure FAP_Ratio =
struct

val size = 1000;
val nT = \<^typ>\<open>n\<close>;
val fT = nT --> nT --> propT;
fun const_name i = "rf_" ^ string_of_int i;
fun pattern f = Logic.all_const nT $ Abs ("x", nT, f $ Bound 0 $ Bound 0);

end;
\<close>

text \<open>Declared at theory level: \<^ML>\<open>Sign.add_abbrev\<close> registers the reverse abbreviation, and
  no local-theory transfer merges the containers after each declaration.\<close>

setup \<open>
  let open FAP_Ratio in
    Sign.add_consts (map (fn i => (Binding.name (const_name i), fT, NoSyn)) (1 upto size))
    #> (fn thy =>
      fold (fn i =>
        Sign.add_abbrev "" (Binding.name ("rp_" ^ string_of_int i),
          pattern (Const (Sign.full_name thy (Binding.name (const_name i)), fT))) #> #2)
      (1 upto size) thy)
  end
\<close>

ML \<open>
let
  open FAP_Ratio;
  (*measured 25 times on the patched tree (2026-10-29); the stock route gives about 1*)
  val ratio_min = 5.0;
  val ctxt = \<^context>;
  val objects =
    map_filter (fn i =>
      if i mod 10 = 0
      then SOME (pattern (Const (Sign.full_name \<^theory> (Binding.name (const_name i)), fT)))
      else NONE) (1 upto size);
  fun clock f =
    let
      val _ = f ();
      val ts = map (fn _ => let val t0 = Time.now (); val _ = f () in Time.now () - t0 end) (1 upto 5);
    in Time.toReal (hd (sort Time.compare ts)) end;
  val stock = FAP_Candidates.stock_procedure ctxt;
  val stock_terms = map (FAP_Candidates.contract ctxt stock) objects;
  val patched_terms = map (Proof_Context.contract_abbrevs ctxt) objects;
  val _ =
    if eq_list (op aconv) (stock_terms, patched_terms) then ()
    else error "ratio: the two routes contract differently";
  val t_stock = clock (fn () => map (FAP_Candidates.contract ctxt stock) objects);
  val t_patched = clock (fn () => map (Proof_Context.contract_abbrevs ctxt) objects);
  val ratio = t_stock / Real.max (t_patched, 1.0E~6);
  val msg =
    "ratio: stock route " ^ Real.fmt (StringCvt.FIX (SOME 2)) (t_stock * 1000.0) ^ " ms, patched " ^
    Real.fmt (StringCvt.FIX (SOME 2)) (t_patched * 1000.0) ^ " ms, " ^
    Real.fmt (StringCvt.FIX (SOME 1)) ratio ^ " times";
in if ratio >= ratio_min then writeln msg else error (msg ^ ", below " ^ Real.toString ratio_min) end
\<close>

end
