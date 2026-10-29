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

val count = 1000;
val nT = \<^typ>\<open>n\<close>;
val fT = nT --> nT --> propT;
fun const_name i = "rf_" ^ string_of_int i;

(*\<And>x. rf_i x x, the abbreviation rp_i's rhs and the timed objects*)
fun pattern thy i =
  Logic.all_const nT $
    Abs ("x", nT, Const (Sign.full_name thy (Binding.name (const_name i)), fT) $ Bound 0 $ Bound 0);

end;
\<close>

text \<open>Declared at theory level: \<^ML>\<open>Sign.add_abbrev\<close> registers the reverted abbreviation, and
  no local-theory transfer merges the containers after each declaration.\<close>

setup \<open>
  Sign.add_consts
    (map (fn i => (Binding.name (FAP_Ratio.const_name i), FAP_Ratio.fT, NoSyn))
      (1 upto FAP_Ratio.count))
  #> (fn thy =>
    fold (fn i =>
      Sign.add_abbrev "" (Binding.name ("rp_" ^ string_of_int i), FAP_Ratio.pattern thy i) #> #2)
    (1 upto FAP_Ratio.count) thy)
\<close>

ML \<open>
let
  (*R = 5: the ratio measured on the patched tree was 25 to 35 (2026-10-29), about 1 on the
    stock route*)
  val ratio_min = 5.0;
  val ctxt = \<^context>;
  val objects =
    map (FAP_Ratio.pattern \<^theory>) (filter (fn i => i mod 10 = 0) (1 upto FAP_Ratio.count));
  fun clock f =
    let
      val _ = f ();
      val ts =
        map (fn _ => let val t0 = Time.now (); val _ = f () in Time.now () - t0 end) (1 upto 5);
    in Time.toReal (hd (sort Time.compare ts)) end;
  val stock = FAP_Candidates.stock_procedure ctxt;
  val stock_terms = map (FAP_Candidates.contract ctxt stock) objects;
  val patched_terms = map (Proof_Context.contract_abbrevs ctxt) objects;
  val _ =
    if eq_list (op aconv) (stock_terms, patched_terms) then ()
    else error "ratio: the two routes contract differently";
  val _ =
    if exists (op aconv) (objects ~~ patched_terms) then error "ratio: an object does not contract"
    else ();
  val t_stock = clock (fn () => map (FAP_Candidates.contract ctxt stock) objects);
  val t_patched = clock (fn () => map (Proof_Context.contract_abbrevs ctxt) objects);
  val ratio = t_stock / Real.max (t_patched, 1.0E~6);
  val msg =
    "ratio: stock route " ^ Real.fmt (StringCvt.FIX (SOME 2)) (t_stock * 1000.0) ^ " ms, patched " ^
    Real.fmt (StringCvt.FIX (SOME 2)) (t_patched * 1000.0) ^ " ms, " ^
    Real.fmt (StringCvt.FIX (SOME 1)) ratio ^ " times";
  val _ = FAP_Entries.write_results \<^theory> "ratio.txt" [msg];
in if ratio >= ratio_min then () else error (msg ^ ", below " ^ Real.toString ratio_min) end
\<close>

end
