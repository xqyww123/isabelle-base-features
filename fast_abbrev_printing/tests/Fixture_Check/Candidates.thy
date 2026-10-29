theory Candidates
  imports Fast_Abbrev_Printing_Fixture.Entries
begin

text \<open>The candidate lists: a copy of \<^ML>\<open>Proof_Context.contract_abbrevs\<close> whose procedure, at
  every object \<^ML>\<open>Pattern.rewrite_term_yoyo\<close> hands it, compares the candidates of
  \<^ML>\<open>Consts.retrieve_abbrevs\<close> that \<^ML>\<open>Pattern.match_rew\<close> accepts with those it accepts
  from stock unification retrieval over \<^ML>\<open>Consts.revert_abbrevs\<close>: equal as ordered lists under
  the container's equality.  It returns the stock head, so the walk proceeds as stock's would.
  The same driver, with the stock route only, is the reference of the timings.\<close>

ML \<open>
structure FAP_Candidates =
struct

(*proof_context.ML, contract_abbrevs; the corpora are not in abbreviation mode and show
  abbreviations*)
fun contract ctxt match_abbrev tm =
  if not (can Term.type_of tm) then tm
  else
    let val inst = #1 (Variable.import_inst true [tm] (Variable.declare_names tm ctxt)) in
      Term_Subst.instantiate inst tm
      |> Pattern.rewrite_term_yoyo (Proof_Context.theory_of ctxt) [] [match_abbrev]
      |> Term_Subst.instantiate_frees (Variable.import_inst_revert inst)
    end;

(*the stock route: unification retrieval over the converted containers, taken once*)
fun stock_procedure ctxt =
  let
    val thy = Proof_Context.theory_of ctxt;
    val nets = Consts.revert_abbrevs (Proof_Context.consts_of ctxt) (print_mode_value () @ [""]);
    val rew = Option.map #1 oo Pattern.match_rew thy;
  in fn t => get_first (fn net => get_first (rew t) (Item_Net.retrieve net t)) nets end;

(*the objects visited and those where the two lists differ*)
fun compare ctxt modes terms =
  Print_Mode.setmp modes (fn () =>
    let
      val thy = Proof_Context.theory_of ctxt;
      val consts = Proof_Context.consts_of ctxt;
      val ms = print_mode_value () @ [""];
      val retrieve = Consts.retrieve_abbrevs consts ms;
      val nets = Consts.revert_abbrevs consts ms;
      fun accepted t = filter (is_some o Pattern.match_rew thy t);
      val visited = Unsynchronized.ref 0;
      val differing = Unsynchronized.ref ([]: term list);
      fun match_abbrev t =
        let
          val patched = accepted t (retrieve t);
          val stock = accepted t (maps (fn net => Item_Net.retrieve net t) nets);
          val _ = visited := ! visited + 1;
          val _ = if FAP_Entries.same patched stock then () else differing := t :: ! differing;
        in (case stock of [] => NONE | item :: _ => Option.map #1 (Pattern.match_rew thy t item)) end;
      val _ = List.app (ignore o contract ctxt match_abbrev) terms;
    in (! visited, rev (! differing)) end) ();

fun check_corpora thy =
  FAP_Entries.corpora thy |> List.app (fn (label, corpus) =>
    let val (visited, differing) = compare (FAP_Entries.context_of corpus) (#modes corpus) (#terms corpus) in
      if null differing then
        writeln ("candidates " ^ label ^ ": " ^ string_of_int visited ^ " objects agree")
      else
        error ("candidates " ^ label ^ ": the lists differ at " ^
          string_of_int (length differing) ^ " of " ^ string_of_int visited ^ " objects, first " ^
          ML_Syntax.print_term (hd differing))
    end);

end;
\<close>

end
