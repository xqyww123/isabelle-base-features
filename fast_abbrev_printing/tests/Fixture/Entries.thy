theory Entries
  imports Golden_Harness.Golden_Harness
begin

text \<open>The entries of the golden files, in stock API only, so that they record on the stock tree:

  \<^item> a term entry: an object printed under given print modes, with the SHA1 of the printed text,
    of the term \<^ML>\<open>Proof_Context.contract_abbrevs\<close> returns and of the term
    \<^ML>\<open>Syntax.uncheck_terms\<close> hands to unparse;
  \<^item> content entries: the reverted abbreviations of each listed mode, in content order;
  \<^item> retrieval entries: the content positions of the items that stock unification and matching
    retrieval return at a probe object.

  The listed modes are the print modes followed by \<open>""\<close>, \<open>internal\<close> and \<open>input\<close>: no stock API
  lists a \<^ML_type>\<open>Consts.T\<close> value's modes, and these are the ones that printing and
  \<^ML>\<open>Consts.revert_abbrevs\<close>' callers depend on.  A corpus records the objects of a context for
  the check sessions.\<close>

ML \<open>
structure FAP_Golden = Golden(val feature = "fast_abbrev_printing");

structure FAP_Entries =
struct

fun digest s = SHA1.rep (SHA1.digest s);
val term_digest = digest o ML_Syntax.print_term;
val one_line = translate_string (fn "\n" => " " | c => c);

(*the equality of the reverted abbreviations (consts.ML)*)
val eq_item = eq_pair (op aconv) (op aconv);

fun listed_modes modes = distinct (op =) (modes @ ["", Print_Mode.internal, Print_Mode.input]);

fun container ctxt m =
  (case Consts.revert_abbrevs (Proof_Context.consts_of ctxt) [m] of
    [net] => SOME net
  | _ => NONE);

fun show_mode "" = "\"\""
  | show_mode m = m;

(*exceptions are part of the behaviour; their messages may carry source positions*)
fun attempt f = \<^try>\<open>f () catch exn => "EXN " ^ General.exnName exn\<close>;

(*a check's results, for reading after a batch build: <tests dir>/out/<name>; a failed build can
  leave an earlier run's file*)
fun write_results thy name lines =
  let val dir = Path.append (Resources.master_directory thy) (Path.explode "../out") in
    Isabelle_System.make_directory dir;
    File.write (Path.append dir (Path.basic name)) (cat_lines lines ^ "\n")
  end;


(* entries *)

fun term_entry {text} ctxt modes (label, t) =
  Print_Mode.setmp modes (fn () =>
    let
      val s =
        attempt (fn () => XML.content_of (YXML.parse_body (Syntax.string_of_term ctxt t)));
      val contracted = attempt (fn () => term_digest (Proof_Context.contract_abbrevs ctxt t));
      val unchecked = attempt (fn () => term_digest (singleton (Syntax.uncheck_terms ctxt) t));
    in
      space_implode "  "
        ([label, digest s, contracted, unchecked] @ (if text then [one_line s] else []))
    end) ();

fun content_entries label ctxt modes =
  listed_modes modes |> maps (fn m =>
    let val items = (case container ctxt m of SOME net => Item_Net.content net | NONE => []) in
      ("# content " ^ label ^ " mode=" ^ show_mode m ^ " count=" ^ string_of_int (length items)) ::
        map_index (fn (i, (pat, lhs)) =>
          string_of_int i ^ "  " ^ term_digest pat ^ "  " ^ term_digest lhs) items
    end);

fun retrieval_entries label ctxt modes probes =
  listed_modes modes |> maps (fn m =>
    (case container ctxt m of
      NONE => []
    | SOME net =>
        let
          val items = Item_Net.content net;
          fun positions xs =
            commas (map (fn x => string_of_int (find_index (fn y => eq_item (x, y)) items)) xs);
        in
          probes |> map (fn (probe, t) =>
            space_implode "  "
              ["# retrieval " ^ label ^ " mode=" ^ show_mode m ^ " probe=" ^ probe,
               "retrieve=" ^ positions (Item_Net.retrieve net t),
               "matching=" ^ positions (Item_Net.retrieve_matching net t)])
        end));


(* corpora for the check sessions *)

type corpus = {thy: string, loc: string, modes: string list, terms: term list};

structure Corpora = Theory_Data
(
  type T = corpus Symtab.table;
  val empty = Symtab.empty;
  val merge = Symtab.merge (K true);
);

fun register label (corpus: corpus) = Corpora.map (Symtab.update_new (label, corpus));
val corpora = Symtab.dest o Corpora.get;

fun context_at thy loc =
  if loc = "" then Proof_Context.init_global thy else Named_Target.init [] loc thy;

fun context_of ({thy, loc, ...}: corpus) = context_at (Thy_Info.get_theory thy) loc;

end;
\<close>

end
