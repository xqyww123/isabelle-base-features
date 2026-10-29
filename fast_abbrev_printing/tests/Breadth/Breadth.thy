theory Breadth
  imports
    "HOL-Algebra.Galois_Connection" "HOL-Algebra.FiniteProduct" "HOL-Algebra.Sylow"
    "HOL-Algebra.Bij" "HOL-Algebra.Multiplicative_Group" "HOL-Algebra.Zassenhaus"
    "HOL-Algebra.Divisibility" "HOL-Algebra.IntRing" "HOL-Algebra.UnivPoly"
    "HOL-Algebra.Algebraic_Closure_Type" "HOL-Algebra.Algebra"
    Fast_Abbrev_Printing_Fixture.Entries
begin

text \<open>Every named fact of HOL-Algebra, printed in the context of the theory that states it, and
  the facts of locale and class contexts, printed there; each in the default print mode and in
  \<open>iff\<close>, the one other print mode with a container in HOL contexts.  Content entries for the
  last theory and for each locale and class context.  The imports are the session's top theories,
  so that every HOL-Algebra theory is an ancestor.\<close>

ML \<open>
structure FAP_Breadth =
struct

val content_modes = ["iff"];
val print_modes = [[], content_modes];

fun mode_label [] = "default"
  | mode_label (m :: _) = m;

val locales =
  ["Group.monoid", "Group.group", "Group.comm_group", "Ring.abelian_monoid", "Ring.ring",
   "UnivPoly.UP_pre_univ_prop", "Orderings.linorder", "Lattices.lattice",
   "Fields.linordered_field"];

fun fact_lines ctxt (name, th) =
  print_modes |> map (fn modes =>
    FAP_Entries.term_entry {text = false} ctxt modes
      (name ^ " @" ^ mode_label modes, Thm.prop_of th));

fun local_facts thy ctxt =
  FAP_Golden.new_facts [Global_Theory.facts_of thy] (Proof_Context.facts_of ctxt);

(*the contexts whose containers the locale golden records and the replay checks: each locale and
  class context, then the last theory's*)
fun locale_contexts thy = map (fn loc => (loc, FAP_Entries.context_at thy loc)) locales;
fun theory_context thy = (Context.theory_base_name thy, Proof_Context.init_global thy);
fun content_contexts thy = locale_contexts thy @ [theory_context thy];

fun register thy =
  let
    val theory_corpora =
      FAP_Golden.facts_of thy "HOL-Algebra."
      |> map (fn (thy', facts) => (Context.theory_long_name thy', thy', "", facts));
    val locale_corpora =
      locale_contexts thy |> map (fn (loc, ctxt) => (loc, thy, loc, local_facts thy ctxt));
  in
    fold (fn (label, thy', loc, facts) =>
      fold (fn modes =>
        FAP_Entries.register (label ^ " @" ^ mode_label modes)
          {thy = Context.theory_long_name thy', loc = loc, modes = modes,
           terms = map (Thm.prop_of o #2) facts})
        print_modes) (theory_corpora @ locale_corpora) thy
  end;

fun theories_dump thy =
  FAP_Golden.facts_dump (fn thy' => cat_lines o fact_lines (Proof_Context.init_global thy'))
    thy "HOL-Algebra.";

fun locales_dump thy =
  (locale_contexts thy |> maps (fn (loc, ctxt) =>
    let val facts = local_facts thy ctxt in
      ("## " ^ loc ^ " (" ^ string_of_int (length facts) ^ " theorems)") ::
        maps (fact_lines ctxt) facts @ FAP_Entries.content_entries loc ctxt content_modes
    end)) @
  (let val (label, ctxt) = theory_context thy
   in FAP_Entries.content_entries label ctxt content_modes end)
  |> cat_lines |> suffix "\n";

end;
\<close>

setup \<open>FAP_Breadth.register\<close>

ML \<open>
FAP_Golden.check \<^theory> "breadth_theories.golden" (FAP_Breadth.theories_dump \<^theory>);
FAP_Golden.check \<^theory> "breadth_locales.golden" (FAP_Breadth.locales_dump \<^theory>);
\<close>

end
