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

val print_modes = [[], ["iff"]];

val locales =
  ["Group.monoid", "Group.group", "Group.comm_group", "Ring.abelian_monoid", "Ring.ring",
   "UnivPoly.UP_pre_univ_prop", "Orderings.linorder", "Lattices.lattice",
   "Fields.linordered_field"];

fun fact_lines ctxt (name, th) =
  print_modes |> map (fn modes =>
    FAP_Entries.term_entry {text = false} ctxt modes
      (name ^ " @" ^ (case modes of [] => "default" | m :: _ => m), Thm.prop_of th));

fun local_facts thy ctxt =
  Facts.dest_static false [Global_Theory.facts_of thy] (Proof_Context.facts_of ctxt)
  |> sort_by #1 |> maps FAP_Golden.indexed;

(*label, theory, locale ("" for a theory context), facts*)
fun contexts thy =
  map (fn (thy', facts) => (Context.theory_long_name thy', thy', "", facts))
    (FAP_Golden.facts_of thy "HOL-Algebra.") @
  map (fn loc =>
    (loc, thy, loc, local_facts thy (Named_Target.init [] loc thy))) locales;

fun context_of thy loc =
  if loc = "" then Proof_Context.init_global thy else Named_Target.init [] loc thy;

fun register thy =
  fold (fn (label, thy', loc, facts) =>
    fold (fn modes =>
      FAP_Entries.register (label ^ " @" ^ (case modes of [] => "default" | m :: _ => m))
        {thy = Context.theory_long_name thy', loc = loc, modes = modes,
         terms = map (Thm.prop_of o #2) facts})
      print_modes) (contexts thy) thy;

fun dump thy kind =
  contexts thy
  |> filter (fn (_, _, loc, _) => (kind = "locales") = (loc <> ""))
  |> maps (fn (label, thy', loc, facts) =>
      let val ctxt = context_of thy' loc in
        ("## " ^ label ^ " (" ^ string_of_int (length facts) ^ " theorems)") ::
          maps (fact_lines ctxt) facts @
          (if kind = "locales" then FAP_Entries.content_entries label ctxt ["iff"] else [])
      end)
  |> cat_lines |> suffix "\n";

end;
\<close>

setup \<open>FAP_Breadth.register\<close>

ML \<open>
FAP_Golden.check \<^theory> "breadth_theories.golden" (FAP_Breadth.dump \<^theory> "theories");
FAP_Golden.check \<^theory> "breadth_locales.golden"
  (FAP_Breadth.dump \<^theory> "locales" ^
    cat_lines (FAP_Entries.content_entries "Breadth" \<^context> ["iff"]) ^ "\n");
\<close>

end
