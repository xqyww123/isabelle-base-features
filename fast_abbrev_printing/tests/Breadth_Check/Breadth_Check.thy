theory Breadth_Check
  imports
    Fast_Abbrev_Printing_Golden.Breadth
    Fast_Abbrev_Printing_Fixture_Check.INet_Regression Fast_Abbrev_Printing_Fixture_Check.Candidates
begin

text \<open>The replay: the reverted abbreviations of the last theory and of each locale and class
  context, every listed mode with a container, through the histories of the container on an
  \<^ML_type>\<open>'a Item_iNet.T\<close> against the stock \<^ML_type>\<open>'a Item_Net.T\<close>.  Then the candidate
  lists on every corpus of the breadth session.\<close>

ML \<open>
structure Pure_iNet_Regression = INet_Regression(iNet);

let
  val thy = \<^theory>;
  val contexts =
    ("Breadth", \<^context>) ::
      map (fn loc => (loc, Named_Target.init [] loc thy)) FAP_Breadth.locales;
  val failures =
    contexts |> maps (fn (label, ctxt) =>
      Print_Mode.setmp ["iff"] FAP_Entries.listed_modes () |> maps (fn m =>
        (case FAP_Entries.container ctxt m of
          NONE => []
        | SOME net =>
            Pure_iNet_Regression.replay FAP_Entries.eq_item (single o #1) (Item_Net.content net)
            |> map (fn msg => label ^ " mode=" ^ FAP_Entries.show_mode m ^ ": " ^ msg))));
in
  if null failures then writeln "replay: pass"
  else error ("replay:\n" ^ cat_lines failures)
end
\<close>

ML \<open>FAP_Candidates.check_corpora \<^theory>\<close>

end
