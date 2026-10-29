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
let
  val failures =
    FAP_Breadth.content_contexts \<^theory> |> maps (fn (label, ctxt) =>
      FAP_Entries.listed_modes FAP_Breadth.content_modes |> maps (fn m =>
        (case FAP_Entries.container ctxt m of
          NONE => []
        | SOME net =>
            Pure_iNet_Regression.replay (Item_Net.content net)
            |> map (fn msg => label ^ " mode=" ^ FAP_Entries.show_mode m ^ ": " ^ msg))));
  val _ =
    FAP_Entries.write_results \<^theory> "breadth_replay.txt"
      (if null failures then ["replay: pass"] else failures);
in if null failures then () else error ("replay:\n" ^ cat_lines failures) end
\<close>

ML \<open>FAP_Candidates.check_corpora \<^theory> "breadth_candidates.txt"\<close>

end
