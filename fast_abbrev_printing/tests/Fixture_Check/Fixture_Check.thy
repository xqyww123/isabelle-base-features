theory Fixture_Check
  imports
    Fast_Abbrev_Printing_Fixture.Fixture_Basic Fast_Abbrev_Printing_Fixture.Fixture_Lambda
    Fast_Abbrev_Printing_Fixture.Fixture_Order Fast_Abbrev_Printing_Fixture.Fixture_Merge
    INet_Regression Candidates
begin

text \<open>Pure's copy of iNet is Performant_Isabelle_ML's \<open>library/improved_net.ML\<close> at its commit
  637990c.  That content is what the safety verification of iNet for abbreviation contraction
  covers, so a new digest needs a new verification first.\<close>

ML \<open>
let
  val sha1 = SHA1.rep (SHA1.digest (File.read (Path.explode "~~/src/Pure/improved_net.ML")));
  val pinned = "89c746402f8034a4ced4aa0054fc32ebfed95cff";
in
  if sha1 = pinned then ()
  else error ("Pure's improved_net.ML has SHA1 " ^ sha1 ^ ", not the verified " ^ pinned)
end
\<close>

ML \<open>
(case Pure_iNet_Regression.failures () of
  [] => ()
| msgs => error ("iNet regression:\n" ^ cat_lines msgs))
\<close>

ML \<open>FAP_Candidates.check_corpora \<^theory> "fixture_candidates.txt"\<close>

text \<open>The discrimination assertion: at \<open>\<And>x. f_1 x x\<close>, \<^ML>\<open>Consts.retrieve_abbrevs\<close> tells the
  three lambda patterns apart; stock unification retrieval returns all three.\<close>

ML \<open>
let
  val consts = Proof_Context.consts_of \<^context>;
  val probe = \<^term>\<open>\<And>x::n. PROP f_1 x x\<close>;
  fun heads items = map (fn (_, lhs) => (case head_of lhs of Const (c, _) => c | _ => "")) items;
  val patched = heads (Consts.retrieve_abbrevs consts [""] probe);
  val stock =
    heads (maps (fn net => Item_Net.retrieve net probe) (Consts.revert_abbrevs consts [""]));
  val (p1, p2, p3) = (\<^const_abbrev>\<open>p_1\<close>, \<^const_abbrev>\<open>p_2\<close>, \<^const_abbrev>\<open>p_3\<close>);
in
  if not (forall (member (op =) stock) [p1, p2, p3]) then
    error "discrimination: stock retrieval does not return all three lambda patterns"
  else if member (op =) patched p1 andalso not (exists (member (op =) patched) [p2, p3]) then ()
  else
    error ("discrimination: retrieve_abbrevs returns " ^
      commas (filter (member (op =) [p1, p2, p3]) patched))
end
\<close>

end
