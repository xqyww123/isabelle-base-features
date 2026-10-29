theory Fixture_Lambda
  imports Fixture_Base
begin

text \<open>The lambda fixture: three abbreviations whose patterns hold a lambda-abstraction under
  \<open>\<And>\<close>.  Stock retrieval keys every abstraction as a wildcard, so at \<open>\<And>x. f_1 x x\<close> it returns all
  three; the retrieval entries record that, against stock.  The eta-expanded object: stock
  contracts \<open>\<lambda>x. ge ce x\<close> to \<open>a_eta\<close> because unification retrieval offers \<open>ge ce\<close> at the
  abstraction and \<^ML>\<open>Pattern.match\<close> eta-expands the pattern there; a matching retrieval that
  does not eta-contract the query finds nothing there and yields \<open>\<lambda>x. a_eta x\<close>.\<close>

consts
  f_1 :: "n \<Rightarrow> n \<Rightarrow> prop"
  f_2 :: "n \<Rightarrow> n \<Rightarrow> prop"
  f_3 :: "n \<Rightarrow> n \<Rightarrow> prop"
  ge :: "n \<Rightarrow> n \<Rightarrow> n"
  ce :: n

abbreviation p_1 where "p_1 \<equiv> (\<And>x::n. PROP f_1 x x)"
abbreviation p_2 where "p_2 \<equiv> (\<And>x::n. PROP f_2 x x)"
abbreviation p_3 where "p_3 \<equiv> (\<And>x::n. PROP f_3 x x)"
abbreviation a_eta where "a_eta \<equiv> ge ce"

ML \<open>
val lambda_probes =
  [("all", \<^term>\<open>\<And>x::n. PROP f_1 x x\<close>),
   ("abs", Abs ("x", \<^typ>\<open>n\<close>, \<^term>\<open>f_1 :: n \<Rightarrow> n \<Rightarrow> prop\<close> $ Bound 0 $ Bound 0))];

val lambda_objects =
  lambda_probes @
   [("eta-expanded", Abs ("x", \<^typ>\<open>n\<close>, \<^term>\<open>ge ce\<close> $ Bound 0)),
    ("eta-contracted", \<^term>\<open>ge ce\<close>)];
\<close>

setup \<open>FAP_Fixture.register "Fixture_Lambda" "" lambda_objects\<close>

ML \<open>
let
  val ctxt = \<^context>;
  val lines =
    FAP_Fixture.dump ctxt "Fixture_Lambda" lambda_objects @
      FAP_Entries.retrieval_entries "Fixture_Lambda" ctxt FAP_Fixture.modes lambda_probes;
in FAP_Golden.check \<^theory> "fixture_lambda.golden" (cat_lines lines ^ "\n") end
\<close>

end
