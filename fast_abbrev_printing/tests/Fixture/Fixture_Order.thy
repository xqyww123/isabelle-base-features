theory Fixture_Order
  imports Fixture_Base
begin

text \<open>Objects matched by two abbreviations, so that the order of candidates decides the result.
  Across net leaves: \<open>a_l\<close> is declared before \<open>b_l\<close>, both match \<open>g3 c d e\<close>, and the newer one
  wins (\<open>b_l c\<close>); the two patterns sit in different leaves.  Across print modes: \<open>d1\<close> in the
  default mode and \<open>m1\<close> in \<open>fap_mode\<close> have the same pattern, and printing under \<open>fap_mode\<close>
  takes that mode's first (\<open>m1 c\<close>); the locale \<open>ord_l\<close> has the same pair.\<close>

consts
  g3 :: "n \<Rightarrow> n \<Rightarrow> n \<Rightarrow> n"
  g2 :: "n \<Rightarrow> n \<Rightarrow> n"
  c :: n
  d :: n
  e :: n
  z :: n

abbreviation a_l where "a_l y \<equiv> g3 c y e"
abbreviation b_l where "b_l x \<equiv> g3 x d e"

abbreviation d1 where "d1 x \<equiv> g2 x z"
abbreviation (fap_mode) m1 where "m1 x \<equiv> g2 x z"

locale ord_l =
  fixes Q :: "'a \<Rightarrow> b" and R :: "'b \<Rightarrow> b"
begin
abbreviation lq where "lq P \<equiv> fall (\<lambda>x::'a. Q (P x))"
abbreviation lr where "lr P \<equiv> fall (\<lambda>x::'a. R (P x))"
abbreviation (fap_mode) lm where "lm P \<equiv> fall (\<lambda>x::'a. Q (P x))"
end

ML \<open>
val order_objects =
  [("across leaves", \<^term>\<open>g3 c d e\<close>),
   ("across modes", \<^term>\<open>g2 c z\<close>)];

(*the locale's parameter Q, as its context fixes it*)
val order_locale_objects =
  [("across modes, locale",
    Term.betapply (\<^term>\<open>\<lambda>Q :: 'a \<Rightarrow> b. fall (\<lambda>x::'a. Q x)\<close>, Free ("Q", \<^typ>\<open>'a \<Rightarrow> b\<close>)))];
\<close>

setup \<open>
  FAP_Fixture.register "Fixture_Order" "" order_objects #>
  FAP_Fixture.register \<^locale>\<open>ord_l\<close> \<^locale>\<open>ord_l\<close> order_locale_objects
\<close>

ML \<open>
let
  val ctxt = \<^context>;
  val lctxt = Named_Target.init [] \<^locale>\<open>ord_l\<close> \<^theory>;
  val lines =
    FAP_Fixture.dump ctxt "Fixture_Order" order_objects @
      FAP_Fixture.dump lctxt \<^locale>\<open>ord_l\<close> order_locale_objects;
in FAP_Golden.check \<^theory> "fixture_order.golden" (cat_lines lines ^ "\n") end
\<close>

end
