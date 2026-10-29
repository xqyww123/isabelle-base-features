theory Fixture_Merge
  imports Fixture_Merge_A Fixture_Merge_B
begin

text \<open>Both parents' abbreviations match \<open>gm cm dm\<close>; the theory merge decides their order, which the
  content entries record.\<close>

ML \<open>val merge_objects = [("across a theory merge", \<^term>\<open>gm cm dm\<close>)]\<close>

setup \<open>FAP_Fixture.register "Fixture_Merge" "" merge_objects\<close>

ML \<open>
FAP_Golden.check \<^theory> "fixture_merge.golden"
  (cat_lines (FAP_Fixture.dump \<^context> "Fixture_Merge" merge_objects) ^ "\n")
\<close>

end
