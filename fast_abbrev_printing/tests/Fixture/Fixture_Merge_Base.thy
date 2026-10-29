theory Fixture_Merge_Base
  imports Fixture_Base
begin

text \<open>The constants of the merge fixture: \<open>Fixture_Merge_A\<close> and \<open>Fixture_Merge_B\<close> each declare an
  abbreviation that matches \<open>gm cm dm\<close>, and \<open>Fixture_Merge\<close> imports both.\<close>

consts
  gm :: "n \<Rightarrow> n \<Rightarrow> n"
  cm :: n
  dm :: n

end
