theory Fixture_Merge_A
  imports Fixture_Merge_Base
begin

text \<open>Without parameters: \<open>ma y \<equiv> gm cm y\<close> would be stored eta-contracted, as the pattern
  \<open>gm cm\<close>, which does not match \<open>gm cm dm\<close> itself.\<close>

abbreviation ma where "ma \<equiv> gm cm dm"

end
