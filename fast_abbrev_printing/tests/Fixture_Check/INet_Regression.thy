theory INet_Regression
  imports Pure
begin

ML_file \<open>inet_regression.ML\<close>

ML \<open>structure Pure_iNet_Regression = INet_Regression(iNet);\<close>

end
