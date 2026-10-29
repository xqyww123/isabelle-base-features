theory Fixture_Base
  imports Entries
begin

text \<open>HOL's shapes written in Pure: \<open>n\<close> for individuals, \<open>b\<close> for truth values, and fixture
  constants of the arity and type shape of HOL's \<open>Not\<close> and \<open>All\<close>.  Fixture entries are printed
  under the fixture's own print mode \<open>fap_mode\<close>.\<close>

typedecl n
typedecl b

consts
  nt :: "b \<Rightarrow> b"
  fall :: "('a \<Rightarrow> b) \<Rightarrow> b"

ML \<open>
structure FAP_Fixture =
struct

val modes = ["fap_mode"];

(*the golden text of a theory or locale context: term entries, then content entries*)
fun dump ctxt label objects =
  ("## " ^ label) :: map (FAP_Entries.term_entry {text = true} ctxt modes) objects @
    FAP_Entries.content_entries label ctxt modes;

fun register label loc (objects: (string * term) list) thy =
  FAP_Entries.register label
    {thy = Context.theory_long_name thy, loc = loc, modes = modes, terms = map #2 objects} thy;

end;
\<close>

end
