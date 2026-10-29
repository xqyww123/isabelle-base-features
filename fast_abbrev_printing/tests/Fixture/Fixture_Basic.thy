theory Fixture_Basic
  imports Fixture_Base
begin

text \<open>Patterns with a binder that an instance may lose (eta-unstable), among them one whose front
  holds both the bound variable and a schematic (front-rigid); \<open>TYPE\<close>; an abbreviation declared
  after a print; and the guards of \<^ML>\<open>Proof_Context.contract_abbrevs\<close>: abbreviation mode,
  \<^ML>\<open>Proof_Context.show_abbrevs\<close> off, an ill-typed term.\<close>

typedecl 'a lst

consts
  fall2 :: "('a \<Rightarrow> 'a \<Rightarrow> b) \<Rightarrow> b"
  k :: "n \<Rightarrow> n \<Rightarrow> b"
  gf :: "n \<Rightarrow> 'a \<Rightarrow> b"
  c :: n
  tf :: "'a itself \<Rightarrow> 'a lst \<Rightarrow> n"
  rv :: "'a lst \<Rightarrow> 'a lst"
  ap :: "'a lst \<Rightarrow> 'a lst \<Rightarrow> 'a lst"
  gl :: "n \<Rightarrow> n \<Rightarrow> n"

abbreviation nall where "nall P \<equiv> fall (\<lambda>x. nt (P x))"
abbreviation swp where "swp P \<equiv> fall2 (\<lambda>x y. P y x)"
abbreviation frg where "frg F \<equiv> fall (\<lambda>x. gf (F x) x)"
abbreviation tt where "tt (xs::'a lst) \<equiv> tf TYPE('a) (rv xs)"
abbreviation tt2 where "tt2 (xs::n lst) \<equiv> tf TYPE(n) (ap xs xs)"

ML \<open>
val basic_objects =
  [("eta-unstable, binder kept", \<^term>\<open>fall (\<lambda>x::b. nt x)\<close>),
   ("eta-unstable, binder lost", \<^term>\<open>fall nt\<close>),
   ("eta-unstable, two binders lost", \<^term>\<open>fall2 k\<close>),
   ("front-rigid", \<^term>\<open>fall (gf c)\<close>),
   ("TYPE, schematic", \<^term>\<open>tf TYPE(n) (rv xs)\<close>),
   ("TYPE, schematic at another type", \<^term>\<open>tf TYPE(b) (rv ys)\<close>),
   ("TYPE, fixed", \<^term>\<open>tf TYPE(n) (ap xs xs)\<close>),
   ("TYPE, fixed, other type", \<^term>\<open>tf TYPE(b) (ap ys ys)\<close>)];

val _ = \<^assert> (case #2 (hd basic_objects) of _ $ Abs _ => true | _ => false);

val late_object = ("declared later", \<^term>\<open>gl c c\<close>);
val late_before =
  FAP_Entries.term_entry {text = true} \<^context> FAP_Fixture.modes
    (apfst (suffix ", printed before") late_object);
\<close>

abbreviation late where "late x \<equiv> gl c x"

setup \<open>FAP_Fixture.register "Fixture_Basic" "" (late_object :: basic_objects)\<close>

ML \<open>
let
  val ctxt = \<^context>;
  val guarded = #2 (hd basic_objects);
  val special =
   [(Proof_Context.set_mode Proof_Context.mode_abbrev ctxt, ("abbreviation mode", guarded)),
    (Config.put Proof_Context.show_abbrevs false ctxt, ("show_abbrevs off", guarded)),
    (*ill-typed at nt, which wants b; without the guard gl c would contract to late*)
    (ctxt, ("ill-typed", \<^term>\<open>nt\<close> $ #2 late_object))];
  val lines =
    FAP_Fixture.dump ctxt "Fixture_Basic" (basic_objects @ [late_object]) @ [late_before] @
      map (fn (ctxt', obj) => FAP_Entries.term_entry {text = true} ctxt' FAP_Fixture.modes obj)
        special;
in FAP_Golden.check \<^theory> "fixture_basic.golden" (cat_lines lines ^ "\n") end
\<close>

end
