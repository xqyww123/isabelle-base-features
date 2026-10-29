(*  Byte-for-byte reference output for the tests of a feature package.

    The tree decides the mode: on the feature's stock tree, whose ISABELLE_IDENTIFIER ends with
    -<feature>-stock, a check records <golden dir>/<name>; on any other tree it compares and, on a
    mismatch, writes <name>.actual next to the reference and fails.  The golden directory is
    ../golden, seen from the directory of the theory that checks.
*)

signature GOLDEN =
sig
  val recording: bool
  val check: theory -> string -> string -> unit
  val indexed: string * thm list -> (string * thm) list
  val facts_of: theory -> string -> (theory * (string * thm) list) list
  val facts_dump: (theory -> string * thm -> string) -> theory -> string -> string
end;

functor Golden(val feature: string): GOLDEN =
struct

val recording = String.isSuffix ("-" ^ feature ^ "-stock") (getenv "ISABELLE_IDENTIFIER");

fun golden_dir thy = Path.append (Resources.master_directory thy) (Path.explode "../golden");

fun first_difference expected actual =
  let
    val ls1 = split_lines expected and ls2 = split_lines actual;
    fun find i (l1 :: r1) (l2 :: r2) = if l1 = l2 then find (i + 1) r1 r2 else SOME (i, l1, l2)
      | find _ [] [] = NONE
      | find i (l1 :: _) [] = SOME (i, l1, "<end of actual>")
      | find i [] (l2 :: _) = SOME (i, "<end of golden>", l2);
  in
    (case find 1 ls1 ls2 of
      SOME (i, l1, l2) =>
        "line " ^ string_of_int i ^ "\n  golden: " ^ l1 ^ "\n  actual: " ^ l2 ^
        "\n  (" ^ string_of_int (length ls1) ^ " vs " ^ string_of_int (length ls2) ^ " lines)"
    | NONE => "no line differs (trailing newline?)")
  end;

fun check thy name text =
  let
    val dir = golden_dir thy;
    val path = Path.append dir (Path.basic name);
  in
    if recording then
      (Isabelle_System.make_directory dir; File.write path text;
       writeln ("recorded golden " ^ name ^ " (" ^ string_of_int (size text) ^ " bytes)"))
    else
      let val expected = File.read path in
        if expected = text then writeln ("golden " ^ name ^ " matches")
        else
          (File.write (Path.append dir (Path.basic (name ^ ".actual"))) text;
           error ("golden " ^ name ^ " differs at " ^ first_difference expected text ^
             "\n  actual output written next to it as " ^ name ^ ".actual"))
      end
  end;

fun indexed (name, [th]) = [(name, th)]
  | indexed (name, ths) = map_index (fn (i, th) => (name ^ "(" ^ string_of_int (i + 1) ^ ")", th)) ths;

(*every fact first stated in an ancestor theory whose long name has the prefix, by theory then by
  name.  Ancestors, not Thy_Info: theories loaded in the running session are not registered there
  yet*)
fun facts_of thy prefix =
  Theory.ancestors_of thy
  |> filter (String.isPrefix prefix o Context.theory_long_name)
  |> sort (string_ord o apply2 Context.theory_long_name)
  |> map (fn thy' =>
      (thy',
        Facts.dest_static false (map Global_Theory.facts_of (Theory.parents_of thy'))
          (Global_Theory.facts_of thy')
        |> sort_by #1 |> maps indexed));

fun facts_dump entry thy prefix =
  facts_of thy prefix
  |> maps (fn (thy', facts) =>
      ("## " ^ Context.theory_long_name thy' ^ " (" ^ string_of_int (length facts) ^ " theorems)")
        :: map (entry thy') facts)
  |> cat_lines |> suffix "\n";

end;
